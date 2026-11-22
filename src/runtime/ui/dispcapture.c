/* M1653: the measured display rate via DXGI Desktop Duplication. The port's own counters only see the frames it renders; the
 * driver's AI-interpolated frames appear only at the desktop/compositor. Desktop Duplication hands us the composed desktop
 * image whenever the output changes, so counting distinct pictures per second uses the compositor's own timing and copies only
 * a small centre patch (no full-screen grabs); AcquireNextFrame's timeout blocks efficiently instead of busy-waiting.
 * Public surface: dispcap_start(hwnd) begins the thread, dispcap_fps() returns the measured distinct pictures per second
 * (0 = no measurement). window.c starts it while the on-screen overlay is on; non-Windows builds get stubs. */
#include "dispcapture.h"
#ifdef _WIN32
#define COBJMACROS
#include <windows.h>
#include <d3d11.h>
#include <dxgi1_2.h>
#include <pthread.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

static volatile LONG g_fps;
static volatile LONG g_started;
static void *g_hwnd;

int dispcap_fps(void) { return (int)InterlockedCompareExchange(&g_fps, 0, 0); }

static int rect_contains(const RECT *r, int x, int y) { return x >= r->left && x < r->right && y >= r->top && y < r->bottom; }

static void *dispcap_thread(void *arg) {
	(void)arg;
	CoInitializeEx(NULL, COINIT_MULTITHREADED);
	ID3D11Device *dev = NULL; ID3D11DeviceContext *ctx = NULL; D3D_FEATURE_LEVEL fl;
	if (FAILED(D3D11CreateDevice(NULL, D3D_DRIVER_TYPE_HARDWARE, NULL, 0, NULL, 0, D3D11_SDK_VERSION, &dev, &fl, &ctx))) { CoUninitialize(); return NULL; }
	IDXGIDevice *dxgi_dev = NULL;
	if (FAILED(dev->lpVtbl->QueryInterface(dev, &IID_IDXGIDevice, (void **)&dxgi_dev))) goto done_noadapter;
	IDXGIAdapter *adapter = NULL;
	if (FAILED(dxgi_dev->lpVtbl->GetAdapter(dxgi_dev, &adapter))) { dxgi_dev->lpVtbl->Release(dxgi_dev); goto done_noadapter; }
	IDXGIOutput1 *output1 = NULL; DXGI_OUTPUT_DESC od;
	RECT wr; GetWindowRect((HWND)g_hwnd, &wr);
	int cx = (wr.left + wr.right) / 2, cy = (wr.top + wr.bottom) / 2;
	for (UINT i = 0; !output1; i++) {
		IDXGIOutput *out = NULL;
		if (FAILED(adapter->lpVtbl->EnumOutputs(adapter, i, &out)) || !out) break;
		if (SUCCEEDED(out->lpVtbl->GetDesc(out, &od)) && rect_contains(&od.DesktopCoordinates, cx, cy))
			if (FAILED(out->lpVtbl->QueryInterface(out, &IID_IDXGIOutput1, (void **)&output1))) output1 = NULL;
		out->lpVtbl->Release(out);
	}
	if (!output1) { adapter->lpVtbl->Release(adapter); dxgi_dev->lpVtbl->Release(dxgi_dev); goto done_noadapter; }
	const int W = 192, H = 108;
	D3D11_TEXTURE2D_DESC td; memset(&td, 0, sizeof td);
	td.Width = W; td.Height = H; td.MipLevels = 1; td.ArraySize = 1; td.Format = DXGI_FORMAT_B8G8R8A8_UNORM;
	td.SampleDesc.Count = 1; td.Usage = D3D11_USAGE_STAGING; td.CPUAccessFlags = D3D11_CPU_ACCESS_READ;
	ID3D11Texture2D *stage = NULL;
	if (FAILED(dev->lpVtbl->CreateTexture2D(dev, &td, NULL, &stage))) { output1->lpVtbl->Release(output1); adapter->lpVtbl->Release(adapter); dxgi_dev->lpVtbl->Release(dxgi_dev); goto done_noadapter; }
	uint8_t *prev = (uint8_t *)malloc((size_t)W * H * 4);
	uint64_t *changes = (uint64_t *)calloc(4096, sizeof(uint64_t));
	IDXGIOutputDuplication *dup = NULL; int nchg = 0, head = 0, have = 0;
	for (;;) {
		if (!dup) {
			if (FAILED(output1->lpVtbl->DuplicateOutput(output1, (IUnknown *)dev, &dup)) || !dup) { Sleep(500); continue; }
		}
		DXGI_OUTDUPL_FRAME_INFO info;
		IDXGIResource *res = NULL;
		HRESULT hr = dup->lpVtbl->AcquireNextFrame(dup, 4, &info, &res);
		if (hr == DXGI_ERROR_WAIT_TIMEOUT) continue;
		if (FAILED(hr)) { dup->lpVtbl->Release(dup); dup = NULL; Sleep(300); continue; }
		if (res) {
			ID3D11Texture2D *tex = NULL;
			if (SUCCEEDED(res->lpVtbl->QueryInterface(res, &IID_ID3D11Texture2D, (void **)&tex)) && tex) {
				RECT wr2; GetWindowRect((HWND)g_hwnd, &wr2);
				int wcx = (wr2.left + wr2.right) / 2, wcy = (wr2.top + wr2.bottom) / 2;
				int sx = wcx - od.DesktopCoordinates.left - W / 2, sy = wcy - od.DesktopCoordinates.top - H / 2;
				int ow = od.DesktopCoordinates.right - od.DesktopCoordinates.left, oh = od.DesktopCoordinates.bottom - od.DesktopCoordinates.top;
				if (sx < 0) sx = 0; if (sy < 0) sy = 0;
				if (sx + W > ow) sx = ow - W; if (sy + H > oh) sy = oh - H;
				D3D11_BOX box; box.left = (UINT)sx; box.top = (UINT)sy; box.front = 0;
				box.right = (UINT)(sx + W); box.bottom = (UINT)(sy + H); box.back = 1;
				ctx->lpVtbl->CopySubresourceRegion(ctx, (ID3D11Resource *)stage, 0, 0, 0, 0, (ID3D11Resource *)tex, 0, &box);
				D3D11_MAPPED_SUBRESOURCE m;
				if (prev && changes && SUCCEEDED(ctx->lpVtbl->Map(ctx, (ID3D11Resource *)stage, 0, D3D11_MAP_READ, 0, &m)) && m.pData) {
					const uint8_t *b = (const uint8_t *)m.pData;
					int changed = 0;
					if (have) {
						int n = 0;
						for (int y = 0; y < H; y++) for (int x = 0; x < W; x++) {
							const uint8_t *p = b + (size_t)y * m.RowPitch + 4 * x, *q = prev + 4 * ((size_t)y * W + x);
							int d = abs((int)p[0] - q[0]) + abs((int)p[1] - q[1]) + abs((int)p[2] - q[2]);
							if (d > 24) n++;
						}
						changed = n > (W * H / 100);
					}
					for (int y = 0; y < H; y++) memcpy(prev + 4 * ((size_t)y * W), b + (size_t)y * m.RowPitch, (size_t)W * 4);
					have = 1;
					ctx->lpVtbl->Unmap(ctx, (ID3D11Resource *)stage, 0);
					uint64_t now = (uint64_t)GetTickCount64() * 1000ull;
					if (changed) { changes[head] = now; head = (head + 1) % 4096; if (nchg < 4096) nchg++; }
					uint64_t cutoff = now - 1000000ull; int in_window = 0;
					for (int k = 0; k < nchg; k++) { int idx = (head - 1 - k + 8192) % 4096; if (changes[idx] >= cutoff) in_window++; else break; }
					InterlockedExchange(&g_fps, in_window);
				}
				tex->lpVtbl->Release(tex);
			}
			res->lpVtbl->Release(res);
		}
		dup->lpVtbl->ReleaseFrame(dup);
	}
	free(prev); free(changes);
	if (dup) dup->lpVtbl->Release(dup);
	if (stage) stage->lpVtbl->Release(stage);
	output1->lpVtbl->Release(output1); adapter->lpVtbl->Release(adapter); dxgi_dev->lpVtbl->Release(dxgi_dev);
done_noadapter:
	if (ctx) ctx->lpVtbl->Release(ctx); if (dev) dev->lpVtbl->Release(dev);
	CoUninitialize();
	return NULL;
}

int dispcap_start(void *hwnd) {
	if (InterlockedCompareExchange(&g_started, 1, 0) != 0) return 0;
	if (!hwnd) return -1;
	g_hwnd = hwnd;
	pthread_t th;
	if (pthread_create(&th, NULL, dispcap_thread, NULL) != 0) return -1;
	pthread_detach(th);
	return 0;
}
#else
int dispcap_start(void *hwnd) { (void)hwnd; return -1; }
int dispcap_fps(void) { return 0; }
#endif
