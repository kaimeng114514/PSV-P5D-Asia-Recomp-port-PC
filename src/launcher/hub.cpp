/*
 * nativ: Project Nativ's launcher, the front door. One window shows the player's games -- every per-game pack
 * (packs/<title>/pack.toml) and every title already under dump/decrypted/ -- as cover-art cards with
 * what state each is in, and runs the pipeline's stages for them: add a game and its update from a player's own
 * copy (a PKG with its licence file, a game folder, or a whole folder searched for them), install the firmware
 * from Sony's update file once, build, play. Each card says which version the copy is and whether its game pack
 * recommends another (the pack's VERSIONS / UPDATE_NOTE: Killzone's 1.12 update brings Botzone and online play).
 * First run (or no firmware yet) opens a short setup: welcome, firmware (with Sony's official download page),
 * games, the online name, ready. The work itself is the existing command line (./vitarecomp): the hub runs it as a
 * child process, shows the step it is on, and keeps its whole output in the activity drawer -- so the command
 * line and the hub never disagree about how a step is done.
 *
 * SDL3 + Dear ImGui on SDL_GPU, the same stack as the in-game overlay (runtime/ui/overlay.cpp). Cover art is the
 * game's own sce_sys/pic0.png and icon0.png (SDL_LoadPNG). Nothing here touches a game's code or data beyond
 * reading param-like facts (the pack's NAME=, which files exist).
 *
 * ATIV_PREFS=<dir>: the launcher's own files and the shared settings there instead of the user's app folder (a test).
 * ATIV_DUMP=<dir>: the library (games, firmware, licences, builds, saves) there instead of the usual one, library_dir (a
 * fresh library to try setup on; the stages it runs inherit it). ATIV_SHOT=f.ppm (a verification aid, no visible window): renders the hub once into f.ppm and exits;
 * ATIV_SHOT_UI=library|setup:<0-4>|add|settings:<0-3>|game:<title>|sac|sac:again picks what is on screen, ATIV_SHOT_SIZE=WxH the size (1280x800),
 * ATIV_SHOT_SCAN=<rows> a folder search's results (vitarecomp scan's output) in the Add dialog.
 * ATIV_TASK=play:<title>|build:<title>|scan:<folder>|licences:<folder>|firmware:<file> (a verification aid, no window): that
 * task run as its button runs it, its log printed, the exit status its outcome; ATIV_TASK_CANCEL=<seconds>: Cancel then.
 */
#include "imgui.h"
#include "backends/imgui_impl_sdl3.h"
#include "backends/imgui_impl_sdlgpu3.h"
#include "ui_theme.h"   /* the look shared with the in-game overlay */
#include <ctime>
#include <SDL3/SDL.h>
#include <algorithm>
#include <atomic>
#include <cctype>
#include <cmath>
#include <csignal>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <strings.h>
#include <dirent.h>
#include <fcntl.h>
#include <map>
#include <random>
#include <mutex>
#include <string>
#include <sys/stat.h>
#include <thread>
#include <vector>
#ifdef _WIN32
#define WIN32_LEAN_AND_MEAN
#define NOMINMAX
#include <windows.h>
#include <shellapi.h>   /* ShellExecuteA: the frame-generation panel opens NVIDIA App (M1645) */
#include <tlhelp32.h>   /* M1788: the Steam-running check before writing shortcuts.vdf */
#include <objbase.h>    /* CoInitializeEx/CoCreateInstance: the folder chooser (M1732) */
#include <shobjidl.h>   /* IFileOpenDialog: choosing where the game files live (M1732) */
#include <direct.h>
#include <io.h>
#else
#include <sys/wait.h>
#include <unistd.h>
#endif
#ifdef __APPLE__
#include <sys/mount.h>
#include <sys/xattr.h>
#endif

#ifndef REPO_ROOT
#define REPO_ROOT "."
#endif
static bool p5d_mode(void);              /* the P5D single-page front (P5D_LAUNCHER / a release build) */
static void p5d_ui(SDL_Window *win);
static int p5d_res_index(void);
static void p5d_start_play(int res);
static int p5d_build_stale(void);
static std::string library_dir(void);          /* (defined below: the library path, prefs p5d_libdir) */
static std::string library_default_dir(void);  /* (the default folder shown in Settings -> Storage) */
static std::atomic<bool> g_move_running{false}, g_move_ok{false}, g_move_finished{false};   /* M1736: library copy state */
static std::string g_move_to, g_move_error;
static bool g_move_clear_pref;   /* M1743: the move target is the default folder (clear p5d_libdir) */
static void change_game_folder(void);           /* M1736: pick a folder, move the existing library there, then switch */
static void change_to_default_folder(void);     /* M1743: move the library back to the default folder */
static void game_folder_move_poll(void);       /* M1736: finish a running library move */
static SDL_Window *g_hub_win;   /* the launcher's window: it gets out of the game's way (and out of its keyboard's) while the game runs */
static std::string g_root = REPO_ROOT;   /* the repository (ATIV_ROOT overrides; else found from where the launcher is) */
static std::string g_dump;               /* the player's library: games, firmware, licences, builds, saves (library_dir) */
static const char *const SONY_FIRMWARE_PAGE = "https://www.playstation.com/en-us/support/hardware/psvita/system-software/";
static const char *const SUPPORT_PAGE = "https://ko-fi.com/kingtorro";   /* (a tip jar for the work: nothing is sold or held back) */

static bool exists(const std::string &p) { struct stat st; return stat(p.c_str(), &st) == 0; }
#ifdef _WIN32   /* (paths are UTF-8 throughout: the launcher's manifest sets the process code page, launcher/nativ.manifest) */
static void make_dir(const std::string &p) { _mkdir(p.c_str()); }
static void set_env(const char *k, const std::string &v) { _putenv_s(k, v.c_str()); }
static std::wstring wide(const std::string &s) {
	int n = MultiByteToWideChar(CP_UTF8, 0, s.c_str(), (int)s.size(), nullptr, 0);
	std::wstring w((size_t)n, L'\0'); if (n) MultiByteToWideChar(CP_UTF8, 0, s.c_str(), (int)s.size(), &w[0], n);
	return w;
}
static std::string narrow(const std::wstring &w) {
	int n = WideCharToMultiByte(CP_UTF8, 0, w.c_str(), (int)w.size(), nullptr, 0, nullptr, nullptr);
	std::string s((size_t)n, '\0'); if (n) WideCharToMultiByte(CP_UTF8, 0, w.c_str(), (int)w.size(), &s[0], n, nullptr, nullptr);
	return s;
}
/* M1732: the native folder picker (folders only); "" = cancelled. */
static std::string pick_folder_dialog(const std::string &initial) {
	std::string out;
	CoInitializeEx(nullptr, COINIT_APARTMENTTHREADED | COINIT_DISABLE_OLE1DDE);
	IFileOpenDialog *dlg = nullptr;
	if (SUCCEEDED(CoCreateInstance(CLSID_FileOpenDialog, nullptr, CLSCTX_INPROC_SERVER, IID_PPV_ARGS(&dlg)))) {
		DWORD opts = 0; dlg->GetOptions(&opts);
		dlg->SetOptions(opts | FOS_PICKFOLDERS | FOS_FORCEFILESYSTEM | FOS_PATHMUSTEXIST);
		dlg->SetTitle(L"Where should the game files live?");
		if (!initial.empty()) { IShellItem *it = nullptr; if (SUCCEEDED(SHCreateItemFromParsingName(wide(initial).c_str(), nullptr, IID_PPV_ARGS(&it)))) { dlg->SetFolder(it); it->Release(); } }
		if (SUCCEEDED(dlg->Show(nullptr))) {
			IShellItem *it = nullptr;
			if (SUCCEEDED(dlg->GetResult(&it))) { PWSTR w = nullptr; if (SUCCEEDED(it->GetDisplayName(SIGDN_FILESYSPATH, &w))) { out = narrow(std::wstring(w)); CoTaskMemFree(w); } it->Release(); }
		}
		dlg->Release();
	}
	CoUninitialize();
	return out;
}
#else
static std::string narrow(const std::wstring &) { return ""; }
static std::string pick_folder_dialog(const std::string &) { return ""; }   /* (the shell folder picker is Windows-only) */
static void make_dir(const std::string &p) { mkdir(p.c_str(), 0755); }
static void set_env(const char *k, const std::string &v) { setenv(k, v.c_str(), 1); }
#endif
#ifdef _WIN32
/* ---- M1651: the AI-interpolation profile repair ----------------------------------------------------------------
 * NVIDIA App stores its Smooth Motion ("AI 插帧") toggle in a driver profile named after the executable. For this game its
 * own "add application" step fails (CxNative log: "Failed to get app metadata: m_AddManualApplication failed with 7") and
 * leaves the profile's only application entry as a broken path ("c:/users/"), so the profile never matches the running
 * game and the driver's frame interpolation never engages. The launcher repairs that entry through NVAPI DRS: add an
 * application named "game_host_min.exe" to the existing profile and save it. Measured on this machine (30 fps dance
 * stage, external capture probe): 29.8 distinct pictures/s before the repair, 55.2 after. */
typedef unsigned int NvU32R; typedef unsigned short NvU16R; typedef unsigned long long NvU64R; typedef float NvF32R;
typedef int NvAPI_StatusR;
#define NVAPI_USTR_MAX 2048
#define NVAPI_BIN_MAX 4096
typedef NvU16R NvAPI_UnicodeStringR[NVAPI_USTR_MAX];
typedef struct { NvU32R valueLength; unsigned char valueData[NVAPI_BIN_MAX]; } NVDRS_BINARY_SETTING_R;
#pragma pack(push, 4)
typedef struct { NvU32R version; NvAPI_UnicodeStringR settingName; NvU32R settingId; NvU32R settingType; NvU32R settingLocation;
	NvU32R isCurrentPredefined; NvU32R isPredefinedValid;
	union { NvU32R u32PredefinedValue; NVDRS_BINARY_SETTING_R binaryPredefinedValue; NvAPI_UnicodeStringR wszPredefinedValue; NvU64R u64PredefinedValue; NvF32R f32PredefinedValue; } predefined;
	union { NvU32R u32CurrentValue; NVDRS_BINARY_SETTING_R binaryCurrentValue; NvAPI_UnicodeStringR wszCurrentValue; NvU64R u64CurrentValue; NvF32R f32CurrentValue; } current;
} NVDRS_SETTING_R;
typedef struct { NvU32R version; NvAPI_UnicodeStringR profileName; NvU32R gpuSupport; NvU32R isPredefined; NvU32R numOfApps; NvU32R numOfSettings; } NVDRS_PROFILE_R;
typedef struct { NvU32R version; NvU32R isPredefined; NvAPI_UnicodeStringR appName; NvAPI_UnicodeStringR userFriendlyName;
	NvAPI_UnicodeStringR launcher; NvAPI_UnicodeStringR fileInFolder; NvU32R flags; NvAPI_UnicodeStringR commandLine; } NVDRS_APPLICATION_R;
#pragma pack(pop)
#define NVVER_R(t, v) ((NvU32R)(sizeof(t) | ((v) << 16)))
typedef void *(*P5DNvQi)(NvU32R);
static void p5d_nv_setw(NvAPI_UnicodeStringR dst, const wchar_t *s) { wcsncpy_s((wchar_t *)dst, NVAPI_USTR_MAX, s, _TRUNCATE); }
static std::string g_fgx_note;   /* the ⑦ panel's driver-file status line */
static bool p5d_repair_fgx_profile(std::string *detail) {
	HMODULE h = LoadLibraryA("nvapi64.dll");
	if (!h) { if (detail) *detail = "no nvapi64.dll"; return false; }
	auto qi = (P5DNvQi)GetProcAddress(h, "nvapi_QueryInterface");
	if (!qi) { if (detail) *detail = "no nvapi_QueryInterface"; return false; }
	auto Initialize = (NvAPI_StatusR (*)())qi(0x0150e828);
	auto CreateSession = (NvAPI_StatusR (*)(void **))qi(0x0694d52e);
	auto LoadSettings = (NvAPI_StatusR (*)(void *))qi(0x375dbd6b);
	auto SaveSettings = (NvAPI_StatusR (*)(void *))qi(0xfcbc7e14);
	auto FindProfileByName = (NvAPI_StatusR (*)(void *, NvAPI_UnicodeStringR, void **))qi(0x7e4a9a0b);
	auto EnumApplications = (NvAPI_StatusR (*)(void *, void *, NvU32R, NvU32R *, NVDRS_APPLICATION_R *))qi(0x7fa2173a);
	auto CreateApplication = (NvAPI_StatusR (*)(void *, void *, NVDRS_APPLICATION_R *))qi(0x4347a9de);
	if (!Initialize || !CreateSession || !LoadSettings || !SaveSettings || !FindProfileByName || !EnumApplications || !CreateApplication) {
		if (detail) *detail = "nvapi entry points missing"; return false;
	}
	if (Initialize() != 0) { if (detail) *detail = "NvAPI_Initialize failed"; return false; }
	void *sess = nullptr; if (CreateSession(&sess) != 0 || !sess) { if (detail) *detail = "session failed"; return false; }
	LoadSettings(sess);
	NvAPI_UnicodeStringR pn;
	{ const char *ov = getenv("P5D_FGX_PROFILE");
	  if (ov && *ov) { int n = MultiByteToWideChar(CP_UTF8, 0, ov, -1, nullptr, 0); if (n > 1 && n <= NVAPI_USTR_MAX) MultiByteToWideChar(CP_UTF8, 0, ov, -1, (wchar_t *)pn, n); else p5d_nv_setw(pn, L"game_host_min.exe"); }
	  else p5d_nv_setw(pn, L"game_host_min.exe"); }
	void *prof = nullptr;
	if (FindProfileByName(sess, pn, &prof) != 0 || !prof) {
		if (detail) *detail = "no AI 插帧 profile yet (enable AI 插帧 for this program in NVIDIA App once)";
		return false;
	}
	bool have = false;
	for (NvU32R k = 0; k < 16; k++) {
		NVDRS_APPLICATION_R *a = (NVDRS_APPLICATION_R *)calloc(1, sizeof(NVDRS_APPLICATION_R) + 4096);
		if (!a) break;
		a->version = NVVER_R(NVDRS_APPLICATION_R, 4);
		NvU32R cnt = 1;
		if (EnumApplications(sess, prof, k, &cnt, a) != 0) { free(a); break; }
		const wchar_t *n = (const wchar_t *)a->appName;
		if (wcsstr(n, L"game_host_min.exe")) have = true;
		free(a);
	}
	if (have) { if (detail) *detail = "driver file OK"; return false; }
	NVDRS_APPLICATION_R *na = (NVDRS_APPLICATION_R *)calloc(1, sizeof(NVDRS_APPLICATION_R) + 4096);
	if (!na) { if (detail) *detail = "out of memory"; return false; }
	na->version = NVVER_R(NVDRS_APPLICATION_R, 4);
	p5d_nv_setw(na->appName, L"game_host_min.exe");
	p5d_nv_setw(na->userFriendlyName, L"Persona 5 Dancing in Starlight");
	NvAPI_StatusR st = CreateApplication(sess, prof, na);
	free(na);
	if (st == 0) {
		SaveSettings(sess);
		if (detail) *detail = "driver file repaired (NVIDIA App had written a broken application path)";
		return true;
	}
	if (detail) *detail = "driver file repair failed";
	return false;
}
#else
static std::string g_fgx_note;
static bool p5d_repair_fgx_profile(std::string *detail) { (void)detail; return false; }
#endif

static std::string shown_args(const std::vector<std::string> &argv) {   /* a command for the log: words with spaces quoted */
	std::string s;
	for (const std::string &a : argv) { if (!s.empty()) s += ' '; s += a.empty() || a.find_first_of(" \t\"'") != std::string::npos ? "\"" + a + "\"" : a; }
	return s;
}
/* the stages' command line (pipeline/vitarecomp.py) on the repository's Python: its virtualenv, else one installed beside the
 * launcher (<root>/python: Windows' and the self-contained Linux install's), else the system's */
static std::string python_exe(void) {   /* P5D_PYTHON: the packaged runtime's interpreter, when the single-exe wrapper names it */
	if (const char *p = getenv("P5D_PYTHON")) if (*p) return p;
#ifdef _WIN32
	for (const char *p : {"/.venv/Scripts/python.exe", "/python/python.exe"}) if (exists(g_root + p)) return g_root + p;
	return "python";
#else
	for (const char *p : {"/.venv/bin/python", "/python/bin/python3"}) if (exists(g_root + p)) return g_root + p;   /* (an install's: <root>/python) */
	return "python3";
#endif
}
static std::vector<std::string> vitarecomp(std::initializer_list<std::string> args) {
	std::vector<std::string> v{python_exe(), g_root + "/pipeline/vitarecomp.py"};
	v.insert(v.end(), args);
	return v;
}
static std::vector<std::string> vitarecomp(const std::vector<std::string> &args) {
	std::vector<std::string> v{python_exe(), g_root + "/pipeline/vitarecomp.py"};
	v.insert(v.end(), args.begin(), args.end());
	return v;
}
static void open_folder(const std::string &p) {
#ifdef _WIN32
	/* M1733: not SDL_OpenURL -- it blocked the launcher's UI thread while the shell processed the open verb (the
	 * "打開文件夾" button froze the window). ShellExecuteW only starts the shell and returns; the same call the game
	 * helper p5d_open_path uses. A missing folder would make the shell show its own error dialog: create it first. */
	make_dir(p);
	ShellExecuteW(nullptr, L"open", wide(p).c_str(), nullptr, nullptr, SW_SHOWNORMAL);
#else
	SDL_OpenURL(("file://" + p).c_str());
#endif
}

/* ---- textures: the games' own PNGs, uploaded once */
struct Tex { SDL_GPUTexture *t = nullptr; int w = 0, h = 0; };
static SDL_GPUDevice *g_gpu;
static std::map<std::string, Tex> g_tex;
static Tex texture(const std::string &path) {
	auto it = g_tex.find(path);
	if (it != g_tex.end()) return it->second;
	Tex x;
	SDL_Surface *s = exists(path) ? SDL_LoadPNG(path.c_str()) : nullptr;
	SDL_Surface *r = s ? SDL_ConvertSurface(s, SDL_PIXELFORMAT_ABGR8888) : nullptr;   /* bytes R, G, B, A */
	if (s) SDL_DestroySurface(s);
	if (r && g_gpu) {
		SDL_GPUTextureCreateInfo ci = {};
		ci.type = SDL_GPU_TEXTURETYPE_2D; ci.format = SDL_GPU_TEXTUREFORMAT_R8G8B8A8_UNORM; ci.usage = SDL_GPU_TEXTUREUSAGE_SAMPLER;
		ci.width = (Uint32)r->w; ci.height = (Uint32)r->h; ci.layer_count_or_depth = 1; ci.num_levels = 1;
		SDL_GPUTransferBufferCreateInfo tc = {}; tc.usage = SDL_GPU_TRANSFERBUFFERUSAGE_UPLOAD; tc.size = (Uint32)(r->w * r->h * 4);
		SDL_GPUTexture *t = SDL_CreateGPUTexture(g_gpu, &ci);
		SDL_GPUTransferBuffer *tb = SDL_CreateGPUTransferBuffer(g_gpu, &tc);
		if (t && tb) {
			uint8_t *dst = (uint8_t *)SDL_MapGPUTransferBuffer(g_gpu, tb, false);
			for (int y = 0; dst && y < r->h; y++) memcpy(dst + (size_t)y * r->w * 4, (uint8_t *)r->pixels + (size_t)y * r->pitch, (size_t)r->w * 4);
			SDL_UnmapGPUTransferBuffer(g_gpu, tb);
			SDL_GPUCommandBuffer *cb = SDL_AcquireGPUCommandBuffer(g_gpu);
			SDL_GPUCopyPass *cp = SDL_BeginGPUCopyPass(cb);
			SDL_GPUTextureTransferInfo src = {}; src.transfer_buffer = tb; src.pixels_per_row = (Uint32)r->w; src.rows_per_layer = (Uint32)r->h;
			SDL_GPUTextureRegion dr = {}; dr.texture = t; dr.w = (Uint32)r->w; dr.h = (Uint32)r->h; dr.d = 1;
			SDL_UploadToGPUTexture(cp, &src, &dr, false);
			SDL_EndGPUCopyPass(cp); SDL_SubmitGPUCommandBuffer(cb);
			x.t = t; x.w = r->w; x.h = r->h;
		} else if (t) SDL_ReleaseGPUTexture(g_gpu, t);
		if (tb) SDL_ReleaseGPUTransferBuffer(g_gpu, tb);
	}
	if (r) SDL_DestroySurface(r);
	g_tex[path] = x;
	return x;
}
static ImTextureRef tex_ref(const Tex &t) { return ImTextureRef((ImTextureID)(intptr_t)t.t); }

/* ---- MODs (M1664): Reloaded-II folder mods under <library>/decrypted/PCSH10109/recomp/mods.
 * A mod is a folder with Mod.xml (Id/Title/Author/Version/Description) and a Data/ tree whose files replace the
 * game's same-named resources (the runtime applies that; the launcher imports, lists, and remembers each one's switch). */
struct P5dMod { std::string dir, title, author, version, desc, cover; bool enabled = false; };
static std::string mods_root(void) { return g_dump + "/decrypted/PCSH10109/recomp/mods"; }
static std::string mod_field(const std::string &xml, const char *tag) {
	std::string open = std::string("<") + tag + ">", close = std::string("</") + tag + ">";
	size_t a = xml.find(open); if (a == std::string::npos) return "";
	a += open.size(); size_t b = xml.find(close, a); if (b == std::string::npos) return "";
	return xml.substr(a, b - a);
}
static std::string path_base(const std::string &p) { size_t i = p.find_last_of("/\\"); return i == std::string::npos ? p : p.substr(i + 1); }
static void mods_scan(std::vector<P5dMod> &out) {
	out.clear();
	std::string root = mods_root();
	std::map<std::string, bool> en;
	{ FILE *f = fopen((root + "/mods.ini").c_str(), "rb"); if (f) { char line[512];
		while (fgets(line, sizeof line, f)) { std::string t = line; while (!t.empty() && (t.back() == '\n' || t.back() == '\r' || t.back() == ' ')) t.pop_back();
			if (t.rfind("enabled=", 0) == 0) en[t.substr(8)] = true; } fclose(f); } }
	DIR *d = opendir(root.c_str()); if (!d) return;
	while (struct dirent *e = readdir(d)) {
		std::string nm = e->d_name; if (nm == "." || nm == "..") continue;
		std::string dir = root + "/" + nm; struct stat st;
		if (stat(dir.c_str(), &st) != 0 || !(st.st_mode & S_IFDIR)) continue;
		P5dMod m; m.dir = dir; m.title = nm; m.enabled = en.count(nm) > 0;
		{ FILE *f = fopen((dir + "/Mod.xml").c_str(), "rb");
		  if (f) { std::string xml; char buf[4096]; size_t n;
			while ((n = fread(buf, 1, sizeof buf, f)) > 0) xml.append(buf, n); fclose(f);
			std::string t = mod_field(xml, "Title"); if (!t.empty()) m.title = t;
			m.author = mod_field(xml, "Author"); m.version = mod_field(xml, "Version"); m.desc = mod_field(xml, "Description"); } }
		{ DIR *md = opendir(dir.c_str()); std::string best;
		  if (md) { while (struct dirent *ce = readdir(md)) { std::string cn = ce->d_name, lower = cn;
				for (auto &c : lower) c = (char)tolower((unsigned char)c);
				if (lower.size() > 4 && (lower.substr(lower.size() - 4) == ".png" || lower.substr(lower.size() - 4) == ".jpg")) {
					if (lower.find("cover") != std::string::npos || lower.find("preview") != std::string::npos) { best = cn; break; }
					if (best.empty()) best = cn; } } closedir(md); }
		  if (!best.empty()) m.cover = dir + "/" + best; }
		out.push_back(m);
	}
	closedir(d);
}
static bool mods_delete_tree(const std::string &p) {   /* M1749: 撤销导入：删掉整份 MOD 文件 */
	DIR *d = opendir(p.c_str());
	if (!d) return remove(p.c_str()) == 0;
	bool ok = true;
	while (struct dirent *e = readdir(d)) {
		if (!strcmp(e->d_name, ".") || !strcmp(e->d_name, "..")) continue;
		const std::string a = p + "/" + e->d_name; struct stat st;
		if (stat(a.c_str(), &st) != 0) { ok = false; continue; }
		if (S_ISDIR(st.st_mode)) ok = mods_delete_tree(a) && ok;
		else ok = (remove(a.c_str()) == 0) && ok;
	}
	closedir(d);
	if (rmdir(p.c_str()) != 0) ok = false;
	return ok;
}
static void mods_save(const std::vector<P5dMod> &v) {
	std::string root = mods_root(); make_dir(root.c_str());
	FILE *f = fopen((root + "/mods.ini").c_str(), "wb"); if (!f) return;
	for (const auto &m : v) if (m.enabled) fprintf(f, "enabled=%s\n", path_base(m.dir).c_str());
	fclose(f);
}
static void mods_copy_tree(const std::string &src, const std::string &dst) {   /* (no <filesystem>: win32_compat.h's sync macro) */
	make_dir(dst.c_str());
	DIR *d = opendir(src.c_str()); if (!d) return;
	while (struct dirent *e = readdir(d)) { std::string nm = e->d_name; if (nm == "." || nm == "..") continue;
		std::string sp = src + "/" + nm, dp = dst + "/" + nm; struct stat st;
		if (stat(sp.c_str(), &st) != 0) continue;
		if (st.st_mode & S_IFDIR) mods_copy_tree(sp, dp);
		else { FILE *in = fopen(sp.c_str(), "rb"); if (!in) continue; FILE *out = fopen(dp.c_str(), "wb");
			if (!out) { fclose(in); continue; }
			char buf[65536]; size_t n; while ((n = fread(buf, 1, sizeof buf, in)) > 0) fwrite(buf, 1, n, out);
			fclose(in); fclose(out); } }
	closedir(d);
}
static void mods_import(const std::string &src) {
	std::string base = path_base(src); std::string root = mods_root(); make_dir(root.c_str());
	mods_copy_tree(src, root + "/" + base);
	fprintf(stderr, "mods: imported %s as %s\n", src.c_str(), base.c_str());
}

/* the app icon on the window (and the Dock / taskbar): assets/brand's, macOS's drawn on its own inset grid */
static void window_icon(SDL_Window *win) {   /* the port's own icon (assets/p5d), the old brand only as a fallback */
	const char *cands[] = {"/assets/p5d/png/icon-256.png", "/assets/p5d/png/icon-512.png",
	                       "/assets/brand/png/icon-256.png", nullptr};
	for (int i = 0; cands[i]; i++) {
		std::string png = g_root + cands[i];
		if (!exists(png)) continue;
		if (SDL_Surface *s = SDL_LoadPNG(png.c_str())) { SDL_SetWindowIcon(win, s); SDL_DestroySurface(s); return; }
	}
}

/* ---- the user's settings (the platform's per-user app folder, or ATIV_PREFS=<dir>: a test's): setup finished, the
 * drawer's state (launcher.ini); a folder search's results (scan.tsv); the settings every game reads (settings.ini) */
static std::string pref_dir(void) {
	if (const char *d = getenv("ATIV_PREFS")) { make_dir(d); return std::string(d) + "/"; }
	char *p = SDL_GetPrefPath("P5D-Port", "P5D");
	std::string s = p ? p : "";
	SDL_free(p);
	return s;
}
static std::map<std::string, std::string> g_prefs;
static std::string prefs_path(void) { std::string d = pref_dir(); return d.empty() ? "" : d + "launcher.ini"; }
static void prefs_load(void) {
	FILE *f = fopen(prefs_path().c_str(), "r"); if (!f) return;
	char line[512];
	while (fgets(line, sizeof line, f)) {
		char *eq = strchr(line, '='); if (!eq) continue;
		*eq = 0; std::string v = eq + 1; while (!v.empty() && (v.back() == '\n' || v.back() == '\r')) v.pop_back();
		g_prefs[line] = v;
	}
	fclose(f);
}
static void prefs_set(const char *k, const std::string &v) {
	g_prefs[k] = v;
	std::string p = prefs_path(); if (p.empty()) return;
	FILE *f = fopen(p.c_str(), "w"); if (!f) return;
	for (auto &kv : g_prefs) fprintf(f, "%s=%s\n", kv.first.c_str(), kv.second.c_str());
	fclose(f);
}
static void prefs_erase(const char *k) {   /* M1786: drop a key (the remembered ROM folder after 撤銷導入) */
	g_prefs.erase(k);
	std::string p = prefs_path(); if (p.empty()) return;
	FILE *f = fopen(p.c_str(), "w"); if (!f) return;
	for (auto &kv : g_prefs) fprintf(f, "%s=%s\n", kv.first.c_str(), kv.second.c_str());
	fclose(f);
}

#ifdef _WIN32
/* ---- M1788: 「添加到 Steam 庫」 -- append one non-Steam shortcut to
 *      <steam>/userdata/<account>/config/shortcuts.vdf
 * That file is Valve's BINARY KeyValues: 0x00 object "name"\0 children 0x08; 0x01 string; 0x02 int32; 0x07 uint64.
 * The shortcut's Exe is wscript.exe and its LaunchOptions a stable .vbs which runs the newest extracted launcher:
 * launcher updates (a new extraction folder) therefore cannot break the Steam entry, and the desktop launcher keeps
 * working unchanged -- both start the same program.
 * Steam REWRITES shortcuts.vdf when it exits, so the add only runs while Steam is closed; the existing file is backed
 * up (shortcuts.vdf.bak) and only appended to (unknown fields are preserved untouched).
 * Env overrides used by the headless self test: P5D_STEAM_DIR (steam install), P5D_STEAM_STUB_DIR (where the .vbs
 * goes), P5D_STEAM_ADD=1 (run the add once, no window) and P5D_STEAM_ADD_OUT (write the result there). */
static uint32_t steam_crc32(const std::string &s) {
	static uint32_t t[256]; static bool init;
	if (!init) { init = true; for (uint32_t i = 0; i < 256; i++) { uint32_t c = i; for (int k = 0; k < 8; k++) c = (c & 1u) ? (0xEDB88320u ^ (c >> 1)) : (c >> 1); t[i] = c; } }
	uint32_t c = 0xFFFFFFFFu;
	for (unsigned char ch : s) c = t[(c ^ ch) & 0xFFu] ^ (c >> 8);
	return c ^ 0xFFFFFFFFu;
}
static std::string steam_reg(HKEY root, const char *sub, const char *val) {
	char buf[2048]; DWORD n = sizeof buf, type = 0;
	if (RegGetValueA(root, sub, val, RRF_RT_REG_SZ, &type, buf, &n) != ERROR_SUCCESS) return "";
	std::string s = buf; for (char &c : s) if (c == '/') c = '\\';
	return s;
}
static bool steam_running(void) {
	HANDLE sn = CreateToolhelp32Snapshot(TH32CS_SNAPPROCESS, 0);
	if (sn == INVALID_HANDLE_VALUE) return false;
	PROCESSENTRY32 pe; pe.dwSize = sizeof pe; bool run = false;
	if (Process32First(sn, &pe)) do { if (!_stricmp(pe.szExeFile, "steam.exe")) { run = true; break; } } while (Process32Next(sn, &pe));
	CloseHandle(sn);
	return run;
}
static std::string steam_read_all(const std::string &p) {
	std::string b; FILE *f = fopen(p.c_str(), "rb"); if (!f) return b;
	char buf[65536]; size_t n; while ((n = fread(buf, 1, sizeof buf, f)) > 0) b.append(buf, n);
	fclose(f);
	return b;
}
static void steam_mkdirs(const std::string &p) {
	for (size_t i = 1; i <= p.size(); i++)
		if (i == p.size() || p[i] == '\\' || p[i] == '/') {
			std::string d = p.substr(0, i);
			if (!d.empty() && !exists(d)) make_dir(d);
		}
}
static void steam_box_blur(SDL_Surface *s, int r, int passes) {   /* RGBA32 only; a cheap blur for the fill behind the art */
	if (!s || s->format != SDL_PIXELFORMAT_RGBA32 || r < 1) return;
	const int w = s->w, h = s->h;
	std::vector<Uint8> tmp((size_t)w * h * 4);
	for (int p = 0; p < passes; p++) {
		SDL_LockSurface(s);
		Uint8 *px = (Uint8 *)s->pixels;
		const size_t pitch = (size_t)s->pitch;
		for (int y = 0; y < h; y++) {
			Uint8 *row = px + y * pitch;
			for (int x = 0; x < w; x++) {
				int acc[3] = {0, 0, 0}, n = 0;
				const int x0 = std::max(0, x - r), x1 = std::min(w - 1, x + r);
				for (int i = x0; i <= x1; i++) { acc[0] += row[i * 4]; acc[1] += row[i * 4 + 1]; acc[2] += row[i * 4 + 2]; n++; }
				tmp[((size_t)y * w + x) * 4 + 0] = (Uint8)(acc[0] / n); tmp[((size_t)y * w + x) * 4 + 1] = (Uint8)(acc[1] / n); tmp[((size_t)y * w + x) * 4 + 2] = (Uint8)(acc[2] / n); tmp[((size_t)y * w + x) * 4 + 3] = row[x * 4 + 3];
			}
		}
		for (int y = 0; y < h; y++) memcpy(px + (size_t)y * pitch, &tmp[(size_t)y * w * 4], (size_t)w * 4);
		for (int x = 0; x < w; x++) {
			for (int y = 0; y < h; y++) {
				int acc[3] = {0, 0, 0}, n = 0;
				const int y0 = std::max(0, y - r), y1 = std::min(h - 1, y + r);
				for (int i = y0; i <= y1; i++) { const Uint8 *q = px + (size_t)i * pitch + x * 4; acc[0] += q[0]; acc[1] += q[1]; acc[2] += q[2]; n++; }
				tmp[((size_t)y * w + x) * 4 + 0] = (Uint8)(acc[0] / n); tmp[((size_t)y * w + x) * 4 + 1] = (Uint8)(acc[1] / n); tmp[((size_t)y * w + x) * 4 + 2] = (Uint8)(acc[2] / n); tmp[((size_t)y * w + x) * 4 + 3] = px[(size_t)y * pitch + x * 4 + 3];
			}
		}
		for (int y = 0; y < h; y++) memcpy(px + (size_t)y * pitch, &tmp[(size_t)y * w * 4], (size_t)w * 4);
		SDL_UnlockSurface(s);
	}
}
/* binary VDF: skip one value of the given type (objects recurse), advancing p past it */
static bool steam_vdf_skip(const std::string &b, size_t &p, uint8_t type) {
	switch (type) {
	case 0x01: while (p < b.size() && b[p]) p++; p++; return p <= b.size();
	case 0x02: case 0x03: case 0x04: case 0x06: p += 4; return p <= b.size();
	case 0x07: case 0x0A: p += 8; return p <= b.size();
	case 0x00: {
		while (true) {
			if (p >= b.size()) return false;
			uint8_t t = (uint8_t)b[p++];
			if (t == 0x08) return true;
			while (p < b.size() && b[p]) p++;
			if (p >= b.size()) return false;
			p++;   /* the key's NUL */
			if (!steam_vdf_skip(b, p, t)) return false;
		}
	}
	default: return false;
	}
}
static void steam_vdf_puts(std::string &o, const char *k, const std::string &v) {
	o += '\x01'; o += k; o += '\0'; o += v; o += '\0';
}
static void steam_vdf_puti(std::string &o, const char *k, int32_t v) {
	o += '\x02'; o += k; o += '\0'; o.append((const char *)&v, 4);
}
static std::string steam_shortcut_entry(int idx, const std::string &name, const std::string &exe, const std::string &start, const std::string &args, uint32_t appid) {
	std::string e; e += '\x00'; e += std::to_string(idx); e += '\0';
	steam_vdf_puti(e, "appid", (int32_t)appid);
	steam_vdf_puts(e, "AppName", name);
	steam_vdf_puts(e, "Exe", exe);
	steam_vdf_puts(e, "StartDir", start);
	steam_vdf_puts(e, "icon", "");
	steam_vdf_puts(e, "ShortcutPath", "");
	steam_vdf_puts(e, "LaunchOptions", args);
	steam_vdf_puti(e, "IsHidden", 0);
	steam_vdf_puti(e, "AllowDesktopConfig", 1);
	steam_vdf_puti(e, "AllowOverlay", 1);
	steam_vdf_puti(e, "OpenVR", 0);
	steam_vdf_puti(e, "Devkit", 0);
	steam_vdf_puts(e, "DevkitGameID", "");
	steam_vdf_puti(e, "LastPlayTime", 0);
	e += '\x08';
	return e;
}
static bool steam_write_all(const std::string &p, const std::string &b) {
	std::string tmp = p + ".tmp";
	FILE *f = fopen(tmp.c_str(), "wb");
	if (!f) return false;
	size_t w = fwrite(b.data(), 1, b.size(), f);
	if (fclose(f) != 0 || w != b.size()) { remove(tmp.c_str()); return false; }
	return MoveFileExA(tmp.c_str(), p.c_str(), MOVEFILE_REPLACE_EXISTING) != 0;
}
/* append one entry to an existing shortcuts.vdf (or create one); false + why on a malformed file */
static bool steam_vdf_append(const std::string &path, const std::string &entry, int &count, std::string &why) {
	std::string b = steam_read_all(path);
	size_t insert_at; count = 0;
	if (b.empty()) {   /* a fresh file: 0x00 "shortcuts"\0 0x08 */
		b = std::string("\x00" "shortcuts" "\0", 11);
		insert_at = b.size();
	} else {
		size_t p = 0;
		if (b.size() < 2 || (uint8_t)b[p++] != 0x00) { why = "shortcuts.vdf 不是二進位 VDF"; return false; }
		size_t ks = p; while (p < b.size() && b[p]) p++;
		if (p >= b.size()) { why = "shortcuts.vdf 損壞（標題）"; return false; }
		if (b.compare(ks, p - ks, "shortcuts") != 0) { why = "shortcuts.vdf 沒有 shortcuts 節點"; return false; }
		p++;   /* key NUL */
		while (true) {
			if (p >= b.size()) { why = "shortcuts.vdf 損壞（尾端）"; return false; }
			uint8_t t = (uint8_t)b[p++];
			if (t == 0x08) { insert_at = p - 1; break; }
			while (p < b.size() && b[p]) p++;
			if (p >= b.size()) { why = "shortcuts.vdf 損壞（鍵）"; return false; }
			p++;
			count++;
			if (!steam_vdf_skip(b, p, t)) { why = "shortcuts.vdf 含有不支援的欄位"; return false; }
		}
	}
	if (!b.empty()) {
		FILE *src = fopen(path.c_str(), "rb");
		if (src) { std::string bak = path + ".bak"; FILE *dst = fopen(bak.c_str(), "wb"); if (dst) { char buf[65536]; size_t n; while ((n = fread(buf, 1, sizeof buf, src)) > 0) fwrite(buf, 1, n, dst); fclose(dst); } fclose(src); }
	}
	std::string out = b.substr(0, insert_at) + entry + b.substr(insert_at);
	if (!steam_write_all(path, out)) { why = "寫入 shortcuts.vdf 失敗（權限？Steam 正在執行？）"; return false; }
	return true;
}
/* the stable entry point: run the newest extracted launcher, wherever the payload put it */
static std::string steam_write_stub(const std::string &dir) {
	steam_mkdirs(dir);
	const std::string vbs = dir + "\\P5D Launcher.vbs";
	const char *script =
		"' P5D port: start the newest extracted launcher (Steam shortcut entry; the desktop launcher keeps working).\r\n"
		"Option Explicit\r\n"
		"Dim fso, sh, base, d, f, n, newest, newestPath\r\n"
		"Set fso = CreateObject(\"Scripting.FileSystemObject\")\r\n"
		"Set sh = CreateObject(\"WScript.Shell\")\r\n"
		"base = sh.ExpandEnvironmentStrings(\"%LOCALAPPDATA%\") & \"\\P5D-Port\"\r\n"
		"newestPath = \"\"\r\n"
		"If fso.FolderExists(base) Then\r\n"
		"  For Each d In fso.GetFolder(base).SubFolders\r\n"
		"    For Each f In d.Files\r\n"
		"      n = LCase(f.Name)\r\n"
		"      If Left(n, 4) = \"p5d \" And Right(n, 4) = \".exe\" And InStr(n, \"bak\") = 0 Then\r\n"
		"        If newestPath = \"\" Then\r\n"
		"          newestPath = f.Path : newest = f.DateLastModified\r\n"
		"        ElseIf f.DateLastModified > newest Then\r\n"
		"          newestPath = f.Path : newest = f.DateLastModified\r\n"
		"        End If\r\n"
		"      End If\r\n"
		"    Next\r\n"
		"  Next\r\n"
		"End If\r\n"
		"If newestPath = \"\" Then\r\n"
		"  MsgBox \"P5D launcher not found. Run P5D Windows launcher from the release package again.\", 48, \"P5D\"\r\n"
		"Else\r\n"
		"  sh.Run \"\"\"\" & newestPath & \"\"\"\", 1, False\r\n"
		"End If\r\n";
	FILE *f = fopen(vbs.c_str(), "wb");
	if (!f) return "";
	fwrite(script, 1, strlen(script), f);
	fclose(f);
	return vbs;
}
/* M1789/M1790/M1791/M1792: the Steam art, generated at the moment 「添加到 Steam 庫」 runs from the player's own built
 * game -- NOTHING is bundled in the launcher, only this generation code is:
 *   <appid>p.png            600x900 portrait cover, from the livearea bg0.png: a sharp cover crop anchored to the RIGHT
 *                           (the picture is landscape; the centre slice showed only hands/coat, the right one shows Joker)
 *   <appid>.png             920x430 wide capsule ("grid"), from pic0.png
 *   <appid>_hero.png        1920x620 game-page background, from bg0.png: sharp cover crop anchored to the TOP (a middle
 *                           crop cut Morgana's and Joker's heads) + the bottom vignette
 *   <appid>_header.png      460x215 legacy header, from pic0.png
 *   <appid>_p.png           legacy portrait name (kept for older Steam)
 * Both the signed and the unsigned appid spelling are written (tools differ on which one names the files); PNG only. */
static bool steam_cover_images(const std::string &title_art, const std::string &char_art, const std::string &griddir, uint32_t appid, std::string &why) {
	SDL_Surface *src = SDL_LoadPNG(title_art.c_str());
	if (!src) { why = "讀不到封面圖 " + title_art; return false; }
	SDL_Surface *himg = char_art.empty() ? nullptr : SDL_LoadPNG(char_art.c_str());
	steam_mkdirs(griddir);
	SDL_Surface *blurred = SDL_ConvertSurface(src, SDL_PIXELFORMAT_RGBA32);
	if (blurred) steam_box_blur(blurred, 6, 2);
	const std::string ids[2] = {std::to_string((int32_t)appid), std::to_string((uint32_t)appid)};
	bool ok = false;
	auto save = [&](SDL_Surface *s, const char *suffix) {
		if (!s) return;
		for (const std::string &id : ids) if (SDL_SavePNG(s, (griddir + "\\" + id + suffix).c_str())) ok = true;
	};
	auto darkened = [](SDL_Surface *s) {
		if (SDL_Surface *b = SDL_ConvertSurface(s, SDL_PIXELFORMAT_RGBA32)) {
			SDL_LockSurface(b);
			for (int y = 0; y < b->h; y++) {
				Uint8 *row = (Uint8 *)b->pixels + (size_t)y * b->pitch;
				for (int x = 0; x < b->w; x++) { row[x * 4 + 0] = (Uint8)(row[x * 4 + 0] * 110 / 255); row[x * 4 + 1] = (Uint8)(row[x * 4 + 1] * 110 / 255); row[x * 4 + 2] = (Uint8)(row[x * 4 + 2] * 110 / 255); }
			}
			SDL_UnlockSurface(b);
			SDL_DestroySurface(s);
			return b;
		}
		return s;
	};
	auto bottom_vignette = [](SDL_Surface *s, int alpha) {
		SDL_LockSurface(s);
		for (int y = 0; y < s->h; y++) {
			const float t = ((float)y / (s->h - 1) - 0.55f) / 0.45f;
			if (t <= 0) continue;
			const float f = std::max(0.0f, 1.0f - (alpha / 255.0f) * t);
			Uint8 *row = (Uint8 *)s->pixels + (size_t)y * s->pitch;
			for (int x = 0; x < s->w; x++) { row[x * 4 + 0] = (Uint8)(row[x * 4 + 0] * f); row[x * 4 + 1] = (Uint8)(row[x * 4 + 1] * f); row[x * 4 + 2] = (Uint8)(row[x * 4 + 2] * f); }
		}
		SDL_UnlockSurface(s);
	};
	auto cover_of = [&](SDL_Surface *s, int W, int H, float anchorY, float anchorX = 0.5f) -> SDL_Surface * {
		if (!s || s->w <= 0 || s->h <= 0) return nullptr;
		float k = std::max((float)W / s->w, (float)H / s->h);
		int sw = (int)std::ceil(s->w * k), sh = (int)std::ceil(s->h * k);
		SDL_Surface *sc = SDL_ScaleSurface(s, sw, sh, SDL_SCALEMODE_LINEAR);
		if (!sc) return nullptr;
		SDL_Surface *d = SDL_CreateSurface(W, H, SDL_PIXELFORMAT_RGBA32);
		if (d) { SDL_Rect sr{ (int)((sw - W) * anchorX), (int)((sh - H) * anchorY), W, H }; if (!SDL_BlitSurface(sc, &sr, d, nullptr)) { SDL_DestroySurface(d); d = nullptr; } }
		SDL_DestroySurface(sc);
		return d;
	};
	do {
		if (src->w <= 0 || src->h <= 0) break;
		if (himg) {
			if (SDL_Surface *cov = cover_of(himg, 600, 900, 0.5f, 1.0f)) {
				save(cov, "p.png");
				save(cov, "_p.png");
				SDL_DestroySurface(cov);
			}
		} else {   /* no bg0.png: the title art over its own blurred fill */
			const int CW = 600, CH = 900, TW = 600, TH = 340;
			SDL_Surface *canvas = SDL_CreateSurface(CW, CH, SDL_PIXELFORMAT_RGBA32);
			if (!canvas) break;
			SDL_FillSurfaceRect(canvas, nullptr, SDL_MapSurfaceRGBA(canvas, 0, 0, 0, 255));
			if (blurred) {
				const float cover = std::max((float)CW / blurred->w, (float)CH / blurred->h);
				const int bw = (int)std::ceil(blurred->w * cover), bh = (int)std::ceil(blurred->h * cover);
				if (SDL_Surface *bg = SDL_ScaleSurface(blurred, bw, bh, SDL_SCALEMODE_LINEAR)) {
					SDL_Surface *b32 = darkened(bg);
					if (b32) { SDL_Rect br{ (bw - CW) / 2, (bh - CH) / 2, CW, CH }; SDL_BlitSurface(b32, &br, canvas, nullptr); SDL_DestroySurface(b32); }
				}
			}
			if (SDL_Surface *thumb = SDL_ScaleSurface(src, TW, TH, SDL_SCALEMODE_LINEAR)) {
				SDL_Rect tr{ 0, (CH - TH) / 2, TW, TH };
				SDL_BlitSurface(thumb, nullptr, canvas, &tr);
				SDL_DestroySurface(thumb);
			}
			save(canvas, "p.png");
			save(canvas, "_p.png");
			SDL_DestroySurface(canvas);
		}

		if (SDL_Surface *wide = cover_of(src, 920, 430, 0.5f)) { save(wide, ".png"); SDL_DestroySurface(wide); }

		if (himg) {
			if (SDL_Surface *hero = cover_of(himg, 1920, 620, 0.0f)) {
				bottom_vignette(hero, 120);
				save(hero, "_hero.png");
				SDL_DestroySurface(hero);
			}
		} else {
			SDL_Surface *hero = SDL_CreateSurface(1920, 620, SDL_PIXELFORMAT_RGBA32);
			if (hero) {
				SDL_FillSurfaceRect(hero, nullptr, SDL_MapSurfaceRGBA(hero, 0, 0, 0, 255));
				if (blurred) {
					const float hc = std::max(1920.0f / blurred->w, 620.0f / blurred->h);
					const int hw = (int)std::ceil(blurred->w * hc), hh = (int)std::ceil(blurred->h * hc);
					if (SDL_Surface *big = SDL_ScaleSurface(blurred, hw, hh, SDL_SCALEMODE_LINEAR)) {
						SDL_Surface *b32 = darkened(big);
						if (b32) { SDL_Rect br{ (hw - 1920) / 2, (hh - 620) / 2, 1920, 620 }; SDL_BlitSurface(b32, &br, hero, nullptr); SDL_DestroySurface(b32); }
					}
				}
				const int fh = 620, fw = (int)std::ceil(src->w * (620.0f / src->h));
				if (SDL_Surface *fg = SDL_ScaleSurface(src, fw, fh, SDL_SCALEMODE_LINEAR)) {
					SDL_Rect fr{ (1920 - fw) / 2, 0, fw, fh };
					SDL_BlitSurface(fg, nullptr, hero, &fr);
					SDL_DestroySurface(fg);
				}
				save(hero, "_hero.png");
				SDL_DestroySurface(hero);
			}
		}

		if (SDL_Surface *hd = cover_of(src, 460, 215, 0.5f)) { save(hd, "_header.png"); SDL_DestroySurface(hd); }
	} while (0);
	if (himg) SDL_DestroySurface(himg);
	if (blurred) SDL_DestroySurface(blurred);
	SDL_DestroySurface(src);
	if (!ok) why = "封面圖生成失敗（" + title_art + "）";
	return ok;
}
static bool p5d_steam_add(std::string &msg) {
	/* only a BUILT game can be added: the art comes from its own files and the entry runs a launcher for a game that must
	 * exist. The button is disabled too; this is the safety net. Paths are built from g_dump at click time, so a library
	 * moved with 「遊戲存放位置」 just works. */
	const std::string host_exe = g_dump + "/decrypted/PCSH10109/recomp/game_host_min.exe";
	if (!exists(host_exe)) { msg = "遊戲尚未構建，無法添加到 Steam 庫：請先完成構建（見主頁 ④）。"; return false; }
	std::string steam = getenv("P5D_STEAM_DIR") ? getenv("P5D_STEAM_DIR") : "";
	if (steam.empty()) steam = steam_reg(HKEY_CURRENT_USER, "Software\\Valve\\Steam", "SteamPath");
	if (steam.empty()) steam = steam_reg(HKEY_LOCAL_MACHINE, "SOFTWARE\\WOW6432Node\\Valve\\Steam", "InstallPath");
	if (steam.empty()) steam = steam_reg(HKEY_LOCAL_MACHINE, "SOFTWARE\\Valve\\Steam", "InstallPath");
	if (steam.empty()) {
		const char *cands[] = {"C:\\Program Files (x86)\\Steam", "C:\\Program Files\\Steam", "D:\\Steam", "D:\\steam", "E:\\Steam", "E:\\steam"};
		for (const char *c : cands) if (exists(std::string(c) + "\\steam.exe")) { steam = c; break; }
	}
	if (steam.empty() || !exists(steam + "\\steam.exe")) { msg = "找不到 Steam 安裝位置：請先安裝並登入 Steam，或用「添加非 Steam 遊戲」手動加入。"; return false; }
	if (!getenv("P5D_STEAM_DIR") && steam_running()) { msg = "Steam 正在執行：Steam 結束時會覆寫快捷方式檔案，請先完全退出 Steam，再點一次。"; return false; }
	std::string stub_dir = getenv("P5D_STEAM_STUB_DIR") ? getenv("P5D_STEAM_STUB_DIR") : "";
	if (stub_dir.empty()) { const char *la = getenv("LOCALAPPDATA"); if (!la || !*la) { msg = "找不到 LOCALAPPDATA（Steam 入口腳本的位置）"; return false; } stub_dir = std::string(la) + "\\P5D-Port\\P5D"; }
	const std::string vbs = steam_write_stub(stub_dir);
	if (vbs.empty()) { msg = "無法建立 Steam 入口腳本（" + stub_dir + "）"; return false; }
	char win[MAX_PATH] = ""; GetWindowsDirectoryA(win, MAX_PATH);
	const std::string exe = std::string(win) + "\\System32\\wscript.exe";
	const std::string args = "\"" + vbs + "\"";
	const std::string start = stub_dir;
	const std::string name = "P5D Windows移植版";
	std::vector<std::string> accounts;
	if (DIR *d = opendir((steam + "\\userdata").c_str())) {
		while (dirent *e = readdir(d)) {
			std::string n = e->d_name;
			if (n.empty() || n[0] < '0' || n[0] > '9') continue;
			if (exists(steam + "\\userdata\\" + n + "\\config")) accounts.push_back(n);
		}
		closedir(d);
	}
	if (accounts.empty()) { msg = "Steam 沒有任何已登入的使用者資料（先登入一次 Steam 再試）"; return false; }
	int wrote = 0, skipped = 0, covers = 0; std::string last_why, cover_why;
	const uint32_t appid = steam_crc32(exe + name) | 0x80000000u;
	const std::string pic0a = g_dump + "/decrypted/PCSH10109/recomp/fs/app0/sce_sys/pic0.png";
	const std::string pic0b = g_dump + "/decrypted/PCSH10109/app0/sce_sys/pic0.png";
	const std::string pic0 = exists(pic0a) ? pic0a : (exists(pic0b) ? pic0b : "");
	const std::string bg0a = g_dump + "/decrypted/PCSH10109/recomp/fs/app0/sce_sys/livearea/contents/bg0.png";
	const std::string bg0b = g_dump + "/decrypted/PCSH10109/app0/sce_sys/livearea/contents/bg0.png";
	const std::string char_art = exists(bg0a) ? bg0a : (exists(bg0b) ? bg0b : "");
	for (const std::string &acc : accounts) {
		const std::string path = steam + "\\userdata\\" + acc + "\\config\\shortcuts.vdf";
		const std::string have = steam_read_all(path);
		if (have.find(name) != std::string::npos) skipped++;
		else {
			std::string why;
			int count = 0, idx = 0;
			{   /* count existing top-level entries */
				std::string b = have; size_t p = 0;
				if (!b.empty() && (uint8_t)b[0] == 0x00) {
					p = 1; while (p < b.size() && b[p]) p++; p++;
					while (p < b.size()) { uint8_t t = (uint8_t)b[p++]; if (t == 0x08) break; while (p < b.size() && b[p]) p++; p++; idx++; if (!steam_vdf_skip(b, p, t)) break; }
				}
			}
			const std::string e2 = steam_shortcut_entry(idx, name, exe, start, args, appid);
			if (steam_vdf_append(path, e2, count, why)) wrote++;
			else last_why = why;
		}
		if (!pic0.empty() || !char_art.empty()) {
			if (steam_cover_images(pic0.empty() ? char_art : pic0, char_art, steam + "\\userdata\\" + acc + "\\config\\grid", appid, cover_why)) covers++;
		}
	}
	if (covers == 0 && !cover_why.empty()) last_why += (last_why.empty() ? "" : "；") + cover_why;
	const std::string art = covers > 0 ? "，封面圖已生成" : "（找不到遊戲封面圖，未生成封面）";
	if (wrote > 0) { msg = "已添加到 Steam 庫（" + std::to_string(wrote) + " 個帳號" + art + "）：重新啟動 Steam 後，在「收藏庫」裡啟動「" + name + "」。桌面啟動器仍然可以照常使用。"; return true; }
	if (skipped > 0) { msg = "已在 Steam 庫中（無需重複添加" + art + "）。桌面啟動器仍然可以照常使用。"; return true; }
	msg = "添加失敗：" + last_why;
	return false;
}
#endif   /* _WIN32 */


/* ---- a child process: its output (stdout and stderr together) read through a pipe; killed with everything it started
 * (POSIX: its own process group; Windows: a job object holding the process tree) */
struct Proc {
#ifdef _WIN32
	HANDLE process = nullptr, job = nullptr, out = nullptr;
#else
	pid_t pid = 0; int out = -1;
#endif
};
#ifdef _WIN32
static std::wstring win_arg(const std::wstring &a) {   /* one argument, quoted the way CommandLineToArgvW reads it back */
	if (!a.empty() && a.find_first_of(L" \t\n\v\"") == std::wstring::npos) return a;
	std::wstring q = L"\"";
	for (size_t i = 0;; i++) {
		size_t bs = 0; while (i < a.size() && a[i] == L'\\') { bs++; i++; }
		if (i == a.size()) { q.append(bs * 2, L'\\'); break; }
		if (a[i] == L'"') { q.append(bs * 2 + 1, L'\\'); q += L'"'; } else { q.append(bs, L'\\'); q += a[i]; }
	}
	return q + L"\"";
}
static bool proc_start(Proc &p, const std::vector<std::string> &argv, const std::vector<std::string> &env) {
	SECURITY_ATTRIBUTES sa = {sizeof sa, nullptr, TRUE};
	HANDLE rd, wr, nul = CreateFileW(L"NUL", GENERIC_READ, FILE_SHARE_READ | FILE_SHARE_WRITE, &sa, OPEN_EXISTING, 0, nullptr);
	if (!CreatePipe(&rd, &wr, &sa, 0)) return false;
	SetHandleInformation(rd, HANDLE_FLAG_INHERIT, 0);
	std::wstring cmd; for (const std::string &a : argv) { if (!cmd.empty()) cmd += L' '; cmd += win_arg(wide(a)); }
	std::vector<std::string> env_all = env;   /* M1735: the library folder goes in explicitly -- _putenv_s alone did not
	                                           * reach the child's OS environment block, so a build after changing the folder
	                                           * still wrote into the old library */
	if (!g_dump.empty()) env_all.push_back("ATIV_DUMP=" + g_dump);
	std::wstring block;   /* the launcher's environment with the step's NAME=value settings over it */
	{
		std::vector<std::wstring> vars;
		if (wchar_t *e = GetEnvironmentStringsW()) { for (wchar_t *v = e; *v; v += wcslen(v) + 1) vars.push_back(v); FreeEnvironmentStringsW(e); }
		for (const std::string &kv : env_all) {
			std::wstring w = wide(kv), k = w.substr(0, w.find(L'=') + 1);
			vars.erase(std::remove_if(vars.begin(), vars.end(), [&](const std::wstring &v) { return _wcsnicmp(v.c_str(), k.c_str(), k.size()) == 0; }), vars.end());
			vars.push_back(w);
		}
		for (const std::wstring &v : vars) { block += v; block += L'\0'; }
		block += L'\0';
	}
	STARTUPINFOW si = {}; si.cb = sizeof si; si.dwFlags = STARTF_USESTDHANDLES; si.hStdInput = nul; si.hStdOutput = wr; si.hStdError = wr;
	PROCESS_INFORMATION pi = {};
	std::wstring dir = wide(g_root);
	BOOL ok = CreateProcessW(nullptr, &cmd[0], nullptr, nullptr, TRUE, CREATE_SUSPENDED | CREATE_NO_WINDOW | CREATE_UNICODE_ENVIRONMENT,
	                         &block[0], dir.c_str(), &si, &pi);
	CloseHandle(wr); if (nul != INVALID_HANDLE_VALUE) CloseHandle(nul);
	if (!ok) { CloseHandle(rd); return false; }
	p.job = CreateJobObjectW(nullptr, nullptr);
	if (p.job) AssignProcessToJobObject(p.job, pi.hProcess);
	ResumeThread(pi.hThread); CloseHandle(pi.hThread);
	p.process = pi.hProcess; p.out = rd;
	return true;
}
static long proc_read(Proc &p, char *buf, size_t n) { DWORD got = 0; return ReadFile(p.out, buf, (DWORD)n, &got, nullptr) ? (long)got : -1; }
static int proc_wait(Proc &p) {   /* its exit code (a Cancel: 1) */
	WaitForSingleObject(p.process, INFINITE);
	DWORD code = 1; GetExitCodeProcess(p.process, &code);
	CloseHandle(p.out); CloseHandle(p.process);
	return (int)code;
}
static void proc_kill(Proc &p) { if (p.job) TerminateJobObject(p.job, 1); else if (p.process) TerminateProcess(p.process, 1); }
static void proc_done(Proc &p) { if (p.job) CloseHandle(p.job); p = Proc(); }
#else
extern char **environ;
static bool proc_start(Proc &p, const std::vector<std::string> &argv, const std::vector<std::string> &env) {
	/* everything the child needs made before fork: the launcher has threads, and a child of one may only exec */
	std::vector<char *> a; for (const std::string &s : argv) a.push_back((char *)s.c_str()); a.push_back(nullptr);
	std::vector<std::string> vars;
	for (char **e = environ; *e; e++) {
		bool over = false;
		for (const std::string &kv : env) over |= strncmp(*e, kv.c_str(), kv.find('=') + 1) == 0;
		if (!over) vars.push_back(*e);
	}
	vars.insert(vars.end(), env.begin(), env.end());
	std::vector<char *> envp; for (std::string &v : vars) envp.push_back(&v[0]); envp.push_back(nullptr);
	int fd[2];
	if (pipe(fd) != 0) return false;
	pid_t pid = fork();
	if (pid == 0) {
		setpgid(0, 0);
		dup2(fd[1], 1); dup2(fd[1], 2); close(fd[0]); close(fd[1]);
		if (chdir(g_root.c_str()) != 0) _exit(126);
		environ = envp.data();
		execvp(a[0], a.data());
		static const char msg[] = "can't run the command\n"; (void)!write(2, msg, sizeof msg - 1);
		_exit(127);
	}
	close(fd[1]);
	if (pid < 0) { close(fd[0]); return false; }
	setpgid(pid, pid);
	p.pid = pid; p.out = fd[0];
	return true;
}
static long proc_read(Proc &p, char *buf, size_t n) { return (long)read(p.out, buf, n); }
static int proc_wait(Proc &p) {   /* its exit code; killed by a signal: 128 + the signal */
	close(p.out);
	int st = 0; waitpid(p.pid, &st, 0);
	return WIFEXITED(st) ? WEXITSTATUS(st) : 128 + WTERMSIG(st);
}
static void proc_kill(Proc &p) { if (p.pid > 0) kill(-p.pid, SIGTERM); }
static void proc_done(Proc &p) { p = Proc(); }
#endif

/* ---- one task at a time: its steps run in turn, their output into the log; Cancel kills the step running and runs no
 * more. A step announces itself with an "@@ <step>" line (the latest is the status). A failed step ends its group: group
 * 0 is the whole task; a folder search's chain gives each game its own (one game failing doesn't stop the next) */
struct Step {
	std::string say;                 /* "@@ " + this before it runs (a step with no command: only the line) */
	std::vector<std::string> argv;
	std::vector<std::string> env;    /* NAME=value over the launcher's environment */
	int group = 0;
};
/* ---- a newer Nativ: `vitarecomp update-check` in the background at start (it asks GitHub at most once a day, and only
 * an install whose dist named a release channel); its release, or nothing */
static struct { std::mutex m; std::string tag, page; bool dismissed = false; } g_update;
static void update_check_start(void) {
	std::thread([]() {
		Proc p; if (!proc_start(p, vitarecomp({"update-check"}), {})) return;
		std::string out; char b[512]; long n; while ((n = proc_read(p, b, sizeof b)) > 0) out.append(b, (size_t)n);
		proc_wait(p); proc_done(p);
		for (size_t a = 0; a < out.size(); ) {
			size_t e = out.find('\n', a); if (e == std::string::npos) e = out.size();
			char tag[64], page[512];
			if (sscanf(out.substr(a, e - a).c_str(), "update %63s %511s", tag, page) == 2 && !strncmp(page, "https://", 8)) {
				std::lock_guard<std::mutex> l(g_update.m); g_update.tag = tag; g_update.page = page;
			}
			a = e + 1;
		}
	}).detach();
}
/* ---- an install with files missing or cut short: the release's own list (.p5d-files, "size path" a line
 * writes it into the Windows zip, the one install a player unpacks), checked in the background at start. A player's Python
 * once lacked Lib\collections, an unpacking that stopped part way (2026-10-30): the firmware step died on a traceback */
static struct { std::mutex m; int bad = 0; std::string first; bool dismissed = false; } g_files;
static void files_check(void) {
	FILE *f = fopen((g_root + "/.p5d-files").c_str(), "rb"); if (!f) return;
	char line[2048]; int bad = 0; std::string first;
	while (fgets(line, sizeof line, f)) {
		char *sp = strchr(line, ' '); if (!sp) continue;
		*sp = 0; std::string rel(sp + 1); while (!rel.empty() && (rel.back() == '\n' || rel.back() == '\r')) rel.pop_back();
		struct stat st; const long long want = atoll(line);
		if (stat((g_root + "/" + rel).c_str(), &st) != 0 || (long long)st.st_size != want) { if (!bad++) first = rel; }
	}
	fclose(f);
	if (!bad) return;
	fprintf(stderr, "install: %d of the release's files missing or cut short (the first: %s)\n", bad, first.c_str());
#ifdef _WIN32
	std::replace(first.begin(), first.end(), '/', '\\');
#endif
	std::lock_guard<std::mutex> l(g_files.m); g_files.bad = bad; g_files.first = first;
}
static void files_check_start(void) { std::thread(files_check).detach(); }
static Step step(const std::string &say, std::vector<std::string> argv = {}, int group = 0) { Step s; s.say = say; s.argv = std::move(argv); s.group = group; return s; }
struct Task {
	std::string name, game, kind;
	std::vector<std::string> games;   /* the titles it works on: their cards show its step (game, or a search's chain's) */
	std::atomic<bool> running{false}, cancelled{false};
	bool ok = false;
	std::atomic<int> pct{0}, pct_max{0};   /* the running build's PROGRESS done/total (pipeline: runtime/build.py) */
	size_t log_from = 0;
	std::thread reader;
	std::mutex proc_lock; Proc proc;  /* the step running */
};
static Task g_task;
static std::mutex g_log_lock;
static std::string g_log;
static std::atomic<bool> g_refresh{false};   /* a task ended: the library's states may have changed */
static std::string g_failed;                  /* the last task that failed, for the banner (empty: none) */
static bool g_drawer;                         /* the activity drawer open (the whole log) */
static std::string g_log_file;                /* <prefs>/launcher.log: the log as each task ends, for a bug report (the launcher
                                               * before this one: launcher.prev.log) */

static void log_append(const char *s, size_t n) {
	std::lock_guard<std::mutex> l(g_log_lock);
	for (size_t i = 0; i + 9 <= n; i++) {   /* "PROGRESS <done>/<total>": the build bar's real percentage */
		if (std::memcmp(s + i, "PROGRESS ", 9) != 0) continue;
		int a = 0, b = 0;
		if (sscanf(s + i + 9, "%d/%d", &a, &b) == 2 && b > 0) { g_task.pct = a; g_task.pct_max = b; }
	}
	g_log.append(s, n);
	if (g_log.size() > (1u << 20)) { size_t cut = g_log.size() - (1u << 19); g_log.erase(0, cut); g_task.log_from = g_task.log_from > cut ? g_task.log_from - cut : 0; }
}
static void log_append(const std::string &s) { log_append(s.data(), s.size()); }
static void task_start(const std::string &name, const std::string &kind, const std::string &game, std::vector<Step> steps) {
	if (g_task.running) return;
	if (g_task.reader.joinable()) g_task.reader.join();
	g_failed.clear();
	{ std::lock_guard<std::mutex> l(g_log_lock); g_log += "\n== " + name + "\n"; g_task.log_from = g_log.size(); }
	g_task.name = name; g_task.kind = kind; g_task.game = game; g_task.ok = false; g_task.cancelled = false; g_task.running = true;
	g_task.pct = 0; g_task.pct_max = 0;
	g_task.games.clear(); if (!game.empty()) g_task.games.push_back(game);
	g_task.reader = std::thread([steps = std::move(steps), name]() {
		std::vector<int> failed;   /* the groups that failed */
		int last = 0;
		for (const Step &s : steps) {
			if (g_task.cancelled) break;
			if (std::find(failed.begin(), failed.end(), s.group) != failed.end()) continue;
			if (!s.say.empty()) log_append("@@ " + s.say + "\n");
			if (s.argv.empty()) continue;
			log_append("$ " + shown_args(s.argv) + "\n");
			Proc p;
			{ std::lock_guard<std::mutex> l(g_task.proc_lock); if (g_task.cancelled || !proc_start(p, s.argv, s.env)) { if (!g_task.cancelled) log_append("can't start " + s.argv[0] + "\n"); last = 127; failed.push_back(s.group); if (s.group == 0) break; continue; } g_task.proc = p; }
			char buf[4096]; long n;
			while ((n = proc_read(p, buf, sizeof buf)) > 0) log_append(buf, (size_t)n);
			int code = proc_wait(p);
			{ std::lock_guard<std::mutex> l(g_task.proc_lock); proc_done(g_task.proc); }
			if (code != 0) { last = code; failed.push_back(s.group); if (s.group == 0) break; }
		}
		bool stopped = g_task.cancelled;
		g_task.ok = failed.empty() && !stopped;
		char end[96]; int m = snprintf(end, sizeof end, "== %s (exit %d)\n", stopped ? "stopped" : "done", stopped ? -1 : last);
		log_append(end, (size_t)m);
		if (!g_task.ok && !stopped) g_failed = name;
		if (!g_log_file.empty()) {
			std::string copy; { std::lock_guard<std::mutex> l(g_log_lock); copy = g_log; }
			if (FILE *f = fopen(g_log_file.c_str(), "wb")) { fwrite(copy.data(), 1, copy.size(), f); fclose(f); }
		}
		g_task.running = false;
		g_refresh = true;
	});
}
static void task_cancel(void) {
	if (!g_task.running) return;
	std::lock_guard<std::mutex> l(g_task.proc_lock);
	g_task.cancelled = true;
	proc_kill(g_task.proc);
}
static std::string task_status(void) {   /* the latest "@@ step" of the running task, else its last line of output */
	std::lock_guard<std::mutex> l(g_log_lock);
	size_t from = g_task.log_from < g_log.size() ? g_task.log_from : g_log.size();
	size_t at = g_log.rfind("\n@@ ");
	if (at != std::string::npos && at + 1 >= from) { size_t e = g_log.find('\n', at + 4); return g_log.substr(at + 4, e == std::string::npos ? std::string::npos : e - at - 4); }
	size_t e = g_log.size(); while (e > from && (g_log[e - 1] == '\n' || g_log[e - 1] == ' ')) e--;
	size_t b = g_log.rfind('\n', e ? e - 1 : 0); b = b == std::string::npos || b < from ? from : b + 1;
	std::string s = e > b ? g_log.substr(b, e - b) : "";
	if (s.size() > 90) s = s.substr(0, 87) + "...";
	return s;
}

/* ---- the library: packs + whatever is under dump/decrypted */
struct Game {
	std::string id, name, elf = "eboot.bin.elf", base = "game";   /* base: the pack's BASE= (the host binary is <base>_host) */
	std::string version;      /* this copy's (dump/decrypted/<id>/version, vitarecomp import's); "-": the pack's one build, no number recorded */
	std::vector<std::pair<std::string, std::string>> versions;   /* the pack's versions: (version, recommended | supported) */
	std::string update_note;  /* the pack's UPDATE_NOTE: what its recommended version brings */
	std::string cover, icon;  /* the copy's own art (art_paths): "" when it has none */
	std::string region;       /* the pack's REGION: the release it plays (US) */
	bool pack = false, imported = false, built = false;
};
static std::string recommended_version(const Game &g) {
	for (auto &v : g.versions) if (v.second == "recommended") return v.first;
	return "";
}
static std::string played_versions(const Game &g) {   /* "1.00, 1.12" (the numbers recorded) */
	std::string s;
	for (auto &v : g.versions) if (v.first != "-") s += (s.empty() ? "" : ", ") + v.first;
	return s;
}
static std::vector<Game> g_games;
static bool g_firmware;
static std::string g_firmware_version;

/* a game pack (packs/<title>/pack.toml; the format: pipeline/packconf.py), as far as the launcher reads it: the top-level
 * settings (KEY = "text" or a number) and each [versions."<version>"] table's status, in the pack's order */
struct Pack { std::map<std::string, std::string> top; std::vector<std::pair<std::string, std::string>> versions; };
static Pack pack_read(const std::string &path) {
	Pack p; std::string text, table;
	if (FILE *f = fopen(path.c_str(), "rb")) { char b[4096]; size_t n; while ((n = fread(b, 1, sizeof b, f)) > 0) text.append(b, n); fclose(f); }
	for (size_t at = 0; at < text.size();) {
		size_t end = text.find('\n', at); if (end == std::string::npos) end = text.size();
		const std::string l = text.substr(at, end - at); at = end + 1;
		size_t s = l.find_first_not_of(" \t\r"); if (s == std::string::npos || l[s] == '#') continue;
		if (l[s] == '[') {
			size_t e = l.rfind(']'); table = e != std::string::npos && e > s ? l.substr(s + 1, e - s - 1) : "";
			if (table.size() > 11 && table.compare(0, 10, "versions.\"") == 0 && table.back() == '"') p.versions.push_back({table.substr(10, table.size() - 11), "supported"});
			continue;
		}
		size_t eq = l.find('=', s), v = eq == std::string::npos ? eq : l.find_first_not_of(" \t", eq + 1);
		if (eq == std::string::npos || eq == s || v == std::string::npos) continue;
		const std::string key = l.substr(s, l.find_last_not_of(" \t", eq - 1) - s + 1);
		std::string val;
		if (l[v] == '"') { for (v++; v < l.size() && l[v] != '"'; v++) { if (l[v] == '\\' && v + 1 < l.size()) v++; val += l[v]; } }
		else { size_t e = l.find_first_of(" \t#\r", v); val = l.substr(v, e == std::string::npos ? std::string::npos : e - v); }
		if (table.empty()) p.top[key] = val;
		else if (key == "status" && table.compare(0, 9, "versions.") == 0 && !p.versions.empty()) p.versions.back().second = val;
	}
	return p;
}
static std::string pack_value(const Pack &p, const char *key) { auto it = p.top.find(key); return it == p.top.end() ? "" : it->second; }
static std::string first_line(const std::string &path) {
	FILE *f = fopen(path.c_str(), "r"); if (!f) return "";
	char line[256] = ""; if (!fgets(line, sizeof line, f)) line[0] = 0;
	fclose(f);
	std::string v = line; while (!v.empty() && (v.back() == '\n' || v.back() == '\r' || v.back() == ' ')) v.pop_back();
	return v;
}
static bool title_like(const char *s) {   /* PCSA00029: four letters, five digits */
	if (strlen(s) != 9) return false;
	for (int i = 0; i < 4; i++) if (s[i] < 'A' || s[i] > 'Z') return false;
	for (int i = 4; i < 9; i++) if (s[i] < '0' || s[i] > '9') return false;
	return true;
}
static void art_paths(Game &g);
static void count_licences(void);
static void library_scan(void) {
	count_licences();
	for (auto it = g_tex.begin(); it != g_tex.end();) it = it->second.t ? std::next(it) : g_tex.erase(it);   /* (retry art not found before) */
	std::map<std::string, Game> by;
	std::string packs = g_root + "/packs";
	if (DIR *d = opendir(packs.c_str())) {
		while (dirent *e = readdir(d)) {
			std::string n = e->d_name;
			const std::string path = packs + "/" + n + "/pack.toml";
			if (n.size() != 9 || !title_like(n.c_str()) || !exists(path)) continue;
			const Pack p = pack_read(path);
			Game &g = by[n];
			g.id = n; g.pack = true;
			g.name = pack_value(p, "NAME");
			std::string elf = pack_value(p, "ELF"); if (!elf.empty()) g.elf = elf;
			std::string base = pack_value(p, "BASE"); if (!base.empty()) g.base = base;
			g.versions = p.versions;
			g.update_note = pack_value(p, "UPDATE_NOTE");
			g.region = pack_value(p, "REGION");
		}
		closedir(d);
	}
	std::string dumps = g_dump + "/decrypted";
	if (DIR *d = opendir(dumps.c_str())) {
		while (dirent *e = readdir(d)) {
			if (!title_like(e->d_name)) continue;
			std::string w = dumps + "/" + e->d_name;
			if (!exists(w + "/elf")) continue;   /* a scratch or analysis folder, not an imported game */
			Game &g = by[e->d_name]; g.id = e->d_name;
		}
		closedir(d);
	}
	g_games.clear();
	for (auto &kv : by) {
		Game g = kv.second;
		std::string w = dumps + "/" + g.id;
		g.imported = exists(w + "/elf/" + g.elf);
#ifdef _WIN32
		/* a BUILD_MINIMAL pack builds <base>_host_min.exe (runtime/build.py host()): the P5D port is one, so
		 * checking only <base>_host.exe left the launch button disabled for every player (reported 2026-11-10) */
		g.built = exists(w + "/recomp/" + g.base + "_host.exe") || exists(w + "/recomp/" + g.base + "_host_min.exe");
#else
		g.built = exists(w + "/recomp/" + g.base + "_host") || exists(w + "/recomp/" + g.base + "_host_min");
#endif
		g.version = first_line(w + "/version");
		if (g.imported) art_paths(g);
		if (g.name.empty()) g.name = g.id;
		g_games.push_back(g);
	}
	/* a console dump's modules, or a firmware update file's from setup (dump/firmware/<version>/) */
	g_firmware = exists(dumps + "/us/libgxm_es4.suprx.elf"); g_firmware_version.clear();
	std::string fw = g_dump + "/firmware";
	if (DIR *d = opendir(fw.c_str())) {   /* the newest update file installed */
		while (dirent *e = readdir(d))
			if (e->d_name[0] != '.' && exists(fw + "/" + e->d_name + "/os0/us/libgxm_es4.suprx.elf") && std::string(e->d_name) > g_firmware_version) { g_firmware = true; g_firmware_version = e->d_name; }
		closedir(d);
	}
	if (g_firmware && g_firmware_version.empty()) g_firmware_version = "from a console dump";
}
/* ---- a card's art, from the copy's own sce_sys: pic0.png (960x544, the game's background picture); else its LiveArea's
 * background (template.xml <livearea-background><image>, 840x500); else its LiveArea gate's start image (280x158).
 * (Nothing of a game ships with Nativ: a game not added yet keeps its typeset placeholder.) */
static std::string read_file(const std::string &path) {
	std::string s; FILE *f = fopen(path.c_str(), "rb"); if (!f) return s;
	char buf[4096]; size_t n; while ((n = fread(buf, 1, sizeof buf, f)) > 0 && s.size() < (1u << 20)) s.append(buf, n);
	fclose(f);
	return s;
}
static std::string tag_text(const std::string &x, const char *tag, size_t from = 0) {   /* the text right after <tag ...>, trimmed */
	size_t a = x.find(tag, from); if (a == std::string::npos) return "";
	a = x.find('>', a); if (a == std::string::npos) return "";
	size_t b = x.find('<', ++a); std::string v = x.substr(a, b == std::string::npos ? std::string::npos : b - a);
	size_t s0 = v.find_first_not_of(" \t\r\n"), s1 = v.find_last_not_of(" \t\r\n");
	return s0 == std::string::npos ? "" : v.substr(s0, s1 - s0 + 1);
}
static void art_paths(Game &g) {
	std::string sys = g_dump + "/decrypted/" + g.id + "/recomp/fs/app0/sce_sys/", la = sys + "livearea/contents/";
	g.icon = exists(sys + "icon0.png") ? sys + "icon0.png" : "";
	g.cover.clear();
	if (exists(sys + "pic0.png")) { g.cover = sys + "pic0.png"; return; }
	std::string x = read_file(la + "template.xml");
	size_t bg = x.find("<livearea-background");
	for (const std::string &v : {bg == std::string::npos ? std::string() : tag_text(x, "<image", bg), tag_text(x, "<startup-image")})
		if (!v.empty() && v.find('/') == std::string::npos && exists(la + v)) { g.cover = la + v; return; }
}

/* ---- the native file dialogs (SDL3): their callback lands the chosen path in a field */
static std::mutex g_pick_lock;
static std::string *g_pick_target;
static std::string g_pick_result; static bool g_pick_done;
static void SDLCALL picked(void *, const char *const *files, int) {
	std::lock_guard<std::mutex> l(g_pick_lock);
	if (files && files[0]) { g_pick_result = files[0]; g_pick_done = true; }
}
static void pick_file(SDL_Window *w, std::string *target, const SDL_DialogFileFilter *f, int nf) { g_pick_target = target; SDL_ShowOpenFileDialog(picked, nullptr, w, f, nf, nullptr, false); }
static void pick_folder(SDL_Window *w, std::string *target) { g_pick_target = target; SDL_ShowOpenFolderDialog(picked, nullptr, w, nullptr, false); }
static void pick_poll(void) {
	std::lock_guard<std::mutex> l(g_pick_lock);
	if (g_pick_done && g_pick_target) *g_pick_target = g_pick_result;
	g_pick_done = false;
}
static bool input_text(const char *label, std::string &s, float w = -1, const char *hint = nullptr) {   /* ImGui::InputText over a std::string */
	char buf[2048]; snprintf(buf, sizeof buf, "%s", s.c_str());
	ImGui::SetNextItemWidth(w);
	bool ch = hint ? ImGui::InputTextWithHint(label, hint, buf, sizeof buf) : ImGui::InputText(label, buf, sizeof buf);
	if (ch) s = buf;
	return ch;
}
static bool path_row(const char *id, std::string &s, const char *hint) {   /* a path field with Browse... beside it: true when Browse is pressed */
	float bw = ImGui::CalcTextSize("Browse…").x + ImGui::GetStyle().FramePadding.x * 2;
	input_text(id, s, -bw - ImGui::GetStyle().ItemSpacing.x, hint);
	ImGui::SameLine();
	ImGui::PushID(id); bool r = ImGui::Button("Browse…"); ImGui::PopID();
	return r;
}

/* ---- the stages, as commands */
static void build_steps(std::vector<Step> &steps, const std::string &id, int group = 0) {   /* analyse, recompile, build: each its own "@@" step */
	steps.push_back(step("Step 1 of 3: analysing the game", vitarecomp({"analyze", id}), group));
	steps.push_back(step("Step 2 of 3: recompiling it to C", vitarecomp({"recompile", id}), group));
	steps.push_back(step("Step 3 of 3: compiling the native program", vitarecomp({"build", id}), group));
	steps.push_back(step("Ready to play", {}, group));
}
static void start_build(const Game &g) { std::vector<Step> s; build_steps(s, g.id); task_start("Building " + g.name, "build", g.id, s); }
static bool needs_online_name(const Game &g);   /* (below: an online game, and no name of the player's own yet) */
static std::string g_name_game;                  /* the game waiting on the online name prompt (online_name_modal) */
static void start_play_now(const Game &g);
static void start_play(const Game &g) {
	if (needs_online_name(g)) { g_name_game = g.id; return; }
	start_play_now(g);
}
static void start_play_now(const Game &g) {   /* (ATIV_LAUNCHER: the game's menu offers "Back to the library"; the launcher comes back to the front when it ends) */
	Step s = step("Running " + g.name, vitarecomp({"run", g.id})); s.env.push_back("ATIV_LAUNCHER=1");
	if (p5d_mode()) {   /* no online update channel: the exe the player runs brings its build, so start at once --
	                    * through the same p5d step as the UI's button (the CLI and the button must launch alike) */
		p5d_start_play(p5d_res_index());
		return;
	}
	/* ready first: a build older than these tools (Nativ was updated) is brought up to date before the game starts, so an
	 * update reaches every game; when it's current that's a moment */
	Step r = step("Checking " + g.name + "'s build is up to date", vitarecomp({"ready", g.id}));
	task_start("Playing " + g.name, "play", g.id, {r, s});
}

/* ---- a controller's L1 / R1 (or Ctrl+Tab, Ctrl+Shift+Tab) step a row of tabs: -1, +1, or 0 -- not while a control is held */
static int tab_step(void) {
	if (ImGui::IsAnyItemActive()) return 0;
	const bool ctrl = ImGui::GetIO().KeyCtrl, shift = ImGui::GetIO().KeyShift;
	if (ImGui::IsKeyPressed(ImGuiKey_GamepadL1, false) || (ctrl && shift && ImGui::IsKeyPressed(ImGuiKey_Tab, false))) return -1;
	if (ImGui::IsKeyPressed(ImGuiKey_GamepadR1, false) || (ctrl && !shift && ImGui::IsKeyPressed(ImGuiKey_Tab, false))) return 1;
	return 0;
}
static void tab_hint(void) {   /* (shown with a controller connected) */
	if (SDL_HasGamepad()) { ImGui::SameLine(); ImGui::AlignTextToFramePadding(); ImGui::TextDisabled("L1 / R1"); }
}

/* ---- shared pieces of the setup and the dialogs */
static int g_add_kind = 0;   /* 0 a folder to search, 1 a PKG file, 2 a game folder */
static std::string g_add_path, g_add_license, g_fw_path, g_scan_path;

/* "Where's my licence?": a PKG carries none (PSN gives each owner their own, the PKG is the same for everyone); the
 * owner's Vita has it -- a game installed from a PKG keeps it in its folder, sce_sys/package/work.bin; a game bought
 * and installed the usual way gets one written by the NoNpDrm plugin when started, ux0:nonpdrm/license/app/.
 * Searching a folder that holds the licence file finds it by its content id. */
static void center_next_popup(void);
static void licence_help_popup(void) {
	center_next_popup();
	if (!ImGui::BeginPopup("licence_help")) return;
	const float em = ImGui::GetFontSize();
	ImGui::PushTextWrapPos(em * 30);
	ImGui::TextUnformatted("Where's my licence?");
	ui::muted_wrapped("A PKG never carries one: PSN keeps a licence for each owner, and the PKG is the same file for everyone. Your Vita has yours:");
	ImGui::Bullet(); ImGui::TextWrapped("A game installed from its PKG: its folder holds the licence, ux0:app/<title>/sce_sys/package/work.bin. Copy the whole game folder and nothing else is needed.");
	ImGui::Bullet(); ImGui::TextWrapped("A game bought and installed the usual way: with the NoNpDrm plugin on, start the game once. Its licence is then saved as a .rif file in ux0:nonpdrm/license/app/<title>/.");
	ImGui::Bullet(); ImGui::TextWrapped("Copy that file (or the whole ux0:nonpdrm folder) next to your PKG and search the folder: Nativ matches each licence to its game.");
	ui::muted_wrapped("Easiest: Licences, From my Vita… fetches them all at once over Wi-Fi. Nativ keeps your licences on this computer only.");
	ImGui::PopTextWrapPos();
	ImGui::EndPopup();
}
static void licence_help_link(void) { if (ImGui::TextLink("Where's my licence?")) ImGui::OpenPopup("licence_help"); licence_help_popup(); }

/* ---- the player's licences: how many are kept, and three ways in -- the Vita itself (VitaShell's FTP), a folder (a
 * copied ux0:nonpdrm, licence files kept anywhere), a Vita3K install's -- each once; a folder search keeps the ones it
 * finds too. Fetched or imported, every later PKG, update and add-on of those games is added without asking. */
static int g_licences;   /* kept, counted at each library scan */
static std::string g_vita_addr, g_lic_folder;
static bool g_open_vita_popup;   /* (ATIV_SHOT_UI=add:vita: the popup open in a screenshot) */
static std::string vita3k_licences(void) {   /* Vita3K's ux0/license where it keeps it by default (SDL's pref path Vita3K/Vita3K), "" none */
	const char *home = getenv("HOME"), *appdata = getenv("APPDATA"), *xdg = getenv("XDG_DATA_HOME");
	std::vector<std::string> bases;
	if (home) { bases.push_back(std::string(home) + "/Library/Application Support/Vita3K/Vita3K"); bases.push_back((xdg ? std::string(xdg) : std::string(home) + "/.local/share") + "/Vita3K/Vita3K"); }
	if (appdata) bases.push_back(std::string(appdata) + "/Vita3K/Vita3K");
	for (const std::string &b : bases) for (const char *sub : {"/ux0/license", "/fs/ux0/license"}) if (exists(b + sub)) return b + sub;
	return "";
}
static void count_licences(void) {
	g_licences = 0;
	if (DIR *d = opendir((g_dump + "/licenses").c_str())) { while (dirent *e = readdir(d)) { size_t n = strlen(e->d_name); g_licences += n > 4 && !strcmp(e->d_name + n - 4, ".rif"); } closedir(d); }
}
static void center_next_popup(void) { const ImGuiViewport *vp = ImGui::GetMainViewport(); ImGui::SetNextWindowPos(ImVec2(vp->WorkPos.x + vp->WorkSize.x * 0.5f, vp->WorkPos.y + vp->WorkSize.y * 0.5f), ImGuiCond_Appearing, ImVec2(0.5f, 0.5f)); }
static void vita_licences_popup(void) {
	center_next_popup();
	if (!ImGui::BeginPopup("vita_licences")) return;
	const float em = ImGui::GetFontSize();
	ImGui::PushTextWrapPos(em * 28);
	ImGui::TextUnformatted("Get your licences from your Vita");
	ui::muted_wrapped("Your Vita and this computer on the same network. Nativ reads only licence files, nothing else.");
	ImGui::TextWrapped("1. On the Vita, open VitaShell and press SELECT. It shows an address like ftp://192.168.0.50:1337.");
	ImGui::TextWrapped("2. Type that address here:");
	if (g_vita_addr.empty()) g_vita_addr = g_prefs["vita_address"];
	input_text("##vaddr", g_vita_addr, em * 16, "192.168.0.50:1337");
	ImGui::SameLine();
	ImGui::BeginDisabled(g_vita_addr.empty() || g_task.running);
	if (ui::primary_button("Get licences")) {
		std::string a = g_vita_addr; if (a.rfind("ftp://", 0) == 0) a = a.substr(6); while (!a.empty() && a.back() == '/') a.pop_back();
		prefs_set("vita_address", a);
		task_start("Getting licences from the Vita", "licences", "", {step("Reading the Vita", vitarecomp({"licenses", "vita", a}))});
		ImGui::CloseCurrentPopup();
	}
	ImGui::EndDisabled();
	ui::muted_wrapped("A game bought and installed the usual way has a licence only the Vita can use: start it once with the NoNpDrm plugin on, then get licences again.");
	ImGui::PopTextWrapPos();
	ImGui::EndPopup();
}
static void licences_row(SDL_Window *win) {
	ImGui::PushID("licences");
	ui::dot(g_licences ? ui::ready : ui::border);
	ImGui::Text("Licences: %d kept", g_licences); ImGui::SameLine();
	ImGui::BeginDisabled(g_task.running);
	if (ImGui::SmallButton("From my Vita…") || g_open_vita_popup) { ImGui::OpenPopup("vita_licences"); g_open_vita_popup = false; }
	ImGui::SameLine(); if (ImGui::SmallButton("From a folder…")) { g_lic_folder.clear(); pick_folder(win, &g_lic_folder); }
	std::string v3k = vita3k_licences();
	if (!v3k.empty()) { ImGui::SameLine(); if (ImGui::SmallButton("From Vita3K")) task_start("Importing Vita3K's licences", "licences", "", {step("", vitarecomp({"licenses", "vita3k", v3k}))}); }
	ImGui::EndDisabled();
	if (!g_lic_folder.empty() && !g_task.running) {   /* (a folder picked: its licences in) */
		task_start("Importing licences", "licences", "", {step("", vitarecomp({"licenses", "import", g_lic_folder}))});
		g_lic_folder.clear();
	}
	vita_licences_popup();
	ImGui::PopID();
}

/* a folder search's finds (vitarecomp scan: pipeline/packs.py's rows) -- games, updates, add-ons, firmware files, each
 * with what its game pack says of that version -- picked for adding in one go */
struct Found { std::string kind, form, id, version, status, licence, name, path, licence_file, content_id, note; bool pick = false; };
/* the player's licences, kept once (pipeline/licenses.py: <dump>/licenses/<content id>.rif): add finds a copy's
 * there by itself, so a row whose licence is kept -- by this search, or fetched from the Vita meanwhile -- is ready */
static std::string kept_licence(const std::string &cid) { std::string p = g_dump + "/licenses/" + cid + ".rif"; return !cid.empty() && cid != "-" && exists(p) ? p : ""; }
static std::vector<Found> g_found;
static bool g_found_ready;   /* a search finished: its rows (maybe none) are in g_found */
static std::string scan_file(void) { std::string d = pref_dir(); return d.empty() ? g_dump + "/.scan.tsv" : d + "scan.tsv"; }
static bool playable_status(const std::string &st) { return st == "recommended" || st == "supported" || st == "check"; }
static void scan_load(const std::string &path) {
	g_found.clear(); g_found_ready = true;
	FILE *f = fopen(path.c_str(), "r"); if (!f) return;
	char line[4096];
	while (fgets(line, sizeof line, f)) {
		std::vector<std::string> c(1);
		for (const char *q = line; *q && *q != '\n' && *q != '\r'; q++) { if (*q == '\t') c.emplace_back(); else c.back() += *q; }
		if (c.size() < 8) continue;
		Found x; x.kind = c[0]; x.form = c[1]; x.id = c[2]; x.version = c[3]; x.status = c[4]; x.licence = c[5]; x.name = c[6]; x.path = c[7];
		if (c.size() > 8) x.licence_file = c[8];   /* (licence "file": a kept one, or one found elsewhere in the folder) */
		if (c.size() > 9) x.content_id = c[9];
		if (c.size() > 10) x.note = c[10];   /* (a copy Nativ can't play as it is: which release and version it does) */
		/* picked to start with: what plays and needs nothing typed in; the firmware when none is installed (the newest file) */
		if (x.kind == "game" || x.kind == "update") {
			bool dup = false; for (const Found &y : g_found) dup |= y.pick && y.kind == x.kind && y.id == x.id;
			x.pick = !dup && playable_status(x.status);   /* (one still needing its licence is ticked, its field showing; it's added once it has one) */
		} else if (x.kind == "firmware" && x.status == "firmware" && !g_firmware) {
			for (Found &y : g_found) if (y.kind == "firmware") y.pick = false;   /* (rows come sorted by version) */
			x.pick = true;
		}
		g_found.push_back(x);
	}
	fclose(f);
}
static bool found_ready(const Found &x) {   /* it has what adding it needs */
	if (x.kind == "firmware") return true;
	if (!kept_licence(x.content_id).empty()) return true;
	if (x.licence == "rif" || (x.kind == "game" && x.licence == "no")) return !x.licence_file.empty();
	if (x.kind == "update" && x.licence == "no") {   /* it decrypts with its game's licence: the game is being added with one */
		for (const Found &y : g_found) if (y.pick && y.kind == "game" && y.id == x.id && found_ready(y)) return true;
		return false;
	}
	return true;
}
static std::vector<Step> found_steps(int *n, std::vector<std::string> *titles) {   /* the firmware first, then per game: the game and its update kept, imported, built once */
	std::vector<Step> steps;   /* (each its own group: one failing doesn't stop the rest) */
	int group = 0;
	*n = 0;
	for (const Found &x : g_found)
		if (x.pick && x.kind == "firmware") { steps.push_back(step("Installing the firmware " + x.version, vitarecomp({"firmware", x.path}), ++group)); ++*n; break; }
	std::vector<std::string> ids;
	for (const Found &x : g_found) if (x.pick && (x.kind == "game" || x.kind == "update") && std::find(ids.begin(), ids.end(), x.id) == ids.end()) ids.push_back(x.id);
	if (titles) *titles = ids;
	for (const std::string &id : ids) {
		std::vector<const Found *> items;
		for (const char *k : {"game", "update"})
			for (const Found &x : g_found) if (x.pick && x.id == id && x.kind == k && found_ready(x)) { items.push_back(&x); break; }
		if (items.empty()) continue;
		bool pack = false;
		for (const Found &x : g_found) pack |= x.id == id && x.status != "nopack";
		++group;
		for (const Found *xp : items) {
			const Found &x = *xp;
			std::vector<std::string> argv = vitarecomp({"add", x.path});
			if (!x.licence_file.empty()) argv.insert(argv.end(), {"--license", x.licence_file});
			argv.push_back("--no-build");
			steps.push_back(step(x.kind == "update" ? "Adding its update " + x.version : "Adding " + x.name + " " + x.version, argv, group));
			++*n;
		}
		steps.push_back(step("Checking its version", vitarecomp({"import", id}), group));   /* (the game with its update layered over it) */
		if (pack) build_steps(steps, id, group);
	}
	return steps;
}
static void found_status(const Found &x) {   /* what its game pack says of it, as a dot and a line */
	struct S { const char *key, *text; int tone; };   /* tone: 0 good, 1 a caution, 2 neutral */
	static const S st[] = {
		{"recommended", "Recommended version", 0}, {"supported", "Supported version", 0}, {"check", "Checked against its game pack when added", 2},
		{"unsupported", "This version isn't supported yet", 1}, {"nopack", "No game pack yet: experimental", 1},
		{"otherregion", "This region's release isn't supported yet", 1},
		{"added", "Already in your library", 2}, {"licensed", "Nothing to add: the game gets its add-ons", 2},
		{"installed", "Already installed", 2}, {"firmware", "Not installed yet", 0}};
	for (const S &e : st) if (x.status == e.key) {
		ui::dot(e.tone == 0 ? ui::ready : e.tone == 1 ? ui::warn : ui::border);
		ImGui::TextDisabled("%s", e.text);
		if (!x.note.empty()) { ImGui::PushTextWrapPos(0.0f); ImGui::PushStyleColor(ImGuiCol_Text, ui::muted); ImGui::TextWrapped("%s.", x.note.c_str()); ImGui::PopStyleColor(); ImGui::PopTextWrapPos(); }
		return;
	}
	ui::dot(ui::border); ImGui::TextDisabled("%s", x.status.c_str());
}
static void found_list(void) {
	const float em = ImGui::GetFontSize();
	if (g_found.empty()) { ui::muted_wrapped("Nothing found there: no game or update folders (with sce_sys/param.sfo), PKGs or firmware update files (.PUP)."); return; }
	float row_h = ImGui::GetTextLineHeightWithSpacing() * 3.2f;
	ImGui::BeginChild("found", ImVec2(0, std::min(em * 17.0f, row_h * g_found.size() + em)), ImGuiChildFlags_Borders);
	for (size_t i = 0; i < g_found.size(); i++) {
		Found &x = g_found[i];
		ImGui::PushID((int)i);
		if (i) ImGui::Separator();
		bool can = x.kind == "game" || x.kind == "update" || (x.kind == "firmware" && x.status == "firmware");
		ImGui::BeginDisabled(!can || g_task.running);
		if (ImGui::Checkbox("##pick", &x.pick) && x.pick)   /* one copy of a game (or of its update) at a time */
			for (Found &y : g_found) if (&y != &x && y.kind == x.kind && y.id == x.id && x.kind != "firmware") y.pick = false;
		ImGui::EndDisabled();
		ImGui::SameLine();
		ImGui::BeginGroup();
		const char *kind = x.kind == "game" ? "Game" : x.kind == "update" ? "Update" : x.kind == "addon" ? "Add-on" : "Firmware file";
		ImGui::TextUnformatted(x.name.c_str()); ImGui::SameLine();
		ImGui::TextDisabled("%s%s%s%s", kind, x.version.empty() ? "" : " ", x.version.c_str(), x.form == "pkg" ? " (PKG)" : "");
		found_status(x);
		if (x.pick && (x.licence == "rif" || (x.kind == "game" && x.licence == "no")) && kept_licence(x.content_id).empty()) {
			ui::dot(ui::warn); ImGui::TextDisabled("Needs its licence file (.rif or work.bin).");
			licence_help_link();
			if (path_row("##licfile", x.licence_file, "Its licence file (.rif or work.bin)")) pick_file(nullptr, &x.licence_file, nullptr, 0);
		} else if (x.pick && x.kind == "update" && x.licence == "no" && !found_ready(x)) {
			ui::dot(ui::warn); ImGui::TextDisabled("Add its game too: an update decrypts with its game's licence");
		}
		ImGui::PushFont(nullptr, em * 0.85f); ImGui::PushStyleColor(ImGuiCol_Text, ui::muted);
		ImGui::TextUnformatted(x.path.c_str());
		if (!kept_licence(x.content_id).empty() && (x.kind == "game" || x.kind == "update")) ImGui::TextUnformatted("Licence: kept");
		else if (x.licence == "file") ImGui::Text("Licence: %s", x.licence_file.c_str());
		ImGui::PopStyleColor(); ImGui::PopFont();
		ImGui::EndGroup();
		ImGui::PopID();
	}
	ImGui::EndChild();
}
static bool search_form(SDL_Window *win) {   /* a folder searched for games, updates and the firmware file; true when adding started */
	ui::muted_wrapped("A folder to look through, every subfolder too: a copy of your Vita's ux0: (its app, patch and addcont folders) or a downloads folder. Games, their updates and the firmware file are found and checked against the game packs, which play the games' US releases at the versions listed.");
	ImGui::Spacing();
	if (path_row("##scanpath", g_scan_path, "Choose a folder to search")) pick_folder(win, &g_scan_path);
	const bool searching = g_task.running && g_task.kind == "scan";
	ImGui::BeginDisabled(g_scan_path.empty() || g_task.running);
	bool go = g_found_ready ? ImGui::Button("Search again") : ui::primary_button("Search");
	ImGui::EndDisabled();
	if (go) { g_found.clear(); g_found_ready = false; task_start("Searching a folder", "scan", "", {step("Searching", vitarecomp({"scan", g_scan_path, "--import-licences", "--out", scan_file()}))}); }
	if (searching) { ImGui::SameLine(); ui::spinner(ui::accent); ImGui::TextDisabled("Searching…"); }
	if (!g_found_ready) return false;
	ImGui::Spacing();
	found_list();
	int n = 0; std::vector<std::string> titles; std::vector<Step> steps = found_steps(&n, &titles);
	ImGui::Spacing();
	ImGui::BeginDisabled(n == 0 || g_task.running);
	std::string label = n ? "Add " + std::to_string(n) + (n == 1 ? " item" : " items") : "Add";
	bool started = ui::primary_button(label.c_str());
	ImGui::EndDisabled();
	int waiting = 0; for (const Found &x : g_found) waiting += x.pick && (x.kind == "game" || x.kind == "update") && !found_ready(x);
	if (waiting) { ImGui::SameLine(); ImGui::TextDisabled("%d waiting for a licence", waiting); }
	if (started) {
		task_start(n == 1 ? "Adding from the folder" : "Adding " + std::to_string(n) + " items", "add", "", steps);
		g_task.games = titles;   /* (their cards show the chain's step) */
		g_found.clear(); g_found_ready = false;
	}
	return started;
}
static bool add_form(SDL_Window *win) {   /* a player's own copy -> decrypted, imported, analysed, recompiled, built; true when started */
	static const char *const kinds[] = {"Search a folder", "A PKG file", "A game folder"};
	ui::segmented(kinds, 3, &g_add_kind); tab_hint();
	g_add_kind = (g_add_kind + tab_step() + 3) % 3;
	ImGui::Dummy(ImVec2(0, ImGui::GetFontSize() * 0.15f));
	if (g_add_kind == 0) return search_form(win);
	const bool pkg_kind = g_add_kind == 1;
	ui::muted_wrapped(pkg_kind ? "The .pkg of a game you own, with its licence file: the .rif from your Vita. Or its update's PKG, once the game is added (it uses the game's licence)."
	                           : "A game folder copied from your Vita (ux0:app/<title>: it carries its licence, sce_sys/package/work.bin), or one already decrypted; or its update (ux0:patch/<title>), once the game is added.");
	licence_help_link();
	ImGui::Spacing();
	if (path_row("##addpath", g_add_path, pkg_kind ? "Choose the .pkg file" : "Choose the game folder")) {
		static const SDL_DialogFileFilter pkg[] = {{"PS Vita package", "pkg"}};
		if (pkg_kind) pick_file(win, &g_add_path, pkg, 1); else pick_folder(win, &g_add_path);
	}
	if (path_row("##lic", g_add_license, pkg_kind ? "Its licence file (.rif or work.bin)" : "Its licence file, if the folder has none (.rif or work.bin)")) pick_file(win, &g_add_license, nullptr, 0);
	ImGui::Spacing();
	bool started = false;
	ImGui::BeginDisabled(g_add_path.empty() || g_task.running);
	if (ui::primary_button("Add this game")) {
		std::vector<std::string> argv = vitarecomp({"add", g_add_path});
		if (!g_add_license.empty()) argv.insert(argv.end(), {"--license", g_add_license});
		task_start("Adding a game", "add", "", {step("Decrypting and importing your copy", argv), step("Added")});
		g_add_path.clear(); g_add_license.clear();
		started = true;
	}
	ImGui::EndDisabled();
	return started;
}
static void task_line(void) {   /* the running task, inline: spinner, its step, Cancel; or the last failure */
	if (g_task.running) {
		ui::spinner(ui::accent);
		ImGui::TextUnformatted(g_task.name.c_str()); ImGui::SameLine(); ImGui::TextDisabled("%s", task_status().c_str());
	} else if (!g_failed.empty()) {
		ui::dot(ui::error); ImGui::TextColored(ui::error, "%s didn’t finish.", g_failed.c_str()); ImGui::SameLine();
		if (ImGui::TextLink("Show the log")) g_drawer = true;
	}
}

/* ---- settings (runtime/core/settings.h): the shared file every game reads -- display, controls, sound, online ID -- beside this
 * launcher's own files, and each game's own (its options, and where it keeps a value of its own). A game reads its own
 * file first, then the shared one; a change in any game's menu changes the shared file. The launcher's Settings page
 * edits the shared file, a card's Game settings its game's. Each change is read-modify-written at once (a running game
 * merges its own changes the same way). */
struct Ini { std::vector<std::pair<std::string, std::string>> kv; };
static Ini ini_load(const std::string &path) {
	Ini x; FILE *f = fopen(path.c_str(), "r"); if (!f) return x;
	char line[512];
	while (fgets(line, sizeof line, f)) {
		std::string l = line; size_t eq = l.find('=');
		size_t b = l.find_first_not_of(" \t"); if (b == std::string::npos || l[b] == '#' || l[b] == ';' || eq == std::string::npos) continue;
		auto trim = [](std::string v) { size_t a = v.find_first_not_of(" \t\r\n"), e = v.find_last_not_of(" \t\r\n"); return a == std::string::npos ? std::string() : v.substr(a, e - a + 1); };
		x.kv.push_back({trim(l.substr(0, eq)), trim(l.substr(eq + 1))});
	}
	fclose(f);
	return x;
}
static const std::string *ini_find(const Ini &x, const std::string &k) { for (auto &e : x.kv) if (e.first == k) return &e.second; return nullptr; }
static void ini_set(Ini &x, const std::string &k, const std::string &v) { for (auto &e : x.kv) if (e.first == k) { e.second = v; return; } x.kv.push_back({k, v}); }
static void ini_erase(Ini &x, const std::string &k) { x.kv.erase(std::remove_if(x.kv.begin(), x.kv.end(), [&](const std::pair<std::string, std::string> &e) { return e.first == k; }), x.kv.end()); }
static void ini_save(const Ini &x, const std::string &path, const char *header) {
	std::string tmp = path + ".tmp"; FILE *f = fopen(tmp.c_str(), "w"); if (!f) return;
	fprintf(f, "%s\n", header);
	for (auto &e : x.kv) fprintf(f, "%s = %s\n", e.first.c_str(), e.second.c_str());
	if (fclose(f) == 0) {
#ifdef _WIN32
		MoveFileExA(tmp.c_str(), path.c_str(), MOVEFILE_REPLACE_EXISTING);   /* (rename refuses an existing file on Windows) */
#else
		rename(tmp.c_str(), path.c_str());
#endif
	}
}
static const char *const SHARED_HEADER = "# P5D 移植版 settings for the game (the launcher's Settings, and the game's own menu; runtime/core/settings.h)";
static const char *const GAME_HEADER = "# vitarecomp settings for this game: its own options, and where it differs from the shared settings (runtime/core/settings.h)";
static bool game_key(const std::string &k) {   /* (settings.c's game_key: kept in the game's own file) */
	for (const char *g : {"fov", "view_distance", "scenery_detail", "character_detail", "private_server", "net_redirect", "menu_hint_shown", "controller_layout"}) if (k == g) return true;
	return false;
}
/* the shared keys' defaults where a game reads no value (runtime/core/settings.h; the consumers' own) */
static const char *setting_default(const std::string &k) {
	static const std::pair<const char *, const char *> d[] = {{"render_scale", "1"}, {"fullscreen", "0"}, {"aspect_ratio", "native"}, {"hud_layout", "edges"},
		{"aspect", "fit"}, {"frame_rate", "30"}, {"post_aa", "1"}, {"sharpen", "0.35"}, {"vibrance", "0"}, {"anisotropy", "16"}, {"shadow_filter", "1"}, {"full_res_world", "1"},
		{"ssao", "1"}, {"ssao_strength", "1"}, {"osd", "0"}, {"input_mode", "auto"}, {"mouse_look", "1"}, {"raw_look", "1"}, {"mouse_sens", "1"},
		{"mouse_invert", "0"}, {"shoulder_buttons", "bumpers"}, {"touch_cursor_speed", "1"}, {"gyro", "1"}, {"gyro_pose", "upright"}, {"gyro_sens", "1"}, {"volume", "1"}, {"online_id", ""}, {"online", "1"},
		{"camera", "light"}, {"save_dialog", "ask"}, {"audio_sync_trim_ms", "0"}, {"audio_buffers", "1"}};
	for (auto &e : d) if (k == e.first) return e.second;
	return nullptr;
}
/* keys only some games read (an online one, a camera one, one with ambient occlusion): a game without the key never chose */
static bool some_games_key(const std::string &k) { return k == "online_id" || k == "online" || k == "np_account_id" || k == "np_age" || k == "camera" || k == "ssao" || k == "ssao_strength"; }
static std::string shared_path(void) { std::string d = pref_dir(); return d.empty() ? "" : d + "settings.ini"; }
static std::string game_settings_path(const std::string &id) { return g_dump + "/decrypted/" + id + "/recomp/settings.ini"; }
static std::string fmt_g(double v) { char b[32]; snprintf(b, sizeof b, "%g", v); return b; }

/* the starting point on a new machine: the look most players want from a PC version -- fullscreen, sharp for this display,
 * the full width of the screen, the mouse aiming 1:1, softer shadows (the games' own menus, and Settings, change it) */
static int recommended_scale(void) {
	const SDL_DisplayMode *m = SDL_GetCurrentDisplayMode(SDL_GetPrimaryDisplay());
	float h = m ? m->h * (m->pixel_density > 0 ? m->pixel_density : 1.0f) : 1080;
	int k = (int)lroundf(h / 544.0f); return k < 2 ? 2 : k > 4 ? 4 : k;
}
static void recommended_into(Ini &x) {   /* (no frame_rate: 60 is experimental and makes parts timed in 1/30 s steps run fast; the game decides) */
	ini_set(x, "fullscreen", "1"); ini_set(x, "render_scale", std::to_string(recommended_scale())); ini_set(x, "aspect_ratio", "window");
	ini_set(x, "raw_look", "1"); ini_set(x, "shadow_filter", "2");
}
/* once, when there is no shared file yet: it starts as what this library's games agree on (each key: the value most of
 * their files hold; a tie, the most recently changed file's), or the recommended set on a new install. Then, every
 * start, a game's file drops a shared key holding the same value as the shared file -- no change in what it plays with,
 * and what's left in it is what differs (its Game settings list those) */
static void settings_migrate(void) {
	std::string sp = shared_path(); if (sp.empty()) return;
	if (p5d_mode() && exists(sp) && g_prefs["p5d_frame_rate_fixed"] != "1") {
		/* the first builds' recommended set forced frame_rate = 60 (experimental): parts timed in 1/30 s steps ran
		 * fast (reported 2026-11-07). Back to the game's own rate, once; Settings can still choose 60 on purpose. */
		Ini cur = ini_load(sp);
		bool had60 = false;
		for (auto &e : cur.kv) if (e.first == "frame_rate" && e.second == "60") had60 = true;
		if (had60) {
			ini_set(cur, "frame_rate", "30");
			ini_save(cur, sp, SHARED_HEADER);
		}
		prefs_set("p5d_frame_rate_fixed", "1");
	}
	struct F { std::string path; Ini x; time_t mtime; };
	std::vector<F> files;
	if (DIR *d = opendir((g_dump + "/decrypted").c_str())) {
		while (dirent *e = readdir(d)) {
			if (e->d_name[0] == '.') continue;
			std::string p = g_dump + "/decrypted/" + e->d_name + "/recomp/settings.ini"; struct stat st;
			if (stat(p.c_str(), &st) == 0) files.push_back({p, ini_load(p), st.st_mtime});
		}
		closedir(d);
	}
	/* (a shared file holding only np_* keys is a game's account record -- a game ran before the launcher ever did -- not
	 * anyone's choices: it starts like a new one, those keys kept) */
	Ini before = exists(sp) ? ini_load(sp) : Ini();
	bool chosen = false; for (auto &e : before.kv) chosen |= e.first.rfind("np_", 0) != 0;
	if (!chosen) {
		/* a game whose file lacks a key plays with its default: a vote for leaving the key out (but for keys only some
		 * games read) -- so one game's choice stays that game's, and what most games chose becomes everyone's */
		Ini sh; std::map<std::string, std::map<std::string, std::pair<int, time_t>>> votes;
		const std::string ABSENT = std::string("\x01") + "absent";
		for (const F &f : files) for (auto &e : f.x.kv) if (!game_key(e.first) && e.first.rfind("bind_", 0) != 0) {
			auto &v = votes[e.first][e.second]; v.first++; if (f.mtime > v.second) v.second = f.mtime;
		}
		for (auto &k : votes) if (!some_games_key(k.first))
			for (const F &f : files) if (!ini_find(f.x, k.first)) { auto &v = k.second[ABSENT]; v.first++; if (f.mtime > v.second) v.second = f.mtime; }
		for (auto &k : votes) {
			const std::string *best = nullptr; std::pair<int, time_t> bv{0, 0};
			for (auto &v : k.second) if (v.second > bv) { bv = v.second; best = &v.first; }
			if (best && *best != ABSENT) ini_set(sh, k.first, *best);
		}
		bool voted = false; for (auto &k : votes) voted |= k.first.rfind("np_", 0) != 0;   /* (account keys alone: no one's choices) */
		if (!voted) recommended_into(sh);
		for (auto &e : before.kv) ini_set(sh, e.first, e.second);
		ini_save(sh, sp, SHARED_HEADER);
		fprintf(stderr, "settings: the shared file started %s (%s)\n", !voted ? "with the recommended set" : "from this library's games", sp.c_str());
	}
	Ini sh = ini_load(sp);
	for (F &f : files) {
		size_t before = f.x.kv.size();
		f.x.kv.erase(std::remove_if(f.x.kv.begin(), f.x.kv.end(), [&](const std::pair<std::string, std::string> &e) {
			if (game_key(e.first)) return false;
			const std::string *v = ini_find(sh, e.first); const char *d = setting_default(e.first);   /* (the value it would read without it) */
			return v ? *v == e.second : d && atof(d) == atof(e.second.c_str()) && (isdigit((unsigned char)d[0]) || e.second == d); }), f.x.kv.end());
		if (f.x.kv.size() != before) ini_save(f.x, f.path, GAME_HEADER);
	}
}

/* the Settings page's controls: each a settings row (ui_theme.h) over one key of an Ini, written at once */
struct SetTarget { Ini *x; std::string path; const char *header; };
static void target_write(const SetTarget &t, const std::string &k, const std::string &v) {   /* read-modify-write: a running game's changes stay */
	ini_set(*t.x, k, v);
	Ini disk = ini_load(t.path); ini_set(disk, k, v); ini_save(disk, t.path, t.header);
}
static std::string tget(const SetTarget &t, const char *k, const char *def) { const std::string *v = ini_find(*t.x, k); return v ? *v : def; }
static void seg_row(const SetTarget &t, const char *label, const char *expl, const char *key, const char *def, std::initializer_list<std::pair<const char *, const char *>> opts) {
	ui::row(label, expl);
	ImGui::PushID(key);
	std::vector<const char *> names; std::string cur = tget(t, key, def); int v = 0, i = 0;
	for (auto &o : opts) { if (cur == o.first) v = i; names.push_back(o.second); i++; }
	if (ui::segmented(names.data(), (int)names.size(), &v)) target_write(t, key, opts.begin()[v].first);
	ImGui::PopID();
}
static void toggle_row(const SetTarget &t, const char *label, const char *expl, const char *key, bool def) {
	ui::row(label, expl);
	bool on = atoi(tget(t, key, def ? "1" : "0").c_str()) != 0;
	if (ui::toggle(key, &on)) target_write(t, key, on ? "1" : "0");
}
static void slider_row(const SetTarget &t, const char *label, const char *expl, const char *key, double def, float lo, float hi, const char *fmt, float shown = 1, ImGuiSliderFlags fl = 0) {
	ui::row(label, expl);
	float v = (float)atof(tget(t, key, fmt_g(def).c_str()).c_str()) * shown;
	ImGui::SetNextItemWidth(-FLT_MIN);
	std::string id = std::string("##") + key;
	if (ImGui::SliderFloat(id.c_str(), &v, lo, hi, fmt, fl)) ini_set(*t.x, key, fmt_g(v / shown));
	if (ImGui::IsItemDeactivatedAfterEdit()) target_write(t, key, tget(t, key, ""));   /* (written once the drag ends) */
}
static bool g_settings_open; static int g_settings_tab; static Ini g_shared;
static bool g_setup_online = true;   /* setup's Play online, written with the name */
static bool g_settings_writable = true;   /* (false in a screenshot run without ATIV_PREFS: it touches no one's settings) */

/* the online name (runtime/net/np.c np_online_id makes the same): others see "ntv_" and the player's name, up to 10
 * letters, digits, '-' or '_' -- or, with none chosen, "ntv_" and a tag of six from this install's account ID (settings
 * np_account_id: random, made once, here when no game has made it yet) */
/* online_status.txt beside the shared settings (runtime/net/online/status.c): a game playing online rewrites it every 5 s.
 * "" when there is none */
static std::string online_status_line(void) {
	std::string d = pref_dir(); if (d.empty()) return "";
	Ini st = ini_load(d + "online_status.txt");
	const std::string *tm = ini_find(st, "time"); if (!tm) return "";
	const long long ago = (long long)time(nullptr) - atoll(tm->c_str());
	auto num = [&](const char *k) { const std::string *v = ini_find(st, k); return v ? atoi(v->c_str()) : 0; };
	const std::string *g = ini_find(st, "game"); const std::string game = g && !g->empty() ? *g : "a game";
	const int linked = num("linked"), rooms = num("rooms_heard") + num("rooms_mine");
	char b[256];
	if (ago >= 0 && ago < 15) snprintf(b, sizeof b, "Online now in %s: %s, %d %s open.", game.c_str(), linked ? (std::to_string(linked) + (linked == 1 ? " other copy linked" : " other copies linked")).c_str() : "looking for other players", rooms, rooms == 1 ? "room" : "rooms");
	else {
		const long long m = ago / 60;
		const std::string when = m < 1 ? "a moment ago" : m < 60 ? std::to_string(m) + " min ago" : m < 48 * 60 ? std::to_string(m / 60) + " h ago" : std::to_string(m / 1440) + " days ago";
		snprintf(b, sizeof b, "Last online %s, in %s%s.", when.c_str(), game.c_str(), linked ? (", linked with " + std::to_string(linked) + (linked == 1 ? " other copy" : " other copies")).c_str() : "");
	}
	return b;
}
static const char *ONLINE_EXPL = "Games' online modes (Killzone: Mercenary, Unit 13) with other Project Nativ players, on your network and over the internet. They see your online name and your computer's IP address, as in any peer-to-peer game.";
static bool online_name_ok(const std::string &n) {
	return n.size() <= 10 && std::all_of(n.begin(), n.end(), [](char c) { return isalnum((unsigned char)c) || c == '-' || c == '_'; });
}
static std::string online_name(const Ini &shared) {   /* the chosen name, without a tag a user may have typed: "ntv_", or the ones before, "nativ_" and Project Ativ's "ativ_" */
	const std::string *v = ini_find(shared, "online_id"); std::string n = v ? *v : "";
	for (const char *tag : {"ntv_", "nativ_", "ativ_"}) if (!strncasecmp(n.c_str(), tag, strlen(tag))) return n.substr(strlen(tag));
	return n;
}
static bool game_option(const Game &g, const char *name);
static bool needs_online_name(const Game &g) {   /* asked once: an online game, online on, and the player hasn't named themselves */
	if (g_prefs["online_name_asked"] == "1" || !game_option(g, "online")) return false;
	const Ini sh = ini_load(shared_path());
	const std::string *on = ini_find(sh, "online");
	return !(on && atoi(on->c_str()) == 0) && online_name(sh).empty();
}
static std::string online_tag(Ini &shared) {
	const std::string *a = ini_find(shared, "np_account_id");
	uint64_t v = a ? strtoull(a->c_str(), nullptr, 16) : 0;
	if (!v) {
		std::random_device rd; v = ((uint64_t)rd() << 32 | rd()) | 1;
		char b[24]; snprintf(b, sizeof b, "%016llx", (unsigned long long)v);
		if (g_settings_writable) target_write(SetTarget{&shared, shared_path(), SHARED_HEADER}, "np_account_id", b);
	}
	static const char al[] = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789";   /* (no 0/O, 1/I lookalikes) */
	std::string tag; for (int n = 0; n < 6; n++, v >>= 5) tag += al[v & 31];
	return tag;
}
static void settings_modal(void) {
	game_folder_move_poll();
	const ImGuiViewport *vp = ImGui::GetMainViewport();
	const float em = ImGui::GetFontSize();
	if (g_settings_open && !ImGui::IsPopupOpen("Settings")) { ImGui::OpenPopup("Settings"); g_shared = ini_load(shared_path()); }
	ImGui::SetNextWindowSize(ImVec2(vp->WorkSize.x < 50 * em ? vp->WorkSize.x * 0.94f : 46 * em, vp->WorkSize.y * 0.86f), ImGuiCond_Always);
	ImGui::SetNextWindowPos(ImVec2(vp->WorkPos.x + vp->WorkSize.x * 0.5f, vp->WorkPos.y + vp->WorkSize.y * 0.5f), ImGuiCond_Always, ImVec2(0.5f, 0.5f));
	ImGui::PushStyleVar(ImGuiStyleVar_WindowPadding, ImVec2(1.6f * em, 1.3f * em)); ImGui::PushStyleVar(ImGuiStyleVar_WindowBorderSize, 1.0f);
	if (!ImGui::BeginPopupModal("Settings", nullptr, ImGuiWindowFlags_NoTitleBar | ImGuiWindowFlags_NoSavedSettings | ImGuiWindowFlags_NoMove)) { ImGui::PopStyleVar(2); return; }
	ImGui::PopStyleVar(2);
	ui::heading("Settings", em * 1.4f);
	ui::muted_wrapped("For every game. A game reads them when it starts; its own menu (F10) changes them too, for every game. A game's own options, and any value it keeps for itself, are under Game settings on its card.");
	ImGui::Dummy(ImVec2(0, em * 0.2f));
	static const char *const tabs[] = {"Display##st", "Controls##st", "Sound & online##st", "Storage##st"};
	ui::segmented(tabs, 4, &g_settings_tab); tab_hint();
	g_settings_tab = (g_settings_tab + tab_step() + 4) % 4;
	ImGui::Dummy(ImVec2(0, em * 0.2f));
	SetTarget t{&g_shared, shared_path(), SHARED_HEADER};
	ImGui::BeginChild("settings_rows", ImVec2(0, -ImGui::GetFrameHeightWithSpacing() - em * 0.4f), 0);
	if (ui::rows_begin("shared")) {
		if (g_settings_tab == 0) {
			ui::row("Resolution", "The game drawn at a multiple of the Vita's 960 × 544. Higher is sharper; 4× and up want a fast GPU.");
			{	ImGui::PushID("render_scale");
				const char *const names[6] = {"1×", "2×", "3×", "4×", "5×", "6×"}; int v = atoi(tget(t, "render_scale", "1").c_str()) - 1; if (v < 0) v = 0; if (v > 5) v = 5;
				if (ui::segmented(names, 6, &v)) target_write(t, "render_scale", std::to_string(v + 1));
				int r = recommended_scale(); if (r != v + 1) { char l[48]; snprintf(l, sizeof l, "%d× suits this display", r); if (ImGui::TextLink(l)) target_write(t, "render_scale", std::to_string(r)); }
				ImGui::PopID(); }
			toggle_row(t, "Fullscreen", "Also kept when you use the window's own fullscreen button.", "fullscreen", false);
			seg_row(t, "Widescreen", "Shows more of the game at the sides, in games that support it.", "aspect_ratio", "native", {{"native", "Off"}, {"21:9", "21:9"}, {"32:9", "32:9"}, {"window", "Window"}});
			seg_row(t, "HUD", "With widescreen on: the HUD at the screen's edges, in a 16:9 frame in the middle, or stretched.", "hud_layout", "edges", {{"edges", "Edges"}, {"16:9", "16:9"}, {"stretch", "Stretched"}});
			seg_row(t, "Picture fit", "How the picture fills the window.", "aspect", "fit", {{"fit", "Fit"}, {"stretch", "Stretch"}, {"fill", "Fill"}});
			seg_row(t, "Frame rate", "60 is experimental: parts of a game timed in fixed 1/30 s steps can run fast.", "frame_rate", "30", {{"30", "30"}, {"60", "60"}});
			toggle_row(t, "Anti-aliasing", "Smooths jagged edges (FXAA).", "post_aa", true);
			slider_row(t, "Sharpening", "Brings back detail lost to scaling and anti-aliasing.", "sharpen", 0.35, 0.0f, 100.0f, "%.0f%%", 100.0f);
			slider_row(t, "Dynamic Vibrance", "Our built-in vibrance: lifts dull colours without clipping saturated ones (0 = off).", "vibrance", 0, 0.0f, 100.0f, "%.0f%%");
			seg_row(t, "Texture filtering", "Keeps textures crisp when seen at an angle.", "anisotropy", "16", {{"1", "Off"}, {"2", "2×"}, {"4", "4×"}, {"8", "8×"}, {"16", "16×"}});
			seg_row(t, "Shadow edges", "How soft the edges of shadows are.", "shadow_filter", "1", {{"0", "Original"}, {"1", "Soft"}, {"2", "Softer"}});
			toggle_row(t, "Full-resolution world", "Games that draw their 3D world below the screen's resolution draw it at the full one. Sharper, at a GPU cost.", "full_res_world", true);
			toggle_row(t, "Ambient occlusion", "Soft shadows where surfaces meet, in games that support it.", "ssao", true);
			slider_row(t, "Occlusion strength", nullptr, "ssao_strength", 1.0, 0.0f, 200.0f, "%.0f%%", 100.0f);
			seg_row(t, "On-screen stats", "Frame rate and timings over the game. F1 cycles them.", "osd", "0", {{"0", "Off"}, {"1", "FPS"}, {"2", "Full"}});
		} else if (g_settings_tab == 1) {
			seg_row(t, "Play with", "Automatic follows the last device you touch.", "input_mode", "auto", {{"auto", "Automatic"}, {"pad", "Controller"}, {"kbm", "Keyboard & mouse"}});
			toggle_row(t, "Mouse look", "The mouse turns the camera and aims; left button R, right button L.", "mouse_look", true);
			seg_row(t, "Mouse aim", "Direct: the game turns exactly as far as the mouse moves (Uncharted, Unit 13, Killzone). Stick: the mouse moves the right stick. F8 switches in a game.", "raw_look", "1", {{"1", "Direct"}, {"0", "Stick"}});
			slider_row(t, "Mouse sensitivity", nullptr, "mouse_sens", 1.0, 0.1f, 5.0f, "%.2f×", 1, ImGuiSliderFlags_Logarithmic);
			toggle_row(t, "Invert vertical look", nullptr, "mouse_invert", false);
			seg_row(t, "L and R buttons", "The shoulder pair that is the game's L and R (aim and fire in a shooter). The other pair holds the touch cursor, or is L2 and R2 in a PS TV layout.", "shoulder_buttons", "bumpers", {{"bumpers", "Bumpers (L1 / R1)"}, {"triggers", "Triggers (L2 / R2)"}});
			slider_row(t, "Touch cursor speed", "Hold the shoulder pair that isn't L and R, and move a stick: the cursor is a finger on the touch screen.", "touch_cursor_speed", 1.0, 0.25f, 3.0f, "%.2f×");
			toggle_row(t, "Gyro", "A controller's gyro as the Vita's motion sensor.", "gyro", true);
			seg_row(t, "A level controller is a Vita held", "Upright, as in your hands, or flat on a table.", "gyro_pose", "upright", {{"upright", "Upright"}, {"flat", "Flat"}});
			slider_row(t, "Gyro sensitivity", nullptr, "gyro_sens", 1.0, 0.25f, 3.0f, "%.2f×");
		} else if (g_settings_tab == 2) {
			slider_row(t, "Volume", nullptr, "volume", 1.0, 0.0f, 100.0f, "%.0f%%", 100.0f);
			toggle_row(t, "Play online", ONLINE_EXPL, "online", true);
			{ const std::string st = online_status_line(); if (!st.empty()) ui::muted_wrapped(st.c_str()); }
			ui::row("Online name", "Others see ntv_ and your name, so players know you're on PC: up to 10 letters, digits, '-' or '_'.");
			{	static std::string oid; static bool init; if (!init || !ImGui::IsPopupOpen("Settings")) { oid = online_name(*t.x); init = true; }
				ImGui::AlignTextToFramePadding(); ImGui::TextUnformatted("ntv_"); ImGui::SameLine(0, 0);
				input_text("##oid", oid, -FLT_MIN);
				const bool ok = online_name_ok(oid);
				if (ImGui::IsItemDeactivatedAfterEdit() && ok) target_write(t, "online_id", oid);
				if (!ok) ui::muted_wrapped("Not saved: up to 10 letters, digits, '-' or '_'");
				else if (oid.empty()) ui::muted_wrapped(("Empty: you play as ntv_" + online_tag(*t.x) + ", a tag made for this computer.").c_str());
			}
		} else if (g_settings_tab == 3) {
			ui::heading("Game folder", em * 1.15f);
			ui::muted_wrapped("The whole game after building: the program, its saves, the firmware and the MODs. The default is this computer's app data folder; changing it later starts a new, empty library, so the game and firmware have to be imported there again.");
			ImGui::Dummy(ImVec2(0, em * 0.35f));
			ImGui::TextDisabled("Current folder");
			ImGui::TextWrapped("%s", g_dump.c_str());
			ImGui::Dummy(ImVec2(0, em * 0.2f));
			ImGui::BeginDisabled(g_task.running);
			if (ImGui::Button("Change folder…")) change_game_folder();
			ImGui::SameLine();
			if (ImGui::Button("Use default")) change_to_default_folder();
			ImGui::SameLine();
			if (ImGui::Button("Open folder")) open_folder(g_dump);
			ImGui::EndDisabled();
			ImGui::Dummy(ImVec2(0, em * 0.2f));
			ui::muted_wrapped(("Default: " + library_default_dir()).c_str());
			ui::muted_wrapped("Keep it on a local drive with space for several gigabytes. A folder inside the game's own download, or one this copy cannot write, is refused when it is used.");
		}
		ui::rows_end();
	}
	ImGui::EndChild();
	if (ImGui::Button("Use the recommended set")) { Ini r; recommended_into(r); for (auto &e : r.kv) target_write(t, e.first, e.second); }
	if (ImGui::IsItemHovered()) ImGui::SetTooltip("Fullscreen, %d× resolution, widescreen to the window, 60 fps, direct mouse aim, softer shadows", recommended_scale());
	ImGui::SameLine(ImGui::GetContentRegionMax().x - ImGui::CalcTextSize("Done").x - ImGui::GetStyle().FramePadding.x * 2);
	if (ui::primary_button("Done")) { g_settings_open = false; ImGui::CloseCurrentPopup(); }
	ImGui::EndPopup();
}

/* a game's own settings: its options (the pack's RECOMP_GAME_OPTIONS -- the ones its hooks honour) and the values it keeps
 * apart from the shared ones, each of which can go back to the shared value */
static std::string g_game_settings;   /* the game whose dialog is open ("": none) */
static Ini g_game_ini;
static bool game_option(const Game &g, const char *name) {
	std::string env = pack_value(pack_read(g_root + "/packs/" + g.id + "/pack.toml"), "RUN_ENV") + " ";
	size_t a = env.find("RECOMP_GAME_OPTIONS="); if (a == std::string::npos) return false;
	std::string list = "," + env.substr(a + 20, env.find(' ', a) - a - 20) + ",";
	return list.find(std::string(",") + name + ",") != std::string::npos;
}
static const char *setting_name(const std::string &k) {
	static const std::pair<const char *, const char *> names[] = {{"render_scale", "Resolution"}, {"fullscreen", "Fullscreen"}, {"aspect_ratio", "Widescreen"},
		{"hud_layout", "HUD"}, {"aspect", "Picture fit"}, {"frame_rate", "Frame rate"}, {"post_aa", "Anti-aliasing"}, {"sharpen", "Sharpening"},
		{"anisotropy", "Texture filtering"}, {"shadow_filter", "Shadow edges"}, {"full_res_world", "Full-resolution world"}, {"ssao", "Ambient occlusion"},
		{"ssao_strength", "Occlusion strength"}, {"osd", "On-screen stats"}, {"input_mode", "Play with"}, {"mouse_look", "Mouse look"}, {"raw_look", "Mouse aim"},
		{"mouse_sens", "Mouse sensitivity"}, {"mouse_invert", "Invert vertical look"}, {"shoulder_buttons", "L and R buttons"}, {"volume", "Volume"}, {"online_id", "Online name"}, {"online", "Play online"}, {"gyro", "Gyro"},
		{"gyro_sens", "Gyro sensitivity"}, {"camera", "Rear camera"}};
	for (auto &n : names) if (k == n.first) return n.second;
	return nullptr;
}
static void game_settings_modal(void) {
	const ImGuiViewport *vp = ImGui::GetMainViewport();
	const float em = ImGui::GetFontSize();
	const Game *g = nullptr; for (const Game &x : g_games) if (x.id == g_game_settings) g = &x;
	if (!g_game_settings.empty() && !ImGui::IsPopupOpen("Game settings")) { ImGui::OpenPopup("Game settings"); g_game_ini = ini_load(game_settings_path(g_game_settings)); }
	ImGui::SetNextWindowSize(ImVec2(vp->WorkSize.x < 44 * em ? vp->WorkSize.x * 0.94f : 40 * em, 0), ImGuiCond_Always);
	ImGui::SetNextWindowPos(ImVec2(vp->WorkPos.x + vp->WorkSize.x * 0.5f, vp->WorkPos.y + vp->WorkSize.y * 0.5f), ImGuiCond_Always, ImVec2(0.5f, 0.5f));
	ImGui::PushStyleVar(ImGuiStyleVar_WindowPadding, ImVec2(1.6f * em, 1.3f * em)); ImGui::PushStyleVar(ImGuiStyleVar_WindowBorderSize, 1.0f);
	if (!ImGui::BeginPopupModal("Game settings", nullptr, ImGuiWindowFlags_NoTitleBar | ImGuiWindowFlags_NoSavedSettings | ImGuiWindowFlags_NoMove)) { ImGui::PopStyleVar(2); return; }
	ImGui::PopStyleVar(2);
	if (!g) { g_game_settings.clear(); ImGui::CloseCurrentPopup(); ImGui::EndPopup(); return; }
	ui::heading((g->name + " settings").c_str(), em * 1.4f);
	SetTarget t{&g_game_ini, game_settings_path(g->id), GAME_HEADER};
	bool any = false;
	if (ui::rows_begin("game_own")) {
		if (game_option(*g, "fov")) { any = true; slider_row(t, "Field of view", "A wider view. 1.00× is the game's own.", "fov", 1.0, 0.75f, 1.5f, "%.2f×"); }
		if (game_option(*g, "view_distance")) { any = true; slider_row(t, "View distance", "How far fading scenery reaches. 1.00× is the game's own.", "view_distance", 1.0, 1.0f, 3.0f, "%.2f×"); }
		if (game_option(*g, "scenery_detail")) { any = true; slider_row(t, "Scenery detail", "How far small scenery details stay visible. 1.00× is the game's own.", "scenery_detail", 1.0, 1.0f, 8.0f, "%.1f×"); }
		if (game_option(*g, "character_detail")) { any = true; slider_row(t, "Character detail", "How far characters and props keep their full detail. 1.00× is the game's own.", "character_detail", 1.0, 1.0f, 8.0f, "%.1f×"); }
		if (game_option(*g, "private_server")) {   /* (a game whose online needs its makers' servers: Killzone; Unit 13 needs none) */
			any = true;
			ui::row("Private server", "The community server that stands in for the game's own (host, or host:port). Empty: the game's own, long offline.");
			static std::string srv; static std::string for_id; if (for_id != g->id) { srv = tget(t, "private_server", ""); for_id = g->id; }
			input_text("##srv", srv, -FLT_MIN);
			if (ImGui::IsItemDeactivatedAfterEdit()) target_write(t, "private_server", srv);
		}
		ui::rows_end();
	}
	if (!any) ui::muted_wrapped("This game has no options of its own yet.");
	/* what it keeps apart from the shared settings */
	Ini sh = ini_load(shared_path());
	std::vector<std::pair<std::string, std::string>> own;
	for (auto &e : g_game_ini.kv) if (!game_key(e.first) && setting_name(e.first)) own.push_back(e);
	ImGui::Dummy(ImVec2(0, em * 0.5f));
	if (own.empty()) ui::muted_wrapped("Everything else follows the shared Settings.");
	else {
		ImGui::TextUnformatted("Kept for this game only");
		ui::muted_wrapped("Values this game uses instead of the shared Settings (from before settings were shared, or set here).");
		for (auto &e : own) {
			ImGui::PushID(e.first.c_str());
			const std::string *sv = ini_find(sh, e.first);
			ImGui::Bullet(); ImGui::Text("%s: %s", setting_name(e.first), e.second.c_str());
			ImGui::SameLine(); ImGui::TextDisabled("(shared: %s)", sv ? sv->c_str() : setting_default(e.first) ? setting_default(e.first) : "default");
			ImGui::SameLine(); if (ImGui::SmallButton("Use shared")) { ini_erase(g_game_ini, e.first); Ini disk = ini_load(t.path); ini_erase(disk, e.first); ini_save(disk, t.path, GAME_HEADER); }
			ImGui::PopID();
		}
	}
	ImGui::Dummy(ImVec2(0, em * 0.4f));
	if (ui::primary_button("Done")) { g_game_settings.clear(); ImGui::CloseCurrentPopup(); }
	ImGui::EndPopup();
}

/* ---- Windows' Smart App Control. When it's on, a program that isn't signed and that Windows doesn't already know gets a
 * verdict from Microsoft's cloud, one per file (by its hash), and the verdict sticks. Every game Nativ builds is new to it
 * (made on this PC, from the player's own copy), and now and then one is refused: on one PC (2026-10-26) Shovel Knight's
 * build was, while Killzone's, the launcher, and the same Shovel Knight code with one byte more all started. A rebuild is
 * a new file (the linker stamps the time), checked afresh; turning Smart App Control off is the way left after that, as
 * Windows has no exception for one program. The dialog opens when Windows refused a game: vitarecomp's SAC_BLOCKED line */
static bool g_sac_open, g_sac_rebuilt;   /* (rebuilt: the player already rebuilt it once and it was refused again) */
static std::string g_sac_game;            /* the game Windows refused */
/* ---- the online name, before the first online game: what other players will see (the same field as Settings' Online name
 * and setup's). Asked once; Play with it empty keeps the tag made for this computer */
static void online_name_modal(void) {
	const ImGuiViewport *vp = ImGui::GetMainViewport();
	const float em = ImGui::GetFontSize();
	static std::string name;
	if (!g_name_game.empty() && !ImGui::IsPopupOpen("Online name")) { name.clear(); ImGui::OpenPopup("Online name"); }
	ImGui::SetNextWindowSize(ImVec2(vp->WorkSize.x < 40 * em ? vp->WorkSize.x * 0.94f : 32 * em, 0), ImGuiCond_Always);
	ImGui::SetNextWindowPos(ImVec2(vp->WorkPos.x + vp->WorkSize.x * 0.5f, vp->WorkPos.y + vp->WorkSize.y * 0.5f), ImGuiCond_Always, ImVec2(0.5f, 0.5f));
	ImGui::PushStyleVar(ImGuiStyleVar_WindowPadding, ImVec2(1.6f * em, 1.3f * em)); ImGui::PushStyleVar(ImGuiStyleVar_WindowBorderSize, 1.0f);
	if (!ImGui::BeginPopupModal("Online name", nullptr, ImGuiWindowFlags_NoTitleBar | ImGuiWindowFlags_NoSavedSettings | ImGuiWindowFlags_NoMove)) { ImGui::PopStyleVar(2); return; }
	ImGui::PopStyleVar(2);
	const Game *g = nullptr; for (const Game &x : g_games) if (x.id == g_name_game) g = &x;
	if (!g) { g_name_game.clear(); ImGui::CloseCurrentPopup(); ImGui::EndPopup(); return; }
	ui::heading("Your online name", em * 1.4f);
	ImGui::PushTextWrapPos(0);
	ImGui::TextUnformatted((g->name + " plays online with other Project Nativ players. Choose the name they'll see: it shows as ntv_ and your name.").c_str());
	ImGui::Dummy(ImVec2(0, em * 0.3f));
	ImGui::AlignTextToFramePadding(); ImGui::TextUnformatted("ntv_"); ImGui::SameLine(0, 0);
	if (ImGui::IsWindowAppearing()) ImGui::SetKeyboardFocusHere();
	input_text("##name_oid", name, em * 12, "your name");
	const bool ok = online_name_ok(name);
	if (!ok) ui::muted_wrapped("Up to 10 letters, digits, '-' or '_'.");
	else if (name.empty()) ui::muted_wrapped(("Left empty, you play as ntv_" + online_tag(g_shared) + ", a tag made for this computer.").c_str());
	ui::muted_wrapped("You can change it any time in Settings.");
	ImGui::PopTextWrapPos();
	ImGui::Dummy(ImVec2(0, em * 0.4f));
	ImGui::BeginDisabled(!ok);
	if (ui::primary_button("Play") || (ok && ImGui::IsKeyPressed(ImGuiKey_Enter))) {
		if (!name.empty() && g_settings_writable) target_write(SetTarget{&g_shared, shared_path(), SHARED_HEADER}, "online_id", name);
		prefs_set("online_name_asked", "1");
		const Game game = *g; g_name_game.clear(); ImGui::CloseCurrentPopup(); ImGui::EndDisabled(); ImGui::EndPopup();
		start_play_now(game);
		return;
	}
	ImGui::EndDisabled();
	ImGui::SameLine(); if (ImGui::Button("Not now") || ImGui::IsKeyPressed(ImGuiKey_Escape)) { g_name_game.clear(); ImGui::CloseCurrentPopup(); }
	ImGui::EndPopup();
}
static void sac_modal(void) {
	const ImGuiViewport *vp = ImGui::GetMainViewport();
	const float em = ImGui::GetFontSize();
	if (g_sac_open && !ImGui::IsPopupOpen("Smart App Control")) ImGui::OpenPopup("Smart App Control");
	ImGui::SetNextWindowSize(ImVec2(vp->WorkSize.x < 44 * em ? vp->WorkSize.x * 0.94f : 36 * em, 0), ImGuiCond_Always);
	ImGui::SetNextWindowPos(ImVec2(vp->WorkPos.x + vp->WorkSize.x * 0.5f, vp->WorkPos.y + vp->WorkSize.y * 0.5f), ImGuiCond_Always, ImVec2(0.5f, 0.5f));
	ImGui::PushStyleVar(ImGuiStyleVar_WindowPadding, ImVec2(1.6f * em, 1.3f * em)); ImGui::PushStyleVar(ImGuiStyleVar_WindowBorderSize, 1.0f);
	if (!ImGui::BeginPopupModal("Smart App Control", nullptr, ImGuiWindowFlags_NoTitleBar | ImGuiWindowFlags_NoSavedSettings | ImGuiWindowFlags_NoMove)) { ImGui::PopStyleVar(2); return; }
	ImGui::PopStyleVar(2);
	const Game *g = nullptr; for (const Game &x : g_games) if (x.id == g_sac_game) g = &x;
	ui::heading(("Windows blocked " + (g ? g->name : g_sac_game)).c_str(), em * 1.4f);
	ImGui::PushTextWrapPos(0);
	ImGui::TextUnformatted(g_sac_rebuilt ? "Windows' Smart App Control refused the rebuilt game too." : "Windows' Smart App Control refused to start it.");
	ImGui::Dummy(ImVec2(0, em * 0.3f));
	ImGui::TextUnformatted("Smart App Control checks each program Windows doesn't know with Microsoft's cloud, and every game Nativ builds is "
	                       "new to it, because it's built on this PC from your own copy. Its verdict is made once for each file, and now and "
	                       "then it refuses one. A rebuild makes a new file that Windows checks afresh, and that usually starts.");
	ImGui::Dummy(ImVec2(0, em * 0.3f));
	ImGui::TextUnformatted("If it's refused again, turn Smart App Control off: in Windows Security, open App & browser control, then Smart App "
	                       "Control settings, and choose Off. Windows has no way to allow a single program.");
	ImGui::Dummy(ImVec2(0, em * 0.2f));
	ui::muted_wrapped("On most versions of Windows 11, Smart App Control can't be turned back on without reinstalling Windows.");
	ImGui::PopTextWrapPos();
	ImGui::Dummy(ImVec2(0, em * 0.5f));
	auto rebuild = [&]() {   /* (a relink: the same code as a new file, then the game, as Play does) */
		Step b = step("Rebuilding " + g->name + " as a new file for Windows to check", vitarecomp({"build", g->id}));
		Step r = step("Running " + g->name, vitarecomp({"run", g->id})); r.env.push_back("ATIV_LAUNCHER=1");
		task_start("Playing " + g->name, "play", g->id, {b, r});
		g_sac_rebuilt = true; g_sac_open = false; ImGui::CloseCurrentPopup();
	};
	auto settings = [&]() { SDL_OpenURL("windowsdefender://smartapp"); };
	ImGui::BeginDisabled(!g || g_task.running);
	if (g_sac_rebuilt ? ImGui::Button("Rebuild and try again") : ui::primary_button("Rebuild and try again")) rebuild();
	ImGui::EndDisabled();
	ImGui::SameLine();
	if (g_sac_rebuilt ? ui::primary_button("Open Smart App Control settings") : ImGui::Button("Open Smart App Control settings")) settings();
	ImGui::SameLine(); if (ImGui::Button("Close")) { g_sac_open = g_sac_rebuilt = false; ImGui::CloseCurrentPopup(); }
	ImGui::EndPopup();
}

/* ---- setup: welcome, firmware, games, ready (first run, or whenever the firmware is missing) */
static bool g_setup_open;
static int g_setup_step;
static void stepper(int step) {
	static const char *const names[] = {"Welcome", "Firmware", "Your games", "Online", "Ready"};
	ImDrawList *dl = ImGui::GetWindowDrawList();
	float h = ImGui::GetTextLineHeight(), r = h * 0.5f;
	for (int i = 0; i < 5; i++) {
		if (i) ImGui::SameLine(0, h * 0.9f);
		ImVec2 p = ImGui::GetCursorScreenPos();
		bool done = i == 1 ? g_firmware : i < step, cur = i == step;   /* (firmware: done only when installed, skipped or not) */
		ImVec4 c = cur ? ui::accent : done ? ui::ready : ui::border;
		dl->AddCircleFilled(ImVec2(p.x + r, p.y + r), r, ui::u32(c));
		char n[4]; snprintf(n, sizeof n, "%d", i + 1);
		ImVec2 ts = ImGui::CalcTextSize(n);
		dl->AddText(ImVec2(p.x + r - ts.x * 0.5f, p.y + r - ts.y * 0.5f), ui::u32(cur || done ? ui::accent_ink : ui::muted), n);
		ImGui::Dummy(ImVec2(r * 2, h)); ImGui::SameLine(0, h * 0.35f);
		ImGui::PushStyleColor(ImGuiCol_Text, cur ? ui::text : ui::muted); ImGui::TextUnformatted(names[i]); ImGui::PopStyleColor();
	}
}
static void setup_modal(SDL_Window *win) {
	const ImGuiViewport *vp = ImGui::GetMainViewport();
	const float em = ImGui::GetFontSize();
	float w = vp->WorkSize.x < 44 * em ? vp->WorkSize.x * 0.94f : 40 * em;
	ImGui::SetNextWindowSize(ImVec2(w, 0), ImGuiCond_Always);
	ImGui::SetNextWindowPos(ImVec2(vp->WorkPos.x + vp->WorkSize.x * 0.5f, vp->WorkPos.y + vp->WorkSize.y * 0.5f), ImGuiCond_Always, ImVec2(0.5f, 0.5f));
	if (g_setup_open && !ImGui::IsPopupOpen("Setup")) ImGui::OpenPopup("Setup");
	ImGui::PushStyleVar(ImGuiStyleVar_WindowPadding, ImVec2(1.8f * em, 1.5f * em)); ImGui::PushStyleVar(ImGuiStyleVar_WindowBorderSize, 1.0f);
	if (!ImGui::BeginPopupModal("Setup", nullptr, ImGuiWindowFlags_NoTitleBar | ImGuiWindowFlags_NoSavedSettings | ImGuiWindowFlags_NoMove)) { ImGui::PopStyleVar(2); return; }
	ImGui::PopStyleVar(2);
	stepper(g_setup_step);
	ImGui::Dummy(ImVec2(0, em * 0.6f));
	ImGui::PushTextWrapPos(ImGui::GetContentRegionAvail().x + ImGui::GetCursorPosX());
	auto finish = [&]() { prefs_set("setup_done", "1"); g_setup_open = false; ImGui::CloseCurrentPopup(); };
	switch (g_setup_step) {
	case 0:
		{	/* the logo: the Vita, its screen dark, the name beneath (assets/brand/logo.svg) */
			ImDrawList *dl = ImGui::GetWindowDrawList(); const float avail = ImGui::GetContentRegionAvail().x, lw = std::min(em * 12, avail * 0.55f);
			ImVec2 p = ImGui::GetCursorScreenPos(); p.x += (avail - lw) * 0.5f;
			ui::vita(dl, p, lw, ui::u32(ui::text), ui::u32(ImVec4(0.051f, 0.059f, 0.075f, 1)));
			ui::wordmark(dl, ImVec2(p.x + lw * 0.25f, p.y + lw * 310 / 600), lw / 6);
			ImGui::Dummy(ImVec2(lw, lw * 420 / 600 + em * 0.4f));
		}
		ui::heading("Welcome to Project Nativ", em * 1.55f);
		ImGui::TextWrapped("Nativ rebuilds the PS Vita games you own as native programs for this computer — sharper, wider and faster than the console could run them.");
		ImGui::Dummy(ImVec2(0, em * 0.3f));
		ImGui::TextWrapped("It ships no Sony or game code. You bring two things, and they stay on this computer:");
		ImGui::Bullet(); ImGui::TextWrapped("The PS Vita system software (firmware) update file — free, from Sony's own website.");
		ImGui::Bullet(); ImGui::TextWrapped("Your own copies of your games and their updates: game folders copied from your Vita, or PKGs, or a whole folder to search.");
		ImGui::Bullet(); ImGui::TextWrapped("Their licences: a game folder from your Vita carries its own. For PKGs, Nativ fetches yours from your Vita over Wi-Fi, once.");
		ui::muted_wrapped("Each game plays as one exact release: the US version, at the versions its card lists (Killzone: 1.00 or its 1.12 update). Other regions and versions are recognised and named, but not supported yet.");
		ImGui::Dummy(ImVec2(0, em * 0.6f));
		if (ui::primary_button("Get started")) g_setup_step = 1;
		ImGui::SameLine(); if (ImGui::Button("Set up later")) finish();
		break;
	case 1:
		ui::heading("Firmware", em * 1.55f);
		if (g_firmware) {
			ui::dot(ui::ready); ImGui::TextWrapped("Installed (%s). Every game builds against it — nothing more to do here.", g_firmware_version.c_str());
		} else {
			ImGui::TextWrapped("Download the PS Vita system software update file from Sony's official page, then choose it below. Its system libraries are decrypted once and every game builds against them.");
			ImGui::Dummy(ImVec2(0, em * 0.2f));
			if (ImGui::Button("Open Sony's download page")) SDL_OpenURL(SONY_FIRMWARE_PAGE);
			ImGui::SameLine(); ImGui::TextLinkOpenURL("playstation.com/.../psvita/system-software", SONY_FIRMWARE_PAGE);
			ui::muted_wrapped("On that page, download the update file (PSVUPDAT.PUP or PSP2UPDAT.PUP, version 3.74). Any recent version works.");
			ImGui::Dummy(ImVec2(0, em * 0.2f));
			if (path_row("##pup", g_fw_path, "Choose the update file (.PUP)")) { static const SDL_DialogFileFilter pup[] = {{"PS Vita update file", "PUP;pup"}}; pick_file(win, &g_fw_path, pup, 1); }
			ImGui::BeginDisabled(g_fw_path.empty() || g_task.running);
			if (ui::primary_button("Install firmware")) task_start("Installing the firmware", "firmware", "", {step("Decrypting the system update", vitarecomp({"firmware", g_fw_path})), step("Installed")});
			ImGui::EndDisabled();
		}
		ImGui::Dummy(ImVec2(0, em * 0.35f));
		ImGui::TextDisabled("Game files folder (optional)");
		ImGui::TextWrapped("%s", g_dump.c_str());
		if (ImGui::Button("Change…")) change_game_folder();
		ImGui::SameLine();
		if (ImGui::Button("Use default")) change_to_default_folder();
		ui::muted_wrapped("Leave it as it is to use the default. Changing it later starts an empty library.");
		ImGui::Dummy(ImVec2(0, em * 0.2f)); task_line();
		ImGui::Dummy(ImVec2(0, em * 0.5f));
		if (g_task.running) ui::muted_wrapped("It carries on in the background: continue whenever you like.");
		if (g_firmware || g_task.running) { if (ui::primary_button("Continue")) g_setup_step = 2; }
		else if (ImGui::Button("Skip for now")) g_setup_step = 2;
		ImGui::SameLine(); if (ImGui::Button("Back")) g_setup_step = 0;
		break;
	case 2: {
		ui::heading("Your games", em * 1.55f);
		ImGui::TextWrapped("Add the games you own, with their updates. Each one is decrypted and checked against its game pack, which says which versions it plays. Your licences are kept once: every later PKG, update or add-on of those games just adds.");
		ImGui::Dummy(ImVec2(0, em * 0.2f));
		add_form(win);
		ImGui::Dummy(ImVec2(0, em * 0.2f)); task_line();
		ImGui::Dummy(ImVec2(0, em * 0.2f)); licences_row(win);
		int have = 0; for (const Game &g : g_games) have += g.imported;
		if (have) {
			ImGui::Dummy(ImVec2(0, em * 0.3f));
			ImGui::TextDisabled("In your library:");
			for (const Game &g : g_games) if (g.imported) { ImGui::Bullet(); ImGui::TextUnformatted(g.name.c_str()); }
		}
		ImGui::Dummy(ImVec2(0, em * 0.5f));
		if (g_task.running) ui::muted_wrapped("Adding and building carry on in the background: continue whenever you like.");
		if (have || g_task.running ? ui::primary_button("Continue") : ImGui::Button("Skip for now")) g_setup_step = 3;   /* (never waits on a running task: the bar at the bottom shows it) */
		ImGui::SameLine(); if (ImGui::Button("Back")) g_setup_step = 1;
		break;
	}
	case 3: {   /* the name other players see (the same field as Settings' Online name) */
		static std::string name; static bool loaded;
		if (!loaded) { g_shared = ini_load(shared_path()); name = online_name(g_shared); loaded = true; }
		ui::heading("Your online name", em * 1.55f);
		ImGui::TextWrapped("The name other players see when you play a game online. It shows as ntv_ and your name, so they know you're playing on PC.");
		ImGui::Dummy(ImVec2(0, em * 0.2f));
		ImGui::AlignTextToFramePadding(); ImGui::TextUnformatted("ntv_"); ImGui::SameLine(0, 0);
		input_text("##setup_oid", name, em * 12, "your name");
		const bool ok = online_name_ok(name);
		if (!ok) ui::muted_wrapped("Up to 10 letters, digits, '-' or '_'.");
		else if (name.empty()) ui::muted_wrapped(("Left empty, you play as ntv_" + online_tag(g_shared) + ", a tag made for this computer.").c_str());
		ui::muted_wrapped("You can change it any time in Settings.");
		ImGui::Dummy(ImVec2(0, em * 0.5f));
		{	static bool online = true; static bool online_loaded;
			if (!online_loaded) { const std::string *v = ini_find(g_shared, "online"); online = !v || atoi(v->c_str()) != 0; online_loaded = true; }
			ui::toggle("setup_online", &online); ImGui::SameLine(); ImGui::TextUnformatted("Play online");
			ui::muted_wrapped(ONLINE_EXPL);
			g_setup_online = online;
		}
		ImGui::Dummy(ImVec2(0, em * 0.5f));
		ImGui::BeginDisabled(!ok);
		if (ui::primary_button("Continue")) {
			if (g_settings_writable) { SetTarget st{&g_shared, shared_path(), SHARED_HEADER}; target_write(st, "online_id", name); target_write(st, "online", g_setup_online ? "1" : "0"); }
			g_setup_step = 4;
		}
		ImGui::EndDisabled();
		ImGui::SameLine(); if (ImGui::Button("Back")) g_setup_step = 2;
		break;
	}
	default:
		ui::heading("You’re set", em * 1.55f);
		ImGui::TextWrapped("Each game is built into a native program the first time — a few minutes per game — and starts straight away after that.");
		ImGui::Bullet(); ImGui::TextWrapped("In a game, F10 (or the PS button) opens the menu: display, controls, frame rate, field of view.");
		ImGui::Bullet(); ImGui::TextWrapped("Settings, at the top right, holds the display, controls and sound for every game; a card's … menu has that game's own options.");
		ImGui::Bullet(); ImGui::TextWrapped("Setup is at the top right whenever you need it again.");
		if (g_task.running) { ImGui::Dummy(ImVec2(0, em * 0.3f)); ui::muted_wrapped("Still working on your games: the bar at the bottom of the library shows how far it's got."); }
		ImGui::Dummy(ImVec2(0, em * 0.6f));
		if (ui::primary_button("Go to my library")) finish();
		ImGui::SameLine(); if (ImGui::Button("Back")) g_setup_step = 3;
		break;
	}
	ImGui::PopTextWrapPos();
	ImGui::EndPopup();
}

static bool g_add_open;   /* the Add a game dialog */
/* ---- a game's card: its cover (pic0), icon, name, state, one primary action */
static void game_card(const Game &g, float w, float name_h) {
	const float em = ImGui::GetFontSize(), pad = em * 0.9f;
	const float img_h = w * 544.0f / 960.0f;
	const bool busy = g_task.running, mine = busy && std::find(g_task.games.begin(), g_task.games.end(), g.id) != g_task.games.end();
	ImGui::PushID(g.id.c_str());
	ImGui::PushStyleColor(ImGuiCol_ChildBg, ui::card); ImGui::PushStyleColor(ImGuiCol_Border, ui::border);
	ImGui::PushStyleVar(ImGuiStyleVar_WindowPadding, ImVec2(0, 0));
	ImGui::BeginChild("card", ImVec2(w, 0), ImGuiChildFlags_Borders | ImGuiChildFlags_AutoResizeY, ImGuiWindowFlags_NoScrollbar);
	ImDrawList *dl = ImGui::GetWindowDrawList();
	ImVec2 p = ImGui::GetCursorScreenPos();
	float rounding = ImGui::GetStyle().ChildRounding;
	Tex cover = g.cover.empty() ? Tex() : texture(g.cover), icon = g.icon.empty() ? Tex() : texture(g.icon);
	if (cover.t) {   /* filled, not stretched: a LiveArea background is 840x500, the card 960x544 */
		ImVec2 uv0(0, 0), uv1(1, 1); float box = w / img_h, ia = (float)cover.w / (float)cover.h;
		if (ia > box) { uv0.x = (1 - box / ia) * 0.5f; uv1.x = 1 - uv0.x; } else { uv0.y = (1 - ia / box) * 0.5f; uv1.y = 1 - uv0.y; }
		dl->AddImageRounded(tex_ref(cover), p, ImVec2(p.x + w, p.y + img_h), uv0, uv1, IM_COL32_WHITE, rounding, ImDrawFlags_RoundCornersTop);
	}
	else {   /* no art in this copy: a quiet panel with the title set large */
		dl->AddRectFilledMultiColor(p, ImVec2(p.x + w, p.y + img_h), ui::u32(ui::card_hi), ui::u32(ui::card_hi), ui::u32(ui::surface), ui::u32(ui::surface));
		ImGui::PushFont(nullptr, em * 1.9f);
		float wrap = w - em * 3;
		ImVec2 ts = ImGui::CalcTextSize(g.name.c_str(), nullptr, false, wrap);
		dl->AddText(nullptr, 0, ImVec2(p.x + (w - ts.x) * 0.5f, p.y + (img_h - ts.y) * 0.5f), ui::u32(ui::muted, 0.75f), g.name.c_str(), nullptr, wrap);
		ImGui::PopFont();
	}
	if (icon.t) {   /* the icon over the cover's bottom-left corner */
		float s = em * 3.0f; ImVec2 a(p.x + pad, p.y + img_h - s * 0.6f);
		dl->AddRectFilled(ImVec2(a.x - 2, a.y - 2), ImVec2(a.x + s + 2, a.y + s + 2), ui::u32(ui::card), em * 0.5f);
		dl->AddImageRounded(tex_ref(icon), a, ImVec2(a.x + s, a.y + s), ImVec2(0, 0), ImVec2(1, 1), IM_COL32_WHITE, em * 0.45f);
	}
	ImGui::Dummy(ImVec2(w, img_h + em * 2.0f));   /* (room for the icon on every card, so they line up) */
	/* the text block, one height on every card: name (two lines at most), state, title ID */
	float y0 = ImGui::GetCursorPosY();
	ImGui::SetCursorPosX(pad);
	ImGui::PushTextWrapPos(w - pad);
	ImGui::PushFont(nullptr, em * 1.15f); ImGui::TextWrapped("%s", g.name.c_str()); ImGui::PopFont();
	ImGui::SetCursorPosY(y0 + name_h + ImGui::GetStyle().ItemSpacing.y);
	ImGui::SetCursorPosX(pad);
	if (mine) { ui::spinner(ui::accent); ImGui::TextDisabled("%s", task_status().c_str()); }
	else if (g.built) { ui::dot(ui::ready); ImGui::TextUnformatted("Ready to play"); }
	else if (g.imported) { ui::dot(ui::warn); ImGui::TextUnformatted("Needs a one-time build"); }
	else { ui::dot(ui::border); ImGui::TextDisabled("Not added yet"); }
	ImGui::SetCursorPosX(pad);
	{	/* the title id and the version: this copy's, else what the pack plays; a chip when the pack recommends another */
		std::string line = g.id, rec = recommended_version(g), vs = played_versions(g);
		if (!g.pack) line += "  -  experimental (no game pack)";
		else if (g.imported && !g.version.empty() && g.version != "-") line += "  ·  " + (g.region.empty() ? "" : g.region + " ") + g.version;
		else if (!g.imported && !vs.empty()) line += "  ·  plays " + (g.region.empty() ? "" : g.region + " ") + vs;
		ImGui::TextDisabled("%s", line.c_str());
		if (g.imported && !rec.empty() && g.version != rec) {
			ImGui::SameLine();   /* (one unwrapped line of text, not a chip: every card's lines keep one height) */
			ImGui::PushTextWrapPos(-1.0f); ImGui::TextColored(ui::warn, "Update %s available", rec.c_str()); ImGui::PopTextWrapPos();   /* ("Update 1.12" beside the version read as the copy's own: a 1.00 copy was taken for 1.12) */
			if (ImGui::IsItemHovered())
				ImGui::SetTooltip("%s (this copy is %s).\nAdd it with + Add game: its update folder (ux0:patch/%s) or PKG,\nor search the folder you copied from your Vita.",
				                  (g.update_note.empty() ? "Version " + rec + " is recommended" : g.update_note).c_str(), g.version.c_str(), g.id.c_str());
		}
	}
	ImGui::PopTextWrapPos();
	ImGui::Dummy(ImVec2(0, em * 0.2f));
	ImGui::SetCursorPosX(pad);
	float bw = w - pad * 2, more = ImGui::GetFrameHeight();
	ImGui::BeginDisabled(busy);
	if (g.built) { if (ui::primary_button("Play", ImVec2(bw - more - ImGui::GetStyle().ItemSpacing.x, 0))) start_play(g); ImGui::SameLine(); }
	else if (g.imported) { if (ui::primary_button("Build", ImVec2(bw - more - ImGui::GetStyle().ItemSpacing.x, 0))) start_build(g); ImGui::SameLine(); }
	else { if (ImGui::Button("Add your copy…", ImVec2(bw - more - ImGui::GetStyle().ItemSpacing.x, 0))) g_add_open = true; ImGui::SameLine(); }
	ImGui::EndDisabled();
	{	/* the "more" button: three dots, drawn (the font may have no ellipsis glyph) */
		if (ImGui::Button("##more", ImVec2(more, 0))) ImGui::OpenPopup("more");
		ImVec2 a = ImGui::GetItemRectMin(), b = ImGui::GetItemRectMax(), m((a.x + b.x) * 0.5f, (a.y + b.y) * 0.5f);
		for (int k = -1; k <= 1; k++) dl->AddCircleFilled(ImVec2(m.x + k * em * 0.32f, m.y), em * 0.09f, ui::u32(ui::text, 0.8f));
	}
	if (ImGui::BeginPopup("more")) {
		ImGui::BeginDisabled(busy || !g.imported);
		if (ImGui::MenuItem(g.built ? "Rebuild" : "Build")) start_build(g);
		ImGui::EndDisabled();
		ImGui::BeginDisabled(!g.imported);
		if (ImGui::MenuItem("Game settings…")) { make_dir(g_dump + "/decrypted/" + g.id + "/recomp"); g_game_settings = g.id; }
		ImGui::EndDisabled();
		if (ImGui::MenuItem("Show its folder")) open_folder(g_dump + "/decrypted/" + g.id);
		ImGui::BeginDisabled(busy);
		if (ImGui::MenuItem("Report a problem…"))   /* (the logs, settings and F5 pictures in one zip, shown in its folder) */
			task_start("Making a bug report for " + g.name, "report", g.id, {step("Collecting the logs and settings", vitarecomp({"report", g.id}))});
		ImGui::EndDisabled();
		if (ImGui::IsItemHovered(ImGuiHoveredFlags_AllowWhenDisabled))
			ImGui::SetTooltip("One zip of this game's logs, your settings and the pictures from your last F5,\nto send with a description of what happened. No game files, saves or keys.");
		ImGui::EndPopup();
	}
	ImGui::Dummy(ImVec2(0, pad * 0.4f));
	ImGui::EndChild();
	ImGui::PopStyleVar(); ImGui::PopStyleColor(2);
	ImGui::PopID();
}

/* ---- the window */
static void hub_ui(SDL_Window *win) {
	game_folder_move_poll();
	if (p5d_mode()) { p5d_ui(win); return; }
	const ImGuiViewport *vp = ImGui::GetMainViewport();
	const float em = ImGui::GetFontSize();
	ImGui::SetNextWindowPos(vp->WorkPos); ImGui::SetNextWindowSize(vp->WorkSize);
	ImGui::PushStyleVar(ImGuiStyleVar_WindowBorderSize, 0.0f); ImGui::PushStyleVar(ImGuiStyleVar_WindowRounding, 0.0f);
	ImGui::Begin("##hub", nullptr, ImGuiWindowFlags_NoDecoration | ImGuiWindowFlags_NoMove | ImGuiWindowFlags_NoSavedSettings | ImGuiWindowFlags_NoBringToFrontOnFocus);
	ImGui::PopStyleVar(2);
	const bool busy = g_task.running, narrow = vp->WorkSize.x < 44 * em;

	/* header: the logo (the Vita, its screen lit as the app icon's, and the wordmark), the setup state, Add game, the setup gear */
	{	ImDrawList *dl = ImGui::GetWindowDrawList(); const ImVec2 p = ImGui::GetCursorScreenPos(); const float h = em * 1.6f, vh = h * 0.9f, vw = vh * 600 / 280;
		ui::vita(dl, ImVec2(p.x, p.y + (h - vh) * 0.5f), vw, ui::u32(ui::text), ui::u32(ui::accent), 30, 1);
		float ww = ui::wordmark(dl, ImVec2(p.x + vw + em * 0.6f, p.y), h);
		ImGui::Dummy(ImVec2(vw + em * 0.6f + ww, h));
	}
	if (!narrow) { ImGui::SameLine(); ImGui::SetCursorPosY(ImGui::GetCursorPosY() + em * 0.45f); ImGui::TextDisabled("your PS Vita games, rebuilt natively"); }
	float right = ImGui::GetWindowContentRegionMax().x;
	float bw = ImGui::CalcTextSize("+ Add game").x + ImGui::CalcTextSize("Settings").x + ImGui::CalcTextSize("Setup").x + ImGui::GetStyle().FramePadding.x * 6 + ImGui::GetStyle().ItemSpacing.x * 2;
	std::string fw = g_firmware ? "Firmware " + g_firmware_version : "Firmware missing";
	float pw = ImGui::CalcTextSize(fw.c_str()).x + em * 1.6f;
	if (!narrow) ImGui::SameLine(right - bw - pw - ImGui::GetStyle().ItemSpacing.x * 2); else ImGui::Dummy(ImVec2(0, 0));
	{	/* the firmware pill: green when installed, amber (and opens setup) when not */
		ImVec2 p = ImGui::GetCursorScreenPos(); float h = ImGui::GetFrameHeight();
		ImGui::GetWindowDrawList()->AddRectFilled(p, ImVec2(p.x + pw, p.y + h), ui::u32(g_firmware ? ui::ready : ui::warn, 0.14f), h * 0.5f);
		ImDrawList *dl = ImGui::GetWindowDrawList(); float lh = ImGui::GetTextLineHeight();
		dl->AddCircleFilled(ImVec2(p.x + em * 0.6f + lh * 0.22f, p.y + h * 0.5f), lh * 0.22f, ui::u32(g_firmware ? ui::ready : ui::warn));
		dl->AddText(ImVec2(p.x + em * 0.6f + lh * 0.8f, p.y + (h - lh) * 0.5f), ui::u32(ui::text), fw.c_str());
		if (ImGui::InvisibleButton("fwpill", ImVec2(pw, h)) && !g_firmware) { g_setup_step = 1; g_setup_open = true; }
		if (ImGui::IsItemHovered() && !g_firmware) ImGui::SetTooltip("Install the firmware");
	}
	ImGui::SameLine();
	ImGui::BeginDisabled(busy);
	if (ui::primary_button("+ Add game")) g_add_open = true;
	ImGui::EndDisabled();
	ImGui::SameLine(); if (ImGui::Button("Settings")) g_settings_open = true;
	ImGui::SameLine(); if (ImGui::Button("Setup")) { g_setup_step = 0; g_setup_open = true; }
	ImGui::Dummy(ImVec2(0, em * 0.3f));

	/* the library: a grid of cards, sized to the window */
	const float bar_h = ImGui::GetFrameHeightWithSpacing() + em * 0.8f, drawer_h = g_drawer ? ImGui::GetContentRegionAvail().y * 0.4f : 0;
	ImGui::BeginChild("library", ImVec2(0, ImGui::GetContentRegionAvail().y - bar_h - drawer_h), 0);
	int nimp = 0; for (const Game &g : g_games) nimp += g.imported;
	ImGui::PushFont(nullptr, em * 1.15f); ImGui::TextUnformatted("Library"); ImGui::PopFont();
	ImGui::SameLine(); ImGui::TextDisabled("%d of %zu added", nimp, g_games.size());
	if (!g_firmware) {
		ImGui::PushStyleColor(ImGuiCol_ChildBg, ImVec4(ui::warn.x, ui::warn.y, ui::warn.z, 0.10f));
		ImGui::BeginChild("fwnote", ImVec2(0, 0), ImGuiChildFlags_AutoResizeY | ImGuiChildFlags_AlwaysUseWindowPadding);
		ui::dot(ui::warn); ImGui::TextWrapped("The firmware isn't installed yet. Games build against Sony's system software — it’s a free download from Sony.");
		if (ui::primary_button("Set up the firmware")) { g_setup_step = 1; g_setup_open = true; }
		ImGui::EndChild(); ImGui::PopStyleColor();
	}
	{	int bad = 0; std::string first; { std::lock_guard<std::mutex> l(g_files.m); if (!g_files.dismissed) { bad = g_files.bad; first = g_files.first; } }
		if (bad) {   /* the install is missing files (files_check_start) */
			ImGui::PushStyleColor(ImGuiCol_ChildBg, ImVec4(ui::warn.x, ui::warn.y, ui::warn.z, 0.10f));
			ImGui::BeginChild("filesnote", ImVec2(0, 0), ImGuiChildFlags_AutoResizeY | ImGuiChildFlags_AlwaysUseWindowPadding);
			ui::dot(ui::warn); ImGui::TextWrapped("P5D 移植版 is missing %d of its files (the first: %s), so the game can't be built. Download the exe again and unpack it into an empty folder. If files go missing again, your antivirus may be removing them.", bad, first.c_str());
			if (ImGui::Button("Not now##files")) { std::lock_guard<std::mutex> l(g_files.m); g_files.dismissed = true; }
			ImGui::EndChild(); ImGui::PopStyleColor();
		}
	}
	{	std::string tag, page; { std::lock_guard<std::mutex> l(g_update.m); if (!g_update.dismissed) { tag = g_update.tag; page = g_update.page; } }
		if (!tag.empty()) {   /* a newer release: its page, where the download is */
			ImGui::PushStyleColor(ImGuiCol_ChildBg, ImVec4(ui::accent.x, ui::accent.y, ui::accent.z, 0.10f));
			ImGui::BeginChild("updnote", ImVec2(0, 0), ImGuiChildFlags_AutoResizeY | ImGuiChildFlags_AlwaysUseWindowPadding);
#ifdef __APPLE__
			ui::dot(ui::accent); ImGui::TextWrapped("Project Nativ %s is out. Download it and drag it into Applications, replacing this one: your games, saves and settings stay as they are.", tag.c_str());
#else
			ui::dot(ui::accent); ImGui::TextWrapped("Project Nativ %s is out. Download it and replace this folder with it: your games, saves and settings stay as they are.", tag.c_str());
#endif
			if (ui::primary_button("Download")) SDL_OpenURL(page.c_str());
			ImGui::SameLine(); if (ImGui::Button("Not now")) { std::lock_guard<std::mutex> l(g_update.m); g_update.dismissed = true; }
			ImGui::EndChild(); ImGui::PopStyleColor();
		}
	}
	if (g_games.empty()) {
		ImGui::Dummy(ImVec2(0, em * 2));
		ImGui::TextDisabled("No games yet."); ImGui::TextWrapped("Add your own copy of a game — a PKG with its licence file, or a game folder — with + Add game.");
	}
	const float gap = em * 1.0f, min_w = em * 15.5f, avail = ImGui::GetContentRegionAvail().x;
	int cols = (int)((avail + gap) / (min_w + gap)); if (cols < 1) cols = 1;
	float cw = (avail - gap * (cols - 1)) / cols; if (cw > em * 24) cw = em * 24;   /* (a wide window gets more columns, not giant cards) */
	float name_h = 0;   /* the longest name's height at this width: every card's text block lines up */
	ImGui::PushFont(nullptr, em * 1.15f);
	for (const Game &g : g_games) { float hh = ImGui::CalcTextSize(g.name.c_str(), nullptr, false, cw - em * 1.8f).y; if (hh > name_h) name_h = hh; }
	ImGui::PopFont();
	ImGui::PushStyleVar(ImGuiStyleVar_ItemSpacing, ImVec2(gap, gap));
	for (size_t i = 0; i < g_games.size(); i++) {
		if (i % cols) ImGui::SameLine();
		ImGui::BeginGroup(); game_card(g_games[i], cw, name_h); ImGui::EndGroup();
	}
	ImGui::PopStyleVar();
	ImGui::EndChild();

	/* the activity bar: what's running (its step), the last failure, the log on demand */
	ImGui::Separator();
	ImGui::Dummy(ImVec2(0, em * 0.1f));
	if (busy || !g_failed.empty()) task_line(); else { ui::dot(ui::border); ImGui::TextDisabled("Nothing running"); }
	{
		const ImGuiStyle &sty = ImGui::GetStyle();
		float lw = ImGui::CalcTextSize(g_drawer ? "Hide log" : "Show log").x + sty.FramePadding.x * 2, cw2 = busy ? ImGui::CalcTextSize("Cancel").x + sty.FramePadding.x * 2 + sty.ItemSpacing.x : 0;
		const bool tip = !busy && !narrow; const float sw = tip ? ImGui::CalcTextSize("Support Nativ").x + sty.ItemSpacing.x * 3 : 0;
		ImGui::SameLine(ImGui::GetWindowContentRegionMax().x - lw - cw2 - sw);
		if (tip) {   /* a quiet link to the developer's tip jar: never a popup, never in a game */
			ImGui::AlignTextToFramePadding(); ImGui::PushStyleColor(ImGuiCol_TextLink, ui::muted);
			if (ImGui::TextLink("Support Nativ")) SDL_OpenURL(SUPPORT_PAGE);
			ImGui::PopStyleColor();
			if (ImGui::IsItemHovered()) ImGui::SetTooltip("Nativ is free. If you'd like to support its development, you can leave a tip on Ko-fi.");
			ImGui::SameLine(0, sty.ItemSpacing.x * 2);
		}
	}
	if (busy) { if (ImGui::Button("Cancel")) task_cancel(); ImGui::SameLine(); }
	if (ImGui::Button(g_drawer ? "Hide log" : "Show log")) g_drawer = !g_drawer;
	if (g_drawer) {
		ImGui::PushStyleColor(ImGuiCol_ChildBg, ui::surface);
		ImGui::BeginChild("log", ImVec2(0, 0), ImGuiChildFlags_Borders | ImGuiChildFlags_AlwaysUseWindowPadding);
		{ std::lock_guard<std::mutex> l(g_log_lock); ImGui::PushStyleColor(ImGuiCol_Text, ui::muted); ImGui::TextUnformatted(g_log.c_str(), g_log.c_str() + g_log.size()); ImGui::PopStyleColor(); }
		if (ImGui::GetScrollY() >= ImGui::GetScrollMaxY() - 4) ImGui::SetScrollHereY(1.0f);   /* follow the end unless scrolled up */
		ImGui::EndChild();
		ImGui::PopStyleColor();
	}

	/* Add a game, as its own dialog */
	if (g_add_open && !ImGui::IsPopupOpen("Add a game")) ImGui::OpenPopup("Add a game");
	ImGui::SetNextWindowSize(ImVec2(narrow ? vp->WorkSize.x * 0.94f : 38 * em, 0), ImGuiCond_Always);
	ImGui::SetNextWindowPos(ImVec2(vp->WorkPos.x + vp->WorkSize.x * 0.5f, vp->WorkPos.y + vp->WorkSize.y * 0.5f), ImGuiCond_Always, ImVec2(0.5f, 0.5f));
	ImGui::PushStyleVar(ImGuiStyleVar_WindowPadding, ImVec2(1.6f * em, 1.3f * em)); ImGui::PushStyleVar(ImGuiStyleVar_WindowBorderSize, 1.0f);
	if (ImGui::BeginPopupModal("Add a game", nullptr, ImGuiWindowFlags_NoTitleBar | ImGuiWindowFlags_NoSavedSettings | ImGuiWindowFlags_NoMove)) {
		ImGui::PopStyleVar(2);
		ui::heading("Add a game", em * 1.4f);
		ImGui::PushTextWrapPos(0);
		if (add_form(win)) { g_add_open = false; ImGui::CloseCurrentPopup(); }
		ImGui::SameLine(); if (ImGui::Button("Cancel")) { g_add_open = false; ImGui::CloseCurrentPopup(); }
		ImGui::Dummy(ImVec2(0, em * 0.3f)); ImGui::Separator(); ImGui::Dummy(ImVec2(0, em * 0.1f)); licences_row(win);
		ImGui::PopTextWrapPos();
		ImGui::EndPopup();
	} else ImGui::PopStyleVar(2);
	sac_modal();
	online_name_modal();
	setup_modal(win);
	settings_modal();
	game_settings_modal();
	ImGui::End();
}

/* ---- P5D: the single-page front for Persona 5 Dancing in Starlight --------------------------------------------
 * The player's whole trip in one window: import their own copy of the game (and the Vita system software once),
 * build the native program, pick an output resolution and start it. The work itself is still the pipeline's own
 * commands (vitarecomp add/analyze/recompile/build/run), run as child processes: the same steps the hub runs and
 * the command line documents, so a build made here is the same build the hub makes. "P5D_LAUNCHER" picks this
 * screen (a release build compiles it in with -DP5D_LAUNCHER). */
static bool p5d_mode(void) {
#ifdef P5D_LAUNCHER
	return true;
#else
	const char *e = getenv("P5D_LAUNCHER");
	return e && *e && strcmp(e, "0") != 0;
#endif
}
static const char *const P5D_TITLE = "P5D Windows移植版启动器";
/* the release's version: the payload's version.txt ("v0.1.5-p5d-HEAD+hash": the part before the first '-'); a dev tree has
 * no version.txt and says the release version this source belongs to. Shown beside the page subtitle (M1642). */
static const std::string &p5d_version(void) {
	static std::string v;
	if (!v.empty()) return v;
	v = "v0.2.3";   /* (M1793: the version this source belongs to; a release's payload version.txt overrides it) */
	if (FILE *f = fopen((g_root + "/version.txt").c_str(), "rb")) {
		char b[128]; size_t n = fread(b, 1, sizeof b - 1, f); fclose(f); b[n] = 0;
		std::string t(b); size_t e = t.find_first_of("-\r\n");
		if (e != std::string::npos) t = t.substr(0, e);
		if (t.size() > 2) v = t;
	}
	return v;
}   /* the exe's and window's name (the game's own name stays in the page subtitle) */

/* ---- M1645: the frame-generation panel. NVIDIA Smooth Motion is a driver-level AI frame interpolator for RTX 40/50 on
 * DirectX 11/12 and Vulkan applications (NVIDIA App > Graphics > Program settings > Driver settings > Smooth Motion). This
 * port is already a Vulkan application, so it needs no game-side DLSS code: the panel reports the GPU/driver via nvidia-smi,
 * copies the built game executable's path (the program to add in NVIDIA App) and opens NVIDIA App. */
struct P5dFgProbe { bool done = false, nv = false, app = false; std::string gpu, driver, app_path; };
static P5dFgProbe g_fg;
static std::string p5d_run_capture(const std::vector<std::string> &argv) {
	std::string out; Proc p;
	if (!proc_start(p, argv, {})) return out;
	char b[512]; long n; while ((n = proc_read(p, b, sizeof b)) > 0) out.append(b, (size_t)n);
	proc_wait(p); proc_done(p);
	return out;
}
static const P5dFgProbe &p5d_fg(void) {
	if (g_fg.done) return g_fg;
	g_fg = P5dFgProbe(); g_fg.done = true;
#ifdef _WIN32
	for (const char *p : {"C:\\Program Files\\NVIDIA Corporation\\NVIDIA App\\CEF\\NVIDIA App.exe",
	                      "C:\\Program Files\\NVIDIA Corporation\\NVIDIA App\\NVIDIA App.exe"}) {
		struct stat st; if (!g_fg.app && stat(p, &st) == 0) { g_fg.app = true; g_fg.app_path = p; }
	}
#endif
	const char *cands[] = {
#ifdef _WIN32
		"C:\\Windows\\System32\\nvidia-smi.exe",
		"C:\\Program Files\\NVIDIA Corporation\\NVSMI\\nvidia-smi.exe",
#endif
		"nvidia-smi" };
	std::string raw;
	for (const char *c : cands) { raw = p5d_run_capture({c, "--query-gpu=name,driver_version", "--format=csv,noheader"}); if (!raw.empty()) break; }
	for (size_t a = 0; a < raw.size() && !g_fg.nv; ) {
		size_t e = raw.find('\n', a); if (e == std::string::npos) e = raw.size();
		std::string line = raw.substr(a, e - a);
		while (!line.empty() && (line.back() == '\r' || line.back() == ' ')) line.pop_back();
		size_t c = line.rfind(',');
		if (c != std::string::npos) {
			std::string gpu = line.substr(0, c), drv = line.substr(c + 1);
			while (!drv.empty() && drv.front() == ' ') drv.erase(drv.begin());
			if (!gpu.empty()) { g_fg.gpu = gpu; g_fg.driver = drv; g_fg.nv = true; }
		}
		a = e + 1;
	}
	return g_fg;
}
static void p5d_open_path(const std::string &path) {   /* the shell's "open": NVIDIA App (or a folder) */
#ifdef _WIN32
	ShellExecuteA(nullptr, "open", path.c_str(), nullptr, nullptr, SW_SHOWNORMAL);
#else
	SDL_OpenURL(("file://" + path).c_str());
#endif
}
static std::string g_p5d_rom_path;      /* the folder the player picked: a copy of their game */
static std::string g_p5d_rom_tried;     /* the path an import was started for in this session ("" until a real pick) */
static int g_p5d_rom_kind;               /* 0: a game folder; 1: a PKG file (+ its licence) */
static std::string g_p5d_lic_path;       /* the PKG's licence file (.rif / work.bin), when the player gives one */
static bool g_p5d_lic_zrif;             /* the licence came as a pasted zRIF (kept in the licence store) */
static char g_p5d_zrif_buf[4096];       /* the popup's zRIF text */
static bool g_p5d_undo_ask;             /* the 撤銷導入 confirmation popup is open */
static std::string g_p5d_steam_msg;     /* the last 添加到 Steam 庫 result (shown under the button) */
static bool g_p5d_steam_ok;
static bool g_p5d_disclaimer_ask;       /* M1823: the first-run disclaimer is reopened from 其他設置 */
static std::string g_p5d_fw_path;       /* the .PUP they picked: the Vita system software */
static const Game *p5d_game(void) {
	for (const Game &g : g_games) if (g.id == "PCSH10109") return &g;
	return nullptr;
}
static const char *const P5D_RES[5] = {"960x544", "1280x720", "1920x1080", "2560x1440", "3840x2160"};
static const char *const P5D_RES_LABEL[5] = {"原版 960×544", "720p 1280×720", "1080p 1920×1080", "2K 2560×1440", "4K 3840×2160"};
static int p5d_res_index(void) {   /* the remembered choice (prefs launcher.ini: p5d_res), 2K when unset */
	const std::string r = g_prefs.count("p5d_res") ? g_prefs["p5d_res"] : std::string("2560x1440");
	for (int i = 0; i < 5; i++) if (r == P5D_RES[i]) return i;
	return 3;
}
static const char *const P5D_FPS[2] = {"30", "60"};
static const char *const P5D_FPS_LABEL[2] = {"30 幀（原版節奏）", "60 幀"};   /* (M1640: no explanation beside the 60 fps choice, at the user's request) */
static int p5d_fps_index(void) {   /* the remembered choice (prefs launcher.ini: p5d_fps), 30 when unset */
	const std::string r = g_prefs.count("p5d_fps") ? g_prefs["p5d_fps"] : std::string("30");
	return r == "60" ? 1 : 0;
}
static bool p5d_show_fps(void) {   /* prefs launcher.ini: p5d_show_fps = 1 shows the runtime's top-left FPS overlay */
	const std::string r = g_prefs.count("p5d_show_fps") ? g_prefs["p5d_show_fps"] : std::string("0");
	return r == "1";
}
static int p5d_vibrance(void) {   /* prefs launcher.ini: p5d_vibrance = 0..100 (0 = off), the runtime's dynamic vibrance */
	const std::string r = g_prefs.count("p5d_vibrance") ? g_prefs["p5d_vibrance"] : std::string("0");
	int v = atoi(r.c_str()); if (v < 0) v = 0; if (v > 100) v = 100; return v;
}
static bool p5d_fg_present(void) {   /* prefs launcher.ini: p5d_fg_present = 1 launches the game with RECOMP_FG_PRESENT=1
                                      * (present only fresh frames, so the driver's AI interpolator has frames to work from;
                                      * the panel's checkbox; M1646) */
	const std::string r = g_prefs.count("p5d_fg_present") ? g_prefs["p5d_fg_present"] : std::string("0");
	return r == "1";
}
static void p5d_font(ImGuiIO &io) {   /* the system's Chinese face (nothing shipped): Microsoft YaHei, else any CJK sans */
	static const char *const faces[] = {"C:\\Windows\\Fonts\\msyh.ttc", "C:\\Windows\\Fonts\\msyh.ttf",
		"C:\\Windows\\Fonts\\simhei.ttf", "C:\\Windows\\Fonts\\simsun.ttc", 0};
	for (int i = 0; faces[i]; i++) {
		struct stat st;
		if (stat(faces[i], &st) == 0) if (io.Fonts->AddFontFromFileTTF(faces[i])) return;
	}
	ui::load_system_font(io);
}
static void p5d_log_drawer(void) {   /* the whole log, on demand (a failed build says why here) */
	ImGui::PushStyleColor(ImGuiCol_ChildBg, ui::surface);
	ImGui::BeginChild("p5dlog", ImVec2(0, ImGui::GetFontSize() * 12), ImGuiChildFlags_Borders | ImGuiChildFlags_AlwaysUseWindowPadding);
	{ std::lock_guard<std::mutex> l(g_log_lock); ImGui::PushStyleColor(ImGuiCol_Text, ui::muted); ImGui::TextUnformatted(g_log.c_str(), g_log.c_str() + g_log.size()); ImGui::PopStyleColor(); }
	if (ImGui::GetScrollY() >= ImGui::GetScrollMaxY() - 4) ImGui::SetScrollHereY(1.0f);
	ImGui::EndChild();
	ImGui::PopStyleColor();
}
/* the `add` stage's arguments: a game folder, or a PKG file with its licence (--license .rif / work.bin) */
static std::vector<std::string> p5d_add_args(bool nobuild) {
	std::vector<std::string> a{"add", g_p5d_rom_path};
	if (g_p5d_rom_kind == 1 && !g_p5d_lic_zrif && !g_p5d_lic_path.empty()) { a.push_back("--license"); a.push_back(g_p5d_lic_path); }
	if (nobuild) a.push_back("--no-build");
	return a;
}
static void p5d_start_build(void) {
	const Game *g = p5d_game();
	std::vector<Step> steps;
	if (!(g && g->imported) && !g_p5d_rom_path.empty()) steps.push_back(step("導入遊戲拷貝（解密並校驗版本）", vitarecomp(p5d_add_args(false))));
	build_steps(steps, "PCSH10109");   /* analyse, recompile, compile: the same "@@" steps the hub's card runs */
	task_start("構建 女神異聞錄5：星夜熱舞", "build", "PCSH10109", steps);
}
/* 導入許可證：拷進啟動器的許可證庫（按內容 ID），之後這款遊戲的 PKG 導入就不再需要它 */
static void p5d_import_licence(void) {
	if (g_p5d_lic_path.empty()) return;
	prefs_set("p5d_lic_path", g_p5d_lic_path);
	task_start("導入許可證", "licences", "", {step("導入許可證", vitarecomp({"licenses", "import", g_p5d_lic_path}))});
}
static void p5d_start_import(void) {
	/* M1783: decrypt + import ONLY (the button was later removed at the owner's request: picking the folder does it). */
	std::vector<Step> steps;
	steps.push_back(step("導入遊戲拷貝（解密）", vitarecomp(p5d_add_args(true))));
	steps.push_back(step("導入（生成 ELF 與版本）", vitarecomp({"import", "PCSH10109"})));
	task_start("僅導入 女神異聞錄5：星夜熱舞", "import", "PCSH10109", steps);
}
static void p5d_undo_import(void) {
	/* M1786: drop the IMPORT ONLY -- elf/ (the decrypted main ELF the ① status and the recompile read) and version (the
	 * recorded game version). The built game (recomp/), its fs (saves) and app0 are kept, so the game stays playable; the
	 * ① line returns to 未導入 and the folder picker can import again. Added because the importer could not otherwise be
	 * re-tested on a machine whose game was already imported and built. */
	const std::string w = g_dump + "/decrypted/PCSH10109";
	mods_delete_tree(w + "/elf");
	remove((w + "/version").c_str());
	g_p5d_rom_path.clear();
	prefs_erase("p5d_rom_path");
	library_scan();
	fprintf(stderr, "p5d: import undone (elf/ and version removed; recomp/, fs/ and app0 kept)\n");
}
static void p5d_start_play(int res) {
	/* straight in: no "is the build up to date" check (there is no online update channel: the exe a player
	 * downloaded brought its own build; the rebuild button covers a new launcher version) */
	/* the launcher owns the game build: check it is the build this exe's source makes (ready rebuilds only when
	 * the payload version stamp changed), then run it. Without this a new launcher exe never reached a player who
	 * had an older build - the operation logic we keep fixing stayed stale for them (reported 2026-11-07). */
	Step chk = step("CHECKING THE GAME BUILD", vitarecomp({"ready", "PCSH10109"}));
	Step run = step("運行遊戲", vitarecomp({"run", "PCSH10109"}));
	/* M1646: a launcher update may bring new runtime code (this round: the AI-interpolation present mode). The game binary is
	 * the player's own build, so it must be rebuilt for that code to reach it - do it here when the payload's content hash no
	 * longer matches the build stamp, instead of only hinting at it (players ran the old binary and saw no change). */
	std::vector<Step> play_steps{chk};
	if (p5d_build_stale()) play_steps.push_back(step("更新遊戲構建", vitarecomp({"build", "PCSH10109"})));
	play_steps.push_back(run);
	if (g_hub_win) SDL_MinimizeWindow(g_hub_win);   /* the game's window gets the foreground (and the keyboard): a launcher left up front kept the keys (reported 2026-11-07) */
	/* the internal render scale follows the chosen resolution (original 960x544 = 1, 720p = 1, 1080p = 2, 2K = 3, 4K = 4):
	 * handed to the runtime as RECOMP_RENDER_SCALE (its FIRST source, before the settings files) so the choice always
	 * applies; the game's own settings.ini override of render_scale is dropped, because that file is read before the
	 * shared one and a stale value there kept the old scale (a 4K choice that still rendered at 3x looked upscaled) */
	static const char *const scale[5] = {"1", "1", "2", "3", "4"};
	run.env.push_back(std::string("RECOMP_RENDER_SCALE=") + scale[res]);
	run.env.push_back(std::string("RECOMP_VIBRANCE=") + std::to_string(p5d_vibrance()));   /* M1663: the dynamic vibrance strength */

	/* M1646: the panel's AI-interpolation mode: present only fresh game frames (30 fps setting -> 30 presents/s, 60 -> 60) so
	 * the driver's interpolator can insert frames between them; without it the present loop repeats each picture at 60/s and
	 * there is nothing to interpolate (a 30 fps setting looked unchanged with Smooth Motion on). */
	if (p5d_fg_present()) run.env.push_back("RECOMP_FG_PRESENT=1");
	/* M1651: NVIDIA App's AI 插帧 profile has a broken application entry for this game (its "add application" step failed),
	 * so the driver profile never matches the process and the interpolation never engages; repair it before every launch. */
	{ std::string d; if (p5d_repair_fgx_profile(&d)) g_fgx_note = d; }
	{ std::string gp = game_settings_path("PCSH10109");
	  if (exists(gp)) { Ini g = ini_load(gp); bool had = false;
		for (auto &e : g.kv) if (e.first == "render_scale") had = true;
		if (had) { ini_erase(g, "render_scale"); ini_save(g, gp, GAME_HEADER); } } }
	/* the output: a resolution larger than this desktop cannot be shown -- use the desktop's for the window and keep
	 * the chosen render scale (4K on a 2K screen = 4x supersampling, never a window hanging off the screen) */
	{ std::string resstr = P5D_RES[res];
	  const SDL_DisplayMode *dm = SDL_GetCurrentDisplayMode(SDL_GetPrimaryDisplay());
	  int rw = 0, rh = 0;
	  if (dm && sscanf(P5D_RES[res], "%dx%d", &rw, &rh) == 2 && (rw > dm->w || rh > dm->h)) {
		char b[32]; snprintf(b, sizeof b, "%dx%d", dm->w, dm->h); resstr = b;
	  }
	  run.env.push_back(std::string("RECOMP_RES=") + resstr);   /* the output resolution, the runtime's own setting */ }
	/* the internal render scale follows the chosen resolution (original 960x544 = 1, 720p = 1, 1080p = 2,
	 * 2K = 3, 4K = 4): the earlier build always rendered at 3x whatever the resolution said (the launcher's
	 * first-run settings had written render_scale = 3) */
	/* the chosen output resolution drives the INTERNAL render resolution too (reported: "修改启动器分辨率的时候，
	 * 要能真正修改游戏内部渲染分辨率"): write the matching scale into the shared settings file, which the game reads
	 * (RECOMP_SETTINGS_SHARED). Original 960x544 = 1x, 720p = 1x, 1080p = 2x (1920x1088), 2K = 3x (2880x1632),
	 * 4K = 4x (3840x2176).
	 * No env override: the settings file stays the single source of truth (an env override made the Settings page's
	 * value ineffective before, M1476). */
	{ std::string sp = shared_path();
	  if (!sp.empty()) {
		Ini cur = exists(sp) ? ini_load(sp) : Ini{};
		ini_set(cur, "render_scale", scale[res]);
		/* the frame-rate choice (v0.1.0: 30 / 60): display.c reads "frame_rate" every frame; it caps the swap
		 * interval a game asks for to 1, so the game's own frame loop runs at 60 -- the game-side fixes for the
		 * systems timed in 1/30 s steps are the pack's 60 fps hooks (work in progress) */
		ini_set(cur, "frame_rate", P5D_FPS[p5d_fps_index()]);
		/* the top-left real-time frame-rate overlay (metrics.c: `osd` = 0 off / 1 fps+frame time / 2 full);
		 * the launcher's option writes 1 or 0, the game's own F1 still cycles it at run time */
		ini_set(cur, "osd", p5d_show_fps() ? "1" : "0");
		/* M1663h: the dynamic vibrance: the env passed to the play step was not reaching the child, so it goes through
		 * the shared settings the game does read (the same channel as render_scale/frame_rate/osd) */
		ini_set(cur, "vibrance", std::to_string(p5d_vibrance()));
		ini_set(cur, "vib_strong", "0");   /* M1663j: 強烈模式 removed */
		ini_save(cur, sp, SHARED_HEADER);
	  } }
	/* M1664: before the game starts, apply the enabled MODs to the library's CPK archives (the script restores the
	 * previous patch first, then patches the currently enabled set; a MOD toggle therefore just needs a restart). */
	{
		/* the packaged release ships the pipeline folder, not dev/: look there first (the script was missing from
		 * release builds, which made the MOD enable switch do nothing) */
		std::string script = g_root + "/pipeline/p5d_mods_apply.py";
		if (!exists(script)) script = g_root + "/dev/p5d_mods_apply.py";
		if (exists(script)) {
			Proc p;
			/* the script works on the decrypted title folder (<library>/decrypted/<id>/), not on the library root: passing the root
			 * made it look for <library>/app0/data/data.cpk, find nothing and quietly do nothing -- the real reason a MOD enable
			 * had no effect even after the script shipped. */
			std::string title = g_dump + "/decrypted/PCSH10109";
			if (proc_start(p, {python_exe(), script, "apply"}, {std::string("P5D_LIB=") + title})) {
				int rc = proc_wait(p); proc_done(p);
				fprintf(stderr, "mods: apply exit %d\n", rc);
			}
		}
	}
	task_start("啟動 女神異聞錄5：星夜熱舞", "play", "PCSH10109", play_steps);
}
/* the build's version stamp vs this launcher's: only a hint (no rebuild, no waiting) */
static int p5d_build_stale(void) {
	std::string mine, built;
	if (FILE *f = fopen((g_root + "/version.txt").c_str(), "rb")) { char b[256]; size_t n = fread(b, 1, sizeof b - 1, f); fclose(f); mine.assign(b, n); }
	if (FILE *f = fopen((g_dump + "/decrypted/PCSH10109/recomp/.built_version_min").c_str(), "rb")) { char b[256]; size_t n = fread(b, 1, sizeof b - 1, f); fclose(f); built.assign(b, n); }
	while (!mine.empty() && (mine.back() == '\n' || mine.back() == '\r' || mine.back() == ' ')) mine.pop_back();
	while (!built.empty() && (built.back() == '\n' || built.back() == '\r' || built.back() == ' ')) built.pop_back();
	/* M1645: only the content hash after '+' decides staleness. A launcher-only release bumps the commit prefix in
	 * version.txt ("v0.1.5-p5d-<commit>+<content>") but not the game's runtime/packs content, so a player who just updated
	 * the launcher must not be told to rebuild the game. Older files without '+' fall back to the whole string. */
	size_t mp = mine.rfind('+'), bp = built.rfind('+');
	if (mp != std::string::npos && bp != std::string::npos) { mine = mine.substr(mp); built = built.substr(bp); }
	return !mine.empty() && !built.empty() && mine != built;
}
static void p5d_install_firmware(void) {
	task_start("安裝系統固件", "firmware", "", {step("解密系統更新文件", vitarecomp({"firmware", g_p5d_fw_path})), step("完成")});
}
static std::string g_p5d_fw_dir;        /* a folder the player picked: a decrypted firmware tree (no .PUP needed) */
static std::string g_p5d_fw_dir_seen;   /* the one already imported (pick_folder fills g_p5d_fw_dir asynchronously) */
static void p5d_import_firmware_dir(void) {   /* copy an already-decrypted firmware folder into the library (LICENSE/FIRMWARE-3.74/os0/vs0) */
	static const char *script =
		"import os, sys, shutil\n"
		"src, lib = sys.argv[1], sys.argv[2]\n"
		"ver = None\n"
		"cands = [src] + [os.path.join(src, d) for d in sorted(os.listdir(src)) if os.path.isdir(os.path.join(src, d))]\n"
		"for cand in cands:\n"
		"    vf = os.path.join(cand, 'version.txt')\n"
		"    if os.path.isfile(vf):\n"
		"        ver = (open(vf).read().strip() or os.path.basename(cand)); src = cand; break\n"
		"if not ver:\n"
		"    print('that folder holds no decrypted firmware (no version.txt): pick the one with os0/ and vs0/, or its parent')\n"
		"    sys.exit(2)\n"
		"dst = os.path.join(lib, 'firmware', ver)\n"
		"os.makedirs(os.path.dirname(dst), exist_ok=True)\n"
		"shutil.copytree(src, dst, dirs_exist_ok=True)\n"
		"print('firmware', ver, '->', dst)\n";
	task_start("導入系統固件", "firmware", "", {step("複製已解壓的固件", {python_exe(), "-c", script, g_p5d_fw_dir, g_dump})});
}

/* ---- M1657: DLC (add-on content) ---------------------------------------------------------------------------------
 * P5D's add-ons live on a Vita in ux0:addcont/<title>/<ADDCONT...>/ (the decrypted NoNpDrm folder tree players keep):
 * one folder per add-on with its own DLCDxxxxx.cpk. The game mounts addcont0: (libapputil's sceAppUtilDrmOpen) and opens
 * "addcont0:/ADDCONT<id>/<id>.cpk" (the string is in eboot.bin), so the port only has to put those folders under
 * <RECOMP_FS>/addcont0/ -- its fs root is <library>/decrypted/PCSH10109/recomp/fs. apputil.c then reports the add-ons as
 * licensed (it already did that whenever addcont0 exists) and the game finds its DLC. Optional: the base game works
 * without it. */
static std::string g_p5d_dlc_dir;
static std::string g_p5d_mod_src, g_p5d_mod_src_seen;
static std::vector<P5dMod> g_mods; static bool g_mods_loaded;        /* the folder the player picked (pick_folder fills it asynchronously) */
static std::string g_p5d_dlc_dir_seen;   /* the one already imported */
static std::string p5d_dlc_target(void) { return g_dump + "/decrypted/PCSH10109/recomp/fs/addcont0"; }
static bool p5d_is_dir(const std::string &p) { struct stat st; return stat(p.c_str(), &st) == 0 && S_ISDIR(st.st_mode); }
static unsigned long long p5d_tree_size(const std::string &p) {
	unsigned long long n = 0; DIR *d = opendir(p.c_str()); if (!d) return 0;
	struct dirent *e;
	while ((e = readdir(d))) {
		if (e->d_name[0] == '.' && (!e->d_name[1] || (e->d_name[1] == '.' && !e->d_name[2]))) continue;
		std::string c = p + "/" + e->d_name; struct stat st; if (stat(c.c_str(), &st) != 0) continue;
		n += S_ISDIR(st.st_mode) ? p5d_tree_size(c) : (unsigned long long)st.st_size;
	}
	closedir(d);
	return n;
}
/* the add-ons already imported: their count and size (0 when none) */
static int p5d_dlc_imported(unsigned long long *bytes) {
	*bytes = 0;
	std::string dst = p5d_dlc_target();
	DIR *d = opendir(dst.c_str()); if (!d) return 0;
	int n = 0; struct dirent *e;
	while ((e = readdir(d))) {
		if (strncasecmp(e->d_name, "ADDCONT", 7) != 0) continue;
		std::string c = dst + "/" + e->d_name;
		if (!p5d_is_dir(c)) continue;
		n++; *bytes += p5d_tree_size(c);
	}
	closedir(d);
	return n;
}
static void p5d_dlc_remove_tree(const std::string &p) {
	DIR *d = opendir(p.c_str()); if (!d) { remove(p.c_str()); return; }
	struct dirent *e;
	while ((e = readdir(d))) {
		if (e->d_name[0] == '.' && (!e->d_name[1] || (e->d_name[1] == '.' && !e->d_name[2]))) continue;
		std::string c = p + "/" + e->d_name;
		if (p5d_is_dir(c)) p5d_dlc_remove_tree(c); else remove(c.c_str());
	}
	closedir(d);
	rmdir(p.c_str());
}
/* the copy itself: Python (shutil), so a 2 GB tree moves with a real progress bar; it accepts the reAddcont folder (with
 * its PCSH10109), the PCSH10109 folder, or a folder that already holds ADDCONT* add-ons, and skips a non-DLC pick */
static std::string p5d_dlc_script(void) {
	return
		"import os, sys, shutil\n"
		"src, lib = sys.argv[1], sys.argv[2]\n"
		"cands = [src]\n"
		"p = os.path.join(src, 'PCSH10109')\n"
		"if os.path.isdir(p): cands.insert(0, p)\n"
		"base = adds = None\n"
		"for cand in cands:\n"
		"    if not os.path.isdir(cand): continue\n"
		"    a = [d for d in sorted(os.listdir(cand)) if d.upper().startswith('ADDCONT') and os.path.isdir(os.path.join(cand, d))]\n"
		"    if a: base, adds = cand, a; break\n"
		"if not base:\n"
		"    print('DLC: no ADDCONT* add-ons in that folder: pick the reAddcont folder (it holds PCSH10109) or the PCSH10109 folder itself')\n"
		"    sys.exit(2)\n"
		"dst = os.path.join(lib, 'decrypted', 'PCSH10109', 'recomp', 'fs', 'addcont0')\n"
		"os.makedirs(dst, exist_ok=True)\n"
		"files = []\n"
		"for a in adds:\n"
		"    for root, _, fs in os.walk(os.path.join(base, a)):\n"
		"        for f in fs: files.append(os.path.join(root, f))\n"
		"total = len(files) or 1\n"
		"copied = written = 0\n"
		"for i, f in enumerate(files, 1):\n"
		"    out = os.path.join(dst, os.path.relpath(f, base))\n"
		"    os.makedirs(os.path.dirname(out), exist_ok=True)\n"
		"    try:\n"
		"        shutil.copy2(f, out); copied += 1; written += os.path.getsize(f)\n"
		"    except OSError as e:\n"
		"        print('DLC: copy failed %s: %s' % (f, e))\n"
		"    if i % 8 == 0 or i == total: print('PROGRESS %d/%d' % (i, total), flush=True)\n"
		"print('DLC: %d add-ons (%.1f MB) imported' % (len(adds), written / 1048576.0))\n";
}
static void p5d_import_dlc(void) {
	task_start("導入 DLC", "dlc", "", {step("複製追加內容", {python_exe(), "-c", p5d_dlc_script(), g_p5d_dlc_dir, g_dump})});
}
static void p5d_ui(SDL_Window *win) {
	game_folder_move_poll();
	const ImGuiViewport *vp = ImGui::GetMainViewport();
	const float em = ImGui::GetFontSize();
	const bool busy = g_task.running;
	const Game *g = p5d_game();
	const bool imported = g && g->imported, built = g && g->built;
	ImGui::SetNextWindowPos(vp->WorkPos); ImGui::SetNextWindowSize(vp->WorkSize);
	ImGui::PushStyleVar(ImGuiStyleVar_WindowBorderSize, 0.0f); ImGui::PushStyleVar(ImGuiStyleVar_WindowRounding, 0.0f);
	ImGui::PushStyleColor(ImGuiCol_WindowBg, ImVec4(0, 0, 0, 0));   /* the key art below is the background */
	ImGui::Begin("##p5d", nullptr, ImGuiWindowFlags_NoDecoration | ImGuiWindowFlags_NoMove | ImGuiWindowFlags_NoSavedSettings | ImGuiWindowFlags_NoBringToFrontOnFocus);
	ImGui::PopStyleColor();
	ImGui::PopStyleVar(2);
	{   /* the port's background: Persona 5's own red-black star art (assets/p5d/bg.png), cover-fitted; a dark scrim
	     * keeps the white text readable over the red stripes */
		static Tex bg; static bool bg_loaded;
		if (!bg_loaded) { bg_loaded = true; bg = texture(g_root + "/assets/p5d/bg.png"); }
		if (bg.t) {
			const ImVec2 a = ImGui::GetWindowPos(), b = ImVec2(a.x + ImGui::GetWindowSize().x, a.y + ImGui::GetWindowSize().y);
			const float ws = b.x - a.x, hs = b.y - a.y;
			const float sc = std::max(ws / (float)bg.w, hs / (float)bg.h);
			const float iw = bg.w * sc, ih = bg.h * sc;
			ImDrawList *dl = ImGui::GetWindowDrawList();
			dl->AddImage(tex_ref(bg), ImVec2(a.x + (ws - iw) * 0.5f, a.y + (hs - ih) * 0.5f), ImVec2(a.x + (ws + iw) * 0.5f, a.y + (hs + ih) * 0.5f));
			dl->AddRectFilled(a, b, IM_COL32(0, 0, 0, 150));
		}
	}

	/* M1823: the first-run disclaimer gate. Until the player ticks the box, the whole page is replaced by the notice
	 * (a modal could be dismissed with Esc, so the gate is a page instead); the acceptance is remembered in launcher.ini
	 * together with the notice version, so a changed notice asks again. 其他設置 can reopen it; ATIV_SHOT skips it so the
	 * documentation screenshots stay capturable (ATIV_SHOT_DISC=1 forces it for a capture). */
	{
		static const char *const DISC_VER = "1";
		static bool disc_checked;
		const std::string acc = g_prefs.count("p5d_disclaimer") ? g_prefs["p5d_disclaimer"] : "";
		const bool accepted = acc == DISC_VER;
		const bool shot_skip = getenv("ATIV_SHOT") && !getenv("ATIV_SHOT_DISC");
		if ((!accepted || g_p5d_disclaimer_ask) && !shot_skip) {
			ui::heading(P5D_TITLE, em * 1.7f);
			ImGui::TextDisabled("Persona 5 Dancing in Starlight · PC 移植版");
			ImGui::Dummy(ImVec2(0, em * 1.2f));
			ui::heading("使用前請閱讀並同意免責聲明", em * 1.25f);
			ui::muted_wrapped("P5D Windows 移植版是由玩家社區開發的非官方、非商業同人移植工程，與 ATLUS／SEGA／Sony 沒有任何關係，也未獲得其授權、贊助或認可。");
			ImGui::Dummy(ImVec2(0, em * 0.5f));
			ImGui::BeginChild("##p5d_disclaimer_text", ImVec2(0, vp->WorkSize.y * 0.46f), ImGuiChildFlags_Borders | ImGuiChildFlags_AlwaysUseWindowPadding);
			auto bullet = [](const char *t) { ImGui::Bullet(); ImGui::SameLine(); ImGui::TextWrapped("%s", t); };
			bullet("必須自備正版遊戲：您需要自己合法持有的《Persona 5: Dancing in Starlight》（PCSH10109，亞洲版）與 PS Vita 系統固件；本移植版不包含遊戲本體、遊戲數據、密鑰、固件或遊戲重編譯產物。");
			bullet("僅限個人非商業用途：本移植版供個人學習、研究、備份與離線遊玩；不得用於破解其他作品或繞過版權保護；非商業使用（以 GPL-2 發布的代碼依 GPL-2 處理）。");
			bullet("不協助獲取遊戲資源：本項目不提供、也不協助獲取遊戲本體、固件或任何盜版資源；請勿傳播解密後的遊戲數據、固件或重編譯產物。");
			bullet("社區分享：玩家可在社區內原樣、免費分享本移植版，但請保留出處與官方發布頁鏈接，不要以移植者名義發布或冒充官方更新。");
			bullet("試用與刪除：若您僅作試用或評估，請在 24 小時內刪除發行包程序文件；您自行合法備份的遊戲數據、存檔與 GPL-2 源碼不受此限。");
			bullet("風險自負、不提供擔保與技術支持：因使用本軟件導致的存檔損壞、數據丟失、設備問題或其它損失由使用者自行承擔；重要存檔請自行備份。");
			bullet("未成年人：未滿 18 歲（或當地法定成年年齡）者，須事先取得監護人知情並明確同意。");
			bullet("完整條款：完整免責聲明（23 條）見 README；條款可能更新，更新後繼續使用即視為接受。");
			ImGui::EndChild();
			ImGui::Dummy(ImVec2(0, em * 0.5f));
			ImGui::Checkbox("我已閱讀並確認上述內容，並同意完整免責聲明（見 README）", &disc_checked);
			ImGui::Dummy(ImVec2(0, em * 0.3f));
			ImGui::BeginDisabled(!disc_checked);
			if (ui::primary_button("同 意 並 繼 續")) {
				prefs_set("p5d_disclaimer", DISC_VER);
				g_p5d_disclaimer_ask = false;
				disc_checked = false;
			}
			ImGui::EndDisabled();
			if (accepted) {
				ImGui::SameLine();
				if (ImGui::Button("返回")) { g_p5d_disclaimer_ask = false; disc_checked = false; }
			} else {
				ImGui::SameLine();
				ImGui::TextDisabled("需勾選後才能使用啟動器");
			}
			ImGui::End();
			return;
		}
	}

	/* M1784/M1785: picking a ROM folder starts its import at once (decrypt + import in the background) -- the owner asked
	 * for "select the folder -> 已導入" while the old flow only imported as the first build step. Two rules learned from
	 * the first test build: a REMEMBERED path from launcher.ini is NOT a pick (no auto import nor 已導入 at start-up), and
	 * only a real pick (the path changing this session) triggers the import. Selection never starts a build. */
	static bool rom_loaded;
	static std::string rom_seen;
	static std::string lic_seen;
	static bool rom_pending;
	if (!rom_loaded) {
		rom_loaded = true;
		if (g_prefs.count("p5d_rom_kind")) g_p5d_rom_kind = atoi(g_prefs["p5d_rom_kind"].c_str()) ? 1 : 0;
		if (g_p5d_rom_path.empty() && g_prefs.count("p5d_rom_path")) g_p5d_rom_path = g_prefs["p5d_rom_path"];
		if (g_p5d_lic_path.empty() && g_prefs.count("p5d_lic_path")) g_p5d_lic_path = g_prefs["p5d_lic_path"];
		rom_seen = g_p5d_rom_path;
		lic_seen = g_p5d_lic_path;
		rom_pending = false;
	}
	if (g_p5d_rom_path != rom_seen || g_p5d_lic_path != lic_seen) {
		rom_seen = g_p5d_rom_path;
		lic_seen = g_p5d_lic_path;
		g_p5d_rom_tried.clear();
		/* a PKG without its licence is not imported yet: the player picks the licence first (a kept licence needs none) */
		rom_pending = !rom_seen.empty() && g_p5d_rom_kind == 0;   /* (a PKG waits for 導入許可證 and ④ 開始構建) */
		if (!rom_seen.empty()) prefs_set("p5d_rom_path", rom_seen);
		prefs_set("p5d_lic_path", g_p5d_lic_path);
		prefs_set("p5d_rom_kind", std::to_string(g_p5d_rom_kind));
	}
	if (rom_pending && (imported || busy)) rom_pending = false;
	if (rom_pending) {
		rom_pending = false;
		g_p5d_rom_tried = g_p5d_rom_path;
		p5d_start_import();
	}

	ui::heading(P5D_TITLE, em * 2.0f);
	ImGui::SameLine(); ImGui::AlignTextToFramePadding();
	ImGui::TextDisabled("Persona 5 Dancing in Starlight · PC 移植版 · 鍵盤鼠標 / 手柄 · %s", p5d_version().c_str());
	ImGui::Dummy(ImVec2(0, em * 0.2f));
	ui::muted_wrapped("需要你自己的《女神異聞錄5：星夜熱舞》遊戲拷貝（PS Vita，PCSH10109 / 1.00 亞洲版）：mai 遊戲格式文件夾（MaiDump），或 PKG 格式遊戲文件 + 許可證（.rif / work.bin 或 zRIF）；以及 PS Vita 系統軟件（PSVUPDAT.PUP 3.74）。遊戲數據不會上傳，全部在本機構建。");
	ImGui::Dummy(ImVec2(0, em * 0.25f));
	ui::muted_wrapped("為什麼不內含遊戲 ROM：遊戲本體、語音、影片與 PS Vita 系統固件都是 Sony / ATLUS 的版權內容，不能隨本移植版一起分發。"
	                  "啟動器只提供工具：把你自己擁有的遊戲重新編譯成 PC 原生程序。解密、編譯、存檔都在你自己的電腦上完成，不會上傳、也不會放進這個啟動器裡。");
	ImGui::Dummy(ImVec2(0, em * 0.5f));
	ImGui::Separator();
	ImGui::Dummy(ImVec2(0, em * 0.5f));
	/* M1648: a menu bar with pages instead of one long page. The main tab keeps the game copy, firmware, build, the
	 * on-screen frame rate display and the launch block; the "畫質選項" tab holds resolution, frame rate and the AI frame
	 * interpolation. */
	ImGui::Dummy(ImVec2(0, em * 0.3f));
	if (ImGui::BeginTabBar("##p5d_pages")) {
		if (ImGui::BeginTabItem("主頁")) {
			ImGui::Dummy(ImVec2(0, em * 0.5f));
	/* ① the game copy */
	ui::heading("① 遊戲 ROM", em * 1.25f);
	{
		static const char *const kinds[] = {"mai 遊戲格式文件夾", "PKG 格式遊戲文件"};
		int k = g_p5d_rom_kind;
		if (ui::segmented(kinds, 2, &k)) { g_p5d_rom_kind = k; prefs_set("p5d_rom_kind", std::to_string(g_p5d_rom_kind)); g_p5d_rom_tried.clear(); }
	}
	if (imported && (g_p5d_rom_kind == 0 || g->version == "1.00-pkg")) {
		ui::dot(ui::ready); ImGui::Text("已導入：Persona 5 Dancing in Starlight（%s）", g->version.empty() ? "1.00" : g->version.c_str());
	} else if (imported) {
		/* the library already holds a copy (the folder version): a PKG chosen here is not imported yet, so say both */
		ui::dot(ui::muted); ImGui::TextDisabled("庫中目前是文件夾導入的版本（%s）；導入本 PKG 後「開始構建」會替換它", g->version.empty() ? "1.00" : g->version.c_str());
	}
	else if (!g_p5d_rom_path.empty() && !busy && g_failed.rfind("僅導入", 0) == 0) {
		/* the auto import of the picked copy failed (a licence, a version the pack does not play, a PKG that is not a
		 * game...): say so here instead of leaving an orange "will import" line forever. The log says why. */
		ui::dot(ui::warn); ImGui::TextUnformatted("導入失敗：請看下方日誌（重新選擇遊戲拷貝可重試；「開始構建」也會先導入）");
		ImGui::TextDisabled("已選：%s", g_p5d_rom_path.c_str());
		if (g_p5d_rom_kind == 1 && !g_p5d_lic_path.empty()) ImGui::TextDisabled("許可證：%s", g_p5d_lic_path.c_str());
	}
	else if (!g_p5d_rom_path.empty() && g_p5d_rom_tried == g_p5d_rom_path) {
		/* this path was PICKED in this session and the auto import was started for it (the owner asked for
		 * "select the folder -> 已導入"; the real state follows when the import ends). */
		ui::dot(ui::ready);
		if (busy && g_task.kind == "import") ImGui::TextUnformatted("已導入（正在校驗版本…）");
		else ImGui::TextUnformatted(g_p5d_rom_kind == 1 ? "已導入（選擇的 PKG 文件）" : "已導入（選擇的遊戲文件夾）");
		ImGui::TextDisabled("已選：%s", g_p5d_rom_path.c_str());
		if (g_p5d_rom_kind == 1 && !g_p5d_lic_path.empty()) ImGui::TextDisabled("許可證：%s", g_p5d_lic_path.c_str());
	}
	else if (!g_p5d_rom_path.empty()) {
		/* a REMEMBERED path (launcher.ini) with nothing imported here is still "not imported": at start-up this used to
		 * read 已導入 and even started a version check on a library that had no game (the fresh/test-library report). */
		ui::dot(ui::muted); ImGui::TextUnformatted("尚未導入：已記住上次的遊戲拷貝，重新選擇它即可導入（或點「開始構建」）");
		ImGui::TextDisabled("已選：%s", g_p5d_rom_path.c_str());
	} else { ui::dot(ui::muted); ImGui::TextUnformatted(g_p5d_rom_kind == 1 ? "尚未導入遊戲：選擇你的 PKG 格式遊戲文件（另需許可證 .rif / work.bin 或 zRIF）" : "尚未導入遊戲：選擇你的 mai 遊戲格式文件夾（ux0:app/…，含 licence 的拷貝）"); }
	ImGui::BeginDisabled(busy);
	if (g_p5d_rom_kind == 1) {
		/* PKG 流程：先「導入 PKG」與「導入許可證」各完成一次，再點「④ 開始構建」；構建成功後即可啟動遊戲 */
		if (ImGui::Button("導入 PKG…")) { static const SDL_DialogFileFilter pkgf[] = {{"PS Vita package", "pkg"}}; pick_file(win, &g_p5d_rom_path, pkgf, 1); }
		ImGui::SameLine();
		if (g_p5d_rom_path.empty()) ImGui::TextDisabled("尚未導入 PKG");
		else if (g_p5d_rom_tried == g_p5d_rom_path || (imported && g && g->version == "1.00-pkg")) { ui::dot(ui::ready); ImGui::TextDisabled("PKG 已導入"); }
		else { ui::dot(ui::muted); ImGui::TextDisabled("已選擇 PKG（尚未導入；點「開始構建」導入）"); }
		if (ImGui::Button("導入許可證…")) { g_p5d_lic_zrif = false; pick_file(win, &g_p5d_lic_path, nullptr, 0); }
		ImGui::SameLine(); ImGui::TextDisabled("或"); ImGui::SameLine();
		if (ImGui::Button("粘貼 zRIF…")) ImGui::OpenPopup("p5d_zrif");
		ImGui::SameLine();
		if (g_p5d_lic_zrif) { ui::dot(ui::ready); ImGui::TextDisabled("許可證已導入（zRIF）"); }
		else if (!g_p5d_lic_path.empty()) { ui::dot(ui::ready); ImGui::TextDisabled("許可證已導入"); }
		else ImGui::TextDisabled("尚未導入許可證（PKG 解密需要，一次即可）");
		static std::string lic_imported;
		if (!g_p5d_lic_path.empty() && g_p5d_lic_path != lic_imported) { lic_imported = g_p5d_lic_path; p5d_import_licence(); }
		if (ImGui::BeginPopup("p5d_zrif")) {
			ImGui::TextUnformatted("粘貼你自己授權產生的 zRIF（pkg2zip 的 rif2zrif，或 NoNpDrm 生態）");
			ImGui::TextDisabled("只能是你自己的授權；社區分享的 zRIF 屬盜版，請勿使用。");
			ImGui::InputTextMultiline("##zrif", g_p5d_zrif_buf, sizeof g_p5d_zrif_buf, ImVec2(em * 46, em * 4.0f));
			if (ui::primary_button("導入 zRIF")) {
				g_p5d_lic_zrif = true;
				g_p5d_lic_path.clear();
				prefs_erase("p5d_lic_path");
				task_start("導入 zRIF", "licences", "", {step("導入 zRIF", vitarecomp({"licenses", "import-zrif", std::string(g_p5d_zrif_buf)}))});
				ImGui::CloseCurrentPopup();
			}
			ImGui::SameLine();
			if (ImGui::Button("取消")) ImGui::CloseCurrentPopup();
			ImGui::EndPopup();
		}
	} else {
		if (ImGui::Button("導入 mai 遊戲格式文件夾…")) pick_folder(win, &g_p5d_rom_path);
		ImGui::SameLine(); ImGui::TextDisabled("%s", g_p5d_rom_path.empty() ? "（或直接點「開始構建」使用已導入的拷貝）" : g_p5d_rom_path.c_str());
	}
	ImGui::EndDisabled();
	ImGui::SameLine();
	ImGui::BeginDisabled(busy || !imported);
	if (ImGui::Button("撤銷導入")) g_p5d_undo_ask = true;
	ImGui::EndDisabled();
	ImGui::Dummy(ImVec2(0, em * 0.9f));
	/* M1786: 撤銷導入 -- undo the imported game folder: only the import records (elf/ and version) go away, so the built
	 * game, its saves and the MODs stay and the folder picker can import again. */
	if (g_p5d_undo_ask) { ImGui::OpenPopup("撤銷導入遊戲文件夾？"); g_p5d_undo_ask = false; }
	if (ImGui::BeginPopupModal("撤銷導入遊戲文件夾？", nullptr, ImGuiWindowFlags_AlwaysAutoResize)) {
		ImGui::TextUnformatted("只刪除這個遊戲文件夾的「導入」記錄（elf/ 與 version），");
		ImGui::TextUnformatted("不會刪除已構建的遊戲（recomp）、存檔與 MOD。");
		ImGui::TextUnformatted("撤銷後遊戲仍可啟動；重新選擇遊戲文件夾即可再次導入（用於重新驗證導入流程）。");
		ImGui::Dummy(ImVec2(0, em * 0.4f));
		if (ui::primary_button("確定撤銷")) { p5d_undo_import(); ImGui::CloseCurrentPopup(); }
		ImGui::SameLine();
		if (ImGui::Button("取消")) ImGui::CloseCurrentPopup();
		ImGui::EndPopup();
	}

	/* ② the firmware */
	ui::heading("② 系統固件", em * 1.25f);
	if (g_firmware) { ui::dot(ui::ready); ImGui::Text("已安裝：PS Vita 系統軟件 %s", g_firmware_version.c_str()); }
	else { ui::dot(ui::warn); ImGui::TextUnformatted("尚未安裝：PS Vita 系統固件（PSVUPDAT.PUP 3.74，或已解壓的固件文件夾）"); }
	ImGui::BeginDisabled(busy);
	if (ImGui::Button("從文件夾導入固件…")) pick_folder(win, &g_p5d_fw_dir);
	ImGui::SameLine(); ImGui::TextDisabled("（含 version.txt / os0 / vs0 的文件夾，或它的上一層）");
	ImGui::EndDisabled();
	if (!g_p5d_fw_dir.empty() && g_p5d_fw_dir != g_p5d_fw_dir_seen) { g_p5d_fw_dir_seen = g_p5d_fw_dir; p5d_import_firmware_dir(); }
	ImGui::BeginDisabled(busy);
	if (ImGui::Button("選擇 PSVUPDAT.PUP…")) { static const SDL_DialogFileFilter pup[] = {{"PS Vita 系統更新", "PUP"}}; pick_file(win, &g_p5d_fw_path, pup, 1); }
	ImGui::SameLine(); ImGui::TextDisabled("%s", g_p5d_fw_path.c_str());
	ImGui::SameLine(); ImGui::BeginDisabled(g_p5d_fw_path.empty()); if (ImGui::Button("安裝固件")) p5d_install_firmware(); ImGui::EndDisabled();
	ImGui::EndDisabled();
	ImGui::Dummy(ImVec2(0, em * 0.9f));

	ImGui::Dummy(ImVec2(0, em * 0.9f));

	/* ③ DLC (optional) */
	ui::heading("③ 追加內容（DLC，可選）", em * 1.25f);
	{
		static int dlc_n = -1; static unsigned long long dlc_b = 0; static double dlc_at = -1e9;
		if (!busy && ImGui::GetTime() - dlc_at > 2.0) { dlc_n = p5d_dlc_imported(&dlc_b); dlc_at = ImGui::GetTime(); }
		if (dlc_n > 0) { ui::dot(ui::ready); ImGui::Text("已導入：%d 個追加內容（%.2f GB）", dlc_n, (double)dlc_b / 1073741824.0); }
		else { ui::dot(ui::muted); ImGui::TextUnformatted("未導入追加內容（可選，不影響遊戲本體）"); }
		ImGui::BeginDisabled(busy);
		if (ImGui::Button("選擇 DLC 文件夾…")) pick_folder(win, &g_p5d_dlc_dir);
		ImGui::SameLine(); ImGui::TextDisabled("reAddcont 文件夾（內含 PCSH10109）或其中的 PCSH10109 文件夾");
		ImGui::EndDisabled();
		if (!g_p5d_dlc_dir.empty() && g_p5d_dlc_dir != g_p5d_dlc_dir_seen) { g_p5d_dlc_dir_seen = g_p5d_dlc_dir; p5d_import_dlc(); }
		if (dlc_n > 0) {
			ImGui::BeginDisabled(busy);
			if (ImGui::SmallButton("移除全部 DLC")) {
				p5d_dlc_remove_tree(p5d_dlc_target()); dlc_n = -1; dlc_at = -1e9;
			}
			ImGui::EndDisabled();
		}
	}
	ImGui::Dummy(ImVec2(0, em * 0.9f));

	/* ④ build */
	ui::heading("④ 開始構建", em * 1.25f);
	if (built) { ui::dot(ui::ready); ImGui::TextUnformatted("已構建：可隨時啟動遊戲"); }
	else if (imported) { ui::dot(ui::accent); ImGui::TextUnformatted("已導入，等待構建（AOT 重編譯 + 鏈接，約 2–6 分鐘）"); }
	else { ui::dot(ui::muted); ImGui::TextUnformatted(g_p5d_rom_kind == 1 ? "導入 PKG 與許可證後點擊右側按鈕（會自動解密、識別版本並編譯）" : "導入遊戲後點擊右側按鈕"); }
	ImGui::BeginDisabled(busy || (!imported && (g_p5d_rom_path.empty() || (g_p5d_rom_kind == 1 && !g_p5d_lic_zrif && g_p5d_lic_path.empty()))));
	if (ui::primary_button(built ? "重新構建" : "開始構建")) p5d_start_build();
	ImGui::EndDisabled();
	ImGui::SameLine(); ImGui::TextDisabled("（會自動解密、識別版本並編譯成全原生程序）");
	ImGui::Dummy(ImVec2(0, em * 0.9f));

	/* ⑤ on-screen frame rate */
	ui::heading("⑤ 畫面幀率顯示", em * 1.25f);
	{
		bool show = p5d_show_fps();
		if (ImGui::Checkbox("在畫面左上角顯示實時幀率（FPS / 幀時間）", &show)) prefs_set("p5d_show_fps", show ? "1" : "0");
		ImGui::TextDisabled("僅影響顯示，不影響效能；遊戲內按 F1 可切換 關 / 幀率 / 完整統計");
		ImGui::TextDisabled("幀率行：FPS = 遊戲真實渲染幀數；DISP = 實測這個遊戲視窗每秒顯示的不同畫面張數（由螢幕擷取量測，");
		ImGui::TextDisabled("包含驅動 AI 插帧生成的幀；30 幀設定約 48–56、60 幀設定約 107，受面板刷新率上限）。");
	}
	ImGui::Dummy(ImVec2(0, em * 0.9f));

	/* ⑥ launch */
	ImGui::BeginDisabled(busy || !built || !g_firmware);
	const float bw = ImGui::CalcTextSize("啟 動 遊 戲").x + em * 3.0f;
	if (ui::primary_button("啟 動 遊 戲", ImVec2(bw, em * 2.0f))) p5d_start_play(p5d_res_index());
	ImGui::EndDisabled();
	if (!built) { ImGui::SameLine(); ImGui::TextDisabled("構建完成後可啟動"); }
	else if (p5d_build_stale()) {
		ImGui::Dummy(ImVec2(0, em * 0.3f));
		ui::dot(ui::warn); ImGui::TextUnformatted("偵測到啟動器已更新：啟動遊戲時會自動重新構建一次（之後不會再檢查）");
	}

	/* the run */
	ImGui::Separator();
	if (busy) {
		ui::spinner(ui::accent); ImGui::TextUnformatted(g_task.name.c_str()); ImGui::SameLine(); ImGui::TextDisabled("%s", task_status().c_str());
		const int pm = g_task.pct_max.load(), pv = g_task.pct.load();
		if (pm > 0) {   /* the pipeline's PROGRESS lines (runtime/build.py): a real percentage */
			char lbl[64]; snprintf(lbl, sizeof lbl, "%d%% (%d/%d)", pv * 100 / pm, pv, pm);
			ImGui::ProgressBar((float)pv / (float)pm, ImVec2(-1, em * 0.8f), lbl);
		} else {
			float t = (float)ImGui::GetTime();
			ImGui::ProgressBar(fmodf(t * 0.35f, 1.0f), ImVec2(-1, em * 0.8f), " ");   /* (indeterminate until the first PROGRESS line) */
		}
		if (g_task.kind == "build") ImGui::TextDisabled("首次構建約 10–30 分鐘（之後啟動秒進）；進度來自 pipeline 的構建行");
		if (ImGui::Button("取消")) task_cancel();
	} else if (!g_failed.empty()) {
		ui::dot(ui::error); ImGui::TextColored(ui::error, "%s 沒有完成。", g_failed.c_str()); ImGui::SameLine();
		if (ImGui::TextLink("查看日誌")) g_drawer = true;
		if (ImGui::TextLink("重試構建")) p5d_start_build();
	} else {
		ui::dot(ui::muted); ImGui::TextDisabled("就緒");
	}
	if (ImGui::Button(g_drawer ? "隱藏日誌" : "顯示日誌")) g_drawer = !g_drawer;
	if (g_drawer) p5d_log_drawer();
			ImGui::EndTabItem();
		}
		if (ImGui::BeginTabItem("畫質選項")) {
			ImGui::Dummy(ImVec2(0, em * 0.5f));
	/* the quality page (M1648): resolution, frame rate and the AI frame interpolation together */
	{
		ImGui::SeparatorText("解析度");
		int ri = p5d_res_index();
		for (int i = 0; i < 5; i++) {
			if (i % 2) ImGui::SameLine(ImGui::GetFontSize() * 15.0f);
			if (ImGui::RadioButton(P5D_RES_LABEL[i], ri == i)) { ri = i; prefs_set("p5d_res", P5D_RES[i]); }
		}
		ImGui::TextDisabled("內部渲染倍率隨所選尺寸提升（4K=4x、2K=3x、1080p=2x），原版 960×544 佈局不變；全屏可在遊戲內設定；4K 需要 4K 顯示器（在 2K 螢幕上會以 4x 超採樣呈現，畫面不會超出螢幕）");
		ImGui::Dummy(ImVec2(0, em * 0.6f));

		ImGui::SeparatorText("幀率");
		int fi = p5d_fps_index();
		for (int i = 0; i < 2; i++) {
			if (i) ImGui::SameLine(ImGui::GetFontSize() * 15.0f);
			if (ImGui::RadioButton(P5D_FPS_LABEL[i], fi == i)) { fi = i; prefs_set("p5d_fps", P5D_FPS[i]); }
		}
		if (fi == 0) ImGui::TextDisabled("30 幀：與 PS Vita 原版一致，節奏/動畫最穩定");
		ImGui::Dummy(ImVec2(0, em * 0.6f));

		ImGui::SeparatorText("動態亮麗（內置色彩增強）");
		{
			int vib = p5d_vibrance();
			ImGui::SetNextItemWidth(ImGui::GetFontSize() * 16.0f);
			if (ImGui::SliderInt("##vibrance", &vib, 0, 100, "%d%%")) prefs_set("p5d_vibrance", std::to_string(vib));
			ImGui::SameLine();
			if (vib <= 0) ImGui::TextDisabled("關閉（0%% = 預設）");
			else if (vib < 35) ImGui::TextDisabled("輕微");
			else if (vib < 70) ImGui::TextDisabled("標準（推薦）");
			else ImGui::TextDisabled("強烈");
		}
		ImGui::TextDisabled("類比 NVIDIA「動態亮麗」的自適應飽和度：低飽和的顏色提升多、已飽和的幾乎不動，膚色與白色不會溢色；");
		ImGui::TextDisabled("0 = 關閉（預設）；100% = 標準強度上限；改完需重新啟動遊戲生效；不影響幀率");
		ImGui::Dummy(ImVec2(0, em * 0.6f));

		ImGui::SeparatorText("AI 插帧（NVIDIA Smooth Motion）");
		const P5dFgProbe &fg = p5d_fg();
		if (!fg.nv) { ui::dot(ui::muted); ImGui::TextUnformatted("未檢測到 NVIDIA 顯示卡 / 驅動（需要 GeForce RTX 40/50 並安裝 NVIDIA App）"); }
		else {
			bool rtx = fg.gpu.find("RTX 40") != std::string::npos || fg.gpu.find("RTX 50") != std::string::npos;
			ui::dot(rtx ? ui::ready : ui::warn);
			if (rtx) ImGui::Text("檢測到 %s（驅動 %s）：可在 NVIDIA App 為這個遊戲開啟「AI 插帧」", fg.gpu.c_str(), fg.driver.c_str());
			else ImGui::Text("%s（驅動 %s）：AI 插帧需要 RTX 40/50 系", fg.gpu.c_str(), fg.driver.c_str());
		}
		std::string exe = g_dump + "/decrypted/PCSH10109/recomp/game_host_min.exe";
		struct stat st; bool have_exe = stat(exe.c_str(), &st) == 0;
		ImGui::TextDisabled("遊戲程式：%s%s", exe.c_str(), have_exe ? "" : "（尚未構建）");
		static double copied_until;
		if (ImGui::Button("複製遊戲程式路徑")) { if (!SDL_SetClipboardText(exe.c_str())) {} copied_until = ImGui::GetTime() + 2.0; }
		if (copied_until > ImGui::GetTime()) { ImGui::SameLine(); ImGui::TextDisabled("已複製"); }
		ImGui::SameLine();
		if (fg.app) { if (ImGui::Button("打開 NVIDIA App")) p5d_open_path(fg.app_path); }
		else { if (ImGui::Button("NVIDIA App 下載頁")) SDL_OpenURL("https://www.nvidia.com/en-us/software/nvidia-app/"); }
		ImGui::SameLine();
		if (ImGui::Button("重新檢測")) { g_fg = P5dFgProbe(); }
		/* the panel's own switch: the presentation side of the feature, which the launcher can control (the Smooth Motion
		 * toggle itself lives in NVIDIA App's private driver channel and cannot be flipped from here) */
		bool fgp = p5d_fg_present();
		if (ImGui::Checkbox("啟用 AI 插帧支援（30 幀設定也有效）", &fgp)) prefs_set("p5d_fg_present", fgp ? "1" : "0");
		ImGui::TextDisabled("這個選項只改「畫面怎麼送給顯卡驅動」，不改遊戲本身：遊戲每秒只送出真實的新畫面（30 幀設定 → 30 張，");
		ImGui::TextDisabled("60 幀 → 60 張），不重複送同一張；這樣驅動才有兩張不同的畫面可以插幀。不影響節奏、音樂或判定。");
		ImGui::TextDisabled("30 幀設定時螢幕上約看到 2× 的幀數（驅動在 30 張真實幀之間補幀）。");
		ImGui::TextDisabled("開啟：NVIDIA App → 圖形 → 程式設定 → 加入上面的遊戲程式 → 驅動程式設定 → AI 插帧（英文 Smooth Motion）= 開；");
		ImGui::TextDisabled("NVIDIA 覆蓋層的 FPS 顯示插幀後的值，遊戲內 F1 顯示的仍是真實渲染的 30 / 60。");
		ImGui::TextDisabled("驅動檔案：%s", g_fgx_note.empty() ? "（點「啟動遊戲」時自動檢查；NVIDIA App 加入程式時可能把路徑寫壞，"
			"導致插帧不生效，啟動器會自動修好）" : g_fgx_note.c_str());
		ImGui::TextDisabled("修好驅動條目後 AI 插帧才會真正生效（啟動器每次啟動遊戲前會自動檢查並修復；OSD 的 DISP 會顯示插帧後幀數）；");
		ImGui::TextDisabled("說明：這是 NVIDIA 驅動級的 AI 插帧（AI frame interpolation / Smooth Motion），不是 DLSS 優設或 DLSS 幀生成；");
		ImGui::TextDisabled("本移植是 Vulkan 程式（沒有 D3D12 與運動向量），僅 RTX 40/50 有效，可能有輕微延遲或畫面偽影。");
	}
	ImGui::Dummy(ImVec2(0, em * 0.9f));

			ImGui::EndTabItem();
		}
		if (ImGui::BeginTabItem("其他設置")) {
			ImGui::Dummy(ImVec2(0, em * 0.5f));
			ui::heading("其他設置", em * 1.25f);
			ui::muted_wrapped("與遊戲檔案相關的其他功能：遊戲存放位置、存檔位置，以及添加到 Steam 庫。");
			ImGui::Dummy(ImVec2(0, em * 0.6f));

			/* M1794: the game-library location moved here from 主頁 ③ (the owner asked for it): the whole library -- game,
			 * saves, firmware, MODs -- moves with the switch, so it is only offered once the game is built. */
			ImGui::SeparatorText("遊戲存放位置");
			if (built) { ui::dot(ui::ready); ImGui::TextUnformatted("遊戲已構建：可以更改遊戲存放位置"); }
			else { ui::dot(ui::muted); ImGui::TextUnformatted("遊戲尚未構建：構建完成後才能更改存放位置"); }
			ImGui::TextDisabled("當前：%s", g_dump.c_str());
			{ const std::string built_dir = g_dump + "/decrypted/PCSH10109/recomp";   /* M1734: where the built game itself is */
			  ImGui::TextDisabled("構建後的遊戲：%s", built_dir.c_str());
			  if (built) { ImGui::SameLine(); if (ImGui::SmallButton("打開遊戲文件夾")) open_folder(built_dir); } }
			if (g_move_running) { ui::spinner(ui::accent); ImGui::SameLine(); ImGui::TextWrapped("正在把現有遊戲庫（含存檔）移動到新位置…（同盤瞬間完成；跨盤逐檔移動，邊複製邊刪除，不會佔用雙份空間）"); }
			if (!g_move_error.empty()) ui::muted_wrapped(g_move_error.c_str());
			if (g_move_running) ui::muted_wrapped("移動可能需要一點時間，期間請不要關閉啟動器。");
			ImGui::BeginDisabled(busy || g_move_running || !built);
			if (ImGui::Button("更改文件夾…")) change_game_folder();
			ImGui::SameLine();
			if (ImGui::Button("使用默認位置")) change_to_default_folder();
			ImGui::SameLine();
			if (ImGui::Button("打開文件夾")) open_folder(g_dump);
			ImGui::EndDisabled();
			if (!built) { ImGui::SameLine(); ImGui::TextDisabled("構建完成後可用"); }
			ImGui::TextDisabled("默認：%s", library_default_dir().c_str());
			ui::muted_wrapped("提示：這個位置是「整個遊戲庫」的位置。改到空文件夾時現有庫會移動過去；「使用默認位置」在默認位置為空時也會把整個庫移動回去；若新位置已有內容則直接使用它。移動後原位置不再保留（需要備份請先自行複製一份）。");
			ImGui::Dummy(ImVec2(0, em * 0.9f));

			ImGui::SeparatorText("存檔位置");
			/* the saves live in the built game's fs tree (runtime/core/apputil.c: savedata0: is <RECOMP_FS>/savedata0). The
			 * path follows g_dump, so a moved library moves the saves with it. */
			const std::string save_dir = g_dump + "/decrypted/PCSH10109/recomp/fs/savedata0";
			if (built) { ui::dot(ui::ready); ImGui::TextUnformatted("遊戲已構建：存檔文件夾可用"); }
			else { ui::dot(ui::muted); ImGui::TextUnformatted("遊戲尚未構建：構建完成後存檔文件夾才可用"); }
			ImGui::TextDisabled("存檔文件夾：%s", save_dir.c_str());
			ImGui::Dummy(ImVec2(0, em * 0.3f));
			ImGui::BeginDisabled(!built);
			if (ImGui::Button("打開存檔文件夾")) open_folder(save_dir);
			ImGui::SameLine();
			if (ImGui::Button("複製存檔路徑")) { if (!SDL_SetClipboardText(save_dir.c_str())) {} }
			ImGui::EndDisabled();
			if (!built) { ImGui::SameLine(); ImGui::TextDisabled("構建完成後可用"); }
			ImGui::Dummy(ImVec2(0, em * 0.4f));
			ui::muted_wrapped("提示：存檔會隨「遊戲存放位置」一起移動；備份存檔時直接複製這個文件夾即可。");
			ImGui::Dummy(ImVec2(0, em * 0.9f));

			/* M1788: add the port to the Steam library -- from then on it starts through Steam (overlay, play time), while
			 * the desktop launcher keeps working exactly as before. Needs the game built (gated) and Steam closed. */
			ImGui::SeparatorText("Steam");
#ifdef _WIN32
			ui::muted_wrapped("把本移植版加入 Steam 庫：之後可以在 Steam 裡啟動（Steam 覆蓋層、遊戲時長統計）；桌面啟動器仍然可以照常使用。");
			ui::muted_wrapped("注意：手柄使用遊戲內建的支援，本移植版不支援 Steam 的手柄配置（Steam Input）映射——在 Steam 裡改手把配置不會影響本作。");
			if (built) { ui::dot(ui::ready); ImGui::TextUnformatted("遊戲已構建：可以添加到 Steam 庫（封面/背景由遊戲檔案即時生成）"); }
			else { ui::dot(ui::muted); ImGui::TextUnformatted("遊戲尚未構建：構建完成後才能添加到 Steam 庫"); }
			ImGui::BeginDisabled(busy || !built);
			if (ImGui::Button("添加到 Steam 庫")) { std::string m; g_p5d_steam_ok = p5d_steam_add(m); g_p5d_steam_msg = m; }
			ImGui::EndDisabled();
			if (!built) { ImGui::SameLine(); ImGui::TextDisabled("構建完成後可用"); }
			if (!g_p5d_steam_msg.empty()) {
				ui::dot(g_p5d_steam_ok ? ui::ready : ui::warn);
				ImGui::TextWrapped("%s", g_p5d_steam_msg.c_str());
			}
			ImGui::TextDisabled("加入後如果 Steam 裡沒有出現：重新啟動 Steam；Steam 執行時請勿再次添加。");
#else
			ui::muted_wrapped("Steam 快捷方式目前只在 Windows 版啟動器裡提供。");
#endif

			/* M1823: re-open the first-run notice from here (players may want to read it again). */
			ImGui::Dummy(ImVec2(0, em * 0.9f));
			ImGui::SeparatorText("其他");
			if (ImGui::Button("查看使用條款／免責聲明")) g_p5d_disclaimer_ask = true;

			ImGui::EndTabItem();
		}
		if (ImGui::BeginTabItem("金手指")) {
			ImGui::Dummy(ImVec2(0, em * 0.5f));
			ui::heading("金手指", em * 1.25f);
			ui::muted_wrapped("遊戲內直接按鍵即可使用的內置金手指（不需要安裝任何東西，也不會修改遊戲檔案或存檔）。");
			ImGui::Dummy(ImVec2(0, em * 0.5f));

			ImGui::SeparatorText("F5：自動演奏");
			ImGui::TextUnformatted("在遊戲中按 F5 開啟 / 關閉自動演奏：演奏時自動命中，適合只想看演出或解鎖歌曲。");
			ImGui::TextDisabled("可能會偶爾在部分地方觸發閃退。");
			ImGui::Dummy(ImVec2(0, em * 0.6f));

			ImGui::SeparatorText("F6：一鍵解鎖");
			ImGui::TextUnformatted("在遊戲主選單按 F6：COMMUNITY 全部解鎖、全支援與挑戰解鎖、歌曲記錄全滿。");
			ImGui::TextDisabled("按鍵後畫面上方會顯示提示框（約 1 秒）。");
			ImGui::TextDisabled("F6 會把全部事件 flag 置滿，因此歌曲成績會顯示為滿分 / 全連段；不想影響真實記錄時，請不要在按 F6 後存檔。");
			ImGui::Dummy(ImVec2(0, em * 0.6f));

			ImGui::SeparatorText("說明");
			ImGui::TextDisabled("適合測試、看劇情與快速解鎖；正常遊玩時請不要使用，以免破壞成就與記錄體驗。");
			ImGui::Dummy(ImVec2(0, em * 0.9f));
			ImGui::EndTabItem();
		}
		/* ATIV_SHOT documentation aid: P5D_SHOT_TAB=MOD opens the MOD page for a screenshot */
		const bool shot_mod_tab = getenv("ATIV_SHOT") && getenv("P5D_SHOT_TAB") && !strcmp(getenv("P5D_SHOT_TAB"), "MOD");
		if (ImGui::BeginTabItem("MOD", nullptr, shot_mod_tab ? ImGuiTabItemFlags_SetSelected : 0)) {
			ImGui::Dummy(ImVec2(0, em * 0.5f));
			ui::heading("MOD", em * 1.25f);
			ui::muted_wrapped("支援 Reloaded-II 格式的 MOD（Mod.xml + Data/ 文件夾）。導入後可逐個開關；啟用時啟動遊戲會用 MOD 的文件替換遊戲內同名資源。");
			ImGui::Dummy(ImVec2(0, em * 0.4f));
			ImGui::BeginDisabled(busy);
			if (ImGui::Button("添加 MOD 文件夾…")) pick_folder(win, &g_p5d_mod_src);
			ImGui::SameLine(); ImGui::TextDisabled("選擇包含 Mod.xml 的文件夾（或其上一層）");
			ImGui::EndDisabled();
			if (!g_p5d_mod_src.empty() && g_p5d_mod_src != g_p5d_mod_src_seen) {
				g_p5d_mod_src_seen = g_p5d_mod_src;
				std::string src = g_p5d_mod_src;
				if (!exists(src + "/Mod.xml")) {   /* accept the parent folder: take the first child that is a mod */
					DIR *dd = opendir(src.c_str());
					if (dd) { while (struct dirent *ce = readdir(dd)) { std::string cn = ce->d_name; if (cn == "." || cn == "..") continue;
						if (exists(src + "/" + cn + "/Mod.xml")) { src = src + "/" + cn; break; } } closedir(dd); }
				}
				mods_import(src); g_mods_loaded = false;
			}
			if (ImGui::Button("重新掃描")) g_mods_loaded = false;
			if (!g_mods_loaded) { mods_scan(g_mods); g_mods_loaded = true; }
			ImGui::Dummy(ImVec2(0, em * 0.5f));
			if (g_mods.empty()) { ui::dot(ui::muted); ImGui::TextUnformatted("尚未導入 MOD"); }
			else {
				std::string root = mods_root(); (void)root;
				std::vector<P5dMod> all = g_mods; bool dirty = false;
				std::string to_remove;
				const float img_h = em * 5.0f;
				for (auto &m : all) {
					const ImVec2 card_start = ImGui::GetCursorScreenPos();
					const float card_w = ImGui::GetContentRegionAvail().x;
					ImGui::PushID(m.dir.c_str());
					ImGui::BeginGroup();
					if (!m.cover.empty()) { Tex t = texture(m.cover); if (t.t) ImGui::Image(tex_ref(t), ImVec2(em * 5.0f, em * 5.0f)); else ImGui::Dummy(ImVec2(em * 5.0f, em * 5.0f)); }
					else ImGui::Dummy(ImVec2(em * 5.0f, em * 5.0f));
					ImGui::EndGroup();
					ImGui::SameLine();
					ImGui::BeginGroup();
					ImGui::TextUnformatted(m.title.c_str());
					std::string sub = std::string("作者：") + (m.author.empty() ? "未知" : m.author) + "   版本：" + (m.version.empty() ? "-" : m.version);
					ImGui::TextDisabled("%s", sub.c_str());
					if (!m.desc.empty()) { ImGui::PushTextWrapPos(ImGui::GetFontSize() * 30.0f); ImGui::TextDisabled("%s", m.desc.c_str()); ImGui::PopTextWrapPos(); }
					bool en = m.enabled;
					if (ImGui::Checkbox("啟用", &en)) { m.enabled = en; dirty = true; }
					ImGui::SameLine(); ImGui::TextDisabled(en ? "啟動遊戲時生效" : "未啟用");
					ImGui::EndGroup();
					/* M1824: the card's real height is the taller of the cover and the text column. The separator used to
					 * be drawn right after the 撤銷導入 button, whose SetCursorScreenPos puts the cursor at the cover's
					 * bottom edge -- so with a long description the line ran through the text (separator position was
					 * the cover height, not the card height). */
					const float card_h = std::max(img_h, ImGui::GetItemRectSize().y);
					{   /* M1749: 撤銷導入（右下角） */
						const char *label = "撤銷導入";
						const ImVec2 ts = ImGui::CalcTextSize(label);
						const ImGuiStyle &st = ImGui::GetStyle();
						const float bw = ts.x + st.FramePadding.x * 2.0f, bh = ts.y + st.FramePadding.y * 2.0f;
						ImGui::SetCursorScreenPos(ImVec2(card_start.x + card_w - bw, card_start.y + card_h - bh));
						ImGui::PushStyleColor(ImGuiCol_Button, ImVec4(0.45f, 0.18f, 0.18f, 1.0f));
						ImGui::PushStyleColor(ImGuiCol_ButtonHovered, ImVec4(0.62f, 0.24f, 0.24f, 1.0f));
						ImGui::PushStyleColor(ImGuiCol_ButtonActive, ImVec4(0.38f, 0.14f, 0.14f, 1.0f));
						if (ImGui::Button(label)) to_remove = m.dir;
						ImGui::PopStyleColor(3);
					}
					ImGui::SetCursorScreenPos(ImVec2(card_start.x, card_start.y + card_h + ImGui::GetStyle().ItemSpacing.y));
					ImGui::Separator();
					ImGui::PopID();
				}
				if (dirty) { mods_save(all); g_mods = all; }
				if (!to_remove.empty()) {   /* M1749: 撤销导入：删文件夹、改写启用列表、刷新 */
					const bool ok = mods_delete_tree(to_remove);
					if (!ok) fprintf(stderr, "mods: could not remove %s\n", to_remove.c_str());
					mods_scan(g_mods); g_mods_loaded = true;
					mods_save(g_mods);
				}
			}
			ImGui::Dummy(ImVec2(0, em * 0.9f));
			ImGui::EndTabItem();
		}
		ImGui::EndTabBar();
	}

	ImGui::End();
}

/* ---- ATIV_SHOT: one frame into a file, no visible window */
static int shot(SDL_Window *win, const char *path, int w, int h) {
	SDL_GPUTextureCreateInfo ci = {};
	ci.type = SDL_GPU_TEXTURETYPE_2D; ci.format = SDL_GPU_TEXTUREFORMAT_R8G8B8A8_UNORM; ci.usage = SDL_GPU_TEXTUREUSAGE_COLOR_TARGET;
	ci.width = (Uint32)w; ci.height = (Uint32)h; ci.layer_count_or_depth = 1; ci.num_levels = 1;
	SDL_GPUTexture *t = SDL_CreateGPUTexture(g_gpu, &ci);
	SDL_GPUTransferBufferCreateInfo dc = {}; dc.usage = SDL_GPU_TRANSFERBUFFERUSAGE_DOWNLOAD; dc.size = (Uint32)(w * h * 4);
	SDL_GPUTransferBuffer *down = SDL_CreateGPUTransferBuffer(g_gpu, &dc);
	if (!t || !down) { fprintf(stderr, "ATIV_SHOT: out of GPU memory\n"); return 1; }
	const int frames = 40;
	for (int f = 0; f < frames; f++) {   /* ImGui sizes auto-sized windows on the first frames; a modal's dim fades in */
		ImGui_ImplSDLGPU3_NewFrame(); ImGui_ImplSDL3_NewFrame();
		ImGui::GetIO().DisplaySize = ImVec2((float)w, (float)h); ImGui::GetIO().DisplayFramebufferScale = ImVec2(1, 1); ImGui::GetIO().DeltaTime = 1.0f / 60;
		ImGui::NewFrame(); hub_ui(win); ImGui::Render();
		ImDrawData *dd = ImGui::GetDrawData();
		SDL_GPUCommandBuffer *cmd = SDL_AcquireGPUCommandBuffer(g_gpu);
		ImGui_ImplSDLGPU3_PrepareDrawData(dd, cmd);
		SDL_GPUColorTargetInfo ti = {}; ti.texture = t; ti.clear_color = SDL_FColor{ui::bg.x, ui::bg.y, ui::bg.z, 1}; ti.load_op = SDL_GPU_LOADOP_CLEAR; ti.store_op = SDL_GPU_STOREOP_STORE;
		SDL_GPURenderPass *rp = SDL_BeginGPURenderPass(cmd, &ti, 1, nullptr);
		ImGui_ImplSDLGPU3_RenderDrawData(dd, cmd, rp);
		SDL_EndGPURenderPass(rp);
		if (f == frames - 1) {
			SDL_GPUCopyPass *cp = SDL_BeginGPUCopyPass(cmd);
			SDL_GPUTextureRegion src = {}; src.texture = t; src.w = (Uint32)w; src.h = (Uint32)h; src.d = 1;
			SDL_GPUTextureTransferInfo dst = {}; dst.transfer_buffer = down; dst.pixels_per_row = (Uint32)w; dst.rows_per_layer = (Uint32)h;
			SDL_DownloadFromGPUTexture(cp, &src, &dst);
			SDL_EndGPUCopyPass(cp);
		}
		SDL_GPUFence *fence = SDL_SubmitGPUCommandBufferAndAcquireFence(cmd);
		SDL_WaitForGPUFences(g_gpu, true, &fence, 1); SDL_ReleaseGPUFence(g_gpu, fence);
	}
	const uint8_t *px = (const uint8_t *)SDL_MapGPUTransferBuffer(g_gpu, down, false);
	FILE *f = fopen(path, "wb");
	if (!f || !px) { fprintf(stderr, "ATIV_SHOT: can't write %s\n", path); return 1; }
	fprintf(f, "P6 %d %d 255\n", w, h);
	for (int i = 0; i < w * h; i++) fwrite(px + 4 * i, 1, 3, f);
	fclose(f); SDL_UnmapGPUTransferBuffer(g_gpu, down);
	fprintf(stderr, "ATIV_SHOT: %s\n", path);
	return 0;
}

/* the repository (or an install of it): ATIV_ROOT, else the one the launcher sits in -- launcher/nativ, or beside it
 * at the top -- wherever it was moved, else where it was built */
static std::string find_root(void) {
	if (const char *r = getenv("ATIV_ROOT")) if (*r) return r;
	if (const char *b = SDL_GetBasePath())
		for (const char *up : {"..", "."}) {
			std::string r = std::string(b) + up;
#ifdef _WIN32
			char full[MAX_PATH * 4]; if (_fullpath(full, r.c_str(), sizeof full)) r = full;
#else
			if (char *full = realpath(r.c_str(), nullptr)) { r = full; free(full); }
#endif
			while (r.size() > 1 && (r.back() == '/' || r.back() == '\\')) r.pop_back();
			if (exists(r + "/pipeline/vitarecomp.py")) return r;
		}
	return REPO_ROOT;
}

/* the player's library (pipeline/datadir.py makes the same choice; the stages get this one as ATIV_DUMP): ATIV_DUMP, else
 * the folder chosen in Settings (prefs p5d_libdir), else <root>/dump when it exists (a checkout, an install from before),
 * else the platform's per-user data folder -- local, not roaming, on Windows: a game is gigabytes -- so an update replaces
 * the install without touching what the player made */
static std::string library_default_dir(void) {   /* (what "Use default" goes back to: the rule before M1732) */
	if (exists(g_root + "/dump")) return g_root + "/dump";
	const char *home = getenv("HOME"); std::string base;
#ifdef _WIN32
	const char *la = getenv("LOCALAPPDATA"), *up = getenv("USERPROFILE");
	base = la && *la ? la : std::string(up ? up : ".") + "/AppData/Local";
#elif defined(__APPLE__)
	base = std::string(home ? home : ".") + "/Library/Application Support";
#else
	const char *xdg = getenv("XDG_DATA_HOME");
	base = xdg && *xdg ? xdg : std::string(home ? home : ".") + "/.local/share";
#endif
	(void)home;
	return base + "/P5D-Port/P5D/library";
}
/* M1736: the saves live inside the library, so switching to an empty folder looked like they were gone. When the new
 * folder is empty and the current library has content, copy the whole library there in the background (the old folder is
 * left untouched as a backup) and switch only when the copy finished. An already-populated folder is used as it is. */
static bool looks_like_library(const std::string &p) {   /* M1747: a real library, not a folder with leftovers */
	return exists(p + "/firmware") && exists(p + "/decrypted");
}
static bool prune_empty_dirs(const std::string &p) {   /* M1747: remove empty directories (leftovers); returns true if p is gone */
	DIR *d = opendir(p.c_str()); if (!d) return false;
	bool any = false;
	while (struct dirent *e = readdir(d)) {
		if (!strcmp(e->d_name, ".") || !strcmp(e->d_name, "..")) continue;
		const std::string a = p + "/" + e->d_name;
		struct stat st; if (stat(a.c_str(), &st) != 0) { any = true; continue; }
		if (S_ISDIR(st.st_mode)) { if (!prune_empty_dirs(a)) any = true; }
		else any = true;
	}
	closedir(d);
	if (!any) { rmdir(p.c_str()); return true; }
	return false;
}
static bool dir_has_entries(const std::string &p) {
	DIR *d = opendir(p.c_str()); if (!d) return false;
	bool any = false;
	while (struct dirent *e = readdir(d)) { if (strcmp(e->d_name, ".") && strcmp(e->d_name, "..")) { any = true; break; } }
	closedir(d);
	return any;
}
/* a portable recursive copy (the runtime's win32_compat.h force-include defines a "sync" macro, so no <filesystem>) */
static bool copy_tree(const std::string &src, const std::string &dst) {
	make_dir(dst);
	DIR *d = opendir(src.c_str()); if (!d) return false;
	bool ok = true;
	while (struct dirent *e = readdir(d)) {
		if (!strcmp(e->d_name, ".") || !strcmp(e->d_name, "..")) continue;
		const std::string a = src + "/" + e->d_name, b = dst + "/" + e->d_name;
		struct stat st;
		if (stat(a.c_str(), &st) != 0) { ok = false; continue; }
		if (S_ISDIR(st.st_mode)) { ok = copy_tree(a, b) && ok; continue; }
		FILE *in = fopen(a.c_str(), "rb");
		if (!in) { ok = false; continue; }
		FILE *out = fopen(b.c_str(), "wb");
		if (!out) { fclose(in); ok = false; continue; }
		static thread_local char buf[1 << 20]; size_t n;
		while ((n = fread(buf, 1, sizeof buf, in)) > 0) if (fwrite(buf, 1, n, out) != n) { ok = false; break; }
		fclose(in); fclose(out);
	}
	closedir(d);
	return ok;
}
static bool delete_tree(const std::string &p) {   /* (used only for a move: the source after a complete copy) */
	DIR *d = opendir(p.c_str()); if (!d) return remove(p.c_str()) == 0;
	bool ok = true;
	while (struct dirent *e = readdir(d)) {
		if (!strcmp(e->d_name, ".") || !strcmp(e->d_name, "..")) continue;
		const std::string a = p + "/" + e->d_name;
		struct stat st;
		if (stat(a.c_str(), &st) != 0) { ok = false; continue; }
		if (S_ISDIR(st.st_mode)) ok = delete_tree(a) && ok; else if (remove(a.c_str()) != 0) ok = false;
	}
	closedir(d);
	if (ok) rmdir(p.c_str());
	return ok;
}
/* M1738: a true cross-volume move, file by file: each file is copied to the new folder and only then removed from the
 * old one, so the two disks never hold the whole library twice (the total stays about one library). A failure rolls the
 * already-moved files back, so the library is never split between the two folders. */
static bool move_files_progressive(const std::string &src, const std::string &dst, const std::string &rel,
                                   std::vector<std::string> &moved, std::string &err) {
	make_dir(dst);
	DIR *d = opendir(src.c_str());
	if (!d) { err = src; return false; }
	while (struct dirent *e = readdir(d)) {
		if (!strcmp(e->d_name, ".") || !strcmp(e->d_name, "..")) continue;
		const std::string a = src + "/" + e->d_name, b = dst + "/" + e->d_name, r = rel.empty() ? e->d_name : rel + "/" + e->d_name;
#ifdef _WIN32
		{   /* M1744: check the link attribute FIRST -- a junction whose target is gone made stat() fail and aborted the
			 * whole move (the target folder was rolled back and vanished). Links are re-created by the pipeline, never moved. */
			const DWORD at = GetFileAttributesW(wide(a).c_str());
			if (at != INVALID_FILE_ATTRIBUTES && (at & FILE_ATTRIBUTE_REPARSE_POINT)) continue;
		}
#endif
		struct stat st;
		if (stat(a.c_str(), &st) != 0) {
			fprintf(stderr, "move: skipping unreadable %s\n", a.c_str());
			continue;
		}
		if (S_ISDIR(st.st_mode)) {
			if (!move_files_progressive(a, b, r, moved, err)) { closedir(d); return false; }
			rmdir(a.c_str());
			continue;
		}
		FILE *in = fopen(a.c_str(), "rb"); if (!in) { err = a; closedir(d); return false; }
		FILE *out = fopen(b.c_str(), "wb"); if (!out) { fclose(in); err = a; closedir(d); return false; }
		static thread_local char buf[1 << 20]; size_t n; bool ok = true;
		while ((n = fread(buf, 1, sizeof buf, in)) > 0) if (fwrite(buf, 1, n, out) != n) { ok = false; break; }
		const bool bad = ferror(in) != 0;
		fclose(in); fclose(out);
		if (!ok || bad) { remove(b.c_str()); err = a; closedir(d); return false; }
		if (remove(a.c_str()) != 0) {   /* copied but could not delete: leave it and report the library as moved */
			fprintf(stderr, "move: copied %s but could not remove it\n", a.c_str());
			continue;
		}
		moved.push_back(r);
	}
	closedir(d);
	return true;
}
static bool move_library(const std::string &src, const std::string &dst, std::string &errpath) {
#ifdef _WIN32
	if (rmdir(dst.c_str()) == 0) {   /* a directory rename wants the name free */
		if (MoveFileW(wide(src).c_str(), wide(dst).c_str())) return true;
		make_dir(dst);
	}
#else
	if (rename(src.c_str(), dst.c_str()) == 0) return true;
#endif
	std::vector<std::string> moved; std::string err;
	if (move_files_progressive(src, dst, "", moved, err)) { rmdir(src.c_str()); return true; }
	errpath = err;
	/* roll back: put the already-moved files back so the library stays in one piece */
	fprintf(stderr, "move: failed on %s -- rolling back\n", err.c_str());
	for (const std::string &r : moved) {
		const std::string a = src + "/" + r, b = dst + "/" + r;
		FILE *in = fopen(b.c_str(), "rb"); if (!in) continue;
		const std::string dir = a.substr(0, a.find_last_of('/'));
		make_dir(dir);
		FILE *out = fopen(a.c_str(), "wb"); if (!out) { fclose(in); continue; }
		static thread_local char buf[1 << 20]; size_t n;
		while ((n = fread(buf, 1, sizeof buf, in)) > 0) fwrite(buf, 1, n, out);
		fclose(in); fclose(out);
	}
	delete_tree(dst);
	make_dir(dst);   /* M1744: leave the folder the player picked in place */
	return false;
}
static void move_log(const std::string &line) {
	const std::string d = pref_dir();
	if (d.empty()) return;
	FILE *f = fopen((d + "launcher-move.log").c_str(), "a");
	if (!f) return;
	fprintf(f, "%s\n", line.c_str());
	fclose(f);
}
static void game_folder_move_poll(void) {
	if (!g_move_finished.exchange(false)) return;
	if (!g_move_ok) { g_move_error = "移動失敗（" + g_move_error + "）：遊戲庫保持原樣，原位置不變"; return; }
	if (g_move_clear_pref) prefs_set("p5d_libdir", ""); else prefs_set("p5d_libdir", g_move_to);
	g_dump = g_move_to; make_dir(g_dump); library_scan();
	g_move_error.clear();
}
static void switch_game_folder(const std::string &picked, bool is_default) {
	if (picked.empty() || picked == g_dump) return;
	const std::string old = g_dump;
	make_dir(picked);
	const bool target_lib = looks_like_library(picked);
	const bool old_has = dir_has_entries(old) || exists(old + "/decrypted") || exists(old + "/firmware");
	if (old_has && !target_lib) prune_empty_dirs(picked);   /* leftovers of an old failed move must not block the move */
	const bool target_empty = !dir_has_entries(picked);
	move_log(std::string("decide: target_empty=") + (target_empty ? "1" : "0") + " target_lib=" + (target_lib ? "1" : "0") + " old_has=" + (old_has ? "1" : "0"));
	if (old_has && !target_lib && !target_empty) {
		g_move_error = "目標文件夾裡有其它文件，且不是遊戲庫。請選擇一個空文件夾（或先在資源管理器裡清空它）。";
		return;
	}
	if (old_has && !target_lib) {   /* move first, switch after: saves and builds travel with it */
		g_move_to = picked; g_move_clear_pref = is_default;
		g_move_ok = false; g_move_finished = false; g_move_running = true; g_move_error.clear();
		move_log("move: " + old + " -> " + picked);
		std::thread([old, picked] {
			std::string errpath;
			const bool ok = move_library(old, picked, errpath);
			move_log(ok ? "move: done " + picked : "move: FAILED " + errpath);
			if (!ok && !errpath.empty()) g_move_error = errpath;
			g_move_ok = ok; g_move_running = false; g_move_finished = true;
		}).detach();
		return;
	}
	if (is_default) prefs_set("p5d_libdir", ""); else prefs_set("p5d_libdir", picked);
	g_dump = picked; make_dir(g_dump); library_scan();
}
static void change_game_folder(void) {
	g_move_error.clear();
	const std::string picked = pick_folder_dialog(g_dump);
	move_log("change: picked=\"" + picked + "\" current=\"" + g_dump + "\"");
	if (picked.empty()) { g_move_error = "沒有選擇文件夾（文件夾對話框被取消）"; return; }
	switch_game_folder(picked, false);
}
static void change_to_default_folder(void) {
	g_move_error.clear();
	const std::string def = library_default_dir();
	move_log("default: target=\"" + def + "\" current=\"" + g_dump + "\"");
	switch_game_folder(def, true);
}
static std::string library_dir(void) {
	if (const char *d = getenv("ATIV_DUMP")) if (*d) return d;
	{ auto it = g_prefs.find("p5d_libdir"); if (it != g_prefs.end() && !it->second.empty()) return it->second; }   /* M1732: the player's choice */
	return library_default_dir();
}

static int task_cli(const std::string &t) {   /* ATIV_TASK */
	size_t c = t.find(':'); std::string kind = t.substr(0, c), arg = c == std::string::npos ? "" : t.substr(c + 1);
	library_scan();
	const Game *g = nullptr; for (const Game &x : g_games) if (x.id == arg) g = &x;
	if ((kind == "play" || kind == "build") && !g) { fprintf(stderr, "ATIV_TASK: no game %s in the library\n", arg.c_str()); return 2; }
	if (kind == "play") start_play(*g);
	else if (kind == "build") start_build(*g);
	else if (kind == "scan") task_start("Searching a folder", "scan", "", {step("Searching", vitarecomp({"scan", arg, "--out", scan_file()}))});
	else if (kind == "licences") task_start("Importing licences", "licences", "", {step("", vitarecomp({"licenses", "import", arg}))});
	else if (kind == "firmware") task_start("Installing the firmware", "firmware", "", {step("Decrypting the system update", vitarecomp({"firmware", arg})), step("Installed")});
	else { fprintf(stderr, "ATIV_TASK: play|build|scan|licences|firmware\n"); return 2; }
	const char *cancel = getenv("ATIV_TASK_CANCEL");
	Uint64 t0 = SDL_GetTicks();
	while (g_task.running) {
		SDL_Delay(50);
		if (cancel && SDL_GetTicks() - t0 > (Uint64)(atof(cancel) * 1000)) { task_cancel(); cancel = nullptr; }
	}
	g_task.reader.join();
#ifdef _WIN32
	_setmode(_fileno(stdout), _O_BINARY);   /* (the log as the steps wrote it: no second \r before each \n) */
#endif
	fwrite(g_log.data(), 1, g_log.size(), stdout);
	if (kind == "scan" && g_task.ok) { scan_load(scan_file()); printf("(%zu found)\n", g_found.size()); }
	return g_task.ok ? 0 : 1;
}

#ifdef __APPLE__
/* the Mac app's own checks, before its window: where it runs from (a temporary copy macOS makes of a downloaded app
 * opened where it landed, or a read-only disk image: it belongs in Applications), the download's quarantine on its own
 * files (cleared once the player has opened it), and Apple's Command Line Tools (every game build needs their compiler
 * and SDK: Apple's to install, not ours to ship). False: it said why and the launcher stops. */
static bool mac_preflight(void) {
	struct statfs fs;
	const bool in_place = g_root.find("/AppTranslocation/") == std::string::npos && !(statfs(g_root.c_str(), &fs) == 0 && (fs.f_flags & MNT_RDONLY));
	if (!in_place) {
		const SDL_MessageBoxButtonData b[2] = {{SDL_MESSAGEBOX_BUTTON_RETURNKEY_DEFAULT, 1, "Open Applications"}, {SDL_MESSAGEBOX_BUTTON_ESCAPEKEY_DEFAULT, 0, "Quit"}};
		const SDL_MessageBoxData m = {SDL_MESSAGEBOX_INFORMATION, nullptr, "Project Nativ", "Drag Project Nativ into your Applications folder first, then open it from there.", 2, b, nullptr};
		int hit = 0; SDL_ShowMessageBox(&m, &hit);
		if (hit == 1) SDL_OpenURL("file:///Applications");
		return false;
	}
	const size_t c = g_root.rfind("/Contents/Resources");   /* (inside the app: its bundle) */
	const std::string app = c != std::string::npos ? g_root.substr(0, c) : g_root;
	if (getxattr(app.c_str(), "com.apple.quarantine", nullptr, 0, 0, 0) >= 0) (void)!system(("xattr -dr com.apple.quarantine '" + app + "' 2>/dev/null").c_str());
	if (system("xcode-select -p >/dev/null 2>&1") != 0) {
		(void)!system("xcode-select --install >/dev/null 2>&1");
		SDL_ShowSimpleMessageBox(SDL_MESSAGEBOX_INFORMATION, "P5D 移植版", "P5D builds the game with Apple's free Command Line Tools.\n\nInstall them from the window that just opened, then open P5D 移植版 again.", nullptr);
		return false;
	}
	return true;
}
#endif

int main(int argc, char **argv) {
	g_root = find_root();
	if (!exists(g_root + "/pipeline/vitarecomp.py")) {   /* (the launcher apart from its folder: run from inside the zip, or copied out alone) */
		SDL_ShowSimpleMessageBox(SDL_MESSAGEBOX_ERROR, "P5D 移植版", "P5D 移植版找不到运行所需的文件。\n\n请重新下载完整的 exe（不要从压缩包/临时文件夹里直接运行），再打开它。", nullptr);
		return 1;
	}
	prefs_load();   /* M1732: first, because library_dir honours the saved game-files folder */
	g_dump = library_dir();
	make_dir(g_dump);   /* (a chosen folder on another drive may not exist yet: the library makes itself) */
	/* M1740: no ATIV_DUMP in our own environment -- the child steps get it explicitly (proc_start) */
	for (int i = 1; i + 1 < argc; i++) if (!strcmp(argv[i], "--import-dlc")) {   /* the DLC copy without the window */
		std::vector<std::string> a{python_exe(), "-c", p5d_dlc_script(), argv[i + 1], g_dump};
		Proc p;
		if (!proc_start(p, a, {})) { fprintf(stderr, "can't start python\n"); return 1; }
		char buf[4096]; long n; while ((n = proc_read(p, buf, sizeof buf)) > 0) { fwrite(buf, 1, (size_t)n, stdout); fflush(stdout); }
		int code = proc_wait(p); proc_done(p);
		return code;
	}
#ifdef _WIN32
	if (const char *rf = getenv("P5D_REPAIR_FGX")) {
		if (*rf) {
			std::string d; bool fixed = p5d_repair_fgx_profile(&d);
			fprintf(stderr, "P5D_REPAIR_FGX: %s (%s)\n", fixed ? "repaired" : "unchanged", d.c_str());
			if (const char *tp = getenv("TEMP")) {
				std::string f = std::string(tp) + "\\p5d_fgx_result.txt";
				FILE *fp = fopen(f.c_str(), "wb");
				if (fp) { fprintf(fp, "%s (%s)\n", fixed ? "repaired" : "unchanged", d.c_str()); fclose(fp); }
			}
			return 0;
		}
	}
#endif   /* (the stages it runs: the same library whatever their own rule finds) */
#ifdef _WIN32
	{   /* M1788: the headless self test of 添加到 Steam 庫 (P5D_STEAM_DIR / P5D_STEAM_STUB_DIR / P5D_STEAM_ADD[_OUT]) */
		const char *sa = getenv("P5D_STEAM_ADD");
		if (sa && *sa) {
			std::string m; bool ok = p5d_steam_add(m);
			fprintf(stderr, "STEAM_ADD: %s\n%s\n", ok ? "ok" : "failed", m.c_str());
			if (const char *o = getenv("P5D_STEAM_ADD_OUT")) if (FILE *f = fopen(o, "wb")) { fprintf(f, "%s\n%s\n", ok ? "ok" : "failed", m.c_str()); fclose(f); }
			return ok ? 0 : 1;
		}
	}
#endif
	const char *shot_path = getenv("ATIV_SHOT");
#ifdef SIGPIPE
	signal(SIGPIPE, SIG_IGN);
#endif
#ifdef __APPLE__
	if (!shot_path && !getenv("ATIV_TASK") && !mac_preflight()) return 0;
#endif
	if (!getenv("PYTHONPYCACHEPREFIX")) set_env("PYTHONPYCACHEPREFIX", pref_dir() + "pycache");   /* (the stages' compiled Python beside the settings: an install is never written) */
	if (!getenv("PYTHONUTF8")) set_env("PYTHONUTF8", "1");   /* (the stages' Python in UTF-8 mode: Windows' cp1252 default crashed an add on a game title outside it) */
#if !defined(_WIN32) && !defined(__APPLE__)
	if (!getenv("ZIG_GLOBAL_CACHE_DIR")) {   /* (Linux's compiler's own cache, kept per user: an AppImage's install can't be written, and it outlives an update) */
		const char *x = getenv("XDG_CACHE_HOME"), *h = getenv("HOME");
		set_env("ZIG_GLOBAL_CACHE_DIR", (x && *x ? std::string(x) : std::string(h ? h : "/tmp") + "/.cache") + "/ProjectNativ/zig");
	}
#endif
	if (const char *t = getenv("ATIV_TASK")) return task_cli(t);   /* (after the caches above: a task's steps run as the window's do) */
	if (const char *ft = getenv("ATIV_FOLDER_TEST")) {   /* test hook: move the library to <folder>, report, exit */
		make_dir(std::string(ft));
		std::string err;
		const bool ok = move_library(g_dump, std::string(ft), err);
		fprintf(stderr, "[FOLDERTEST] %s -> %s ok=%d%s%s\n", g_dump.c_str(), ft, (int)ok, ok ? "" : " err=", ok ? "" : err.c_str());
		move_log(ok ? "test: moved " + g_dump + " -> " + ft : "test: FAILED " + err);
		return ok ? 0 : 1;
	}
	if (!shot_path) {   /* (the last launcher's log kept beside this one's) */
		const std::string d = pref_dir();
		if (!d.empty()) { g_log_file = d + "launcher.log"; remove((d + "launcher.prev.log").c_str()); rename(g_log_file.c_str(), (d + "launcher.prev.log").c_str()); }
	}
	if (!SDL_Init(SDL_INIT_VIDEO | SDL_INIT_GAMEPAD)) { fprintf(stderr, "SDL_Init: %s\n", SDL_GetError()); return 1; }
	int sw = 1280, sh = 800;
	if (const char *s = getenv("ATIV_SHOT_SIZE")) sscanf(s, "%dx%d", &sw, &sh);
	const float scale = shot_path ? 1.0f : SDL_GetDisplayContentScale(SDL_GetPrimaryDisplay());
	SDL_Window *win = shot_path ? SDL_CreateWindow(p5d_mode() ? P5D_TITLE : "Project Nativ", sw, sh, SDL_WINDOW_HIDDEN)
	                            : SDL_CreateWindow(p5d_mode() ? P5D_TITLE : "Project Nativ", (int)(1180 * scale), (int)(760 * scale), SDL_WINDOW_RESIZABLE | SDL_WINDOW_HIGH_PIXEL_DENSITY);
	g_gpu = SDL_CreateGPUDevice(SDL_GPU_SHADERFORMAT_SPIRV | SDL_GPU_SHADERFORMAT_DXIL | SDL_GPU_SHADERFORMAT_METALLIB, false, nullptr);
	if (!win || !g_gpu || (!shot_path && !SDL_ClaimWindowForGPUDevice(g_gpu, win))) { fprintf(stderr, "window/GPU: %s\n", SDL_GetError()); return 1; }
	g_hub_win = win;
	if (!shot_path) SDL_SetGPUSwapchainParameters(g_gpu, win, SDL_GPU_SWAPCHAINCOMPOSITION_SDR, SDL_GPU_PRESENTMODE_VSYNC);
	SDL_SetWindowMinimumSize(win, 420, 480);
	window_icon(win);

	IMGUI_CHECKVERSION();
	ImGui::CreateContext();
	ImGuiIO &io = ImGui::GetIO();
	io.IniFilename = nullptr;
	io.ConfigFlags |= ImGuiConfigFlags_NavEnableKeyboard | ImGuiConfigFlags_NavEnableGamepad;   /* a controller (or the arrows) moves through everything; L1/R1 the tabs */
	if (p5d_mode()) p5d_font(io); else ui::load_system_font(io);
	ui::apply(16.0f, scale);
	ImGui_ImplSDL3_InitForSDLGPU(win);
	ImGui_ImplSDLGPU3_InitInfo info = {};
	info.Device = g_gpu; info.ColorTargetFormat = shot_path ? SDL_GPU_TEXTUREFORMAT_R8G8B8A8_UNORM : SDL_GetGPUSwapchainTextureFormat(g_gpu, win); info.MSAASamples = SDL_GPU_SAMPLECOUNT_1;
	ImGui_ImplSDLGPU3_Init(&info);

	g_settings_writable = !shot_path || getenv("ATIV_PREFS");
	if (g_settings_writable) settings_migrate();   /* (a screenshot run touches no one's settings but a test folder's) */
	set_env("RECOMP_SETTINGS_SHARED", shared_path());   /* the games it starts read the same shared file (runtime/core/main.c) */
	library_scan();
	g_setup_open = g_prefs["setup_done"] != "1" || !g_firmware;   /* first run, or the firmware still missing */
	if (!g_firmware && g_prefs["setup_done"] == "1") g_setup_step = 1;
	if (shot_path) {
		std::string ui_sel = getenv("ATIV_SHOT_UI") ? getenv("ATIV_SHOT_UI") : "library";
		g_setup_open = ui_sel.rfind("setup", 0) == 0;
		if (g_setup_open) g_setup_step = ui_sel.size() > 6 ? atoi(ui_sel.c_str() + 6) : 0;
		g_add_open = ui_sel == "add" || ui_sel == "add:vita"; g_open_vita_popup = ui_sel == "add:vita";
		if (const char *f = getenv("ATIV_SHOT_SCAN")) { scan_load(f); g_add_kind = 0; g_scan_path = "/Volumes/Vita/ux0"; }
		g_drawer = ui_sel == "log";
		g_sac_open = ui_sel.rfind("sac", 0) == 0; g_sac_game = "PCSE00640"; g_sac_rebuilt = ui_sel == "sac:again";
		g_settings_open = ui_sel.rfind("settings", 0) == 0; if (g_settings_open && ui_sel.size() > 9) g_settings_tab = atoi(ui_sel.c_str() + 9);
		if (ui_sel.rfind("game:", 0) == 0) g_game_settings = ui_sel.substr(5);
		if (ui_sel.rfind("name:", 0) == 0) g_name_game = ui_sel.substr(5);
		if (getenv("ATIV_SHOT_NOFW") && *getenv("ATIV_SHOT_NOFW")) { g_firmware = false; g_firmware_version.clear(); }
		if (const char *u = getenv("ATIV_SHOT_UPDATE")) { g_update.tag = u; g_update.page = "https://example.invalid/"; }   /* (the notice, without asking anyone) */
		files_check();   /* (an install's own check, as at start: what a damaged copy shows) */
		int r = shot(win, shot_path, sw, sh);
		SDL_WaitForGPUIdle(g_gpu);
		ImGui_ImplSDL3_Shutdown(); ImGui_ImplSDLGPU3_Shutdown(); ImGui::DestroyContext();
		SDL_DestroyGPUDevice(g_gpu); SDL_DestroyWindow(win); SDL_Quit();
		return r;
	}

	update_check_start(); files_check_start();
	bool quit = false;
	while (!quit) {
		SDL_Event e;
		while (SDL_PollEvent(&e)) {
			ImGui_ImplSDL3_ProcessEvent(&e);
			if (e.type == SDL_EVENT_QUIT || (e.type == SDL_EVENT_WINDOW_CLOSE_REQUESTED && e.window.windowID == SDL_GetWindowID(win))) quit = true;
		}
		if (SDL_GetWindowFlags(win) & SDL_WINDOW_MINIMIZED) { SDL_Delay(50); continue; }
		pick_poll();
		{	/* a touch screen in use: bigger targets (finger-sized frame padding), until a mouse moves again */
			static bool touch; static ImVec2 pad = ImGui::GetStyle().FramePadding;
			bool t = io.MouseSource == ImGuiMouseSource_TouchScreen;   /* (the SDL backend tags touch-driven pointer events) */
			if (t != touch) { touch = t; ImGui::GetStyle().FramePadding = t ? ImVec2(pad.x * 1.4f, pad.y * 1.8f) : pad; }
		}
		static Uint64 last_scan;
		if (g_task.running && SDL_GetTicks() - last_scan > 1500) { library_scan(); last_scan = SDL_GetTicks(); }   /* (a long add: its card follows) */
		if (g_refresh.exchange(false)) {
			if (g_task.kind == "play") { SDL_RestoreWindow(win); SDL_RaiseWindow(win); }   /* (the game closed: back to the library) */
			library_scan();
			if (g_task.kind == "scan" && g_task.ok) scan_load(scan_file());
			if (g_task.kind == "report" && g_task.ok) open_folder(g_dump + "/reports");
			if (g_task.kind == "play") {   /* Windows refused the game (vitarecomp's SAC_BLOCKED line): the Smart App Control dialog */
				bool blocked;
				{ std::lock_guard<std::mutex> l(g_log_lock); blocked = !g_task.ok && g_log.find("Smart App Control is on", g_task.log_from) != std::string::npos; }
				if (blocked && g_sac_game != g_task.game) g_sac_rebuilt = false;   /* (another game: its first refusal) */
				if (blocked) { g_sac_game = g_task.game; g_sac_open = true; } else g_sac_rebuilt = false;
			}
		}
		ImGui_ImplSDLGPU3_NewFrame(); ImGui_ImplSDL3_NewFrame(); ImGui::NewFrame();
		hub_ui(win);
		ImGui::Render();
		ImDrawData *dd = ImGui::GetDrawData();
		SDL_GPUCommandBuffer *cmd = SDL_AcquireGPUCommandBuffer(g_gpu);
		SDL_GPUTexture *swap = nullptr;
		if (cmd && SDL_WaitAndAcquireGPUSwapchainTexture(cmd, win, &swap, nullptr, nullptr) && swap && dd->DisplaySize.x > 0) {
			ImGui_ImplSDLGPU3_PrepareDrawData(dd, cmd);
			SDL_GPUColorTargetInfo ti = {};
			ti.texture = swap; ti.clear_color = SDL_FColor{ui::bg.x, ui::bg.y, ui::bg.z, 1}; ti.load_op = SDL_GPU_LOADOP_CLEAR; ti.store_op = SDL_GPU_STOREOP_STORE;
			SDL_GPURenderPass *rp = SDL_BeginGPURenderPass(cmd, &ti, 1, nullptr);
			ImGui_ImplSDLGPU3_RenderDrawData(dd, cmd, rp);
			SDL_EndGPURenderPass(rp);
		}
		if (cmd) SDL_SubmitGPUCommandBuffer(cmd);
	}
	task_cancel();
	if (g_task.reader.joinable()) g_task.reader.join();
	SDL_WaitForGPUIdle(g_gpu);
	for (auto &kv : g_tex) if (kv.second.t) SDL_ReleaseGPUTexture(g_gpu, kv.second.t);
	ImGui_ImplSDL3_Shutdown(); ImGui_ImplSDLGPU3_Shutdown(); ImGui::DestroyContext();
	SDL_ReleaseWindowFromGPUDevice(g_gpu, win); SDL_DestroyGPUDevice(g_gpu); SDL_DestroyWindow(win); SDL_Quit();
	return 0;
}
