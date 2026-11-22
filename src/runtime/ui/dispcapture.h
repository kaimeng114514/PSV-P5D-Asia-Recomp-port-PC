/* M1653: DXGI Desktop Duplication based display-rate measurement (see dispcapture.c). */
#ifndef RECOMP_DISPCAPTURE_H
#define RECOMP_DISPCAPTURE_H
#ifdef __cplusplus
extern "C" {
#endif
int dispcap_start(void *hwnd);   /* begin measuring the output that contains hwnd; 0 ok */
int dispcap_fps(void);           /* measured distinct pictures per second; 0 = no measurement */
#ifdef __cplusplus
}
#endif
#endif
