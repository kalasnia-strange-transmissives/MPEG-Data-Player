/*
 * hexplayer.c -- a basic video player with a hex/binary byte-histogram
 * and real frame file-offset display, plus JPEG snapshot export and
 * a text-report export describing the frame's raw file data.
 *
 * ARCHITECTURE:
 *   - ffmpeg extracts every frame to numbered PNGs in a temp folder
 *     (simple, discrete, matches this project's established pattern).
 *   - ffprobe dumps per-packet info (pts_time, size, pos, flags) to a
 *     CSV file -- `pos` is the frame's exact BYTE OFFSET in the
 *     original file. This is real, documented ffprobe behavior.
 *   - The histogram is built from the RAW COMPRESSED BYTES of the
 *     current frame's packet, read directly from the original file
 *     at [pos, pos+size], NOT from decoded pixel values. Axis labels
 *     and per-bucket readouts are hex/binary, per the request.
 *
 * REQUIREMENTS (same as prior builds in this project):
 *   stb_image_write.h  (github.com/nothings/stb) -- only for JPEG snapshot
 *   ffmpeg.exe + ffprobe.exe        (gyan.dev/ffmpeg/builds)
 *
 * COMPILE:
 *   gcc hexplayer.c -o HexPlayer.exe -mwindows -lcomdlg32 -lgdi32 -lcomctl32 -lwinmm -static
 *
 * UNVERIFIED against a real Windows build -- no Windows machine or
 * cross-compiler available to test this. Careful first draft, not a
 * guaranteed first-compile success.
 */

#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <commdlg.h>
#include <commctrl.h>
#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>
#include <string.h>
#include <stdlib.h>
#include <math.h>
#include <mmsystem.h>

#define STB_IMAGE_WRITE_IMPLEMENTATION
#include "stb_image_write.h"

/* ---------------------------------------------------------------------
 * Data structures
 * ------------------------------------------------------------------- */

typedef struct {
    double   pts_time;
    long long size;
    long long pos;       /* real file byte offset, from ffprobe */
    int      is_keyframe;
} PacketInfo;

typedef struct {
    char        inputPath[MAX_PATH];
    char        tempDir[MAX_PATH];
    PacketInfo *packets;
    int         packetCount;
    int         currentFrame;
    unsigned char *pixels;   /* currently decoded frame, RGB */
    int         width, height;
    BOOL        playing;
    unsigned long histogram[256];       /* compressed packet bytes (existing) */
    unsigned long r_hist[256];          /* decoded RGB/luma channels (new) */
    unsigned long g_hist[256];
    unsigned long b_hist[256];
    unsigned long y_hist[256];
    char        pixFmt[32];
    char        colorSpace[32];
    char        colorRange[32];
    int         streamWidth, streamHeight;
    HANDLE      hExtractionProcess;  /* non-blocking ffmpeg PNG extraction */
    int         highestAvailableFrame; /* -1 = none yet */
    BOOL        extractionComplete;
    BOOL        firstFrameShown;
} AppState;

static AppState g_state = {0};

#define ID_BTN_OPEN      2001
#define ID_BTN_PLAYPAUSE 2002
#define ID_BTN_PREV      2003
#define ID_BTN_NEXT      2004
#define ID_BTN_SNAPSHOT  2005
#define ID_BTN_EXPORTINFO 2006
#define ID_BTN_DUMPRAW    2007
#define ID_TIMER_PLAYBACK 1
#define ID_TIMER_POLL_EXTRACTION 2
#define WM_EXTRACTION_DONE (WM_APP + 1)

/*
 * Worker-thread extraction. The thread touches ONLY local variables
 * and the filesystem (via ffmpeg/ffprobe) -- it never writes to the
 * global AppState directly. Results are packaged into a heap struct
 * and handed back to the main thread via PostMessage, where g_state
 * is updated safely on the UI thread alone. This avoids any data race
 * between the extraction work and WM_PAINT reading g_state concurrently.
 */
typedef struct {
    BOOL        success;
    char        errorMsg[256];
    PacketInfo *packets;
    int         packetCount;
    char        pixFmt[32];
    char        colorSpace[32];
    char        colorRange[32];
    int         streamWidth, streamHeight;
} ExtractionResult;

typedef struct {
    HWND hwnd;
    char inputPath[MAX_PATH];
    char tempDir[MAX_PATH];
} ExtractionThreadInput;

#define VIDEO_AREA_X 10
#define VIDEO_AREA_Y 50
#define VIDEO_AREA_W 480
#define VIDEO_AREA_H 270

#define HIST_AREA_X 10
#define HIST_AREA_Y 330
#define HIST_AREA_W 480
#define HIST_AREA_H 140

static HWND g_hStatus;
static HWND g_hAddrInfo;
static HWND g_hDataTable;
static HFONT g_hMonoFont;
static RECT  g_dynRect = { 0, 45, 800, 625 };   /* only this region is ever invalidated */
#define REDRAW(h) InvalidateRect((h), &g_dynRect, FALSE)
static BOOL  g_frameValid = FALSE;
static size_t g_pixCap = 0;
static int   g_stride = 0;

/* ---------------------------------------------------------------------
 * Process helpers (same pattern as earlier builds in this project)
 * ------------------------------------------------------------------- */

static BOOL RunHiddenRedirected(const char *exeName, const char *args, const char *stdoutFile)
{
    STARTUPINFOA si;
    PROCESS_INFORMATION pi;
    char cmdline[4096];

    SECURITY_ATTRIBUTES sa;
    sa.nLength = sizeof(sa);
    sa.bInheritHandle = TRUE;
    sa.lpSecurityDescriptor = NULL;

    HANDLE hOut = NULL;
    if (stdoutFile) {
        hOut = CreateFileA(stdoutFile, GENERIC_WRITE, FILE_SHARE_READ, &sa,
                            CREATE_ALWAYS, FILE_ATTRIBUTE_NORMAL, NULL);
        if (hOut == INVALID_HANDLE_VALUE) {
            return FALSE;
        }
    }

    ZeroMemory(&si, sizeof(si));
    si.cb = sizeof(si);
    if (stdoutFile) {
        si.dwFlags |= STARTF_USESTDHANDLES;
        si.hStdOutput = hOut;
        si.hStdError = hOut;
    }
    ZeroMemory(&pi, sizeof(pi));

    snprintf(cmdline, sizeof(cmdline), "%s %s", exeName, args);

    BOOL ok = CreateProcessA(NULL, cmdline, NULL, NULL, TRUE,
                              CREATE_NO_WINDOW, NULL, NULL, &si, &pi);

    if (hOut) CloseHandle(hOut);

    if (!ok) {
        return FALSE;
    }

    WaitForSingleObject(pi.hProcess, INFINITE);
    DWORD exitCode = 0;
    GetExitCodeProcess(pi.hProcess, &exitCode);
    CloseHandle(pi.hProcess);
    CloseHandle(pi.hThread);

    return (exitCode == 0);
}

static void SetStatus(const char *msg)
{
    static char last[256];
    if (strcmp(last, msg) == 0) return;
    strncpy(last, msg, sizeof(last) - 1);
    SetWindowTextA(g_hStatus, msg);
}

/* ---------------------------------------------------------------------
 * Frame extraction + packet info parsing
 * ------------------------------------------------------------------- */

/*
 * Launches ffmpeg frame extraction WITHOUT waiting for it to finish.
 * ffmpeg writes frame_00001.png, frame_00002.png, etc. to disk
 * progressively as it decodes -- this function just starts that
 * process and hands back its handle so the caller can poll for
 * individual files appearing, rather than blocking until the whole
 * video is done. This is the actual mechanism behind "live" display.
 */
static BOOL LaunchFrameExtractionAsync(const char *inputPath, const char *tempDir, HANDLE *outProcessHandle)
{
    char cmdline[1024];
    snprintf(cmdline, sizeof(cmdline), "ffmpeg.exe -y -i \"%s\" -nostdin -vsync 0 -pix_fmt rgb24 \"%s\\frame_%%05d.ppm\"",
             inputPath, tempDir);

    STARTUPINFOA si;
    PROCESS_INFORMATION pi;
    ZeroMemory(&si, sizeof(si));
    si.cb = sizeof(si);
    ZeroMemory(&pi, sizeof(pi));

    BOOL ok = CreateProcessA(NULL, cmdline, NULL, NULL, FALSE,
                              CREATE_NO_WINDOW, NULL, NULL, &si, &pi);
    if (!ok) {
        return FALSE;
    }

    CloseHandle(pi.hThread); /* don't need the thread handle, only the process */
    *outProcessHandle = pi.hProcess;
    return TRUE;
}

/*
 * Dumps per-packet info to a CSV file. Fields requested explicitly
 * (pts_time,size,pos,flags) so column order is stable and known,
 * rather than relying on ffprobe's default field set/order.
 */
static BOOL DumpPacketInfo(const char *inputPath, const char *csvPath)
{
    char args[1024];
    snprintf(args, sizeof(args),
             "-v quiet -select_streams v -show_entries packet=pts_time,size,pos,flags -of csv=p=0 \"%s\"",
             inputPath);
    return RunHiddenRedirected("ffprobe.exe", args, csvPath);
}

/*
 * Splits one CSV line (no quoted-field handling needed -- ffprobe's
 * csv=p=0 output for these specific fields never contains embedded
 * commas) into up to maxFields tokens. Returns the number of fields
 * found. Trailing newline is stripped from the last field.
 */
static int SplitCsvLine(char *line, char *fields[], int maxFields)
{
    int count = 0;
    char *tok = line;
    while (count < maxFields) {
        fields[count++] = tok;
        char *comma = strchr(tok, ',');
        if (!comma) break;
        *comma = '\0';
        tok = comma + 1;
    }
    /* Strip trailing \r\n from the final field. */
    if (count > 0) {
        char *last = fields[count - 1];
        size_t len = strlen(last);
        while (len > 0 && (last[len - 1] == '\n' || last[len - 1] == '\r')) {
            last[--len] = '\0';
        }
    }
    return count;
}

/*
 * Parses one field as a double, tolerating ffprobe's "N/A" (common on
 * packet-level pts_time for many older/simpler formats). Returns TRUE
 * if a real number was found; on "N/A"/garbage, returns FALSE and
 * sets *out to 0.0 -- the CALLER decides whether that's fatal for
 * this field (pts_time: not fatal, just imprecise) or not (pos: fatal,
 * a packet with no real file address isn't usable here).
 */
static BOOL ParseDoubleField(const char *field, double *out)
{
    char *endptr = NULL;
    double v = strtod(field, &endptr);
    if (endptr == field) { *out = 0.0; return FALSE; } /* no digits parsed at all */
    *out = v;
    return TRUE;
}

static BOOL ParseInt64Field(const char *field, long long *out)
{
    char *endptr = NULL;
    long long v = strtoll(field, &endptr, 10);
    if (endptr == field) { *out = 0; return FALSE; }
    *out = v;
    return TRUE;
}

static BOOL ParsePacketCSV(const char *csvPath, PacketInfo **outPackets, int *outCount)
{
    FILE *f = fopen(csvPath, "r");
    if (!f) return FALSE;

    int capacity = 256;
    int count = 0;
    PacketInfo *packets = (PacketInfo *)malloc(sizeof(PacketInfo) * capacity);
    if (!packets) { fclose(f); return FALSE; }

    char line[512];
    while (fgets(line, sizeof(line), f)) {
        /* Expected CSV order: pts_time,size,pos,flags */
        char *fields[4];
        int fieldCount = SplitCsvLine(line, fields, 4);
        if (fieldCount < 3) {
            continue; /* genuinely malformed line (not just N/A), skip */
        }

        double pts_time = 0.0;
        ParseDoubleField(fields[0], &pts_time); /* N/A here is tolerated, not fatal */

        long long size = 0, pos = 0;
        BOOL sizeOk = ParseInt64Field(fields[1], &size);
        BOOL posOk  = ParseInt64Field(fields[2], &pos);
        if (!sizeOk || !posOk) {
            /* A packet with no real size/address isn't usable for
             * this tool's whole purpose -- skip it, but this should
             * be rare; a genuine video file has real packet sizes
             * and positions for every packet. */
            continue;
        }

        const char *flags = (fieldCount >= 4) ? fields[3] : "";

        if (count >= capacity) {
            capacity *= 2;
            PacketInfo *grown = (PacketInfo *)realloc(packets, sizeof(PacketInfo) * capacity);
            if (!grown) { free(packets); fclose(f); return FALSE; }
            packets = grown;
        }

        packets[count].pts_time = pts_time;
        packets[count].size = size;
        packets[count].pos = pos;
        packets[count].is_keyframe = (strchr(flags, 'K') != NULL);
        count++;
    }

    fclose(f);
    *outPackets = packets;
    *outCount = count;
    return TRUE;
}

/* ---------------------------------------------------------------------
 * Stream-level pixel format / color space detection (real ffprobe
 * fields -- these describe how RAW decoded frames are structured,
 * distinct from the compressed packet bytes the histogram reads).
 * ------------------------------------------------------------------- */

static BOOL GetStreamInfo(const char *inputPath, const char *csvPath)
{
    char args[1024];
    snprintf(args, sizeof(args),
        "-v quiet -select_streams v:0 -show_entries stream=pix_fmt,color_space,color_range,width,height -of csv=p=0 \"%s\"",
        inputPath);
    return RunHiddenRedirected("ffprobe.exe", args, csvPath);
}

static BOOL ParseStreamInfoCSV(const char *csvPath, AppState *state)
{
    FILE *f = fopen(csvPath, "r");
    if (!f) return FALSE;

    char line[256];
    if (!fgets(line, sizeof(line), f)) { fclose(f); return FALSE; }
    fclose(f);

    /* Expected order: pix_fmt,color_space,color_range,width,height
     * Any field ffprobe doesn't know reports as the literal string
     * "unknown" or "N/A" -- captured as-is, not treated as an error. */
    char pixFmt[32] = "unknown", colorSpace[32] = "unknown", colorRange[32] = "unknown";
    int w = 0, h = 0;
    sscanf(line, "%31[^,],%31[^,],%31[^,],%d,%d", pixFmt, colorSpace, colorRange, &w, &h);

    strncpy(state->pixFmt, pixFmt, sizeof(state->pixFmt) - 1);
    strncpy(state->colorSpace, colorSpace, sizeof(state->colorSpace) - 1);
    strncpy(state->colorRange, colorRange, sizeof(state->colorRange) - 1);
    state->streamWidth = w;
    state->streamHeight = h;
    return TRUE;
}

/*
 * Computes the deterministic byte layout of a RAW decoded frame for
 * the handful of basic formats covered here. This layout is REAL and
 * exact for an actual raw dump -- it is NOT applicable to compressed
 * packet bytes, which have no fixed per-pixel byte offset at all.
 *
 * Returns TRUE and fills the offsets if the format is a known one;
 * FALSE (with a plain message) if not -- this function does not guess
 * at formats it doesn't recognize.
 */
typedef struct {
    BOOL   isPlanar;
    long long yOffset, ySize;
    long long uOffset, uSize;
    long long vOffset, vSize;
    long long totalSize;
    char   description[256];
} PlaneLayout;

static BOOL ComputePlaneLayout(const char *pixFmt, int w, int h, PlaneLayout *out)
{
    memset(out, 0, sizeof(*out));

    if (strcmp(pixFmt, "yuv420p") == 0 || strcmp(pixFmt, "yuvj420p") == 0) {
        out->isPlanar = TRUE;
        out->yOffset = 0; out->ySize = (long long)w * h;
        out->uOffset = out->ySize; out->uSize = (long long)(w / 2) * (h / 2);
        out->vOffset = out->uOffset + out->uSize; out->vSize = out->uSize;
        out->totalSize = out->vOffset + out->vSize;
        snprintf(out->description, sizeof(out->description),
            "Planar YUV 4:2:0. Y plane first (full resolution), then U, "
            "then V, each at quarter resolution (half width, half height).");
        return TRUE;
    }
    if (strcmp(pixFmt, "yuv422p") == 0) {
        out->isPlanar = TRUE;
        out->yOffset = 0; out->ySize = (long long)w * h;
        out->uOffset = out->ySize; out->uSize = (long long)(w / 2) * h;
        out->vOffset = out->uOffset + out->uSize; out->vSize = out->uSize;
        out->totalSize = out->vOffset + out->vSize;
        snprintf(out->description, sizeof(out->description),
            "Planar YUV 4:2:2. Y plane first (full resolution), then U, "
            "then V, each half-width but full height.");
        return TRUE;
    }
    if (strcmp(pixFmt, "yuv444p") == 0) {
        out->isPlanar = TRUE;
        out->yOffset = 0; out->ySize = (long long)w * h;
        out->uOffset = out->ySize; out->uSize = (long long)w * h;
        out->vOffset = out->uOffset + out->uSize; out->vSize = out->uSize;
        out->totalSize = out->vOffset + out->vSize;
        snprintf(out->description, sizeof(out->description),
            "Planar YUV 4:4:4, no subsampling. Y, U, V planes are all "
            "identical size (full resolution).");
        return TRUE;
    }
    if (strcmp(pixFmt, "rgb24") == 0 || strcmp(pixFmt, "bgr24") == 0) {
        out->isPlanar = FALSE;
        out->totalSize = (long long)w * h * 3;
        snprintf(out->description, sizeof(out->description),
            "Packed %s, 3 bytes per pixel, no separate planes: "
            "byte 0/1/2 = pixel(0,0)'s %s, byte 3/4/5 = pixel(1,0), "
            "repeating left-to-right then top-to-bottom.",
            pixFmt, strcmp(pixFmt, "rgb24") == 0 ? "R/G/B" : "B/G/R");
        return TRUE;
    }

    snprintf(out->description, sizeof(out->description),
        "Pixel format \"%s\" is not one of the basic formats this tool "
        "computes layout for (yuv420p/yuv422p/yuv444p/rgb24/bgr24). "
        "No offsets computed -- verify manually against FFmpeg's own "
        "pixel format documentation before trusting a layout for it.",
        pixFmt);
    return FALSE;
}

/* Dumps the current frame as RAW, uncompressed pixel data in the
 * stream's own reported pix_fmt -- this is the file that genuinely
 * has a fixed, correlatable byte-to-pixel layout, unlike the
 * compressed original. */
static BOOL DumpRawFrame(const char *inputPath, double ptsTime, const char *pixFmt, const char *outPath)
{
    char args[1024];
    snprintf(args, sizeof(args),
        "-y -ss %.3f -i \"%s\" -pix_fmt %s -frames:v 1 -f rawvideo \"%s\"",
        ptsTime, inputPath, pixFmt, outPath);
    return RunHiddenRedirected("ffmpeg.exe", args, NULL);
}

/* ---------------------------------------------------------------------
 * Histogram: built from RAW FILE BYTES of the current frame's packet,
 * not from decoded pixels.
 * ------------------------------------------------------------------- */

static BOOL ComputeHistogramForFrame(const char *inputPath, const PacketInfo *pkt,
                                      unsigned long histogram[256])
{
    memset(histogram, 0, sizeof(unsigned long) * 256);

    FILE *f = fopen(inputPath, "rb");
    if (!f) return FALSE;

    if (_fseeki64(f, pkt->pos, SEEK_SET) != 0) {
        fclose(f);
        return FALSE;
    }

    unsigned char buf[4096];
    long long remaining = pkt->size;
    while (remaining > 0) {
        size_t toRead = (remaining < (long long)sizeof(buf)) ? (size_t)remaining : sizeof(buf);
        size_t got = fread(buf, 1, toRead, f);
        if (got == 0) break;
        for (size_t i = 0; i < got; i++) {
            histogram[buf[i]]++;
        }
        remaining -= (long long)got;
    }

    fclose(f);
    return TRUE;
}

/* Binary string helper -- "01001011" style, for the per-bucket readout. */
static void ByteToBinaryString(unsigned char b, char out[9])
{
    for (int i = 0; i < 8; i++) {
        out[i] = (b & (0x80 >> i)) ? '1' : '0';
    }
    out[8] = '\0';
}

/* ---------------------------------------------------------------------
 * Rendering: ONE double-buffered paint. Fixed layout, values overwritten
 * in place every frame -- no edit control, no log, no erase flicker.
 * ------------------------------------------------------------------- */

#define BB_W 800
#define BB_H 720
static HDC     g_memDC;
static HBITMAP g_memBmp;
static int     g_cw = 8;                 /* monospace char width */
static int     g_modeValue;
static unsigned long g_modeCount;
static unsigned char *g_scratch;
static size_t  g_scratchCap;

static double NowMs(void)
{
    LARGE_INTEGER f, c;
    QueryPerformanceFrequency(&f);
    QueryPerformanceCounter(&c);
    return (double)c.QuadPart * 1000.0 / (double)f.QuadPart;
}
static double g_playClockStart, g_playPtsStart;
static void StartPlaybackClock(void)
{
    g_playClockStart = NowMs();
    g_playPtsStart = (g_state.packetCount > 0 && g_state.currentFrame < g_state.packetCount)
        ? g_state.packets[g_state.currentFrame].pts_time * 1000.0 : 0.0;
}

static int ComparePktPts(const void *a, const void *b)
{
    double x = ((const PacketInfo *)a)->pts_time, y = ((const PacketInfo *)b)->pts_time;
    return (x > y) - (x < y);
}
/* ffprobe lists packets in DECODE order; frames are written in DISPLAY
 * order. Sorting by pts makes packets[i] match frame_i. */
static void SortPackets(PacketInfo *p, int n)
{
    int any = 0;
    for (int i = 0; i < n; i++) if (p[i].pts_time > 0.0) { any = 1; break; }
    if (!any) { for (int i = 0; i < n; i++) p[i].pts_time = i / 30.0; return; }
    qsort(p, (size_t)n, sizeof(PacketInfo), ComparePktPts);
}

static BOOL FrameFileExists(int oneBased)
{
    char path[MAX_PATH];
    snprintf(path, sizeof(path), "%s\\frame_%05d.ppm", g_state.tempDir, oneBased);
    return GetFileAttributesA(path) != INVALID_FILE_ATTRIBUTES;
}

/* Loads a binary PPM into g_state.pixels as top-down BGR with DWORD-padded
 * rows (what StretchDIBits wants). Returns FALSE if the file is missing or
 * still being written. */
static BOOL LoadFramePPM(const char *path, int *outW, int *outH)
{
    FILE *f = fopen(path, "rb");
    if (!f) return FALSE;
    _fseeki64(f, 0, SEEK_END);
    long long sz = _ftelli64(f);
    _fseeki64(f, 0, SEEK_SET);
    if (sz < 16) { fclose(f); return FALSE; }
    if ((size_t)sz > g_scratchCap) {
        free(g_scratch);
        g_scratch = (unsigned char *)malloc((size_t)sz);
        g_scratchCap = g_scratch ? (size_t)sz : 0;
        if (!g_scratch) { fclose(f); return FALSE; }
    }
    size_t got = fread(g_scratch, 1, (size_t)sz, f);
    fclose(f);
    if (got != (size_t)sz) return FALSE;

    const unsigned char *p = g_scratch, *end = g_scratch + sz;
    if (p[0] != 'P' || p[1] != '6') return FALSE;
    p += 2;
    int vals[3];
    for (int k = 0; k < 3; k++) {
        while (p < end && (*p == ' ' || *p == '\n' || *p == '\r' || *p == '\t' || *p == '#')) {
            if (*p == '#') { while (p < end && *p != '\n') p++; } else p++;
        }
        if (p >= end || *p < '0' || *p > '9') return FALSE;
        int v = 0;
        while (p < end && *p >= '0' && *p <= '9') { v = v * 10 + (*p - '0'); p++; }
        vals[k] = v;
    }
    p++; /* single whitespace after maxval */
    int w = vals[0], h = vals[1];
    if (w <= 0 || h <= 0 || vals[2] != 255) return FALSE;
    if ((long long)(end - p) < (long long)w * h * 3) return FALSE; /* partial write */

    int stride = (w * 3 + 3) & ~3;
    size_t need = (size_t)stride * h;
    if (need > g_pixCap) {
        free(g_state.pixels);
        g_state.pixels = (unsigned char *)malloc(need);
        g_pixCap = g_state.pixels ? need : 0;
        if (!g_state.pixels) return FALSE;
    }
    for (int y = 0; y < h; y++) {
        const unsigned char *src = p + (size_t)y * w * 3;
        unsigned char *dst = g_state.pixels + (size_t)y * stride;
        for (int x = 0; x < w; x++) {
            dst[x * 3 + 0] = src[x * 3 + 2];
            dst[x * 3 + 1] = src[x * 3 + 1];
            dst[x * 3 + 2] = src[x * 3 + 0];
        }
    }
    g_stride = stride;
    *outW = w; *outH = h;
    return TRUE;
}

static BOOL LoadFrame(int index)
{
    if (index < 0 || index >= g_state.packetCount) return FALSE;

    char path[MAX_PATH];
    snprintf(path, sizeof(path), "%s\\frame_%05d.ppm", g_state.tempDir, index + 1);

    int w, h;
    if (!LoadFramePPM(path, &w, &h)) return FALSE;

    g_state.width = w;
    g_state.height = h;
    g_state.currentFrame = index;
    g_frameValid = TRUE;

    ComputeHistogramForFrame(g_state.inputPath, &g_state.packets[index], g_state.histogram);
    g_modeValue = 0; g_modeCount = 0;
    for (int i = 0; i < 256; i++) {
        if (g_state.histogram[i] > g_modeCount) { g_modeCount = g_state.histogram[i]; g_modeValue = i; }
    }
    return TRUE;
}

static void InfoRow(HDC dc, int x, int *y, const char *label, const char *val)
{
    TextOutA(dc, x, *y, label, (int)strlen(label));
    TextOutA(dc, x + 10 * g_cw, *y, val, (int)strlen(val));
    *y += 18;
}

static void PaintAll(HDC hdc, const RECT *clip)
{
    if (!g_memDC) {
        g_memDC = CreateCompatibleDC(hdc);
        g_memBmp = CreateCompatibleBitmap(hdc, BB_W, BB_H);
        SelectObject(g_memDC, g_memBmp);
    }
    HDC dc = g_memDC;
    RECT all = { 0, 0, BB_W, BB_H };
    FillRect(dc, &all, GetSysColorBrush(COLOR_WINDOW));

    HGDIOBJ oldFont = SelectObject(dc, g_hMonoFont);
    TEXTMETRICA tm;
    if (GetTextMetricsA(dc, &tm)) g_cw = tm.tmAveCharWidth;
    SetBkMode(dc, TRANSPARENT);
    SetTextColor(dc, RGB(0, 0, 0));

    /* ---- video ---- */
    RECT vr = { VIDEO_AREA_X, VIDEO_AREA_Y, VIDEO_AREA_X + VIDEO_AREA_W, VIDEO_AREA_Y + VIDEO_AREA_H };
    FillRect(dc, &vr, (HBRUSH)GetStockObject(BLACK_BRUSH));
    BOOL have = g_frameValid && g_state.packetCount > 0 && g_state.currentFrame < g_state.packetCount;
    if (have) {
        int w = g_state.width, h = g_state.height;
        int dw = VIDEO_AREA_W, dh = (int)((long long)dw * h / w);
        if (dh > VIDEO_AREA_H) { dh = VIDEO_AREA_H; dw = (int)((long long)dh * w / h); }
        int dx = VIDEO_AREA_X + (VIDEO_AREA_W - dw) / 2;
        int dy = VIDEO_AREA_Y + (VIDEO_AREA_H - dh) / 2;
        BITMAPINFO bmi;
        ZeroMemory(&bmi, sizeof(bmi));
        bmi.bmiHeader.biSize = sizeof(BITMAPINFOHEADER);
        bmi.bmiHeader.biWidth = w;
        bmi.bmiHeader.biHeight = -h;
        bmi.bmiHeader.biPlanes = 1;
        bmi.bmiHeader.biBitCount = 24;
        bmi.bmiHeader.biCompression = BI_RGB;
        SetStretchBltMode(dc, COLORONCOLOR);
        StretchDIBits(dc, dx, dy, dw, dh, 0, 0, w, h, g_state.pixels, &bmi, DIB_RGB_COLORS, SRCCOPY);
    }

    /* ---- fixed info panel (right of video) ---- */
    int px = VIDEO_AREA_X + VIDEO_AREA_W + 14, py = VIDEO_AREA_Y;
    TextOutA(dc, px, py, "FRAME INFO", 10); py += 22;
    char v[96];
    if (have) {
        PacketInfo *pkt = &g_state.packets[g_state.currentFrame];
        char bin[9];
        snprintf(v, sizeof(v), "%d / %d", g_state.currentFrame + 1, g_state.packetCount); InfoRow(dc, px, &py, "Frame", v);
        snprintf(v, sizeof(v), "%.3f s", pkt->pts_time);               InfoRow(dc, px, &py, "PTS", v);
        InfoRow(dc, px, &py, "Keyframe", pkt->is_keyframe ? "Yes" : "No");
        snprintf(v, sizeof(v), "0x%08llX", (unsigned long long)pkt->pos); InfoRow(dc, px, &py, "Offset", v);
        snprintf(v, sizeof(v), "%lld", (long long)pkt->pos);           InfoRow(dc, px, &py, "Offset dec", v);
        snprintf(v, sizeof(v), "%lld bytes", (long long)pkt->size);    InfoRow(dc, px, &py, "Pkt size", v);
        snprintf(v, sizeof(v), "%d x %d", g_state.width, g_state.height); InfoRow(dc, px, &py, "Decoded", v);
        InfoRow(dc, px, &py, "PixFmt", g_state.pixFmt);
        InfoRow(dc, px, &py, "ColorSp", g_state.colorSpace);
        InfoRow(dc, px, &py, "Range", g_state.colorRange);
        py += 6;
        TextOutA(dc, px, py, "TOP PACKET BYTE", 15); py += 20;
        ByteToBinaryString((unsigned char)g_modeValue, bin);
        snprintf(v, sizeof(v), "0x%02X", g_modeValue);                 InfoRow(dc, px, &py, "Hex", v);
        InfoRow(dc, px, &py, "Binary", bin);
        snprintf(v, sizeof(v), "%lu", g_modeCount);                    InfoRow(dc, px, &py, "Count", v);
    } else {
        TextOutA(dc, px, py, "No frame loaded.", 16);
    }
    RECT pr = { px - 6, VIDEO_AREA_Y - 4, 792, VIDEO_AREA_Y + VIDEO_AREA_H };
    FrameRect(dc, &pr, (HBRUSH)GetStockObject(GRAY_BRUSH));

    /* ---- fixed pixel table: same 12 sample points every frame ---- */
    int ty = 330;
    const char *title = "DECODED PIXEL SAMPLES (fixed 4x3 grid)  ADDR = byte offset in RGB24 raw dump, C = chroma magnitude";
    TextOutA(dc, 10, ty, title, (int)strlen(title)); ty += 20;
    char line[160];
    snprintf(line, sizeof(line), "%-25s | %-13s | %-13s | %-13s | %-13s",
             " #  (  X ,  Y )  ADDRESS", "R  HX  BINARY", "G  HX  BINARY", "B  HX  BINARY", "C  HX  BINARY");
    TextOutA(dc, 10, ty, line, (int)strlen(line)); ty += 17;
    memset(line, '-', 89); line[89] = 0;
    TextOutA(dc, 10, ty, line, 89); ty += 17;

    const double MAXC = sqrt(127.0 * 127.0 + 127.0 * 127.0);
    for (int j = 0; j < 3; j++) {
        for (int i = 0; i < 4; i++) {
            int n = j * 4 + i;
            if (have) {
                int x = (g_state.width * (2 * i + 1)) / 8;
                int y = (g_state.height * (2 * j + 1)) / 6;
                const unsigned char *q = g_state.pixels + (size_t)y * g_stride + (size_t)x * 3;
                unsigned char b = q[0], g = q[1], r = q[2];
                long long addr = ((long long)y * g_state.width + x) * 3;
                double cb = -0.168736 * r - 0.331264 * g + 0.5 * b;
                double cr = 0.5 * r - 0.418688 * g - 0.081312 * b;
                unsigned char cm = (unsigned char)(sqrt(cb * cb + cr * cr) / MAXC * 255.0);
                char rb[9], gb[9], bb[9], cbn[9];
                ByteToBinaryString(r, rb); ByteToBinaryString(g, gb);
                ByteToBinaryString(b, bb); ByteToBinaryString(cm, cbn);
                snprintf(line, sizeof(line),
                    "%2d (%4d,%4d) 0x%08llX | R %02X %s | G %02X %s | B %02X %s | C %02X %s",
                    n + 1, x, y, (unsigned long long)addr, r, rb, g, gb, b, bb, cm, cbn);
            } else {
                snprintf(line, sizeof(line), "%2d (  --,  --) 0x--------", n + 1);
            }
            TextOutA(dc, 10, ty, line, (int)strlen(line));
            ty += 17;
        }
    }
    SelectObject(dc, oldFont);

    RECT c;
    if (IntersectRect(&c, clip, &all))
        BitBlt(hdc, c.left, c.top, c.right - c.left, c.bottom - c.top, dc, c.left, c.top, SRCCOPY);
}

/* ---------------------------------------------------------------------
 * Export functions
 * ------------------------------------------------------------------- */

static void ExportSnapshotJpeg(HWND hwnd)
{
    if (!g_frameValid) {
        SetStatus("No frame loaded to export.");
        return;
    }

    char filename[MAX_PATH] = {0};
    OPENFILENAMEA ofn;
    ZeroMemory(&ofn, sizeof(ofn));
    ofn.lStructSize = sizeof(ofn);
    ofn.hwndOwner = hwnd;
    ofn.lpstrFilter = "JPEG Image\0*.jpg\0";
    ofn.lpstrFile = filename;
    ofn.nMaxFile = MAX_PATH;
    ofn.lpstrDefExt = "jpg";
    ofn.Flags = OFN_OVERWRITEPROMPT;

    if (!GetSaveFileNameA(&ofn)) return;

    int sw = g_state.width, sh = g_state.height;
    unsigned char *rgb = (unsigned char *)malloc((size_t)sw * sh * 3);
    int wrote = 0;
    if (rgb) {
        for (int y = 0; y < sh; y++) {
            const unsigned char *src = g_state.pixels + (size_t)y * g_stride;
            unsigned char *dst = rgb + (size_t)y * sw * 3;
            for (int x = 0; x < sw; x++) {
                dst[x * 3 + 0] = src[x * 3 + 2];
                dst[x * 3 + 1] = src[x * 3 + 1];
                dst[x * 3 + 2] = src[x * 3 + 0];
            }
        }
        wrote = stbi_write_jpg(filename, sw, sh, 3, rgb, 95);
        free(rgb);
    }
    if (wrote) {
        SetStatus("Snapshot exported.");
    } else {
        SetStatus("ERROR: failed to write JPEG.");
    }
}

static void ExportRawFrameAndLayout(HWND hwnd)
{
    if (g_state.packetCount == 0) {
        SetStatus("No frame loaded.");
        return;
    }

    char baseName[MAX_PATH] = {0};
    OPENFILENAMEA ofn;
    ZeroMemory(&ofn, sizeof(ofn));
    ofn.lStructSize = sizeof(ofn);
    ofn.hwndOwner = hwnd;
    ofn.lpstrFilter = "Raw Frame Dump\0*.raw\0";
    ofn.lpstrFile = baseName;
    ofn.nMaxFile = MAX_PATH;
    ofn.lpstrDefExt = "raw";
    ofn.Flags = OFN_OVERWRITEPROMPT;

    if (!GetSaveFileNameA(&ofn)) return;

    PacketInfo *pkt = &g_state.packets[g_state.currentFrame];

    SetStatus("Dumping raw frame (this re-decodes via ffmpeg)...");
    if (!DumpRawFrame(g_state.inputPath, pkt->pts_time, g_state.pixFmt, baseName)) {
        SetStatus("ERROR: ffmpeg failed to produce raw frame dump.");
        return;
    }

    PlaneLayout layout;
    BOOL known = ComputePlaneLayout(g_state.pixFmt, g_state.streamWidth, g_state.streamHeight, &layout);

    char reportPath[MAX_PATH];
    snprintf(reportPath, sizeof(reportPath), "%s_layout.txt", baseName);

    FILE *out = fopen(reportPath, "w");
    if (!out) {
        SetStatus("Raw dump written, but failed to write layout report.");
        return;
    }

    fprintf(out, "HexPlayer Raw Frame Layout Report\r\n");
    fprintf(out, "===================================\r\n\r\n");
    fprintf(out, "IMPORTANT: this layout describes the RAW DUMP FILE\r\n");
    fprintf(out, "(%s), produced by re-decoding this frame. It does NOT\r\n", baseName);
    fprintf(out, "describe the original compressed video file's bytes --\r\n");
    fprintf(out, "compressed data has no fixed per-pixel byte offset.\r\n\r\n");

    fprintf(out, "Source frame  : #%d, PTS %.3fs\r\n", g_state.currentFrame + 1, pkt->pts_time);
    fprintf(out, "Pixel format  : %s\r\n", g_state.pixFmt);
    fprintf(out, "Color space   : %s\r\n", g_state.colorSpace);
    fprintf(out, "Color range   : %s\r\n", g_state.colorRange);
    fprintf(out, "Dimensions    : %d x %d\r\n\r\n", g_state.streamWidth, g_state.streamHeight);

    if (known) {
        fprintf(out, "%s\r\n\r\n", layout.description);
        fprintf(out, "Total raw file size: %" PRId64 " bytes\r\n\r\n", layout.totalSize);
        if (layout.isPlanar) {
            fprintf(out, "Y plane : offset 0x%06" PRIX64 " to 0x%06" PRIX64 "  (%" PRId64 " bytes)\r\n",
                    (unsigned long long)layout.yOffset,
                    (unsigned long long)(layout.yOffset + layout.ySize - 1), layout.ySize);
            fprintf(out, "U plane : offset 0x%06" PRIX64 " to 0x%06" PRIX64 "  (%" PRId64 " bytes)\r\n",
                    (unsigned long long)layout.uOffset,
                    (unsigned long long)(layout.uOffset + layout.uSize - 1), layout.uSize);
            fprintf(out, "V plane : offset 0x%06" PRIX64 " to 0x%06" PRIX64 "  (%" PRId64 " bytes)\r\n",
                    (unsigned long long)layout.vOffset,
                    (unsigned long long)(layout.vOffset + layout.vSize - 1), layout.vSize);
            fprintf(out, "\r\nOpen the .raw file in HxD and these exact offsets\r\n");
            fprintf(out, "will line up with the Y/U/V planes above.\r\n");
        } else {
            fprintf(out, "\r\nThis is a PACKED format (no separate plane offsets).\r\n");
            fprintf(out, "Byte 0 in HxD = first pixel's first channel byte, repeating\r\n");
            fprintf(out, "every 3 bytes across the row, left to right, top to bottom.\r\n");
        }
    } else {
        fprintf(out, "%s\r\n", layout.description);
    }

    fclose(out);
    SetStatus("Raw frame + layout report exported.");
}

static void ExportFrameInfoText(HWND hwnd)
{
    if (g_state.packetCount == 0) {
        SetStatus("No frame loaded to export info for.");
        return;
    }

    char filename[MAX_PATH] = {0};
    OPENFILENAMEA ofn;
    ZeroMemory(&ofn, sizeof(ofn));
    ofn.lStructSize = sizeof(ofn);
    ofn.hwndOwner = hwnd;
    ofn.lpstrFilter = "Text Document\0*.txt\0";
    ofn.lpstrFile = filename;
    ofn.nMaxFile = MAX_PATH;
    ofn.lpstrDefExt = "txt";
    ofn.Flags = OFN_OVERWRITEPROMPT;

    if (!GetSaveFileNameA(&ofn)) return;

    PacketInfo *pkt = &g_state.packets[g_state.currentFrame];

    FILE *out = fopen(filename, "w");
    if (!out) {
        SetStatus("ERROR: could not create text report.");
        return;
    }

    fprintf(out, "HexPlayer Frame Report\r\n");
    fprintf(out, "=======================\r\n\r\n");
    fprintf(out, "Source file   : %s\r\n", g_state.inputPath);
    fprintf(out, "Frame index   : %d of %d\r\n", g_state.currentFrame + 1, g_state.packetCount);
    fprintf(out, "PTS time      : %.3f seconds\r\n", pkt->pts_time);
    fprintf(out, "Keyframe      : %s\r\n", pkt->is_keyframe ? "Yes" : "No");
    fprintf(out, "File offset   : 0x%" PRIX64 " (%" PRId64 " decimal)\r\n", (unsigned long long)pkt->pos, pkt->pos);
    fprintf(out, "Packet size   : %" PRId64 " bytes\r\n\r\n", pkt->size);

    fprintf(out, "First 64 bytes of this frame's raw file data:\r\n");
    fprintf(out, "Offset    Hex                                              Binary (first 8 shown)\r\n");

    FILE *src = fopen(g_state.inputPath, "rb");
    if (src) {
        _fseeki64(src, pkt->pos, SEEK_SET);
        unsigned char buf[64];
        size_t got = fread(buf, 1, sizeof(buf), src);
        for (size_t i = 0; i < got; i += 8) {
            fprintf(out, "0x%06" PRIX64 "  ", (unsigned long long)(pkt->pos + (long long)i));
            for (size_t j = i; j < i + 8 && j < got; j++) {
                fprintf(out, "%02X ", buf[j]);
            }
            fprintf(out, "   ");
            if (i < got) {
                char bin[9];
                ByteToBinaryString(buf[i], bin);
                fprintf(out, "%s", bin);
            }
            fprintf(out, "\r\n");
        }
        fclose(src);
    }

    fprintf(out, "\r\nByte-value histogram summary (full frame, not just first 64 bytes):\r\n");
    for (int i = 0; i < 256; i++) {
        if (g_state.histogram[i] > 0) {
            char bin[9];
            ByteToBinaryString((unsigned char)i, bin);
            fprintf(out, "  0x%02X (%s): %lu occurrences\r\n", i, bin, g_state.histogram[i]);
        }
    }

    fclose(out);
    SetStatus("Frame info report exported.");
}

/* ---------------------------------------------------------------------
 * Background extraction thread -- this is what keeps the UI responsive
 * instead of freezing on the main thread for the duration of ffmpeg's
 * work.
 * ------------------------------------------------------------------- */

/*
 * Gathers METADATA ONLY (packet positions/sizes, stream pixel format).
 * Deliberately does NOT extract PNG frames here -- reading packet
 * headers and stream info is fast (no decoding happens), so this
 * finishes quickly and lets the UI start showing frame 1 as soon as
 * the separate, slower PNG extraction process produces it, rather
 * than waiting on everything together.
 */
static DWORD WINAPI ExtractionThreadProc(LPVOID param)
{
    ExtractionThreadInput *input = (ExtractionThreadInput *)param;
    ExtractionResult *result = (ExtractionResult *)calloc(1, sizeof(ExtractionResult));

    if (!result) {
        free(input);
        return 1;
    }

    char csvPath[MAX_PATH];
    snprintf(csvPath, sizeof(csvPath), "%s\\packets.csv", input->tempDir);

    if (!DumpPacketInfo(input->inputPath, csvPath)) {
        strncpy(result->errorMsg, "ffprobe failed to produce packet info.", sizeof(result->errorMsg) - 1);
        PostMessageA(input->hwnd, WM_EXTRACTION_DONE, 0, (LPARAM)result);
        free(input);
        return 1;
    }

    if (!ParsePacketCSV(csvPath, &result->packets, &result->packetCount)) {
        strncpy(result->errorMsg, "Could not parse ffprobe packet CSV.", sizeof(result->errorMsg) - 1);
        PostMessageA(input->hwnd, WM_EXTRACTION_DONE, 0, (LPARAM)result);
        free(input);
        return 1;
    }

    char streamCsvPath[MAX_PATH];
    snprintf(streamCsvPath, sizeof(streamCsvPath), "%s\\streaminfo.csv", input->tempDir);

    AppState tempState = {0}; /* reuse ParseStreamInfoCSV's existing signature locally */
    if (GetStreamInfo(input->inputPath, streamCsvPath) && ParseStreamInfoCSV(streamCsvPath, &tempState)) {
        strncpy(result->pixFmt, tempState.pixFmt, sizeof(result->pixFmt) - 1);
        strncpy(result->colorSpace, tempState.colorSpace, sizeof(result->colorSpace) - 1);
        strncpy(result->colorRange, tempState.colorRange, sizeof(result->colorRange) - 1);
        result->streamWidth = tempState.streamWidth;
        result->streamHeight = tempState.streamHeight;
    } else {
        strncpy(result->pixFmt, "unknown", sizeof(result->pixFmt) - 1);
        strncpy(result->colorSpace, "unknown", sizeof(result->colorSpace) - 1);
        strncpy(result->colorRange, "unknown", sizeof(result->colorRange) - 1);
    }

    result->success = TRUE;
    PostMessageA(input->hwnd, WM_EXTRACTION_DONE, 0, (LPARAM)result);
    free(input);
    return 0;
}

/* ---------------------------------------------------------------------
 * Open file flow
 * ------------------------------------------------------------------- */

static void CleanOldFrames(const char *dir)
{
    char pat[MAX_PATH];
    snprintf(pat, sizeof(pat), "%s\\frame_*.*", dir);
    WIN32_FIND_DATAA fd;
    HANDLE h = FindFirstFileA(pat, &fd);
    if (h == INVALID_HANDLE_VALUE) return;
    do {
        char p[MAX_PATH];
        snprintf(p, sizeof(p), "%s\\%s", dir, fd.cFileName);
        DeleteFileA(p);
    } while (FindNextFileA(h, &fd));
    FindClose(h);
}

static void OnOpenClicked(HWND hwnd)
{
    char filename[MAX_PATH] = {0};
    OPENFILENAMEA ofn;
    ZeroMemory(&ofn, sizeof(ofn));
    ofn.lStructSize = sizeof(ofn);
    ofn.hwndOwner = hwnd;
    ofn.lpstrFilter = "Video Files\0*.mov;*.avi;*.mpeg;*.mpg\0All Files\0*.*\0";
    ofn.lpstrFile = filename;
    ofn.nMaxFile = MAX_PATH;
    ofn.Flags = OFN_FILEMUSTEXIST | OFN_PATHMUSTEXIST;

    if (!GetOpenFileNameA(&ofn)) return;

    /* Reset state for a new file. */
    if (g_state.packets) { free(g_state.packets); g_state.packets = NULL; }
    g_frameValid = FALSE;
    if (g_state.hExtractionProcess) {
        TerminateProcess(g_state.hExtractionProcess, 0); /* stop any prior extraction */
        CloseHandle(g_state.hExtractionProcess);
        g_state.hExtractionProcess = NULL;
    }
    KillTimer(hwnd, ID_TIMER_POLL_EXTRACTION);
    KillTimer(hwnd, ID_TIMER_PLAYBACK);
    g_state.playing = FALSE;
    g_state.packetCount = 0;
    g_state.currentFrame = 0;
    g_state.highestAvailableFrame = -1;
    g_state.extractionComplete = FALSE;
    g_state.firstFrameShown = FALSE;

    strncpy(g_state.inputPath, filename, MAX_PATH - 1);

    GetTempPathA(MAX_PATH, g_state.tempDir);
    strncat(g_state.tempDir, "hexplayer_frames", MAX_PATH - strlen(g_state.tempDir) - 1);
    CreateDirectoryA(g_state.tempDir, NULL);
    CleanOldFrames(g_state.tempDir);

    SetStatus("Reading frame addresses (fast -- no decoding yet)...");

    /* Fire off the FAST metadata gather (packet positions, pixel
     * format) on a worker thread. Full frame extraction is launched
     * separately, afterward, as soon as metadata is ready -- see
     * WM_EXTRACTION_DONE below. This is what lets frame 1 appear
     * within a second or two instead of after the whole video decodes. */
    ExtractionThreadInput *threadInput = (ExtractionThreadInput *)malloc(sizeof(ExtractionThreadInput));
    if (!threadInput) {
        SetStatus("ERROR: out of memory starting extraction.");
        return;
    }
    threadInput->hwnd = hwnd;
    strncpy(threadInput->inputPath, g_state.inputPath, MAX_PATH - 1);
    strncpy(threadInput->tempDir, g_state.tempDir, MAX_PATH - 1);

    HANDLE hThread = CreateThread(NULL, 0, ExtractionThreadProc, threadInput, 0, NULL);
    if (hThread) {
        CloseHandle(hThread); /* don't need to join it; it posts a message when done */
    } else {
        SetStatus("ERROR: could not start metadata thread.");
        free(threadInput);
    }
}

/* ---------------------------------------------------------------------
 * Window procedure
 * ------------------------------------------------------------------- */

LRESULT CALLBACK WindowProc(HWND hwnd, UINT msg, WPARAM wParam, LPARAM lParam)
{
    switch (msg) {
        case WM_CREATE: {
            CreateWindowA("BUTTON", "Open Video", WS_VISIBLE | WS_CHILD | BS_PUSHBUTTON,
                10, 10, 100, 30, hwnd, (HMENU)ID_BTN_OPEN, NULL, NULL);
            CreateWindowA("BUTTON", "Prev", WS_VISIBLE | WS_CHILD | BS_PUSHBUTTON,
                120, 10, 60, 30, hwnd, (HMENU)ID_BTN_PREV, NULL, NULL);
            CreateWindowA("BUTTON", "Play/Pause", WS_VISIBLE | WS_CHILD | BS_PUSHBUTTON,
                190, 10, 90, 30, hwnd, (HMENU)ID_BTN_PLAYPAUSE, NULL, NULL);
            CreateWindowA("BUTTON", "Next", WS_VISIBLE | WS_CHILD | BS_PUSHBUTTON,
                290, 10, 60, 30, hwnd, (HMENU)ID_BTN_NEXT, NULL, NULL);
            CreateWindowA("BUTTON", "Snapshot JPEG", WS_VISIBLE | WS_CHILD | BS_PUSHBUTTON,
                360, 10, 110, 30, hwnd, (HMENU)ID_BTN_SNAPSHOT, NULL, NULL);
            CreateWindowA("BUTTON", "Dump Raw Frame + Layout", WS_VISIBLE | WS_CHILD | BS_PUSHBUTTON,
                10, 630, 170, 30, hwnd, (HMENU)ID_BTN_DUMPRAW, NULL, NULL);
            CreateWindowA("BUTTON", "Export Frame Info", WS_VISIBLE | WS_CHILD | BS_PUSHBUTTON,
                190, 630, 140, 30, hwnd, (HMENU)ID_BTN_EXPORTINFO, NULL, NULL);

            g_hMonoFont = CreateFontA(
                15, 0, 0, 0, FW_NORMAL, FALSE, FALSE, FALSE,
                ANSI_CHARSET, OUT_DEFAULT_PRECIS, CLIP_DEFAULT_PRECIS,
                DEFAULT_QUALITY, FIXED_PITCH | FF_MODERN, "Consolas");
            g_hStatus = CreateWindowA("STATIC", "Ready.",
                WS_VISIBLE | WS_CHILD, 10, 670, 760, 20, hwnd, NULL, NULL, NULL);
            return 0;
        }
        case WM_COMMAND: {
            switch (LOWORD(wParam)) {
                case ID_BTN_OPEN: OnOpenClicked(hwnd); REDRAW(hwnd); break;
                case ID_BTN_PREV:
                    if (g_state.currentFrame > 0) LoadFrame(g_state.currentFrame - 1);
                    REDRAW(hwnd);
                    break;
                case ID_BTN_NEXT:
                    if (g_state.currentFrame < g_state.highestAvailableFrame) {
                        LoadFrame(g_state.currentFrame + 1);
                    } else if (!g_state.extractionComplete) {
                        SetStatus("That frame hasn't been extracted yet -- still buffering.");
                    }
                    REDRAW(hwnd);
                    break;
                case ID_BTN_PLAYPAUSE:
                    g_state.playing = !g_state.playing;
                    if (g_state.playing) {
                        StartPlaybackClock(); SetTimer(hwnd, ID_TIMER_PLAYBACK, 8, NULL);
                    } else {
                        KillTimer(hwnd, ID_TIMER_PLAYBACK);
                    }
                    break;
                case ID_BTN_SNAPSHOT: ExportSnapshotJpeg(hwnd); break;
                case ID_BTN_EXPORTINFO: ExportFrameInfoText(hwnd); break;
                case ID_BTN_DUMPRAW: ExportRawFrameAndLayout(hwnd); break;
            }
            return 0;
        }
        case WM_EXTRACTION_DONE: {
            ExtractionResult *result = (ExtractionResult *)lParam;

            if (!result->success) {
                char msg[320];
                snprintf(msg, sizeof(msg), "ERROR: %s", result->errorMsg);
                SetStatus(msg);
                free(result);
                return 0;
            }

            /* Metadata is ready -- store it on the UI thread (safe,
             * single-threaded access to g_state from here on). */
            g_state.packets = result->packets;
            g_state.packetCount = result->packetCount;
            SortPackets(g_state.packets, g_state.packetCount);
            strncpy(g_state.pixFmt, result->pixFmt, sizeof(g_state.pixFmt) - 1);
            strncpy(g_state.colorSpace, result->colorSpace, sizeof(g_state.colorSpace) - 1);
            strncpy(g_state.colorRange, result->colorRange, sizeof(g_state.colorRange) - 1);
            g_state.streamWidth = result->streamWidth;
            g_state.streamHeight = result->streamHeight;
            free(result); /* packets ownership now belongs to g_state, NOT freed here */

            SetStatus("Metadata ready. Starting frame extraction (first frame will appear shortly)...");

            /* NOW actually launch frame extraction -- non-blocking,
             * writes PNGs progressively while this returns immediately. */
            if (!LaunchFrameExtractionAsync(g_state.inputPath, g_state.tempDir, &g_state.hExtractionProcess)) {
                SetStatus("ERROR: could not launch ffmpeg for frame extraction.");
                return 0;
            }

            /* Poll frequently so frame 1 appears as fast as ffmpeg
             * actually writes it, not on some arbitrary slow interval. */
            SetTimer(hwnd, ID_TIMER_POLL_EXTRACTION, 25, NULL);
            return 0;
        }
        case WM_ERASEBKGND:
            return 1;
        case WM_TIMER: {
            if (wParam == ID_TIMER_POLL_EXTRACTION) {
                BOOL procDone = (g_state.hExtractionProcess == NULL) ||
                    WaitForSingleObject(g_state.hExtractionProcess, 0) == WAIT_OBJECT_0;
                while (1) {
                    int nextIndex = g_state.highestAvailableFrame + 1;
                    if (nextIndex >= g_state.packetCount) break;
                    if (!FrameFileExists(nextIndex + 1)) break;
                    /* a frame is complete once the NEXT file exists (or ffmpeg is done) */
                    if (!procDone && !FrameFileExists(nextIndex + 2)) break;
                    g_state.highestAvailableFrame = nextIndex;
                }
                if (!g_state.firstFrameShown && g_state.highestAvailableFrame >= 0) {
                    if (LoadFrame(0)) {
                        g_state.firstFrameShown = TRUE;
                        SetStatus("First frame ready -- press Play. Extraction continues in the background.");
                        REDRAW(hwnd);
                    }
                }
                if (g_state.hExtractionProcess && procDone) {
                    CloseHandle(g_state.hExtractionProcess);
                    g_state.hExtractionProcess = NULL;
                    g_state.extractionComplete = TRUE;
                    KillTimer(hwnd, ID_TIMER_POLL_EXTRACTION);
                    SetStatus("Extraction complete. Full video available.");
                }
            }
            else if (wParam == ID_TIMER_PLAYBACK) {
                /* Clock-driven: show the frame whose pts <= elapsed time,
                 * skipping intermediates if we fell behind. */
                double target = g_playPtsStart + (NowMs() - g_playClockStart);
                int f = g_state.currentFrame;
                while (f + 1 <= g_state.highestAvailableFrame &&
                       g_state.packets[f + 1].pts_time * 1000.0 <= target) f++;

                if (f != g_state.currentFrame) {
                    if (LoadFrame(f)) REDRAW(hwnd);
                } else if (f + 1 > g_state.highestAvailableFrame) {
                    if (g_state.extractionComplete) {
                        g_state.playing = FALSE;
                        KillTimer(hwnd, ID_TIMER_PLAYBACK);
                        SetStatus("End of video.");
                    } else if (f + 1 < g_state.packetCount &&
                               g_state.packets[f + 1].pts_time * 1000.0 <= target) {
                        StartPlaybackClock();   /* starved: pause the clock, don't skip ahead */
                        SetStatus("Buffering -- waiting for extraction...");
                    }
                }
            }
            return 0;
        }
        case WM_PAINT: {
            PAINTSTRUCT ps;
            HDC hdc = BeginPaint(hwnd, &ps);
            PaintAll(hdc, &ps.rcPaint);
            EndPaint(hwnd, &ps);
            return 0;
        }
        case WM_DESTROY:
            PostQuitMessage(0);
            return 0;
    }
    return DefWindowProcA(hwnd, msg, wParam, lParam);
}

int WINAPI WinMain(HINSTANCE hInstance, HINSTANCE hPrevInstance, LPSTR lpCmdLine, int nCmdShow)
{
    (void)hPrevInstance; (void)lpCmdLine;

    const char CLASS_NAME[] = "HexPlayerWindowClass";
    WNDCLASSA wc = {0};
    wc.lpfnWndProc = WindowProc;
    wc.hInstance = hInstance;
    wc.lpszClassName = CLASS_NAME;
    wc.hCursor = LoadCursor(NULL, IDC_ARROW);
    wc.hbrBackground = (HBRUSH)(COLOR_WINDOW + 1);
    RegisterClassA(&wc);

    HWND hwnd = CreateWindowExA(0, CLASS_NAME, "HexPlayer",
        WS_CAPTION | WS_SYSMENU | WS_MINIMIZEBOX | WS_CLIPCHILDREN, CW_USEDEFAULT, CW_USEDEFAULT, 816, 760,
        NULL, NULL, hInstance, NULL);
    if (!hwnd) return 0;

    timeBeginPeriod(1);
    ShowWindow(hwnd, nCmdShow);

    MSG msg = {0};
    while (GetMessage(&msg, NULL, 0, 0)) {
        TranslateMessage(&msg);
        DispatchMessage(&msg);
    }
    timeEndPeriod(1);
    return 0;
}
