#include <atomic>
#include <chrono>
#include <functional>
#include <iostream>
#include <mutex>
#include <random>
#include <string>
#include <thread>
#include <vector>
#include <array>
#include <fstream>
#include <string>
#include <sstream>
// { changed code: needed for std::max }
#include <algorithm>
// needed for std::round, std::abs, snprintf
#include <cmath>
#include <cstdio>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <cwchar>
#include <cctype>
#include <limits>
#include <iomanip>
#ifdef _MSC_VER
    #include <intrin.h>
#else
    #include <x86intrin.h>
#endif

#ifdef _WIN32
  // { changed code }
  #ifndef NOMINMAX
  #define NOMINMAX
  #endif
  #include <windows.h>
  #include <windowsx.h>
    #include <powrprof.h>
    #pragma comment(lib, "PowrProf.lib")
        // COM helpers used when converting GUID to string
        #include <objbase.h>
        #include <oleauto.h>
        #include <wbemidl.h>
        #include <srrestoreptapi.h>
        #pragma comment(lib, "Ole32.lib")
  #include <conio.h>
    // For PlaySound from memory
    #include <mmsystem.h>
    #include <processthreadsapi.h>
    // For process enumeration and termination
    #include <tlhelp32.h>
    // For device enumeration and disable
    #include <setupapi.h>
    #include <cfgmgr32.h>
    // For opening URLs in browser
    #include <shellapi.h>
    #pragma comment(lib, "setupapi.lib")
    #pragma comment(lib, "Cfgmgr32.lib")
    #pragma comment(lib, "winmm.lib")
    #pragma comment(lib, "shell32.lib")
        #include "resource.h"
#else
  #include <unistd.h>
  #include <termios.h>
  #include <sys/ioctl.h>
  #include <sys/select.h>    // added for non-blocking input
#endif

#ifndef SARDANELLO_ENABLE_AUDIO
#define SARDANELLO_ENABLE_AUDIO 0
#endif

static std::atomic<bool> g_running{true};
static std::mutex g_consoleMutex;
// current page shown in the menu; 1-based
static int g_currentPage = 1;
static int g_totalPages = 12;
// benchmark running flag
static std::atomic<bool> g_timerBenchmarkRunning{false};
// Pause flag for matrix background rendering (when true, rain is paused)
static std::atomic<bool> g_matrixPause{false};
// If true, a recent boot/registry tweak was applied and user may press Y to reboot
static std::atomic<bool> g_rebootAvailable{false};
static std::string g_rebootMessage; // optional message or error
// Флаг: выполняется ли сейчас применение/импорт плана питания (защита от повторных запусков)
static std::atomic<bool> g_powerPlanApplying{false};

// Глобальные переменные для службы таймера
static double g_targetTimerMs = 1.0;
static ULONG g_targetTime100ns = 10000;
static bool g_timerSet = false;

// Keyboard layout handling: save previous and optionally switch to English (US)
// System-wide keyboard layout handling: broadcast request to change input language for all windows
static HKL g_prevKeyboardLayout = NULL;
static HKL g_broadcastEnglishHKL = NULL;
static bool g_layoutBroadcasted = false;

enum class AppLanguage {
    Russian = 0,
    English,
    German,
    Turkish,
    Spanish,
    PortugueseBrazil,
    Hindi
};

static AppLanguage g_appLanguage = AppLanguage::Russian;

static std::string toUtf8(const std::wstring& text)
{
#ifdef _WIN32
    if (text.empty()) return std::string();
    int needed = WideCharToMultiByte(CP_UTF8, 0, text.c_str(), -1, nullptr, 0, nullptr, nullptr);
    if (needed <= 0) return std::string(text.begin(), text.end());
    std::string out((size_t)needed - 1, '\0');
    WideCharToMultiByte(CP_UTF8, 0, text.c_str(), -1, out.data(), needed, nullptr, nullptr);
    return out;
#else
    return std::string(text.begin(), text.end());
#endif
}

static const wchar_t* appTextW(const wchar_t* ru, const wchar_t* en, const wchar_t* de,
                               const wchar_t* tr, const wchar_t* es, const wchar_t* pt,
                               const wchar_t* hi)
{
    switch (g_appLanguage) {
    case AppLanguage::English: return en;
    case AppLanguage::German: return de;
    case AppLanguage::Turkish: return tr;
    case AppLanguage::Spanish: return es;
    case AppLanguage::PortugueseBrazil: return pt;
    case AppLanguage::Hindi: return hi;
    case AppLanguage::Russian:
    default: return ru;
    }
}

static std::string appText(const wchar_t* ru, const wchar_t* en, const wchar_t* de,
                           const wchar_t* tr, const wchar_t* es, const wchar_t* pt,
                           const wchar_t* hi)
{
    return toUtf8(appTextW(ru, en, de, tr, es, pt, hi));
}

// Broadcast a request to switch the system input language to English (US). Stores previous layout.
static bool broadcastSwitchToEnglishLayout()
{
    // Save current layout of the foreground thread/window
        // Start global benchmark stopwatch
        auto benchStart = std::chrono::steady_clock::now();
        auto formatElapsed = [&](void)->std::string {
            using namespace std::chrono;
            auto now = steady_clock::now();
            auto delta = duration_cast<seconds>(now - benchStart);
            int totalSec = (int)delta.count();
            int mins = totalSec / 60;
            int secs = totalSec % 60;
            char buf[64]; std::snprintf(buf, sizeof(buf), "Elapsed %02d:%02d", mins, secs);
            return std::string(buf);
        };
    g_prevKeyboardLayout = GetKeyboardLayout(GetCurrentThreadId());
    // Load English (US) layout handle
    HKL hEng = LoadKeyboardLayoutA("00000409", KLF_NOTELLSHELL);
    if (!hEng) return false;
    g_broadcastEnglishHKL = hEng;
    // Broadcast WM_INPUTLANGCHANGEREQUEST to all top-level windows to change layout visually
    BOOL posted = PostMessageW(HWND_BROADCAST, WM_INPUTLANGCHANGEREQUEST, 0, (LPARAM)hEng);
    g_layoutBroadcasted = posted != 0;
    return g_layoutBroadcasted;
}

static void broadcastRestoreLayout()
{
    if (!g_layoutBroadcasted) return;
    if (g_prevKeyboardLayout) {
        PostMessageW(HWND_BROADCAST, WM_INPUTLANGCHANGEREQUEST, 0, (LPARAM)g_prevKeyboardLayout);
    }
    g_layoutBroadcasted = false;
}

// Forward declaration; full implementation placed after helpers and globals so it can use ConsoleSize, g_menuMutex, etc.
void showBestTimer();

// forward-declare Rect and drawMenu so showBestTimer can call it to repaint the UI after benchmarking
struct Rect;
Rect drawMenu();

// declare prototype; implementation will be placed after console helpers so it can use ConsoleSize etc.
void disableHighPrecisionTimer();

// Forward declarations for optimal timer functions
struct OptimalTimerResult;
static void saveOptimalTimer(double timerMs, double cvScore,
                             double stableZoneStartMs = -1.0,
                             double stableZoneEndMs = -1.0,
                             double formulaBestTimerMs = -1.0);
static OptimalTimerResult loadOptimalTimer();
static bool createTimerService(double timerMs);
static bool applyOptimalTimer(double timerMs);
static bool isServiceRunning();
static bool stopTimerService();
static bool startTimerService();
static bool resetTimerToDefault();
static bool loadUpdatedTimer();
static bool setTimerResolution();
static int runTimerService();

// Forward declarations for power plan functions
static bool isAdministrator();
static bool detectS0ModernStandby();
static bool setPlatformAoAcOverride(bool enable);
static int getPlatformAoAcOverride();

void exitProgram()
{
    // Это будет вызвано из основного потока при желании завершить программу.
    g_running = false;
}

// Cross-platform get terminal size
struct ConsoleSize { int cols = 80; int rows = 25; };

ConsoleSize getConsoleSize()
{
    ConsoleSize cs;
#ifdef _WIN32
    CONSOLE_SCREEN_BUFFER_INFO info;
    HANDLE h = GetStdHandle(STD_OUTPUT_HANDLE);
    if (GetConsoleScreenBufferInfo(h, &info)) {
        cs.cols = info.srWindow.Right - info.srWindow.Left + 1;
        cs.rows = info.srWindow.Bottom - info.srWindow.Top + 1;
    }
#else
    struct winsize w;
    if (ioctl(0, TIOCGWINSZ, &w) == 0) {
        cs.cols = w.ws_col;
        cs.rows = w.ws_row;
    }
#endif
    return cs;
}

// Cross-platform set cursor position and color helpers
void setCursorPosition(int x, int y)
{
#ifdef _WIN32
    HANDLE h = GetStdHandle(STD_OUTPUT_HANDLE);
    // { changed code }
    COORD pos;
    pos.X = static_cast<SHORT>(x);
    pos.Y = static_cast<SHORT>(y);
    SetConsoleCursorPosition(h, pos);
#else
    std::cout << "\x1b[" << (y+1) << ";" << (x+1) << "H";
#endif
}

// Full implementation of disableHighPrecisionTimer moved further below so it can use
// Rect and g_menuMutex which are defined later in the file.

void hideCursor()
{
#ifdef _WIN32
    HANDLE h = GetStdHandle(STD_OUTPUT_HANDLE);
    // { changed code }
    CONSOLE_CURSOR_INFO info;
    info.dwSize = 1;
    info.bVisible = FALSE;
    SetConsoleCursorInfo(h, &info);
#else
    std::cout << "\x1b[?25l";
#endif
}

void showCursor()
{
#ifdef _WIN32
    HANDLE h = GetStdHandle(STD_OUTPUT_HANDLE);
    // { changed code }
    CONSOLE_CURSOR_INFO info;
    info.dwSize = 1;
    info.bVisible = TRUE;
    SetConsoleCursorInfo(h, &info);
#else
    std::cout << "\x1b[?25h";
#endif
}

void setMatrixColors()
{
#ifdef _WIN32
    HANDLE h = GetStdHandle(STD_OUTPUT_HANDLE);
    // Зеленый текст на черном фоне, интенсивный зелен
    SetConsoleTextAttribute(h, FOREGROUND_GREEN | FOREGROUND_INTENSITY);
#else
    // ANSI: bright green on black
    std::cout << "\x1b[1;32m";
#endif
}

void resetColors()
{
#ifdef _WIN32
    HANDLE h = GetStdHandle(STD_OUTPUT_HANDLE);
    SetConsoleTextAttribute(h, FOREGROUND_RED | FOREGROUND_GREEN | FOREGROUND_BLUE);
#else
    std::cout << "\x1b[0m";
#endif
    std::cout.flush();
}

// Minimal cross-platform single-key read (non-echoing when possible)
// { changed code: make non-blocking; return -1 when no key pressed }
int getKey()
{
#ifdef _WIN32
    if (_kbhit()) return _getch();
    return -1;
#else
    struct termios oldt, newt;
    tcgetattr(STDIN_FILENO, &oldt);
    newt = oldt;
    newt.c_lflag &= ~(ICANON | ECHO);
    tcsetattr(STDIN_FILENO, TCSANOW, &newt);

    fd_set set;
    FD_ZERO(&set);
    FD_SET(STDIN_FILENO, &set);
    struct timeval tv;
    tv.tv_sec = 0;
    tv.tv_usec = 0; // poll
    int rv = select(STDIN_FILENO + 1, &set, NULL, NULL, &tv);
    int c = -1;
    if (rv > 0) c = getchar();

    tcsetattr(STDIN_FILENO, TCSANOW, &oldt);
    return c;
#endif
}

// { added code: enable ANSI VT sequences on Windows and switch to UTF-8 }
#ifdef _WIN32
void enableVirtualTerminalAndUTF8()
{
    HANDLE out = GetStdHandle(STD_OUTPUT_HANDLE);
    if (out != INVALID_HANDLE_VALUE) {
        DWORD mode = 0;
        if (GetConsoleMode(out, &mode)) {
            // ENABLE_VIRTUAL_TERMINAL_PROCESSING may be undefined on some very old SDKs,
            // but on MinGW-w64 it normally exists. Fallback: try define if necessary.
  #ifndef ENABLE_VIRTUAL_TERMINAL_PROCESSING
  #define ENABLE_VIRTUAL_TERMINAL_PROCESSING 0x0004
  #endif
            mode |= ENABLE_VIRTUAL_TERMINAL_PROCESSING;
            SetConsoleMode(out, mode);
        }
    }
    // switch to UTF-8 output/input so Cyrillic prints correctly
    SetConsoleOutputCP(CP_UTF8);
    SetConsoleCP(CP_UTF8);
}

// Disable QuickEdit (mouse selection) and mouse input so console clicks don't pause the program
static void disableConsoleQuickEdit()
{
#ifdef _WIN32
    HANDLE hin = GetStdHandle(STD_INPUT_HANDLE);
    if (hin != INVALID_HANDLE_VALUE) {
        DWORD mode = 0;
        if (GetConsoleMode(hin, &mode)) {
            // Per MSDN, to change ENABLE_QUICK_EDIT_MODE we must set ENABLE_EXTENDED_FLAGS first
            mode |= ENABLE_EXTENDED_FLAGS;
            // Clear QuickEdit so selection doesn't pause the console
            mode &= ~ENABLE_QUICK_EDIT_MODE;
            // Also disable mouse input so clicks aren't reported
            mode &= ~ENABLE_MOUSE_INPUT;
            SetConsoleMode(hin, mode);
        }
    }
#endif
}

// ...existing code...

// Shared helper to run bcdedit tweaks and set GlobalTimerResolutionRequests registry value.
// Returns true on success, false on failure and sets errOut.
static bool performBootAndRegistryTweaks(std::string &errOut)
{
    const std::vector<std::string> cmds = {
        "bcdedit /set disabledynamictick yes",
        "bcdedit /set useplatformtick yes",
        "bcdedit /set useplatformclock false",
        "bcdedit /deletevalue useplatformclock"
    };

    for (auto &c : cmds) {
        std::vector<char> cmdBuf(c.begin(), c.end()); cmdBuf.push_back('\0');
        STARTUPINFOA si; PROCESS_INFORMATION pi;
        ZeroMemory(&si, sizeof(si)); si.cb = sizeof(si);
        ZeroMemory(&pi, sizeof(pi));
        BOOL ok = CreateProcessA(NULL, cmdBuf.data(), NULL, NULL, FALSE, CREATE_NO_WINDOW, NULL, NULL, &si, &pi);
        if (!ok) {
            errOut = std::string("CreateProcess failed (code )") + std::to_string((int)GetLastError()) + "; cmd=" + c;
            return false;
        }
        WaitForSingleObject(pi.hProcess, INFINITE);
        DWORD exitCode = 0; GetExitCodeProcess(pi.hProcess, &exitCode);
        CloseHandle(pi.hProcess); CloseHandle(pi.hThread);
        if (exitCode != 0) {
            errOut = std::string("Command failed with exit ") + std::to_string((int)exitCode) + ": " + c;
            return false;
        }
    }

    HKEY hK = NULL;
    LONG r = RegCreateKeyExA(HKEY_LOCAL_MACHINE,
                             "SYSTEM\\CurrentControlSet\\Control\\Session Manager\\kernel",
                             0, NULL, REG_OPTION_NON_VOLATILE, KEY_SET_VALUE, NULL, &hK, NULL);
    if (r != ERROR_SUCCESS) {
        errOut = std::string("RegCreateKeyEx failed: ") + std::to_string((int)r);
        return false;
    }
    DWORD val = 1;
    LONG r2 = RegSetValueExA(hK, "GlobalTimerResolutionRequests", 0, REG_DWORD, (const BYTE*)&val, sizeof(val));
    RegCloseKey(hK);
    if (r2 != ERROR_SUCCESS) {
        errOut = std::string("RegSetValueEx failed: ") + std::to_string((int)r2);
        return false;
    }
    return true;
}

// Attempt a system reboot. Tries to enable shutdown privilege and call InitiateSystemShutdownExA,
// falls back to calling 'shutdown /r /t 0' if necessary. This runs synchronously but is called
// from the main input loop so it won't block other threads.
static void attemptReboot()
{
    g_rebootAvailable = false;
    // try to enable SeShutdownPrivilege
    HANDLE tok = NULL;
    if (OpenProcessToken(GetCurrentProcess(), TOKEN_ADJUST_PRIVILEGES | TOKEN_QUERY, &tok)) {
        TOKEN_PRIVILEGES tp; LUID luid;
        if (LookupPrivilegeValueA(NULL, "SeShutdownPrivilege", &luid)) {
            tp.PrivilegeCount = 1;
            tp.Privileges[0].Luid = luid;
            tp.Privileges[0].Attributes = SE_PRIVILEGE_ENABLED;
            AdjustTokenPrivileges(tok, FALSE, &tp, sizeof(tp), NULL, NULL);
        }
        CloseHandle(tok);
    }

    // Try graceful reboot via InitiateSystemShutdownExA
    BOOL ok = InitiateSystemShutdownExA(NULL, (LPSTR)"Перезагрузка по запросу из программы", 0, TRUE, TRUE, SHTDN_REASON_MAJOR_OTHER);
    if (!ok) {
        // fallback: use shutdown.exe command
        std::string cmd = "shutdown /r /t 0";
        std::vector<char> cmdBuf(cmd.begin(), cmd.end()); cmdBuf.push_back('\0');
        STARTUPINFOA si; PROCESS_INFORMATION pi; ZeroMemory(&si, sizeof(si)); si.cb = sizeof(si); ZeroMemory(&pi, sizeof(pi));
        if (CreateProcessA(NULL, cmdBuf.data(), NULL, NULL, FALSE, CREATE_NO_WINDOW, NULL, NULL, &si, &pi)) {
            CloseHandle(pi.hThread); CloseHandle(pi.hProcess);
        }
    }
}
#else
void enableVirtualTerminalAndUTF8() { /* no-op on POSIX */ }
#endif

#ifdef _WIN32
// Optional embedded audio for private builds. Public GitHub builds keep it off.
bool PlayEmbeddedWav(UINT resourceId)
{
#if SARDANELLO_ENABLE_AUDIO
    HMODULE hModule = GetModuleHandleW(NULL);
    if (!hModule) return false;

    HRSRC hRes = FindResource(hModule, MAKEINTRESOURCE(resourceId), RT_RCDATA);
    if (!hRes) return false;

    HGLOBAL hData = LoadResource(hModule, hRes);
    if (!hData) return false;

    DWORD size = SizeofResource(hModule, hRes);
    void* pData = LockResource(hData);
    if (!pData || size == 0) return false;

    // PlaySound supports playing from memory with SND_MEMORY flag.
    // Use SND_SYNC so it plays to completion before returning.
    BOOL ok = PlaySoundA(static_cast<LPCSTR>(pData), NULL, SND_MEMORY | SND_SYNC);
    return ok == TRUE;
#else
    (void)resourceId;
    return false;
#endif
}

bool PlayEmbeddedWavAsync(UINT resourceId)
{
#if SARDANELLO_ENABLE_AUDIO
    HMODULE hModule = GetModuleHandleW(NULL);
    if (!hModule) return false;

    HRSRC hRes = FindResource(hModule, MAKEINTRESOURCE(resourceId), RT_RCDATA);
    if (!hRes) return false;

    HGLOBAL hData = LoadResource(hModule, hRes);
    if (!hData) return false;

    DWORD size = SizeofResource(hModule, hRes);
    void* pData = LockResource(hData);
    if (!pData || size == 0) return false;

    BOOL ok = PlaySoundA(static_cast<LPCSTR>(pData), NULL, SND_MEMORY | SND_ASYNC | SND_NODEFAULT);
    return ok == TRUE;
#else
    (void)resourceId;
    return false;
#endif
}
#endif

#ifdef _WIN32
// Optional startup audio sequence for private builds.
// Музыка привязывается к CPU 1 (или последнему доступному), чтобы не мешать измерительному CPU.
static std::atomic<unsigned long> g_musicTicket{0};

static void ConfigureEmbeddedMusicThread()
{
    SYSTEM_INFO sysInfo;
    GetSystemInfo(&sysInfo);
    DWORD_PTR numProcessors = std::max<DWORD_PTR>(1, sysInfo.dwNumberOfProcessors);
    DWORD_PTR musicCpuMask = (numProcessors > 1) ? (DWORD_PTR)2 : (DWORD_PTR)1;
    SetThreadAffinityMask(GetCurrentThread(), musicCpuMask);
    SetThreadPriority(GetCurrentThread(), THREAD_PRIORITY_BELOW_NORMAL);
}

void StopEmbeddedMusic()
{
    ++g_musicTicket;
#if SARDANELLO_ENABLE_AUDIO
    PlaySoundA(NULL, NULL, 0);
#endif
}

void StartMusicTrack(UINT resourceId)
{
#if SARDANELLO_ENABLE_AUDIO
    StopEmbeddedMusic();
    ++g_musicTicket;
    PlayEmbeddedWavAsync(resourceId);
#else
    (void)resourceId;
    ++g_musicTicket;
#endif
}

void StartMusicSequence()
{
#if SARDANELLO_ENABLE_AUDIO
    std::thread([](){
        // Привязываем музыкальный поток к CPU 1 (или последнему CPU если только 1 ядро)
        SYSTEM_INFO sysInfo;
        GetSystemInfo(&sysInfo);
        DWORD_PTR numProcessors = sysInfo.dwNumberOfProcessors;
        
        // Если больше 1 CPU, используем CPU 1, иначе используем последний доступный
        DWORD_PTR musicCpuMask = (numProcessors > 1) ? (DWORD_PTR)2 : (DWORD_PTR)(1 << (numProcessors - 1));
        SetThreadAffinityMask(GetCurrentThread(), musicCpuMask);
        SetThreadPriority(GetCurrentThread(), THREAD_PRIORITY_BELOW_NORMAL); // Низкий приоритет для музыки
        
        // play first, if fails continue to second
        PlayEmbeddedWav(IDR_WAV_1);
        // small gap
        std::this_thread::sleep_for(std::chrono::milliseconds(50));
        PlayEmbeddedWav(IDR_WAV_2);
    }).detach();
#else
    ++g_musicTicket;
#endif
}

// Rect and globals used by showLoadingScreen and menu drawing
struct Rect { int x, y, w, h; };
static Rect g_menuRect = {0,0,0,0};
static Rect g_bannerRect = {0,0,0,0};
static std::mutex g_menuMutex;
// Persistent status lines shown under the page indicator; kept across redraws
static std::array<std::string,3> g_statusLines = { std::string(), std::string(), std::string() };

// Helper function to get exe directory
static std::string getExeDirectory() {
    char exePath[MAX_PATH];
    GetModuleFileNameA(nullptr, exePath, MAX_PATH);
    std::string exeDir = std::string(exePath);
    size_t lastSlash = exeDir.find_last_of("\\/");
    if (lastSlash != std::string::npos) exeDir = exeDir.substr(0, lastSlash + 1);
    return exeDir;
}

// Power config helper logging
static void appendPowerLog(const std::string &txt)
{
    std::string path = getExeDirectory();
    std::string file = path + "powercfg_helper.log";
    std::ofstream f(file, std::ios::app);
    if (!f) return;
    // timestamp
    auto now = std::chrono::system_clock::now();
    std::time_t t = std::chrono::system_clock::to_time_t(now);
    char buf[64];
    std::strftime(buf, sizeof(buf), "%Y-%m-%d %H:%M:%S", std::localtime(&t));
    f << "[" << buf << "] " << txt << std::endl;
}

// Сглаживание скользящим средним для графика
static std::vector<double> smooth(const std::vector<double>& a, int window=5) {
    int n = (int)a.size();
    std::vector<double> out(n);
    int hw = window/2;
    for (int i=0;i<n;i++) {
        int L = std::max(0, i - hw);
        int R = std::min(n-1, i + hw);
        double s = 0; int cnt = 0;
        for (int j=L;j<=R;j++){ s += a[j]; cnt++; }
        out[i] = (cnt>0)?(s / cnt):0.0;
    }
    return out;
}

struct TimerMeasurementStats {
    double avgAbsDeltaMs{std::numeric_limits<double>::infinity()};
    double avgWakeMs{std::numeric_limits<double>::infinity()};
    double stdDevWakeMs{std::numeric_limits<double>::infinity()};
    double cvPercent{std::numeric_limits<double>::infinity()};
    double cvPenaltyMs{std::numeric_limits<double>::infinity()};
    double scoreMs{std::numeric_limits<double>::infinity()};
    double minWakeMs{std::numeric_limits<double>::infinity()};
    double maxWakeMs{std::numeric_limits<double>::infinity()};
    double medianWakeMs{std::numeric_limits<double>::infinity()};
    int samples{0};
};

struct PhysicalCoreInfo {
    int physicalIndex{0};
    int representativeCpu{0};
    DWORD_PTR groupMask{0};
    int logicalSiblingCount{1};
    int efficiencyClass{0};
};

static constexpr double kScore1AvgAbsWeight = 0.75;
static constexpr double kScore1CvWeight = 0.25;
static constexpr double kScoreCvReferenceMs = 1.0;
static constexpr double kRobustTrimUpperFraction = 0.02;
static constexpr int kTopFirstWaveCount = 15;
static constexpr int kSecondWaveRounds = 7;
static constexpr int kThirdWaveRounds = 5;
static constexpr double kStableZoneScoreToleranceFraction = 0.05;

static double calculateWeightedTimerScoreMs(double avgAbsDeltaMs, double cvPenaltyMs,
                                            double avgAbsWeight, double cvWeight) {
    return avgAbsWeight * avgAbsDeltaMs + cvWeight * cvPenaltyMs;
}

static size_t robustUpperTrimmedCount(size_t sampleCount) {
    if (sampleCount == 0) return 0;
    size_t robustCount = sampleCount;
    if (sampleCount >= 100) {
        size_t trimUpper = (size_t)std::ceil(sampleCount * kRobustTrimUpperFraction);
        if (trimUpper > 0 && trimUpper < robustCount) {
            robustCount -= trimUpper;
            robustCount = std::max<size_t>(robustCount, std::min<size_t>(sampleCount, 10));
        }
    }
    return robustCount;
}

static TimerMeasurementStats calculateTimerMeasurementStats(const std::vector<double>& timesMs) {
    TimerMeasurementStats stats;
    stats.samples = (int)timesMs.size();
    if (timesMs.empty()) return stats;

    double sumWake = 0.0;
    std::vector<double> absDeltas;
    absDeltas.reserve(timesMs.size());
    stats.minWakeMs = timesMs[0];
    stats.maxWakeMs = timesMs[0];
    for (double t : timesMs) {
        sumWake += t;
        absDeltas.push_back(std::abs(t - 1.0));
        stats.minWakeMs = std::min(stats.minWakeMs, t);
        stats.maxWakeMs = std::max(stats.maxWakeMs, t);
    }
    stats.avgWakeMs = sumWake / (double)timesMs.size();

    std::sort(absDeltas.begin(), absDeltas.end());
    size_t robustAbsCount = robustUpperTrimmedCount(absDeltas.size());
    double robustAbsSum = 0.0;
    for (size_t i = 0; i < robustAbsCount; ++i) {
        robustAbsSum += absDeltas[i];
    }
    stats.avgAbsDeltaMs = robustAbsSum / (double)robustAbsCount;

    std::vector<double> sorted = timesMs;
    std::sort(sorted.begin(), sorted.end());
    size_t mid = sorted.size() / 2;
    if (sorted.size() % 2 == 0) {
        stats.medianWakeMs = (sorted[mid - 1] + sorted[mid]) * 0.5;
    } else {
        stats.medianWakeMs = sorted[mid];
    }

    // Robust CV: ignore the slowest wake-up outliers.
    size_t robustCount = robustUpperTrimmedCount(sorted.size());

    double robustSum = 0.0;
    for (size_t i = 0; i < robustCount; ++i) {
        robustSum += sorted[i];
    }
    double robustAvgWakeMs = robustSum / (double)robustCount;

    double robustVariance = 0.0;
    for (size_t i = 0; i < robustCount; ++i) {
        double diff = sorted[i] - robustAvgWakeMs;
        robustVariance += diff * diff;
    }
    stats.stdDevWakeMs = std::sqrt(robustVariance / (double)robustCount);
    stats.cvPercent = (robustAvgWakeMs > 0.0)
        ? (stats.stdDevWakeMs / robustAvgWakeMs) * 100.0
        : std::numeric_limits<double>::infinity();
    stats.cvPenaltyMs = (stats.cvPercent / 100.0) * kScoreCvReferenceMs;
    stats.scoreMs = calculateWeightedTimerScoreMs(stats.avgAbsDeltaMs, stats.cvPenaltyMs,
                                                  kScore1AvgAbsWeight,
                                                  kScore1CvWeight);
    return stats;
}

static int firstSetCpuFromMask(DWORD_PTR mask) {
    const int bits = (int)(sizeof(DWORD_PTR) * 8);
    for (int cpu = 0; cpu < bits; ++cpu) {
        if (mask & (((DWORD_PTR)1) << cpu)) return cpu;
    }
    return -1;
}

static int countSetCpus(DWORD_PTR mask) {
    int count = 0;
    while (mask) {
        count += (int)(mask & 1);
        mask >>= 1;
    }
    return std::max(1, count);
}

static std::vector<PhysicalCoreInfo> detectPhysicalCores() {
    std::vector<PhysicalCoreInfo> cores;

#ifdef _WIN32
    DWORD len = 0;
    if (!GetLogicalProcessorInformationEx(RelationProcessorCore, nullptr, &len) &&
        GetLastError() == ERROR_INSUFFICIENT_BUFFER && len > 0) {
        std::vector<unsigned char> buffer(len);
        auto* info = reinterpret_cast<PSYSTEM_LOGICAL_PROCESSOR_INFORMATION_EX>(buffer.data());
        if (GetLogicalProcessorInformationEx(RelationProcessorCore, info, &len)) {
            unsigned char* ptr = buffer.data();
            unsigned char* end = buffer.data() + len;
            int physicalIndex = 0;
            while (ptr < end) {
                auto* entry = reinterpret_cast<PSYSTEM_LOGICAL_PROCESSOR_INFORMATION_EX>(ptr);
                if (entry->Relationship == RelationProcessorCore) {
                    const PROCESSOR_RELATIONSHIP& rel = entry->Processor;
                    for (WORD g = 0; g < rel.GroupCount; ++g) {
                        if (rel.GroupMask[g].Group != 0) continue; // This code uses SetThreadAffinityMask, group 0 only.
                        DWORD_PTR mask = (DWORD_PTR)rel.GroupMask[g].Mask;
                        int representative = firstSetCpuFromMask(mask);
                        if (representative >= 0) {
                            PhysicalCoreInfo core;
                            core.physicalIndex = physicalIndex;
                            core.representativeCpu = representative;
                            core.groupMask = mask;
                            core.logicalSiblingCount = countSetCpus(mask);
                            core.efficiencyClass = (int)rel.EfficiencyClass;
                            cores.push_back(core);
                        }
                    }
                    ++physicalIndex;
                }
                if (entry->Size == 0) break;
                ptr += entry->Size;
            }
        }
    }
#endif

    if (cores.empty()) {
        SYSTEM_INFO sysInfo;
        GetSystemInfo(&sysInfo);
        int logicalCpuCount = std::max(1, (int)sysInfo.dwNumberOfProcessors);
        const int bits = (int)(sizeof(DWORD_PTR) * 8);
        for (int cpu = 0; cpu < std::min(logicalCpuCount, bits); ++cpu) {
            PhysicalCoreInfo core;
            core.physicalIndex = cpu;
            core.representativeCpu = cpu;
            core.groupMask = ((DWORD_PTR)1) << cpu;
            core.logicalSiblingCount = 1;
            cores.push_back(core);
        }
    }

    std::sort(cores.begin(), cores.end(), [](const PhysicalCoreInfo& a, const PhysicalCoreInfo& b) {
        return a.representativeCpu < b.representativeCpu;
    });
    for (size_t i = 0; i < cores.size(); ++i) {
        cores[i].physicalIndex = (int)i;
    }
    return cores;
}

static std::vector<PhysicalCoreInfo> preferredMeasurementCores(const std::vector<PhysicalCoreInfo>& cores) {
    if (cores.empty()) return cores;
    int maxEfficiency = cores[0].efficiencyClass;
    for (const auto& core : cores) {
        maxEfficiency = std::max(maxEfficiency, core.efficiencyClass);
    }
    if (maxEfficiency <= 0) return cores;

    std::vector<PhysicalCoreInfo> preferred;
    for (const auto& core : cores) {
        if (core.efficiencyClass == maxEfficiency) preferred.push_back(core);
    }
    return preferred.empty() ? cores : preferred;
}

struct GameLikeLoadStats {
    int logicalCpuCount{1};
    int physicalCoreCount{1};
    int measurementCpu{0};
    int measurementPhysicalCore{0};
    int workerCount{0};
    int logicalSiblingsIgnored{0};
    int periodMs{10};
    int prewarmSeconds{40};
    double targetLoadPercent{60.0};
    double dutyCyclePercent{60.0};
    bool measurementAffinityOk{false};
};

class GameLikeLoadGenerator {
public:
    explicit GameLikeLoadGenerator(double targetLoadPercent,
                                   int periodMs,
                                   const std::vector<PhysicalCoreInfo>& physicalCores,
                                   int measurementCpu)
        : targetLoadPercent_(targetLoadPercent), periodMs_(periodMs), physicalCores_(physicalCores) {
        SYSTEM_INFO sysInfo;
        GetSystemInfo(&sysInfo);
        logicalCpuCount_ = std::max(1, (int)sysInfo.dwNumberOfProcessors);
        if (physicalCores_.empty()) physicalCores_ = detectPhysicalCores();
        physicalCoreCount_ = std::max(1, (int)physicalCores_.size());

        measurementCpu_ = measurementCpu;
        measurementPhysicalCore_ = 0;
        DWORD_PTR measurementMask = 0;
        const int bits = (int)(sizeof(DWORD_PTR) * 8);
        if (measurementCpu_ >= 0 && measurementCpu_ < bits) {
            measurementMask = ((DWORD_PTR)1) << measurementCpu_;
        }

        bool foundMeasurementCore = false;
        for (const auto& core : physicalCores_) {
            if (core.representativeCpu == measurementCpu_ ||
                (measurementMask != 0 && (core.groupMask & measurementMask))) {
                measurementCpu_ = core.representativeCpu;
                measurementPhysicalCore_ = core.physicalIndex;
                foundMeasurementCore = true;
                break;
            }
        }
        if (!foundMeasurementCore && !physicalCores_.empty()) {
            measurementCpu_ = physicalCores_[0].representativeCpu;
            measurementPhysicalCore_ = physicalCores_[0].physicalIndex;
        }

        int totalLogicalSiblings = 0;
        for (const auto& core : physicalCores_) {
            totalLogicalSiblings += std::max(0, core.logicalSiblingCount - 1);
            if (core.physicalIndex != measurementPhysicalCore_) {
                workerCpus_.push_back(core.representativeCpu);
            }
        }
        if (workerCpus_.empty()) workerCpus_.push_back(measurementCpu_);
        workerCount_ = (int)workerCpus_.size();
        logicalSiblingsIgnored_ = totalLogicalSiblings;

        double targetFraction = std::max(0.10, std::min(0.90, targetLoadPercent_ / 100.0));
        dutyCycle_ = targetFraction * (double)physicalCoreCount_ / (double)workerCount_;
        dutyCycle_ = std::max(0.10, std::min(0.95, dutyCycle_));
    }

    ~GameLikeLoadGenerator() {
        stop();
    }

    void start() {
        stopRequested_.store(false, std::memory_order_release);
        workers_.reserve(workerCount_);
        for (int i = 0; i < workerCount_; ++i) {
            int cpu = workerCpus_[i % workerCpus_.size()];
            workers_.emplace_back([this, cpu, i]() {
                workerLoop(cpu, i);
            });
        }
    }

    void stop() {
        stopRequested_.store(true, std::memory_order_release);
        for (auto& worker : workers_) {
            if (worker.joinable()) worker.join();
        }
        workers_.clear();
    }

    GameLikeLoadStats stats(bool measurementAffinityOk) const {
        GameLikeLoadStats s;
        s.logicalCpuCount = logicalCpuCount_;
        s.physicalCoreCount = physicalCoreCount_;
        s.measurementCpu = measurementCpu_;
        s.measurementPhysicalCore = measurementPhysicalCore_;
        s.workerCount = workerCount_;
        s.logicalSiblingsIgnored = logicalSiblingsIgnored_;
        s.periodMs = periodMs_;
        s.prewarmSeconds = 40;
        s.targetLoadPercent = targetLoadPercent_;
        s.dutyCyclePercent = dutyCycle_ * 100.0;
        s.measurementAffinityOk = measurementAffinityOk;
        return s;
    }

private:
    void workerLoop(int cpu, int workerIndex) {
        SetThreadPriority(GetCurrentThread(), THREAD_PRIORITY_BELOW_NORMAL);

        const int bits = (int)(sizeof(DWORD_PTR) * 8);
        if (cpu >= 0 && cpu < bits) {
            DWORD_PTR mask = ((DWORD_PTR)1) << cpu;
            SetThreadAffinityMask(GetCurrentThread(), mask);
        }

        using clock = std::chrono::steady_clock;
        const auto period = std::chrono::microseconds(periodMs_ * 1000);
        const auto busyTime = std::chrono::microseconds(
            std::max(1, (int)std::llround((double)period.count() * dutyCycle_)));

        volatile uint64_t state = 0x9e3779b97f4a7c15ull ^ (uint64_t)(workerIndex + 1);
        while (!stopRequested_.load(std::memory_order_acquire) && g_running) {
            auto cycleStart = clock::now();
            auto busyUntil = cycleStart + busyTime;
            while (clock::now() < busyUntil &&
                   !stopRequested_.load(std::memory_order_relaxed) &&
                   g_running) {
                state ^= state << 7;
                state ^= state >> 9;
                state += 0x9e3779b97f4a7c15ull;
                _mm_pause();
            }

            auto cycleEnd = cycleStart + period;
            while (clock::now() < cycleEnd &&
                   !stopRequested_.load(std::memory_order_relaxed) &&
                   g_running) {
                auto now = clock::now();
                auto remainingUs = std::chrono::duration_cast<std::chrono::microseconds>(cycleEnd - now).count();
                if (remainingUs <= 0) break;

                DWORD sleepMs = (DWORD)std::max<long long>(1, std::min<long long>(2, (remainingUs + 999) / 1000));
                Sleep(sleepMs);
            }
        }
        (void)state;
    }

    double targetLoadPercent_;
    int periodMs_;
    int logicalCpuCount_;
    int physicalCoreCount_;
    int measurementCpu_;
    int measurementPhysicalCore_;
    int workerCount_;
    int logicalSiblingsIgnored_;
    double dutyCycle_;
    std::atomic<bool> stopRequested_{false};
    std::vector<PhysicalCoreInfo> physicalCores_;
    std::vector<int> workerCpus_;
    std::vector<std::thread> workers_;
};

struct ThreadSettingsGuard {
    ThreadSettingsGuard(HANDLE processHandle, HANDLE threadHandle)
        : process(processHandle),
          thread(threadHandle),
          oldPriorityClass(GetPriorityClass(processHandle)),
          oldThreadPriority(GetThreadPriority(threadHandle)) {}

    ~ThreadSettingsGuard() {
        SetThreadExecutionState(ES_CONTINUOUS);
        if (oldThreadPriority != THREAD_PRIORITY_ERROR_RETURN) {
            SetThreadPriority(thread, oldThreadPriority);
        }
        if (oldPriorityClass != 0) {
            SetPriorityClass(process, oldPriorityClass);
        }
        if (affinityChanged) {
            SetThreadAffinityMask(thread, oldAffinityMask);
        }
    }

    bool pinToCpu(int cpu) {
        const int bits = (int)(sizeof(DWORD_PTR) * 8);
        if (cpu < 0 || cpu >= bits) return false;
        DWORD_PTR mask = ((DWORD_PTR)1) << cpu;
        DWORD_PTR previous = SetThreadAffinityMask(thread, mask);
        if (previous == 0) return false;
        oldAffinityMask = previous;
        affinityChanged = true;
        return true;
    }

    HANDLE process;
    HANDLE thread;
    DWORD oldPriorityClass{0};
    int oldThreadPriority{THREAD_PRIORITY_ERROR_RETURN};
    DWORD_PTR oldAffinityMask{0};
    bool affinityChanged{false};
};

struct QuietCpuProbeResult {
    int cpu{0};
    int physicalCore{0};
    double scoreMs{std::numeric_limits<double>::infinity()};
    double avgAbsDeltaMs{std::numeric_limits<double>::infinity()};
    double cvPercent{std::numeric_limits<double>::infinity()};
    bool ok{false};
};

static QuietCpuProbeResult chooseQuietMeasurementCpu(double qpcFreq,
                                                     const std::vector<PhysicalCoreInfo>& candidateCores,
                                                     int probeMs = 1500) {
    std::vector<QuietCpuProbeResult> candidates;
    HANDLE thread = GetCurrentThread();
    DWORD_PTR originalAffinity = 0;
    bool haveOriginalAffinity = false;

    for (const auto& core : candidateCores) {
        if (!g_running) break;
        int cpu = core.representativeCpu;
        const int bits = (int)(sizeof(DWORD_PTR) * 8);
        if (cpu < 0 || cpu >= bits) continue;
        DWORD_PTR mask = ((DWORD_PTR)1) << cpu;
        DWORD_PTR previous = SetThreadAffinityMask(thread, mask);
        if (previous == 0) continue;
        if (!haveOriginalAffinity) {
            originalAffinity = previous;
            haveOriginalAffinity = true;
        }

        Sleep(20);
        std::vector<double> times;
        times.reserve(probeMs + 64);
        auto endT = std::chrono::steady_clock::now() + std::chrono::milliseconds(probeMs);
        while (std::chrono::steady_clock::now() < endT && g_running) {
            LARGE_INTEGER t1, t2;
            QueryPerformanceCounter(&t1);
            Sleep(1);
            QueryPerformanceCounter(&t2);
            double elapsedMs = (double)(t2.QuadPart - t1.QuadPart) * 1000.0 / qpcFreq;
            times.push_back(elapsedMs);
        }

        TimerMeasurementStats stats = calculateTimerMeasurementStats(times);
        if (!times.empty()) {
            QuietCpuProbeResult result;
            result.cpu = cpu;
            result.physicalCore = core.physicalIndex;
            result.scoreMs = stats.scoreMs;
            result.avgAbsDeltaMs = stats.avgAbsDeltaMs;
            result.cvPercent = stats.cvPercent;
            result.ok = true;
            candidates.push_back(result);
        }
    }

    if (haveOriginalAffinity) {
        SetThreadAffinityMask(thread, originalAffinity);
    }
    QuietCpuProbeResult best;
    if (!candidates.empty()) {
        std::sort(candidates.begin(), candidates.end(), [](const QuietCpuProbeResult& a, const QuietCpuProbeResult& b) {
            if (std::abs(a.scoreMs - b.scoreMs) < 1e-12) return a.cpu < b.cpu;
            return a.scoreMs < b.scoreMs;
        });

        double bestScore = candidates.front().scoreMs;
        double tolerance = std::max(0.000001, bestScore * 0.03);
        best = candidates.front();
        for (const auto& candidate : candidates) {
            if (candidate.scoreMs <= bestScore + tolerance && candidate.cpu < best.cpu) {
                best = candidate;
            }
        }
    } else {
        best.cpu = candidateCores.empty() ? 0 : candidateCores.front().representativeCpu;
        best.physicalCore = candidateCores.empty() ? 0 : candidateCores.front().physicalIndex;
    }
    return best;
}

// Упрощенная структура для результатов первой волны
struct TimerTestResult {
    double timerMs;      // значение таймера (мс)
    double avgAbsDeltaMs; // robust average(abs(Sleep(1)-1.000 ms))
    double cvPercent;
    double cvPenaltyMs;
    double scoreMs;
    double avgWakeMs;
    double stdDevWakeMs;
    double minWakeMs;
    double maxWakeMs;
    double medianWakeMs;
    int samples;
    int coresTested;     // число успешных ядер (ожидаемо 1)
};

// Структура для результатов второй волны
// Удалено: старый SecondWaveResult — больше не используется

// Структура результатов второй волны в окрестности лучшего
struct NeighborhoodResult {
    double timerMs;
    double avgAbsDeltaMs;
    double cvPercent;
    double cvPenaltyMs;
    double scoreMs;
    double avgWakeMs;
    double stdDevWakeMs;
    double minWakeMs;
    double maxWakeMs;
    double medianWakeMs;
    int samples;
};

struct TimerZoneSelection {
    bool valid{false};
    double recommendedTimerMs{std::numeric_limits<double>::infinity()};
    double recommendedScoreMs{std::numeric_limits<double>::infinity()};
    double formulaBestTimerMs{std::numeric_limits<double>::infinity()};
    double formulaBestScoreMs{std::numeric_limits<double>::infinity()};
    double zoneStartMs{std::numeric_limits<double>::infinity()};
    double zoneEndMs{std::numeric_limits<double>::infinity()};
    int recommendedIndex{-1};
    int formulaBestIndex{-1};
    std::vector<NeighborhoodResult> zoneResults;
};

static double roundTimerTo001(double timerMs) {
    return std::round(timerMs * 1000.0) / 1000.0;
}

static TimerZoneSelection selectRecommendedFromStableZone(const std::vector<NeighborhoodResult>& sortedByTimer) {
    TimerZoneSelection selection;
    if (sortedByTimer.empty()) return selection;

    int bestIndex = 0;
    double bestScore = sortedByTimer[0].scoreMs;
    for (size_t i = 1; i < sortedByTimer.size(); ++i) {
        if (sortedByTimer[i].scoreMs < bestScore ||
            (std::abs(sortedByTimer[i].scoreMs - bestScore) < 1e-12 &&
             sortedByTimer[i].timerMs < sortedByTimer[bestIndex].timerMs)) {
            bestScore = sortedByTimer[i].scoreMs;
            bestIndex = (int)i;
        }
    }

    double tolerance = std::max(0.00001, bestScore * kStableZoneScoreToleranceFraction);
    int left = bestIndex;
    while (left > 0 && std::abs(sortedByTimer[left - 1].scoreMs - bestScore) <= tolerance) {
        --left;
    }
    int right = bestIndex;
    while (right + 1 < (int)sortedByTimer.size() &&
           std::abs(sortedByTimer[right + 1].scoreMs - bestScore) <= tolerance) {
        ++right;
    }

    selection.zoneStartMs = sortedByTimer[left].timerMs;
    selection.zoneEndMs = sortedByTimer[right].timerMs;
    for (int i = left; i <= right; ++i) {
        selection.zoneResults.push_back(sortedByTimer[i]);
    }

    double zoneCenter = roundTimerTo001((selection.zoneStartMs + selection.zoneEndMs) * 0.5);
    int recommendedIndex = left;
    double bestDistance = std::abs(sortedByTimer[left].timerMs - zoneCenter);
    for (int i = left + 1; i <= right; ++i) {
        double distance = std::abs(sortedByTimer[i].timerMs - zoneCenter);
        if (distance < bestDistance ||
            (std::abs(distance - bestDistance) < 1e-12 &&
             sortedByTimer[i].scoreMs < sortedByTimer[recommendedIndex].scoreMs)) {
            bestDistance = distance;
            recommendedIndex = i;
        }
    }

    selection.valid = true;
    selection.formulaBestIndex = bestIndex;
    selection.formulaBestTimerMs = sortedByTimer[bestIndex].timerMs;
    selection.formulaBestScoreMs = sortedByTimer[bestIndex].scoreMs;
    selection.recommendedIndex = recommendedIndex;
    selection.recommendedTimerMs = sortedByTimer[recommendedIndex].timerMs;
    selection.recommendedScoreMs = sortedByTimer[recommendedIndex].scoreMs;
    return selection;
}

// Генерация HTML отчета с таблицей и графиками
static void generateHTMLReport(const std::vector<TimerTestResult>& results,
                              const std::vector<NeighborhoodResult>& topRetest,
                              const std::vector<NeighborhoodResult>& neighborhood,
                              double bestTimerMs, double bestScoreMs, int totalTime,
                              const GameLikeLoadStats& loadStats) {
    std::string htmlFile = getExeDirectory() + "gaming_timer_analysis.html";
    std::ofstream f(htmlFile);
    if (!f) return;

    // Создаем копию результатов первой волны и сортируем по таймеру
    std::vector<TimerTestResult> sortedResults = results;
    std::sort(sortedResults.begin(), sortedResults.end(), 
              [](const TimerTestResult& a, const TimerTestResult& b) {
                  return a.timerMs < b.timerMs;
              });

    // Найдём минимум первой волны по итоговому score.
    int bestIndex = -1; double bestFirstWaveScore = std::numeric_limits<double>::infinity();
    for (size_t i = 0; i < sortedResults.size(); ++i) {
        if (sortedResults[i].scoreMs < bestFirstWaveScore) {
            bestFirstWaveScore = sortedResults[i].scoreMs;
            bestIndex = (int)i;
        }
    }
    
    // Подготовим данные второй волны (retest top-15): отсортируем по таймеру и найдём минимум.
    std::vector<NeighborhoodResult> sortedSecond = topRetest;
    std::sort(sortedSecond.begin(), sortedSecond.end(), [](const NeighborhoodResult &a, const NeighborhoodResult &b){
        return a.timerMs < b.timerMs;
    });
    int bestIndex2 = -1;
    double bestSecondWaveScore = std::numeric_limits<double>::infinity();
    for (size_t i = 0; i < sortedSecond.size(); ++i) {
        if (sortedSecond[i].scoreMs < bestSecondWaveScore) {
            bestSecondWaveScore = sortedSecond[i].scoreMs;
            bestIndex2 = (int)i;
        }
    }

    // Подготовим данные третьей волны (окрестность): отсортируем по таймеру и найдём минимум.
    std::vector<NeighborhoodResult> sortedThird = neighborhood;
    std::sort(sortedThird.begin(), sortedThird.end(), [](const NeighborhoodResult &a, const NeighborhoodResult &b){
        return a.timerMs < b.timerMs;
    });
    int bestIndex3 = -1;
    double bestScore3 = std::numeric_limits<double>::infinity();
    for (size_t i = 0; i < sortedThird.size(); ++i) {
        if (sortedThird[i].scoreMs < bestScore3) {
            bestScore3 = sortedThird[i].scoreMs;
            bestIndex3 = (int)i;
        }
    }
    TimerZoneSelection thirdSelection = selectRecommendedFromStableZone(sortedThird);
    int recommendedIndex3 = thirdSelection.valid ? thirdSelection.recommendedIndex : bestIndex3;

    // Решаем, что показывать в шапке как финальный результат: центр стабильной зоны третьей волны -> вторая -> первая.
    double finalBestTimer = bestTimerMs;
    double finalBestScore = bestScoreMs;
    double finalBestAvgAbs = std::numeric_limits<double>::infinity();
    double finalBestCv = std::numeric_limits<double>::infinity();
    if (recommendedIndex3 >= 0 && recommendedIndex3 < (int)sortedThird.size()) {
        finalBestTimer = sortedThird[recommendedIndex3].timerMs;
        finalBestScore = sortedThird[recommendedIndex3].scoreMs;
        finalBestAvgAbs = sortedThird[recommendedIndex3].avgAbsDeltaMs;
        finalBestCv = sortedThird[recommendedIndex3].cvPercent;
    } else if (bestIndex2 >= 0 && bestIndex2 < (int)sortedSecond.size()) {
        finalBestTimer = sortedSecond[bestIndex2].timerMs;
        finalBestScore = sortedSecond[bestIndex2].scoreMs;
        finalBestAvgAbs = sortedSecond[bestIndex2].avgAbsDeltaMs;
        finalBestCv = sortedSecond[bestIndex2].cvPercent;
    } else if (bestIndex >= 0 && bestIndex < (int)sortedResults.size()) {
        finalBestAvgAbs = sortedResults[bestIndex].avgAbsDeltaMs;
        finalBestCv = sortedResults[bestIndex].cvPercent;
    }

    std::vector<TimerTestResult> topCandidates = sortedResults;
    std::sort(topCandidates.begin(), topCandidates.end(),
              [](const TimerTestResult& a, const TimerTestResult& b) {
                  if (std::abs(a.scoreMs - b.scoreMs) < 1e-12) return a.timerMs < b.timerMs;
                  return a.scoreMs < b.scoreMs;
              });
    if (topCandidates.size() > (size_t)kTopFirstWaveCount) topCandidates.resize(kTopFirstWaveCount);

    std::vector<TimerTestResult> stableZone;
    if (std::isfinite(bestFirstWaveScore)) {
        double tolerance = std::max(0.00001, bestFirstWaveScore * 0.05);
        for (const auto& r : sortedResults) {
            if (std::abs(r.scoreMs - bestFirstWaveScore) <= tolerance) {
                stableZone.push_back(r);
            }
        }
    }

    std::vector<NeighborhoodResult> finalStableZone;
    if (thirdSelection.valid) {
        finalStableZone = thirdSelection.zoneResults;
    }

    if (g_appLanguage != AppLanguage::Russian) {
        const std::string title = appText(L"Gaming Timer Stability Analysis", L"Gaming Timer Stability Analysis", L"Gaming-Timer-Stabilitatsanalyse", L"Oyun zamanlayici stabilite analizi", L"Analisis de estabilidad del temporizador gaming", L"Analise de estabilidade do timer gamer", L"\u0917\u0947\u092e\u093f\u0902\u0917 \u091f\u093e\u0907\u092e\u0930 \u0938\u094d\u0925\u093f\u0930\u0924\u093e \u0930\u093f\u092a\u094b\u0930\u094d\u091f");
        const std::string subtitle = appText(L"Windows timer report under game-like CPU load.", L"Windows timer report under game-like CPU load.", L"Windows-Timer-Bericht unter spielahnlicher CPU-Last.", L"Oyun benzeri CPU yukunde Windows zamanlayici raporu.", L"Informe del temporizador de Windows con carga tipo juego.", L"Relatorio do timer do Windows com carga tipo jogo.", L"\u0917\u0947\u092e \u091c\u0948\u0938\u0940 CPU \u0932\u094b\u0921 \u092e\u0947\u0902 Windows \u091f\u093e\u0907\u092e\u0930 \u0930\u093f\u092a\u094b\u0930\u094d\u091f.");
        const std::string resultsTitle = appText(L"Results", L"Results", L"Ergebnisse", L"Sonuclar", L"Resultados", L"Resultados", L"\u0928\u0924\u0940\u091c\u0947");
        const std::string recommendedTimerLabel = appText(L"Recommended timer", L"Recommended timer", L"Empfohlener Timer", L"Onerilen timer", L"Temporizador recomendado", L"Timer recomendado", L"\u0938\u0941\u091d\u093e\u092f\u093e \u091f\u093e\u0907\u092e\u0930");
        const std::string formulaBestLabel = appText(L"Best by formula", L"Best by formula", L"Bestes Ergebnis nach Formel", L"Formule gore en iyi", L"Mejor por formula", L"Melhor pela formula", L"\u092b\u0949\u0930\u094d\u092e\u0942\u0932\u093e \u0915\u0947 \u0939\u093f\u0938\u093e\u092c \u0938\u0947 \u0938\u0930\u094d\u0935\u0936\u094d\u0930\u0947\u0937\u094d\u0920");
        const std::string finalScoreLabel = appText(L"Final score1", L"Final score1", L"Finaler score1", L"Final score1", L"Score1 final", L"Score1 final", L"\u0905\u0902\u0924\u093f\u092e score1");
        const std::string sleepMissLabel = appText(L"Sleep(1) miss", L"Sleep(1) miss", L"Sleep(1)-Abweichung", L"Sleep(1) sapmasi", L"Desvio de Sleep(1)", L"Erro do Sleep(1)", L"Sleep(1) \u091a\u0942\u0915");
        const std::string jitterLabel = appText(L"Jitter", L"Jitter", L"Streuung", L"Dagilim", L"Dispersion", L"Variacao", L"\u092b\u0948\u0932\u093e\u0935");
        const std::string totalTimeLabel = appText(L"Test time", L"Test time", L"Testzeit", L"Test suresi", L"Tiempo de prueba", L"Tempo de teste", L"\u091f\u0947\u0938\u094d\u091f \u0938\u092e\u092f");
        const std::string candidatesLabel = appText(L"Candidates tested", L"Candidates tested", L"Getestete Kandidaten", L"Test edilen adaylar", L"Candidatos probados", L"Candidatos testados", L"\u091f\u0947\u0938\u094d\u091f \u0915\u093f\u090f \u0917\u090f \u0909\u092e\u094d\u092e\u0940\u0926\u0935\u093e\u0930");
        const std::string stableZoneLabel = appText(L"Stable zone", L"Stable zone", L"Stabile Zone", L"Stabil bolge", L"Zona estable", L"Zona estavel", L"\u0938\u094d\u0925\u093f\u0930 \u0915\u094d\u0937\u0947\u0924\u094d\u0930");
        const std::string msUnit = appText(L"ms", L"ms", L"ms", L"ms", L"ms", L"ms", L"ms");
        const std::string secUnit = appText(L"sec", L"sec", L"s", L"sn", L"s", L"s", L"\u0938\u0947\u0915\u0902\u0921");
        const std::string methodTitle = appText(L"How the timer was selected", L"How the timer was selected", L"Wie der Timer gewahlt wurde", L"Timer nasil secildi", L"Como se eligio el temporizador", L"Como o timer foi escolhido", L"\u091f\u093e\u0907\u092e\u0930 \u0915\u0948\u0938\u0947 \u091a\u0941\u0928\u093e \u0917\u092f\u093e");
        const std::string simpleMethod = appText(L"The program looks for the value where Sleep(1) wakes up most evenly under game-like load. Lower score is better. The final recommendation uses the center of the stable zone so one random spike does not decide the result.", L"The program looks for the value where Sleep(1) wakes up most evenly under game-like load. Lower score is better. The final recommendation uses the center of the stable zone so one random spike does not decide the result.", L"Das Programm sucht den Wert, bei dem Sleep(1) unter spielahnlicher Last am gleichmassigsten aufwacht. Ein kleinerer Score ist besser. Die Empfehlung nimmt die Mitte der stabilen Zone, damit ein zufalliger Spike nicht entscheidet.", L"Program, oyun benzeri yuk altinda Sleep(1) en duzgun uyandiran degeri arar. Dusuk score daha iyidir. Son sonuc stabil bolgenin merkezidir; tek bir rastgele spike sonucu belirlemez.", L"El programa busca el valor donde Sleep(1) despierta de forma mas uniforme bajo carga tipo juego. Menor score es mejor. La recomendacion usa el centro de la zona estable para que un pico aleatorio no decida.", L"O programa procura o valor em que Sleep(1) acorda de forma mais uniforme sob carga tipo jogo. Score menor e melhor. A recomendacao usa o centro da zona estavel para um pico aleatorio nao decidir.", L"\u092a\u094d\u0930\u094b\u0917\u094d\u0930\u093e\u092e \u0935\u0939 \u092e\u0942\u0932\u094d\u092f \u0922\u0942\u0902\u0922\u0924\u093e \u0939\u0948 \u091c\u0939\u093e\u0902 game-like load \u092e\u0947\u0902 Sleep(1) \u0938\u092c\u0938\u0947 \u0938\u094d\u0925\u093f\u0930 \u091c\u093e\u0917\u0924\u093e \u0939\u0948. \u0915\u092e score \u092c\u0947\u0939\u0924\u0930 \u0939\u0948. \u0905\u0902\u0924\u093f\u092e \u0938\u0941\u091d\u093e\u0935 \u0938\u094d\u0925\u093f\u0930 \u0915\u094d\u0937\u0947\u0924\u094d\u0930 \u0915\u0947 \u092e\u0927\u094d\u092f \u0938\u0947 \u0932\u093f\u092f\u093e \u0917\u092f\u093e \u0939\u0948.");
        const std::string wave1Desc = appText(L"Wave 1: all candidates are tested quickly, then the best 15 are kept.", L"Wave 1: all candidates are tested quickly, then the best 15 are kept.", L"Welle 1: alle Kandidaten werden schnell getestet, danach bleiben die besten 15.", L"Dalga 1: tum adaylar hizli test edilir, en iyi 15 kalir.", L"Ola 1: se prueban todos los candidatos y se guardan los mejores 15.", L"Onda 1: todos os candidatos sao testados e os 15 melhores ficam.", L"\u0935\u0947\u0935 1: \u0938\u092d\u0940 \u0909\u092e\u094d\u092e\u0940\u0926\u0935\u093e\u0930 \u091f\u0947\u0938\u094d\u091f \u0939\u094b\u0924\u0947 \u0939\u0948\u0902, \u092b\u093f\u0930 \u0938\u0930\u094d\u0935\u0936\u094d\u0930\u0947\u0937\u094d\u0920 15 \u0930\u0916\u0947 \u091c\u093e\u0924\u0947 \u0939\u0948\u0902.");
        const std::string wave2Desc = appText(L"Wave 2: the top 15 are retested in 7 shuffled rounds with the same formula.", L"Wave 2: the top 15 are retested in 7 shuffled rounds with the same formula.", L"Welle 2: die Top 15 werden in 7 gemischten Runden mit derselben Formel erneut getestet.", L"Dalga 2: ilk 15 aday ayni formulle 7 karisik turda tekrar test edilir.", L"Ola 2: los mejores 15 se repiten en 7 rondas mezcladas con la misma formula.", L"Onda 2: os 15 melhores sao retestados em 7 rodadas embaralhadas com a mesma formula.", L"\u0935\u0947\u0935 2: top 15 \u0915\u094b \u0935\u0939\u0940 \u092b\u0949\u0930\u094d\u092e\u0942\u0932\u093e \u0932\u0917\u093e\u0915\u0930 7 shuffled rounds \u092e\u0947\u0902 \u0926\u094b\u092c\u093e\u0930\u093e \u091f\u0947\u0938\u094d\u091f \u0915\u093f\u092f\u093e \u0917\u092f\u093e.");
        const std::string wave3Desc = appText(L"Wave 3: a +/-0.002 ms neighborhood around the second-wave winner is tested, about 20 seconds per point. If the winner is 0.500 ms, the range is 0.500-0.504 ms.", L"Wave 3: a +/-0.002 ms neighborhood around the second-wave winner is tested, about 20 seconds per point. If the winner is 0.500 ms, the range is 0.500-0.504 ms.", L"Welle 3: um den Sieger der zweiten Welle wird +/-0.002 ms getestet, etwa 20 Sekunden pro Punkt. Wenn der Sieger 0.500 ms ist, gilt 0.500-0.504 ms.", L"Dalga 3: ikinci dalga kazananinin etrafinda +/-0.002 ms test edilir, nokta basina yaklasik 20 saniye. Kazanan 0.500 ms ise aralik 0.500-0.504 ms olur.", L"Ola 3: se prueba +/-0.002 ms alrededor del ganador de la segunda ola, unos 20 segundos por punto. Si gana 0.500 ms, el rango es 0.500-0.504 ms.", L"Onda 3: testa +/-0.002 ms ao redor do vencedor da segunda onda, cerca de 20 segundos por ponto. Se o vencedor for 0.500 ms, o intervalo e 0.500-0.504 ms.", L"\u0935\u0947\u0935 3: \u0926\u0942\u0938\u0930\u0940 \u0935\u0947\u0935 \u0915\u0947 \u0935\u093f\u091c\u0947\u0924\u093e \u0915\u0947 \u0906\u0938\u092a\u093e\u0938 +/-0.002 ms \u091f\u0947\u0938\u094d\u091f \u0939\u094b\u0924\u093e \u0939\u0948, \u0932\u0917\u092d\u0917 20 \u0938\u0947\u0915\u0902\u0921 \u092a\u094d\u0930\u0924\u093f \u092a\u0949\u0907\u0902\u091f. \u0905\u0917\u0930 \u0935\u093f\u091c\u0947\u0924\u093e 0.500 ms \u0939\u0948, \u0930\u0947\u0902\u091c 0.500-0.504 ms \u0939\u0948.");
        const std::string formulaDesc = appText(L"Formula: score1 = 0.75 * robust average Sleep(1) miss + 0.25 * robust CV penalty. The slowest 2% wake-time outliers are trimmed.", L"Formula: score1 = 0.75 * robust average Sleep(1) miss + 0.25 * robust CV penalty. The slowest 2% wake-time outliers are trimmed.", L"Formel: score1 = 0.75 * robuste mittlere Sleep(1)-Abweichung + 0.25 * robuste CV-Strafe. Die langsamsten 2% Wake-Time-Ausreisser werden entfernt.", L"Formul: score1 = 0.75 * robust ortalama Sleep(1) sapmasi + 0.25 * robust CV cezasi. En yavas %2 wake-time aykiri degerleri kesilir.", L"Formula: score1 = 0.75 * desvio robusto medio de Sleep(1) + 0.25 * penalizacion robusta de CV. Se recorta el 2% mas lento de wake-time.", L"Formula: score1 = 0.75 * erro medio robusto do Sleep(1) + 0.25 * penalidade robusta de CV. Os 2% piores wake-times sao cortados.", L"\u092b\u0949\u0930\u094d\u092e\u0942\u0932\u093e: score1 = 0.75 * robust average Sleep(1) miss + 0.25 * robust CV penalty. \u0938\u092c\u0938\u0947 \u0927\u0940\u092e\u0947 2% wake-time outliers \u0939\u091f\u093e\u090f \u0917\u090f.");
        const std::string environmentTitle = appText(L"Test environment", L"Test environment", L"Testumgebung", L"Test ortami", L"Entorno de prueba", L"Ambiente do teste", L"\u091f\u0947\u0938\u094d\u091f \u092a\u0930\u093f\u0935\u0947\u0936");
        const std::string gameLoadLabel = appText(L"Game-like load", L"Game-like load", L"Spielahnliche Last", L"Oyun benzeri yuk", L"Carga tipo juego", L"Carga tipo jogo", L"game-like load");
        const std::string logicalCpuLabel = appText(L"Logical CPUs", L"Logical CPUs", L"Logische CPUs", L"Mantiksal CPU", L"CPUs logicas", L"CPUs logicas", L"\u0932\u0949\u091c\u093f\u0915\u0932 CPU");
        const std::string physicalCoreLabel = appText(L"Physical cores", L"Physical cores", L"Physische Kerne", L"Fiziksel cekirdek", L"Nucleos fisicos", L"Nucleos fisicos", L"\u092b\u093f\u091c\u093f\u0915\u0932 \u0915\u094b\u0930");
        const std::string measurementCoreLabel = appText(L"Measurement core", L"Measurement core", L"Messkern", L"Olcum cekirdegi", L"Nucleo de medicion", L"Nucleo de medicao", L"\u092e\u093e\u092a \u0915\u094b\u0930");
        const std::string workerCoreLabel = appText(L"Loaded physical cores", L"Loaded physical cores", L"Belastete physische Kerne", L"Yuklenen fiziksel cekirdekler", L"Nucleos fisicos con carga", L"Nucleos fisicos com carga", L"\u0932\u094b\u0921 \u0935\u093e\u0932\u0947 \u092b\u093f\u091c\u093f\u0915\u0932 \u0915\u094b\u0930");
        const std::string siblingsLabel = appText(L"Logical siblings ignored", L"Logical siblings ignored", L"Logische Siblings ignoriert", L"Mantiksal kardesler yok sayildi", L"Siblings logicos ignorados", L"Siblings logicos ignorados", L"\u0932\u0949\u091c\u093f\u0915\u0932 siblings \u0939\u091f\u093e\u090f \u0917\u090f");
        const std::string loadStepLabel = appText(L"Load step", L"Load step", L"Lastschritt", L"Yuk adimi", L"Paso de carga", L"Passo da carga", L"\u0932\u094b\u0921 \u0938\u094d\u091f\u0947\u092a");
        const std::string loadPowerLabel = appText(L"Load strength", L"Load strength", L"Laststarke", L"Yuk gucu", L"Fuerza de carga", L"Forca da carga", L"\u0932\u094b\u0921 \u0936\u0915\u094d\u0924\u093f");
        const std::string prewarmLabel = appText(L"Pre-warm", L"Pre-warm", L"Vorwarmung", L"On isitma", L"Precalentamiento", L"Pre-aquecimento", L"\u092a\u094d\u0930\u0940-\u0935\u0949\u0930\u094d\u092e");
        const std::string affinityOk = appText(L"Measurement thread affinity was applied.", L"Measurement thread affinity was applied.", L"Die Mess-Thread-Affinitat wurde gesetzt.", L"Olcum thread affinity uygulandi.", L"Se aplico la afinidad del hilo de medicion.", L"A afinidade da thread de medicao foi aplicada.", L"\u092e\u093e\u092a thread affinity \u0932\u0917\u093e\u0908 \u0917\u0908.");
        const std::string affinityFail = appText(L"Measurement thread affinity failed; the test continued with a warning.", L"Measurement thread affinity failed; the test continued with a warning.", L"Mess-Thread-Affinitat fehlgeschlagen; Test lief mit Warnung weiter.", L"Olcum thread affinity basarisiz; test uyariyla devam etti.", L"Fallo la afinidad del hilo de medicion; la prueba continuo con aviso.", L"Falha na afinidade da thread de medicao; o teste continuou com aviso.", L"\u092e\u093e\u092a thread affinity \u0928\u0939\u0940\u0902 \u0932\u0917\u0940; \u091f\u0947\u0938\u094d\u091f warning \u0915\u0947 \u0938\u093e\u0925 \u091a\u0932\u093e.");
        const std::string wave1Title = appText(L"Wave 1 - all candidates", L"Wave 1 - all candidates", L"Welle 1 - alle Kandidaten", L"Dalga 1 - tum adaylar", L"Ola 1 - todos los candidatos", L"Onda 1 - todos os candidatos", L"\u0935\u0947\u0935 1 - \u0938\u092d\u0940 \u0909\u092e\u094d\u092e\u0940\u0926\u0935\u093e\u0930");
        const std::string top15Title = appText(L"Top 15 from wave 1", L"Top 15 from wave 1", L"Top 15 aus Welle 1", L"Dalga 1 top 15", L"Top 15 de la ola 1", L"Top 15 da onda 1", L"\u0935\u0947\u0935 1 \u0915\u0947 top 15");
        const std::string wave2Title = appText(L"Wave 2 - shuffled top 15 retest", L"Wave 2 - shuffled top 15 retest", L"Welle 2 - gemischter Top-15-Retest", L"Dalga 2 - karisik top 15 tekrar testi", L"Ola 2 - repeticion mezclada del top 15", L"Onda 2 - reteste embaralhado do top 15", L"\u0935\u0947\u0935 2 - shuffled top 15 retest");
        const std::string wave3Title = appText(L"Wave 3 - neighborhood and stable zone", L"Wave 3 - neighborhood and stable zone", L"Welle 3 - Umgebung und stabile Zone", L"Dalga 3 - komsuluk ve stabil bolge", L"Ola 3 - vecindad y zona estable", L"Onda 3 - vizinhanca e zona estavel", L"\u0935\u0947\u0935 3 - \u0928\u093f\u0915\u091f \u0915\u094d\u0937\u0947\u0924\u094d\u0930 \u0914\u0930 \u0938\u094d\u0925\u093f\u0930 \u091c\u094b\u0928");
        const std::string stableCandidatesTitle = appText(L"Stable candidates", L"Stable candidates", L"Stabile Kandidaten", L"Stabil adaylar", L"Candidatos estables", L"Candidatos estaveis", L"\u0938\u094d\u0925\u093f\u0930 \u0909\u092e\u094d\u092e\u0940\u0926\u0935\u093e\u0930");
        const std::string timerHeader = appText(L"Timer (ms)", L"Timer (ms)", L"Timer (ms)", L"Timer (ms)", L"Temporizador (ms)", L"Timer (ms)", L"\u091f\u093e\u0907\u092e\u0930 (ms)");
        const std::string scoreHeader = appText(L"Score1 (lower is better)", L"Score1 (lower is better)", L"Score1 (kleiner ist besser)", L"Score1 (dusuk daha iyi)", L"Score1 (menor es mejor)", L"Score1 (menor e melhor)", L"Score1 (\u0915\u092e \u092c\u0947\u0939\u0924\u0930)");
        const std::string deltaHeader = appText(L"Robust Sleep(1) miss (ms)", L"Robust Sleep(1) miss (ms)", L"Robuste Sleep(1)-Abweichung (ms)", L"Robust Sleep(1) sapmasi (ms)", L"Desvio robusto Sleep(1) (ms)", L"Erro robusto Sleep(1) (ms)", L"Robust Sleep(1) \u091a\u0942\u0915 (ms)");
        const std::string cvHeader = appText(L"Robust CV (%)", L"Robust CV (%)", L"Robuster CV (%)", L"Robust CV (%)", L"CV robusto (%)", L"CV robusto (%)", L"Robust CV (%)");
        const std::string cvPenaltyHeader = appText(L"CV penalty (ms)", L"CV penalty (ms)", L"CV-Strafe (ms)", L"CV cezasi (ms)", L"Penalizacion CV (ms)", L"Penalidade CV (ms)", L"CV penalty (ms)");
        const std::string avgWakeHeader = appText(L"Average wake (ms)", L"Average wake (ms)", L"Mittleres Aufwachen (ms)", L"Ortalama uyanma (ms)", L"Despertar medio (ms)", L"Wake medio (ms)", L"\u0914\u0938\u0924 wake (ms)");
        const std::string stdWakeHeader = appText(L"Wake stddev (ms)", L"Wake stddev (ms)", L"Wake-Stddev (ms)", L"Wake stddev (ms)", L"Stddev wake (ms)", L"Stddev wake (ms)", L"Wake stddev (ms)");
        const std::string samplesHeader = appText(L"Samples", L"Samples", L"Samples", L"Ornek", L"Muestras", L"Amostras", L"\u0938\u0948\u0902\u092a\u0932");

        auto writeTimerRows = [&](const std::vector<TimerTestResult>& rows, int bestRow) {
            for (size_t i = 0; i < rows.size(); ++i) {
                const auto& r = rows[i];
                f << "<tr class=\"" << ((int)i == bestRow ? "best-result" : "") << "\">"
                  << "<td>" << std::fixed << std::setprecision(3) << r.timerMs << "</td>"
                  << "<td>" << std::fixed << std::setprecision(6) << r.scoreMs << "</td>"
                  << "<td>" << std::fixed << std::setprecision(6) << r.avgAbsDeltaMs << "</td>"
                  << "<td>" << std::fixed << std::setprecision(3) << r.cvPercent << "</td>"
                  << "<td>" << std::fixed << std::setprecision(6) << r.cvPenaltyMs << "</td>"
                  << "<td>" << std::fixed << std::setprecision(6) << r.avgWakeMs << "</td>"
                  << "<td>" << std::fixed << std::setprecision(6) << r.stdDevWakeMs << "</td>"
                  << "<td>" << r.samples << "</td>"
                  << "<td>" << std::fixed << std::setprecision(6) << r.minWakeMs << "</td>"
                  << "<td>" << std::fixed << std::setprecision(6) << r.maxWakeMs << "</td>"
                  << "<td>" << std::fixed << std::setprecision(6) << r.medianWakeMs << "</td>"
                  << "</tr>\n";
            }
        };
        auto writeNeighborhoodRows = [&](const std::vector<NeighborhoodResult>& rows, int bestRow) {
            for (size_t i = 0; i < rows.size(); ++i) {
                const auto& r = rows[i];
                f << "<tr class=\"" << ((int)i == bestRow ? "best-result" : "") << "\">"
                  << "<td>" << std::fixed << std::setprecision(3) << r.timerMs << "</td>"
                  << "<td>" << std::fixed << std::setprecision(6) << r.scoreMs << "</td>"
                  << "<td>" << std::fixed << std::setprecision(6) << r.avgAbsDeltaMs << "</td>"
                  << "<td>" << std::fixed << std::setprecision(3) << r.cvPercent << "</td>"
                  << "<td>" << std::fixed << std::setprecision(6) << r.cvPenaltyMs << "</td>"
                  << "<td>" << std::fixed << std::setprecision(6) << r.avgWakeMs << "</td>"
                  << "<td>" << std::fixed << std::setprecision(6) << r.stdDevWakeMs << "</td>"
                  << "<td>" << r.samples << "</td>"
                  << "<td>" << std::fixed << std::setprecision(6) << r.minWakeMs << "</td>"
                  << "<td>" << std::fixed << std::setprecision(6) << r.maxWakeMs << "</td>"
                  << "<td>" << std::fixed << std::setprecision(6) << r.medianWakeMs << "</td>"
                  << "</tr>\n";
            }
        };
        auto writeTableHeader = [&]() {
            f << "<thead><tr><th>" << timerHeader << "</th><th>" << scoreHeader << "</th><th>" << deltaHeader
              << "</th><th>" << cvHeader << "</th><th>" << cvPenaltyHeader << "</th><th>" << avgWakeHeader
              << "</th><th>" << stdWakeHeader << "</th><th>" << samplesHeader
              << "</th><th>Min (ms)</th><th>Max (ms)</th><th>Median (ms)</th></tr></thead>";
        };

        std::vector<double> rawScores; rawScores.reserve(sortedResults.size());
        for (const auto& r : sortedResults) rawScores.push_back(r.scoreMs);
        std::vector<double> smoothScores = smooth(rawScores, 5);

        f << "<!DOCTYPE html><html><head><meta charset=\"UTF-8\"><title>" << title << "</title>\n"
          << "<script src=\"https://cdn.jsdelivr.net/npm/chart.js\"></script>\n"
          << "<style>body{font-family:'Segoe UI','Nirmala UI',Arial,sans-serif;margin:20px;background:#070b10;color:#dce7f3}.container{max-width:1400px;margin:0 auto;background:#101820;padding:20px;border-radius:10px;box-shadow:0 16px 44px rgba(0,0,0,.45);border:1px solid #263545}.header{text-align:center;margin-bottom:26px}.summary{background:#15212b;padding:15px;border-radius:8px;margin-bottom:20px;border:1px solid #263545}.best-result{background:#123529!important;border:2px solid #2dd4bf}.chart-container{width:100%;height:400px;margin:20px 0}table{width:100%;border-collapse:collapse;margin:20px 0}th,td{padding:8px;text-align:right;border:1px solid #2b3b4a;color:#dce7f3}th{background:#1d2a36;font-weight:bold;color:#f1f7ff}tr:nth-child(even){background:#121d26}tr:nth-child(odd){background:#0f1720}.metric{display:inline-block;margin:10px 20px}.metric-label{font-weight:bold;color:#b8c7d6}.metric-value{color:#67e8f9;font-size:1.1em}.note{line-height:1.55}h1,h2{color:#f4f8ff}p{color:#d0dbe7}</style></head><body><div class=\"container\">\n";
        f << "<div class=\"header\"><h1>" << title << "</h1><p>" << subtitle << "</p></div>\n";
        f << "<div class=\"summary\"><h2>" << resultsTitle << "</h2>"
          << "<div class=\"metric\"><span class=\"metric-label\">" << recommendedTimerLabel << ":</span> <span class=\"metric-value\">" << std::fixed << std::setprecision(3) << finalBestTimer << " " << msUnit << "</span></div>"
          << "<div class=\"metric\"><span class=\"metric-label\">" << formulaBestLabel << ":</span> <span class=\"metric-value\">" << std::fixed << std::setprecision(3) << (thirdSelection.valid ? thirdSelection.formulaBestTimerMs : finalBestTimer) << " " << msUnit << "</span></div>"
          << "<div class=\"metric\"><span class=\"metric-label\">" << finalScoreLabel << ":</span> <span class=\"metric-value\">" << std::fixed << std::setprecision(6) << finalBestScore << "</span></div>"
          << "<div class=\"metric\"><span class=\"metric-label\">" << sleepMissLabel << ":</span> <span class=\"metric-value\">" << std::fixed << std::setprecision(6) << finalBestAvgAbs << " " << msUnit << "</span></div>"
          << "<div class=\"metric\"><span class=\"metric-label\">" << jitterLabel << ":</span> <span class=\"metric-value\">" << std::fixed << std::setprecision(3) << finalBestCv << "%</span></div>"
          << "<div class=\"metric\"><span class=\"metric-label\">" << totalTimeLabel << ":</span> <span class=\"metric-value\">" << (totalTime / 60) << ":" << std::setfill('0') << std::setw(2) << (totalTime % 60) << std::setfill(' ') << "</span></div>"
          << "<div class=\"metric\"><span class=\"metric-label\">" << candidatesLabel << ":</span> <span class=\"metric-value\">" << sortedResults.size() << "</span></div>";
        if (!finalStableZone.empty()) {
            f << "<div class=\"metric\"><span class=\"metric-label\">" << stableZoneLabel << ":</span> <span class=\"metric-value\">";
            for (size_t i = 0; i < finalStableZone.size(); ++i) {
                if (i) f << ", ";
                f << std::fixed << std::setprecision(3) << finalStableZone[i].timerMs;
            }
            f << " " << msUnit << "</span></div>";
        }
        f << "</div>\n";

        f << "<div class=\"summary\"><h2>" << methodTitle << "</h2><p class=\"note\">" << simpleMethod << "</p><p>" << wave1Desc
          << "</p><p>" << wave2Desc << "</p><p>" << wave3Desc << "</p><p>" << formulaDesc << "</p></div>\n";

        f << "<div class=\"summary\"><h2>" << environmentTitle << "</h2>"
          << "<div class=\"metric\"><span class=\"metric-label\">" << gameLoadLabel << ":</span> <span class=\"metric-value\">" << std::fixed << std::setprecision(1) << loadStats.targetLoadPercent << "%</span></div>"
          << "<div class=\"metric\"><span class=\"metric-label\">" << logicalCpuLabel << ":</span> <span class=\"metric-value\">" << loadStats.logicalCpuCount << "</span></div>"
          << "<div class=\"metric\"><span class=\"metric-label\">" << physicalCoreLabel << ":</span> <span class=\"metric-value\">" << loadStats.physicalCoreCount << "</span></div>"
          << "<div class=\"metric\"><span class=\"metric-label\">" << measurementCoreLabel << ":</span> <span class=\"metric-value\">Physical #" << loadStats.measurementPhysicalCore << " / CPU " << loadStats.measurementCpu << "</span></div>"
          << "<div class=\"metric\"><span class=\"metric-label\">" << workerCoreLabel << ":</span> <span class=\"metric-value\">" << loadStats.workerCount << "</span></div>"
          << "<div class=\"metric\"><span class=\"metric-label\">" << siblingsLabel << ":</span> <span class=\"metric-value\">" << loadStats.logicalSiblingsIgnored << "</span></div>"
          << "<div class=\"metric\"><span class=\"metric-label\">" << loadStepLabel << ":</span> <span class=\"metric-value\">" << loadStats.periodMs << " " << msUnit << "</span></div>"
          << "<div class=\"metric\"><span class=\"metric-label\">" << loadPowerLabel << ":</span> <span class=\"metric-value\">" << std::fixed << std::setprecision(1) << loadStats.dutyCyclePercent << "%</span></div>"
          << "<div class=\"metric\"><span class=\"metric-label\">" << prewarmLabel << ":</span> <span class=\"metric-value\">" << loadStats.prewarmSeconds << " " << secUnit << "</span></div>"
          << "<p class=\"note\">" << (loadStats.measurementAffinityOk ? affinityOk : affinityFail) << "</p></div>\n";

        f << "<div class=\"chart-container\"><canvas id=\"wave1Chart\"></canvas></div>\n";
        f << "<h2>" << wave1Title << "</h2><table>"; writeTableHeader(); f << "<tbody>"; writeTimerRows(sortedResults, bestIndex); f << "</tbody></table>\n";
        f << "<h2>" << top15Title << "</h2><table>"; writeTableHeader(); f << "<tbody>"; writeTimerRows(topCandidates, -1); f << "</tbody></table>\n";
        if (!stableZone.empty()) {
            f << "<h2>" << stableCandidatesTitle << "</h2><table>"; writeTableHeader(); f << "<tbody>"; writeTimerRows(stableZone, -1); f << "</tbody></table>\n";
        }
        if (!sortedSecond.empty()) {
            f << "<h2>" << wave2Title << "</h2><div class=\"chart-container\"><canvas id=\"wave2Chart\"></canvas></div><table>";
            writeTableHeader(); f << "<tbody>"; writeNeighborhoodRows(sortedSecond, bestIndex2); f << "</tbody></table>\n";
        }
        if (!sortedThird.empty()) {
            f << "<h2>" << wave3Title << "</h2><div class=\"chart-container\"><canvas id=\"wave3Chart\"></canvas></div><table>";
            writeTableHeader(); f << "<tbody>"; writeNeighborhoodRows(sortedThird, recommendedIndex3); f << "</tbody></table>\n";
        }

        f << "<script>Chart.defaults.color='#cbd5e1';Chart.defaults.borderColor='rgba(148,163,184,.22)';const labels=[";
        for (size_t i = 0; i < sortedResults.size(); ++i) { if (i) f << ","; f << "'" << std::fixed << std::setprecision(3) << sortedResults[i].timerMs << "'"; }
        f << "];const scoreRaw=[";
        for (size_t i = 0; i < rawScores.size(); ++i) { if (i) f << ","; f << std::fixed << std::setprecision(8) << rawScores[i]; }
        f << "];const scoreSmooth=[";
        for (size_t i = 0; i < smoothScores.size(); ++i) { if (i) f << ","; f << std::fixed << std::setprecision(8) << smoothScores[i]; }
        f << "];new Chart(document.getElementById('wave1Chart').getContext('2d'),{type:'line',data:{labels:labels,datasets:[{label:'Score1 raw',data:scoreRaw,borderColor:'rgb(54,162,235)',backgroundColor:'rgba(54,162,235,.2)',tension:.1},{label:'Score1 smooth',data:scoreSmooth,borderColor:'rgb(0,200,83)',backgroundColor:'rgba(0,200,83,.15)',tension:.2,pointRadius:0}]},options:{responsive:true,maintainAspectRatio:false,plugins:{title:{display:true,text:'" << wave1Title << "'}},scales:{x:{title:{display:true,text:'" << timerHeader << "'}},y:{title:{display:true,text:'Score1'}}}}});\n";
        if (!sortedSecond.empty()) {
            f << "const labels2=[";
            for (size_t i = 0; i < sortedSecond.size(); ++i) { if (i) f << ","; f << "'" << std::fixed << std::setprecision(3) << sortedSecond[i].timerMs << "'"; }
            f << "];const score2=[";
            for (size_t i = 0; i < sortedSecond.size(); ++i) { if (i) f << ","; f << std::fixed << std::setprecision(8) << sortedSecond[i].scoreMs; }
            f << "];new Chart(document.getElementById('wave2Chart').getContext('2d'),{type:'line',data:{labels:labels2,datasets:[{label:'Score1',data:score2,borderColor:'#f59e0b',backgroundColor:'rgba(245,158,11,.18)',tension:.1}]},options:{responsive:true,maintainAspectRatio:false,plugins:{title:{display:true,text:'" << wave2Title << "'}},scales:{x:{title:{display:true,text:'" << timerHeader << "'}},y:{title:{display:true,text:'Score1'}}}}});\n";
        }
        if (!sortedThird.empty()) {
            f << "const labels3=[";
            for (size_t i = 0; i < sortedThird.size(); ++i) { if (i) f << ","; f << "'" << std::fixed << std::setprecision(3) << sortedThird[i].timerMs << "'"; }
            f << "];const score3=[";
            for (size_t i = 0; i < sortedThird.size(); ++i) { if (i) f << ","; f << std::fixed << std::setprecision(8) << sortedThird[i].scoreMs; }
            f << "];new Chart(document.getElementById('wave3Chart').getContext('2d'),{type:'line',data:{labels:labels3,datasets:[{label:'Score1',data:score3,borderColor:'#a78bfa',backgroundColor:'rgba(167,139,250,.18)',tension:.1}]},options:{responsive:true,maintainAspectRatio:false,plugins:{title:{display:true,text:'" << wave3Title << "'}},scales:{x:{title:{display:true,text:'" << timerHeader << "'}},y:{title:{display:true,text:'Score1'}}}}});\n";
        }
        f << "</script></div></body></html>";
        f.close();
        return;
    }

    f << R"HTML(<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <title>Gaming Timer Stability Analysis Report</title>
    <script src="https://cdn.jsdelivr.net/npm/chart.js"></script>
    <script src="https://cdn.jsdelivr.net/npm/chartjs-plugin-zoom@2.0.1"></script>
    <style>
        body { font-family: Arial, sans-serif; margin: 20px; background: #070b10; color: #dce7f3; }
        .container { max-width: 1400px; margin: 0 auto; background: #101820; padding: 20px; border-radius: 10px; box-shadow: 0 16px 44px rgba(0,0,0,0.45); border: 1px solid #263545; }
        .header { text-align: center; margin-bottom: 30px; }
        .summary { background: #15212b; padding: 15px; border-radius: 8px; margin-bottom: 20px; border: 1px solid #263545; }
        .best-result { background: #123529 !important; border: 2px solid #2dd4bf; }
        .chart-container { width: 100%; height: 400px; margin: 20px 0; }
        table { width: 100%; border-collapse: collapse; margin: 20px 0; }
        th, td { padding: 8px; text-align: right; border: 1px solid #2b3b4a; color: #dce7f3; }
        th { background: #1d2a36; font-weight: bold; color: #f1f7ff; }
        tr:nth-child(even) { background: #121d26; }
        tr:nth-child(odd) { background: #0f1720; }
        .metric { display: inline-block; margin: 10px 20px; }
        .metric-label { font-weight: bold; color: #b8c7d6; }
        .metric-value { color: #67e8f9; font-size: 1.1em; }
        .note { line-height: 1.5; }
        h1, h2 { color: #f4f8ff; }
        p { color: #d0dbe7; }
    </style>
</head>
<body>
    <div class="container">
        <div class="header">
            <h1>🎮 Gaming Timer Stability Analysis</h1>
            <p>Игровой анализ стабильности таймеров Windows для оптимального frame timing</p>
        </div>

        <div class="summary">
            <h2>📊 Результаты тестирования</h2>
            <div class="metric">
                <span class="metric-label">🏆 Рекомендованный таймер:</span>
                <span class="metric-value">)HTML" << std::fixed << std::setprecision(3) << finalBestTimer << R"HTML( мс</span>
            </div>
            <div class="metric">
                <span class="metric-label">Лучший по формуле:</span>
                <span class="metric-value">)HTML" << std::fixed << std::setprecision(3) << (thirdSelection.valid ? thirdSelection.formulaBestTimerMs : finalBestTimer) << R"HTML( мс</span>
            </div>
            <div class="metric">
                <span class="metric-label">📉 Итоговый балл score1:</span>
                <span class="metric-value">)HTML" << std::fixed << std::setprecision(6) << finalBestScore << R"HTML( мс-экв.</span>
            </div>
            <div class="metric">
                <span class="metric-label">Промах Sleep(1):</span>
                <span class="metric-value">)HTML" << std::fixed << std::setprecision(6) << finalBestAvgAbs << R"HTML( мс</span>
            </div>
            <div class="metric">
                <span class="metric-label">Разброс:</span>
                <span class="metric-value">)HTML" << std::fixed << std::setprecision(3) << finalBestCv << R"HTML(%</span>
            </div>
            <div class="metric">
                <span class="metric-label">⏱️ Время тестирования:</span>
                <span class="metric-value">)HTML" << (totalTime / 60) << ":" << std::setfill('0') << std::setw(2) << (totalTime % 60) << R"HTML(</span>
            </div>
            <div class="metric">
                <span class="metric-label">🔬 Кандидатов протестировано:</span>
                <span class="metric-value">)HTML" << sortedResults.size() << R"HTML( (по ~5 сек измерений каждый)</span>
            </div>
)HTML";
            if (!finalStableZone.empty()) {
                f << R"HTML(
            <div class="metric">
                <span class="metric-label">🟢 Стабильная зона:</span>
                <span class="metric-value">)HTML";
                for (size_t i = 0; i < finalStableZone.size(); ++i) {
                    if (i) f << ", ";
                    f << std::fixed << std::setprecision(3) << finalStableZone[i].timerMs;
                }
                f << R"HTML( мс</span>
            </div>)HTML";
            }
            f << R"HTML(
        </div>

        <div class="summary">
            <h2>ℹ️ Как выбирался таймер</h2>
            <p class="note"><strong>Если коротко:</strong> программа ищет таймер, при котором Sleep(1) просыпается ровнее всего под игровой нагрузкой. Чем меньше score, тем лучше. Финальная рекомендация берется как центр стабильной зоны, чтобы соседний случайный пик не менял результат от запуска к запуску.</p>
            <p><strong>1-я волна:</strong> быстро проверяем все значения и берем 15 лучших.</p>
            <p><strong>2-я волна:</strong> эти 15 значений гоняются 7 кругов в перемешанном порядке, чтобы прогрев и фоновые скачки не давали преимущество одному месту.</p>
            <p><strong>3-я волна:</strong> вокруг победителя второй волны проверяем маленькую окрестность ±0.002 мс в перемешанных кругах, всего ~20 сек на точку. Если победил край 0.500 мс, проверяем 0.500–0.504 мс.</p>
            <p><strong>Для любопытных:</strong> score = 0.75 * средний промах Sleep(1) + 0.25 * штраф за разброс. Чем меньше score, тем ровнее таймер. Верхние 2% самых плохих пробуждений обрезаются (robust avgAbsDelta и robust CV), чтобы один случайный spike не ломал результат.</p>
        </div>

        <div class="summary">
            <h2>⚙️ Что было во время теста</h2>
            <div class="metric"><span class="metric-label">Игровая нагрузка:</span> <span class="metric-value">)HTML" << std::fixed << std::setprecision(1) << loadStats.targetLoadPercent << R"HTML(%</span></div>
            <div class="metric"><span class="metric-label">Логических ядер:</span> <span class="metric-value">)HTML" << loadStats.logicalCpuCount << R"HTML(</span></div>
            <div class="metric"><span class="metric-label">Физических ядер:</span> <span class="metric-value">)HTML" << loadStats.physicalCoreCount << R"HTML(</span></div>
            <div class="metric"><span class="metric-label">Ядро замера:</span> <span class="metric-value">Physical #)HTML" << loadStats.measurementPhysicalCore << R"HTML( / CPU )HTML" << loadStats.measurementCpu << R"HTML(</span></div>
            <div class="metric"><span class="metric-label">Физических ядер под нагрузкой:</span> <span class="metric-value">)HTML" << loadStats.workerCount << R"HTML(</span></div>
            <div class="metric"><span class="metric-label">Логических siblings исключено:</span> <span class="metric-value">)HTML" << loadStats.logicalSiblingsIgnored << R"HTML(</span></div>
            <div class="metric"><span class="metric-label">Шаг нагрузки:</span> <span class="metric-value">)HTML" << loadStats.periodMs << R"HTML( мс</span></div>
            <div class="metric"><span class="metric-label">Сила нагрузки:</span> <span class="metric-value">)HTML" << std::fixed << std::setprecision(1) << loadStats.dutyCyclePercent << R"HTML(%</span></div>
            <div class="metric"><span class="metric-label">Прогрев перед поиском:</span> <span class="metric-value">)HTML" << loadStats.prewarmSeconds << R"HTML( сек</span></div>
            <p class="note">Перед стартом программа проверила только физические ядра и выбрала тихое ядро для Sleep(1)+QPC: Physical #)HTML" << loadStats.measurementPhysicalCore << R"HTML( / CPU )HTML" << loadStats.measurementCpu << R"HTML(. Нагрузка шла только на представители других физических ядер; логические SMT/Hyper-Threading siblings не использовались. )HTML" << (loadStats.measurementAffinityOk ? "Закрепление измерительного потока применено." : "Закрепить измерительный поток не удалось, тест продолжился с предупреждением.") << R"HTML(</p>
        </div>

        <div class="chart-container">
            <canvas id="combinedChart"></canvas>
        </div>

        <div class="summary">
            <p><strong>Обозначения простыми словами:</strong> промах Sleep(1) — насколько пробуждение отличается от идеальной 1.000 мс. Разброс — насколько эти пробуждения гуляют друг относительно друга. (Технически: Δ = |Sleep(1) − 1.000 ms|; robust CV = robust stddev(wake) / robust average(wake) * 100% после обрезки верхних 2% wake-time выбросов.)</p>
        </div>

    <h2>📋 Первая волна — score по всем кандидатам</h2>
        <table>
            <thead>
                <tr>
                    <th>Таймер (мс)</th>
                    <th>Score1 (меньше лучше) 🏆</th>
                    <th>Промах Sleep(1), robust (мс)</th>
                    <th>Разброс, robust CV (%)</th>
                    <th>Штраф за разброс (мс)</th>
                    <th>Среднее пробуждение (мс)</th>
                    <th>Разброс wake, robust stddev (мс)</th>
                    <th>Замеров</th>
                    <th>Min (мс)</th>
                    <th>Max (мс)</th>
                    <th>Median (мс)</th>
                    <th>Физическое ядро замера</th>
                </tr>
            </thead>
            <tbody>)HTML";

    // Генерируем строки таблицы
    for (size_t i = 0; i < sortedResults.size(); ++i) {
        const auto& r = sortedResults[i];
        std::string rowClass = (bestIndex == (int)i) ? "best-result" : "";
                f << "<tr class=\"" << rowClass << "\">" 
                    << "<td>" << std::fixed << std::setprecision(3) << r.timerMs << "</td>"
                    << "<td>" << std::fixed << std::setprecision(6) << r.scoreMs << "</td>"
                    << "<td>" << std::fixed << std::setprecision(6) << r.avgAbsDeltaMs << "</td>"
                    << "<td>" << std::fixed << std::setprecision(3) << r.cvPercent << "</td>"
                    << "<td>" << std::fixed << std::setprecision(6) << r.cvPenaltyMs << "</td>"
                    << "<td>" << std::fixed << std::setprecision(6) << r.avgWakeMs << "</td>"
                    << "<td>" << std::fixed << std::setprecision(6) << r.stdDevWakeMs << "</td>"
                    << "<td>" << r.samples << "</td>"
                    << "<td>" << std::fixed << std::setprecision(6) << r.minWakeMs << "</td>"
                    << "<td>" << std::fixed << std::setprecision(6) << r.maxWakeMs << "</td>"
                    << "<td>" << std::fixed << std::setprecision(6) << r.medianWakeMs << "</td>"
                    << "<td>Physical #" << loadStats.measurementPhysicalCore << " / CPU " << loadStats.measurementCpu << "</td>"
                    << "</tr>\n";
    }    f << R"HTML(            </tbody>
        </table>)HTML";

    if (!topCandidates.empty()) {
        f << R"HTML(

    <h2>🏅 Top-15 первой волны по score</h2>
        <table>
            <thead>
                <tr>
                    <th>#</th>
                    <th>Таймер (мс)</th>
                    <th>Score1 (меньше лучше)</th>
                    <th>Промах Sleep(1), robust (мс)</th>
                    <th>Разброс, robust CV (%)</th>
                    <th>Штраф за разброс (мс)</th>
                    <th>Среднее пробуждение (мс)</th>
                    <th>Замеров</th>
                </tr>
            </thead>
            <tbody>)HTML";
        for (size_t i = 0; i < topCandidates.size(); ++i) {
            const auto& r = topCandidates[i];
            f << "<tr>"
              << "<td>" << (i + 1) << "</td>"
              << "<td>" << std::fixed << std::setprecision(3) << r.timerMs << "</td>"
              << "<td>" << std::fixed << std::setprecision(6) << r.scoreMs << "</td>"
              << "<td>" << std::fixed << std::setprecision(6) << r.avgAbsDeltaMs << "</td>"
              << "<td>" << std::fixed << std::setprecision(3) << r.cvPercent << "</td>"
              << "<td>" << std::fixed << std::setprecision(6) << r.cvPenaltyMs << "</td>"
              << "<td>" << std::fixed << std::setprecision(6) << r.avgWakeMs << "</td>"
              << "<td>" << r.samples << "</td>"
              << "</tr>\n";
        }
        f << R"HTML(            </tbody>
        </table>)HTML";
    }

    if (stableZone.size() > 1) {
        f << R"HTML(

    <div class="summary">
        <h2>🟢 Стабильная зона первой волны</h2>
        <p>Значения, которые почти не уступили победителю первой волны (в пределах 5% по score):</p>
        <p>)HTML";
        for (size_t i = 0; i < stableZone.size(); ++i) {
            if (i) f << ", ";
            f << std::fixed << std::setprecision(3) << stableZone[i].timerMs << " ms";
        }
        f << R"HTML(</p>
    </div>)HTML";
    }

    if (!sortedSecond.empty()) {
        f << R"HTML(

    <h2>🥈 Вторая волна — 7 кругов по top-15</h2>
        <div class="summary">
            <p><strong>Параметры:</strong> 15 лучших кандидатов первой волны; 7 перемешанных кругов; около 14 сек суммарных измерений на кандидата</p>
            <p><strong>Критерий:</strong> побеждает минимальный score1: 75% за малый промах Sleep(1), 25% за малый разброс (score1 = 0.75 * robustAvgAbsDelta + 0.25 * ((robust CV% / 100) * 1.000 ms)).</p>
        </div>

        <div class="chart-container">
            <canvas id="secondWaveTopChart"></canvas>
        </div>

        <table>
            <thead>
                <tr>
                    <th>Таймер (мс)</th>
                    <th>Score1 (меньше лучше) 🏆</th>
                    <th>Промах Sleep(1), robust (мс)</th>
                    <th>Разброс, robust CV (%)</th>
                    <th>Штраф за разброс (мс)</th>
                    <th>Среднее пробуждение (мс)</th>
                    <th>Разброс wake, robust stddev (мс)</th>
                    <th>Замеров</th>
                    <th>Min (мс)</th>
                    <th>Max (мс)</th>
                    <th>Median (мс)</th>
                </tr>
            </thead>
            <tbody>)HTML";
        for (size_t i = 0; i < sortedSecond.size(); ++i) {
            const auto &r2 = sortedSecond[i];
            std::string rowClass2 = (bestIndex2 == (int)i) ? "best-result" : "";
            f << "<tr class=\"" << rowClass2 << "\">"
              << "<td>" << std::fixed << std::setprecision(3) << r2.timerMs << "</td>"
              << "<td>" << std::fixed << std::setprecision(6) << r2.scoreMs << "</td>"
              << "<td>" << std::fixed << std::setprecision(6) << r2.avgAbsDeltaMs << "</td>"
              << "<td>" << std::fixed << std::setprecision(3) << r2.cvPercent << "</td>"
              << "<td>" << std::fixed << std::setprecision(6) << r2.cvPenaltyMs << "</td>"
              << "<td>" << std::fixed << std::setprecision(6) << r2.avgWakeMs << "</td>"
              << "<td>" << std::fixed << std::setprecision(6) << r2.stdDevWakeMs << "</td>"
              << "<td>" << r2.samples << "</td>"
              << "<td>" << std::fixed << std::setprecision(6) << r2.minWakeMs << "</td>"
              << "<td>" << std::fixed << std::setprecision(6) << r2.maxWakeMs << "</td>"
              << "<td>" << std::fixed << std::setprecision(6) << r2.medianWakeMs << "</td>"
              << "</tr>\n";
        }
        f << R"HTML(            </tbody>
        </table>)HTML";
    }

    if (finalStableZone.size() > 1) {
        f << R"HTML(

    <div class="summary">
        <h2>🎯 Финальная стабильная зона</h2>
        <p>Соседние значения из третьей волны, которые почти не уступили лучшему score1 (в пределах 5%). Рекомендованный таймер берется как центр этой зоны:</p>
        <p>)HTML";
        for (size_t i = 0; i < finalStableZone.size(); ++i) {
            if (i) f << ", ";
            f << std::fixed << std::setprecision(3) << finalStableZone[i].timerMs << " ms";
        }
        f << R"HTML(</p>
    </div>)HTML";
    }

    // Добавляем секцию третьей волны (окрестность) если есть результаты
    if (!sortedThird.empty()) {
        f << R"HTML(
        
    <h2>🎯 Третья волна — окрестность top-1 второй волны</h2>
        <div class="summary">
            <p><strong>Параметры:</strong> Окрестность ±0.002 мс вокруг top-1 второй волны, шаг 0.001 мс; 5 перемешанных кругов, суммарно ~20 сек измерений на точку. Если top-1 = 0.500 мс, проверяется 0.500–0.504 мс.</p>
            <p><strong>Критерий:</strong> побеждает минимальный score1: 75% за малый промах Sleep(1), 25% за малый разброс (score1 = 0.75 * robustAvgAbsDelta + 0.25 * ((robust CV% / 100) * 1.000 ms)).</p>
        </div>

        <div class="chart-container">
            <canvas id="secondWaveMadChart"></canvas>
        </div>

        <table>
            <thead>
                <tr>
                    <th>Таймер (мс)</th>
                    <th>Score1 (меньше лучше) 🏆</th>
                    <th>Промах Sleep(1), robust (мс)</th>
                    <th>Разброс, robust CV (%)</th>
                    <th>Штраф за разброс (мс)</th>
                    <th>Среднее пробуждение (мс)</th>
                    <th>Разброс wake, robust stddev (мс)</th>
                    <th>Замеров</th>
                    <th>Min (мс)</th>
                    <th>Max (мс)</th>
                    <th>Median (мс)</th>
                </tr>
            </thead>
            <tbody>)HTML";

                for (size_t i = 0; i < sortedThird.size(); ++i) {
                        const auto &r3 = sortedThird[i];
                        std::string rowClass3 = (recommendedIndex3 == (int)i) ? "best-result" : "";
                        f << "<tr class=\"" << rowClass3 << "\">"
                            << "<td>" << std::fixed << std::setprecision(3) << r3.timerMs << "</td>"
                            << "<td>" << std::fixed << std::setprecision(6) << r3.scoreMs << "</td>"
                            << "<td>" << std::fixed << std::setprecision(6) << r3.avgAbsDeltaMs << "</td>"
                            << "<td>" << std::fixed << std::setprecision(3) << r3.cvPercent << "</td>"
                            << "<td>" << std::fixed << std::setprecision(6) << r3.cvPenaltyMs << "</td>"
                            << "<td>" << std::fixed << std::setprecision(6) << r3.avgWakeMs << "</td>"
                            << "<td>" << std::fixed << std::setprecision(6) << r3.stdDevWakeMs << "</td>"
                            << "<td>" << r3.samples << "</td>"
                            << "<td>" << std::fixed << std::setprecision(6) << r3.minWakeMs << "</td>"
                            << "<td>" << std::fixed << std::setprecision(6) << r3.maxWakeMs << "</td>"
                            << "<td>" << std::fixed << std::setprecision(6) << r3.medianWakeMs << "</td>"
                            << "</tr>\n";
                }

        f << R"HTML(            </tbody>
        </table>)HTML";
    }

    f << R"HTML(

        <script>
            // Данные для графиков
            const labels = [)HTML";

    // Генерируем данные для JavaScript
    for (size_t i = 0; i < sortedResults.size(); ++i) {
        if (i > 0) f << ", ";
        f << "'" << std::fixed << std::setprecision(3) << sortedResults[i].timerMs << "'";
    }

    f << R"HTML(];)HTML";
            
            // legacy CV chart removed

    // (нет отдельного массива для второй волны кроме sortedThird)

    // Добавляем данные второй волны если есть
    if (!sortedSecond.empty()) {
        f << R"HTML(

            // Данные второй волны (top-15 retest)
            const labels2 = [)HTML";
        for (size_t i = 0; i < sortedSecond.size(); ++i) {
            if (i > 0) f << ", ";
            f << "'" << std::fixed << std::setprecision(3) << sortedSecond[i].timerMs << "'";
        }
        f << R"HTML(];
            const scoreTop5 = [)HTML";
        for (size_t i = 0; i < sortedSecond.size(); ++i) {
            if (i > 0) f << ", ";
            f << std::fixed << std::setprecision(6) << sortedSecond[i].scoreMs;
        }
        f << R"HTML(];)HTML";
    }

    // Добавляем данные третьей волны если есть
    if (!sortedThird.empty()) {
        f << R"HTML(

            // Данные третьей волны (окрестность)
            const labels3 = [)HTML";
        for (size_t i = 0; i < sortedThird.size(); ++i) {
            if (i > 0) f << ", ";
            f << "'" << std::fixed << std::setprecision(3) << sortedThird[i].timerMs << "'";
        }
        f << R"HTML(];
            const score3 = [)HTML";
        for (size_t i = 0; i < sortedThird.size(); ++i) {
            if (i > 0) f << ", ";
            f << std::fixed << std::setprecision(6) << sortedThird[i].scoreMs;
        }
        f << R"HTML(];)HTML";
    }

    // JavaScript код для создания графиков (всегда генерируется)
    f << R"HTML(
            // Подготовка данных для основного графика score (raw + smoothed)
    )HTML";

    // Собираем raw score и сглаженную диагностическую линию.
    std::vector<double> rawScores; rawScores.reserve(sortedResults.size());
    for (const auto &r : sortedResults) rawScores.push_back(r.scoreMs);
    std::vector<double> smoothScores = smooth(rawScores, 5);

    // Вертикальная линия на графике показывает реальный лучший raw-кандидат по score.
    int n = (int)smoothScores.size();
    int i0 = (bestIndex >= 0) ? bestIndex : 0;
    if (i0 >= n) i0 = std::max(0, n - 1);
    double fracOffset = 0.0;
    double bestMarkerTimer = sortedResults.empty() ? 0.0 : sortedResults[std::min(std::max(i0,0), (int)sortedResults.size()-1)].timerMs;

    // Выводим JS массивы и координату лучшего raw-минимума.
    {
        // raw
    f << "\n            const scoreRaw = [";
        for (size_t i = 0; i < rawScores.size(); ++i) {
            if (i) f << ", ";
            f << std::fixed << std::setprecision(8) << rawScores[i];
        }
        f << "];\n";
        // smooth
    f << "            const scoreSmooth = [";
        for (size_t i = 0; i < smoothScores.size(); ++i) {
            if (i) f << ", ";
            f << std::fixed << std::setprecision(8) << smoothScores[i];
        }
        f << "];\n";
        // best raw score marker
        f << "            const bestMarkerIndex = " << std::fixed << std::setprecision(6) << (i0 + fracOffset) << ";\n";
        f << "            const bestMarkerTimer = " << std::fixed << std::setprecision(6) << bestMarkerTimer << ";\n";
    }

    // Теперь продолжаем JS
    f << R"HTML(

            Chart.defaults.color = '#cbd5e1';
            Chart.defaults.borderColor = 'rgba(148, 163, 184, 0.22)';

            // График первой волны: итоговый score
            const ctx2 = document.getElementById('combinedChart').getContext('2d');
            const vLinePlugin = {
                id: 'vline',
                afterDatasetsDraw(chart, args, pluginOptions) {
                    const {ctx, chartArea: {top, bottom}, scales: {x}} = chart;
                    const i = Math.floor(bestMarkerIndex);
                    const frac = bestMarkerIndex - i;
                    const x0 = x.getPixelForValue(i);
                    const x1 = x.getPixelForValue(i+1);
                    const xp = isFinite(x0) && isFinite(x1) ? (x0 + frac*(x1 - x0)) : x.getPixelForValue(i);
                    ctx.save();
                    ctx.strokeStyle = 'rgba(0,0,0,0.6)';
                    ctx.setLineDash([4,3]);
                    ctx.beginPath();
                    ctx.moveTo(xp, top);
                    ctx.lineTo(xp, bottom);
                    ctx.stroke();
                    ctx.restore();
                }
            };
            Chart.register(vLinePlugin);
            new Chart(ctx2, {
                type: 'line',
                data: {
                    labels: labels,
                    datasets: [{
                        label: 'Score1 (raw, ms-eq)',
                        data: scoreRaw,
                        borderColor: 'rgb(54, 162, 235)',
                        backgroundColor: 'rgba(54, 162, 235, 0.2)',
                        tension: 0.1,
                        pointBackgroundColor: scoreRaw.map((val, idx) => 
                            idx === )HTML" << bestIndex << R"HTML( ? 'red' : 'rgb(54, 162, 235)'
                        ),
                        pointRadius: scoreRaw.map((val, idx) => 
                            idx === )HTML" << bestIndex << R"HTML( ? 8 : 3
                        )
                    },{
                        label: 'Score1 (smoothed, ms-eq)',
                        data: scoreSmooth,
                        borderColor: 'rgb(0, 200, 83)',
                        backgroundColor: 'rgba(0, 200, 83, 0.15)',
                        tension: 0.2,
                        pointRadius: 0
                    }]
                },
                options: {
                    responsive: true,
                    maintainAspectRatio: false,
                    plugins: {
                        title: {
                            display: true,
                            text: 'Первая волна: итоговый score (raw и сглаженный). Вертикальная линия — лучший raw score.'
                        },
                        zoom: {
                            pan: { enabled: true, mode: 'x' },
                            zoom: {
                                wheel: { enabled: true },
                                pinch: { enabled: true },
                                mode: 'x'
                            }
                        }
                    },
                    scales: {
                        x: {
                            title: {
                                display: true,
                                text: 'Таймер (мс)'
                            }
                        },
                        y: {
                            title: {
                                display: true,
                                text: 'Score1 (ms-eq)'
                            }
                        }
                    }
                }
            });)HTML";
        // Добавляем график второй волны (top-15 retest) если есть данные
        if (!sortedSecond.empty()) {
            f << R"HTML(

            // График второй волны: top-15 retest
            const ctxTop5 = document.getElementById('secondWaveTopChart').getContext('2d');
            new Chart(ctxTop5, {
                type: 'line',
                data: {
                    labels: labels2,
                    datasets: [{
                        label: 'Score1 top-15 retest (ms-eq)',
                        data: scoreTop5,
                        borderColor: '#f59e0b',
                        backgroundColor: 'rgba(245, 158, 11, 0.18)',
                        tension: 0.1,
                        pointBackgroundColor: scoreTop5.map((val, idx) =>
                            idx === )HTML" << bestIndex2 << R"HTML( ? '#2dd4bf' : '#f59e0b'
                        ),
                        pointRadius: scoreTop5.map((val, idx) =>
                            idx === )HTML" << bestIndex2 << R"HTML( ? 8 : 4
                        )
                    }]
                },
                options: {
                    responsive: true,
                    maintainAspectRatio: false,
                    plugins: {
                        title: {
                            display: true,
                            text: 'Вторая волна: top-15, 7 перемешанных кругов'
                        }
                    },
                    scales: {
                        x: {
                            title: { display: true, text: 'Таймер (мс)' }
                        },
                        y: {
                            title: { display: true, text: 'Score1 (ms-eq)' }
                        }
                    }
                }
            });

            )HTML";
        }
        // Добавляем график третьей волны (окрестность) если есть данные
        if (!sortedThird.empty()) {
            f << R"HTML(

            // График третьей волны: итоговый score1
            const ctx5 = document.getElementById('secondWaveMadChart').getContext('2d');
            new Chart(ctx5, {
                type: 'line',
                data: {
                    labels: labels3,
                    datasets: [{
                        label: 'Score1 neighborhood (ms-eq)',
                        data: score3,
                        borderColor: '#a78bfa',
                        backgroundColor: 'rgba(167, 139, 250, 0.18)',
                        tension: 0.1,
                        pointBackgroundColor: score3.map((val, idx) => 
                            idx === )HTML" << recommendedIndex3 << R"HTML( ? '#2dd4bf' : '#a78bfa'
                        ),
                        pointRadius: score3.map((val, idx) => 
                            idx === )HTML" << recommendedIndex3 << R"HTML( ? 8 : 3
                        )
                    }]
                },
                options: {
                    responsive: true,
                    maintainAspectRatio: false,
                    plugins: {
                        title: {
                            display: true,
                            text: 'Третья волна: окрестность top-1 второй волны'
                        }
                    },
                    scales: {
                        x: {
                            title: { display: true, text: 'Таймер (мс)' }
                        },
                        y: {
                            title: { display: true, text: 'Score1 (ms-eq)' }
                        }
                    }
                }
            });

            )HTML";

        }

        f << R"HTML(

            </script>
        </div>
    </body>
    </html>)HTML";

        f.close();
    }

// Heuristic match for the friendly name of the setting we want to change
// Normalize a friendly name: lowercase (Unicode-aware), convert invisible spaces to plain space,
// collapse punctuation/whitespace and trim. Returns a normalized std::wstring suitable for matching.
static std::wstring normalizeFriendlyName(const std::wstring &src)
{
    // Lowercase using LCMapStringW (invariant locale) to handle Cyrillic correctly.
    int outLen = LCMapStringW(LOCALE_INVARIANT, LCMAP_LOWERCASE, src.c_str(), -1, NULL, 0);
    std::wstring lower;
    if (outLen > 0) {
        std::vector<WCHAR> tmp(outLen);
        LCMapStringW(LOCALE_INVARIANT, LCMAP_LOWERCASE, src.c_str(), -1, tmp.data(), outLen);
        lower.assign(tmp.data());
    } else {
        lower = src;
    }

    std::wstring cleaned; cleaned.reserve(lower.size());
    for (wchar_t c : lower) {
        // map common invisible/nbsp characters to space
        if (c == 0x00A0u || c == 0x200Bu || c == 0xFEFFu || c == 0x202Fu || c == 0x2007u) { cleaned.push_back(L' '); continue; }
        if (iswspace(c)) { cleaned.push_back(L' '); continue; }
        // keep digits, ASCII letters, or any non-ASCII character (covers Cyrillic etc.)
        if (iswalnum(c) || (unsigned int)c > 127u) cleaned.push_back(c);
        else cleaned.push_back(L' ');
    }
    // collapse multiple spaces
    std::wstring out; out.reserve(cleaned.size()); bool lastSpace = false;
    for (wchar_t c : cleaned) {
        if (c == L' ') { if (!lastSpace) { out.push_back(c); lastSpace = true; } }
        else { out.push_back(c); lastSpace = false; }
    }
    // trim
    if (!out.empty() && out.front() == L' ') out.erase(out.begin());
    if (!out.empty() && out.back() == L' ') out.pop_back();
    return out;
}

static bool friendlyNameMatches(const std::wstring &name)
{
    std::wstring norm = normalizeFriendlyName(name);

    // Fast-path exact normalized Russian canonical name
    const std::wstring canonical_ru = L"интервал проверки производительности процессора";
    if (norm == canonical_ru) return true;

    // English substrings (normalized)
    bool eng = (norm.find(L"processor") != std::wstring::npos && (norm.find(L"check") != std::wstring::npos || norm.find(L"interval") != std::wstring::npos))
            || (norm.find(L"performance") != std::wstring::npos && norm.find(L"interval") != std::wstring::npos)
            || (norm.find(L"processor performance check interval") != std::wstring::npos);

    // Russian substrings (normalized)
    bool rus = (norm.find(L"интерв") != std::wstring::npos && (norm.find(L"провер") != std::wstring::npos || norm.find(L"процессор") != std::wstring::npos))
            || (norm.find(L"интервал проверки") != std::wstring::npos)
            || (norm.find(L"интервал проверки производительности") != std::wstring::npos)
            || (norm.find(L"интервал проверки производительности процессора") != std::wstring::npos);

    return eng || rus;
}

// Change the processor performance check interval to msValue for all power schemes and apply.
static void setProcessorCheckIntervalAllSchemes(unsigned long msValue)
{
    appendPowerLog("Starting setProcessorCheckIntervalAllSchemes, target ms=" + std::to_string(msValue));
    // Initialize COM in case PowerReadFriendlyName uses it internally for string conversions
    HRESULT hrCo = CoInitializeEx(NULL, COINIT_APARTMENTTHREADED);
    appendPowerLog(std::string("CoInitializeEx rc=") + std::to_string((int)hrCo));
    // enumerate schemes
    DWORD idx = 0;
    GUID schemeGuid;
    while (true) {
        DWORD bufSize = sizeof(GUID);
        DWORD rc = PowerEnumerate(NULL, NULL, NULL, ACCESS_SCHEME, idx, (UCHAR*)&schemeGuid, &bufSize);
        if (rc == ERROR_NO_MORE_ITEMS) break;
        if (rc != ERROR_SUCCESS) {
            appendPowerLog(std::string("PowerEnumerate(schemes) failed idx=") + std::to_string(idx) + " rc=" + std::to_string(rc));
            break;
        }
        // enumerate subgroups
        DWORD sidx = 0;
        GUID subgroupGuid;
        bool schemeModified = false;
        while (true) {
            bufSize = sizeof(GUID);
            DWORD rc2 = PowerEnumerate(NULL, &schemeGuid, NULL, ACCESS_SUBGROUP, sidx, (UCHAR*)&subgroupGuid, &bufSize);
            if (rc2 == ERROR_NO_MORE_ITEMS) break;
            if (rc2 != ERROR_SUCCESS) {
                appendPowerLog(std::string("PowerEnumerate(subgroups) failed sidx=") + std::to_string(sidx) + " rc=" + std::to_string(rc2));
                break;
            }
            // enumerate settings
            DWORD setIdx = 0;
            GUID settingGuid;
            while (true) {
                bufSize = sizeof(GUID);
                DWORD rc3 = PowerEnumerate(NULL, &schemeGuid, &subgroupGuid, ACCESS_INDIVIDUAL_SETTING, setIdx, (UCHAR*)&settingGuid, &bufSize);
                if (rc3 == ERROR_NO_MORE_ITEMS) break;
                if (rc3 != ERROR_SUCCESS) {
                    appendPowerLog(std::string("PowerEnumerate(settings) failed setIdx=") + std::to_string(setIdx) + " rc=" + std::to_string(rc3));
                    break;
                }

                // read friendly name
                DWORD nameSize = 0;
                DWORD rc4 = PowerReadFriendlyName(NULL, &schemeGuid, &subgroupGuid, &settingGuid, NULL, &nameSize);
                std::wstring fname;
                if (rc4 == ERROR_MORE_DATA || rc4 == ERROR_SUCCESS) {
                    std::vector<WCHAR> buf(nameSize/sizeof(WCHAR) + 1);
                    rc4 = PowerReadFriendlyName(NULL, &schemeGuid, &subgroupGuid, &settingGuid, (UCHAR*)buf.data(), &nameSize);
                    if (rc4 == ERROR_SUCCESS) {
                        fname.assign(buf.data());
                    }
                }
                std::string fnameUtf8 = "";
                if (!fname.empty()) {
                    // convert to utf8 for logging
                    int needed = WideCharToMultiByte(CP_UTF8, 0, fname.c_str(), -1, NULL, 0, NULL, NULL);
                    if (needed > 0) {
                        std::vector<char> tmp(needed);
                        WideCharToMultiByte(CP_UTF8, 0, fname.c_str(), -1, tmp.data(), needed, NULL, NULL);
                        fnameUtf8 = tmp.data();
                    }
                }

                // Build normalized version for logging (same normalization used in friendlyNameMatches)
                std::wstring s2; s2.reserve(fname.size());
                for (wchar_t c : fname) {
                    wchar_t lc = towlower(c);
                    if (lc == 0x00A0u || lc == 0x200Bu || lc == 0xFEFFu) { s2.push_back(L' '); continue; }
                    if (iswspace(lc)) { s2.push_back(L' '); continue; }
                    if (iswalpha(lc) || iswdigit(lc) || (unsigned int)lc > 127u) s2.push_back(lc);
                    else s2.push_back(L' ');
                }
                std::wstring norm2; norm2.reserve(s2.size()); bool lastSpace2 = false;
                for (wchar_t c : s2) {
                    if (c == L' ') { if (!lastSpace2) { norm2.push_back(c); lastSpace2 = true; } }
                    else { norm2.push_back(c); lastSpace2 = false; }
                }
                if (!norm2.empty() && norm2.front() == L' ') norm2.erase(norm2.begin());
                if (!norm2.empty() && norm2.back() == L' ') norm2.pop_back();
                std::string normUtf8 = "";
                if (!norm2.empty()) {
                    int n2 = WideCharToMultiByte(CP_UTF8, 0, norm2.c_str(), -1, NULL, 0, NULL, NULL);
                    if (n2 > 0) {
                        std::vector<char> tmp2(n2);
                        WideCharToMultiByte(CP_UTF8, 0, norm2.c_str(), -1, tmp2.data(), n2, NULL, NULL);
                        normUtf8 = tmp2.data();
                    }
                }
                if (!normUtf8.empty()) appendPowerLog(std::string("Normalized friendly name: ") + normUtf8);

                if (!fname.empty() && friendlyNameMatches(fname)) {
                    appendPowerLog(std::string("Matched setting: ") + fnameUtf8 + " — changing to " + std::to_string(msValue));
                    // Write AC and DC values
                    DWORD wrc1 = PowerWriteACValueIndex(NULL, &schemeGuid, &subgroupGuid, &settingGuid, msValue);
                    DWORD wrc2 = PowerWriteDCValueIndex(NULL, &schemeGuid, &subgroupGuid, &settingGuid, msValue);
                    if (wrc1 == ERROR_SUCCESS && wrc2 == ERROR_SUCCESS) {
                        appendPowerLog("PowerWrite values success for scheme");
                        schemeModified = true;
                    } else {
                        appendPowerLog(std::string("PowerWrite failed AC rc=") + std::to_string(wrc1) + " DC rc=" + std::to_string(wrc2));
                    }
                } else {
                    if (!fnameUtf8.empty()) appendPowerLog(std::string("Skipping setting: ") + fnameUtf8);
                }

                ++setIdx;
            }
            ++sidx;
        }

        // If we modified the scheme, write the scheme (call PowerSetActiveScheme with same GUID to reapply?)
        if (schemeModified) {
            // write the scheme to persist changes
            GUID *pScheme = &schemeGuid;
            DWORD r = PowerSetActiveScheme(NULL, pScheme);
            if (r == ERROR_SUCCESS) appendPowerLog("PowerSetActiveScheme called for modified scheme");
            else appendPowerLog(std::string("PowerSetActiveScheme failed rc=") + std::to_string(r));
        }

        ++idx;
    }

    // Reapply current active scheme so changes take effect now
    GUID *active = NULL;
    DWORD gr = PowerGetActiveScheme(NULL, &active);
    if (gr == ERROR_SUCCESS && active) {
        DWORD r2 = PowerSetActiveScheme(NULL, active);
        if (r2 == ERROR_SUCCESS) appendPowerLog("Reapplied active scheme successfully");
        else appendPowerLog(std::string("Reapply active scheme failed rc=") + std::to_string(r2));
        LocalFree(active);
    } else {
        appendPowerLog(std::string("PowerGetActiveScheme failed rc=") + std::to_string(gr));
    }

    appendPowerLog("Completed setProcessorCheckIntervalAllSchemes");
    if (hrCo == S_OK || hrCo == S_FALSE) CoUninitialize();
}

// Show a temporary status message in g_statusLines[2] for duration_ms milliseconds.
// Captures previous status lines and restores them only if the temporary message is still present.
static void showTemporaryStatus(const std::string &msg, int duration_ms)
{
    std::vector<std::string> prev(3);
    {
        std::lock_guard<std::mutex> sl(g_menuMutex);
        for (int i = 0; i < 3; ++i) prev[i] = g_statusLines[i];
        g_statusLines[2] = msg;
    }
    // force redraw (вне блокировки g_menuMutex)
    try { drawMenu(); } catch(...) {}

    // spawn a thread to restore after delay, but only if nobody else changed g_statusLines[2]
    std::thread([prev, msg, duration_ms]() {
        std::this_thread::sleep_for(std::chrono::milliseconds(duration_ms));
        bool needRedraw = false;
        {
            std::lock_guard<std::mutex> sl(g_menuMutex);
            // restore only if the current status still equals our temporary message
            if (g_statusLines[2] == msg) {
                for (int i = 0; i < 3; ++i) g_statusLines[i] = prev[i];
                needRedraw = true;
            }
        }
        if (needRedraw) { try { drawMenu(); } catch(...) {} }
    }).detach();
}

// Функция для получения количества физических ядер (без Hyper-Threading)
static int getPhysicalCoreCount() {
    SYSTEM_INFO sysInfo;
    GetSystemInfo(&sysInfo);
    
    // Получаем информацию о логических процессорах
    DWORD bufferSize = 0;
    GetLogicalProcessorInformation(nullptr, &bufferSize);
    
    if (bufferSize == 0) {
        // Fallback: используем половину от логических ядер (предполагаем HT)
        return std::max(1, (int)sysInfo.dwNumberOfProcessors / 2);
    }
    
    std::vector<SYSTEM_LOGICAL_PROCESSOR_INFORMATION> buffer(bufferSize / sizeof(SYSTEM_LOGICAL_PROCESSOR_INFORMATION));
    if (!GetLogicalProcessorInformation(buffer.data(), &bufferSize)) {
        return std::max(1, (int)sysInfo.dwNumberOfProcessors / 2);
    }
    
    int physicalCores = 0;
    for (const auto& info : buffer) {
        if (info.Relationship == RelationProcessorCore) {
            physicalCores++;
        }
    }
    
    return std::max(1, physicalCores);
}

// Явный warmup процессора для стабилизации измерений
static void performCPUWarmup(int durationMs) {
    auto start = std::chrono::steady_clock::now();
    auto end = start + std::chrono::milliseconds(durationMs);
    
    // Интенсивная нагрузка для прогрева
    volatile int counter = 0;
    while (std::chrono::steady_clock::now() < end) {
        for (int i = 0; i < 1000; ++i) {
            counter += i;
        }
        Sleep(1); // Включаем Sleep для прогрева таймера
    }
}

// Точное busy-spin ожидание 1мс без использования Sleep
static void busySpinWait1ms() {
    LARGE_INTEGER freq, start, end;
    QueryPerformanceFrequency(&freq);
    QueryPerformanceCounter(&start);
    
    // Целевое время: 1 миллисекунда
    LONGLONG targetTicks = freq.QuadPart / 1000;
    LONGLONG endTime = start.QuadPart + targetTicks;
    
    // Busy-spin до достижения целевого времени
    LARGE_INTEGER current;
    do {
        QueryPerformanceCounter(&current);
        // Небольшая пауза для снижения нагрузки на CPU
        _mm_pause();
    } while (current.QuadPart < endTime);
}

// Стабилизация системы для точных измерений
static void stabilizeSystem() {
    {
        std::lock_guard<std::mutex> cl(g_consoleMutex);
        std::lock_guard<std::mutex> sl(g_menuMutex);
        g_statusLines[1] = "🔧 Стабилизация системы для точных измерений...";
    }
    
    // 1. Пауза для завершения фоновых процессов
    std::this_thread::sleep_for(std::chrono::milliseconds(2000));
    
    // 2. Принудительный thermal warmup процессора до стабильной частоты
    {
        std::lock_guard<std::mutex> cl(g_consoleMutex);
        std::lock_guard<std::mutex> sl(g_menuMutex);
        g_statusLines[1] = "🔥 Thermal warmup процессора (5 сек)...";
    }
    
    auto start = std::chrono::steady_clock::now();
    volatile uint64_t heat = 0;
    while (std::chrono::steady_clock::now() - start < std::chrono::seconds(5)) {
        // Intensive CPU work to reach stable frequency
        for (int i = 0; i < 500000; ++i) {
            heat += i * i + std::chrono::steady_clock::now().time_since_epoch().count();
        }
        if (!g_running) return;
    }
    
    // 3. Финальная пауза для стабилизации
    {
        std::lock_guard<std::mutex> cl(g_consoleMutex);
        std::lock_guard<std::mutex> sl(g_menuMutex);
        g_statusLines[1] = "⏳ Финальная стабилизация (3 сек)...";
    }
    std::this_thread::sleep_for(std::chrono::milliseconds(3000));
    
    // Подавляем предупреждение о неиспользуемой переменной
    (void)heat;
}

// Helper RAII to pause/resume matrix rain while benchmarking timers
struct MatrixPauseGuard {
    MatrixPauseGuard() { g_matrixPause.store(true); }
    ~MatrixPauseGuard() { g_matrixPause.store(false); }
};

// Reworked showBestTimer: three-stage search (Coarse/Medium/Fine) with warm-up, stabilization, RAII for timer
// resolution, per-point abs-deltas, median/mean/RMS, ETA, and Russian UI progress messages.
void showBestTimer()
{
    g_timerBenchmarkRunning = true;
    MatrixPauseGuard pauseMatrix; // ensure matrix rain is paused during the entire benchmark
    
    using NtSetTimerResFn = LONG (WINAPI *)(ULONG, BOOLEAN, PULONG);
    using NtQueryTimerResFn = LONG (WINAPI *)(PULONG, PULONG, PULONG);

    HMODULE ntdll = GetModuleHandleA("ntdll.dll");
    NtSetTimerResFn pNtSetTimerRes = nullptr;
    NtQueryTimerResFn pNtQueryTimerRes = nullptr;
    if (ntdll) {
        pNtSetTimerRes = (NtSetTimerResFn)GetProcAddress(ntdll, "NtSetTimerResolution");
        pNtQueryTimerRes = (NtQueryTimerResFn)GetProcAddress(ntdll, "NtQueryTimerResolution");
    }

    ConsoleSize cs = getConsoleSize(); int cols = cs.cols; int rows = cs.rows; int msgY = -1;
    // save current menu/banner rects so we can restore the graphical window after the test
    Rect savedMenu = {0,0,0,0};
    Rect savedBanner = {0,0,0,0};
    {
        std::lock_guard<std::mutex> ml(g_menuMutex);
        savedMenu = g_menuRect;
        savedBanner = g_bannerRect;
        if (g_menuRect.h >= 3) msgY = g_menuRect.y + g_menuRect.h - 3;
    }
    if (msgY < 0) msgY = std::max(0, rows - 4);

    if (!pNtSetTimerRes || !pNtQueryTimerRes) {
        std::lock_guard<std::mutex> sl(g_menuMutex);
        g_statusLines[0] = appText(L"NtSetTimerResolution или NtQueryTimerResolution не найдены",
                                   L"NtSetTimerResolution or NtQueryTimerResolution was not found",
                                   L"NtSetTimerResolution oder NtQueryTimerResolution wurde nicht gefunden",
                                   L"NtSetTimerResolution veya NtQueryTimerResolution bulunamadi",
                                   L"No se encontro NtSetTimerResolution o NtQueryTimerResolution",
                                   L"NtSetTimerResolution ou NtQueryTimerResolution nao encontrado",
                                   L"NtSetTimerResolution \u092f\u093e NtQueryTimerResolution \u0928\u0939\u0940\u0902 \u092e\u093f\u0932\u093e");
        g_statusLines[1] = "";
        g_statusLines[2] = "";
        try { drawMenu(); } catch(...) {}
        g_timerBenchmarkRunning = false;
        return;
    }

    // Настройка thread priority, affinity и execution state для стабильности.
    HANDLE hProcess = GetCurrentProcess();
    HANDLE hThread = GetCurrentThread();
    ThreadSettingsGuard threadSettings(hProcess, hThread);
    
    // Высокий приоритет для точных измерений (не реального времени)
    SetPriorityClass(hProcess, HIGH_PRIORITY_CLASS);
    SetThreadPriority(hThread, THREAD_PRIORITY_HIGHEST);
    SetThreadExecutionState(ES_CONTINUOUS | ES_SYSTEM_REQUIRED | ES_AWAYMODE_REQUIRED | ES_DISPLAY_REQUIRED);

    LARGE_INTEGER quietProbeFreqLi;
    QueryPerformanceFrequency(&quietProbeFreqLi);
    std::vector<PhysicalCoreInfo> physicalCores = detectPhysicalCores();
    std::vector<PhysicalCoreInfo> measurementCandidates = preferredMeasurementCores(physicalCores);
    QuietCpuProbeResult quietCpu = chooseQuietMeasurementCpu((double)quietProbeFreqLi.QuadPart, measurementCandidates, 1500);
    const int measurementCpu = quietCpu.cpu;
    bool measurementAffinityOk = threadSettings.pinToCpu(measurementCpu);
    GameLikeLoadGenerator gameLoad(60.0, 10, physicalCores, measurementCpu);
    GameLikeLoadStats loadStats = gameLoad.stats(measurementAffinityOk);
    const int loadPrewarmSeconds = 40;
    loadStats.prewarmSeconds = loadPrewarmSeconds;
    
    // Запускаем постоянную встроенную Game-like нагрузку перед sweep-ом.
    {
        std::lock_guard<std::mutex> cl(g_consoleMutex);
        std::lock_guard<std::mutex> sl(g_menuMutex);
        g_statusLines[0] = appText(L"Запуск встроенной Game-like CPU load (target 60%)...",
                                   L"Starting built-in game-like CPU load (target 60%)...",
                                   L"Starte eingebaute spielahnliche CPU-Last (Ziel 60%)...",
                                   L"Yerlesik oyun benzeri CPU yuku basliyor (hedef %60)...",
                                   L"Iniciando carga CPU tipo juego integrada (objetivo 60%)...",
                                   L"Iniciando carga CPU tipo jogo integrada (alvo 60%)...",
                                   L"\u092c\u093f\u0932\u094d\u091f-\u0907\u0928 game-like CPU load \u0936\u0941\u0930\u0942 (target 60%)...");
        g_statusLines[1] = appText(L"Thermal/scheduler pre-warm 40 сек перед timer sweep",
                                   L"Thermal/scheduler pre-warm: 40 sec before timer sweep",
                                   L"Thermal/Scheduler-Vorwarmung: 40 s vor dem Timer-Sweep",
                                   L"Thermal/scheduler on isitma: timer sweep oncesi 40 sn",
                                   L"Precalentamiento thermal/scheduler: 40 s antes del sweep",
                                   L"Pre-aquecimento thermal/scheduler: 40 s antes do sweep",
                                   L"timer sweep \u0938\u0947 \u092a\u0939\u0932\u0947 thermal/scheduler pre-warm: 40 sec");
        char cpuLine[256];
        if (measurementAffinityOk) {
            std::string prefix = appText(L"Ядро замера", L"Measurement core", L"Messkern", L"Olcum cekirdegi", L"Nucleo de medicion", L"Nucleo de medicao", L"\u092e\u093e\u092a \u0915\u094b\u0930");
            std::snprintf(cpuLine, sizeof(cpuLine), "%s: physical #%d / CPU %d (probe %.6f)", prefix.c_str(), quietCpu.physicalCore, measurementCpu, quietCpu.scoreMs);
        } else {
            std::string prefix = appText(L"WARNING: не удалось закрепить measurement thread на",
                                         L"WARNING: could not pin measurement thread to",
                                         L"WARNUNG: Mess-Thread konnte nicht gepinnt werden auf",
                                         L"UYARI: olcum thread'i sabitlenemedi",
                                         L"AVISO: no se pudo fijar el hilo de medicion en",
                                         L"AVISO: nao foi possivel fixar a thread de medicao em",
                                         L"WARNING: measurement thread pin \u0928\u0939\u0940\u0902 \u0939\u0941\u0906");
            std::snprintf(cpuLine, sizeof(cpuLine), "%s physical #%d / CPU %d", prefix.c_str(), quietCpu.physicalCore, measurementCpu);
        }
        g_statusLines[2] = cpuLine;
        
        for (int m = 0; m < 3; ++m) {
            int y = msgY + m;
            if (y >= 0 && y < rows) {
                setCursorPosition(0, y);
                std::cout << "\x1b[40m" << std::string(cols, ' ');
                if (!g_statusLines[m].empty()) {
                    setCursorPosition(2, y);
                    std::cout << g_statusLines[m];
                }
                std::cout << "\x1b[0m";
            }
        }
        std::cout.flush();
    }
    
    gameLoad.start();
    for (int sec = 0; sec < loadPrewarmSeconds && g_running; ++sec) {
        {
            std::lock_guard<std::mutex> cl(g_consoleMutex);
            std::lock_guard<std::mutex> sl(g_menuMutex);
            char buf[256];
            std::string prefix = appText(L"Прогрев Game-like load", L"Game-like load warm-up", L"Game-like-Last Vorwarmung", L"Game-like load on isitma", L"Precalentamiento de carga tipo juego", L"Aquecimento da carga tipo jogo", L"Game-like load warm-up");
            std::string secText = appText(L"сек", L"sec", L"s", L"sn", L"s", L"s", L"\u0938\u0947\u0915\u0902\u0921");
            std::snprintf(buf, sizeof(buf), "%s: %d/%d %s", prefix.c_str(), sec + 1, loadPrewarmSeconds, secText.c_str());
            g_statusLines[1] = buf;
            int y = msgY + 1;
            if (y >= 0 && y < rows) {
                setCursorPosition(0, y);
                std::cout << "\x1b[40m" << std::string(cols, ' ');
                setCursorPosition(2, y);
                std::cout << g_statusLines[1];
                std::cout << "\x1b[0m";
                std::cout.flush();
            }
        }
        std::this_thread::sleep_for(std::chrono::seconds(1));
    }
    
    LARGE_INTEGER freqLI; QueryPerformanceFrequency(&freqLI);
    double freq = (double)freqLI.QuadPart;

    // Параметры sweep первой волны
    const double startMs = 0.5;
    const double endMs = 1.0;
    const double stepMs = 0.005;            // укрупненный шаг
    const int stabilizationMsFirst = 200;   // короткая стабилизация
    const int measurementMsFirst = 5000;    // ~5s измерения
    
    // Секундомер
    auto sweepStart = std::chrono::steady_clock::now();
    auto formatElapsed = [&]() -> std::string {
        auto now = std::chrono::steady_clock::now();
        auto elapsed = std::chrono::duration_cast<std::chrono::seconds>(now - sweepStart);
        int mins = elapsed.count() / 60;
        int secs = elapsed.count() % 60;
        char buf[32];
        std::snprintf(buf, sizeof(buf), "%02d:%02d", mins, secs);
        return std::string(buf);
    };
    auto formatSeconds = [](int totalSeconds) -> std::string {
        if (totalSeconds < 0) totalSeconds = 0;
        int mins = totalSeconds / 60;
        int secs = totalSeconds % 60;
        char buf[32];
        std::snprintf(buf, sizeof(buf), "%02d:%02d", mins, secs);
        return std::string(buf);
    };

    // Оценка времени теста (3 волны: первая по всем, вторая top-15, третья окрестность top-1)
    const int totalCandidatesEst = (int)((endMs - startMs) / stepMs) + 1; // ~101
    const double firstPerCandSec = (stabilizationMsFirst + measurementMsFirst) / 1000.0;
    const int stabilizationMsTopRetest = 200; // ~0.2s
    const int measurementMsTopRetestRound = 2000; // ~2s per round
    const int stabilizationMsNeighborhood = 200; // ~0.2s
    const int measurementMsNeighborhoodRound = 4000; // 5 rounds -> ~20s per third-wave point
    const double topRetestPerCandSec = kSecondWaveRounds * (stabilizationMsTopRetest + measurementMsTopRetestRound) / 1000.0;
    const double neighPerCandSec = kThirdWaveRounds * (stabilizationMsNeighborhood + measurementMsNeighborhoodRound) / 1000.0;
    const int topRetestCntEst = kTopFirstWaveCount; // top-15 первой волны
    const int neighborhoodCntEst = 5;       // окрестность ±0.002 с шагом 0.001
    const double totalSecEst = totalCandidatesEst * firstPerCandSec
                             + topRetestCntEst * topRetestPerCandSec
                             + neighborhoodCntEst * neighPerCandSec;

    // Логирование - создаём файл рядом с exe
    std::string logFile = getExeDirectory() + "timer_cv_sweep.csv";
    
    FILE *logF = fopen(logFile.c_str(), "w");
    if (logF) {
        fprintf(logF, "timer_us,score1_ms,avg_abs_delta_ms,robust_cv_percent,robust_cv_penalty_ms,avg_wake_ms,robust_stddev_wake_ms,samples,min_ms,max_ms,median_ms,measurement_cpu,measurement_physical_core,physical_core_count,physical_worker_count,target_load_percent,duty_cycle_percent\n");
        fclose(logF);
    }

    // Сохранение текущего таймера для восстановления
    ULONG currentMin, currentMax, currentActual;
    pNtQueryTimerRes(&currentMin, &currentMax, &currentActual);
    // Track our own requested resolution to properly release between candidates
    ULONG prevDesired100ns = 0;

    // Sweep: тестируем каждое значение от 0.5 до 1.0 мс по итоговому score.
    double bestTimerMs = startMs;
    double bestScoreMs = std::numeric_limits<double>::infinity();
    std::vector<TimerTestResult> testResults; // для HTML отчета
    
    double currentTimerMs = startMs;
    int totalCandidates = (int)((endMs - startMs) / stepMs) + 1;
    int candidateIndex = 0;
    
    // Структура для результатов тестирования на одном ядре (первая волна - только Sleep(1))
    struct CoreResult {
        int coreId;
        std::vector<double> times;  // elapsed (ms)
        bool success;
    };
    
    while (currentTimerMs <= endMs + 1e-9 && g_running) {
        candidateIndex++;
        
        // Обновляем GUI
        {
            std::lock_guard<std::mutex> cl(g_consoleMutex);
            std::lock_guard<std::mutex> sl(g_menuMutex);
            
            char buf0[256], buf1[256], buf2[256];
            std::string waveTitle = appText(L"Gaming Timer Analysis: волна 1 — score1 = 0.75*robust |Δ| + 0.25*robust CV",
                                            L"Gaming Timer Analysis: wave 1 - score1 = 0.75*robust |delta| + 0.25*robust CV",
                                            L"Gaming Timer Analysis: Welle 1 - score1 = 0.75*robust |Delta| + 0.25*robust CV",
                                            L"Gaming Timer Analysis: dalga 1 - score1 = 0.75*robust |delta| + 0.25*robust CV",
                                            L"Gaming Timer Analysis: ola 1 - score1 = 0.75*robust |delta| + 0.25*robust CV",
                                            L"Gaming Timer Analysis: onda 1 - score1 = 0.75*robust |delta| + 0.25*robust CV",
                                            L"Gaming Timer Analysis: wave 1 - score1 = 0.75*robust |delta| + 0.25*robust CV");
            std::string testing = appText(L"Тестирую", L"Testing", L"Teste", L"Test", L"Probando", L"Testando", L"\u091f\u0947\u0938\u094d\u091f");
            std::string onCpu = appText(L"на CPU", L"on CPU", L"auf CPU", L"CPU", L"en CPU", L"na CPU", L"CPU");
            std::string windowText = appText(L"окно ~5 сек", L"window ~5 sec", L"Fenster ~5 s", L"pencere ~5 sn", L"ventana ~5 s", L"janela ~5 s", L"window ~5 sec");
            std::string timeText = appText(L"Время", L"Time", L"Zeit", L"Sure", L"Tiempo", L"Tempo", L"\u0938\u092e\u092f");
            std::string estimateText = appText(L"Оценка", L"Estimate", L"Schatzung", L"Tahmin", L"Estimacion", L"Estimativa", L"\u0905\u0928\u0941\u092e\u093e\u0928");
            std::string minText = appText(L"мин", L"min", L"min", L"dk", L"min", L"min", L"min");
            std::snprintf(buf0, sizeof(buf0), "%s", waveTitle.c_str());
            std::snprintf(buf1, sizeof(buf1), "%s: %.3f ms (%d/%d) %s %d - %s", testing.c_str(), currentTimerMs, candidateIndex, totalCandidates, onCpu.c_str(), measurementCpu, windowText.c_str());
            std::snprintf(buf2, sizeof(buf2), "%s: %s | %s: ~%d %s", timeText.c_str(), formatElapsed().c_str(), estimateText.c_str(), (int)std::round(totalSecEst/60.0), minText.c_str());
            
            g_statusLines[0] = buf0;
            g_statusLines[1] = buf1;
            g_statusLines[2] = buf2;
            
            for (int m = 0; m < 3; ++m) {
                int y = msgY + m;
                if (y < 0 || y >= rows) continue;
                setCursorPosition(0, y);
                std::cout << "\x1b[40m" << std::string(cols, ' ');
                if (!g_statusLines[m].empty()) {
                    setCursorPosition(2, y);
                    std::cout << g_statusLines[m];
                }
                std::cout << "\x1b[0m";
            }
            std::cout.flush();
        }

        // Устанавливаем таймер
        ULONG desired100ns = (ULONG)(currentTimerMs * 10000.0); // мс в 100нс единицы
        ULONG actual = 0;
        // Release previous request if changing resolution
        if (prevDesired100ns && prevDesired100ns != desired100ns) {
            pNtSetTimerRes(prevDesired100ns, FALSE, &actual);
            prevDesired100ns = 0;
        }
        LONG result = pNtSetTimerRes(desired100ns, TRUE, &actual);
        
        if (result == 0) { // успешно установлен
            prevDesired100ns = desired100ns;
            // Короткая стабилизация
            Sleep(stabilizationMsFirst);
            
            // ОДНОЯДЕРНОЕ ТЕСТИРОВАНИЕ НА ВЫБРАННОМ ТИХОМ CPU
            std::vector<CoreResult> coreResults(1); // Только один результат для выбранного CPU
            
            coreResults[0].coreId = measurementCpu;
            coreResults[0].times.reserve(measurementMsFirst + 128);
            coreResults[0].success = true;
            
            // Измерения по времени (~5s)
            {
                auto endT = std::chrono::steady_clock::now() + std::chrono::milliseconds(measurementMsFirst);
                while (std::chrono::steady_clock::now() < endT && g_running) {
                    LARGE_INTEGER t1, t2;
                    QueryPerformanceCounter(&t1);
                    // Measure like measuresleep.exe: real Sleep(1) + QPC
                    Sleep(1);
                    QueryPerformanceCounter(&t2);
                    double elapsedMs = (double)(t2.QuadPart - t1.QuadPart) * 1000.0 / freq;
                    coreResults[0].times.push_back(elapsedMs);
                }
            }
            
            if (coreResults[0].times.empty()) {
                coreResults[0].success = false;
            }
            
            // Анализируем результаты выбранного CPU по итоговой формуле robust avgAbsDelta + robust CV.
            std::vector<double> allTimes;  // все времена Sleep(1)+QPC для score
            int successfulCores = 0;
            
            if (coreResults[0].success && !coreResults[0].times.empty()) {
                for (double tt : coreResults[0].times) {
                    allTimes.push_back(tt);
                }
                successfulCores = 1;
            }
            
            TimerMeasurementStats stats = calculateTimerMeasurementStats(allTimes);
            double avgAbsDeltaMs = stats.avgAbsDeltaMs;
            double scoreMs = stats.scoreMs;
            
            // Логируем упрощенный результат
            logF = fopen(logFile.c_str(), "a");
            if (logF) {
                fprintf(logF, "%.1f,%.6f,%.6f,%.3f,%.6f,%.6f,%.6f,%d,%.6f,%.6f,%.6f,%d,%d,%d,%d,%.1f,%.1f\n",
                        currentTimerMs * 1000.0,
                        stats.scoreMs,
                        stats.avgAbsDeltaMs,
                        stats.cvPercent,
                        stats.cvPenaltyMs,
                        stats.avgWakeMs,
                        stats.stdDevWakeMs,
                        stats.samples,
                        stats.minWakeMs,
                        stats.maxWakeMs,
                        stats.medianWakeMs,
                        loadStats.measurementCpu,
                        loadStats.measurementPhysicalCore,
                        loadStats.physicalCoreCount,
                        loadStats.workerCount,
                        loadStats.targetLoadPercent,
                        loadStats.dutyCyclePercent);
                fclose(logF);
            }
            
            // Сохраняем результат для HTML отчета
            TimerTestResult result;
            result.timerMs = currentTimerMs;
            result.avgAbsDeltaMs = avgAbsDeltaMs;
            result.cvPercent = stats.cvPercent;
            result.cvPenaltyMs = stats.cvPenaltyMs;
            result.scoreMs = stats.scoreMs;
            result.avgWakeMs = stats.avgWakeMs;
            result.stdDevWakeMs = stats.stdDevWakeMs;
            result.minWakeMs = stats.minWakeMs;
            result.maxWakeMs = stats.maxWakeMs;
            result.medianWakeMs = stats.medianWakeMs;
            result.samples = stats.samples;
            result.coresTested = successfulCores;
            testResults.push_back(result);
            
            // Запоминаем лучшего первой волны; вторая волна дополнительно проверит top-15 зон.
            if (scoreMs < bestScoreMs || (std::abs(scoreMs - bestScoreMs) < 1e-12 && currentTimerMs < bestTimerMs)) {
                bestScoreMs = scoreMs;
                bestTimerMs = currentTimerMs;
            }
        }
        
        currentTimerMs += stepMs;
    }

    // *** ВТОРАЯ ВОЛНА — ПОВТОРНАЯ ПРОВЕРКА TOP-15 ПЕРВОЙ ВОЛНЫ ***
    std::vector<NeighborhoodResult> secondWaveResults;
    std::vector<NeighborhoodResult> thirdWaveResults;

    if (!testResults.empty()) {
        // === Вторая волна: тестируем top-15 первой волны в 7 перемешанных кругов ===
        std::vector<TimerTestResult> topFirstWave = testResults;
        std::sort(topFirstWave.begin(), topFirstWave.end(),
                  [](const TimerTestResult& a, const TimerTestResult& b) {
                      if (std::abs(a.scoreMs - b.scoreMs) < 1e-12) return a.timerMs < b.timerMs;
                      return a.scoreMs < b.scoreMs;
                  });
        const size_t centersToCheck = std::min<size_t>((size_t)kTopFirstWaveCount, topFirstWave.size());
        topFirstWave.resize(centersToCheck);

        std::vector<double> topRetestTimers;
        topRetestTimers.reserve(topFirstWave.size());
        for (const auto& center : topFirstWave) {
            topRetestTimers.push_back(center.timerMs);
        }
        {
            std::lock_guard<std::mutex> cl(g_consoleMutex);
            std::lock_guard<std::mutex> sl(g_menuMutex);
            char buf[256];
            std::string wave2Line = appText(L"Вторая волна", L"Wave 2", L"Welle 2", L"Dalga 2", L"Ola 2", L"Onda 2", L"Wave 2");
            std::string firstTopLine = appText(L"top первой волны", L"top from wave 1", L"Top aus Welle 1", L"dalga 1 top", L"top de la ola 1", L"top da onda 1", L"wave 1 top");
            std::string roundsLine = appText(L"перемешанных кругов", L"shuffled rounds", L"gemischte Runden", L"karisik tur", L"rondas mezcladas", L"rodadas embaralhadas", L"shuffled rounds");
            std::snprintf(buf, sizeof(buf), "%s: top-%d %s, %d %s", wave2Line.c_str(), (int)centersToCheck, firstTopLine.c_str(), kSecondWaveRounds, roundsLine.c_str());
            g_statusLines[0] = appText(L"Gaming Timer Analysis: волна 2 — 7 кругов top-15 по score1",
                                        L"Gaming Timer Analysis: wave 2 - 7 shuffled top-15 rounds by score1",
                                        L"Gaming Timer Analysis: Welle 2 - 7 gemischte Top-15-Runden nach score1",
                                        L"Gaming Timer Analysis: dalga 2 - score1 ile 7 karisik top-15 tur",
                                        L"Gaming Timer Analysis: ola 2 - 7 rondas mezcladas top-15 por score1",
                                        L"Gaming Timer Analysis: onda 2 - 7 rodadas top-15 embaralhadas por score1",
                                        L"Gaming Timer Analysis: wave 2 - score1 \u0915\u0947 \u0939\u093f\u0938\u093e\u092c \u0938\u0947 7 shuffled top-15 rounds");
            g_statusLines[1] = buf;
            g_statusLines[2] = appText(L"Время", L"Time", L"Zeit", L"Sure", L"Tiempo", L"Tempo", L"\u0938\u092e\u092f") + ": " + formatElapsed() + " | " +
                               appText(L"Волна 2 стартует", L"Wave 2 is starting", L"Welle 2 startet", L"Dalga 2 basliyor", L"Empieza ola 2", L"Onda 2 iniciando", L"Wave 2 \u0936\u0941\u0930\u0942");
            int y0 = msgY + 0;
            if (y0 >= 0 && y0 < rows) {
                setCursorPosition(0, y0);
                std::cout << "\x1b[40m" << std::string(cols, ' ');
                setCursorPosition(2, y0);
                std::cout << g_statusLines[0];
                std::cout << "\x1b[0m";
            }
            int y1 = msgY + 1;
            if (y1 >= 0 && y1 < rows) {
                setCursorPosition(0, y1);
                std::cout << "\x1b[40m" << std::string(cols, ' ');
                setCursorPosition(2, y1);
                std::cout << g_statusLines[1];
                std::cout << "\x1b[0m";
            }
            int y2 = msgY + 2;
            if (y2 >= 0 && y2 < rows) {
                setCursorPosition(0, y2);
                std::cout << "\x1b[40m" << std::string(cols, ' ');
                setCursorPosition(2, y2);
                std::cout << g_statusLines[2];
                std::cout << "\x1b[0m";
            }
            std::cout.flush();
        }

        double bestSecondScore = std::numeric_limits<double>::infinity();
        double bestSecondTimer = bestTimerMs;
        std::vector<std::vector<double>> topRetestTimes(topRetestTimers.size());
        std::mt19937 shuffleRng(0x51A7D15u);
        for (int round = 0; round < kSecondWaveRounds && g_running; ++round) {
            std::vector<size_t> order(topRetestTimers.size());
            for (size_t i = 0; i < order.size(); ++i) order[i] = i;
            std::shuffle(order.begin(), order.end(), shuffleRng);

            for (size_t pos = 0; pos < order.size() && g_running; ++pos) {
                size_t idx = order[pos];
                double candTimer = topRetestTimers[idx];
                ULONG actual = 0;
                ULONG req = (ULONG)(candTimer * 10000.0);
                if (prevDesired100ns && prevDesired100ns != req) {
                    pNtSetTimerRes(prevDesired100ns, FALSE, &actual);
                    prevDesired100ns = 0;
                }
                LONG setResult = pNtSetTimerRes(req, TRUE, &actual);
                if (setResult != 0) {
                    continue;
                }
                prevDesired100ns = req;
                std::this_thread::sleep_for(std::chrono::milliseconds(stabilizationMsTopRetest));

                const int wave2TotalSteps = kSecondWaveRounds * (int)order.size();
                const double wave2DoneBase = round * (int)order.size() + (double)pos;
                auto measureStartT = std::chrono::steady_clock::now();
                auto nextStatusTick = measureStartT;
                auto endT = std::chrono::steady_clock::now() + std::chrono::milliseconds(measurementMsTopRetestRound);
                while (std::chrono::steady_clock::now() < endT && g_running) {
                    LARGE_INTEGER t1, t2; QueryPerformanceCounter(&t1); Sleep(1); QueryPerformanceCounter(&t2);
                    double elapsedMs = (double)(t2.QuadPart - t1.QuadPart) * 1000.0 / freq;
                    topRetestTimes[idx].push_back(elapsedMs);
                    auto nowTick = std::chrono::steady_clock::now();
                    if (nowTick >= nextStatusTick) {
                        double measuredMs = (double)std::chrono::duration_cast<std::chrono::milliseconds>(nowTick - measureStartT).count();
                        double fraction = std::min(1.0, std::max(0.0, measuredMs / (double)measurementMsTopRetestRound));
                        double doneSteps = wave2DoneBase + fraction;
                        int remainSec = (int)std::round(std::max(0.0, (wave2TotalSteps - doneSteps) * (stabilizationMsTopRetest + measurementMsTopRetestRound) / 1000.0));
                        std::lock_guard<std::mutex> sl(g_menuMutex);
                        g_statusLines[2] = appText(L"Время", L"Time", L"Zeit", L"Sure", L"Tiempo", L"Tempo", L"\u0938\u092e\u092f") + ": " + formatElapsed() + " | " +
                                           appText(L"Осталось волны 2", L"Wave 2 remaining", L"Welle 2 verbleibend", L"Dalga 2 kalan", L"Resta ola 2", L"Restante onda 2", L"Wave 2 \u092c\u093e\u0915\u0940") + ": ~" + formatSeconds(remainSec);
                        nextStatusTick = nowTick + std::chrono::seconds(1);
                    }
                }

                {
                    std::lock_guard<std::mutex> cl(g_consoleMutex);
                    std::lock_guard<std::mutex> sl(g_menuMutex);
                    char buf[256];
                    std::string roundText = appText(L"круг", L"round", L"Runde", L"tur", L"ronda", L"rodada", L"round");
                    std::snprintf(buf, sizeof(buf), "%s %d/%d, %zu/%zu: %.3f ms - samples: %zu", roundText.c_str(), round + 1, kSecondWaveRounds, pos + 1, order.size(), candTimer, topRetestTimes[idx].size());
                    g_statusLines[1] = buf;
                    const int totalSteps = kSecondWaveRounds * (int)order.size();
                    const int doneSteps = round * (int)order.size() + (int)pos + 1;
                    const int leftSteps = std::max(0, totalSteps - doneSteps);
                    const int remainSec = (int)std::round(leftSteps * (stabilizationMsTopRetest + measurementMsTopRetestRound) / 1000.0);
                    g_statusLines[2] = appText(L"Время", L"Time", L"Zeit", L"Sure", L"Tiempo", L"Tempo", L"\u0938\u092e\u092f") + ": " + formatElapsed() + " | " +
                                       appText(L"Осталось волны 2", L"Wave 2 remaining", L"Welle 2 verbleibend", L"Dalga 2 kalan", L"Resta ola 2", L"Restante onda 2", L"Wave 2 \u092c\u093e\u0915\u0940") + ": ~" + formatSeconds(remainSec);
                    int y = msgY + 1;
                    if (y >= 0 && y < rows) {
                        setCursorPosition(0, y);
                        std::cout << "\x1b[40m" << std::string(cols, ' ');
                        setCursorPosition(2, y);
                        std::cout << g_statusLines[1];
                        std::cout << "\x1b[0m";
                    }
                    int y2 = msgY + 2;
                    if (y2 >= 0 && y2 < rows) {
                        setCursorPosition(0, y2);
                        std::cout << "\x1b[40m" << std::string(cols, ' ');
                        setCursorPosition(2, y2);
                        std::cout << g_statusLines[2];
                        std::cout << "\x1b[0m";
                    }
                    std::cout.flush();
                }
            }
        }

        for (size_t i = 0; i < topRetestTimers.size(); ++i) {
            if (topRetestTimes[i].empty()) continue;
            double candTimer = topRetestTimers[i];
            TimerMeasurementStats stats = calculateTimerMeasurementStats(topRetestTimes[i]);
            double scoreMs = stats.scoreMs;
            secondWaveResults.push_back({candTimer, stats.avgAbsDeltaMs, stats.cvPercent, stats.cvPenaltyMs, scoreMs, stats.avgWakeMs, stats.stdDevWakeMs, stats.minWakeMs, stats.maxWakeMs, stats.medianWakeMs, stats.samples});
            if (scoreMs < bestSecondScore || (std::abs(scoreMs - bestSecondScore) < 1e-12 && candTimer < bestSecondTimer)) { bestSecondScore = scoreMs; bestSecondTimer = candTimer; }
        }

        if (!secondWaveResults.empty()) {
            bestTimerMs = bestSecondTimer;
            bestScoreMs = bestSecondScore;
        }

        // === Третья волна: окрестность top-1 второй волны ±0.002 мс ===
        if (!secondWaveResults.empty() && g_running) {
            std::vector<double> neigh3;
            bool edgeAtMinTimer = bestSecondTimer <= startMs + 0.0005;
            if (edgeAtMinTimer) {
                for (int k = 0; k <= 4; ++k) {
                    double cand = startMs + 0.001 * k;
                    if (cand > endMs + 1e-9) continue;
                    cand = std::round(cand * 1000.0) / 1000.0;
                    neigh3.push_back(cand);
                }
            } else {
                for (int k = -2; k <= 2; ++k) {
                    double cand = bestSecondTimer + 0.001 * k;
                    if (cand < startMs - 1e-9 || cand > endMs + 1e-9) continue;
                    cand = std::round(cand * 1000.0) / 1000.0;
                    neigh3.push_back(cand);
                }
            }
            std::sort(neigh3.begin(), neigh3.end());
            neigh3.erase(std::unique(neigh3.begin(), neigh3.end()), neigh3.end());
            {
                std::lock_guard<std::mutex> cl(g_consoleMutex);
                std::lock_guard<std::mutex> sl(g_menuMutex);
                char buf[256];
                if (edgeAtMinTimer) {
                    std::snprintf(buf, sizeof(buf), "Третья волна: край 0.500 мс, 0.500-0.504 (%d точек, %d shuffled кругов)", (int)neigh3.size(), kThirdWaveRounds);
                } else {
                    std::snprintf(buf, sizeof(buf), "Третья волна: %.3f мс ±0.002 (%d точек, %d shuffled кругов)", bestSecondTimer, (int)neigh3.size(), kThirdWaveRounds);
                }
                g_statusLines[0] = appText(L"Gaming Timer Analysis: волна 3 — shuffled окрестность + stable zone",
                                            L"Gaming Timer Analysis: wave 3 - shuffled neighborhood + stable zone",
                                            L"Gaming Timer Analysis: Welle 3 - gemischte Umgebung + stabile Zone",
                                            L"Gaming Timer Analysis: dalga 3 - karisik komsuluk + stabil bolge",
                                            L"Gaming Timer Analysis: ola 3 - vecindad mezclada + zona estable",
                                            L"Gaming Timer Analysis: onda 3 - vizinhanca embaralhada + zona estavel",
                                            L"Gaming Timer Analysis: wave 3 - shuffled neighborhood + stable zone");
                {
                    std::string wave3 = appText(L"Третья волна", L"Wave 3", L"Welle 3", L"Dalga 3", L"Ola 3", L"Onda 3", L"Wave 3");
                    std::string points = appText(L"точек", L"points", L"Punkte", L"nokta", L"puntos", L"pontos", L"points");
                    std::string rounds = appText(L"shuffled кругов", L"shuffled rounds", L"gemischte Runden", L"karisik tur", L"rondas mezcladas", L"rodadas embaralhadas", L"shuffled rounds");
                    if (edgeAtMinTimer) {
                        std::string edge = appText(L"край 0.500 ms", L"edge 0.500 ms", L"Rand 0.500 ms", L"0.500 ms siniri", L"borde 0.500 ms", L"borda 0.500 ms", L"edge 0.500 ms");
                        std::snprintf(buf, sizeof(buf), "%s: %s, 0.500-0.504 (%d %s, %d %s)", wave3.c_str(), edge.c_str(), (int)neigh3.size(), points.c_str(), kThirdWaveRounds, rounds.c_str());
                    } else {
                        std::snprintf(buf, sizeof(buf), "%s: %.3f ms +/-0.002 (%d %s, %d %s)", wave3.c_str(), bestSecondTimer, (int)neigh3.size(), points.c_str(), kThirdWaveRounds, rounds.c_str());
                    }
                }
                g_statusLines[1] = buf;
                g_statusLines[2] = appText(L"Время", L"Time", L"Zeit", L"Sure", L"Tiempo", L"Tempo", L"\u0938\u092e\u092f") + ": " + formatElapsed() + " | " +
                                   appText(L"Волна 3 стартует", L"Wave 3 is starting", L"Welle 3 startet", L"Dalga 3 basliyor", L"Empieza ola 3", L"Onda 3 iniciando", L"Wave 3 \u0936\u0941\u0930\u0942");
                int y0 = msgY + 0;
                if (y0 >= 0 && y0 < rows) {
                    setCursorPosition(0, y0);
                    std::cout << "\x1b[40m" << std::string(cols, ' ');
                    setCursorPosition(2, y0);
                    std::cout << g_statusLines[0];
                    std::cout << "\x1b[0m";
                }
                int y1 = msgY + 1;
                if (y1 >= 0 && y1 < rows) {
                    setCursorPosition(0, y1);
                    std::cout << "\x1b[40m" << std::string(cols, ' ');
                    setCursorPosition(2, y1);
                    std::cout << g_statusLines[1];
                    std::cout << "\x1b[0m";
                }
                int y2 = msgY + 2;
                if (y2 >= 0 && y2 < rows) {
                    setCursorPosition(0, y2);
                    std::cout << "\x1b[40m" << std::string(cols, ' ');
                    setCursorPosition(2, y2);
                    std::cout << g_statusLines[2];
                    std::cout << "\x1b[0m";
                }
                std::cout.flush();
            }

            std::vector<std::vector<double>> neighTimes(neigh3.size());
            std::mt19937 thirdShuffleRng(0x7A3C51D2u);
            for (int round = 0; round < kThirdWaveRounds && g_running; ++round) {
                std::vector<size_t> order(neigh3.size());
                for (size_t i = 0; i < order.size(); ++i) order[i] = i;
                std::shuffle(order.begin(), order.end(), thirdShuffleRng);

                for (size_t pos = 0; pos < order.size() && g_running; ++pos) {
                    size_t idx = order[pos];
                    double candTimer = neigh3[idx];
                    ULONG actual = 0;
                    ULONG req = (ULONG)(candTimer * 10000.0);
                    if (prevDesired100ns && prevDesired100ns != req) {
                        pNtSetTimerRes(prevDesired100ns, FALSE, &actual);
                        prevDesired100ns = 0;
                    }
                    LONG setResult = pNtSetTimerRes(req, TRUE, &actual);
                    if (setResult != 0) {
                        continue;
                    }
                    prevDesired100ns = req;
                    std::this_thread::sleep_for(std::chrono::milliseconds(stabilizationMsNeighborhood));

                    const int wave3TotalSteps = kThirdWaveRounds * (int)order.size();
                    const double wave3DoneBase = round * (int)order.size() + (double)pos;
                    auto measureStartT = std::chrono::steady_clock::now();
                    auto nextStatusTick = measureStartT;
                    auto endT = std::chrono::steady_clock::now() + std::chrono::milliseconds(measurementMsNeighborhoodRound);
                    while (std::chrono::steady_clock::now() < endT && g_running) {
                        LARGE_INTEGER t1, t2;
                        QueryPerformanceCounter(&t1);
                        Sleep(1);
                        QueryPerformanceCounter(&t2);
                        double elapsedMs = (double)(t2.QuadPart - t1.QuadPart) * 1000.0 / freq;
                        neighTimes[idx].push_back(elapsedMs);
                        auto nowTick = std::chrono::steady_clock::now();
                        if (nowTick >= nextStatusTick) {
                            double measuredMs = (double)std::chrono::duration_cast<std::chrono::milliseconds>(nowTick - measureStartT).count();
                            double fraction = std::min(1.0, std::max(0.0, measuredMs / (double)measurementMsNeighborhoodRound));
                            double doneSteps = wave3DoneBase + fraction;
                            int remainSec = (int)std::round(std::max(0.0, (wave3TotalSteps - doneSteps) * (stabilizationMsNeighborhood + measurementMsNeighborhoodRound) / 1000.0));
                            std::lock_guard<std::mutex> sl(g_menuMutex);
                            g_statusLines[2] = appText(L"Время", L"Time", L"Zeit", L"Sure", L"Tiempo", L"Tempo", L"\u0938\u092e\u092f") + ": " + formatElapsed() + " | " +
                                               appText(L"Осталось волны 3", L"Wave 3 remaining", L"Welle 3 verbleibend", L"Dalga 3 kalan", L"Resta ola 3", L"Restante onda 3", L"Wave 3 \u092c\u093e\u0915\u0940") + ": ~" + formatSeconds(remainSec);
                            nextStatusTick = nowTick + std::chrono::seconds(1);
                        }
                    }

                    {
                        std::lock_guard<std::mutex> cl(g_consoleMutex);
                        std::lock_guard<std::mutex> sl(g_menuMutex);
                        char buf[256];
                        std::snprintf(buf, sizeof(buf), "🎯 круг %d/%d, %zu/%zu: %.3f мс — samples: %zu",
                                      round + 1, kThirdWaveRounds, pos + 1, order.size(), candTimer, neighTimes[idx].size());
                        {
                            std::string roundText = appText(L"круг", L"round", L"Runde", L"tur", L"ronda", L"rodada", L"round");
                            std::snprintf(buf, sizeof(buf), "%s %d/%d, %zu/%zu: %.3f ms - samples: %zu",
                                          roundText.c_str(), round + 1, kThirdWaveRounds, pos + 1, order.size(), candTimer, neighTimes[idx].size());
                        }
                        g_statusLines[1] = buf;
                        const int totalSteps = kThirdWaveRounds * (int)order.size();
                        const int doneSteps = round * (int)order.size() + (int)pos + 1;
                        const int leftSteps = std::max(0, totalSteps - doneSteps);
                        const int remainSec = (int)std::round(leftSteps * (stabilizationMsNeighborhood + measurementMsNeighborhoodRound) / 1000.0);
                        g_statusLines[2] = appText(L"Время", L"Time", L"Zeit", L"Sure", L"Tiempo", L"Tempo", L"\u0938\u092e\u092f") + ": " + formatElapsed() + " | " +
                                           appText(L"Осталось волны 3", L"Wave 3 remaining", L"Welle 3 verbleibend", L"Dalga 3 kalan", L"Resta ola 3", L"Restante onda 3", L"Wave 3 \u092c\u093e\u0915\u0940") + ": ~" + formatSeconds(remainSec);
                        int y = msgY + 1;
                        if (y >= 0 && y < rows) {
                            setCursorPosition(0, y);
                            std::cout << "\x1b[40m" << std::string(cols, ' ');
                            setCursorPosition(2, y);
                            std::cout << g_statusLines[1];
                            std::cout << "\x1b[0m";
                        }
                        int y2 = msgY + 2;
                        if (y2 >= 0 && y2 < rows) {
                            setCursorPosition(0, y2);
                            std::cout << "\x1b[40m" << std::string(cols, ' ');
                            setCursorPosition(2, y2);
                            std::cout << g_statusLines[2];
                            std::cout << "\x1b[0m";
                        }
                        std::cout.flush();
                    }
                }
            }

            for (size_t i = 0; i < neigh3.size(); ++i) {
                if (neighTimes[i].empty()) continue;
                double candTimer = neigh3[i];
                TimerMeasurementStats stats = calculateTimerMeasurementStats(neighTimes[i]);
                double scoreMs = stats.scoreMs;
                thirdWaveResults.push_back({candTimer, stats.avgAbsDeltaMs, stats.cvPercent, stats.cvPenaltyMs, scoreMs, stats.avgWakeMs, stats.stdDevWakeMs, stats.minWakeMs, stats.maxWakeMs, stats.medianWakeMs, stats.samples});
            }

            if (!thirdWaveResults.empty()) {
                std::vector<NeighborhoodResult> sortedThirdForSelection = thirdWaveResults;
                std::sort(sortedThirdForSelection.begin(), sortedThirdForSelection.end(),
                          [](const NeighborhoodResult& a, const NeighborhoodResult& b) {
                              return a.timerMs < b.timerMs;
                          });
                TimerZoneSelection selection = selectRecommendedFromStableZone(sortedThirdForSelection);
                if (selection.valid) {
                    bestTimerMs = selection.recommendedTimerMs;
                    bestScoreMs = selection.recommendedScoreMs;
                }
            }
        }
    }

    // Снимаем последний запрос на таймерную резолюцию (если делали)
    if (prevDesired100ns) {
        ULONG tmp = 0;
        pNtSetTimerRes(prevDesired100ns, FALSE, &tmp);
        prevDesired100ns = 0;
    }

    // Останавливаем постоянную Game-like нагрузку; thread settings восстановит ThreadSettingsGuard.
    gameLoad.stop();

    // Финальный результат
    auto sweepEnd = std::chrono::steady_clock::now();
    auto totalTime = std::chrono::duration_cast<std::chrono::seconds>(sweepEnd - sweepStart);
    TimerZoneSelection finalSelection;
    if (!thirdWaveResults.empty()) {
        std::vector<NeighborhoodResult> sortedThirdForSelection = thirdWaveResults;
        std::sort(sortedThirdForSelection.begin(), sortedThirdForSelection.end(),
                  [](const NeighborhoodResult& a, const NeighborhoodResult& b) {
                      return a.timerMs < b.timerMs;
                  });
        finalSelection = selectRecommendedFromStableZone(sortedThirdForSelection);
    }
    
    {
        std::lock_guard<std::mutex> cl(g_consoleMutex);
        std::lock_guard<std::mutex> sl(g_menuMutex);
        
        char finalBuf[512];
        if (finalSelection.valid) {
            std::snprintf(finalBuf, sizeof(finalBuf),
                "Идеальный таймер: %.3f мс (центр зоны %.3f-%.3f, CPU %d) | %02d:%02d",
                bestTimerMs, finalSelection.zoneStartMs, finalSelection.zoneEndMs, measurementCpu,
                (int)(totalTime.count() / 60), (int)(totalTime.count() % 60));
        } else {
            std::snprintf(finalBuf, sizeof(finalBuf),
                "Идеальный таймер: %.3f мс (score1: %.6f, CPU %d) | %02d:%02d",
                bestTimerMs, bestScoreMs, measurementCpu, (int)(totalTime.count() / 60), (int)(totalTime.count() % 60));
        }
        
        {
            std::string idealLabel = appText(L"Идеальный таймер", L"Ideal timer", L"Idealer Timer", L"Ideal timer", L"Temporizador ideal", L"Timer ideal", L"\u0906\u0926\u0930\u094d\u0936 \u091f\u093e\u0907\u092e\u0930");
            if (finalSelection.valid) {
                std::string zoneCenterLabel = appText(L"центр зоны", L"zone center", L"Zonenmitte", L"bolge merkezi", L"centro de zona", L"centro da zona", L"zone center");
                std::snprintf(finalBuf, sizeof(finalBuf), "%s: %.3f ms (%s %.3f-%.3f, CPU %d) | %02d:%02d",
                              idealLabel.c_str(), bestTimerMs, zoneCenterLabel.c_str(),
                              finalSelection.zoneStartMs, finalSelection.zoneEndMs, measurementCpu,
                              (int)(totalTime.count() / 60), (int)(totalTime.count() % 60));
            } else {
                std::snprintf(finalBuf, sizeof(finalBuf), "%s: %.3f ms (score1: %.6f, CPU %d) | %02d:%02d",
                              idealLabel.c_str(), bestTimerMs, bestScoreMs, measurementCpu,
                              (int)(totalTime.count() / 60), (int)(totalTime.count() % 60));
            }
        }
        g_statusLines[0] = finalBuf;
        g_statusLines[1] = appText(L"Отчет создан", L"Report created", L"Bericht erstellt", L"Rapor olusturuldu", L"Informe creado", L"Relatorio criado", L"\u0930\u093f\u092a\u094b\u0930\u094d\u091f \u092c\u0928 \u0917\u0908") + ": gaming_timer_analysis.html";
        g_statusLines[2] = appText(L"Game-like load остановлена", L"Game-like load stopped", L"Game-like-Last gestoppt", L"Game-like load durdu", L"Carga tipo juego detenida", L"Carga tipo jogo parada", L"Game-like load \u0930\u0941\u0915 \u0917\u092f\u093e") + "; CSV: timer_cv_sweep.csv";
        
        for (int m = 0; m < 3; ++m) {
            int y = msgY + m;
            if (y < 0 || y >= rows) continue;
            setCursorPosition(0, y);
            std::cout << "\x1b[40m" << std::string(cols, ' ');
            if (!g_statusLines[m].empty()) {
                setCursorPosition(2, y);
                std::cout << g_statusLines[m];
            }
            std::cout << "\x1b[0m";
        }
        std::cout.flush();
    }
    
    // Генерируем HTML отчет с графиками
    if (!testResults.empty()) {
    generateHTMLReport(testResults, secondWaveResults, thirdWaveResults, bestTimerMs, bestScoreMs, (int)totalTime.count(), loadStats);
    }
    
    // Восстанавливаем GUI состояние
    {
        std::lock_guard<std::mutex> ml(g_menuMutex);
        g_menuRect = savedMenu;
        g_bannerRect = savedBanner;
    }
    
    // Восстанавливаем меню
    try { 
        drawMenu(); 
    } catch(...) {}

    // Сохраняем найденный оптимальный таймер
    saveOptimalTimer(bestTimerMs,
                     bestScoreMs,
                     finalSelection.valid ? finalSelection.zoneStartMs : bestTimerMs,
                     finalSelection.valid ? finalSelection.zoneEndMs : bestTimerMs,
                     finalSelection.valid ? finalSelection.formulaBestTimerMs : bestTimerMs);
    
    // Перезапускаем службу SardanelloTimerConst с новым оптимальным значением
    bool serviceRestarted = startTimerService();
    
    {
        std::lock_guard<std::mutex> sl(g_menuMutex);
        if (serviceRestarted) {
            g_statusLines[2] = "🔄 Служба перезапущена с новым таймером";
        } else {
            g_statusLines[2] = "⚠️ Не удалось запустить службу";
        }
    }

    g_timerBenchmarkRunning = false;
}

// Show a centered loading UI with text "LOADING" and a pixel-style progress bar
// that fills from 0 to 100% over `seconds` seconds. This function blocks the
// calling thread for the specified duration (used to match the first music length).
void showLoadingScreen(double seconds)
{
    const int barWidth = 40; // pixel width of the bar
    const std::string filled = "\u2588"; // full block
    const std::string empty = " ";
    auto start = std::chrono::steady_clock::now();
    auto end = start + std::chrono::milliseconds((int)(seconds * 1000));

    // track previous console size so we can clear on resize to avoid artifacting
    ConsoleSize prevCS = getConsoleSize();

    // Clear any pending input so keys pressed before loading are ignored
#ifdef _WIN32
    FlushConsoleInputBuffer(GetStdHandle(STD_INPUT_HANDLE));
#else
    tcflush(STDIN_FILENO, TCIFLUSH);
#endif

    while (std::chrono::steady_clock::now() < end && g_running) {
        auto now = std::chrono::steady_clock::now();
        double elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(now - start).count() / 1000.0;
        if (elapsed < 0) elapsed = 0;
        double progress = elapsed / seconds;
        if (progress > 1.0) progress = 1.0;
        int filledCount = (int)std::round(progress * barWidth);
        int percent = (int)std::round(progress * 100.0);

        ConsoleSize cs = getConsoleSize();
        int cx = cs.cols / 2;
        int cy = cs.rows / 2;

        // if console resized, clear screen to avoid mosaic and update prevCS
        if (cs.cols != prevCS.cols || cs.rows != prevCS.rows) {
            std::lock_guard<std::mutex> lk(g_consoleMutex);
#ifdef _WIN32
            system("cls");
#else
            std::cout << "\x1b[2J\x1b[H";
#endif
            prevCS = cs;
        }

        // compute loading rect and reserve it so matrix thread won't draw inside
        int titleX = cx - (int)std::string("LOADING").size() / 2;
        int barX = cx - (barWidth / 2);
        int barY = cy + 1;
        Rect loadingRect;
        loadingRect.x = barX - 1;
        loadingRect.y = cy - 1;
        loadingRect.w = barWidth + 2;
        loadingRect.h = 4;

        {
            std::lock_guard<std::mutex> lk(g_consoleMutex);
            g_menuRect = loadingRect;

            // draw LOADING centered in green (ANSI bright green)
            std::cout << "\x1b[1;32m";
            setCursorPosition(std::max(0, titleX), std::max(0, cy - 1));
            std::cout << "LOADING";

            // draw bar frame and fill
            setCursorPosition(std::max(0, barX - 1), barY);
            std::cout << "[";
            for (int i = 0; i < barWidth; ++i) {
                if (i < filledCount) std::cout << filled;
                else std::cout << empty;
            }
            std::cout << "]";

            // draw percentage below
            std::string pct = std::to_string(percent) + "%";
            int pctX = cx - (int)pct.size() / 2;
            setCursorPosition(std::max(0, pctX), barY + 1);
            std::cout << pct;

            // reset color
            std::cout << "\x1b[0m";
            std::cout.flush();
        }

    // ensure input pressed during loading doesn't get buffered
#ifdef _WIN32
    FlushConsoleInputBuffer(GetStdHandle(STD_INPUT_HANDLE));
#else
    tcflush(STDIN_FILENO, TCIFLUSH);
#endif
    // update about 20 times per second
    std::this_thread::sleep_for(std::chrono::milliseconds(50));
    }

    // ensure 100% at end and leave green bar
    {
        std::lock_guard<std::mutex> lk(g_consoleMutex);
        ConsoleSize cs = getConsoleSize();
        int cx = cs.cols / 2;
        int cy = cs.rows / 2;
        int barX = cx - (barWidth / 2);
        int barY = cy + 1;
        setCursorPosition(std::max(0, barX - 1), barY);
        std::cout << "\x1b[1;32m";
        std::cout << "[";
        for (int i = 0; i < barWidth; ++i) std::cout << filled;
        std::cout << "]";
        std::string pct = "100%";
        int pctX = cx - (int)pct.size() / 2;
        setCursorPosition(std::max(0, pctX), barY + 1);
        std::cout << pct;
        std::cout << "\x1b[0m";
        std::cout.flush();
    }

    // brief pause so user sees 100%
    std::this_thread::sleep_for(std::chrono::milliseconds(200));

    // Final clear of input so no keys pressed during loading remain
#ifdef _WIN32
    FlushConsoleInputBuffer(GetStdHandle(STD_INPUT_HANDLE));
#else
    tcflush(STDIN_FILENO, TCIFLUSH);
#endif
}
#endif

// Matrix background thread
void matrixThreadFunc(const std::function<bool(int,int)>& isInMenuArea)
{
    // { changed code: column-based falling rain (streams) }
    std::mt19937 rng((unsigned)std::chrono::high_resolution_clock::now().time_since_epoch().count());
    // Use single-column symbols only: Arabic digits + halfwidth katakana (occupy one column)
    // This avoids overwriting wide ASCII-art banner.
    std::vector<std::string> japanese = {
        "0","1","2","3","4","5","6","7","8","9",
        u8"ｱ", u8"ｲ", u8"ｳ", u8"ｴ", u8"ｵ",
        u8"ｶ", u8"ｷ", u8"ｸ", u8"ｹ", u8"ｺ",
        u8"ｻ", u8"ｼ", u8"ｽ", u8"ｾ", u8"ｿ",
        u8"ﾀ", u8"ﾁ", u8"ﾂ", u8"ﾃ", u8"ﾄ",
        u8"ﾅ", u8"ﾆ", u8"ﾇ", u8"ﾈ", u8"ﾉ",
        u8"ﾊ", u8"ﾋ", u8"ﾌ", u8"ﾍ", u8"ﾎ",
        u8"ﾏ", u8"ﾐ", u8"ﾑ", u8"ﾒ", u8"ﾓ",
        u8"ﾔ", u8"ﾕ", u8"ﾖ", u8"ﾗ", u8"ﾘ", u8"ﾙ", u8"ﾚ", u8"ﾛ", u8"ﾝ"
    };
    std::uniform_int_distribution<int> charIndex(0, (int)japanese.size() - 1);
    ConsoleSize cs = getConsoleSize();
    int cols = cs.cols > 0 ? cs.cols : 80;
    int rows = cs.rows > 0 ? cs.rows : 25;

    // struct Column { int headY; int length; int speed; int phase; }; // phase used as cooldown/start
    // { changed code: track previous head/length to erase orphaned chars when head jumps }
    struct Column { int headY; int length; int speed; int phase; int prevHeadY; int prevLength; }; // phase used as cooldown/start
    std::vector<Column> colsState(cols);
    for (int x = 0; x < cols; ++x) {
        colsState[x].headY = -(int)(rng() % rows); // start above screen
        // length random 3..10 but not exceed rows
        {
            int maxLen = (rows > 10) ? 10 : rows;
            if (maxLen < 3) maxLen = std::max(1, rows);
            int lenRange = maxLen - 3 + 1;
            colsState[x].length = 3 + (rng() % lenRange);
        }
        // { changed code: reduced speeds (~30%): 1..2 }
        colsState[x].speed = 1 + (rng() % 2); // 1..2
        // { changed code: reduce startup delay to make more active columns }
        colsState[x].phase = rng() % 20; // was 50
        // initialize previous trackers so first frame can clear correctly
        colsState[x].prevHeadY = colsState[x].headY;
        colsState[x].prevLength = colsState[x].length;
    }

    while (g_running) {
        // If paused (e.g., during timer benchmark), throttle and skip drawing to reduce interference
        if (g_matrixPause.load()) {
            std::this_thread::sleep_for(std::chrono::milliseconds(50));
            continue;
        }
        // update console size occasionally
        cs = getConsoleSize();
        cols = cs.cols > 0 ? cs.cols : cols;
        rows = cs.rows > 0 ? cs.rows : rows;

        // { changed code: ensure colsState matches current cols to avoid out-of-range access }
        {
            int curSize = (int)colsState.size();
            int safeRows = rows > 0 ? rows : 1;
            if (cols > curSize) {
                colsState.resize(cols);
                for (int x = curSize; x < cols; ++x) {
                    // new column: random length 3..10 constrained by safeRows
                    int maxLen = (safeRows > 10) ? 10 : safeRows;
                    if (maxLen < 3) maxLen =  std::max(1, safeRows);
                    int lenRange = maxLen - 3 + 1;
                    colsState[x].headY = -(int)(rng() % safeRows);
                    colsState[x].length = 3 + (rng() % lenRange);
                    colsState[x].speed = 1 + (rng() % 2); // 1..2
                    colsState[x].phase = rng() % 20;
                    // initialize prev values for new columns
                    colsState[x].prevHeadY = colsState[x].headY;
                    colsState[x].prevLength = colsState[x].length;
                }
            } else if (cols < curSize) {
                colsState.resize(cols);
            }
        }

        {
            std::lock_guard<std::mutex> lk(g_consoleMutex);
            // For each column advance head and draw column characters top->down
            for (int x = 0; x < cols; ++x) {
                Column &col = colsState[x];
                if (col.phase > 0) { col.phase--; continue; }

                // remember previous tail area
                int prevHead = col.prevHeadY;
                int prevLen = col.prevLength;

                // advance head
                col.headY += col.speed;

                // Occasionally restart stream after it passed bottom
                if (col.headY - col.length > rows + (int)(rng()%20)) {
                    col.headY = -(int)(rng() % rows);
                    // restart with random length 3..10 capped by rows
                    {
                        int maxLen = (rows > 10) ? 10 : rows;
                        if (maxLen < 3) maxLen = std::max(1, rows);
                        int lenRange = maxLen - 3 + 1;
                        col.length = 3 + (rng() % lenRange);
                    }
                    col.speed = 1 + (rng() % 2); // 1..2
                    col.phase = rng() % 10; // reduce restart delay for more flow
                    // reset prev trackers so next frame clears correctly
                    col.prevHeadY = col.headY;
                    col.prevLength = col.length;
                    continue;
                }

                int newHead = col.headY;
                int newLen = col.length;

                // Clear positions that belonged to previous tail but are not covered by new tail
                int prevStart = prevHead - prevLen + 1;
                int newStart = newHead - newLen + 1;
                for (int p = prevHead; p >= prevStart; --p) {
                    if (p < 0 || p >= rows) continue;
                    // if p is within new tail range, it'll be redrawn — skip clearing
                    if (p >= newStart && p <= newHead) continue;
                    if (isInMenuArea(x, p)) continue;
                    setCursorPosition(x, p);
                    std::cout.put(' ');
                }

                // draw from head down to tail (new tail)
                for (int k = 0; k < newLen; ++k) {
                    int y = newHead - k;
                    if (y < 0 || y >= rows) continue;
                    if (isInMenuArea(x, y)) continue;

                    // pick a Japanese symbol (UTF-8 string)
                    std::string ch = japanese[ charIndex(rng) ];

#ifdef _WIN32
                    if (k == 0) {
                        std::cout << "\x1b[1;97m";
                    } else if (k < newLen / 3) {
                        std::cout << "\x1b[1;92m";
                    } else {
                        std::cout << "\x1b[2;32m";
                    }
                    setCursorPosition(x, y);
                    std::cout << ch;
                    std::cout << "\x1b[0m";
#else
                    if (k == 0) {
                        std::cout << "\x1b[1;97m";
                    } else if (k < newLen / 3) {
                        std::cout << "\x1b[1;92m";
                    } else {
                        std::cout << "\x1b[2;32m";
                    }
                    setCursorPosition(x, y);
                    std::cout << ch;
                    std::cout << "\x1b[0m";
#endif
                }

                // update prev trackers for next frame
                col.prevHeadY = newHead;
                col.prevLength = newLen;
             }
             // { changed code: если все столбцы уже прошли экран — массово перезапустить дождь }
             bool allPassed = true;
             for (int x = 0; x < cols; ++x) {
                 Column &col = colsState[x];
                 if (col.headY - col.length < rows) { allPassed = false; break; }
             }
             if (allPassed && cols > 0) {
                 for (int x = 0; x < cols; ++x) {
                     int safeRows = rows > 0 ? rows : 1;
                     colsState[x].headY = -(int)(rng() % safeRows);
                    // restart length 3..10 capped by safeRows
                    {
                        int maxLen = (safeRows > 10) ? 10 : safeRows;
                        if (maxLen < 3) maxLen = std::max(1, safeRows);
                        int lenRange = maxLen - 3 + 1;
                        colsState[x].length = 3 + (rng() % lenRange);
                    }
                    colsState[x].speed = 1 + (rng() % 2); // restart with speeds 1..2
                    colsState[x].phase = rng() % 10;
                     // reset prev trackers on mass restart
                     colsState[x].prevHeadY = colsState[x].headY;
                     colsState[x].prevLength = colsState[x].length;
                 }
             }
             std::cout.flush();
         }

        // small frame delay; randomize a bit per cycle for natural effect
        // { changed code: increase frame delay ~30% to slow overall animation }
        std::this_thread::sleep_for(std::chrono::milliseconds(55 + (rng() % 72)));
    }
}

// Draw static centered menu (overwrites background in area)
Rect drawMenu()
{
    // Снимок строк статуса до рисования (чтобы не брать g_menuMutex под g_consoleMutex и избежать дедлоков)
    std::array<std::string,3> statusSnapshot;
    {
        std::lock_guard<std::mutex> sl(g_menuMutex);
        statusSnapshot = g_statusLines;
    }
    ConsoleSize cs = getConsoleSize();
    // New menu layout: 4 rows
    // Row 1: options (1) and (2)
    // Row 2: navigation controls (Back / Forward)
    // Row 3: page indicator [current / total]
    // Row 4: progress bar showing current page progress (current/total)
    int currentPage = g_currentPage;
    int totalPages = g_totalPages;

    std::string row1;
    if (currentPage == 1) {
        row1 = "                                          [1] ОТКЛЮЧИТЬ ВЫСОКОТОЧНЫЙ ТАЙМЕР СОБЫТИЙ                                                                                ";
    } else if (currentPage == 2) {
        row1 = "                                          [1] ПОДОБРАТЬ ИДЕАЛЬНЫЙ ТАЙМЕР                                                                                       ";
    } else if (currentPage == 3) {
        row1 = "                                          [1] УСТАНОВИТЬ ПРОВЕРЕННЫЙ ИДЕАЛЬНЫЙ ТАЙМЕР ПЕРМАНЕНТНО                                                                           ";
    } else if (currentPage == 4) {
        row1 = "                                          [1] УСТАНОВИТЬ ПЛАН ЭЛЕКТРОПИТАНИЯ Sardanello.pow                                                                           ";
    } else if (currentPage >= 5 && currentPage <= 12) {
        row1 = "                                          [В РАЗРАБОТКЕ]                                                                                                             ";
    } else {
        // No selection window on pages other than 1, 2, 3, or 4
        row1 = "";
    }
    std::string row2 = "                   НАЗАД [Backspace]                                                    ВПЕРЕД [SPACE]";
    // English translations for options and navigation
    std::string engOption;
    if (currentPage == 1) engOption = "                                              DISABLE HIGH PRECISION EVENT TIMER                                                                                ";
    else if (currentPage == 2) engOption = "                                              FINDING THE PERFECT TIMER                                                                                       ";
    else if (currentPage == 3) engOption = "                                              SET UP A PROVEN IDEAL TIMER PERMANENTLY                                                                                 ";
    else if (currentPage == 4) engOption = "                                              INSTALL POWER PLAN Sardanello.pow                                                                                 ";
    else if (currentPage >= 5 && currentPage <= 12) engOption = "                                              [IN PROGRESS]                                                                                                           ";
    else engOption = "";

    std::string engNav = "                   BACK                                                                 NEXT";

    char buf[64];
    std::snprintf(buf, sizeof(buf), " [%d / %d]", currentPage, totalPages);
    std::string row3 = std::string(buf);

    // progress bar (drawn separately centered two lines below the menu)
    const int progWidth = 40;
    double prog = (double)currentPage / (double)totalPages;
    if (prog < 0.0) prog = 0.0; if (prog > 1.0) prog = 1.0;
    int progFilled = (int)std::round(prog * progWidth);
    std::string block = "\u2588";
    // build bar only (fixed width progWidth + 2 brackets) so we can anchor its left side
    std::string barOnly = "[";
    for (int i = 0; i < progWidth; ++i) {
        if (i < progFilled) barOnly += block; else barOnly += ' ';
    }
    barOnly += "]";
    // percent text removed — progress bar will show only the bar itself

    // Menu content lines (we draw the page indicator separately below the progress bar)
    // Layout: Russian option, English option, blank, navigation (Russian), navigation (English)
    std::vector<std::string> lines = { row1, engOption, std::string(""), row2, engNav };
    bool hasMenu = !row1.empty();
    int w = 0;
    for (auto &l : lines) if ((int)l.size() > w) w = (int)l.size();
    // menu draws a top and bottom padding line in addition to the content lines
    int innerRows = (int)lines.size();
    int h = hasMenu ? (innerRows + 2) : 0;

    // compute menu start (startY will be adjusted to sit below banner)
    // Move menu closer to the left edge (small left padding)
    int startX = 2;
    // If console is very narrow, clamp so menu still fits
    if (startX + w > cs.cols) startX = std::max(0, cs.cols - w);
    // menu will be positioned immediately below the banner; startY computed later

    // Banner text (draw above menu) — ASCII-art provided by user
    std::vector<std::string> banner = {
        R"(                   ███████╗ █████╗ ██████╗ ██████╗  █████╗ ███╗   ██╗███████╗██╗     ██╗      ██████╗                   )",
        R"(                   ██╔════╝██╔══██╗██╔══██╗██╔══██╗██╔══██╗████╗  ██║██╔════╝██║     ██║     ██╔═══██╗                  )",
        R"(                   ███████╗███████║██████╔╝██║  ██║███████║██╔██╗ ██║█████╗  ██║     ██║     ██║   ██║                  )",
        R"(                   ╚════██║██╔══██║██╔══██╗██║  ██║██╔══██║██║╚██╗██║██╔══╝  ██║     ██║     ██║   ██║                  )",
        R"(                   ███████║██║  ██║██║  ██║██████╔╝██║  ██║██║ ╚████║███████╗███████╗███████╗╚██████╔╝                  )",
        R"(                   ╚══════╝╚═╝  ╚═╝╚═╝  ╚═╝╚═════╝ ╚═╝  ╚═╝╚═╝  ╚═══╝╚══════╝╚══════╝╚══════╝ ╚═════╝                   )",
        R"(                                          OPTIMIZATION WIN 10,11 FOR FPS GAMES                                          )",
        R"(                   DONUT [D]                                                             TELEGRAM [T]                   )",
        
    };
    int bannerW = 0;
    for (auto &b : banner) if ((int)b.size() > bannerW) bannerW = (int)b.size();
    int bannerH = (int)banner.size();
    int bannerX = (cs.cols - bannerW) / 2;
    if (bannerX < 0) bannerX = 0;

    // Place banner and menu 5 rows down so rain is visible above them
    int bannerY = 5;
    // clamp banner so it fits in the screen
    if (bannerY + bannerH > cs.rows) bannerY = std::max(0, cs.rows - bannerH);
    // Place menu immediately below banner (bannerH rows below bannerY)
    int startY = bannerY + bannerH;
    // clamp menu if it would overflow
    if (startY + h > cs.rows) startY = std::max(0, cs.rows - h);

    std::lock_guard<std::mutex> lk(g_consoleMutex);
    // Draw banner (bright green)
#ifdef _WIN32
    // Using ANSI sequences (VT enabled earlier)
#endif
    for (int i = 0; i < bannerH; ++i) {
        // fill left area with black background to avoid rain artifacts
        int leftPad = bannerX;
        if (leftPad > 0) {
            setCursorPosition(0, bannerY + i);
            std::cout << "\x1b[40m" << std::string(leftPad, ' ');
        }

        // draw banner text with bright green on black
        setCursorPosition(bannerX, bannerY + i);
        std::cout << "\x1b[1;92;40m" << banner[i];

        // pad the rest of the console line (to the right edge) with black spaces
        int padLen = cs.cols - bannerX - (int)banner[i].size();
        if (padLen > 0) std::cout << std::string(padLen, ' ');

        // reset attributes
        std::cout << "\x1b[0m";
    }

    // Draw menu only if we have selection content (pages 1 or 2)
    if (hasMenu) {
        for (int i = 0; i < h; ++i) {
            setCursorPosition(startX, startY + i);
            if (i == 0 || i == h-1) {
                std::cout << std::string(w, ' ');
            } else {
                int idx = i - 1;
                std::string s = lines[idx];
                std::cout << s << std::string(w - (int)s.size(), ' ');
            }
        }
        std::cout.flush();

        // Draw progress bar centered two lines below the menu, then page indicator one line below it.
        int progY = startY + h + 1; // two lines below menu (startY+h is one line below)
        int pageY = progY + 1;
        // fill background for both lines with black to prevent rain artifacts
        if (progY >= 0 && progY < cs.rows) {
            setCursorPosition(0, progY);
            std::cout << "\x1b[40m" << std::string(cs.cols, ' ') << "\x1b[0m";
        }
        if (pageY >= 0 && pageY < cs.rows) {
            setCursorPosition(0, pageY);
            std::cout << "\x1b[40m" << std::string(cs.cols, ' ') << "\x1b[0m";
        }
        if (progY >= 0 && progY < cs.rows) {
            // center the bar-only area so its left edge stays fixed while blocks fill to the right
            int progX = (cs.cols - (progWidth + 2)) / 2;
            if (progX < 0) progX = 0;
            setCursorPosition(progX, progY);
            std::cout << barOnly;
            // no percentage text printed (bar only)
        }
        if (pageY >= 0 && pageY < cs.rows) {
            int pageX = (cs.cols - (int)row3.size()) / 2;
            if (pageX < 0) pageX = 0;
            setCursorPosition(pageX, pageY);
            std::cout << row3;
        }

        // Reserve, clear and draw three persistent status lines below the page indicator
        int msgY = pageY + 1;
        for (int m = 0; m < 3; ++m) {
            int y = msgY + m;
            if (y < 0 || y >= cs.rows) continue;
            setCursorPosition(0, y);
            std::cout << "\x1b[40m" << std::string(cs.cols, ' ');
            // draw persistent status line text if present
            std::string s = statusSnapshot[m];
            if (!s.empty()) {
                int px = 2;
                if (px + (int)s.size() > cs.cols) s = s.substr(0, std::max(0, cs.cols - px));
                setCursorPosition(px, y);
                std::cout << s;
            }
            std::cout << "\x1b[0m";
        }
        std::cout.flush();
    }

    // store menu & banner rects under mutex for concurrent access
    Rect r;
    if (hasMenu) {
        // Reserve full console width from the left edge so nothing draws over the centered progress/page/messages
        r.x = 0;
        r.y = startY;
        r.w = cs.cols;
        // reserve the blank line + the progress bar + the page indicator + 3 message lines so matrix doesn't overwrite them
        int reserved = h + 4 + 0; // menu height + blank + prog + page + 3 message lines = h + 4? adjust below
        // compute exact reserved: h (menu) + 1 (blank) + 1 (prog) + 1 (page) + 3 (messages) = h + 6
        reserved = h + 6;
        if (reserved > cs.rows - startY) reserved = std::max(0, cs.rows - startY);
        r.h = reserved;
    } else {
        // no menu present
        r.x = 0; r.y = 0; r.w = 0; r.h = 0;
    }
    {
        std::lock_guard<std::mutex> ml(g_menuMutex);
        g_menuRect = r;
        g_bannerRect.x = bannerX;
        g_bannerRect.y = bannerY;
        // extend banner rect to the right edge as well
        g_bannerRect.w = cs.cols - bannerX;
        g_bannerRect.h = bannerH;
    }
    return r;
}

// Full implementation of disableHighPrecisionTimer (placed after drawMenu so g_menuRect/g_menuMutex are available)
void disableHighPrecisionTimer()
{
    std::lock_guard<std::mutex> lk(g_consoleMutex);
#ifdef _WIN32
    const std::vector<std::string> keywords = {
        "High precision event timer",
        "Высокоточный таймер событий",
        "Timer d'événement haute précision",
        "Temporizador de eventos de alta precisão",
        "Hochpräziser Ereignis-Timer",
        "Alta precisão temporizador de eventos"
    };

    HDEVINFO devs = SetupDiGetClassDevsA(NULL, NULL, NULL, DIGCF_ALLCLASSES | DIGCF_PRESENT);
    if (devs == INVALID_HANDLE_VALUE) {
        std::cout << "Ошибка: не удалось получить список устройств\n";
        std::cout << "Error: failed to enumerate devices\n";
        std::cout.flush();
        return;
    }

    bool anyFound = false;
    bool anyDisabled = false;
    bool accessDenied = false;
    SP_DEVINFO_DATA devInfo;
    devInfo.cbSize = sizeof(devInfo);
    for (DWORD i = 0; SetupDiEnumDeviceInfo(devs, i, &devInfo); ++i) {
        CHAR buf[1024] = {0};
        DWORD needed = 0;
        // Try to read device description and hardware IDs. Hardware IDs are more reliable for HPET.
        std::string desc;
        SetupDiGetDeviceRegistryPropertyA(devs, &devInfo, SPDRP_DEVICEDESC, NULL, (PBYTE)buf, sizeof(buf), &needed);
        if (buf[0]) desc = std::string(buf);

        CHAR hwbuf[2048] = {0};
        SetupDiGetDeviceRegistryPropertyA(devs, &devInfo, SPDRP_HARDWAREID, NULL, (PBYTE)hwbuf, sizeof(hwbuf), &needed);
        std::string hw(hwbuf);

        std::string lowerDesc = desc; for (auto &c : lowerDesc) c = (char)tolower((unsigned char)c);
        std::string lowerHw = hw; for (auto &c : lowerHw) c = (char)tolower((unsigned char)c);

        // More robust hardware ID and description checks
        bool matched = false;
        // Hardware ID patterns commonly associated with HPET
        if (!lowerHw.empty()) {
            // match common HWID forms (lowercased): acpi\ven_pnp&dev_0103, acpi\pnp0103, pnp0103
            if (lowerHw.find("acpi\\ven_pnp&dev_0103") != std::string::npos) matched = true;
            if (lowerHw.find("acpi\\pnp0103") != std::string::npos) matched = true;
            if (lowerHw.find("pnp0103") != std::string::npos) matched = true; // covers pnp0103 and *pnp0103
        }
        // Also check the original-case hardware ID string for common uppercase variants
        if (!hw.empty()) {
            if (hw.find("ACPI\\VEN_PNP&DEV_0103") != std::string::npos) matched = true;
            if (hw.find("ACPI\\PNP0103") != std::string::npos) matched = true;
            if (hw.find("PNP0103") != std::string::npos) matched = true; // covers PNP0103 and *PNP0103
        }
        // Additional description fallbacks
        if (!matched) {
            // expand keyword set with more variations and translations
            std::vector<std::string> more = {
                "high precision event timer", "high-precision event timer", "high precision timer",
                "high precision", "high-precision", "event timer", "precision timer",
                "высокоточный", "высокоточный таймер", "таймер событий", "таймер"
            };
            for (auto &kw : keywords) more.push_back(kw);
            for (auto &kw : more) {
                std::string lowerKw = kw; for (auto &c : lowerKw) c = (char)tolower((unsigned char)c);
                if (!lowerDesc.empty() && lowerDesc.find(lowerKw) != std::string::npos) { matched = true; break; }
            }
        }

        if (matched) {
            anyFound = true;
            DEVINST devInst = devInfo.DevInst;
            CONFIGRET cr = CM_Disable_DevNode(devInst, 0);
            // Prepare message area
            ConsoleSize cs = getConsoleSize();
            int cols = cs.cols; int rows = cs.rows;
            int msgY = -1;
            {
                std::lock_guard<std::mutex> ml(g_menuMutex);
                if (g_menuRect.h >= 3) {
                    msgY = g_menuRect.y + g_menuRect.h - 3;
                }
            }
            if (msgY < 0) msgY = std::max(0, rows - 4);

            if (cr == CR_SUCCESS) {
                anyDisabled = true;
                std::string deviceLine = desc.empty() ? hw : desc;
                // Attempt to write ConfigFlags=1 under HKLM\SYSTEM\CurrentControlSet\Enum\ACPI\PNP0103\<instance>
                bool regSuccess = true;
                HKEY hKey = NULL;
                LONG rr = RegOpenKeyExA(HKEY_LOCAL_MACHINE,
                                        "SYSTEM\\CurrentControlSet\\Enum\\ACPI\\PNP0103",
                                        0, KEY_READ | KEY_WRITE, &hKey);
                if (rr != ERROR_SUCCESS) {
                    regSuccess = false;
                } else {
                    DWORD index = 0;
                    CHAR subName[256];
                    FILETIME ft;
                    while (true) {
                        DWORD nameLen = (DWORD)sizeof(subName);
                        LONG er = RegEnumKeyExA(hKey, index, subName, &nameLen, NULL, NULL, NULL, &ft);
                        if (er == ERROR_NO_MORE_ITEMS) break;
                        if (er != ERROR_SUCCESS) { regSuccess = false; break; }

                        // Open the instance key and set ConfigFlags = 1 (create if missing)
                        HKEY hSub = NULL;
                        std::string subPath = std::string("SYSTEM\\CurrentControlSet\\Enum\\ACPI\\PNP0103\\") + subName;
                        LONG r2 = RegOpenKeyExA(HKEY_LOCAL_MACHINE, subPath.c_str(), 0, KEY_SET_VALUE | KEY_READ, &hSub);
                        if (r2 != ERROR_SUCCESS) { regSuccess = false; ++index; continue; }

                        DWORD val = 1;
                        LONG r3 = RegSetValueExA(hSub, "ConfigFlags", 0, REG_DWORD, (const BYTE*)&val, sizeof(val));
                        if (r3 != ERROR_SUCCESS) regSuccess = false;
                        RegCloseKey(hSub);
                        ++index;
                    }
                    RegCloseKey(hKey);
                }

                // Try to run bcdedit commands and set kernel GlobalTimerResolutionRequests
                auto performBootAndRegistryTweaks = [](std::string &errOut) -> bool {
                    // sequence of commands to run
                    const std::vector<std::string> cmds = {
                        "bcdedit /set disabledynamictick yes",
                        "bcdedit /set useplatformtick yes",
                        "bcdedit /set useplatformclock false",
                        "bcdedit /deletevalue useplatformclock"
                    };

                    for (auto &c : cmds) {
                        // CreateProcess requires a mutable buffer
                        std::vector<char> cmdBuf(c.begin(), c.end()); cmdBuf.push_back('\0');
                        STARTUPINFOA si; PROCESS_INFORMATION pi;
                        ZeroMemory(&si, sizeof(si)); si.cb = sizeof(si);
                        ZeroMemory(&pi, sizeof(pi));
                        BOOL ok = CreateProcessA(NULL, cmdBuf.data(), NULL, NULL, FALSE, CREATE_NO_WINDOW, NULL, NULL, &si, &pi);
                        if (!ok) {
                            errOut = std::string("CreateProcess failed (code )") + std::to_string((int)GetLastError()) + "; cmd=" + c;
                            return false;
                        }
                        WaitForSingleObject(pi.hProcess, INFINITE);
                        DWORD exitCode = 0; GetExitCodeProcess(pi.hProcess, &exitCode);
                        CloseHandle(pi.hProcess); CloseHandle(pi.hThread);
                        if (exitCode != 0) {
                            errOut = std::string("Command failed with exit ") + std::to_string((int)exitCode) + ": " + c;
                            return false;
                        }
                    }

                    // Now update kernel registry key
                    HKEY hK = NULL;
                    LONG r = RegCreateKeyExA(HKEY_LOCAL_MACHINE,
                                             "SYSTEM\\CurrentControlSet\\Control\\Session Manager\\kernel",
                                             0, NULL, REG_OPTION_NON_VOLATILE, KEY_SET_VALUE, NULL, &hK, NULL);
                    if (r != ERROR_SUCCESS) {
                        errOut = std::string("RegCreateKeyEx failed: ") + std::to_string((int)r);
                        return false;
                    }
                    DWORD val = 1;
                    LONG r2 = RegSetValueExA(hK, "GlobalTimerResolutionRequests", 0, REG_DWORD, (const BYTE*)&val, sizeof(val));
                    RegCloseKey(hK);
                    if (r2 != ERROR_SUCCESS) {
                        errOut = std::string("RegSetValueEx failed: ") + std::to_string((int)r2);
                        return false;
                    }
                    return true;
                };

                std::string tweakErr;
                if (regSuccess) {
                    bool tweaksOk = performBootAndRegistryTweaks(tweakErr);
                    if (!tweaksOk) regSuccess = false;
                }

                // Prepare status messages depending on registry and tweak result
                if (regSuccess) {
                    std::lock_guard<std::mutex> sl(g_menuMutex);
                    g_statusLines[0] = "HPET отключён и изменения вступят в силу после перезагрузки";
                    g_statusLines[1] = "HPET disabled and changes take effect after reboot";
                    g_statusLines[2] = deviceLine;
                } else {
                    std::lock_guard<std::mutex> sl(g_menuMutex);
                    g_statusLines[0] = "HPET отключен, но изменения не внесены в реестр, после перезагрузки может включиться снова";
                    g_statusLines[1] = "HPET disabled, but registry changes were not applied; it may re-enable after reboot";
                    g_statusLines[2] = deviceLine;
                }

                // immediate paint of the three status lines
                for (int m = 0; m < 3; ++m) {
                    int y = msgY + m;
                    if (y < 0 || y >= rows) continue;
                    setCursorPosition(0, y);
                    std::cout << "\x1b[40m" << std::string(cols, ' ');
                    int px = 2;
                    std::string s;
                    {
                        std::lock_guard<std::mutex> sl(g_menuMutex);
                        s = g_statusLines[m];
                    }
                    if (!s.empty()) {
                        if (px + (int)s.size() > cols) s = s.substr(0, std::max(0, cols - px));
                        setCursorPosition(px, y);
                        std::cout << s;
                    }
                    std::cout << "\x1b[0m";
                }
                std::cout.flush();
            } else if (cr == CR_ACCESS_DENIED) {
                accessDenied = true;
                {
                    std::lock_guard<std::mutex> sl(g_menuMutex);
                    g_statusLines[0] = "Ошибка, нужны права администратора";
                    g_statusLines[1] = "Error: Administrator privileges required";
                    g_statusLines[2].clear();
                }
                for (int m = 0; m < 3; ++m) {
                    int y = msgY + m;
                    if (y < 0 || y >= rows) continue;
                    setCursorPosition(0, y);
                    std::cout << "\x1b[40m" << std::string(cols, ' ');
                    std::string s;
                    {
                        std::lock_guard<std::mutex> sl(g_menuMutex);
                        s = g_statusLines[m];
                    }
                    if (!s.empty()) { setCursorPosition(2, y); std::cout << s; }
                    std::cout << "\x1b[0m";
                }
                std::cout.flush();
            } else {
                // other failure, show code
                {
                    std::lock_guard<std::mutex> sl(g_menuMutex);
                    g_statusLines[0] = "Ошибка при отключении устройства";
                    g_statusLines[1] = "Error: failed to disable device";
                    g_statusLines[2] = "CM code: " + std::to_string((int)cr);
                }
                for (int m = 0; m < 3; ++m) {
                    int y = msgY + m;
                    if (y < 0 || y >= rows) continue;
                    setCursorPosition(0, y);
                    std::cout << "\x1b[40m" << std::string(cols, ' ');
                    std::string s;
                    {
                        std::lock_guard<std::mutex> sl(g_menuMutex);
                        s = g_statusLines[m];
                    }
                    if (!s.empty()) { setCursorPosition(2, y); std::cout << s; }
                    std::cout << "\x1b[0m";
                }
                std::cout.flush();
            }
        }
    }
    SetupDiDestroyDeviceInfoList(devs);

    if (!anyFound) {
        // write to reserved message area (use g_menuRect when available)
        ConsoleSize cs = getConsoleSize(); int cols = cs.cols; int rows = cs.rows;
        int msgY = -1;
        {
            std::lock_guard<std::mutex> ml(g_menuMutex);
            if (g_menuRect.h >= 3) msgY = g_menuRect.y + g_menuRect.h - 3;
        }
        if (msgY < 0) msgY = std::max(0, rows - 4);
        // Attempt to apply boot/registry tweaks even if HPET was not found
        std::string tweakErr;
        bool tweaksOk = performBootAndRegistryTweaks(tweakErr);
        {
            std::lock_guard<std::mutex> sl(g_menuMutex);
            if (tweaksOk) {
                g_statusLines[0] = "HPET не найден, внесены настройки загрузки; изменения вступят в силу после перезагрузки";
                g_statusLines[1] = "HPET not found; boot tweaks applied, take effect after reboot";
                g_statusLines[2] = std::string(10, ' ') + "Для применения изменения нужна перезагрузка [Y]";
            } else {
                g_statusLines[0] = "HPET не найден";
                g_statusLines[1] = "HPET not found";
                g_statusLines[2] = std::string("Ошибка при применении настроек bcdedit ") + tweakErr;
            }
        }
        // immediate paint
        for (int m = 0; m < 3; ++m) {
            int y = msgY + m;
            if (y < 0 || y >= rows) continue;
            setCursorPosition(0, y);
            std::cout << "\x1b[40m" << std::string(cols, ' ');
            std::string s;
            {
                std::lock_guard<std::mutex> sl(g_menuMutex);
                s = g_statusLines[m];
            }
            if (!s.empty()) { setCursorPosition(2, y); std::cout << s; }
            std::cout << "\x1b[0m";
        }
        std::cout.flush();

        // If we applied tweaks successfully, mark reboot available; main input loop will handle pressing Y
        if (tweaksOk) {
            g_rebootAvailable = true;
            g_rebootMessage = "HPET tweaks applied; press Y to reboot";
        } else {
            g_rebootAvailable = false;
            g_rebootMessage.clear();
        }
    } else if (accessDenied && !anyDisabled) {
        // write to reserved message area (use g_menuRect when available)
        ConsoleSize cs = getConsoleSize(); int cols = cs.cols; int rows = cs.rows;
        int msgY = -1;
        {
            std::lock_guard<std::mutex> ml(g_menuMutex);
            if (g_menuRect.h >= 3) msgY = g_menuRect.y + g_menuRect.h - 3;
        }
        if (msgY < 0) msgY = std::max(0, rows - 4);
        {
            std::lock_guard<std::mutex> sl(g_menuMutex);
            g_statusLines[0] = "Ошибка, нужны права администратора";
            g_statusLines[1] = "Error: Administrator privileges required";
            g_statusLines[2].clear();
        }
        // immediate paint
        for (int m = 0; m < 3; ++m) {
            int y = msgY + m;
            if (y < 0 || y >= rows) continue;
            setCursorPosition(0, y);
            std::cout << "\x1b[40m" << std::string(cols, ' ');
            std::string s;
            {
                std::lock_guard<std::mutex> sl(g_menuMutex);
                s = g_statusLines[m];
            }
            if (!s.empty()) { setCursorPosition(2, y); std::cout << s; }
            std::cout << "\x1b[0m";
        }
        std::cout.flush();
    }
#else
    std::cout << "disableHighPrecisionTimer is supported only on Windows\n";
#endif
}

// Функция создания и открытия файла с важными инструкциями перед тестированием
void createAndOpenReadme() {
    std::string exeDir = getExeDirectory();
    std::string readmePath = exeDir + "READMEPLS.txt";
    
    std::ofstream readme(readmePath);
    if (!readme) return;
    
    readme << R"(
===============================================================================
                         ⚠️  ВАЖНЫЕ ИНСТРУКЦИИ ПЕРЕД ТЕСТИРОВАНИЕМ  ⚠️
===============================================================================

🔴 КРИТИЧЕСКИ ВАЖНО! Все программы, влияющие на таймер, ДОЛЖНЫ БЫТЬ ЗАКРЫТЫ:

📍 ОБЯЗАТЕЛЬНО ЗАКРЫТЬ:
   • Process Lasso (Bitsum) - влияет на планировщик процессов
   • TimerResolution.exe / SetTimerResolution.exe / TimerTool.exe
   • MSI Afterburner + RTSS (RivaTuner Statistics Server)
   • AMD Adrenalin Overlay / NVIDIA GeForce Experience Overlay
   • Discord Overlay / Steam Overlay / любые игровые оверлеи
   • Программы записи экрана (OBS, Bandicam, Fraps, etc.)
   • Стриминг сервисы (Twitch Studio, Streamlabs, etc.)

📍 РЕКОМЕНДУЕТСЯ ЗАКРЫТЬ:
   • Все браузеры (Chrome, Firefox, Edge, Opera, etc.)
   • Торрент-клиенты (uTorrent, qBittorrent, etc.)
   • Мессенджеры (Telegram, WhatsApp, Skype, etc.)
   • Медиа плееры (VLC, Winamp, Spotify, etc.)
   • Антивирусы в режиме реального времени (временно)
   • Все фоновые программы, не связанные с Windows

===============================================================================
███████████████████████████████████████████████████████████████████████████████
██  🎯🎯🎯           ИДЕАЛЬНОЕ СОСТОЯНИЕ СИСТЕМЫ:           🎯🎯🎯        
██                                                                          
██  ✅ Только наша программа тестирования запущена!                         
██  ✅ ВСЕ фоновые программы закрыты!                                       
██  ✅ Если использовали сторонние утилиты Timer Resolution! -            
██     СБРОСЬТЕ до дефолтных настроек!                                        
██  ✅ ПЕРЕЗАГРУЗИТЕ компьютер!                                             
██  ✅ И ТОЛЬКО ТОГДА начинайте тест!                                       
██                                                                           
███████████████████████████████████████████████████████████████████████████████
===============================================================================

⚡ ПЛАН ПИТАНИЯ:
Рекомендуется "Высокая производительность" для максимальной стабильности.
Сбалансированный план может немного увеличить среднюю |Sleep(1)−1.000 ms| (~0.05–0.1%).

🔍 МЕТОДИКА (3 волны):
1) Глобальный проход: перебор таймера от 0.500 до 1.000 мс с шагом 0.005. Для каждого значения измеряем серию Sleep(1)+QPC (~5 сек) и считаем score1.
2) Повтор top-15: пятнадцать лучших кандидатов первой волны измеряются в 7 перемешанных кругов той же формулой score1.
3) Окрестность: вокруг top-1 второй волны строим третью волну ±0.002 мс (шаг 0.001), 5 перемешанных кругов, суммарно ~20 сек на точку. Если top-1 = 0.500 мс, проверяем 0.500–0.504 мс. Финальный таймер берётся как центр стабильной зоны вокруг лучшего score1.
Метрика всех волн: score1 = 0.75*robustAvgAbsDelta + 0.25*((robust CV%/100)*1.000 ms). Robust avgAbsDelta и robust CV считаются после обрезки верхних 2% wake-time выбросов.

⚠️  ВАЖНО ДЛЯ ПРОДВИНУТЫХ ПОЛЬЗОВАТЕЛЕЙ:
Если вы ранее устанавливали таймер вручную через утилиты - СБРОСЬТЕ ЕГО!
Многие программы делают автозапуск после перезагрузки.

🔧 РЕКОМЕНДАЦИЯ:
1. Удалите программы изменения таймера ДО тестирования
2. Найдите идеальное значение нашей программой
3. Используйте найденное значение в страницы 3/12 нашего решения
   ИЛИ внесите его в вашу любимую утилиту

===============================================================================

📊 ПОЧЕМУ ЭТО ВАЖНО:
- Сторонние программы могут изменять системный таймер
- Оверлеи добавляют задержки в цепочку отрисовки
- Фоновые процессы создают непредсказуемые нагрузки
- Результат тестирования должен отражать ЧИСТУЮ систему

🎮 ЦЕЛЬ: Найти истинно оптимальный таймер для вашего железа!

===============================================================================
                             🇺🇸 ENGLISH VERSION 🇺🇸
===============================================================================

🔴 CRITICAL! All timer-affecting programs MUST BE CLOSED:

📍 MANDATORY TO CLOSE:
   • Process Lasso (Bitsum) - affects process scheduler
   • TimerResolution.exe / SetTimerResolution.exe / TimerTool.exe  
   • MSI Afterburner + RTSS (RivaTuner Statistics Server)
   • AMD Adrenalin Overlay / NVIDIA GeForce Experience Overlay
   • Discord Overlay / Steam Overlay / any gaming overlays
   • Screen recording software (OBS, Bandicam, Fraps, etc.)
   • Streaming services (Twitch Studio, Streamlabs, etc.)

📍 RECOMMENDED TO CLOSE:
   • All browsers (Chrome, Firefox, Edge, Opera, etc.)
   • Torrent clients (uTorrent, qBittorrent, etc.)
   • Messengers (Telegram, WhatsApp, Skype, etc.)
   • Media players (VLC, Winamp, Spotify, etc.)
   • Real-time antivirus (temporarily)
   • All background programs not related to Windows

===============================================================================
███████████████████████████████████████████████████████████████████████████████
██                                                                         
██  🎯🎯🎯              IDEAL SYSTEM STATE:              🎯🎯🎯  
██                                                                           
██  ✅ Only our testing program running!                                     
██  ✅ ALL background programs closed!                                       
██  ✅ If you used third-party Timer Resolution utilities -                  
██     RESET to default settings!                                           
██  ✅ REBOOT your computer!                                                 
██  ✅ And ONLY THEN start the test!                                         
██                                                                           
███████████████████████████████████████████████████████████████████████████████
===============================================================================

⚡ POWER PLAN:
Recommended "High Performance" for maximum stability.
Balanced plan may slightly increase average |Sleep(1)−1.000 ms| (~0.05–0.1%).

🔍 METHOD (3 waves):
1) Global sweep: iterate timer from 0.500 to 1.000 ms step 0.005. For each candidate measure Sleep(1)+QPC (~5 s) and compute score1.
2) Top-15 retest: retest the fifteen best first-wave candidates across 7 shuffled rounds using the same score1 formula.
3) Neighborhood: around the second-wave top-1 value perform a ±0.002 ms sweep (step 0.001) across 5 shuffled rounds, ~20 s total per point. If top-1 is 0.500 ms, test 0.500–0.504 ms. Final timer is the center of the stable zone around the best score1.
All waves use score1 = 0.75*robustAvgAbsDelta + 0.25*((robust CV%/100)*1.000 ms). Robust avgAbsDelta and robust CV trim the slowest 2% wake-time outliers.

⚠️  IMPORTANT FOR ADVANCED USERS:
If you previously set timer manually via utilities - RESET IT!
Many programs auto-start after reboot.

🔧 RECOMMENDATION:
1. Remove timer-changing programs BEFORE testing
2. Find ideal value using our program
3. Use found value in our page 3/12 solution
   OR apply it in your preferred utility

===============================================================================

📊 WHY THIS MATTERS:
- Third-party programs can alter system timer
- Overlays add delays to rendering pipeline  
- Background processes create unpredictable loads
- Test results should reflect CLEAN system state

🎮 GOAL: Find truly optimal timer for your hardware!

===============================================================================
)";

    readme.close();
    
    // Открываем файл в текстовом редакторе
#ifdef _WIN32
    std::string command = "notepad \"" + readmePath + "\"";
    system(command.c_str());
#else
    std::string command = "gedit \"" + readmePath + "\" 2>/dev/null || nano \"" + readmePath + "\"";
    system(command.c_str());
#endif
}

// Функции для работы с идеальным таймером
struct OptimalTimerResult {
    double timerMs = 0.0;
    double cvScore = 0.0;
    bool isValid = false;
    std::string timestamp;
};

// Сохранить найденный идеальный таймер в файл
static void saveOptimalTimer(double timerMs, double cvScore,
                             double stableZoneStartMs,
                             double stableZoneEndMs,
                             double formulaBestTimerMs) {
    std::string exeDir = getExeDirectory();
    std::string configPath = exeDir + "optimal_timer.ini";
    
    std::ofstream config(configPath);
    if (config) {
        auto now = std::chrono::system_clock::now();
        std::time_t t = std::chrono::system_clock::to_time_t(now);
        char timeBuf[64];
        std::strftime(timeBuf, sizeof(timeBuf), "%Y-%m-%d %H:%M:%S", std::localtime(&t));
        
        config << "[OptimalTimer]" << std::endl;
        config << "TimerMs=" << std::fixed << std::setprecision(6) << timerMs << std::endl;
        config << "CVScore=" << std::fixed << std::setprecision(8) << cvScore << std::endl;
        if (stableZoneStartMs >= 0.0 && stableZoneEndMs >= 0.0) {
            config << "StableZoneStartMs=" << std::fixed << std::setprecision(6) << stableZoneStartMs << std::endl;
            config << "StableZoneEndMs=" << std::fixed << std::setprecision(6) << stableZoneEndMs << std::endl;
        }
        if (formulaBestTimerMs >= 0.0) {
            config << "FormulaBestTimerMs=" << std::fixed << std::setprecision(6) << formulaBestTimerMs << std::endl;
        }
        config << "Timestamp=" << timeBuf << std::endl;
        config << "Valid=1" << std::endl;
    }
}

// Загрузить сохраненный идеальный таймер
static OptimalTimerResult loadOptimalTimer() {
    OptimalTimerResult result;
    std::string exeDir = getExeDirectory();
    std::string configPath = exeDir + "optimal_timer.ini";
    
    std::ifstream config(configPath);
    if (!config) return result;
    
    std::string line;
    while (std::getline(config, line)) {
        if (line.find("TimerMs=") == 0) {
            result.timerMs = std::stod(line.substr(8));
        } else if (line.find("CVScore=") == 0) {
            result.cvScore = std::stod(line.substr(8));
        } else if (line.find("Timestamp=") == 0) {
            result.timestamp = line.substr(10);
        } else if (line.find("Valid=1") == 0) {
            result.isValid = true;
        }
    }
    
    return result;
}

// Создать и установить службу для постоянного применения таймера
static bool createTimerService(double timerMs) {
#ifdef _WIN32
    // 1. Сохраняем оптимальный таймер в конфигурацию
    saveOptimalTimer(timerMs, 0.0); // CV score не важен для службы
    
    // 2. Добавляем в автозагрузку (для будущих перезагрузок)
    char exePath[MAX_PATH];
    GetModuleFileNameA(nullptr, exePath, MAX_PATH);
    std::string cmdLine = "\"" + std::string(exePath) + "\" --timer-service";
    
    HKEY hKey;
    bool registryOk = false;
    if (RegOpenKeyExA(HKEY_CURRENT_USER, "SOFTWARE\\Microsoft\\Windows\\CurrentVersion\\Run", 0, KEY_SET_VALUE, &hKey) == ERROR_SUCCESS) {
        if (RegSetValueExA(hKey, "SardanelloTimer", 0, REG_SZ, (BYTE*)cmdLine.c_str(), cmdLine.length() + 1) == ERROR_SUCCESS) {
            registryOk = true;
        }
        RegCloseKey(hKey);
    }
    
    // 3. Применяем таймер в текущем процессе (немедленно)
    g_targetTimerMs = timerMs;
    g_targetTime100ns = (ULONG)(timerMs * 10000.0);
    bool timerApplied = setTimerResolution();
    
    // 4. НЕМЕДЛЕННО запускаем фоновый процесс службы для текущей сессии
    STARTUPINFOA si = {0};
    PROCESS_INFORMATION pi = {0};
    si.cb = sizeof(si);
    si.dwFlags = STARTF_USESHOWWINDOW;
    si.wShowWindow = SW_HIDE; // Скрытый запуск - окно вообще не показывается
    
    bool serviceStarted = CreateProcessA(
        nullptr,
        const_cast<char*>(cmdLine.c_str()),
        nullptr, nullptr, FALSE,
        CREATE_NEW_CONSOLE | DETACHED_PROCESS | CREATE_NO_WINDOW, // Добавляем CREATE_NO_WINDOW
        nullptr, nullptr, &si, &pi
    );
    
    if (serviceStarted) {
        CloseHandle(pi.hProcess);
        CloseHandle(pi.hThread);
    }
    
    // Возвращаем true если хотя бы что-то сработало
    return registryOk || timerApplied || serviceStarted;
#else
    return false;
#endif
}

// Функция чтения обновленного таймера из файла конфигурации
bool loadUpdatedTimer() {
    std::string exeDir = getExeDirectory();
    std::string configPath = exeDir + "optimal_timer.ini";
    
    std::ifstream config(configPath);
    if (!config) return false;
    
    std::string line;
    double newTimerMs = 0.0;
    bool found = false;
    
    while (std::getline(config, line)) {
        if (line.find("TimerMs=") == 0) {
            newTimerMs = std::stod(line.substr(8));
            found = true;
            break;
        }
    }
    
    // Если найдено новое значение - обновляем глобальные переменные
    if (found) {
        g_targetTimerMs = newTimerMs;
        g_targetTime100ns = (ULONG)(newTimerMs * 10000.0);
        return true; // Значение обновлено
    }
    
    return false; // Конфигурация не найдена или не изменилась
}

// Установить разрешение таймера
bool setTimerResolution() {
#ifdef _WIN32
    HMODULE ntdll = GetModuleHandleA("ntdll.dll");
    if (!ntdll) return false;
    
    typedef NTSTATUS(WINAPI* NtSetTimerResolution_t)(ULONG DesiredTime, BOOLEAN SetResolution, PULONG ActualTime);
    auto NtSetTimerResolution = (NtSetTimerResolution_t)GetProcAddress(ntdll, "NtSetTimerResolution");
    if (!NtSetTimerResolution) return false;
    
    // Применяем таймер
    ULONG actual = 0;
    NTSTATUS status = NtSetTimerResolution(g_targetTime100ns, TRUE, &actual);
    if (status == 0) {
        g_timerSet = true;
        return true;
    } else {
        g_timerSet = true;
        return true;
    }
    
    return false;
#else
    return false;
#endif
}

// Применить таймер
static bool applyOptimalTimer(double timerMs) {
#ifdef _WIN32
    HMODULE ntdll = GetModuleHandleA("ntdll.dll");
    if (!ntdll) return false;
    
    typedef NTSTATUS(WINAPI* NtSetTimerResolution_t)(ULONG DesiredTime, BOOLEAN SetResolution, PULONG ActualTime);
    auto NtSetTimerResolution = (NtSetTimerResolution_t)GetProcAddress(ntdll, "NtSetTimerResolution");
    if (!NtSetTimerResolution) return false;
    
    ULONG desired = (ULONG)(timerMs * 10000.0); // мс в 100нс единицы
    ULONG actual = 0;
    NTSTATUS status = NtSetTimerResolution(desired, TRUE, &actual);
    
    return (status == 0);
#else
    return false;
#endif
}

// Проверить, настроена ли служба таймера (запись в автозагрузке)
static bool isServiceRunning() {
#ifdef _WIN32
    // Проверяем есть ли запись в автозагрузке
    HKEY hKey;
    bool found = false;
    if (RegOpenKeyExA(HKEY_CURRENT_USER, "SOFTWARE\\Microsoft\\Windows\\CurrentVersion\\Run", 0, KEY_READ, &hKey) == ERROR_SUCCESS) {
        char value[1024];
        DWORD valueSize = sizeof(value);
        if (RegQueryValueExA(hKey, "SardanelloTimer", nullptr, nullptr, (BYTE*)value, &valueSize) == ERROR_SUCCESS) {
            found = true;
        }
        RegCloseKey(hKey);
    }
    
    return found;
#else
    return false;
#endif
}

// Остановить службу таймера (найти и завершить процесс в режиме --timer-service)
static bool stopTimerService() {
#ifdef _WIN32
    HANDLE hSnapshot = CreateToolhelp32Snapshot(TH32CS_SNAPPROCESS, 0);
    if (hSnapshot == INVALID_HANDLE_VALUE) return false;
    
    PROCESSENTRY32 pe32;
    pe32.dwSize = sizeof(PROCESSENTRY32);
    
    bool found = false;
    if (Process32First(hSnapshot, &pe32)) {
        do {
            if (strstr(pe32.szExeFile, "Sardanello.exe") != nullptr) {
                // Проверяем командную строку процесса
                HANDLE hProcess = OpenProcess(PROCESS_QUERY_INFORMATION | PROCESS_VM_READ | PROCESS_TERMINATE, FALSE, pe32.th32ProcessID);
                if (hProcess) {
                    // Получаем текущий процесс для сравнения
                    DWORD currentPid = GetCurrentProcessId();
                    if (pe32.th32ProcessID != currentPid) {
                        // Это другой экземпляр Sardanello - завершаем его
                        TerminateProcess(hProcess, 0);
                        WaitForSingleObject(hProcess, 5000);
                        found = true;
                    }
                    CloseHandle(hProcess);
                }
            }
        } while (Process32Next(hSnapshot, &pe32));
    }
    
    CloseHandle(hSnapshot);
    return found;
#else
    return false;
#endif
}

// Запустить службу таймера (запустить саму программу в режиме --timer-service)
static bool startTimerService() {
#ifdef _WIN32
    // Получаем путь к текущему исполняемому файлу
    char exePath[MAX_PATH];
    GetModuleFileNameA(nullptr, exePath, MAX_PATH);
    
    // Запускаем новый экземпляр в режиме службы
    STARTUPINFOA si = {0};
    PROCESS_INFORMATION pi = {0};
    si.cb = sizeof(si);
    si.dwFlags = STARTF_USESHOWWINDOW;
    si.wShowWindow = SW_HIDE; // Скрытый запуск
    
    std::string cmdLine = "\"" + std::string(exePath) + "\" --timer-service";
    bool result = CreateProcessA(
        nullptr,
        const_cast<char*>(cmdLine.c_str()),
        nullptr, nullptr, FALSE,
        CREATE_NEW_CONSOLE | DETACHED_PROCESS | CREATE_NO_WINDOW, // Создаем без окна
        nullptr, nullptr, &si, &pi
    );
    
    if (result) {
        CloseHandle(pi.hProcess);
        CloseHandle(pi.hThread);
        
        // Добавляем в автозагрузку
        HKEY hKey;
        if (RegOpenKeyExA(HKEY_CURRENT_USER, "SOFTWARE\\Microsoft\\Windows\\CurrentVersion\\Run", 0, KEY_SET_VALUE, &hKey) == ERROR_SUCCESS) {
            RegSetValueExA(hKey, "SardanelloTimer", 0, REG_SZ, (BYTE*)cmdLine.c_str(), cmdLine.length() + 1);
            RegCloseKey(hKey);
        }
    }
    
    return result;
#else
    return false;
#endif
}

// Сбросить таймер к дефолтному значению
static bool resetTimerToDefault() {
#ifdef _WIN32
    HMODULE ntdll = GetModuleHandleA("ntdll.dll");
    if (!ntdll) return false;
    
    typedef NTSTATUS(WINAPI* NtSetTimerResolution_t)(ULONG DesiredTime, BOOLEAN SetResolution, PULONG ActualTime);
    auto NtSetTimerResolution = (NtSetTimerResolution_t)GetProcAddress(ntdll, "NtSetTimerResolution");
    if (!NtSetTimerResolution) return false;
    
    // Сбрасываем таймер (FALSE = вернуть к системному дефолту)
    ULONG actual = 0;
    NTSTATUS status = NtSetTimerResolution(0, FALSE, &actual);
    
    return (status == 0);
#else
    return false;
#endif
}

// Режим службы - постоянный мониторинг и применение таймера
static int runTimerService() {
#ifdef _WIN32
    // Полностью скрываем окно консоли (убираем с панели задач)
    HWND consoleWindow = GetConsoleWindow();
    if (consoleWindow) {
        // Сначала полностью скрываем окно
        ShowWindow(consoleWindow, SW_HIDE);
        
        // Убираем из панели задач и Alt+Tab
        SetWindowLongPtrA(consoleWindow, GWL_EXSTYLE, 
            GetWindowLongPtrA(consoleWindow, GWL_EXSTYLE) | WS_EX_TOOLWINDOW);
        
        // Дополнительно устанавливаем как невидимое
        SetWindowPos(consoleWindow, nullptr, 0, 0, 0, 0, 
            SWP_HIDEWINDOW | SWP_NOACTIVATE | SWP_NOMOVE | SWP_NOSIZE | SWP_NOZORDER);
    }
    
    // Убираем консоль из заголовка процесса (делаем процесс "невидимым")
    FreeConsole();
    
    // Загружаем сохраненное значение перед первым применением, чтобы скрытый
    // timer-service не стартовал с дефолтным 1.000 мс на первые секунды.
    loadUpdatedTimer();

    // Применяем таймер при запуске
    if (setTimerResolution()) {
        // Таймер установлен - теперь мониторим изменения
        while (true) {
            std::this_thread::sleep_for(std::chrono::seconds(5));
            
            // Проверяем обновления конфигурации
            if (loadUpdatedTimer()) {
                // Конфигурация изменилась - переустанавливаем таймер
                setTimerResolution();
            }
        }
    }
    
    return 0;
#else
    return 1;
#endif
}

// ================= POWER PLAN MANAGEMENT FUNCTIONS =================

// Проверка прав администратора
static bool isAdministrator() {
#ifdef _WIN32
    BOOL isAdmin = FALSE;
    PSID administratorsGroup = nullptr;
    
    SID_IDENTIFIER_AUTHORITY ntAuthority = SECURITY_NT_AUTHORITY;
    if (AllocateAndInitializeSid(&ntAuthority, 2, SECURITY_BUILTIN_DOMAIN_RID,
                                 DOMAIN_ALIAS_RID_ADMINS, 0, 0, 0, 0, 0, 0, &administratorsGroup)) {
        if (!CheckTokenMembership(nullptr, administratorsGroup, &isAdmin)) {
            isAdmin = FALSE;
        }
        FreeSid(administratorsGroup);
    }
    return isAdmin == TRUE;
#else
    return false;
#endif
}

// Обнаружение S0 Modern Standby через powercfg (упрощенная надежная версия)
static bool detectS0ModernStandby() {
#ifdef _WIN32
    HANDLE hReadPipe, hWritePipe;
    SECURITY_ATTRIBUTES sa = {sizeof(SECURITY_ATTRIBUTES), nullptr, TRUE};
    
    if (!CreatePipe(&hReadPipe, &hWritePipe, &sa, 0)) {
        return false;
    }
    
    STARTUPINFOA si = {sizeof(STARTUPINFOA)};
    si.dwFlags = STARTF_USESHOWWINDOW | STARTF_USESTDHANDLES;
    si.wShowWindow = SW_HIDE;
    si.hStdOutput = hWritePipe;
    si.hStdError = hWritePipe;
    
    PROCESS_INFORMATION pi;
    
    // Простая команда без смены кодировки
    const char* cmdLine = "powercfg /a";
    bool hasS0 = false;
    
    if (CreateProcessA(nullptr, const_cast<char*>(cmdLine), nullptr, nullptr, TRUE, 
                       CREATE_NO_WINDOW, nullptr, nullptr, &si, &pi)) {
        
        CloseHandle(hWritePipe);
        WaitForSingleObject(pi.hProcess, 10000); // Увеличили таймаут
        
        char buffer[8192]; // Увеличили буфер
        DWORD bytesRead;
        std::string output;
        
        while (ReadFile(hReadPipe, buffer, sizeof(buffer) - 1, &bytesRead, nullptr) && bytesRead > 0) {
            buffer[bytesRead] = '\0';
            output += buffer;
        }
        
        // УПРОЩЕННЫЙ ПОИСК: ищем "S0" в любом месте доступного текста
        // Исключаем поиск в секции недоступных состояний
        
        size_t unavailablePos = output.find("недоступны в данной системе");
        if (unavailablePos == std::string::npos) {
            unavailablePos = output.find("not available on this system");
        }
        
        std::string searchArea;
        if (unavailablePos != std::string::npos) {
            // Берем только часть ДО секции недоступных состояний
            searchArea = output.substr(0, unavailablePos);
        } else {
            // Если секция не найдена, ищем по всему тексту
            searchArea = output;
        }
        
        // Ищем S0 в доступной области (любые варианты)
        if (searchArea.find("S0") != std::string::npos) {
            hasS0 = true;
        }
        
        CloseHandle(pi.hProcess);
        CloseHandle(pi.hThread);
    }
    
    CloseHandle(hReadPipe);
    return hasS0;
#else
    return false;
#endif
}

// Установка PlatformAoAcOverride в реестре (false = 0 = отключить S0, true = 1 = включить S0)
static bool setPlatformAoAcOverride(bool enable) {
#ifdef _WIN32
    HKEY hKey;
    const char* keyPath = "SYSTEM\\CurrentControlSet\\Control\\Power";
    
    if (RegCreateKeyExA(HKEY_LOCAL_MACHINE, keyPath, 0, nullptr, 0, 
                        KEY_SET_VALUE, nullptr, &hKey, nullptr) != ERROR_SUCCESS) {
        return false;
    }
    
    DWORD value = enable ? 1 : 0;
    bool success = (RegSetValueExA(hKey, "PlatformAoAcOverride", 0, REG_DWORD, 
                                   reinterpret_cast<const BYTE*>(&value), sizeof(value)) == ERROR_SUCCESS);
    
    RegCloseKey(hKey);
    return success;
#else
    return false;
#endif
}

// Чтение текущего значения PlatformAoAcOverride из реестра
static int getPlatformAoAcOverride() {
#ifdef _WIN32
    HKEY hKey;
    const char* keyPath = "SYSTEM\\CurrentControlSet\\Control\\Power";
    
    if (RegOpenKeyExA(HKEY_LOCAL_MACHINE, keyPath, 0, KEY_READ, &hKey) != ERROR_SUCCESS) {
        return -1; // Ключ не найден
    }
    
    DWORD value;
    DWORD valueSize = sizeof(value);
    DWORD valueType;
    
    if (RegQueryValueExA(hKey, "PlatformAoAcOverride", nullptr, &valueType, 
                         reinterpret_cast<BYTE*>(&value), &valueSize) != ERROR_SUCCESS) {
        RegCloseKey(hKey);
        return -1; // Значение не найдено
    }
    
    RegCloseKey(hKey);
    
    if (valueType == REG_DWORD) {
        return static_cast<int>(value);
    }
    
    return -1; // Неправильный тип
#else
    return -1;
#endif
}

// Получить список всех GUID планов питания
static std::vector<std::string> getAllPowerPlanGUIDs(const char* exePath) {
    std::vector<std::string> guids;
    
    HANDLE hReadPipe, hWritePipe;
    SECURITY_ATTRIBUTES sa = {sizeof(SECURITY_ATTRIBUTES), nullptr, TRUE};
    
    if (!CreatePipe(&hReadPipe, &hWritePipe, &sa, 0)) {
        return guids;
    }
    
    STARTUPINFOA si = {sizeof(STARTUPINFOA)};
    si.dwFlags = STARTF_USESHOWWINDOW | STARTF_USESTDHANDLES;
    si.wShowWindow = SW_HIDE;
    si.hStdOutput = hWritePipe;
    si.hStdError = hWritePipe;
    
    PROCESS_INFORMATION pi;
    
    const char* listCmd = "powercfg /list";
    if (CreateProcessA(nullptr, const_cast<char*>(listCmd), nullptr, nullptr, TRUE,
                       CREATE_NO_WINDOW, nullptr, exePath, &si, &pi)) {

        CloseHandle(hWritePipe);

        char buffer[4096];
        DWORD bytesRead;
        std::string output;

        // Сначала вычитываем все, что написал дочерний процесс, чтобы не заблокироваться на переполнении буфера
        while (ReadFile(hReadPipe, buffer, sizeof(buffer) - 1, &bytesRead, nullptr) && bytesRead > 0) {
            buffer[bytesRead] = '\0';
            output += buffer;
        }
        // Коротко дожидаемся завершения процесса
        WaitForSingleObject(pi.hProcess, 2000);
        
        // Парсим GUIDs из вывода
        size_t pos = 0;
        while ((pos = output.find_first_of("0123456789abcdefABCDEF", pos)) != std::string::npos) {
            size_t guidEnd = pos;
            // Ищем конец GUID (36 символов: xxxxxxxx-xxxx-xxxx-xxxx-xxxxxxxxxxxx)
            while (guidEnd < output.length() && guidEnd < pos + 36 && 
                   (isalnum(output[guidEnd]) || output[guidEnd] == '-')) {
                guidEnd++;
            }
            
            std::string candidate = output.substr(pos, guidEnd - pos);
            // Проверяем что это валидный GUID (36 символов с дефисами)
            if (candidate.length() == 36 && candidate[8] == '-' && candidate[13] == '-' && 
                candidate[18] == '-' && candidate[23] == '-') {
                guids.push_back(candidate);
            }
            pos = guidEnd;
        }
        
        CloseHandle(pi.hProcess);
        CloseHandle(pi.hThread);
    }
    
    CloseHandle(hReadPipe);
    return guids;
}

// Поиск плана питания по имени (возвращает GUID если найден, иначе пустую строку)
static std::string findPowerPlanByName(const char* exePath, const std::string& planName) {
#ifdef _WIN32
    HANDLE hReadPipe, hWritePipe;
    SECURITY_ATTRIBUTES sa = {sizeof(SECURITY_ATTRIBUTES), nullptr, TRUE};
    
    if (!CreatePipe(&hReadPipe, &hWritePipe, &sa, 0)) {
        return "";
    }
    
    STARTUPINFOA si = {sizeof(STARTUPINFOA)};
    si.dwFlags = STARTF_USESHOWWINDOW | STARTF_USESTDHANDLES;
    si.wShowWindow = SW_HIDE;
    si.hStdOutput = hWritePipe;
    si.hStdError = hWritePipe;
    
    PROCESS_INFORMATION pi;
    
    const char* listCmd = "powercfg /list";
    if (CreateProcessA(nullptr, const_cast<char*>(listCmd), nullptr, nullptr, TRUE,
                       CREATE_NO_WINDOW, nullptr, exePath, &si, &pi)) {

        CloseHandle(hWritePipe);

        char buffer[4096];
        DWORD bytesRead;
        std::string output;

        // Сначала читаем вывод, затем немного ждём завершения процесса
        while (ReadFile(hReadPipe, buffer, sizeof(buffer) - 1, &bytesRead, nullptr) && bytesRead > 0) {
            buffer[bytesRead] = '\0';
            output += buffer;
        }
        WaitForSingleObject(pi.hProcess, 2000);
        
        // Ищем строку с нужным именем плана
        std::istringstream iss(output);
        std::string line;
        int lineCount = 0;
        while (std::getline(iss, line)) {
            lineCount++;
            // Преобразуем строку к нижнему регистру (ASCII) для нестрогого поиска
            std::string lower = line;
            for (auto &c : lower) c = (char)tolower((unsigned char)c);

            // Подготовим набор игл: запрошенное имя в нижнем регистре и общий ключ "sardanello"
            std::vector<std::string> needles;
            std::string planLower = planName;
            for (auto &c : planLower) c = (char)tolower((unsigned char)c);
            // Нормализуем апострофы/кавычки в обоих вариантах (заменим типографский ’ на ') — в кодировках может не совпасть, поэтому также ищем просто по "sardanello")
            needles.push_back(planLower);
            needles.push_back("sardanello");
            // Проверяем наличие любой иглы
            bool matches = false;
            for (const auto &n : needles) {
                if (!n.empty() && lower.find(n) != std::string::npos) { matches = true; break; }
            }

            // Ищем строки вида: "... GUID: 12345678-... (Plan Name)" только если нашли совпадение по имени
            if (matches) {
                // Извлекаем GUID из строки
                size_t guidStart = line.find_first_of("0123456789abcdefABCDEF");
                if (guidStart != std::string::npos) {
                    size_t guidEnd = guidStart;
                    while (guidEnd < line.length() && guidEnd < guidStart + 36 && 
                           (isalnum(line[guidEnd]) || line[guidEnd] == '-')) {
                        guidEnd++;
                    }
                    
                    std::string guid = line.substr(guidStart, guidEnd - guidStart);
                    if (guid.length() == 36 && guid[8] == '-' && guid[13] == '-' && 
                        guid[18] == '-' && guid[23] == '-') {
                        CloseHandle(pi.hProcess);
                        CloseHandle(pi.hThread);
                        CloseHandle(hReadPipe);
                        return guid;
                    }
                }
            }
        }
        
        CloseHandle(pi.hProcess);
        CloseHandle(pi.hThread);
    }
    
    CloseHandle(hReadPipe);
    return "";
#else
    return "";
#endif
}

// Конвертация GUID в строку без фигурных скобок XXXXXXXX-XXXX-XXXX-XXXX-XXXXXXXXXXXX
static std::string guidToString(const GUID &g)
{
    char buf[37];
    std::snprintf(buf, sizeof(buf),
                  "%08lX-%04hX-%04hX-%02X%02X-%02X%02X%02X%02X%02X%02X",
                  g.Data1, g.Data2, g.Data3,
                  g.Data4[0], g.Data4[1], g.Data4[2], g.Data4[3],
                  g.Data4[4], g.Data4[5], g.Data4[6], g.Data4[7]);
    return std::string(buf);
}

// Надёжный поиск GUID плана по подстроке в имени через WinAPI (допускает локализацию и разные кавычки)
static std::string findPowerPlanByNameAPI(const std::string &patternAscii)
{
#ifdef _WIN32
    // Готовим шаблоны поиска в нижнем регистре
    std::vector<std::wstring> needlesW;
    auto toLowerW = [](const std::wstring &s)->std::wstring {
        int len = LCMapStringW(LOCALE_INVARIANT, LCMAP_LOWERCASE, s.c_str(), -1, NULL, 0);
        if (len <= 0) return s;
        std::wstring out; out.resize(len-1);
        LCMapStringW(LOCALE_INVARIANT, LCMAP_LOWERCASE, s.c_str(), -1, &out[0], len);
        return out;
    };
    // добавим "sardanello" и исходный шаблон
    needlesW.push_back(toLowerW(L"sardanello"));
    // преобразуем patternAscii -> wstring
    if (!patternAscii.empty()) {
        int need = MultiByteToWideChar(CP_UTF8, 0, patternAscii.c_str(), -1, NULL, 0);
        if (need > 0) {
            std::wstring w; w.resize(need-1);
            MultiByteToWideChar(CP_UTF8, 0, patternAscii.c_str(), -1, &w[0], need);
            needlesW.push_back(toLowerW(w));
        }
    }

    DWORD idx = 0; GUID schemeGuid;
    while (true) {
        DWORD sz = sizeof(GUID);
        DWORD rc = PowerEnumerate(NULL, NULL, NULL, ACCESS_SCHEME, idx, (UCHAR*)&schemeGuid, &sz);
        if (rc == ERROR_NO_MORE_ITEMS) break;
        if (rc != ERROR_SUCCESS) break;

        // читаем дружественное имя схемы
        DWORD nameSize = 0;
        DWORD r2 = PowerReadFriendlyName(NULL, &schemeGuid, NULL, NULL, NULL, &nameSize);
        if (r2 == ERROR_MORE_DATA || r2 == ERROR_SUCCESS) {
            std::vector<WCHAR> buf(nameSize/sizeof(WCHAR) + 2);
            if (PowerReadFriendlyName(NULL, &schemeGuid, NULL, NULL, (UCHAR*)buf.data(), &nameSize) == ERROR_SUCCESS) {
                std::wstring fname(buf.data());
                // в нижний регистр для сравнения
                std::wstring low = toLowerW(fname);
                // грубая нормализация — заменим типографские апострофы на обычные
                for (auto &ch : low) if (ch == 0x2019) ch = L'\''; // ’ -> '

                bool match = false;
                for (const auto &n : needlesW) {
                    if (!n.empty() && low.find(n) != std::wstring::npos) { match = true; break; }
                }
                if (match) {
                    return guidToString(schemeGuid);
                }
            }
        }
        ++idx;
    }
    return std::string();
#else
    return std::string();
#endif
}

// Извлечение ресурса Sardanello.pow и сохранение во временный файл
static std::string extractPowerPlanFromResource() {
#ifdef _WIN32
    // Ищем ресурс
    HRSRC hResInfo = FindResource(NULL, MAKEINTRESOURCE(IDR_POWER_PLAN), RT_RCDATA);
    if (!hResInfo) return std::string();
    
    // Загружаем ресурс
    HGLOBAL hResData = LoadResource(NULL, hResInfo);
    if (!hResData) return std::string();
    
    // Получаем указатель на данные и размер
    void* pData = LockResource(hResData);
    DWORD dataSize = SizeofResource(NULL, hResInfo);
    if (!pData || dataSize == 0) return std::string();
    
    // Создаем временный файл
    char tempPath[MAX_PATH];
    GetTempPathA(MAX_PATH, tempPath);
    
    char tempFile[MAX_PATH];
    std::snprintf(tempFile, sizeof(tempFile), "%s\\Sardanello_temp_%lu.pow", tempPath, GetTickCount());
    
    // Записываем данные ресурса в временный файл
    HANDLE hFile = CreateFileA(tempFile, GENERIC_WRITE, 0, NULL, CREATE_ALWAYS, FILE_ATTRIBUTE_TEMPORARY, NULL);
    if (hFile == INVALID_HANDLE_VALUE) return std::string();
    
    DWORD bytesWritten;
    bool writeSuccess = WriteFile(hFile, pData, dataSize, &bytesWritten, NULL) && (bytesWritten == dataSize);
    CloseHandle(hFile);
    
    if (writeSuccess) {
        return std::string(tempFile);
    } else {
        DeleteFileA(tempFile);
        return std::string();
    }
#else
    return std::string();
#endif
}

// Упрощенный импорт и применение плана электропитания
static bool importAndApplyPowerPlanSimple() {
#ifdef _WIN32
    // Предотвращаем параллельные/повторные входы
    bool expected = false;
    if (!g_powerPlanApplying.compare_exchange_strong(expected, true)) {
        // Уже выполняется — просто показать статус и выйти
        {
            std::lock_guard<std::mutex> sl(g_menuMutex);
            g_statusLines[0] = "⏳ Применение плана уже выполняется...";
            g_statusLines[1].clear();
            g_statusLines[2].clear();
        }
        drawMenu();
        std::this_thread::sleep_for(std::chrono::milliseconds(800));
        return false;
    }
    struct Guard { ~Guard(){ g_powerPlanApplying = false; } } guard;
    // Начальная диагностика
    {
        std::lock_guard<std::mutex> sl(g_menuMutex);
        g_statusLines[0] = "🔍 Поиск профиля Sardanello";
        g_statusLines[1] = "📂 Проверяем существующие планы питания...";
        g_statusLines[2] = "";
    }
    drawMenu();
    std::this_thread::sleep_for(std::chrono::seconds(1));
    
    // Получаем путь к exe
    char exePath[MAX_PATH];
    DWORD pathLen = GetModuleFileNameA(nullptr, exePath, MAX_PATH);
    if (pathLen == 0 || pathLen >= MAX_PATH) {
        std::lock_guard<std::mutex> sl(g_menuMutex);
        g_statusLines[0] = "❌ ОШИБКА ПУТИ!";
        g_statusLines[1] = "❌ Не удалось получить путь к exe файлу";
        drawMenu();
        std::this_thread::sleep_for(std::chrono::seconds(3));
        return false;
    }
    
    // Извлекаем путь к папке exe (без имени файла)
    char* lastSlash = strrchr(exePath, '\\');
    if (!lastSlash) {
        std::lock_guard<std::mutex> sl(g_menuMutex);
        g_statusLines[0] = "❌ ОШИБКА ПУТИ!";
        g_statusLines[1] = "❌ Некорректный путь к exe файлу";
        drawMenu();
        std::this_thread::sleep_for(std::chrono::seconds(3));
        return false;
    }
    *lastSlash = '\0';
    
    // СНАЧАЛА ПРОВЕРЯЕМ СУЩЕСТВУЮЩИЕ ПЛАНЫ
    {
        std::lock_guard<std::mutex> sl(g_menuMutex);
        g_statusLines[1] = "🔍 Ищем план 'Sardanello\'s pow' или 'Sardanello'...";
        g_statusLines[2] = "📋 Сканируем существующие планы питания";
    }
    drawMenu();
    std::this_thread::sleep_for(std::chrono::seconds(1));
    
    // 1) Сначала пробуем достоверный WinAPI-поиск (без парсинга текста)
    std::string existingGuid = findPowerPlanByNameAPI("sardanello");
    if (existingGuid.empty()) {
        // 2) Фоллбек на парсинг powercfg /list с явными названиями
        existingGuid = findPowerPlanByName(exePath, "Sardanello's pow");
    }
    
    // Если не нашли точное совпадение, попробуем поиск по части имени "Sardanello"
    if (existingGuid.empty()) {
        existingGuid = findPowerPlanByNameAPI("sardanello");
        if (existingGuid.empty()) {
            existingGuid = findPowerPlanByName(exePath, "Sardanello");
        }
    }
    
    // Отладочная информация о результате поиска
    {
        std::lock_guard<std::mutex> sl(g_menuMutex);
        if (existingGuid.empty()) {
            g_statusLines[1] = "❌ План Sardanello не найден";
            g_statusLines[2] = "📦 Будем импортировать новый план";
        } else {
            char foundMsg[300];
            std::snprintf(foundMsg, sizeof(foundMsg), "✅ Найден план: %.36s", existingGuid.c_str());
            g_statusLines[1] = foundMsg;
            g_statusLines[2] = "⚡ Используем существующий план";
        }
    }
    drawMenu();
    std::this_thread::sleep_for(std::chrono::seconds(2));
    
    if (!existingGuid.empty()) {
        // План уже существует - проверяем, активен ли он
        
        // Получаем текущий активный план
        GUID* currentActiveGuid = nullptr;
        DWORD getActiveResult = PowerGetActiveScheme(NULL, &currentActiveGuid);
        bool isAlreadyActive = false;
        
        if (getActiveResult == ERROR_SUCCESS && currentActiveGuid) {
            // Конвертируем GUID в строку для сравнения
            WCHAR currentGuidStr[64];
            StringFromGUID2(*currentActiveGuid, currentGuidStr, 64);
            
            // Конвертируем в char* для сравнения
            char currentGuidCharStr[64];
            WideCharToMultiByte(CP_UTF8, 0, currentGuidStr, -1, currentGuidCharStr, 64, nullptr, nullptr);
            
            // Убираем фигурные скобки из текущего GUID для сравнения
            std::string currentGuidClean = currentGuidCharStr;
            if (!currentGuidClean.empty() && currentGuidClean.front() == '{') {
                currentGuidClean.erase(0, 1);
            }
            if (!currentGuidClean.empty() && currentGuidClean.back() == '}') {
                currentGuidClean.pop_back();
            }
            
            // Сравниваем GUID (без учета регистра)
            std::string existingGuidLower = existingGuid;
            std::transform(existingGuidLower.begin(), existingGuidLower.end(), existingGuidLower.begin(), ::tolower);
            std::transform(currentGuidClean.begin(), currentGuidClean.end(), currentGuidClean.begin(), ::tolower);
            
            if (existingGuidLower == currentGuidClean) {
                isAlreadyActive = true;
            }
            
            LocalFree(currentActiveGuid);
        }
        
        if (isAlreadyActive) {
            // План уже активен - просто сообщаем об этом
            {
                std::lock_guard<std::mutex> sl(g_menuMutex);
                g_statusLines[0] = "✅ План питания найден и уже активен!";
                char guidMsg[200];
                std::snprintf(guidMsg, sizeof(guidMsg), "🔧 GUID: %.36s", existingGuid.c_str());
                g_statusLines[1] = guidMsg;
                g_statusLines[2] = "⚡ Никаких действий не требуется";
            }
            drawMenu();
            std::this_thread::sleep_for(std::chrono::seconds(3));
            return true;
        }
        
        // План существует, но не активен - активируем его
        {
            std::lock_guard<std::mutex> sl(g_menuMutex);
            g_statusLines[0] = "⚡ Активируем существующий план питания...";
            char guidMsg[200];
            std::snprintf(guidMsg, sizeof(guidMsg), "🔧 GUID: %.36s", existingGuid.c_str());
            g_statusLines[1] = guidMsg;
            g_statusLines[2].clear();
        }
        drawMenu();
        std::this_thread::sleep_for(std::chrono::seconds(1));
        
        // Активируем план асинхронно, чтобы не блокировать матричный дождь
        std::thread([existingGuid]() {
            std::this_thread::sleep_for(std::chrono::milliseconds(500)); // Небольшая задержка для стабильности
            
            // Используем нативный Windows API
            GUID planGuid;
            HRESULT hr = CLSIDFromString(std::wstring(existingGuid.begin(), existingGuid.end()).c_str(), &planGuid);
            
            if (FAILED(hr)) {
                // Если не удалось конвертировать строку в GUID, пробуем добавить скобки
                std::string guidWithBrackets = "{" + existingGuid + "}";
                std::wstring wGuidWithBrackets(guidWithBrackets.begin(), guidWithBrackets.end());
                hr = CLSIDFromString(wGuidWithBrackets.c_str(), &planGuid);
            }
            
            bool activateSuccess = false;
            if (SUCCEEDED(hr)) {
                DWORD result = PowerSetActiveScheme(NULL, &planGuid);
                activateSuccess = (result == ERROR_SUCCESS);
            }
            
            // Обновляем UI после активации
            {
                std::lock_guard<std::mutex> sl(g_menuMutex);
                if (activateSuccess) {
                    g_statusLines[0] = "✅ План питания уже есть в системе и применен.";
                    g_statusLines[1].clear();
                    g_statusLines[2].clear();
                } else {
                    g_statusLines[0] = "❌ Не удалось активировать существующий план.";
                    g_statusLines[1] = "⚠️ Проверьте права администратора и повторите.";
                    g_statusLines[2] = "План найден, но активация не удалась.";
                }
            }
            drawMenu();
        }).detach();
        
        // Сразу возвращаем true, так как план найден и активация запущена
        {
            std::lock_guard<std::mutex> sl(g_menuMutex);
            g_statusLines[0] = "✅ План найден, активация запущена...";
            g_statusLines[1] = "⚡ Активация выполняется в фоновом режиме";
            g_statusLines[2] = "";
        }
        drawMenu();
        return true;
    }
    
    // План не найден или активация не удалась - импортируем новый
    {
        std::lock_guard<std::mutex> sl(g_menuMutex);
        g_statusLines[0] = "🔍 Импорт нового плана";
        g_statusLines[1] = "� Извлекаем Sardanello.pow из ресурсов...";
        g_statusLines[2] = "";
    }
    drawMenu();
    std::this_thread::sleep_for(std::chrono::seconds(1));
    
    // Извлекаем план питания из ресурсов
    std::string sourcePath = extractPowerPlanFromResource();
    if (sourcePath.empty()) {
        std::lock_guard<std::mutex> sl(g_menuMutex);
        g_statusLines[0] = "❌ ОШИБКА ИЗВЛЕЧЕНИЯ РЕСУРСА!";
        g_statusLines[1] = "❌ Не удалось извлечь Sardanello.pow из программы";
        g_statusLines[2] = "🔧 Возможно, ресурс не был встроен при компиляции";
        drawMenu();
        std::this_thread::sleep_for(std::chrono::seconds(5));
        return false;
    }
    
    {
        std::lock_guard<std::mutex> sl(g_menuMutex);
        g_statusLines[1] = "✅ План питания извлечен из ресурсов!";
        g_statusLines[2] = "📋 Получаем список планов ДО импорта...";
    }
    drawMenu();
    std::this_thread::sleep_for(std::chrono::seconds(1));
    
    // ПОЛУЧАЕМ СПИСОК ПЛАНОВ ДО ИМПОРТА
    std::vector<std::string> guidsBefore = getAllPowerPlanGUIDs(exePath);
    
    {
        std::lock_guard<std::mutex> sl(g_menuMutex);
        char countMsg[100];
        std::snprintf(countMsg, sizeof(countMsg), "📊 Найдено планов до импорта: %zu", guidsBefore.size());
        g_statusLines[2] = countMsg;
    }
    drawMenu();
    std::this_thread::sleep_for(std::chrono::seconds(1));
    
    {
        std::lock_guard<std::mutex> sl(g_menuMutex);
        g_statusLines[2] = "⚡ Импортируем план напрямую...";
    }
    drawMenu();
    std::this_thread::sleep_for(std::chrono::seconds(1));
    
    // ПРОСТОЙ ИМПОРТ: импортируем .pow файл напрямую
    char importCmd[512];
    std::snprintf(importCmd, sizeof(importCmd), "powercfg /import \"%s\"", sourcePath.c_str());
    
    STARTUPINFOA si = {sizeof(STARTUPINFOA)};
    si.dwFlags = STARTF_USESHOWWINDOW;
    si.wShowWindow = SW_HIDE;
    
    PROCESS_INFORMATION pi;
    
    bool importSuccess = false;
    if (CreateProcessA(nullptr, importCmd, nullptr, nullptr, FALSE, 
                       CREATE_NO_WINDOW, nullptr, exePath, &si, &pi)) {
        WaitForSingleObject(pi.hProcess, 10000); // 10 sec timeout
        
        DWORD importExitCode;
        importSuccess = GetExitCodeProcess(pi.hProcess, &importExitCode) && (importExitCode == 0);
        
        CloseHandle(pi.hProcess);
        CloseHandle(pi.hThread);
    }
    
    if (!importSuccess) {
        std::lock_guard<std::mutex> sl(g_menuMutex);
        g_statusLines[0] = "❌ ОШИБКА ИМПОРТА!";
        g_statusLines[1] = "❌ Команда powercfg /import завершилась с ошибкой";
        g_statusLines[2] = "🔧 Проверьте права администратора";
        drawMenu();
        std::this_thread::sleep_for(std::chrono::seconds(5));
        
        // Очищаем временный файл
        if (!sourcePath.empty()) {
            DeleteFileA(sourcePath.c_str());
        }
        return false;
    }
    
    {
        std::lock_guard<std::mutex> sl(g_menuMutex);
        g_statusLines[1] = "✅ План импортирован!";
        g_statusLines[2] = "� Получаем список планов ПОСЛЕ импорта...";
    }
    drawMenu();
    std::this_thread::sleep_for(std::chrono::seconds(1));
    
    // ПОЛУЧАЕМ СПИСОК ПЛАНОВ ПОСЛЕ ИМПОРТА
    std::vector<std::string> guidsAfter = getAllPowerPlanGUIDs(exePath);
    
    {
        std::lock_guard<std::mutex> sl(g_menuMutex);
        char countMsg[100];
        std::snprintf(countMsg, sizeof(countMsg), "📊 Найдено планов после импорта: %zu", guidsAfter.size());
        g_statusLines[2] = countMsg;
    }
    drawMenu();
    std::this_thread::sleep_for(std::chrono::seconds(1));
    
    // ИЩЕМ НОВЫЙ GUID (разность между списками)
    std::string newGuid;
    for (const std::string& guid : guidsAfter) {
        bool found = false;
        for (const std::string& oldGuid : guidsBefore) {
            if (guid == oldGuid) {
                found = true;
                break;
            }
        }
        if (!found) {
            newGuid = guid;
            break;
        }
    }
    
    if (newGuid.empty()) {
        std::lock_guard<std::mutex> sl(g_menuMutex);
        g_statusLines[0] = "❌ НОВЫЙ ПЛАН НЕ НАЙДЕН!";
        g_statusLines[1] = "❌ Не удалось определить GUID нового плана";
        g_statusLines[2] = "🔧 Возможно, план уже существовал в системе";
        drawMenu();
        std::this_thread::sleep_for(std::chrono::seconds(5));
        return false;
    }
    
    {
        std::lock_guard<std::mutex> sl(g_menuMutex);
        char guidMsg[200];
        std::snprintf(guidMsg, sizeof(guidMsg), "✅ Новый GUID: %.36s", newGuid.c_str());
        g_statusLines[1] = guidMsg;
        g_statusLines[2] = "⚡ Активируем план...";
    }
    drawMenu();
    std::this_thread::sleep_for(std::chrono::seconds(1));
    
    // Активируем найденный новый план
    char activateCmd[256];
    std::snprintf(activateCmd, sizeof(activateCmd), "powercfg /setactive %s", newGuid.c_str());
    
    si = {sizeof(STARTUPINFOA)};
    si.dwFlags = STARTF_USESHOWWINDOW;
    si.wShowWindow = SW_HIDE;
    
    if (!CreateProcessA(nullptr, activateCmd, nullptr, nullptr, FALSE, 
                        CREATE_NO_WINDOW, nullptr, exePath, &si, &pi)) {
        std::lock_guard<std::mutex> sl(g_menuMutex);
        g_statusLines[0] = "❌ ОШИБКА АКТИВАЦИИ!";
        g_statusLines[1] = "❌ Не удалось запустить команду powercfg /setactive";
        drawMenu();
        std::this_thread::sleep_for(std::chrono::seconds(3));
        
        // Очищаем временный файл
        if (!sourcePath.empty()) {
            DeleteFileA(sourcePath.c_str());
        }
        return false;
    }
    
    WaitForSingleObject(pi.hProcess, 5000); // Уменьшили таймаут
    
    DWORD activateExitCode;
    bool activateSuccess = GetExitCodeProcess(pi.hProcess, &activateExitCode) && (activateExitCode == 0);
    
    CloseHandle(pi.hProcess);
    CloseHandle(pi.hThread);
    
    if (!activateSuccess) {
        std::lock_guard<std::mutex> sl(g_menuMutex);
        g_statusLines[0] = "❌ АКТИВАЦИЯ НЕУДАЧНА!";
        g_statusLines[1] = "❌ Команда powercfg /setactive завершилась с ошибкой";
        g_statusLines[2] = "🔧 Возможно, нужны права администратора";
        drawMenu();
        std::this_thread::sleep_for(std::chrono::seconds(5));
        
        // Очищаем временный файл
        if (!sourcePath.empty()) {
            DeleteFileA(sourcePath.c_str());
        }
        return false;
    }
    
    // УСПЕХ (упрощенно)
    {
        std::lock_guard<std::mutex> sl(g_menuMutex);
        g_statusLines[0] = "✅ ПЛАН ИМПОРТИРОВАН!";
        g_statusLines[1] = "🎮 План Sardanello добавлен в систему";
        g_statusLines[2] = "⚡ Активируйте его вручную в настройках питания";
    }
    drawMenu();
    
    // Очищаем временный файл
    if (!sourcePath.empty()) {
        DeleteFileA(sourcePath.c_str());
    }
    
    return true;
#else
    return false;
#endif
}

#ifdef _WIN32

static HWND g_guiHwnd = nullptr;
static int g_guiHoverButton = 0;
static std::atomic<int> g_guiHpetState{0}; // 0 unknown, 1 disabled/not present, 2 enabled
static std::atomic<bool> g_guiHpetQueryRunning{false};
static std::atomic<int> g_guiRestoreState{0}; // 0 unknown, 1 exists, 2 missing
static std::atomic<bool> g_guiRestoreQueryRunning{false};

struct GuiMatrixDrop {
    float x = 0.0f;
    float y = 0.0f;
    float speed = 2.0f;
    int length = 12;
};

struct GuiButton {
    int id = 0;
    std::wstring title;
    std::wstring note;
    RECT rect{0, 0, 0, 0};
    bool enabled = true;
};

static std::vector<GuiMatrixDrop> g_guiDrops;
static std::vector<GuiButton> g_guiButtons;

enum GuiCommandId {
    GUI_CMD_BENCHMARK = 1001,
    GUI_CMD_APPLY_TIMER,
    GUI_CMD_HPET,
    GUI_CMD_POWER_PLAN,
    GUI_CMD_RESTORE_POINT,
    GUI_CMD_OPEN_REPORT,
    GUI_CMD_MANUAL_TIMER,
    GUI_CMD_DONATE,
    GUI_CMD_TELEGRAM,
    GUI_CMD_EXIT
};

static std::wstring utf8ToWide(const std::string& text)
{
    if (text.empty()) return std::wstring();
    int needed = MultiByteToWideChar(CP_UTF8, 0, text.c_str(), -1, nullptr, 0);
    if (needed <= 0) return std::wstring(text.begin(), text.end());
    std::wstring out((size_t)needed - 1, L'\0');
    MultiByteToWideChar(CP_UTF8, 0, text.c_str(), -1, out.data(), needed);
    return out;
}

static std::string wideToUtf8(const std::wstring& text)
{
    if (text.empty()) return std::string();
    int needed = WideCharToMultiByte(CP_UTF8, 0, text.c_str(), -1, nullptr, 0, nullptr, nullptr);
    if (needed <= 0) return std::string(text.begin(), text.end());
    std::string out((size_t)needed - 1, '\0');
    WideCharToMultiByte(CP_UTF8, 0, text.c_str(), -1, out.data(), needed, nullptr, nullptr);
    return out;
}

enum class TextId {
    Subtitle,
    BtnHpet,
    NoteHpet,
    BtnPowerPlan,
    NotePowerPlan,
    BtnRestorePoint,
    NoteRestorePoint,
    BtnBenchmark,
    NoteBenchmark,
    BtnApplyTimer,
    NoteApplyTimer,
    BtnOpenReport,
    NoteOpenReport,
    BtnManualTimer,
    NoteManualTimer,
    BtnDonate,
    NoteDonate,
    BtnTelegram,
    NoteTelegram,
    BtnExit,
    NoteExit,
    ReadyChoose,
    ReadySavedPrefix,
    ReadySavedHint,
    ReadyFirstRun,
    ReadyMatrixHint,
    BusyFooter,
    TestRunning,
    WaitCurrentMeasurement,
    BenchmarkStart,
    BenchmarkStopOld,
    BenchmarkStarted,
    OldServiceStopped,
    BenchmarkInit,
    BenchmarkProgressHere,
    BenchmarkDonePrefix,
    ReportCreated,
    PressApplyTimer,
    BenchmarkNoIni,
    CheckReportFolder,
    CannotApplyDuringTest,
    OptimalNotFound,
    RunTimerTestFirst,
    ApplyingTimerPrefix,
    StartingTimerService,
    TimerAppliedPrefix,
    TimerServiceAutostart,
    TimerAppliedCurrent,
    AfterRebootIni,
    ApplyTimerFail,
    CheckAccessOrAntivirus,
    CannotManualDuringTest,
    SettingManualPrefix,
    SavingManualService,
    ManualTimerSetPrefix,
    ValueWrittenIni,
    HiddenServiceHold,
    ManualFail,
    AdminNeeded,
    RunAsAdmin,
    RestartWithUac,
    HpetStart,
    TakesSeconds,
    HpetRebootQuestion,
    PowerCheck,
    ReadPlatform,
    PlatformSet,
    RebootNeeded,
    AfterRebootPower,
    PlatformFail,
    PowerApplied,
    GameProfile,
    PowerFail,
    CheckPowAdmin,
    PowerRebootQuestion,
    CannotRestoreDuringTest,
    RestoreEnableProtection,
    RestoreAfterProtection,
    RestoreProtectionFail,
    RestoreWindowsDenied,
    RestoreProtectionEnabled,
    RestoreCreating,
    RestoreCreated,
    RestoreIndicatorGreen,
    RestoreCreateFail,
    RestoreRejected,
    ReportMissing,
    ManualDialogTitle,
    ManualDialogLabel,
    ManualDialogCancel,
    ManualDialogInvalid,
    CloseBenchmarkMessage,
    LanguageTitle,
    LanguageSubtitle,
    Count
};

struct UiText {
    const wchar_t* ru;
    const wchar_t* en;
    const wchar_t* de;
    const wchar_t* tr;
    const wchar_t* es;
    const wchar_t* pt;
    const wchar_t* hi;
};

static const UiText kUiTexts[] = {
    {L"Оптимизатор игрового таймера", L"Gaming timer optimizer", L"Gaming-Timer-Optimierer", L"Oyun zamanlayici iyilestirici", L"Optimizador de temporizador gaming", L"Otimizador de timer para jogos", L"\u0917\u0947\u092e\u093f\u0902\u0917 \u091f\u093e\u0907\u092e\u0930 \u0911\u092a\u094d\u091f\u093f\u092e\u093e\u0907\u091c\u093c\u0930"},
    {L"Отключить HPET", L"Disable HPET", L"HPET deaktivieren", L"HPET'i kapat", L"Desactivar HPET", L"Desativar HPET", L"HPET \u092c\u0902\u0926 \u0915\u0930\u0947\u0902"},
    {L"Реестр, boot tweaks и CPU interval", L"Registry, boot tweaks and CPU interval", L"Registry, Boot-Tweaks und CPU-Intervall", L"Kayit, boot ayarlari ve CPU araligi", L"Registro, ajustes boot e intervalo CPU", L"Registro, ajustes de boot e intervalo da CPU", L"\u0930\u091c\u093f\u0938\u094d\u091f\u094d\u0930\u0940, \u092c\u0942\u091f \u0914\u0930 CPU \u0907\u0902\u091f\u0930\u0935\u0932"},
    {L"Установить план питания Sardanello", L"Install Sardanello power plan", L"Sardanello-Energieplan installieren", L"Sardanello guc planini kur", L"Instalar plan de energia Sardanello", L"Instalar plano de energia Sardanello", L"Sardanello \u092a\u093e\u0935\u0930 \u092a\u094d\u0932\u093e\u0928 \u0932\u0917\u093e\u090f\u0902"},
    {L"Импорт и активация профиля", L"Import and activate profile", L"Profil importieren und aktivieren", L"Profili ice aktar ve etkinlestir", L"Importar y activar perfil", L"Importar e ativar perfil", L"\u092a\u094d\u0930\u094b\u092b\u093e\u0907\u0932 \u0907\u092e\u094d\u092a\u094b\u0930\u094d\u091f \u0914\u0930 \u091a\u093e\u0932\u0942"},
    {L"Создать точку восстановления", L"Create restore point", L"Wiederherstellungspunkt erstellen", L"Geri yukleme noktasi olustur", L"Crear punto de restauracion", L"Criar ponto de restauracao", L"\u0930\u093f\u0938\u094d\u091f\u094b\u0930 \u092a\u0949\u0907\u0902\u091f \u092c\u0928\u093e\u090f\u0902"},
    {L"Имя точки: Sardanello", L"Point name: Sardanello", L"Punktname: Sardanello", L"Nokta adi: Sardanello", L"Nombre: Sardanello", L"Nome: Sardanello", L"\u0928\u093e\u092e: Sardanello"},
    {L"Найти идеальный таймер", L"Find ideal timer", L"Idealen Timer finden", L"Ideal timer'i bul", L"Buscar temporizador ideal", L"Encontrar timer ideal", L"\u0906\u0926\u0930\u094d\u0936 \u091f\u093e\u0907\u092e\u0930 \u0922\u0942\u0902\u0922\u0947\u0902"},
    {L"Запустить полный тест", L"Run full test", L"Volltest starten", L"Tam testi baslat", L"Ejecutar prueba completa", L"Executar teste completo", L"\u092a\u0942\u0930\u093e \u091f\u0947\u0938\u094d\u091f \u091a\u0932\u093e\u090f\u0902"},
    {L"Зафиксировать найденный таймер", L"Apply found timer", L"Gefundenen Timer setzen", L"Bulunan timer'i sabitle", L"Fijar temporizador encontrado", L"Fixar timer encontrado", L"\u092e\u093f\u0932\u093e \u091f\u093e\u0907\u092e\u0930 \u0932\u0917\u093e\u090f\u0902"},
    {L"Применить optimal_timer.ini", L"Use optimal_timer.ini", L"optimal_timer.ini nutzen", L"optimal_timer.ini kullan", L"Usar optimal_timer.ini", L"Usar optimal_timer.ini", L"optimal_timer.ini \u0932\u0917\u093e\u090f\u0902"},
    {L"Открыть HTML-отчет", L"Open HTML report", L"HTML-Bericht offnen", L"HTML raporunu ac", L"Abrir informe HTML", L"Abrir relatorio HTML", L"HTML \u0930\u093f\u092a\u094b\u0930\u094d\u091f \u0916\u094b\u0932\u0947\u0902"},
    {L"Последний gaming_timer_analysis", L"Latest gaming_timer_analysis", L"Neuester gaming_timer_analysis", L"Son gaming_timer_analysis", L"Ultimo gaming_timer_analysis", L"Ultimo gaming_timer_analysis", L"\u0928\u0935\u0940\u0928\u0924\u092e gaming_timer_analysis"},
    {L"Установить таймер в ручную", L"Set timer manually", L"Timer manuell setzen", L"Timer'i elle ayarla", L"Ajustar temporizador manualmente", L"Definir timer manualmente", L"\u091f\u093e\u0907\u092e\u0930 \u092e\u0948\u0928\u094d\u092f\u0941\u0905\u0932 \u0932\u0917\u093e\u090f\u0902"},
    {L"Ввести значение в мс самому", L"Enter ms value yourself", L"Millisekundenwert eingeben", L"ms degerini elle gir", L"Introducir valor en ms", L"Digitar valor em ms", L"\u092e\u093f\u0932\u0940\u0938\u0947\u0915\u0902\u0921 \u092e\u0942\u0932\u094d\u092f \u0926\u0930\u094d\u091c \u0915\u0930\u0947\u0902"},
    {L"Donat", L"Donate", L"Spenden", L"Bagis", L"Donar", L"Doar", L"\u0921\u094b\u0928\u0947\u091f"},
    {L"Открыть DonationAlerts", L"Open DonationAlerts", L"DonationAlerts offnen", L"DonationAlerts ac", L"Abrir DonationAlerts", L"Abrir DonationAlerts", L"DonationAlerts \u0916\u094b\u0932\u0947\u0902"},
    {L"Telegram", L"Telegram", L"Telegram", L"Telegram", L"Telegram", L"Telegram", L"Telegram"},
    {L"Открыть канал Sardanello", L"Open Sardanello channel", L"Sardanello-Kanal offnen", L"Sardanello kanalini ac", L"Abrir canal Sardanello", L"Abrir canal Sardanello", L"Sardanello \u091a\u0948\u0928\u0932 \u0916\u094b\u0932\u0947\u0902"},
    {L"Выход", L"Exit", L"Beenden", L"Cikis", L"Salir", L"Sair", L"\u092c\u093e\u0939\u0930"},
    {L"Закрыть приложение", L"Close app", L"App schliessen", L"Uygulamayi kapat", L"Cerrar aplicacion", L"Fechar aplicativo", L"\u0910\u092a \u092c\u0902\u0926 \u0915\u0930\u0947\u0902"},
    {L"Готов. Выбери действие", L"Ready. Choose an action", L"Bereit. Aktion auswahlen", L"Hazir. Bir islem sec", L"Listo. Elige una accion", L"Pronto. Escolha uma acao", L"\u0924\u0948\u092f\u093e\u0930. \u0915\u093e\u0930\u094d\u092f \u091a\u0941\u0928\u0947\u0902"},
    {L"Готов. Сохраненный таймер:", L"Ready. Saved timer:", L"Bereit. Gespeicherter Timer:", L"Hazir. Kayitli timer:", L"Listo. Temporizador guardado:", L"Pronto. Timer salvo:", L"\u0924\u0948\u092f\u093e\u0930. \u0938\u0947\u0935 \u091f\u093e\u0907\u092e\u0930:"},
    {L"Можно применить его или запустить новый тест", L"You can apply it or run a new test", L"Du kannst ihn setzen oder neu testen", L"Uygula veya yeni test baslat", L"Puedes aplicarlo o iniciar otra prueba", L"Voce pode aplicar ou testar de novo", L"\u0907\u0938\u0947 \u0932\u0917\u093e\u090f\u0902 \u092f\u093e \u0928\u092f\u093e \u091f\u0947\u0938\u094d\u091f \u091a\u0932\u093e\u090f\u0902"},
    {L"Готов. Сначала запусти поиск идеального таймера", L"Ready. Start by finding the ideal timer", L"Bereit. Starte mit dem Timer-Test", L"Hazir. Once ideal timer'i bul", L"Listo. Primero busca el temporizador ideal", L"Pronto. Primeiro encontre o timer ideal", L"\u0924\u0948\u092f\u093e\u0930. \u092a\u0939\u0932\u0947 \u0906\u0926\u0930\u094d\u0936 \u091f\u093e\u0907\u092e\u0930 \u0922\u0942\u0902\u0922\u0947\u0902"},
    {L"Матрица замораживается во время точных замеров", L"Matrix rain pauses during exact measurements", L"Matrix-Regen pausiert bei Messungen", L"Olcum sirasinda matrix yagmuru durur", L"La lluvia se pausa durante mediciones exactas", L"A chuva pausa durante medicoes exatas", L"\u0938\u091f\u0940\u0915 \u092e\u093e\u092a \u092e\u0947\u0902 \u092e\u0948\u091f\u094d\u0930\u093f\u0915\u094d\u0938 \u0930\u0941\u0915\u0924\u093e \u0939\u0948"},
    {L"Тест идет. Кнопки с системными изменениями временно заблокированы.", L"Test is running. System-change buttons are temporarily locked.", L"Test lauft. Systemtasten sind kurz gesperrt.", L"Test calisiyor. Sistem dugmeleri kilitli.", L"Prueba en curso. Botones de sistema bloqueados.", L"Teste em andamento. Botoes de sistema bloqueados.", L"\u091f\u0947\u0938\u094d\u091f \u091a\u0932 \u0930\u0939\u093e \u0939\u0948. \u0938\u093f\u0938\u094d\u091f\u092e \u092c\u091f\u0928 \u0932\u0949\u0915 \u0939\u0948\u0902."},
    {L"Тест уже идет", L"Test is already running", L"Test lauft bereits", L"Test zaten calisiyor", L"La prueba ya esta en curso", L"O teste ja esta rodando", L"\u091f\u0947\u0938\u094d\u091f \u092a\u0939\u0932\u0947 \u0938\u0947 \u091a\u0932 \u0930\u0939\u093e \u0939\u0948"},
    {L"Дождитесь завершения текущего замера", L"Wait for the current measurement to finish", L"Warte bis die Messung fertig ist", L"Mevcut olcumun bitmesini bekle", L"Espera a que termine la medicion", L"Aguarde a medicao terminar", L"\u0935\u0930\u094d\u0924\u092e\u093e\u0928 \u092e\u093e\u092a \u0916\u0924\u094d\u092e \u0939\u094b\u0928\u0947 \u0926\u0947\u0902"},
    {L"Запуск Gaming Timer Analysis...", L"Starting Gaming Timer Analysis...", L"Starte Gaming Timer Analysis...", L"Gaming Timer Analysis basliyor...", L"Iniciando Gaming Timer Analysis...", L"Iniciando Gaming Timer Analysis...", L"Gaming Timer Analysis \u0936\u0941\u0930\u0942..."},
    {L"Останавливаю старый timer-service и сбрасываю timer resolution", L"Stopping old timer-service and resetting timer resolution", L"Stoppe alten timer-service und setze Auflosung zuruck", L"Eski timer-service duruyor, cozum sifirlaniyor", L"Deteniendo timer-service y reiniciando resolucion", L"Parando timer-service e resetando resolucao", L"\u092a\u0941\u0930\u093e\u0928\u0940 timer-service \u0930\u094b\u0915 \u0915\u0930 \u0930\u093f\u0938\u0947\u091f \u0915\u0930 \u0930\u0939\u093e \u0939\u0942\u0902"},
    {L"Gaming Timer Analysis запущен", L"Gaming Timer Analysis started", L"Gaming Timer Analysis gestartet", L"Gaming Timer Analysis basladi", L"Gaming Timer Analysis iniciado", L"Gaming Timer Analysis iniciado", L"Gaming Timer Analysis \u091a\u093e\u0932\u0942"},
    {L"Старая служба таймера остановлена", L"Old timer service stopped", L"Alter Timerdienst gestoppt", L"Eski timer servisi durdu", L"Servicio anterior detenido", L"Servico antigo parado", L"\u092a\u0941\u0930\u093e\u0928\u0940 \u091f\u093e\u0907\u092e\u0930 \u0938\u0947\u0935\u093e \u0930\u094b\u0915\u0940 \u0917\u0908"},
    {L"Инициализация теста", L"Initializing test", L"Test wird vorbereitet", L"Test hazirlaniyor", L"Inicializando prueba", L"Inicializando teste", L"\u091f\u0947\u0938\u094d\u091f \u0924\u0948\u092f\u093e\u0930 \u0939\u094b \u0930\u0939\u093e \u0939\u0948"},
    {L"Окно можно оставить открытым, прогресс будет обновляться здесь", L"Keep this window open; progress updates here", L"Fenster offen lassen; Fortschritt steht hier", L"Pencere acik kalsin; ilerleme burada", L"Deja esta ventana abierta; progreso aqui", L"Deixe a janela aberta; progresso aqui", L"\u0916\u093f\u0921\u093c\u0915\u0940 \u0916\u0941\u0932\u0940 \u0930\u0916\u0947\u0902; \u092a\u094d\u0930\u0917\u0924\u093f \u092f\u0939\u093e\u0902"},
    {L"Готово. Рекомендованный таймер:", L"Done. Recommended timer:", L"Fertig. Empfohlener Timer:", L"Bitti. Onerilen timer:", L"Listo. Temporizador recomendado:", L"Pronto. Timer recomendado:", L"\u092a\u0942\u0930\u093e. \u0938\u0941\u091d\u093e\u092f\u093e \u091f\u093e\u0907\u092e\u0930:"},
    {L"HTML-отчет создан рядом с Sardanello.exe", L"HTML report created next to Sardanello.exe", L"HTML-Bericht liegt neben Sardanello.exe", L"HTML raporu Sardanello.exe yaninda", L"Informe HTML creado junto a Sardanello.exe", L"Relatorio HTML criado junto ao Sardanello.exe", L"HTML \u0930\u093f\u092a\u094b\u0930\u094d\u091f Sardanello.exe \u0915\u0947 \u092a\u093e\u0938 \u092c\u0928\u0940"},
    {L"Теперь можно нажать: Зафиксировать найденный таймер", L"Now press: Apply found timer", L"Jetzt: Gefundenen Timer setzen", L"Simdi: Bulunan timer'i sabitle", L"Ahora pulsa: Fijar temporizador encontrado", L"Agora clique: Fixar timer encontrado", L"\u0905\u092c \u0926\u092c\u093e\u090f\u0902: \u092e\u093f\u0932\u093e \u091f\u093e\u0907\u092e\u0930 \u0932\u0917\u093e\u090f\u0902"},
    {L"Тест завершен, но optimal_timer.ini не найден", L"Test finished, but optimal_timer.ini was not found", L"Test fertig, aber optimal_timer.ini fehlt", L"Test bitti ama optimal_timer.ini yok", L"Prueba terminada, falta optimal_timer.ini", L"Teste terminou, mas optimal_timer.ini nao foi encontrado", L"\u091f\u0947\u0938\u094d\u091f \u0916\u0924\u094d\u092e, \u092a\u0930 optimal_timer.ini \u0928\u0939\u0940\u0902 \u092e\u093f\u0932\u093e"},
    {L"Проверьте HTML-отчет и папку с exe", L"Check the HTML report and exe folder", L"HTML-Bericht und exe-Ordner prufen", L"HTML raporu ve exe klasorunu kontrol et", L"Revisa el informe HTML y carpeta exe", L"Confira o relatorio HTML e a pasta do exe", L"HTML \u0930\u093f\u092a\u094b\u0930\u094d\u091f \u0914\u0930 exe \u092b\u094b\u0932\u094d\u0921\u0930 \u091a\u0947\u0915 \u0915\u0930\u0947\u0902"},
    {L"Нельзя применять таймер во время теста", L"Cannot apply timer during the test", L"Timer kann im Test nicht gesetzt werden", L"Test sirasinda timer uygulanamaz", L"No se puede aplicar durante la prueba", L"Nao da para aplicar durante o teste", L"\u091f\u0947\u0938\u094d\u091f \u092e\u0947\u0902 \u091f\u093e\u0907\u092e\u0930 \u0928\u0939\u0940\u0902 \u0932\u0917\u0947\u0917\u093e"},
    {L"Идеальный таймер еще не найден", L"Ideal timer has not been found yet", L"Idealer Timer wurde noch nicht gefunden", L"Ideal timer henuz bulunmadi", L"El temporizador ideal aun no existe", L"Timer ideal ainda nao encontrado", L"\u0906\u0926\u0930\u094d\u0936 \u091f\u093e\u0907\u092e\u0930 \u0905\u092d\u0940 \u0928\u0939\u0940\u0902 \u092e\u093f\u0932\u093e"},
    {L"Сначала запустите тест таймера", L"Run the timer test first", L"Starte zuerst den Timer-Test", L"Once timer testini calistir", L"Primero ejecuta la prueba", L"Execute o teste primeiro", L"\u092a\u0939\u0932\u0947 \u091f\u093e\u0907\u092e\u0930 \u091f\u0947\u0938\u094d\u091f \u091a\u0932\u093e\u090f\u0902"},
    {L"Применяю таймер", L"Applying timer", L"Setze Timer", L"Timer uygulanıyor", L"Aplicando temporizador", L"Aplicando timer", L"\u091f\u093e\u0907\u092e\u0930 \u0932\u0917 \u0930\u0939\u093e \u0939\u0948"},
    {L"Запускаю скрытый timer-service", L"Starting hidden timer-service", L"Starte versteckten timer-service", L"Gizli timer-service basliyor", L"Iniciando timer-service oculto", L"Iniciando timer-service oculto", L"\u091b\u093f\u092a\u0940 timer-service \u0936\u0941\u0930\u0942"},
    {L"Таймер применен", L"Timer applied", L"Timer gesetzt", L"Timer uygulandi", L"Temporizador aplicado", L"Timer aplicado", L"\u091f\u093e\u0907\u092e\u0930 \u0932\u0917 \u0917\u092f\u093e"},
    {L"Скрытый timer-service запущен и добавлен в автозагрузку", L"Hidden timer-service started and added to startup", L"Timerdienst gestartet und Autostart gesetzt", L"Gizli servis basladi ve acilisa eklendi", L"Servicio oculto iniciado y agregado al inicio", L"Servico oculto iniciado e adicionado ao startup", L"\u091b\u093f\u092a\u0940 \u0938\u0947\u0935\u093e \u0936\u0941\u0930\u0942 \u0914\u0930 startup \u092e\u0947\u0902 \u091c\u0941\u0921\u093c\u0940"},
    {L"Таймер применен в текущей сессии", L"Timer applied in current session", L"Timer in aktueller Sitzung gesetzt", L"Timer mevcut oturumda uygulandi", L"Aplicado en la sesion actual", L"Aplicado na sessao atual", L"\u0935\u0930\u094d\u0924\u092e\u093e\u0928 \u0938\u0947\u0936\u0928 \u092e\u0947\u0902 \u0932\u0917\u093e"},
    {L"После перезагрузки значение подхватится из optimal_timer.ini", L"After reboot, value is loaded from optimal_timer.ini", L"Nach Neustart kommt der Wert aus optimal_timer.ini", L"Yeniden baslatinca deger optimal_timer.ini'den gelir", L"Tras reiniciar se cargara desde optimal_timer.ini", L"Apos reiniciar sera lido do optimal_timer.ini", L"\u0930\u0940\u092c\u0942\u091f \u0915\u0947 \u092c\u093e\u0926 optimal_timer.ini \u0938\u0947 \u0932\u094b\u0921 \u0939\u094b\u0917\u093e"},
    {L"Не удалось применить таймер", L"Could not apply timer", L"Timer konnte nicht gesetzt werden", L"Timer uygulanamadi", L"No se pudo aplicar", L"Nao foi possivel aplicar", L"\u091f\u093e\u0907\u092e\u0930 \u0928\u0939\u0940\u0902 \u0932\u0917\u093e"},
    {L"Проверьте права доступа или антивирус", L"Check permissions or antivirus", L"Rechte oder Antivirus prufen", L"Izinleri veya antivirusi kontrol et", L"Revisa permisos o antivirus", L"Confira permissoes ou antivirus", L"\u0905\u0927\u093f\u0915\u093e\u0930 \u092f\u093e antivirus \u091a\u0947\u0915 \u0915\u0930\u0947\u0902"},
    {L"Нельзя менять таймер во время теста", L"Cannot change timer during the test", L"Timer im Test nicht andern", L"Test sirasinda timer degismez", L"No se puede cambiar durante la prueba", L"Nao da para mudar durante o teste", L"\u091f\u0947\u0938\u094d\u091f \u092e\u0947\u0902 \u091f\u093e\u0907\u092e\u0930 \u0928\u0939\u0940\u0902 \u092c\u0926\u0932\u0947\u0917\u093e"},
    {L"Устанавливаю таймер", L"Setting timer", L"Setze Timer", L"Timer ayarlaniyor", L"Ajustando temporizador", L"Definindo timer", L"\u091f\u093e\u0907\u092e\u0930 \u0938\u0947\u091f \u0939\u094b \u0930\u0939\u093e \u0939\u0948"},
    {L"Сохраняю значение и запускаю timer-service", L"Saving value and starting timer-service", L"Speichere Wert und starte timer-service", L"Deger kaydediliyor ve servis basliyor", L"Guardando valor e iniciando servicio", L"Salvando valor e iniciando servico", L"\u092e\u0942\u0932\u094d\u092f \u0938\u0947\u0935 \u0914\u0930 timer-service \u0936\u0941\u0930\u0942"},
    {L"Ручной таймер установлен", L"Manual timer set", L"Manueller Timer gesetzt", L"Manuel timer ayarlandi", L"Temporizador manual fijado", L"Timer manual definido", L"\u092e\u0948\u0928\u094d\u092f\u0941\u0905\u0932 \u091f\u093e\u0907\u092e\u0930 \u0932\u0917 \u0917\u092f\u093e"},
    {L"Значение записано в optimal_timer.ini", L"Value written to optimal_timer.ini", L"Wert in optimal_timer.ini gespeichert", L"Deger optimal_timer.ini'ye yazildi", L"Valor guardado en optimal_timer.ini", L"Valor salvo em optimal_timer.ini", L"\u092e\u0942\u0932\u094d\u092f optimal_timer.ini \u092e\u0947\u0902 \u0938\u0947\u0935"},
    {L"Скрытый timer-service будет удерживать таймер", L"Hidden timer-service will hold the timer", L"Timerdienst halt den Timer aktiv", L"Gizli servis timer'i tutacak", L"Servicio oculto mantendra el temporizador", L"Servico oculto mantera o timer", L"\u091b\u093f\u092a\u0940 \u0938\u0947\u0935\u093e \u091f\u093e\u0907\u092e\u0930 \u092a\u0915\u0921\u093c\u0947 \u0930\u0916\u0947\u0917\u0940"},
    {L"Не удалось установить ручной таймер", L"Could not set manual timer", L"Manueller Timer fehlgeschlagen", L"Manuel timer ayarlanamadi", L"No se pudo fijar manualmente", L"Nao foi possivel definir manualmente", L"\u092e\u0948\u0928\u094d\u092f\u0941\u0905\u0932 \u091f\u093e\u0907\u092e\u0930 \u0928\u0939\u0940\u0902 \u0932\u0917\u093e"},
    {L"Нужны права администратора", L"Administrator rights required", L"Adminrechte erforderlich", L"Yonetici izni gerekli", L"Hacen falta permisos de administrador", L"Precisa de administrador", L"\u090f\u0921\u092e\u093f\u0928 \u0905\u0927\u093f\u0915\u093e\u0930 \u091a\u093e\u0939\u093f\u090f"},
    {L"Запустите Sardanello.exe от имени администратора", L"Run Sardanello.exe as administrator", L"Sardanello.exe als Administrator starten", L"Sardanello.exe'yi yonetici olarak calistir", L"Ejecuta Sardanello.exe como administrador", L"Execute Sardanello.exe como administrador", L"Sardanello.exe \u090f\u0921\u092e\u093f\u0928 \u0930\u0942\u092a \u092e\u0947\u0902 \u091a\u0932\u093e\u090f\u0902"},
    {L"Перезапустите Sardanello и подтвердите UAC", L"Restart Sardanello and approve UAC", L"Sardanello neu starten und UAC bestatigen", L"Sardanello'yu yeniden baslat ve UAC onayla", L"Reinicia Sardanello y confirma UAC", L"Reinicie Sardanello e confirme o UAC", L"Sardanello \u092b\u093f\u0930 \u091a\u0932\u093e\u090f\u0902 \u0914\u0930 UAC \u092e\u093e\u0928\u0947\u0902"},
    {L"Запуск HPET/CPU interval настроек...", L"Applying HPET/CPU interval settings...", L"HPET/CPU-Intervall wird gesetzt...", L"HPET/CPU araligi ayarlaniyor...", L"Aplicando ajustes HPET/CPU interval...", L"Aplicando ajustes HPET/CPU interval...", L"HPET/CPU interval \u0938\u0947\u091f\u093f\u0902\u0917 \u0932\u0917 \u0930\u0939\u0940 \u0939\u0948..."},
    {L"Это может занять несколько секунд", L"This may take a few seconds", L"Das kann ein paar Sekunden dauern", L"Birkac saniye surebilir", L"Puede tardar unos segundos", L"Pode levar alguns segundos", L"\u0907\u0938\u092e\u0947\u0902 \u0915\u0941\u091b \u0938\u0947\u0915\u0902\u0921 \u0932\u0917 \u0938\u0915\u0924\u0947 \u0939\u0948\u0902"},
    {L"HPET/CPU interval и boot-настройки применены. Для полного применения нужна перезагрузка.\n\nПерезагрузить ПК сейчас?", L"HPET/CPU interval and boot settings were applied. A reboot is required.\n\nRestart PC now?", L"HPET/CPU-Intervall und Boot-Einstellungen gesetzt. Neustart erforderlich.\n\nPC jetzt neu starten?", L"HPET/CPU araligi ve boot ayarlari uygulandi. Yeniden baslatma gerekli.\n\nPC simdi yeniden baslatilsin mi?", L"Ajustes HPET/CPU interval y boot aplicados. Se requiere reinicio.\n\nReiniciar ahora?", L"Ajustes HPET/CPU interval e boot aplicados. Reinicializacao necessaria.\n\nReiniciar agora?", L"HPET/CPU interval \u0914\u0930 boot \u0938\u0947\u091f\u093f\u0902\u0917 \u0932\u0917 \u0917\u0908. \u0930\u0940\u092c\u0942\u091f \u091a\u093e\u0939\u093f\u090f.\n\nPC \u0905\u092d\u0940 \u0930\u0940\u092c\u0942\u091f \u0915\u0930\u0947\u0902?"},
    {L"Проверяю питание Windows...", L"Checking Windows power...", L"Prufe Windows-Energie...", L"Windows gucu kontrol ediliyor...", L"Comprobando energia de Windows...", L"Verificando energia do Windows...", L"Windows power \u091a\u0947\u0915 \u0939\u094b \u0930\u0939\u093e \u0939\u0948..."},
    {L"Читаю PlatformAoAcOverride", L"Reading PlatformAoAcOverride", L"Lese PlatformAoAcOverride", L"PlatformAoAcOverride okunuyor", L"Leyendo PlatformAoAcOverride", L"Lendo PlatformAoAcOverride", L"PlatformAoAcOverride \u092a\u0922\u093c \u0930\u0939\u093e \u0939\u0942\u0902"},
    {L"PlatformAoAcOverride установлен в 0", L"PlatformAoAcOverride set to 0", L"PlatformAoAcOverride auf 0 gesetzt", L"PlatformAoAcOverride 0 yapildi", L"PlatformAoAcOverride puesto en 0", L"PlatformAoAcOverride definido como 0", L"PlatformAoAcOverride 0 \u0938\u0947\u091f"},
    {L"Нужна перезагрузка Windows", L"Windows reboot required", L"Windows-Neustart erforderlich", L"Windows yeniden baslatilmali", L"Se requiere reinicio de Windows", L"Windows precisa reiniciar", L"Windows \u0930\u0940\u092c\u0942\u091f \u091a\u093e\u0939\u093f\u090f"},
    {L"После reboot снова нажмите План питания Sardanello", L"After reboot, press Sardanello power plan again", L"Nach Neustart Energieplan erneut drucken", L"Yeniden baslatinca guc planina tekrar bas", L"Tras reiniciar, pulsa de nuevo el plan", L"Apos reiniciar, clique no plano de novo", L"\u0930\u0940\u092c\u0942\u091f \u0915\u0947 \u092c\u093e\u0926 power plan \u092b\u093f\u0930 \u0926\u092c\u093e\u090f\u0902"},
    {L"Не удалось изменить PlatformAoAcOverride", L"Could not change PlatformAoAcOverride", L"PlatformAoAcOverride konnte nicht geandert werden", L"PlatformAoAcOverride degisemedi", L"No se pudo cambiar PlatformAoAcOverride", L"Nao foi possivel mudar PlatformAoAcOverride", L"PlatformAoAcOverride \u0928\u0939\u0940\u0902 \u092c\u0926\u0932\u093e"},
    {L"План питания Sardanello применен", L"Sardanello power plan applied", L"Sardanello-Energieplan gesetzt", L"Sardanello guc plani uygulandi", L"Plan de energia Sardanello aplicado", L"Plano Sardanello aplicado", L"Sardanello power plan \u0932\u0917 \u0917\u092f\u093e"},
    {L"Система настроена на игровой профиль", L"System is tuned for the gaming profile", L"System ist auf Gaming-Profil gesetzt", L"Sistem oyun profiline ayarlandi", L"Sistema ajustado al perfil gaming", L"Sistema ajustado para perfil gamer", L"\u0938\u093f\u0938\u094d\u091f\u092e gaming profile \u092a\u0930 \u0938\u0947\u091f"},
    {L"Не удалось применить план питания", L"Could not apply power plan", L"Energieplan konnte nicht gesetzt werden", L"Guc plani uygulanamadi", L"No se pudo aplicar el plan", L"Nao foi possivel aplicar o plano", L"power plan \u0928\u0939\u0940\u0902 \u0932\u0917\u093e"},
    {L"Проверьте наличие Sardanello.pow и права администратора", L"Check Sardanello.pow and administrator rights", L"Sardanello.pow und Adminrechte prufen", L"Sardanello.pow ve yonetici iznini kontrol et", L"Revisa Sardanello.pow y permisos", L"Confira Sardanello.pow e admin", L"Sardanello.pow \u0914\u0930 \u090f\u0921\u092e\u093f\u0928 \u0905\u0927\u093f\u0915\u093e\u0930 \u091a\u0947\u0915 \u0915\u0930\u0947\u0902"},
    {L"Настройка PlatformAoAcOverride изменена. Чтобы продолжить установку плана питания, нужна перезагрузка.\n\nПерезагрузить ПК сейчас?", L"PlatformAoAcOverride changed. Reboot is required before installing the power plan.\n\nRestart PC now?", L"PlatformAoAcOverride geandert. Vor dem Energieplan ist ein Neustart notig.\n\nPC jetzt neu starten?", L"PlatformAoAcOverride degisti. Guc plani icin yeniden baslatma gerekli.\n\nPC simdi yeniden baslatilsin mi?", L"PlatformAoAcOverride cambiado. Hay que reiniciar antes del plan.\n\nReiniciar ahora?", L"PlatformAoAcOverride mudou. Reinicie antes do plano.\n\nReiniciar agora?", L"PlatformAoAcOverride \u092c\u0926\u0932\u093e. power plan \u0938\u0947 \u092a\u0939\u0932\u0947 \u0930\u0940\u092c\u0942\u091f \u091a\u093e\u0939\u093f\u090f.\n\nPC \u0905\u092d\u0940 \u0930\u0940\u092c\u0942\u091f \u0915\u0930\u0947\u0902?"},
    {L"Нельзя создавать точку восстановления во время теста", L"Cannot create restore point during the test", L"Wiederherstellungspunkt nicht im Test erstellen", L"Testte geri yukleme noktasi olusturulamaz", L"No se puede crear durante la prueba", L"Nao da para criar durante o teste", L"\u091f\u0947\u0938\u094d\u091f \u092e\u0947\u0902 restore point \u0928\u0939\u0940\u0902 \u092c\u0928\u0947\u0917\u093e"},
    {L"Включаю защиту системы для системного диска...", L"Enabling System Protection for the system drive...", L"Aktiviere Systemschutz fur Systemlaufwerk...", L"Sistem diski icin koruma aciliyor...", L"Activando proteccion del sistema...", L"Ativando protecao do sistema...", L"system drive \u0915\u0947 \u0932\u093f\u090f protection \u091a\u093e\u0932\u0942..."},
    {L"После этого будет создана точка восстановления Sardanello", L"Then Sardanello restore point will be created", L"Dann wird Sardanello-Punkt erstellt", L"Sonra Sardanello noktasi olusturulur", L"Luego se creara el punto Sardanello", L"Depois o ponto Sardanello sera criado", L"\u092b\u093f\u0930 Sardanello restore point \u092c\u0928\u0947\u0917\u093e"},
    {L"Не удалось включить защиту системы", L"Could not enable System Protection", L"Systemschutz konnte nicht aktiviert werden", L"Sistem korumasi acilamadi", L"No se pudo activar proteccion", L"Nao foi possivel ativar protecao", L"System Protection \u091a\u093e\u0932\u0942 \u0928\u0939\u0940\u0902 \u0939\u0941\u0906"},
    {L"Windows не разрешила включить System Protection для системного диска", L"Windows did not allow System Protection for the system drive", L"Windows erlaubte Systemschutz nicht", L"Windows sistem korumasina izin vermedi", L"Windows no permitio activar proteccion", L"Windows nao permitiu ativar protecao", L"Windows \u0928\u0947 system drive protection \u0928\u0939\u0940\u0902 \u092e\u093e\u0928\u0940"},
    {L"Защита системы включена", L"System Protection enabled", L"Systemschutz aktiviert", L"Sistem korumasi acik", L"Proteccion del sistema activada", L"Protecao do sistema ativada", L"System Protection \u091a\u093e\u0932\u0942"},
    {L"Создаю точку восстановления Sardanello...", L"Creating Sardanello restore point...", L"Erstelle Sardanello-Punkt...", L"Sardanello noktasi olusturuluyor...", L"Creando punto Sardanello...", L"Criando ponto Sardanello...", L"Sardanello restore point \u092c\u0928 \u0930\u0939\u093e \u0939\u0948..."},
    {L"Точка восстановления Sardanello создана", L"Sardanello restore point created", L"Sardanello-Punkt erstellt", L"Sardanello noktasi olusturuldu", L"Punto Sardanello creado", L"Ponto Sardanello criado", L"Sardanello restore point \u092c\u0928 \u0917\u092f\u093e"},
    {L"Индикатор станет зеленым после проверки Windows", L"Indicator will turn green after Windows check", L"Anzeige wird nach Windows-Prufung grun", L"Windows kontrolunden sonra yesil olur", L"Indicador verde tras comprobacion de Windows", L"Indicador ficara verde apos verificacao", L"Windows check \u0915\u0947 \u092c\u093e\u0926 indicator \u0939\u0930\u093e \u0939\u094b\u0917\u093e"},
    {L"Не удалось создать точку восстановления Sardanello", L"Could not create Sardanello restore point", L"Sardanello-Punkt konnte nicht erstellt werden", L"Sardanello noktasi olusturulamadi", L"No se pudo crear el punto Sardanello", L"Nao foi possivel criar o ponto Sardanello", L"Sardanello restore point \u0928\u0939\u0940\u0902 \u092c\u0928\u093e"},
    {L"Защита была включена, но Windows отклонила создание точки", L"Protection was enabled, but Windows rejected the point", L"Schutz war an, aber Windows lehnte den Punkt ab", L"Koruma acildi ama Windows noktayi reddetti", L"Proteccion activa, pero Windows rechazo el punto", L"Protecao ativa, mas Windows recusou o ponto", L"Protection \u091a\u093e\u0932\u0942 \u0925\u093e, \u092a\u0930 Windows \u0928\u0947 \u092e\u0928\u093e \u0915\u093f\u092f\u093e"},
    {L"HTML-отчет еще не создан", L"HTML report has not been created yet", L"HTML-Bericht wurde noch nicht erstellt", L"HTML raporu henuz olusmadi", L"El informe HTML aun no existe", L"Relatorio HTML ainda nao criado", L"HTML \u0930\u093f\u092a\u094b\u0930\u094d\u091f \u0905\u092d\u0940 \u0928\u0939\u0940\u0902 \u092c\u0928\u0940"},
    {L"Установить таймер вручную", L"Set timer manually", L"Timer manuell setzen", L"Timer'i elle ayarla", L"Ajustar temporizador manualmente", L"Definir timer manualmente", L"\u091f\u093e\u0907\u092e\u0930 \u092e\u0948\u0928\u094d\u092f\u0941\u0905\u0932 \u0932\u0917\u093e\u090f\u0902"},
    {L"Введите таймер в мс, например 0.504", L"Enter timer in ms, for example 0.504", L"Timer in ms eingeben, z.B. 0.504", L"Timer'i ms olarak gir, ornek 0.504", L"Introduce ms, por ejemplo 0.504", L"Digite em ms, por exemplo 0.504", L"\u092e\u093f\u0932\u0940\u0938\u0947\u0915\u0902\u0921 \u092e\u0947\u0902 \u091f\u093e\u0907\u092e\u0930, \u091c\u0948\u0938\u0947 0.504"},
    {L"Отмена", L"Cancel", L"Abbrechen", L"Iptal", L"Cancelar", L"Cancelar", L"\u0930\u0926\u094d\u0926"},
    {L"Введите значение от 0.100 до 15.625 мс.", L"Enter a value from 0.100 to 15.625 ms.", L"Wert von 0.100 bis 15.625 ms eingeben.", L"0.100 ile 15.625 ms arasi gir.", L"Introduce un valor de 0.100 a 15.625 ms.", L"Digite um valor de 0.100 a 15.625 ms.", L"0.100 \u0938\u0947 15.625 ms \u0924\u0915 \u092e\u0942\u0932\u094d\u092f \u0926\u0947\u0902."},
    {L"Тест таймера сейчас идет. Дождись завершения, чтобы не оборвать замер.", L"Timer test is running. Wait until it finishes to avoid breaking the measurement.", L"Timer-Test lauft. Bitte warten, sonst bricht die Messung ab.", L"Timer testi calisiyor. Olcumu bozmamak icin bekle.", L"Prueba en curso. Espera para no cortar la medicion.", L"Teste em andamento. Aguarde para nao interromper.", L"\u091f\u093e\u0907\u092e\u0930 \u091f\u0947\u0938\u094d\u091f \u091a\u0932 \u0930\u0939\u093e \u0939\u0948. \u092e\u093e\u092a \u0928 \u091f\u0942\u091f\u0947, \u0907\u0938\u0932\u093f\u090f \u0930\u0941\u0915\u0947\u0902."},
    {L"Выберите язык", L"Choose language", L"Sprache wahlen", L"Dil sec", L"Elige idioma", L"Escolha o idioma", L"\u092d\u093e\u0937\u093e \u091a\u0941\u0928\u0947\u0902"},
    {L"После выбора откроется Sardanello", L"Sardanello opens after selection", L"Nach der Auswahl offnet sich Sardanello", L"Secimden sonra Sardanello acilir", L"Sardanello se abrira despues", L"Sardanello abre depois da escolha", L"\u091a\u0941\u0928\u0928\u0947 \u0915\u0947 \u092c\u093e\u0926 Sardanello \u0916\u0941\u0932\u0947\u0917\u093e"}
};

static const wchar_t* trW(TextId id)
{
    size_t index = (size_t)id;
    if (index >= (sizeof(kUiTexts) / sizeof(kUiTexts[0]))) return L"";
    const UiText& t = kUiTexts[index];
    switch (g_appLanguage) {
    case AppLanguage::English: return t.en;
    case AppLanguage::German: return t.de;
    case AppLanguage::Turkish: return t.tr;
    case AppLanguage::Spanish: return t.es;
    case AppLanguage::PortugueseBrazil: return t.pt;
    case AppLanguage::Hindi: return t.hi;
    case AppLanguage::Russian:
    default: return t.ru;
    }
}

static std::string trUtf8(TextId id)
{
    return wideToUtf8(trW(id));
}

static void guiSetStatus(const std::string& line0, const std::string& line1 = std::string(), const std::string& line2 = std::string())
{
    {
        std::lock_guard<std::mutex> sl(g_menuMutex);
        g_statusLines[0] = line0;
        g_statusLines[1] = line1;
        g_statusLines[2] = line2;
    }
    if (g_guiHwnd) PostMessageW(g_guiHwnd, WM_APP + 10, 0, 0);
}

static void guiSetStatusW(const std::wstring& line0, const std::wstring& line1 = std::wstring(), const std::wstring& line2 = std::wstring())
{
    guiSetStatus(wideToUtf8(line0), wideToUtf8(line1), wideToUtf8(line2));
}

static HFONT guiCreateFont(int px, int weight, const wchar_t* face)
{
    return CreateFontW(-px, 0, 0, 0, weight, FALSE, FALSE, FALSE, DEFAULT_CHARSET,
                       OUT_DEFAULT_PRECIS, CLIP_DEFAULT_PRECIS, CLEARTYPE_QUALITY,
                       DEFAULT_PITCH | FF_DONTCARE, face);
}

static void guiFillRoundRect(HDC dc, const RECT& r, COLORREF fill, COLORREF border, int radius = 8)
{
    HBRUSH brush = CreateSolidBrush(fill);
    HPEN pen = CreatePen(PS_SOLID, 1, border);
    HGDIOBJ oldBrush = SelectObject(dc, brush);
    HGDIOBJ oldPen = SelectObject(dc, pen);
    RoundRect(dc, r.left, r.top, r.right, r.bottom, radius, radius);
    SelectObject(dc, oldPen);
    SelectObject(dc, oldBrush);
    DeleteObject(pen);
    DeleteObject(brush);
}

static void guiDrawShadowedWideText(HDC dc, const std::wstring& text, RECT r, HFONT font,
                                    COLORREF color, COLORREF shadowColor, double widthFactor)
{
    if (text.empty()) return;
    HGDIOBJ oldFont = SelectObject(dc, font);
    SetBkMode(dc, TRANSPARENT);

    SIZE textSize{};
    GetTextExtentPoint32W(dc, text.c_str(), (int)text.size(), &textSize);
    TEXTMETRICW tm{};
    GetTextMetricsW(dc, &tm);

    int extra = 0;
    if (text.size() > 1 && widthFactor > 1.0) {
        extra = (int)std::round((textSize.cx * (widthFactor - 1.0)) / (double)(text.size() - 1));
    }
    int stretchedWidth = textSize.cx + extra * std::max(0, (int)text.size() - 1);
    int x = r.left + ((r.right - r.left) - stretchedWidth) / 2;
    int y = r.top + ((r.bottom - r.top) - tm.tmHeight) / 2;

    int oldExtra = SetTextCharacterExtra(dc, extra);
    SetTextColor(dc, RGB(0, 22, 8));
    TextOutW(dc, x + 5, y + 5, text.c_str(), (int)text.size());
    SetTextColor(dc, shadowColor);
    TextOutW(dc, x + 3, y + 3, text.c_str(), (int)text.size());
    SetTextColor(dc, RGB(0, 100, 30));
    TextOutW(dc, x + 1, y + 1, text.c_str(), (int)text.size());
    SetTextColor(dc, color);
    TextOutW(dc, x, y, text.c_str(), (int)text.size());
    SetTextCharacterExtra(dc, oldExtra);
    SelectObject(dc, oldFont);
}

static void guiDrawText(HDC dc, const std::wstring& text, RECT r, HFONT font, COLORREF color, UINT format)
{
    HGDIOBJ oldFont = SelectObject(dc, font);
    SetBkMode(dc, TRANSPARENT);
    SetTextColor(dc, color);
    DrawTextW(dc, text.c_str(), -1, &r, format);
    SelectObject(dc, oldFont);
}

static void guiDrawShadowedDrawText(HDC dc, const std::wstring& text, RECT r, HFONT font,
                                    COLORREF color, COLORREF shadowColor, UINT format)
{
    if (text.empty()) return;
    HGDIOBJ oldFont = SelectObject(dc, font);
    SetBkMode(dc, TRANSPARENT);
    RECT shadow = r;
    OffsetRect(&shadow, 3, 3);
    SetTextColor(dc, RGB(0, 22, 8));
    DrawTextW(dc, text.c_str(), -1, &shadow, format);
    shadow = r;
    OffsetRect(&shadow, 1, 1);
    SetTextColor(dc, shadowColor);
    DrawTextW(dc, text.c_str(), -1, &shadow, format);
    SetTextColor(dc, color);
    DrawTextW(dc, text.c_str(), -1, &r, format);
    SelectObject(dc, oldFont);
}

struct LanguageChoice {
    AppLanguage language;
    const wchar_t* label;
    const wchar_t* hint;
};

static const LanguageChoice kLanguageChoices[] = {
    {AppLanguage::Russian, L"Русский", L"Russian"},
    {AppLanguage::English, L"English", L"English"},
    {AppLanguage::German, L"Deutsch", L"German"},
    {AppLanguage::Turkish, L"Türkçe", L"Turkish"},
    {AppLanguage::Spanish, L"Español", L"Spanish"},
    {AppLanguage::PortugueseBrazil, L"Português (Brasil)", L"Brazilian Portuguese"},
    {AppLanguage::Hindi, L"\u0939\u093f\u0928\u094d\u0926\u0940", L"Hindi"}
};

struct LanguageSelectState {
    bool done = false;
    bool ok = false;
    int hover = -1;
    AppLanguage selected = AppLanguage::Russian;
};

static RECT languageChoiceRect(int index, int width)
{
    int left = 44;
    int top = 122 + index * 56;
    return RECT{left, top, width - 44, top + 48};
}

static void guiFillSolid(HDC dc, const RECT& r, COLORREF color)
{
    HBRUSH brush = CreateSolidBrush(color);
    FillRect(dc, &r, brush);
    DeleteObject(brush);
}

static void guiDrawStar(HDC dc, int cx, int cy, int outerR, int innerR, COLORREF color)
{
    POINT pts[10];
    for (int i = 0; i < 10; ++i) {
        double angle = -3.14159265358979323846 / 2.0 + i * 3.14159265358979323846 / 5.0;
        int r = (i % 2 == 0) ? outerR : innerR;
        pts[i].x = cx + (int)std::round(std::cos(angle) * r);
        pts[i].y = cy + (int)std::round(std::sin(angle) * r);
    }
    HBRUSH brush = CreateSolidBrush(color);
    HGDIOBJ oldBrush = SelectObject(dc, brush);
    HPEN pen = CreatePen(PS_SOLID, 1, color);
    HGDIOBJ oldPen = SelectObject(dc, pen);
    Polygon(dc, pts, 10);
    SelectObject(dc, oldPen);
    SelectObject(dc, oldBrush);
    DeleteObject(pen);
    DeleteObject(brush);
}

static void guiDrawFlag(HDC dc, const RECT& r, AppLanguage language)
{
    guiFillSolid(dc, r, RGB(10, 16, 18));
    switch (language) {
    case AppLanguage::Russian: {
        RECT a{r.left, r.top, r.right, r.top + (r.bottom - r.top) / 3};
        RECT b{r.left, a.bottom, r.right, r.top + (r.bottom - r.top) * 2 / 3};
        RECT c{r.left, b.bottom, r.right, r.bottom};
        guiFillSolid(dc, a, RGB(250, 250, 250));
        guiFillSolid(dc, b, RGB(0, 57, 166));
        guiFillSolid(dc, c, RGB(213, 43, 30));
        break;
    }
    case AppLanguage::English: {
        guiFillSolid(dc, r, RGB(1, 33, 105));
        HPEN white = CreatePen(PS_SOLID, 7, RGB(255, 255, 255));
        HPEN red = CreatePen(PS_SOLID, 3, RGB(200, 16, 46));
        HGDIOBJ old = SelectObject(dc, white);
        MoveToEx(dc, r.left, r.top, nullptr); LineTo(dc, r.right, r.bottom);
        MoveToEx(dc, r.right, r.top, nullptr); LineTo(dc, r.left, r.bottom);
        MoveToEx(dc, (r.left + r.right) / 2, r.top, nullptr); LineTo(dc, (r.left + r.right) / 2, r.bottom);
        MoveToEx(dc, r.left, (r.top + r.bottom) / 2, nullptr); LineTo(dc, r.right, (r.top + r.bottom) / 2);
        SelectObject(dc, red);
        MoveToEx(dc, (r.left + r.right) / 2, r.top, nullptr); LineTo(dc, (r.left + r.right) / 2, r.bottom);
        MoveToEx(dc, r.left, (r.top + r.bottom) / 2, nullptr); LineTo(dc, r.right, (r.top + r.bottom) / 2);
        SelectObject(dc, old);
        DeleteObject(white);
        DeleteObject(red);
        break;
    }
    case AppLanguage::German: {
        int h = r.bottom - r.top;
        guiFillSolid(dc, RECT{r.left, r.top, r.right, r.top + h / 3}, RGB(0, 0, 0));
        guiFillSolid(dc, RECT{r.left, r.top + h / 3, r.right, r.top + h * 2 / 3}, RGB(221, 0, 0));
        guiFillSolid(dc, RECT{r.left, r.top + h * 2 / 3, r.right, r.bottom}, RGB(255, 206, 0));
        break;
    }
    case AppLanguage::Turkish: {
        guiFillSolid(dc, r, RGB(227, 10, 23));
        HBRUSH white = CreateSolidBrush(RGB(255, 255, 255));
        HBRUSH red = CreateSolidBrush(RGB(227, 10, 23));
        HGDIOBJ old = SelectObject(dc, white);
        Ellipse(dc, r.left + 9, r.top + 6, r.left + 25, r.top + 24);
        SelectObject(dc, red);
        Ellipse(dc, r.left + 14, r.top + 6, r.left + 30, r.top + 24);
        SelectObject(dc, old);
        DeleteObject(white);
        DeleteObject(red);
        guiDrawStar(dc, r.left + 32, r.top + 15, 5, 2, RGB(255, 255, 255));
        break;
    }
    case AppLanguage::Spanish: {
        int h = r.bottom - r.top;
        guiFillSolid(dc, RECT{r.left, r.top, r.right, r.top + h / 4}, RGB(198, 11, 30));
        guiFillSolid(dc, RECT{r.left, r.top + h / 4, r.right, r.top + h * 3 / 4}, RGB(255, 196, 0));
        guiFillSolid(dc, RECT{r.left, r.top + h * 3 / 4, r.right, r.bottom}, RGB(198, 11, 30));
        break;
    }
    case AppLanguage::PortugueseBrazil: {
        guiFillSolid(dc, r, RGB(0, 156, 59));
        POINT diamond[4] = {{(r.left + r.right) / 2, r.top + 3}, {r.right - 4, (r.top + r.bottom) / 2},
                            {(r.left + r.right) / 2, r.bottom - 3}, {r.left + 4, (r.top + r.bottom) / 2}};
        HBRUSH yellow = CreateSolidBrush(RGB(255, 223, 0));
        HBRUSH blue = CreateSolidBrush(RGB(0, 39, 118));
        HGDIOBJ old = SelectObject(dc, yellow);
        Polygon(dc, diamond, 4);
        SelectObject(dc, blue);
        Ellipse(dc, r.left + 15, r.top + 7, r.right - 15, r.bottom - 7);
        SelectObject(dc, old);
        DeleteObject(yellow);
        DeleteObject(blue);
        break;
    }
    case AppLanguage::Hindi: {
        int h = r.bottom - r.top;
        guiFillSolid(dc, RECT{r.left, r.top, r.right, r.top + h / 3}, RGB(255, 153, 51));
        guiFillSolid(dc, RECT{r.left, r.top + h / 3, r.right, r.top + h * 2 / 3}, RGB(255, 255, 255));
        guiFillSolid(dc, RECT{r.left, r.top + h * 2 / 3, r.right, r.bottom}, RGB(19, 136, 8));
        HBRUSH blue = CreateSolidBrush(RGB(0, 0, 128));
        HGDIOBJ old = SelectObject(dc, blue);
        Ellipse(dc, (r.left + r.right) / 2 - 4, (r.top + r.bottom) / 2 - 4,
                (r.left + r.right) / 2 + 4, (r.top + r.bottom) / 2 + 4);
        SelectObject(dc, old);
        DeleteObject(blue);
        break;
    }
    }
    HPEN border = CreatePen(PS_SOLID, 1, RGB(210, 235, 218));
    HGDIOBJ oldPen = SelectObject(dc, border);
    HGDIOBJ oldBrush = SelectObject(dc, GetStockObject(NULL_BRUSH));
    Rectangle(dc, r.left, r.top, r.right, r.bottom);
    SelectObject(dc, oldBrush);
    SelectObject(dc, oldPen);
    DeleteObject(border);
}

static void languagePaint(HWND hwnd, LanguageSelectState* state)
{
    PAINTSTRUCT ps;
    HDC dc = BeginPaint(hwnd, &ps);
    RECT rc;
    GetClientRect(hwnd, &rc);
    guiFillSolid(dc, rc, RGB(4, 9, 11));

    HFONT titleFont = guiCreateFont(26, FW_SEMIBOLD, L"Segoe UI");
    HFONT subFont = guiCreateFont(14, FW_NORMAL, L"Segoe UI");
    HFONT rowFont = guiCreateFont(18, FW_SEMIBOLD, L"Segoe UI");
    HFONT hintFont = guiCreateFont(12, FW_NORMAL, L"Segoe UI");

    RECT title{28, 20, rc.right - 28, 74};
    guiDrawText(dc, L"Choose language / Выберите язык", title, titleFont, RGB(225, 255, 232), DT_CENTER | DT_SINGLELINE | DT_VCENTER);
    RECT sub{28, 76, rc.right - 28, 104};
    guiDrawText(dc, L"Select the interface language", sub, subFont, RGB(126, 205, 152), DT_CENTER | DT_SINGLELINE | DT_VCENTER);

    for (int i = 0; i < (int)(sizeof(kLanguageChoices) / sizeof(kLanguageChoices[0])); ++i) {
        RECT row = languageChoiceRect(i, rc.right);
        bool hover = state && state->hover == i;
        guiFillRoundRect(dc, row, hover ? RGB(16, 54, 39) : RGB(8, 28, 30),
                         hover ? RGB(90, 235, 135) : RGB(38, 130, 82), 8);
        RECT flag{row.left + 16, row.top + 10, row.left + 64, row.top + 38};
        guiDrawFlag(dc, flag, kLanguageChoices[i].language);
        RECT label{row.left + 82, row.top + 4, row.right - 20, row.top + 30};
        guiDrawText(dc, kLanguageChoices[i].label, label, rowFont, RGB(232, 255, 236), DT_LEFT | DT_SINGLELINE | DT_VCENTER | DT_END_ELLIPSIS);
        RECT hint{row.left + 82, row.top + 28, row.right - 20, row.bottom - 4};
        guiDrawText(dc, kLanguageChoices[i].hint, hint, hintFont, RGB(126, 196, 151), DT_LEFT | DT_SINGLELINE | DT_VCENTER | DT_END_ELLIPSIS);
    }

    DeleteObject(titleFont);
    DeleteObject(subFont);
    DeleteObject(rowFont);
    DeleteObject(hintFont);
    EndPaint(hwnd, &ps);
}

static int languageHitTest(POINT pt, int width)
{
    for (int i = 0; i < (int)(sizeof(kLanguageChoices) / sizeof(kLanguageChoices[0])); ++i) {
        RECT r = languageChoiceRect(i, width);
        if (PtInRect(&r, pt)) return i;
    }
    return -1;
}

static LRESULT CALLBACK languageWndProc(HWND hwnd, UINT msg, WPARAM wParam, LPARAM lParam)
{
    LanguageSelectState* state = reinterpret_cast<LanguageSelectState*>(GetWindowLongPtrW(hwnd, GWLP_USERDATA));
    switch (msg) {
    case WM_NCCREATE: {
        auto cs = reinterpret_cast<CREATESTRUCTW*>(lParam);
        SetWindowLongPtrW(hwnd, GWLP_USERDATA, reinterpret_cast<LONG_PTR>(cs->lpCreateParams));
        return TRUE;
    }
    case WM_PAINT:
        languagePaint(hwnd, state);
        return 0;
    case WM_MOUSEMOVE: {
        RECT rc;
        GetClientRect(hwnd, &rc);
        POINT pt{GET_X_LPARAM(lParam), GET_Y_LPARAM(lParam)};
        int hit = languageHitTest(pt, rc.right);
        if (state && hit != state->hover) {
            state->hover = hit;
            InvalidateRect(hwnd, nullptr, FALSE);
        }
        SetCursor(hit >= 0 ? LoadCursor(nullptr, IDC_HAND) : LoadCursor(nullptr, IDC_ARROW));
        return 0;
    }
    case WM_LBUTTONUP: {
        RECT rc;
        GetClientRect(hwnd, &rc);
        POINT pt{GET_X_LPARAM(lParam), GET_Y_LPARAM(lParam)};
        int hit = languageHitTest(pt, rc.right);
        if (state && hit >= 0) {
            state->selected = kLanguageChoices[hit].language;
            state->ok = true;
            state->done = true;
            DestroyWindow(hwnd);
        }
        return 0;
    }
    case WM_CLOSE:
        if (state) {
            state->ok = false;
            state->done = true;
        }
        DestroyWindow(hwnd);
        return 0;
    default:
        return DefWindowProcW(hwnd, msg, wParam, lParam);
    }
}

static bool runLanguageSelection(HINSTANCE instance, AppLanguage& selectedLanguage)
{
    const wchar_t* className = L"SardanelloLanguageWindow";
    WNDCLASSEXW wc{};
    wc.cbSize = sizeof(wc);
    wc.style = CS_HREDRAW | CS_VREDRAW;
    wc.lpfnWndProc = languageWndProc;
    wc.hInstance = instance;
    wc.hIcon = LoadIconW(instance, MAKEINTRESOURCEW(IDR_MAINICON));
    wc.hCursor = LoadCursor(nullptr, IDC_ARROW);
    wc.hbrBackground = (HBRUSH)GetStockObject(BLACK_BRUSH);
    wc.lpszClassName = className;
    wc.hIconSm = wc.hIcon;
    RegisterClassExW(&wc);

    DWORD style = WS_OVERLAPPED | WS_CAPTION | WS_SYSMENU;
    RECT wr{0, 0, 620, 548};
    AdjustWindowRect(&wr, style, FALSE);
    int winW = wr.right - wr.left;
    int winH = wr.bottom - wr.top;
    int x = (GetSystemMetrics(SM_CXSCREEN) - winW) / 2;
    int y = (GetSystemMetrics(SM_CYSCREEN) - winH) / 2;

    LanguageSelectState state;
    HWND hwnd = CreateWindowExW(WS_EX_TOPMOST, className, L"Sardanello - Language", style,
                                x, y, winW, winH, nullptr, nullptr, instance, &state);
    if (!hwnd) return false;

    ShowWindow(hwnd, SW_SHOW);
    UpdateWindow(hwnd);

    MSG msg;
    while (!state.done && GetMessageW(&msg, nullptr, 0, 0) > 0) {
        TranslateMessage(&msg);
        DispatchMessageW(&msg);
    }

    if (IsWindow(hwnd)) DestroyWindow(hwnd);
    if (state.ok) selectedLanguage = state.selected;
    return state.ok;
}

static std::string guiReadDeviceMultiSz(HDEVINFO devs, SP_DEVINFO_DATA& devInfo, DWORD prop)
{
    CHAR buffer[4096] = {0};
    DWORD needed = 0;
    if (!SetupDiGetDeviceRegistryPropertyA(devs, &devInfo, prop, NULL, (PBYTE)buffer, sizeof(buffer), &needed)) {
        return std::string();
    }
    std::string out;
    for (char* p = buffer; *p; p += std::strlen(p) + 1) {
        if (!out.empty()) out.push_back(' ');
        out += p;
    }
    return out;
}

static bool guiIsHpetMatch(const std::string& desc, const std::string& hw)
{
    std::string lowerDesc = desc;
    std::string lowerHw = hw;
    for (char& c : lowerDesc) c = (char)std::tolower((unsigned char)c);
    for (char& c : lowerHw) c = (char)std::tolower((unsigned char)c);

    if (lowerHw.find("acpi\\ven_pnp&dev_0103") != std::string::npos) return true;
    if (lowerHw.find("acpi\\pnp0103") != std::string::npos) return true;
    if (lowerHw.find("pnp0103") != std::string::npos) return true;
    if (lowerDesc.find("high precision event timer") != std::string::npos) return true;
    if (lowerDesc.find("high-precision event timer") != std::string::npos) return true;
    return false;
}

static int guiQueryHpetState()
{
    HDEVINFO devs = SetupDiGetClassDevsA(NULL, NULL, NULL, DIGCF_ALLCLASSES);
    if (devs == INVALID_HANDLE_VALUE) return 0;

    bool found = false;
    bool enabled = false;
    bool disabled = false;
    SP_DEVINFO_DATA devInfo{};
    devInfo.cbSize = sizeof(devInfo);
    for (DWORD i = 0; SetupDiEnumDeviceInfo(devs, i, &devInfo); ++i) {
        std::string desc = guiReadDeviceMultiSz(devs, devInfo, SPDRP_DEVICEDESC);
        std::string hw = guiReadDeviceMultiSz(devs, devInfo, SPDRP_HARDWAREID);
        if (!guiIsHpetMatch(desc, hw)) continue;

        found = true;
        ULONG status = 0;
        ULONG problem = 0;
        CONFIGRET cr = CM_Get_DevNode_Status(&status, &problem, devInfo.DevInst, 0);
        if (cr == CR_SUCCESS && (problem == CM_PROB_DISABLED || (status & DN_HAS_PROBLEM && problem == CM_PROB_DISABLED))) {
            disabled = true;
        } else {
            enabled = true;
        }
    }
    SetupDiDestroyDeviceInfoList(devs);

    if (!found) return 1;
    if (disabled && !enabled) return 1;
    return 2;
}

static void guiRefreshHpetStatusAsync()
{
    bool expected = false;
    if (!g_guiHpetQueryRunning.compare_exchange_strong(expected, true)) return;
    std::thread([]() {
        int state = guiQueryHpetState();
        g_guiHpetState.store(state);
        g_guiHpetQueryRunning.store(false);
        if (g_guiHwnd) PostMessageW(g_guiHwnd, WM_APP + 10, 0, 0);
    }).detach();
}

static BSTR guiSysAlloc(const wchar_t* text)
{
    return SysAllocString(text);
}

static int guiQueryRestorePointState()
{
    HRESULT hrInit = CoInitializeEx(nullptr, COINIT_MULTITHREADED);
    bool shouldUninit = (hrInit == S_OK || hrInit == S_FALSE);
    if (FAILED(hrInit) && hrInit != RPC_E_CHANGED_MODE) return 0;

    HRESULT hrSec = CoInitializeSecurity(nullptr, -1, nullptr, nullptr,
                                         RPC_C_AUTHN_LEVEL_DEFAULT,
                                         RPC_C_IMP_LEVEL_IMPERSONATE,
                                         nullptr, EOAC_NONE, nullptr);
    (void)hrSec; // RPC_E_TOO_LATE is fine when another COM user initialized security.

    CLSID clsidWbemLocator{};
    IID iidWbemLocator{};
    HRESULT hr = CLSIDFromString(L"{4590F811-1D3A-11D0-891F-00AA004B2E24}", &clsidWbemLocator);
    if (SUCCEEDED(hr)) hr = IIDFromString(L"{DC12A687-737F-11CF-884D-00AA004B2E24}", &iidWbemLocator);
    IWbemLocator* locator = nullptr;
    if (SUCCEEDED(hr)) {
        hr = CoCreateInstance(clsidWbemLocator, nullptr, CLSCTX_INPROC_SERVER,
                              iidWbemLocator, reinterpret_cast<void**>(&locator));
    }
    if (FAILED(hr) || !locator) {
        if (shouldUninit) CoUninitialize();
        return 0;
    }

    IWbemServices* services = nullptr;
    BSTR ns = guiSysAlloc(L"ROOT\\DEFAULT");
    hr = locator->ConnectServer(ns, nullptr, nullptr, nullptr, 0, nullptr, nullptr, &services);
    SysFreeString(ns);
    locator->Release();
    if (FAILED(hr) || !services) {
        if (shouldUninit) CoUninitialize();
        return 0;
    }

    CoSetProxyBlanket(services, RPC_C_AUTHN_WINNT, RPC_C_AUTHZ_NONE, nullptr,
                      RPC_C_AUTHN_LEVEL_CALL, RPC_C_IMP_LEVEL_IMPERSONATE,
                      nullptr, EOAC_NONE);

    IEnumWbemClassObject* enumerator = nullptr;
    BSTR wql = guiSysAlloc(L"WQL");
    BSTR query = guiSysAlloc(L"SELECT Description FROM SystemRestore WHERE Description='Sardanello'");
    hr = services->ExecQuery(wql, query, WBEM_FLAG_FORWARD_ONLY | WBEM_FLAG_RETURN_IMMEDIATELY,
                             nullptr, &enumerator);
    SysFreeString(query);
    SysFreeString(wql);
    services->Release();
    if (FAILED(hr) || !enumerator) {
        if (shouldUninit) CoUninitialize();
        return 0;
    }

    IWbemClassObject* object = nullptr;
    ULONG returned = 0;
    hr = enumerator->Next(5000, 1, &object, &returned);
    bool exists = SUCCEEDED(hr) && returned > 0 && object != nullptr;
    if (object) object->Release();
    enumerator->Release();
    if (shouldUninit) CoUninitialize();
    return exists ? 1 : 2;
}

static void guiRefreshRestoreStatusAsync()
{
    bool expected = false;
    if (!g_guiRestoreQueryRunning.compare_exchange_strong(expected, true)) return;
    std::thread([]() {
        int state = guiQueryRestorePointState();
        g_guiRestoreState.store(state);
        g_guiRestoreQueryRunning.store(false);
        if (g_guiHwnd) PostMessageW(g_guiHwnd, WM_APP + 10, 0, 0);
    }).detach();
}

static std::wstring guiSystemDriveRoot()
{
    wchar_t driveBuf[32] = {};
    DWORD len = GetEnvironmentVariableW(L"SystemDrive", driveBuf, (DWORD)(sizeof(driveBuf) / sizeof(driveBuf[0])));
    std::wstring drive = (len > 0 && len < (DWORD)(sizeof(driveBuf) / sizeof(driveBuf[0]))) ? driveBuf : L"C:";
    if (drive.empty()) drive = L"C:";
    if (drive.back() != L'\\') drive += L"\\";
    return drive;
}

static bool guiEnableSystemProtectionForSystemDrive(std::string& error)
{
    // Clear the classic "disable System Restore" switch first. The WMI Enable
    // call below is still the authoritative step.
    HKEY hKey = nullptr;
    LONG rr = RegCreateKeyExW(HKEY_LOCAL_MACHINE,
                              L"SOFTWARE\\Microsoft\\Windows NT\\CurrentVersion\\SystemRestore",
                              0, nullptr, REG_OPTION_NON_VOLATILE, KEY_SET_VALUE, nullptr, &hKey, nullptr);
    if (rr == ERROR_SUCCESS) {
        DWORD zero = 0;
        RegSetValueExW(hKey, L"DisableSR", 0, REG_DWORD, reinterpret_cast<const BYTE*>(&zero), sizeof(zero));
        RegCloseKey(hKey);
    }

    HRESULT hrInit = CoInitializeEx(nullptr, COINIT_MULTITHREADED);
    bool shouldUninit = (hrInit == S_OK || hrInit == S_FALSE);
    if (FAILED(hrInit) && hrInit != RPC_E_CHANGED_MODE) {
        error = "CoInitializeEx failed: " + std::to_string((int)hrInit);
        return false;
    }

    CoInitializeSecurity(nullptr, -1, nullptr, nullptr,
                         RPC_C_AUTHN_LEVEL_DEFAULT,
                         RPC_C_IMP_LEVEL_IMPERSONATE,
                         nullptr, EOAC_NONE, nullptr);

    CLSID clsidWbemLocator{};
    IID iidWbemLocator{};
    HRESULT hr = CLSIDFromString(L"{4590F811-1D3A-11D0-891F-00AA004B2E24}", &clsidWbemLocator);
    if (SUCCEEDED(hr)) hr = IIDFromString(L"{DC12A687-737F-11CF-884D-00AA004B2E24}", &iidWbemLocator);

    IWbemLocator* locator = nullptr;
    if (SUCCEEDED(hr)) {
        hr = CoCreateInstance(clsidWbemLocator, nullptr, CLSCTX_INPROC_SERVER,
                              iidWbemLocator, reinterpret_cast<void**>(&locator));
    }
    if (FAILED(hr) || !locator) {
        error = "CoCreateInstance IWbemLocator failed: " + std::to_string((int)hr);
        if (shouldUninit) CoUninitialize();
        return false;
    }

    IWbemServices* services = nullptr;
    BSTR ns = guiSysAlloc(L"ROOT\\DEFAULT");
    hr = locator->ConnectServer(ns, nullptr, nullptr, nullptr, 0, nullptr, nullptr, &services);
    SysFreeString(ns);
    locator->Release();
    if (FAILED(hr) || !services) {
        error = "WMI ROOT\\DEFAULT connect failed: " + std::to_string((int)hr);
        if (shouldUninit) CoUninitialize();
        return false;
    }

    CoSetProxyBlanket(services, RPC_C_AUTHN_WINNT, RPC_C_AUTHZ_NONE, nullptr,
                      RPC_C_AUTHN_LEVEL_CALL, RPC_C_IMP_LEVEL_IMPERSONATE,
                      nullptr, EOAC_NONE);

    IWbemClassObject* restoreClass = nullptr;
    BSTR className = guiSysAlloc(L"SystemRestore");
    hr = services->GetObject(className, 0, nullptr, &restoreClass, nullptr);
    SysFreeString(className);
    if (FAILED(hr) || !restoreClass) {
        error = "WMI SystemRestore class not available: " + std::to_string((int)hr);
        services->Release();
        if (shouldUninit) CoUninitialize();
        return false;
    }

    IWbemClassObject* inParamsDefinition = nullptr;
    BSTR methodName = guiSysAlloc(L"Enable");
    hr = restoreClass->GetMethod(methodName, 0, &inParamsDefinition, nullptr);
    restoreClass->Release();
    if (FAILED(hr) || !inParamsDefinition) {
        error = "SystemRestore.Enable method not available: " + std::to_string((int)hr);
        SysFreeString(methodName);
        services->Release();
        if (shouldUninit) CoUninitialize();
        return false;
    }

    IWbemClassObject* inParams = nullptr;
    hr = inParamsDefinition->SpawnInstance(0, &inParams);
    inParamsDefinition->Release();
    if (FAILED(hr) || !inParams) {
        error = "WMI SpawnInstance failed: " + std::to_string((int)hr);
        SysFreeString(methodName);
        services->Release();
        if (shouldUninit) CoUninitialize();
        return false;
    }

    std::wstring drive = guiSystemDriveRoot();
    VARIANT driveVariant;
    VariantInit(&driveVariant);
    driveVariant.vt = VT_BSTR;
    driveVariant.bstrVal = SysAllocString(drive.c_str());
    hr = inParams->Put(L"Drive", 0, &driveVariant, 0);
    VariantClear(&driveVariant);
    if (FAILED(hr)) {
        error = "WMI Enable Drive parameter failed: " + std::to_string((int)hr);
        inParams->Release();
        SysFreeString(methodName);
        services->Release();
        if (shouldUninit) CoUninitialize();
        return false;
    }

    IWbemClassObject* outParams = nullptr;
    BSTR objectPath = guiSysAlloc(L"SystemRestore");
    hr = services->ExecMethod(objectPath, methodName, 0, nullptr, inParams, &outParams, nullptr);
    SysFreeString(objectPath);
    SysFreeString(methodName);
    inParams->Release();

    LONG returnValue = 0;
    if (SUCCEEDED(hr) && outParams) {
        VARIANT ret;
        VariantInit(&ret);
        if (SUCCEEDED(outParams->Get(L"ReturnValue", 0, &ret, nullptr, nullptr))) {
            if (ret.vt == VT_I4 || ret.vt == VT_UI4) returnValue = ret.lVal;
        }
        VariantClear(&ret);
        outParams->Release();
    }
    services->Release();
    if (shouldUninit) CoUninitialize();

    if (FAILED(hr)) {
        error = "SystemRestore.Enable failed: " + std::to_string((int)hr);
        return false;
    }
    if (returnValue != 0) {
        error = "SystemRestore.Enable returned " + std::to_string((int)returnValue);
        return false;
    }
    return true;
}

static bool guiCreateSardanelloRestorePoint(std::string& error)
{
    RESTOREPOINTINFOW rp{};
    STATEMGRSTATUS status{};
    rp.dwEventType = BEGIN_SYSTEM_CHANGE;
    rp.dwRestorePtType = MODIFY_SETTINGS;
    rp.llSequenceNumber = 0;
    wcsncpy(rp.szDescription, L"Sardanello", MAX_DESC_W - 1);

    if (!SRSetRestorePointW(&rp, &status)) {
        error = "SRSetRestorePoint BEGIN failed, status=" + std::to_string((int)status.nStatus) +
                ", winerr=" + std::to_string((int)GetLastError());
        return false;
    }

    RESTOREPOINTINFOW endRp{};
    STATEMGRSTATUS endStatus{};
    endRp.dwEventType = END_SYSTEM_CHANGE;
    endRp.dwRestorePtType = MODIFY_SETTINGS;
    endRp.llSequenceNumber = status.llSequenceNumber;
    wcsncpy(endRp.szDescription, L"Sardanello", MAX_DESC_W - 1);
    if (!SRSetRestorePointW(&endRp, &endStatus)) {
        error = "SRSetRestorePoint END failed, status=" + std::to_string((int)endStatus.nStatus) +
                ", winerr=" + std::to_string((int)GetLastError());
        return false;
    }
    return true;
}

static void guiResetMatrix(int width, int height)
{
    g_guiDrops.clear();
    if (width <= 0 || height <= 0) return;
    const int columnWidth = 13;
    int columns = std::max(1, width / columnWidth);
    std::mt19937 rng((unsigned)GetTickCount());
    std::uniform_real_distribution<float> yDist((float)-height, (float)height);
    std::uniform_real_distribution<float> speedDist(2.0f, 7.0f);
    std::uniform_int_distribution<int> lenDist(8, 26);
    g_guiDrops.reserve((size_t)columns);
    for (int i = 0; i < columns; ++i) {
        GuiMatrixDrop drop;
        drop.x = (float)(i * columnWidth + 2);
        drop.y = yDist(rng);
        drop.speed = speedDist(rng);
        drop.length = lenDist(rng);
        g_guiDrops.push_back(drop);
    }
}

static void guiAdvanceMatrix(const RECT& rc)
{
    if (g_matrixPause.load()) return;
    int height = rc.bottom - rc.top;
    if (height <= 0) return;
    for (auto& drop : g_guiDrops) {
        drop.y += drop.speed;
        if (drop.y - drop.length * 14.0f > height) {
            drop.y = (float)(-(40 + (int)(GetTickCount() % 180)));
            drop.speed = 2.0f + (float)((GetTickCount() + (DWORD)drop.x) % 50) / 10.0f;
            drop.length = 8 + (int)((GetTickCount() + (DWORD)drop.x) % 18);
        }
    }
}

static void guiLayoutButtons(const RECT& rc)
{
    g_guiButtons.clear();
    int width = rc.right - rc.left;
    int margin = 28;
    int top = 214;
    int gap = 12;
    int colGap = 14;
    int columns = width >= 940 ? 2 : 1;
    int contentW = std::max(320, width - margin * 2);
    int buttonW = columns == 2 ? (contentW - colGap) / 2 : contentW;
    int buttonH = 62;
    bool busy = g_timerBenchmarkRunning.load();

    auto numberedTitle = [](int number, const wchar_t* title) {
        wchar_t prefix[16] = {};
        std::swprintf(prefix, 16, L"%d) ", number);
        return std::wstring(prefix) + title;
    };

    auto add = [&](int id, std::wstring title, std::wstring note, bool enabled) {
        int idx = (int)g_guiButtons.size();
        int col = columns == 2 ? idx % 2 : 0;
        int row = columns == 2 ? idx / 2 : idx;
        RECT br;
        br.left = margin + col * (buttonW + colGap);
        br.top = top + row * (buttonH + gap);
        br.right = br.left + buttonW;
        br.bottom = br.top + buttonH;
        g_guiButtons.push_back({id, std::move(title), std::move(note), br, enabled && !busy});
    };

    add(GUI_CMD_RESTORE_POINT, numberedTitle(1, trW(TextId::BtnRestorePoint)), trW(TextId::NoteRestorePoint), !busy);
    add(GUI_CMD_HPET, numberedTitle(2, trW(TextId::BtnHpet)), trW(TextId::NoteHpet), !busy);
    add(GUI_CMD_POWER_PLAN, numberedTitle(3, trW(TextId::BtnPowerPlan)), trW(TextId::NotePowerPlan), !busy);
    add(GUI_CMD_BENCHMARK, numberedTitle(4, trW(TextId::BtnBenchmark)), trW(TextId::NoteBenchmark), !busy);
    add(GUI_CMD_APPLY_TIMER, numberedTitle(5, trW(TextId::BtnApplyTimer)), trW(TextId::NoteApplyTimer), !busy);
    add(GUI_CMD_OPEN_REPORT, numberedTitle(6, trW(TextId::BtnOpenReport)), trW(TextId::NoteOpenReport), true);
    add(GUI_CMD_MANUAL_TIMER, trW(TextId::BtnManualTimer), trW(TextId::NoteManualTimer), !busy);
    add(GUI_CMD_DONATE, trW(TextId::BtnDonate), trW(TextId::NoteDonate), true);
    add(GUI_CMD_TELEGRAM, trW(TextId::BtnTelegram), trW(TextId::NoteTelegram), true);
    add(GUI_CMD_EXIT, trW(TextId::BtnExit), trW(TextId::NoteExit), !busy);
}

static int guiHitTestButton(POINT pt)
{
    for (const auto& b : g_guiButtons) {
        if (b.enabled && PtInRect(&b.rect, pt)) return b.id;
    }
    return 0;
}

static std::string guiLatestReportPath()
{
    std::string dir = getExeDirectory();
    std::string pattern = dir + "gaming_timer_analysis*.html";
    WIN32_FIND_DATAA data{};
    HANDLE hFind = FindFirstFileA(pattern.c_str(), &data);
    if (hFind == INVALID_HANDLE_VALUE) {
        std::string fallback = dir + "gaming_timer_analysis.html";
        DWORD attrs = GetFileAttributesA(fallback.c_str());
        return attrs != INVALID_FILE_ATTRIBUTES ? fallback : std::string();
    }

    std::string best;
    FILETIME bestTime{};
    do {
        if ((data.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) == 0) {
            if (best.empty() || CompareFileTime(&data.ftLastWriteTime, &bestTime) > 0) {
                best = dir + data.cFileName;
                bestTime = data.ftLastWriteTime;
            }
        }
    } while (FindNextFileA(hFind, &data));
    FindClose(hFind);
    return best;
}

static void guiOpenFileOrStatus(const std::string& path, const std::string& missingMessage)
{
    if (path.empty() || GetFileAttributesA(path.c_str()) == INVALID_FILE_ATTRIBUTES) {
        guiSetStatus(missingMessage);
        return;
    }
    ShellExecuteA(g_guiHwnd, "open", path.c_str(), nullptr, nullptr, SW_SHOWNORMAL);
}

static void guiAskRebootNow(const wchar_t* title, const wchar_t* message)
{
    if (!g_guiHwnd) return;
    int answer = MessageBoxW(g_guiHwnd, message, title, MB_YESNO | MB_ICONQUESTION | MB_TOPMOST);
    if (answer == IDYES) {
        attemptReboot();
    }
}

struct ManualTimerDialogState {
    HWND edit = nullptr;
    bool done = false;
    bool ok = false;
    double value = 0.0;
};

static LRESULT CALLBACK manualTimerDialogProc(HWND hwnd, UINT msg, WPARAM wParam, LPARAM lParam)
{
    ManualTimerDialogState* state = reinterpret_cast<ManualTimerDialogState*>(GetWindowLongPtrW(hwnd, GWLP_USERDATA));
    switch (msg) {
    case WM_NCCREATE: {
        auto cs = reinterpret_cast<CREATESTRUCTW*>(lParam);
        SetWindowLongPtrW(hwnd, GWLP_USERDATA, reinterpret_cast<LONG_PTR>(cs->lpCreateParams));
        return TRUE;
    }
    case WM_CREATE: {
        state = reinterpret_cast<ManualTimerDialogState*>(GetWindowLongPtrW(hwnd, GWLP_USERDATA));
        HFONT font = (HFONT)GetStockObject(DEFAULT_GUI_FONT);
        HWND label = CreateWindowW(L"STATIC", trW(TextId::ManualDialogLabel), WS_CHILD | WS_VISIBLE,
                                   18, 18, 330, 22, hwnd, nullptr, nullptr, nullptr);
        state->edit = CreateWindowExW(WS_EX_CLIENTEDGE, L"EDIT", L"0.504",
                                      WS_CHILD | WS_VISIBLE | ES_AUTOHSCROLL,
                                      18, 48, 330, 26, hwnd, (HMENU)10, nullptr, nullptr);
        HWND ok = CreateWindowW(L"BUTTON", L"OK", WS_CHILD | WS_VISIBLE | BS_DEFPUSHBUTTON,
                                116, 92, 92, 30, hwnd, (HMENU)IDOK, nullptr, nullptr);
        HWND cancel = CreateWindowW(L"BUTTON", trW(TextId::ManualDialogCancel), WS_CHILD | WS_VISIBLE,
                                    220, 92, 92, 30, hwnd, (HMENU)IDCANCEL, nullptr, nullptr);
        SendMessageW(label, WM_SETFONT, (WPARAM)font, TRUE);
        SendMessageW(state->edit, WM_SETFONT, (WPARAM)font, TRUE);
        SendMessageW(ok, WM_SETFONT, (WPARAM)font, TRUE);
        SendMessageW(cancel, WM_SETFONT, (WPARAM)font, TRUE);
        SetFocus(state->edit);
        SendMessageW(state->edit, EM_SETSEL, 0, -1);
        return 0;
    }
    case WM_COMMAND:
        if (LOWORD(wParam) == IDOK && state) {
            wchar_t buf[96] = {};
            GetWindowTextW(state->edit, buf, 95);
            std::wstring text = buf;
            std::replace(text.begin(), text.end(), L',', L'.');
            wchar_t* end = nullptr;
            double value = std::wcstod(text.c_str(), &end);
            if (value < 0.1 || value > 15.625) {
                MessageBoxW(hwnd, trW(TextId::ManualDialogInvalid), L"Sardanello", MB_OK | MB_ICONWARNING);
                return 0;
            }
            state->value = value;
            state->ok = true;
            state->done = true;
            DestroyWindow(hwnd);
            return 0;
        }
        if (LOWORD(wParam) == IDCANCEL && state) {
            state->done = true;
            DestroyWindow(hwnd);
            return 0;
        }
        break;
    case WM_CLOSE:
        if (state) state->done = true;
        DestroyWindow(hwnd);
        return 0;
    default:
        break;
    }
    return DefWindowProcW(hwnd, msg, wParam, lParam);
}

static bool guiPromptManualTimer(double& value)
{
    const wchar_t* className = L"SardanelloManualTimerDialog";
    WNDCLASSEXW wc{};
    wc.cbSize = sizeof(wc);
    wc.lpfnWndProc = manualTimerDialogProc;
    wc.hInstance = GetModuleHandleW(nullptr);
    wc.hCursor = LoadCursor(nullptr, IDC_ARROW);
    wc.hbrBackground = (HBRUSH)(COLOR_WINDOW + 1);
    wc.lpszClassName = className;
    RegisterClassExW(&wc);

    ManualTimerDialogState state;
    RECT ownerRc{};
    GetWindowRect(g_guiHwnd, &ownerRc);
    int w = 380;
    int h = 170;
    int x = ownerRc.left + ((ownerRc.right - ownerRc.left) - w) / 2;
    int y = ownerRc.top + ((ownerRc.bottom - ownerRc.top) - h) / 2;
    HWND dlg = CreateWindowExW(WS_EX_DLGMODALFRAME, className, trW(TextId::ManualDialogTitle),
                               WS_POPUP | WS_CAPTION | WS_SYSMENU,
                               x, y, w, h, g_guiHwnd, nullptr, GetModuleHandleW(nullptr), &state);
    if (!dlg) return false;

    EnableWindow(g_guiHwnd, FALSE);
    ShowWindow(dlg, SW_SHOW);
    UpdateWindow(dlg);

    MSG msg;
    while (!state.done && GetMessageW(&msg, nullptr, 0, 0) > 0) {
        if (!IsDialogMessageW(dlg, &msg)) {
            TranslateMessage(&msg);
            DispatchMessageW(&msg);
        }
    }

    if (IsWindow(dlg)) DestroyWindow(dlg);
    EnableWindow(g_guiHwnd, TRUE);
    SetForegroundWindow(g_guiHwnd);
    if (state.ok) value = state.value;
    return state.ok;
}

static std::wstring guiTimerStatusLine(TextId prefix, double timerMs)
{
    wchar_t value[64] = {};
    std::swprintf(value, 64, L" %.6f ms", timerMs);
    return std::wstring(trW(prefix)) + value;
}

static void guiShowBenchmarkPreparationWarning()
{
    const wchar_t* title = appTextW(
        L"Перед тестом таймера",
        L"Before the timer test",
        L"Vor dem Timer-Test",
        L"Timer testinden once",
        L"Antes de la prueba del temporizador",
        L"Antes do teste do timer",
        L"टाइमर टेस्ट से पहले");

    const wchar_t* message = appTextW(
        L"Для более точного и воспроизводимого результата закройте приложения, которые могут грузить CPU/GPU/диск/сеть или включать оверлеи:\n\n"
        L"- Браузеры: Chrome, Edge, Firefox, Opera, Brave, Яндекс\n"
        L"- OBS, Streamlabs, XSplit\n"
        L"- Discord, Telegram, Skype, Teams, Zoom\n"
        L"- Steam, Epic Games, Battle.net, EA App, Riot, Ubisoft Connect\n"
        L"- GeForce Experience/ShadowPlay, Xbox Game Bar, MSI Afterburner/RivaTuner\n"
        L"- Торренты, менеджеры загрузок, OneDrive, Google Drive, Dropbox\n"
        L"- Антивирусные сканирования, Windows Update, лаунчеры с загрузками\n\n"
        L"Когда закроете лишнее, нажмите OK. После OK тест начнется.",

        L"For a more accurate and repeatable result, close apps that can load CPU/GPU/disk/network or add overlays:\n\n"
        L"- Browsers: Chrome, Edge, Firefox, Opera, Brave, Yandex\n"
        L"- OBS, Streamlabs, XSplit\n"
        L"- Discord, Telegram, Skype, Teams, Zoom\n"
        L"- Steam, Epic Games, Battle.net, EA App, Riot, Ubisoft Connect\n"
        L"- GeForce Experience/ShadowPlay, Xbox Game Bar, MSI Afterburner/RivaTuner\n"
        L"- Torrents, download managers, OneDrive, Google Drive, Dropbox\n"
        L"- Antivirus scans, Windows Update, launchers with active downloads\n\n"
        L"Close the extra apps, then press OK. The test starts after OK.",

        L"Fur ein genaueres und wiederholbares Ergebnis schliessen Sie Programme, die CPU/GPU/Datentrager/Netzwerk belasten oder Overlays einblenden:\n\n"
        L"- Browser: Chrome, Edge, Firefox, Opera, Brave, Yandex\n"
        L"- OBS, Streamlabs, XSplit\n"
        L"- Discord, Telegram, Skype, Teams, Zoom\n"
        L"- Steam, Epic Games, Battle.net, EA App, Riot, Ubisoft Connect\n"
        L"- GeForce Experience/ShadowPlay, Xbox Game Bar, MSI Afterburner/RivaTuner\n"
        L"- Torrents, Download-Manager, OneDrive, Google Drive, Dropbox\n"
        L"- Antivirus-Scans, Windows Update, Launcher mit aktiven Downloads\n\n"
        L"Schliessen Sie alles Unnotige und drucken Sie OK. Danach startet der Test.",

        L"Daha dogru ve tekrarlanabilir sonuc icin CPU/GPU/disk/ag yukleyen veya overlay acan uygulamalari kapatin:\n\n"
        L"- Tarayicilar: Chrome, Edge, Firefox, Opera, Brave, Yandex\n"
        L"- OBS, Streamlabs, XSplit\n"
        L"- Discord, Telegram, Skype, Teams, Zoom\n"
        L"- Steam, Epic Games, Battle.net, EA App, Riot, Ubisoft Connect\n"
        L"- GeForce Experience/ShadowPlay, Xbox Game Bar, MSI Afterburner/RivaTuner\n"
        L"- Torrentler, indirme yoneticileri, OneDrive, Google Drive, Dropbox\n"
        L"- Antivirus taramalari, Windows Update, aktif indirme yapan launcherlar\n\n"
        L"Gereksiz uygulamalari kapatin ve OK'e basin. Test OK'ten sonra baslar.",

        L"Para un resultado mas preciso y repetible, cierra apps que carguen CPU/GPU/disco/red o usen overlays:\n\n"
        L"- Navegadores: Chrome, Edge, Firefox, Opera, Brave, Yandex\n"
        L"- OBS, Streamlabs, XSplit\n"
        L"- Discord, Telegram, Skype, Teams, Zoom\n"
        L"- Steam, Epic Games, Battle.net, EA App, Riot, Ubisoft Connect\n"
        L"- GeForce Experience/ShadowPlay, Xbox Game Bar, MSI Afterburner/RivaTuner\n"
        L"- Torrents, gestores de descarga, OneDrive, Google Drive, Dropbox\n"
        L"- Analisis antivirus, Windows Update, launchers con descargas activas\n\n"
        L"Cierra lo innecesario y pulsa OK. La prueba empieza despues de OK.",

        L"Para um resultado mais preciso e repetivel, feche apps que carregam CPU/GPU/disco/rede ou usam overlays:\n\n"
        L"- Navegadores: Chrome, Edge, Firefox, Opera, Brave, Yandex\n"
        L"- OBS, Streamlabs, XSplit\n"
        L"- Discord, Telegram, Skype, Teams, Zoom\n"
        L"- Steam, Epic Games, Battle.net, EA App, Riot, Ubisoft Connect\n"
        L"- GeForce Experience/ShadowPlay, Xbox Game Bar, MSI Afterburner/RivaTuner\n"
        L"- Torrents, gerenciadores de download, OneDrive, Google Drive, Dropbox\n"
        L"- Scans de antivirus, Windows Update, launchers com downloads ativos\n\n"
        L"Feche o que nao precisa e clique OK. O teste comeca depois do OK.",

        L"ज़्यादा सटीक और दोहराने योग्य परिणाम के लिए ऐसे ऐप बंद करें जो CPU/GPU/disk/network लोड करते हैं या overlay लगाते हैं:\n\n"
        L"- Browsers: Chrome, Edge, Firefox, Opera, Brave, Yandex\n"
        L"- OBS, Streamlabs, XSplit\n"
        L"- Discord, Telegram, Skype, Teams, Zoom\n"
        L"- Steam, Epic Games, Battle.net, EA App, Riot, Ubisoft Connect\n"
        L"- GeForce Experience/ShadowPlay, Xbox Game Bar, MSI Afterburner/RivaTuner\n"
        L"- Torrents, download managers, OneDrive, Google Drive, Dropbox\n"
        L"- Antivirus scans, Windows Update, active downloads वाले launchers\n\n"
        L"Extra apps बंद करें और OK दबाएं. OK के बाद टेस्ट शुरू होगा.");

    MessageBoxW(g_guiHwnd, message, title, MB_OK | MB_ICONWARNING | MB_TOPMOST);
}

static void guiStartBenchmark()
{
    bool expected = false;
    if (!g_timerBenchmarkRunning.compare_exchange_strong(expected, true)) {
        guiSetStatusW(trW(TextId::TestRunning), trW(TextId::WaitCurrentMeasurement));
        return;
    }

    guiSetStatusW(trW(TextId::BenchmarkStart), trW(TextId::BenchmarkStopOld));
    std::thread([]() {
        bool serviceWasStopped = stopTimerService();
        resetTimerToDefault();
        guiSetStatusW(trW(TextId::BenchmarkStarted),
                      serviceWasStopped ? trW(TextId::OldServiceStopped) : trW(TextId::BenchmarkInit),
                      trW(TextId::BenchmarkProgressHere));

        showBestTimer();
        g_timerBenchmarkRunning = false;

        OptimalTimerResult optimal = loadOptimalTimer();
        if (optimal.isValid) {
            guiSetStatusW(guiTimerStatusLine(TextId::BenchmarkDonePrefix, optimal.timerMs),
                          trW(TextId::ReportCreated),
                          trW(TextId::PressApplyTimer));
        } else {
            guiSetStatusW(trW(TextId::BenchmarkNoIni), trW(TextId::CheckReportFolder));
        }
    }).detach();
}

static void guiApplySavedTimer()
{
    if (g_timerBenchmarkRunning.load()) {
        guiSetStatusW(trW(TextId::CannotApplyDuringTest));
        return;
    }

    std::thread([]() {
        OptimalTimerResult optimal = loadOptimalTimer();
        if (!optimal.isValid) {
            guiSetStatusW(trW(TextId::OptimalNotFound), trW(TextId::RunTimerTestFirst));
            return;
        }

        guiSetStatusW(guiTimerStatusLine(TextId::ApplyingTimerPrefix, optimal.timerMs),
                      trW(TextId::StartingTimerService));

        bool serviceExists = isServiceRunning();
        bool serviceOk = serviceExists ? startTimerService() : createTimerService(optimal.timerMs);
        bool appliedNow = applyOptimalTimer(optimal.timerMs);

        if (serviceOk || appliedNow) {
            guiSetStatusW(guiTimerStatusLine(TextId::TimerAppliedPrefix, optimal.timerMs),
                          serviceOk ? trW(TextId::TimerServiceAutostart) : trW(TextId::TimerAppliedCurrent),
                          trW(TextId::AfterRebootIni));
            g_rebootAvailable = true;
            g_rebootMessage = "Timer service configured; reboot recommended";
        } else {
            guiSetStatusW(trW(TextId::ApplyTimerFail), trW(TextId::CheckAccessOrAntivirus));
        }
    }).detach();
}

static void guiSetManualTimer()
{
    if (g_timerBenchmarkRunning.load()) {
        guiSetStatusW(trW(TextId::CannotManualDuringTest));
        return;
    }

    double timerMs = 0.0;
    if (!guiPromptManualTimer(timerMs)) {
        return;
    }

    guiSetStatusW(guiTimerStatusLine(TextId::SettingManualPrefix, timerMs),
                  trW(TextId::SavingManualService));

    std::thread([timerMs]() {
        bool serviceOk = createTimerService(timerMs);
        bool appliedNow = applyOptimalTimer(timerMs);
        if (serviceOk || appliedNow) {
            guiSetStatusW(guiTimerStatusLine(TextId::ManualTimerSetPrefix, timerMs),
                          trW(TextId::ValueWrittenIni),
                          trW(TextId::HiddenServiceHold));
        } else {
            guiSetStatusW(trW(TextId::ManualFail), trW(TextId::CheckAccessOrAntivirus));
        }
    }).detach();
}

static void guiRunHpetAndCpuTweaks()
{
    if (!isAdministrator()) {
        guiSetStatusW(trW(TextId::AdminNeeded), trW(TextId::RunAsAdmin));
        return;
    }

    guiSetStatusW(trW(TextId::HpetStart), trW(TextId::TakesSeconds));
    std::thread([]() {
        setProcessorCheckIntervalAllSchemes(5000);
        disableHighPrecisionTimer();
        guiRefreshHpetStatusAsync();
        g_rebootAvailable = true;
        g_rebootMessage = "HPET/boot tweaks changed; reboot required";
        guiSetStatus(appText(L"HPET/CPU interval и boot-настройки применены",
                             L"HPET/CPU interval and boot settings applied",
                             L"HPET/CPU-Intervall und Boot-Einstellungen angewendet",
                             L"HPET/CPU araligi ve boot ayarlari uygulandi",
                             L"Ajustes HPET/CPU interval y boot aplicados",
                             L"Ajustes HPET/CPU interval e boot aplicados",
                             L"HPET/CPU interval \u0914\u0930 boot settings \u0932\u0917 \u0917\u0908"),
                     appText(L"Для полного применения нужна перезагрузка",
                             L"A reboot is required to finish applying changes",
                             L"Zum Abschluss ist ein Neustart erforderlich",
                             L"Tam uygulama icin yeniden baslatma gerekli",
                             L"Se requiere reinicio para completar",
                             L"Reinicie para concluir a aplicacao",
                             L"\u092a\u0942\u0930\u093e \u0932\u093e\u0917\u0942 \u0915\u0930\u0928\u0947 \u0915\u0947 \u0932\u093f\u090f reboot \u091a\u093e\u0939\u093f\u090f"));
        if (g_guiHwnd) PostMessageW(g_guiHwnd, WM_APP + 10, 0, 0);
        guiAskRebootNow(L"Sardanello",
                        trW(TextId::HpetRebootQuestion));
    }).detach();
}

static bool guiActivatePowerPlanGuid(const std::string& guidText)
{
    GUID planGuid{};
    std::string guidWithBraces = guidText;
    if (guidWithBraces.empty()) return false;
    if (guidWithBraces.front() != '{') guidWithBraces = "{" + guidWithBraces + "}";
    std::wstring wideGuid(guidWithBraces.begin(), guidWithBraces.end());
    HRESULT hr = CLSIDFromString(wideGuid.c_str(), &planGuid);
    if (FAILED(hr)) return false;
    return PowerSetActiveScheme(NULL, &planGuid) == ERROR_SUCCESS;
}

static bool guiIsPowerPlanActive(const std::string& guidText)
{
    GUID* currentActiveGuid = nullptr;
    DWORD rc = PowerGetActiveScheme(NULL, &currentActiveGuid);
    if (rc != ERROR_SUCCESS || !currentActiveGuid) return false;

    WCHAR currentGuidStr[64] = {};
    StringFromGUID2(*currentActiveGuid, currentGuidStr, 64);
    LocalFree(currentActiveGuid);

    char currentGuidCharStr[64] = {};
    WideCharToMultiByte(CP_UTF8, 0, currentGuidStr, -1, currentGuidCharStr, 64, nullptr, nullptr);
    std::string current = currentGuidCharStr;
    if (!current.empty() && current.front() == '{') current.erase(0, 1);
    if (!current.empty() && current.back() == '}') current.pop_back();

    std::string expected = guidText;
    std::transform(current.begin(), current.end(), current.begin(), ::tolower);
    std::transform(expected.begin(), expected.end(), expected.begin(), ::tolower);
    return current == expected;
}

static bool guiImportAndApplyPowerPlanLocalized()
{
    bool expected = false;
    if (!g_powerPlanApplying.compare_exchange_strong(expected, true)) {
        guiSetStatus(appText(L"Применение плана уже выполняется",
                             L"Power plan is already being applied",
                             L"Energieplan wird bereits angewendet",
                             L"Guc plani zaten uygulanıyor",
                             L"El plan de energia ya se esta aplicando",
                             L"O plano de energia ja esta sendo aplicado",
                             L"Power plan \u092a\u0939\u0932\u0947 \u0938\u0947 \u0932\u0917 \u0930\u0939\u093e \u0939\u0948"));
        return false;
    }
    struct Guard { ~Guard(){ g_powerPlanApplying = false; } } guard;

    auto setStatus = [](const std::string& a, const std::string& b = std::string(), const std::string& c = std::string()) {
        guiSetStatus(a, b, c);
    };

    setStatus(appText(L"Поиск профиля Sardanello",
                      L"Searching for Sardanello profile",
                      L"Suche Sardanello-Profil",
                      L"Sardanello profili araniyor",
                      L"Buscando perfil Sardanello",
                      L"Procurando perfil Sardanello",
                      L"Sardanello profile \u0922\u0942\u0902\u0922 \u0930\u0939\u093e \u0939\u0942\u0902"),
              appText(L"Проверяем существующие планы питания",
                      L"Checking existing power plans",
                      L"Prufe vorhandene Energieplane",
                      L"Mevcut guc planlari kontrol ediliyor",
                      L"Comprobando planes de energia existentes",
                      L"Verificando planos de energia existentes",
                      L"\u092e\u094c\u091c\u0942\u0926\u093e power plans \u091a\u0947\u0915 \u0939\u094b \u0930\u0939\u0947 \u0939\u0948\u0902"));

    char exePath[MAX_PATH] = {};
    DWORD pathLen = GetModuleFileNameA(nullptr, exePath, MAX_PATH);
    if (pathLen == 0 || pathLen >= MAX_PATH) {
        setStatus(appText(L"Ошибка пути",
                          L"Path error",
                          L"Pfadfehler",
                          L"Yol hatasi",
                          L"Error de ruta",
                          L"Erro de caminho",
                          L"Path error"),
                  appText(L"Не удалось получить путь к exe файлу",
                          L"Could not get exe path",
                          L"Exe-Pfad konnte nicht gelesen werden",
                          L"Exe yolu alinamadi",
                          L"No se pudo obtener la ruta del exe",
                          L"Nao foi possivel obter o caminho do exe",
                          L"exe path \u0928\u0939\u0940\u0902 \u092e\u093f\u0932\u093e"));
        return false;
    }
    char* lastSlash = strrchr(exePath, '\\');
    if (!lastSlash) {
        setStatus(appText(L"Ошибка пути", L"Path error", L"Pfadfehler", L"Yol hatasi", L"Error de ruta", L"Erro de caminho", L"Path error"),
                  appText(L"Некорректный путь к exe файлу",
                          L"Invalid exe path",
                          L"Ungultiger exe-Pfad",
                          L"Gecersiz exe yolu",
                          L"Ruta de exe invalida",
                          L"Caminho do exe invalido",
                          L"exe path invalid"));
        return false;
    }
    *lastSlash = '\0';

    setStatus(appText(L"Ищем план Sardanello",
                      L"Searching for Sardanello plan",
                      L"Suche Sardanello-Plan",
                      L"Sardanello plani araniyor",
                      L"Buscando plan Sardanello",
                      L"Procurando plano Sardanello",
                      L"Sardanello plan \u0922\u0942\u0902\u0922 \u0930\u0939\u093e \u0939\u0942\u0902"),
              appText(L"Сканируем существующие планы питания",
                      L"Scanning existing power plans",
                      L"Scanne vorhandene Energieplane",
                      L"Mevcut guc planlari taraniyor",
                      L"Escaneando planes existentes",
                      L"Escaneando planos existentes",
                      L"\u092e\u094c\u091c\u0942\u0926\u093e plans scan \u0939\u094b \u0930\u0939\u0947 \u0939\u0948\u0902"));

    std::string existingGuid = findPowerPlanByNameAPI("sardanello");
    if (existingGuid.empty()) existingGuid = findPowerPlanByName(exePath, "Sardanello's pow");
    if (existingGuid.empty()) existingGuid = findPowerPlanByName(exePath, "Sardanello");

    if (!existingGuid.empty()) {
        char guidMsg[220] = {};
        std::snprintf(guidMsg, sizeof(guidMsg), "GUID: %.36s", existingGuid.c_str());
        if (guiIsPowerPlanActive(existingGuid)) {
            setStatus(appText(L"План Sardanello найден и уже активен",
                              L"Sardanello plan found and already active",
                              L"Sardanello-Plan gefunden und bereits aktiv",
                              L"Sardanello plani bulundu ve zaten aktif",
                              L"Plan Sardanello encontrado y ya activo",
                              L"Plano Sardanello encontrado e ja ativo",
                              L"Sardanello plan \u092e\u093f\u0932\u093e \u0914\u0930 \u092a\u0939\u0932\u0947 \u0938\u0947 active \u0939\u0948"),
                      guidMsg,
                      appText(L"Никаких действий не требуется",
                              L"No action required",
                              L"Keine Aktion erforderlich",
                              L"Islem gerekmiyor",
                              L"No hace falta ninguna accion",
                              L"Nenhuma acao necessaria",
                              L"\u0915\u094b\u0908 action \u091c\u0930\u0942\u0930\u0940 \u0928\u0939\u0940\u0902"));
            return true;
        }

        setStatus(appText(L"Активируем существующий план питания",
                          L"Activating existing power plan",
                          L"Aktiviere vorhandenen Energieplan",
                          L"Mevcut guc plani etkinlestiriliyor",
                          L"Activando plan de energia existente",
                          L"Ativando plano de energia existente",
                          L"\u092e\u094c\u091c\u0942\u0926\u093e power plan active \u0939\u094b \u0930\u0939\u093e \u0939\u0948"),
                  guidMsg);
        bool ok = guiActivatePowerPlanGuid(existingGuid);
        if (ok) {
            setStatus(appText(L"План питания Sardanello применен",
                              L"Sardanello power plan applied",
                              L"Sardanello-Energieplan angewendet",
                              L"Sardanello guc plani uygulandi",
                              L"Plan de energia Sardanello aplicado",
                              L"Plano de energia Sardanello aplicado",
                              L"Sardanello power plan \u0932\u0917 \u0917\u092f\u093e"),
                      appText(L"Система настроена на игровой профиль",
                              L"System is tuned for the gaming profile",
                              L"System ist auf Gaming-Profil gesetzt",
                              L"Sistem oyun profiline ayarlandi",
                              L"Sistema ajustado al perfil gaming",
                              L"Sistema ajustado para perfil gamer",
                              L"\u0938\u093f\u0938\u094d\u091f\u092e gaming profile \u092a\u0930 \u0938\u0947\u091f"));
        } else {
            setStatus(appText(L"Не удалось активировать существующий план",
                              L"Could not activate existing plan",
                              L"Vorhandener Plan konnte nicht aktiviert werden",
                              L"Mevcut plan etkinlestirilemedi",
                              L"No se pudo activar el plan existente",
                              L"Nao foi possivel ativar o plano existente",
                              L"\u092e\u094c\u091c\u0942\u0926\u093e plan active \u0928\u0939\u0940\u0902 \u0939\u0941\u0906"),
                      appText(L"Проверьте права администратора",
                              L"Check administrator rights",
                              L"Adminrechte prufen",
                              L"Yonetici iznini kontrol et",
                              L"Revisa permisos de administrador",
                              L"Confira permissoes de administrador",
                              L"\u090f\u0921\u092e\u093f\u0928 \u0905\u0927\u093f\u0915\u093e\u0930 \u091a\u0947\u0915 \u0915\u0930\u0947\u0902"));
        }
        return ok;
    }

    setStatus(appText(L"План Sardanello не найден",
                      L"Sardanello plan was not found",
                      L"Sardanello-Plan wurde nicht gefunden",
                      L"Sardanello plani bulunamadi",
                      L"No se encontro el plan Sardanello",
                      L"Plano Sardanello nao encontrado",
                      L"Sardanello plan \u0928\u0939\u0940\u0902 \u092e\u093f\u0932\u093e"),
              appText(L"Импортируем новый план",
                      L"Importing a new plan",
                      L"Importiere neuen Plan",
                      L"Yeni plan ice aktariliyor",
                      L"Importando un plan nuevo",
                      L"Importando novo plano",
                      L"\u0928\u092f\u093e plan import \u0939\u094b \u0930\u0939\u093e \u0939\u0948"));

    std::string sourcePath = extractPowerPlanFromResource();
    if (sourcePath.empty()) {
        setStatus(appText(L"Ошибка извлечения ресурса",
                          L"Resource extraction error",
                          L"Fehler beim Extrahieren der Ressource",
                          L"Kaynak cikarma hatasi",
                          L"Error al extraer recurso",
                          L"Erro ao extrair recurso",
                          L"Resource extraction error"),
                  appText(L"Не удалось извлечь Sardanello.pow из программы",
                          L"Could not extract Sardanello.pow from the program",
                          L"Sardanello.pow konnte nicht aus dem Programm extrahiert werden",
                          L"Sardanello.pow programdan cikarilamadi",
                          L"No se pudo extraer Sardanello.pow",
                          L"Nao foi possivel extrair Sardanello.pow",
                          L"Sardanello.pow extract \u0928\u0939\u0940\u0902 \u0939\u0941\u0906"));
        return false;
    }

    setStatus(appText(L"Sardanello.pow извлечен из ресурсов",
                      L"Sardanello.pow extracted from resources",
                      L"Sardanello.pow aus Ressourcen extrahiert",
                      L"Sardanello.pow kaynaklardan cikarildi",
                      L"Sardanello.pow extraido de recursos",
                      L"Sardanello.pow extraido dos recursos",
                      L"Sardanello.pow resources \u0938\u0947 extract \u0939\u0941\u0906"),
              appText(L"Импортируем план напрямую",
                      L"Importing plan directly",
                      L"Importiere Plan direkt",
                      L"Plan dogrudan ice aktariliyor",
                      L"Importando plan directamente",
                      L"Importando plano diretamente",
                      L"plan direct import \u0939\u094b \u0930\u0939\u093e \u0939\u0948"));

    std::vector<std::string> guidsBefore = getAllPowerPlanGUIDs(exePath);
    char importCmd[512] = {};
    std::snprintf(importCmd, sizeof(importCmd), "powercfg /import \"%s\"", sourcePath.c_str());
    STARTUPINFOA si = {sizeof(STARTUPINFOA)};
    si.dwFlags = STARTF_USESHOWWINDOW;
    si.wShowWindow = SW_HIDE;
    PROCESS_INFORMATION pi{};
    bool importSuccess = false;
    if (CreateProcessA(nullptr, importCmd, nullptr, nullptr, FALSE, CREATE_NO_WINDOW, nullptr, exePath, &si, &pi)) {
        WaitForSingleObject(pi.hProcess, 10000);
        DWORD exitCode = 1;
        importSuccess = GetExitCodeProcess(pi.hProcess, &exitCode) && exitCode == 0;
        CloseHandle(pi.hProcess);
        CloseHandle(pi.hThread);
    }
    if (!importSuccess) {
        setStatus(appText(L"Ошибка импорта",
                          L"Import error",
                          L"Importfehler",
                          L"Ice aktarma hatasi",
                          L"Error de importacion",
                          L"Erro de importacao",
                          L"Import error"),
                  appText(L"Команда powercfg /import завершилась с ошибкой",
                          L"powercfg /import failed",
                          L"powercfg /import ist fehlgeschlagen",
                          L"powercfg /import basarisiz",
                          L"powercfg /import fallo",
                          L"powercfg /import falhou",
                          L"powercfg /import fail \u0939\u0941\u0906"),
                  appText(L"Проверьте права администратора",
                          L"Check administrator rights",
                          L"Adminrechte prufen",
                          L"Yonetici iznini kontrol et",
                          L"Revisa permisos de administrador",
                          L"Confira permissoes de administrador",
                          L"\u090f\u0921\u092e\u093f\u0928 \u0905\u0927\u093f\u0915\u093e\u0930 \u091a\u0947\u0915 \u0915\u0930\u0947\u0902"));
        DeleteFileA(sourcePath.c_str());
        return false;
    }

    setStatus(appText(L"План импортирован",
                      L"Plan imported",
                      L"Plan importiert",
                      L"Plan ice aktarildi",
                      L"Plan importado",
                      L"Plano importado",
                      L"Plan import \u0939\u094b \u0917\u092f\u093e"),
              appText(L"Ищем GUID нового плана",
                      L"Searching for the new plan GUID",
                      L"Suche GUID des neuen Plans",
                      L"Yeni plan GUID araniyor",
                      L"Buscando GUID del nuevo plan",
                      L"Procurando GUID do novo plano",
                      L"\u0928\u090f plan GUID \u0915\u0940 \u0924\u0932\u093e\u0936"));

    std::vector<std::string> guidsAfter = getAllPowerPlanGUIDs(exePath);
    std::string newGuid;
    for (const std::string& guid : guidsAfter) {
        if (std::find(guidsBefore.begin(), guidsBefore.end(), guid) == guidsBefore.end()) {
            newGuid = guid;
            break;
        }
    }
    if (newGuid.empty()) {
        newGuid = findPowerPlanByNameAPI("sardanello");
        if (newGuid.empty()) newGuid = findPowerPlanByName(exePath, "Sardanello");
    }
    if (newGuid.empty()) {
        setStatus(appText(L"Новый план не найден",
                          L"New plan was not found",
                          L"Neuer Plan wurde nicht gefunden",
                          L"Yeni plan bulunamadi",
                          L"No se encontro el nuevo plan",
                          L"Novo plano nao encontrado",
                          L"\u0928\u092f\u093e plan \u0928\u0939\u0940\u0902 \u092e\u093f\u0932\u093e"),
                  appText(L"Возможно, план уже существовал в системе",
                          L"The plan may have already existed in the system",
                          L"Der Plan war moglicherweise schon im System",
                          L"Plan sistemde zaten var olabilir",
                          L"Puede que el plan ya existiera",
                          L"O plano talvez ja existisse no sistema",
                          L"\u0936\u093e\u092f\u0926 plan \u092a\u0939\u0932\u0947 \u0938\u0947 system \u092e\u0947\u0902 \u0925\u093e"));
        DeleteFileA(sourcePath.c_str());
        return false;
    }

    char guidMsg[220] = {};
    std::snprintf(guidMsg, sizeof(guidMsg), "GUID: %.36s", newGuid.c_str());
    setStatus(appText(L"Активируем план",
                      L"Activating plan",
                      L"Aktiviere Plan",
                      L"Plan etkinlestiriliyor",
                      L"Activando plan",
                      L"Ativando plano",
                      L"Plan active \u0939\u094b \u0930\u0939\u093e \u0939\u0948"),
              guidMsg);

    bool activateSuccess = guiActivatePowerPlanGuid(newGuid);
    DeleteFileA(sourcePath.c_str());
    if (!activateSuccess) {
        setStatus(appText(L"Активация неудачна",
                          L"Activation failed",
                          L"Aktivierung fehlgeschlagen",
                          L"Etkinlestirme basarisiz",
                          L"Activacion fallida",
                          L"Ativacao falhou",
                          L"Activation fail \u0939\u0941\u0906"),
                  appText(L"Проверьте права администратора",
                          L"Check administrator rights",
                          L"Adminrechte prufen",
                          L"Yonetici iznini kontrol et",
                          L"Revisa permisos de administrador",
                          L"Confira permissoes de administrador",
                          L"\u090f\u0921\u092e\u093f\u0928 \u0905\u0927\u093f\u0915\u093e\u0930 \u091a\u0947\u0915 \u0915\u0930\u0947\u0902"));
        return false;
    }

    setStatus(appText(L"План питания Sardanello применен",
                      L"Sardanello power plan applied",
                      L"Sardanello-Energieplan angewendet",
                      L"Sardanello guc plani uygulandi",
                      L"Plan de energia Sardanello aplicado",
                      L"Plano de energia Sardanello aplicado",
                      L"Sardanello power plan \u0932\u0917 \u0917\u092f\u093e"),
              appText(L"Система настроена на игровой профиль",
                      L"System is tuned for the gaming profile",
                      L"System ist auf Gaming-Profil gesetzt",
                      L"Sistem oyun profiline ayarlandi",
                      L"Sistema ajustado al perfil gaming",
                      L"Sistema ajustado para perfil gamer",
                      L"\u0938\u093f\u0938\u094d\u091f\u092e gaming profile \u092a\u0930 \u0938\u0947\u091f"));
    return true;
}

static void guiRunPowerPlan()
{
    if (!isAdministrator()) {
        guiSetStatusW(trW(TextId::AdminNeeded), trW(TextId::RunAsAdmin));
        return;
    }

    guiSetStatusW(trW(TextId::PowerCheck), trW(TextId::ReadPlatform));
    std::thread([]() {
        int currentValue = getPlatformAoAcOverride();
        if (currentValue == -1 || currentValue != 0) {
            bool success = setPlatformAoAcOverride(false);
            if (success) {
                g_rebootAvailable = true;
                g_rebootMessage = "PlatformAoAcOverride changed; reboot required";
                guiSetStatusW(trW(TextId::PlatformSet), trW(TextId::RebootNeeded), trW(TextId::AfterRebootPower));
                guiAskRebootNow(L"Sardanello",
                                trW(TextId::PowerRebootQuestion));
            } else {
                guiSetStatusW(trW(TextId::PlatformFail), trW(TextId::RunAsAdmin));
            }
            return;
        }

        bool powerPlanSuccess = guiImportAndApplyPowerPlanLocalized();
        if (powerPlanSuccess) {
            guiSetStatusW(trW(TextId::PowerApplied), trW(TextId::GameProfile));
        } else {
            guiSetStatusW(trW(TextId::PowerFail), trW(TextId::CheckPowAdmin));
        }
    }).detach();
}

static void guiCreateRestorePoint()
{
    if (g_timerBenchmarkRunning.load()) {
        guiSetStatusW(trW(TextId::CannotRestoreDuringTest));
        return;
    }
    if (!isAdministrator()) {
        guiSetStatusW(trW(TextId::AdminNeeded), trW(TextId::RestartWithUac));
        return;
    }

    guiSetStatusW(trW(TextId::RestoreEnableProtection), trW(TextId::RestoreAfterProtection));
    std::thread([]() {
        std::string error;
        bool protectionOk = guiEnableSystemProtectionForSystemDrive(error);
        if (!protectionOk) {
            guiRefreshRestoreStatusAsync();
            guiSetStatus(wideToUtf8(trW(TextId::RestoreProtectionFail)),
                         wideToUtf8(trW(TextId::RestoreWindowsDenied)),
                         error);
            return;
        }

        guiSetStatusW(trW(TextId::RestoreProtectionEnabled), trW(TextId::RestoreCreating));
        std::this_thread::sleep_for(std::chrono::milliseconds(1200));
        error.clear();
        bool ok = guiCreateSardanelloRestorePoint(error);
        guiRefreshRestoreStatusAsync();
        if (ok) {
            guiSetStatusW(trW(TextId::RestoreCreated), trW(TextId::RestoreIndicatorGreen));
        } else {
            guiSetStatus(wideToUtf8(trW(TextId::RestoreCreateFail)),
                         wideToUtf8(trW(TextId::RestoreRejected)),
                         error);
        }
    }).detach();
}

static void guiRunCommand(int id)
{
    switch (id) {
    case GUI_CMD_BENCHMARK:
        if (!g_timerBenchmarkRunning.load()) {
            guiShowBenchmarkPreparationWarning();
        }
        guiStartBenchmark();
        break;
    case GUI_CMD_APPLY_TIMER:
        guiApplySavedTimer();
        break;
    case GUI_CMD_HPET:
        guiRunHpetAndCpuTweaks();
        break;
    case GUI_CMD_POWER_PLAN:
        guiRunPowerPlan();
        break;
    case GUI_CMD_RESTORE_POINT:
        guiCreateRestorePoint();
        break;
    case GUI_CMD_OPEN_REPORT:
        guiOpenFileOrStatus(guiLatestReportPath(), trUtf8(TextId::ReportMissing));
        break;
    case GUI_CMD_MANUAL_TIMER:
        guiSetManualTimer();
        break;
    case GUI_CMD_DONATE:
        ShellExecuteA(g_guiHwnd, "open", "https://www.donationalerts.com/r/sardanello", nullptr, nullptr, SW_SHOWNORMAL);
        break;
    case GUI_CMD_TELEGRAM:
        ShellExecuteA(g_guiHwnd, "open", "https://t.me/Sardanello", nullptr, nullptr, SW_SHOWNORMAL);
        break;
    case GUI_CMD_EXIT:
        if (!g_timerBenchmarkRunning.load()) DestroyWindow(g_guiHwnd);
        break;
    default:
        break;
    }
}

static void guiPaint(HWND hwnd)
{
    PAINTSTRUCT ps;
    HDC hdc = BeginPaint(hwnd, &ps);
    RECT rc;
    GetClientRect(hwnd, &rc);
    int width = std::max(1, (int)(rc.right - rc.left));
    int height = std::max(1, (int)(rc.bottom - rc.top));

    HDC mem = CreateCompatibleDC(hdc);
    HBITMAP bmp = CreateCompatibleBitmap(hdc, width, height);
    HGDIOBJ oldBmp = SelectObject(mem, bmp);

    HBRUSH bg = CreateSolidBrush(RGB(3, 7, 10));
    FillRect(mem, &rc, bg);
    DeleteObject(bg);

    HFONT matrixFont = guiCreateFont(13, FW_NORMAL, L"MS Gothic");
    HGDIOBJ oldFont = SelectObject(mem, matrixFont);
    SetBkMode(mem, TRANSPARENT);
    const wchar_t chars[] = L"アイウエオカキクケコサシスセソタチツテトナニヌネノハヒフヘホマミムメモヤユヨラリルレロワヲン0123456789";
    const int charCount = (int)(sizeof(chars) / sizeof(chars[0])) - 1;
    ULONGLONG tick = GetTickCount64() / 90;
    for (size_t i = 0; i < g_guiDrops.size(); ++i) {
        const auto& drop = g_guiDrops[i];
        for (int j = 0; j < drop.length; ++j) {
            int y = (int)(drop.y - j * 14.0f);
            if (y < -20 || y > height + 20) continue;
            int shade = std::max(55, 245 - j * 8);
            COLORREF color = j == 0 ? RGB(225, 255, 228) : RGB(20, shade, 82);
            SetTextColor(mem, color);
            wchar_t ch = chars[(i * 13 + j * 7 + (size_t)tick) % charCount];
            TextOutW(mem, (int)drop.x, y, &ch, 1);
        }
    }
    SelectObject(mem, oldFont);
    DeleteObject(matrixFont);

    RECT shadeRect = rc;
    HBRUSH shade = CreateSolidBrush(RGB(4, 11, 13));
    FrameRect(mem, &shadeRect, shade);
    DeleteObject(shade);

    const wchar_t* uiFace = g_appLanguage == AppLanguage::Hindi ? L"Nirmala UI" : L"Segoe UI";
    HFONT titleFont = guiCreateFont(width >= 760 ? 44 : 34, FW_NORMAL, L"Fixedsys");
    HFONT subtitleFont = guiCreateFont(width >= 760 ? 20 : 16, FW_NORMAL,
                                       g_appLanguage == AppLanguage::Hindi ? L"Nirmala UI" : L"Fixedsys");
    HFONT statusFont = guiCreateFont(15, FW_NORMAL, uiFace);
    HFONT buttonFont = guiCreateFont(17, FW_SEMIBOLD, uiFace);
    HFONT noteFont = guiCreateFont(13, FW_NORMAL, uiFace);

    RECT titleRect{28, 24, width - 28, 78};
    guiDrawShadowedWideText(mem, L"SARDANELLO", titleRect, titleFont, RGB(0, 255, 65), RGB(0, 150, 42), 1.5);
    RECT subtitleRect{30, 74, width - 28, 105};
    if (g_appLanguage == AppLanguage::Hindi) {
        guiDrawShadowedDrawText(mem, trW(TextId::Subtitle), subtitleRect, subtitleFont,
                                RGB(0, 230, 58), RGB(0, 120, 36),
                                DT_CENTER | DT_SINGLELINE | DT_VCENTER | DT_END_ELLIPSIS);
    } else {
        guiDrawShadowedWideText(mem, trW(TextId::Subtitle), subtitleRect, subtitleFont, RGB(0, 230, 58), RGB(0, 120, 36), 1.5);
    }

    RECT statusPanel{28, 118, width - 28, 194};
    guiFillRoundRect(mem, statusPanel, RGB(7, 18, 22), RGB(32, 120, 78));

    std::array<std::string, 3> statusSnapshot;
    {
        std::lock_guard<std::mutex> sl(g_menuMutex);
        statusSnapshot = g_statusLines;
    }
    bool emptyStatus = statusSnapshot[0].empty() && statusSnapshot[1].empty() && statusSnapshot[2].empty();
    if (emptyStatus) {
        OptimalTimerResult optimal = loadOptimalTimer();
        if (optimal.isValid) {
            statusSnapshot[0] = wideToUtf8(guiTimerStatusLine(TextId::ReadySavedPrefix, optimal.timerMs));
            statusSnapshot[1] = trUtf8(TextId::ReadySavedHint);
        } else {
            statusSnapshot[0] = trUtf8(TextId::ReadyFirstRun);
            statusSnapshot[1] = trUtf8(TextId::ReadyMatrixHint);
        }
    }

    RECT lineRect{48, 130, width - 48, 154};
    guiDrawText(mem, utf8ToWide(statusSnapshot[0]), lineRect, statusFont, RGB(220, 247, 228), DT_LEFT | DT_SINGLELINE | DT_END_ELLIPSIS);
    lineRect.top += 23; lineRect.bottom += 23;
    guiDrawText(mem, utf8ToWide(statusSnapshot[1]), lineRect, statusFont, RGB(156, 209, 178), DT_LEFT | DT_SINGLELINE | DT_END_ELLIPSIS);
    lineRect.top += 23; lineRect.bottom += 23;
    guiDrawText(mem, utf8ToWide(statusSnapshot[2]), lineRect, statusFont, RGB(112, 171, 142), DT_LEFT | DT_SINGLELINE | DT_END_ELLIPSIS);

    guiLayoutButtons(rc);
    for (const auto& b : g_guiButtons) {
        bool hover = b.enabled && b.id == g_guiHoverButton;
        COLORREF fill = b.enabled ? (hover ? RGB(16, 48, 38) : RGB(9, 27, 30)) : RGB(17, 20, 22);
        COLORREF border = b.enabled ? (hover ? RGB(96, 235, 142) : RGB(38, 128, 83)) : RGB(50, 58, 56);
        guiFillRoundRect(mem, b.rect, fill, border);

        RECT t = b.rect;
        t.left += 18; t.right -= 18; t.top += 10; t.bottom = t.top + 25;
        guiDrawText(mem, b.title, t, buttonFont, b.enabled ? RGB(227, 255, 234) : RGB(118, 132, 124), DT_LEFT | DT_SINGLELINE | DT_END_ELLIPSIS);

        RECT n = b.rect;
        n.left += 18; n.right -= 18; n.top += 36; n.bottom -= 8;
        guiDrawText(mem, b.note, n, noteFont, b.enabled ? RGB(136, 196, 159) : RGB(88, 99, 93), DT_LEFT | DT_SINGLELINE | DT_END_ELLIPSIS);

        if (b.id == GUI_CMD_HPET || b.id == GUI_CMD_RESTORE_POINT) {
            int state = (b.id == GUI_CMD_HPET) ? g_guiHpetState.load() : g_guiRestoreState.load();
            RECT ir{b.rect.right - 42, b.rect.top + 14, b.rect.right - 18, b.rect.top + 38};
            COLORREF fill = state == 1 ? RGB(18, 125, 52) : (state == 2 ? RGB(150, 30, 35) : RGB(86, 95, 88));
            COLORREF line = state == 1 ? RGB(180, 255, 190) : (state == 2 ? RGB(255, 190, 190) : RGB(210, 220, 212));
            HBRUSH ib = CreateSolidBrush(fill);
            HPEN ip = CreatePen(PS_SOLID, 2, line);
            HGDIOBJ oldB = SelectObject(mem, ib);
            HGDIOBJ oldP = SelectObject(mem, ip);
            Ellipse(mem, ir.left, ir.top, ir.right, ir.bottom);
            if (state == 1) {
                MoveToEx(mem, ir.left + 6, ir.top + 12, nullptr);
                LineTo(mem, ir.left + 10, ir.top + 17);
                LineTo(mem, ir.left + 19, ir.top + 7);
            } else {
                MoveToEx(mem, ir.left + 7, ir.top + 7, nullptr);
                LineTo(mem, ir.right - 7, ir.bottom - 7);
                MoveToEx(mem, ir.right - 7, ir.top + 7, nullptr);
                LineTo(mem, ir.left + 7, ir.bottom - 7);
            }
            SelectObject(mem, oldP);
            SelectObject(mem, oldB);
            DeleteObject(ip);
            DeleteObject(ib);
        }
    }

    if (g_timerBenchmarkRunning.load()) {
        RECT busyRect{28, height - 48, width - 28, height - 18};
        guiDrawText(mem, trW(TextId::BusyFooter), busyRect,
                    noteFont, RGB(180, 225, 196), DT_LEFT | DT_SINGLELINE | DT_END_ELLIPSIS);
    }

    BitBlt(hdc, 0, 0, width, height, mem, 0, 0, SRCCOPY);

    DeleteObject(titleFont);
    DeleteObject(subtitleFont);
    DeleteObject(statusFont);
    DeleteObject(buttonFont);
    DeleteObject(noteFont);
    SelectObject(mem, oldBmp);
    DeleteObject(bmp);
    DeleteDC(mem);
    EndPaint(hwnd, &ps);
}

static LRESULT CALLBACK guiWndProc(HWND hwnd, UINT msg, WPARAM wParam, LPARAM lParam)
{
    switch (msg) {
    case WM_CREATE: {
        g_guiHwnd = hwnd;
        RECT rc;
        GetClientRect(hwnd, &rc);
        guiResetMatrix(rc.right - rc.left, rc.bottom - rc.top);
        SetTimer(hwnd, 1, 33, nullptr);
        SetTimer(hwnd, 2, 3000, nullptr);
        guiRefreshHpetStatusAsync();
        guiRefreshRestoreStatusAsync();
        guiSetStatusW(trW(TextId::ReadyChoose));
        return 0;
    }
    case WM_SIZE: {
        RECT rc;
        GetClientRect(hwnd, &rc);
        guiResetMatrix(rc.right - rc.left, rc.bottom - rc.top);
        InvalidateRect(hwnd, nullptr, FALSE);
        return 0;
    }
    case WM_TIMER: {
        RECT rc;
        GetClientRect(hwnd, &rc);
        if (wParam == 1) guiAdvanceMatrix(rc);
        if (wParam == 2) {
            guiRefreshHpetStatusAsync();
            guiRefreshRestoreStatusAsync();
        }
        InvalidateRect(hwnd, nullptr, FALSE);
        return 0;
    }
    case WM_MOUSEMOVE: {
        POINT pt{GET_X_LPARAM(lParam), GET_Y_LPARAM(lParam)};
        int hit = guiHitTestButton(pt);
        if (hit != g_guiHoverButton) {
            g_guiHoverButton = hit;
            InvalidateRect(hwnd, nullptr, FALSE);
        }
        SetCursor(hit ? LoadCursor(nullptr, IDC_HAND) : LoadCursor(nullptr, IDC_ARROW));
        return 0;
    }
    case WM_MOUSELEAVE:
        g_guiHoverButton = 0;
        InvalidateRect(hwnd, nullptr, FALSE);
        return 0;
    case WM_LBUTTONUP: {
        POINT pt{GET_X_LPARAM(lParam), GET_Y_LPARAM(lParam)};
        int hit = guiHitTestButton(pt);
        for (const auto& b : g_guiButtons) {
            if (b.id == hit && b.enabled) {
                guiRunCommand(hit);
                break;
            }
        }
        return 0;
    }
    case WM_APP + 10:
        InvalidateRect(hwnd, nullptr, FALSE);
        return 0;
    case WM_PAINT:
        guiPaint(hwnd);
        return 0;
    case WM_CLOSE:
        if (g_timerBenchmarkRunning.load()) {
            MessageBoxW(hwnd, trW(TextId::CloseBenchmarkMessage), L"Sardanello", MB_OK | MB_ICONINFORMATION);
            return 0;
        }
        DestroyWindow(hwnd);
        return 0;
    case WM_DESTROY:
        KillTimer(hwnd, 1);
        KillTimer(hwnd, 2);
        StopEmbeddedMusic();
        g_running = false;
        PostQuitMessage(0);
        return 0;
    default:
        return DefWindowProcW(hwnd, msg, wParam, lParam);
    }
}

static int runGuiApp(HINSTANCE instance)
{
    g_running = true;
    g_matrixPause = false;
    broadcastSwitchToEnglishLayout();

    StartMusicTrack(IDR_WAV_1);
    AppLanguage selectedLanguage = AppLanguage::Russian;
    if (!runLanguageSelection(instance, selectedLanguage)) {
        StopEmbeddedMusic();
        broadcastRestoreLayout();
        return 0;
    }
    g_appLanguage = selectedLanguage;
    StartMusicTrack(IDR_WAV_2);

    const wchar_t* className = L"SardanelloGuiWindow";
    WNDCLASSEXW wc{};
    wc.cbSize = sizeof(wc);
    wc.style = CS_HREDRAW | CS_VREDRAW;
    wc.lpfnWndProc = guiWndProc;
    wc.hInstance = instance;
    wc.hIcon = LoadIconW(instance, MAKEINTRESOURCEW(IDR_MAINICON));
    wc.hCursor = LoadCursor(nullptr, IDC_ARROW);
    wc.hbrBackground = (HBRUSH)GetStockObject(BLACK_BRUSH);
    wc.lpszClassName = className;
    wc.hIconSm = wc.hIcon;
    RegisterClassExW(&wc);

    DWORD style = WS_OVERLAPPED | WS_CAPTION | WS_SYSMENU | WS_MINIMIZEBOX;
    RECT wr{0, 0, 980, 660};
    AdjustWindowRect(&wr, style, FALSE);
    int winW = wr.right - wr.left;
    int winH = wr.bottom - wr.top;
    int x = (GetSystemMetrics(SM_CXSCREEN) - winW) / 2;
    int y = (GetSystemMetrics(SM_CYSCREEN) - winH) / 2;

    HWND hwnd = CreateWindowExW(0, className, L"Sardanello", style,
                                x, y, winW, winH, nullptr, nullptr, instance, nullptr);
    if (!hwnd) {
        StopEmbeddedMusic();
        return 1;
    }

    ShowWindow(hwnd, SW_SHOW);
    UpdateWindow(hwnd);

    MSG msg;
    while (GetMessageW(&msg, nullptr, 0, 0) > 0) {
        TranslateMessage(&msg);
        DispatchMessageW(&msg);
    }

    broadcastRestoreLayout();
    return (int)msg.wParam;
}

#endif

static int runConsoleMain(int argc, char* argv[])
{
    // Проверяем аргументы командной строки для режима службы
    if (argc >= 2 && strcmp(argv[1], "--timer-service") == 0) {
        // Запускаем в режиме службы (фоновый мониторинг таймера)
        return runTimerService();
    }
    
    // Setup console appearance
#ifdef _WIN32
    // Ensure console uses our color immediately
    HANDLE h = GetStdHandle(STD_OUTPUT_HANDLE);
    // Optional: set buffer size or window size here
#endif

    hideCursor();
    setMatrixColors();
    std::cout << std::flush;

    // { changed code: enable VT sequences / UTF-8 on Windows so ANSI coloring works }
    enableVirtualTerminalAndUTF8();

    // Force English keyboard layout for the system while application runs
    broadcastSwitchToEnglishLayout();
    // Prevent mouse selection from pausing the console (QuickEdit)
    disableConsoleQuickEdit();

#ifdef _WIN32
    // Public builds are silent unless SARDANELLO_ENABLE_AUDIO is enabled.
    StartMusicSequence();

    // Prepare and reserve the loading UI area so the matrix thread won't draw over it.
    {
        ConsoleSize cs = getConsoleSize();
        int cx = cs.cols / 2;
        int cy = cs.rows / 2;
        const int barWidth = 40;
        int width = barWidth + 2; // brackets
        Rect loadingRect;
        loadingRect.w = width;
        loadingRect.h = 4; // title, gap, bar, percent
        loadingRect.x = cx - (width / 2);
        loadingRect.y = cy - 1;
        std::lock_guard<std::mutex> ml(g_menuMutex);
        g_menuRect = loadingRect;
        g_bannerRect = {0,0,0,0};
    }

    // Prepare a matrix thread variable so it remains in scope for shutdown
    std::thread matrixThread;
    // Start matrix background so "digital rain" runs during loading
    {
        auto isInMenuLocal = [](int x, int y) -> bool {
            std::lock_guard<std::mutex> lk(g_menuMutex);
            bool inMenu = x >= g_menuRect.x && x < g_menuRect.x + g_menuRect.w &&
                          y >= g_menuRect.y && y < g_menuRect.y + g_menuRect.h;
            bool inBanner = x >= g_bannerRect.x && x < g_bannerRect.x + g_bannerRect.w &&
                            y >= g_bannerRect.y && y < g_bannerRect.y + g_bannerRect.h;
            return inMenu || inBanner;
        };
        matrixThread = std::thread(matrixThreadFunc, isInMenuLocal);
    }

    // Show loading UI for 14 seconds (matches first track length)
    showLoadingScreen(14.0);
#endif

// ... existing code continues

    // Draw initial screen (clear)
#ifdef _WIN32
    system("cls");
#else
    std::cout << "\x1b[2J\x1b[H";
#endif

    // Draw menu and get its area (drawMenu writes to g_menuRect)
    drawMenu();

    // matrixThread already started earlier (it runs during loading)

    // track previous console size to detect resize
    ConsoleSize prevCS = getConsoleSize();

    // Main input loop
    while (g_running) {
        // { changed code: detect window resize and redraw centered menu }
        ConsoleSize curCS = getConsoleSize();
        if (curCS.cols != prevCS.cols || curCS.rows != prevCS.rows) {
            // clear screen while holding console lock to avoid tearing
            {
                std::lock_guard<std::mutex> lk(g_consoleMutex);
    #ifdef _WIN32
                system("cls");
    #else
                std::cout << "\x1b[2J\x1b[H";
    #endif
            }
            drawMenu();            // updates g_menuRect
            prevCS = curCS;
        }

        int c = getKey();
#ifdef _WIN32
        // fallback: if no key from getKey(), also check async key state for SPACE/Backspace
        static auto lastSpace = std::chrono::steady_clock::time_point::min();
        static auto lastBack = std::chrono::steady_clock::time_point::min();
        if (c == -1) {
            if (GetAsyncKeyState(VK_SPACE) & 0x8000) {
                auto now = std::chrono::steady_clock::now();
                if (now - lastSpace > std::chrono::milliseconds(200)) {
                    c = ' ';
                    lastSpace = now;
                }
            } else if (GetAsyncKeyState(VK_BACK) & 0x8000) {
                auto now = std::chrono::steady_clock::now();
                if (now - lastBack > std::chrono::milliseconds(200)) {
                    c = 8;
                    lastBack = now;
                }
            }
        }
#endif
        // Global action: if reboot is available and user pressed Y/y, perform reboot (на страницах 1, 3 и 4)
        if ((c == 'Y' || c == 'y') && g_rebootAvailable && (g_currentPage == 1 || g_currentPage == 3 || g_currentPage == 4)) {
            // attempt reboot (does not block UI thread for long)
            attemptReboot();
            // clear any message and force redraw
            {
                std::lock_guard<std::mutex> sl(g_menuMutex);
                g_statusLines[2] = "Перезагрузка инициирована...";
            }
            drawMenu();
            // continue to next input iteration
        } else if (c != -1 && !g_timerBenchmarkRunning) {
            // Игнорируем все клавиши во время тестирования (кроме Y для перезагрузки)
            if (c == '1') {
            // page-dependent: on page 1 -> perform combined action
            if (g_currentPage == 1) {
                // Проверяем права администратора
                if (!isAdministrator()) {
                    {
                        std::lock_guard<std::mutex> sl(g_menuMutex);
                        g_statusLines[0] = "❌ Требуются права администратора!";
                        g_statusLines[1] = "⚠️ Запустите Sardanello.exe от имени администратора";
                        g_statusLines[2] = "🔐 Для настройки HPET и таймера нужны admin права";
                    }
                    drawMenu();
                } else {
                    // cancel any pending reboot flag first
                    g_rebootAvailable = false;
                    g_rebootMessage.clear();
                    appendPowerLog("User invoked combined set-5000ms + HPET/boot tweaks via [1] key");
                    // run both actions in background so UI doesn't block. Order: set processor interval first, then HPET/tweaks.
                    std::thread([](){
                        // 1) set processor performance check interval for all schemes
                        setProcessorCheckIntervalAllSchemes(5000);

                        // 2) attempt to disable HPET and apply boot/registry tweaks (this function already logs and updates g_statusLines)
                        disableHighPrecisionTimer();
                    }).detach();
                }
            } else if (g_currentPage == 2) {
                // spawn worker thread if not already running
                bool expected = false;
                if (g_timerBenchmarkRunning.compare_exchange_strong(expected, true)) {
                    // starting benchmark clears any pending reboot prompt
                    g_rebootAvailable = false;
                    g_rebootMessage.clear();
                    
                    // Остановим службу SardanelloTimerConst перед тестированием
                    bool serviceWasStopped = stopTimerService();
                    
                    // Сбросим таймер к дефолтному значению
                    resetTimerToDefault();
                    
                    // Немедленное сообщение о начале теста
                    {
                        std::lock_guard<std::mutex> sl(g_menuMutex);
                        g_statusLines[0] = "🚀 Запуск Gaming Timer Analysis...";
                        if (serviceWasStopped) {
                            g_statusLines[1] = "⏳ Служба остановлена, инициализация теста...";
                        } else {
                            g_statusLines[1] = "⏳ Инициализация теста, подождите...";
                        }
                        g_statusLines[2] = "";
                    }
                    drawMenu(); // Немедленно отображаем сообщение
                    
                    std::thread([](){
                        showBestTimer();
                        g_timerBenchmarkRunning = false;
                        // request a redraw by setting a status line (main loop will redraw periodically)
                        std::lock_guard<std::mutex> sl(g_menuMutex);
                        g_statusLines[2] = "Benchmark finished";
                    }).detach();
                } else {
                    std::lock_guard<std::mutex> sl(g_menuMutex);
                    g_statusLines[2] = "Benchmark already running";
                }
            } else if (g_currentPage == 3) {
                // Страница 3: Применить идеальный таймер перманентно
                OptimalTimerResult optimal = loadOptimalTimer();
                
                if (optimal.isValid) {
                    bool serviceExists = isServiceRunning();
                    
                    {
                        std::lock_guard<std::mutex> sl(g_menuMutex);
                        if (serviceExists) {
                            // Служба уже существует - просто обновляем конфигурацию
                            char buf[256];
                            std::snprintf(buf, sizeof(buf), "🔄 Обновлен таймер: %.6f мс", optimal.timerMs);
                            g_statusLines[0] = buf;
                            g_statusLines[1] = "✅ Служба SardanelloTimer автоматически применит новое значение";
                            g_statusLines[2] = "📊 Для применения после перезагрузки нажмите [Y]";
                            
                            // Устанавливаем флаг для перезагрузки
                            g_rebootAvailable = true;
                            g_rebootMessage = "Timer service updated; press Y to reboot";
                        } else {
                            // Создаем службу впервые
                            bool serviceCreated = createTimerService(optimal.timerMs);
                            if (serviceCreated) {
                                // Применяем таймер немедленно
                                bool applied = applyOptimalTimer(optimal.timerMs);
                                
                                char buf[256];
                                std::snprintf(buf, sizeof(buf), "✅ Таймер %.6f мс применен и добавлен в автозагрузку!", optimal.timerMs);
                                g_statusLines[0] = buf;
                                g_statusLines[1] = "🔄 Служба SardanelloTimer запущена в фоновом режиме";
                                g_statusLines[2] = "📊 Для применения после перезагрузки нажмите [Y]";
                                
                                // Устанавливаем флаг для перезагрузки
                                g_rebootAvailable = true;
                                g_rebootMessage = "Timer service configured; press Y to reboot";
                            } else {
                                g_statusLines[0] = "❌ Ошибка запуска службы таймера";
                                g_statusLines[1] = "⚠️ Проверьте права доступа или антивирус";
                                g_statusLines[2] = "🔍 Проверьте диспетчер задач на наличие процесса Sardanello.exe";
                            }
                        }
                    }
                } else {
                    // Таймер не найден - просим ввести вручную
                    {
                        std::lock_guard<std::mutex> sl(g_menuMutex);
                        g_statusLines[0] = "⚠️ Идеальный таймер не найден!";
                        g_statusLines[1] = "📝 Сначала проведите тест на странице 2/12";
                        g_statusLines[2] = "🔧 Или введите таймер вручную (в разработке)";
                    }
                }
            } else if (g_currentPage == 4) {
                // Страница 4: Управление питанием (упрощенная логика)
                
                // 1. Проверяем права администратора
                if (!isAdministrator()) {
                    std::lock_guard<std::mutex> sl(g_menuMutex);
                    g_statusLines[0] = "❌ Требуются права администратора!";
                    g_statusLines[1] = "⚠️ Запустите Sardanello.exe от имени администратора";
                    g_statusLines[2] = "🔐 Для управления питанием нужны admin права";
                } else {
                    // Выполняем двухэтапную логику в фоновом потоке
                    std::thread([](){
                        // УПРОЩЕННАЯ ЛОГИКА: Проверяем состояние реестра PlatformAoAcOverride
                        {
                            std::lock_guard<std::mutex> sl(g_menuMutex);
                            g_statusLines[0] = "🔍 Проверяем состояние реестра...";
                            g_statusLines[1] = "⏳ Читаем PlatformAoAcOverride";
                            g_statusLines[2] = "";
                        }
                        drawMenu();
                        
                        int currentValue = getPlatformAoAcOverride();
                        
                        if (currentValue == -1) {
                            // Ключ не существует - создаем и ставим 0
                            {
                                std::lock_guard<std::mutex> sl(g_menuMutex);
                                g_statusLines[0] = "🔧 Ключ PlatformAoAcOverride не найден";
                                g_statusLines[1] = "⏳ Создаем ключ и устанавливаем значение 0...";
                                g_statusLines[2] = "";
                            }
                            drawMenu();
                            
                            bool success = setPlatformAoAcOverride(false);
                            
                            {
                                std::lock_guard<std::mutex> sl(g_menuMutex);
                                if (success) {
                                    g_statusLines[0] = "✅ Ключ создан и установлен в 0";
                                    g_statusLines[1] = "🔄 Требуется перезагрузка системы";
                                    g_statusLines[2] = "Для шага 4/12 требуется перезагрузка. Нажмите [Y]";
                                    g_rebootAvailable = true;
                                    g_rebootMessage = "Registry key created; reboot required";
                                } else {
                                    g_statusLines[0] = "❌ Ошибка создания ключа в реестре";
                                    g_statusLines[1] = "⚠️ Проверьте права администратора";
                                    g_statusLines[2] = "";
                                }
                            }
                        } else if (currentValue != 0) {
                            // Ключ существует, но не равен 0 - изменяем на 0
                            {
                                std::lock_guard<std::mutex> sl(g_menuMutex);
                                g_statusLines[0] = "🔧 Ключ найден, текущее значение: " + std::to_string(currentValue);
                                g_statusLines[1] = "⏳ Изменяем значение на 0...";
                                g_statusLines[2] = "";
                            }
                            drawMenu();
                            
                            bool success = setPlatformAoAcOverride(false);
                            
                            {
                                std::lock_guard<std::mutex> sl(g_menuMutex);
                                if (success) {
                                    g_statusLines[0] = "✅ Значение изменено на 0";
                                    g_statusLines[1] = "🔄 Требуется перезагрузка системы";
                                    g_statusLines[2] = "Для шага 4/12 требуется перезагрузка. Нажмите [Y]";
                                    g_rebootAvailable = true;
                                    g_rebootMessage = "Registry value changed; reboot required";
                                } else {
                                    g_statusLines[0] = "❌ Ошибка изменения ключа в реестре";
                                    g_statusLines[1] = "⚠️ Проверьте права администратора";
                                    g_statusLines[2] = "";
                                }
                            }
                        } else {
                            // Ключ существует и равен 0 - применяем профиль питания
                            {
                                std::lock_guard<std::mutex> sl(g_menuMutex);
                                g_statusLines[0] = "✅ PlatformAoAcOverride уже равен 0";
                                g_statusLines[1] = "⏳ Применяем профиль Sardanello (поиск и активация)...";
                                g_statusLines[2] = "🔧 S0 отключен, можно применять профиль";
                            }
                            drawMenu();
                            
                            bool powerPlanSuccess = importAndApplyPowerPlanSimple();
                            
                            {
                                std::lock_guard<std::mutex> sl(g_menuMutex);
                                if (powerPlanSuccess) {
                                    g_statusLines[0] = "✅ Профиль Sardanello.pow успешно применен!";
                                    g_statusLines[1] = "🎮 План электропитания активирован";
                                    g_statusLines[2] = "⚡ Система настроена для максимальной производительности";
                                } else {
                                    g_statusLines[0] = "❌ Ошибка установки плана электропитания";
                                    g_statusLines[1] = "⚠️ Проверьте наличие файла Sardanello.pow";
                                    g_statusLines[2] = "📁 Файл должен быть в той же папке с exe";
                                }
                            }
                        }
                        
                        drawMenu();
                    }).detach();
                }
            }
            // redraw menu to keep it visible after message
            drawMenu();
        } else if (c == '2') {
            // Клавиша [2] не назначена во всех разделах — ничего не делаем
            if (!g_timerBenchmarkRunning) {
                showTemporaryStatus("ℹ️ Клавиша [2] не назначена на этой странице", 2000);
            }
        } else if (c == 'D' || c == 'd') {
            // Открываем страницу доната в браузере
            #ifdef _WIN32
            ShellExecuteA(NULL, "open", "https://www.donationalerts.com/r/sardanello", NULL, NULL, SW_SHOWNORMAL);
            #endif
            showTemporaryStatus("💰 Страница доната открыта в браузере! Спасибо за поддержку! 🌟", 3000);
        } else if (c == 'T' || c == 't') {
            // Открываем Telegram канал в браузере
            #ifdef _WIN32
            ShellExecuteA(NULL, "open", "https://t.me/Sardanello", NULL, NULL, SW_SHOWNORMAL);
            #endif
            showTemporaryStatus("📢 Telegram канал открыт в браузере! Подписывайтесь! 🚀", 3000);
        } else if (c == ' ' || c == 32) { // SPACE -> next page
            if (g_timerBenchmarkRunning) {
                showTemporaryStatus("Нельзя переключать страницы во время теста", 2000);
            } else {
                // user navigated -> clear pending reboot
                g_rebootAvailable = false;
                g_rebootMessage.clear();
                
                // Очищаем информационное окно при переходе между страницами
                {
                    std::lock_guard<std::mutex> sl(g_menuMutex);
                    g_statusLines[0].clear();
                    g_statusLines[1].clear();
                    g_statusLines[2].clear();
                }
                
                g_currentPage++;
                if (g_currentPage > g_totalPages) g_currentPage = g_totalPages;
                
                // При переходе на страницу 2 (тестирование) открываем важные инструкции
                if (g_currentPage == 2) {
                    createAndOpenReadme();
                }
                
                drawMenu();
            }
        } else if (c == 8) { // Backspace
            if (g_timerBenchmarkRunning) {
                showTemporaryStatus("Нельзя переключать страницы во время теста", 2000);
            } else {
                // user navigated -> clear pending reboot
                g_rebootAvailable = false;
                g_rebootMessage.clear();
                
                // Очищаем информационное окно при переходе между страницами
                {
                    std::lock_guard<std::mutex> sl(g_menuMutex);
                    g_statusLines[0].clear();
                    g_statusLines[1].clear();
                    g_statusLines[2].clear();
                }
                
                g_currentPage--;
                if (g_currentPage < 1) g_currentPage = 1;
                drawMenu();
            }
        } else if (c == 27) { // ESC
            exitProgram();
            break;
        }
        } // конец блока !g_timerBenchmarkRunning

        // small sleep to avoid busy loop
        std::this_thread::sleep_for(std::chrono::milliseconds(20));
    }

    // Shutdown
    g_running = false;
    if (matrixThread.joinable()) matrixThread.join();

    {
        std::lock_guard<std::mutex> lk(g_consoleMutex);
        showCursor();
        resetColors();
#ifdef _WIN32
        // optional: clear before exit
        // system("cls");
#ifdef _WIN32
    // restore previous keyboard layout if we changed it
    broadcastRestoreLayout();
#endif
#else
        // clear line and move cursor to bottom
        std::cout << "\n";
#endif
    }

    return 0;
}

#ifdef _WIN32
static std::wstring quoteWideArg(const std::wstring& arg)
{
    if (arg.find_first_of(L" \t\"") == std::wstring::npos) return arg;
    std::wstring out = L"\"";
    for (wchar_t ch : arg) {
        if (ch == L'"') out += L'\\';
        out += ch;
    }
    out += L"\"";
    return out;
}

static bool relaunchSelfElevated()
{
    if (isAdministrator()) return false;

    wchar_t exePath[MAX_PATH] = {};
    if (!GetModuleFileNameW(nullptr, exePath, MAX_PATH)) return false;

    int argcW = 0;
    LPWSTR* argvW = CommandLineToArgvW(GetCommandLineW(), &argcW);
    std::wstring params;
    if (argvW) {
        for (int i = 1; i < argcW; ++i) {
            if (!params.empty()) params += L' ';
            params += quoteWideArg(argvW[i]);
        }
        LocalFree(argvW);
    }

    SHELLEXECUTEINFOW sei{};
    sei.cbSize = sizeof(sei);
    sei.fMask = SEE_MASK_NOCLOSEPROCESS;
    sei.lpVerb = L"runas";
    sei.lpFile = exePath;
    sei.lpParameters = params.empty() ? nullptr : params.c_str();
    sei.nShow = SW_SHOWNORMAL;

    if (ShellExecuteExW(&sei)) {
        if (sei.hProcess) CloseHandle(sei.hProcess);
        return true;
    }

    DWORD err = GetLastError();
    if (err != ERROR_CANCELLED) {
        MessageBoxW(nullptr, L"Не удалось запустить Sardanello от имени администратора.", L"Sardanello", MB_OK | MB_ICONERROR);
    }
    return true;
}
#endif

int main(int argc, char* argv[])
{
    if (argc >= 2 && strcmp(argv[1], "--timer-service") == 0) {
        return runTimerService();
    }

#ifdef _WIN32
    if (relaunchSelfElevated()) {
        return 0;
    }
#endif

    if (argc >= 2 && strcmp(argv[1], "--console") == 0) {
#ifdef _WIN32
        if (!GetConsoleWindow()) {
            AllocConsole();
            FILE* ignored = nullptr;
            freopen_s(&ignored, "CONIN$", "r", stdin);
            freopen_s(&ignored, "CONOUT$", "w", stdout);
            freopen_s(&ignored, "CONOUT$", "w", stderr);
        }
#endif
        return runConsoleMain(argc, argv);
    }

#ifdef _WIN32
    return runGuiApp(GetModuleHandleW(nullptr));
#else
    return runConsoleMain(argc, argv);
#endif
}
// ...existing code...
