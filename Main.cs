using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Diagnostics;
using System.Drawing;
using System.Drawing.Imaging;
using System.IO;
using System.Linq;
using System.Runtime.InteropServices;
using System.Threading.Tasks;
using Flow.Launcher.Plugin;
using NAudio.CoreAudioApi;
using Windows.Media.Control;

namespace Flow.Launcher.Plugin.MediaControl
{
    public class Main : IPlugin, IContextMenu
    {
        private PluginInitContext _context = null!;
        private GlobalSystemMediaTransportControlsSessionManager? _smtcManager;

        private static readonly ConcurrentDictionary<string, string> _iconMemoryCache = new();
        private static readonly ConcurrentDictionary<string, bool> _localPlayState = new();
        private static readonly ConcurrentDictionary<string, DateTime> _lastToggleTime = new();
        private static readonly MMDeviceEnumerator _audioEnumerator = new();

        // 【核心】后台会话缓存池
        private static readonly ConcurrentDictionary<string, MediaSessionCache> _sessionCache = new();
        
        // 【核心】启发式学习字典：记录 乱码ID -> 真实进程名 (如 29a0986d... -> zen)
        private static readonly ConcurrentDictionary<string, string> _appIdentityMap = new();

        // 【UI强制刷新核心变量】
        private static List<Result> _cachedResults = new();
        private static string _currentTargetApp = "";
        private static string _currentActionKeyword = "mc";
        private static string _lastRawQuery = ""; // 记录最后一次输入框里的确切文本
        private static bool _wasVisible = false;  // 状态机：记录上一次判定时窗口是否可见
        private static uint _currentPid;

        // 黑名单
        private static readonly HashSet<string> _blacklist = new(StringComparer.OrdinalIgnoreCase)
        {
            "flow.launcher", "flowlauncher", "explorer", "shellexperiencehost",
            "textinputhost", "systemsettings", "applicationframehost"
        };

        // ================= 本地化：静态内置字典 =================
        private static readonly Dictionary<string, string> _zhCn = new()
        {
            {"masterVolume", "总音量: {0}%"},
            {"currentOutput", "当前输出: {0}"},
            {"switchOutputDevice", "点击切换输出设备"},
            {"systemSounds", "系统声音: {0}%"},
            {"appPlaying", "[{0}] ▶ 播放中 | 音量: {1}%"},
            {"appPaused", "[{0}] ⏸ 已暂停 | 音量: {1}%"},
            {"appVolumeOnly", "[{0}] 音量: {1}%"},
            {"play", "播放"},
            {"pause", "暂停"},
            {"previous", "上一首"},
            {"next", "下一首"},
            {"volumeUp", "增大音量"},
            {"volumeDown", "减小音量"},
            {"mute", "静音"},
            {"unmute", "恢复声音"},
            {"setVolumeTo", "设定音量至 {0}%"},
            {"inUse", "[当前使用]"},
            {"clickToSwitch", "点击切换"},
            {"jumpTo", "跳转到 {0}"},
            {"appDefaultName", "应用"}
        };

        private static readonly Dictionary<string, string> _en = new()
        {
            {"masterVolume", "Master Volume: {0}%"},
            {"currentOutput", "Output: {0}"},
            {"switchOutputDevice", "Click to switch output device"},
            {"systemSounds", "System Sounds: {0}%"},
            {"appPlaying", "[{0}] ▶ Playing | Volume: {1}%"},
            {"appPaused", "[{0}] ⏸ Paused | Volume: {1}%"},
            {"appVolumeOnly", "[{0}] Volume: {1}%"},
            {"play", "Play"},
            {"pause", "Pause"},
            {"previous", "Previous"},
            {"next", "Next"},
            {"volumeUp", "Volume Up"},
            {"volumeDown", "Volume Down"},
            {"mute", "Mute"},
            {"unmute", "Unmute"},
            {"setVolumeTo", "Set volume to {0}%"},
            {"inUse", "[In use]"},
            {"clickToSwitch", "Click to switch"},
            {"jumpTo", "Jump to {0}"},
            {"appDefaultName", "App"}
        };

        private string Tr(string key)
        {
            string lang = System.Globalization.CultureInfo.CurrentUICulture.Name;
            bool isZh = lang.StartsWith("zh", StringComparison.OrdinalIgnoreCase);
            var dict = isZh ? _zhCn : _en;
            if (dict.TryGetValue(key, out string? value) && value != null)
                return value;
            return key; // fallback
        }

        // ================= Win32 API =================
        [DllImport("user32.dll")]
        private static extern bool SetForegroundWindow(IntPtr hWnd);
        
        [DllImport("user32.dll")]
        private static extern bool IsIconic(IntPtr hWnd);
        
        [DllImport("user32.dll")]
        private static extern bool ShowWindowAsync(IntPtr hWnd, int nCmdShow);
        
        [DllImport("user32.dll")]
        private static extern IntPtr GetForegroundWindow();

        [DllImport("user32.dll")]
        private static extern uint GetWindowThreadProcessId(IntPtr hWnd, out uint lpdwProcessId);

        [DllImport("user32.dll", CharSet = CharSet.Auto)]
        private static extern IntPtr SendMessageW(IntPtr hWnd, uint Msg, IntPtr wParam, IntPtr lParam);

        private const uint WM_APPCOMMAND = 0x0319;
        private const int APPCOMMAND_VOLUME_MUTE = 8;
        private const int APPCOMMAND_VOLUME_DOWN = 9;
        private const int APPCOMMAND_VOLUME_UP = 10;
        private const int APPCOMMAND_MEDIA_NEXTTRACK = 11;
        private const int APPCOMMAND_MEDIA_PREVIOUSTRACK = 12;
        private const int APPCOMMAND_MEDIA_PLAY_PAUSE = 14;

        public void Init(PluginInitContext context)
        {
            _context = context;
            _currentPid = (uint)Process.GetCurrentProcess().Id;

            try
            {
                string cachePath = Path.Combine(_context.CurrentPluginMetadata.PluginDirectory, "Cache");
                if (Directory.Exists(cachePath)) Directory.Delete(cachePath, true);
                _iconMemoryCache.Clear();
            }
            catch { }

            // 全局守护进程：在后台静默监听系统媒体事件
            Task.Run(async () =>
            {
                try
                {
                    _smtcManager = await GlobalSystemMediaTransportControlsSessionManager.RequestAsync();
                    if (_smtcManager != null)
                    {
                        _smtcManager.SessionsChanged += SmtcManagerOnSessionsChanged;
                        RefreshSessions();
                    }
                }
                catch { }
            });

            // ================= 前台强制热刷新与踢出引擎 =================
            Task.Run(async () =>
            {
                while (true)
                {
                    await Task.Delay(250); // 后台极低占用轮询
                    try
                    {
                        RefreshSessions();

                        IntPtr hWnd = GetForegroundWindow();
                        GetWindowThreadProcessId(hWnd, out uint fgPid);
                        var fgProc = Process.GetProcessById((int)fgPid);
                        
                        bool isVisible = fgProc.ProcessName.Contains("Flow.Launcher", StringComparison.OrdinalIgnoreCase);

                        if (!isVisible)
                        {
                            _wasVisible = false;
                            continue;
                        }

                        // ====== 【防劫持核心逻辑】：跨线程读取输入框内容 ======
                        string? currentInput = GetCurrentInputText();
                        // 如果成功读取到了搜索框，并且发现它不是以我们自定义的插件关键词(如 mc)开头，说明用户在搜别的！
                        // 此时直接跳过所有 ChangeQuery 逻辑，绝对不劫持。
                        if (currentInput != null && !currentInput.TrimStart().StartsWith(_currentActionKeyword, StringComparison.OrdinalIgnoreCase))
                        {
                            continue;
                        }

                        // ================= 1. 死进程踢回主菜单逻辑 (优先级最高) =================
                        if (!string.IsNullOrEmpty(_currentTargetApp) && _currentTargetApp != "master" && _currentTargetApp != "sys" && _currentTargetApp != "out")
                        {
                            var cache = GetTargetCache(_currentTargetApp);
                            var proc = GetProcessSafe(_currentTargetApp);
                            
                            if (cache == null && proc == null)
                            {
                                _currentTargetApp = ""; 
                                _lastRawQuery = $"{_currentActionKeyword} "; 
                                _context.API.ChangeQuery(_lastRawQuery, true); 
                                continue;
                            }
                        }

                        // ================= 2. 重新唤出时的“强行自动刷新” =================
                        if (!_wasVisible)
                        {
                            _wasVisible = true;
                            if (!string.IsNullOrEmpty(_lastRawQuery) && _lastRawQuery.StartsWith(_currentActionKeyword, StringComparison.OrdinalIgnoreCase))
                            {
                                _context.API.ChangeQuery(_lastRawQuery, true);
                                continue;
                            }
                        }

                        // ================= 3. 停留在界面时的“静默热更新” =================
                        if (_cachedResults.Count > 0)
                        {
                            using var device = _audioEnumerator.GetDefaultAudioEndpoint(DataFlow.Render, Role.Multimedia);
                            foreach (var res in _cachedResults)
                            {
                                // 热更新：播放/暂停 按钮状态
                                if (res.Title == "暂停" || res.Title == "播放")
                                {
                                    var cache = GetTargetCache(_currentTargetApp);
                                    bool isPlaying = cache?.IsPlaying ?? false;

                                    if (_lastToggleTime.TryGetValue(_currentTargetApp, out DateTime lastTime) &&
                                        (DateTime.Now - lastTime).TotalMilliseconds < 2000 &&
                                        _localPlayState.TryGetValue(_currentTargetApp, out bool cachedState))
                                    {
                                        isPlaying = cachedState;
                                    }

                                    string targetTitle = isPlaying ? "暂停" : "播放";
                                    string targetIco = isPlaying ? "Images\\pause.png" : "Images\\play.png";
                                    
                                    if (res.Title != targetTitle) res.Title = targetTitle;
                                    if (res.IcoPath != targetIco) res.IcoPath = targetIco;
                                }
                                // 热更新：主音量界面
                                else if (res.Title != null && res.Title.StartsWith("总音量:"))
                                {
                                    int masterVol = (int)Math.Round(device.AudioEndpointVolume.MasterVolumeLevelScalar * 100);
                                    string targetTitle = $"总音量: {masterVol}%";
                                    string targetIco = device.AudioEndpointVolume.Mute ? "Images\\mute.png" : "Images\\app.png";
                                    
                                    if (res.Title != targetTitle) res.Title = targetTitle;
                                    if (res.IcoPath != targetIco) res.IcoPath = targetIco;
                                }
                                // 热更新：主菜单里的各个 App 音量与播放状态
                                else if (res.SubTitle != null && res.SubTitle.StartsWith("[") && res.SubTitle.Contains("] "))
                                {
                                    int endBracket = res.SubTitle.IndexOf(']');
                                    if (endBracket > 1)
                                    {
                                        string realAppName = res.SubTitle.Substring(1, endBracket - 1);
                                        var cache = GetTargetCache(realAppName);
                                        var proc = GetProcessSafe(realAppName);
                                        
                                        if (cache == null && proc == null)
                                        {
                                            string deadSub = $"[{realAppName}] ⏸ 已结束";
                                            if (res.SubTitle != deadSub) res.SubTitle = deadSub;
                                        }
                                        else
                                        {
                                            int vol = 100;
                                            var audioSession = FindSession(realAppName, device);
                                            if (audioSession != null) vol = (int)Math.Round(audioSession.SimpleAudioVolume.Volume * 100);
                                            
                                            bool isPlaying = cache?.IsPlaying ?? false;
                                            string tSub = $"[{realAppName}] {(isPlaying ? "▶ 播放中" : "⏸ 已暂停")} | 音量: {vol}%";
                                            if (res.SubTitle != tSub) res.SubTitle = tSub;
                                        }
                                    }
                                }
                            }
                        }
                    }
                    catch { }
                }
            });
        }

        // 利用底层反射调用 UIAutomation 获取输入框文本 (防编译报错)
        private static string? GetCurrentInputText()
        {
            try
            {
                Type? uiaType = Type.GetType("System.Windows.Automation.AutomationElement, UIAutomationClient, Version=4.0.0.0, Culture=neutral, PublicKeyToken=31bf3856ad364e35") 
                            ?? Type.GetType("System.Windows.Automation.AutomationElement, UIAutomationClient");
                if (uiaType == null) return null;

                object? focusedElement = uiaType.GetProperty("FocusedElement")?.GetValue(null);
                if (focusedElement == null) return null;

                Type? valuePatternType = Type.GetType("System.Windows.Automation.ValuePattern, UIAutomationClient, Version=4.0.0.0, Culture=neutral, PublicKeyToken=31bf3856ad364e35")
                                     ?? Type.GetType("System.Windows.Automation.ValuePattern, UIAutomationClient");
                
                if (valuePatternType != null)
                {
                    object? pattern = valuePatternType.GetField("Pattern")?.GetValue(null);
                    if (pattern != null)
                    {
                        object? valuePatternObj = uiaType.GetMethod("GetCurrentPattern")?.Invoke(focusedElement, new[] { pattern });
                        if (valuePatternObj != null)
                        {
                            object? currentObj = valuePatternType.GetProperty("Current")?.GetValue(valuePatternObj);
                            if (currentObj != null)
                            {
                                return currentObj.GetType().GetProperty("Value")?.GetValue(currentObj) as string;
                            }
                        }
                    }
                }
            }
            catch { }
            return null;
        }

        // ================= 全局启发式指纹识别引擎 =================
        private static string ResolveAndLearnIdentity(string appId, string title)
        {
            if (string.IsNullOrEmpty(appId)) return "";

            if (_appIdentityMap.TryGetValue(appId, out string? realName) && realName != null)
                return realName;

            string normalized = NormalizeAppId(appId);
            
            bool isHash = !normalized.Contains(".") && normalized.Length >= 8 && !new[] { "spotify", "chrome", "msedge", "firefox", "cloudmusic", "qqmusic" }.Contains(normalized);
            if (!isHash)
            {
                _appIdentityMap[appId] = normalized;
                return normalized;
            }

            if (!string.IsNullOrWhiteSpace(title))
            {
                var processes = Process.GetProcesses();
                foreach (var p in processes)
                {
                    if (!string.IsNullOrEmpty(p.MainWindowTitle))
                    {
                        if (p.MainWindowTitle.Contains(title, StringComparison.OrdinalIgnoreCase) ||
                            title.Contains(p.MainWindowTitle, StringComparison.OrdinalIgnoreCase))
                        {
                            string matchedName = NormalizeAppId(p.ProcessName);
                            _appIdentityMap[appId] = matchedName; 
                            return matchedName;
                        }
                    }
                }
            }

            string[] knownBrowsers = { "zen", "msedge", "chrome", "firefox", "brave" };
            foreach (var browser in knownBrowsers)
            {
                if (Process.GetProcessesByName(browser).Any())
                {
                    _appIdentityMap[appId] = browser;
                    return browser;
                }
            }

            return normalized;
        }

        // ================= 后台缓存与自动更新 =================
        private class MediaSessionCache : IDisposable
        {
            public GlobalSystemMediaTransportControlsSession Session { get; private set; }
            public string AppId { get; private set; }
            public string RealAppName { get; private set; } = "";
            public string Title { get; private set; } = "";
            public string Artist { get; private set; } = "";
            public bool IsPlaying { get; private set; }
            public bool IsValid { get; private set; } = true;

            public MediaSessionCache(GlobalSystemMediaTransportControlsSession session)
            {
                Session = session;
                AppId = session.SourceAppUserModelId ?? "";
                RealAppName = NormalizeAppId(AppId); // 默认值
                UpdateSession(session);
            }

            public void UpdateSession(GlobalSystemMediaTransportControlsSession session)
            {
                Unhook();
                Session = session;
                AppId = session.SourceAppUserModelId ?? "";
                Hook();
                UpdatePropertiesCore(true, true);
            }

            private void Hook()
            {
                try { Session.PlaybackInfoChanged += OnPlaybackChanged; Session.MediaPropertiesChanged += OnPropertiesChanged; } catch { }
            }

            private void Unhook()
            {
                try { if (Session != null) { Session.PlaybackInfoChanged -= OnPlaybackChanged; Session.MediaPropertiesChanged -= OnPropertiesChanged; } } catch { }
            }

            private void OnPlaybackChanged(GlobalSystemMediaTransportControlsSession sender, PlaybackInfoChangedEventArgs args) 
                => UpdatePropertiesCore(true, false);

            private void OnPropertiesChanged(GlobalSystemMediaTransportControlsSession sender, MediaPropertiesChangedEventArgs args) 
                => UpdatePropertiesCore(false, true);

            private void UpdatePropertiesCore(bool updatePlayback, bool updateMediaProps)
            {
                try
                {
                    if (updatePlayback)
                    {
                        var playbackInfo = Session.GetPlaybackInfo();
                        if (playbackInfo == null || playbackInfo.PlaybackStatus == GlobalSystemMediaTransportControlsSessionPlaybackStatus.Closed)
                        {
                            IsValid = false; return;
                        }
                        IsValid = true;
                        IsPlaying = playbackInfo.PlaybackStatus == GlobalSystemMediaTransportControlsSessionPlaybackStatus.Playing;
                    }

                    if (updateMediaProps)
                    {
                        Task.Run(async () =>
                        {
                            try
                            {
                                var props = await Session.TryGetMediaPropertiesAsync();
                                if (props != null)
                                {
                                    Title = props.Title ?? ""; Artist = props.Artist ?? "";
                                    RealAppName = ResolveAndLearnIdentity(AppId, Title);
                                }
                            } catch { }
                        });
                    }
                }
                catch { IsValid = false; }
            }

            public void Dispose() => Unhook();
        }

        private void SmtcManagerOnSessionsChanged(GlobalSystemMediaTransportControlsSessionManager sender, SessionsChangedEventArgs args)
        {
            RefreshSessions();
        }

        private void RefreshSessions()
        {
            if (_smtcManager == null) return;
            try
            {
                var sessions = _smtcManager.GetSessions();
                var currentIds = new HashSet<string>();

                foreach (var session in sessions)
                {
                    string id = session.SourceAppUserModelId ?? "";
                    if (string.IsNullOrEmpty(id)) continue;
                    
                    currentIds.Add(id);
                    if (_sessionCache.TryGetValue(id, out var existingCache)) existingCache.UpdateSession(session);
                    else _sessionCache[id] = new MediaSessionCache(session);
                }

                var toRemove = _sessionCache.Keys.Except(currentIds).ToList();
                foreach (var id in toRemove)
                {
                    if (_sessionCache.TryRemove(id, out var removedSession)) removedSession.Dispose();
                }
            } catch { }
        }

        private static string NormalizeAppId(string appId)
        {
            if (string.IsNullOrEmpty(appId)) return "";
            string lower = appId.ToLower();
            if (lower.Contains("spotify")) return "spotify";
            if (lower.Contains("chrome")) return "chrome";
            if (lower.Contains("msedge") || lower.Contains("edge")) return "msedge";
            if (lower.Contains("firefox")) return "firefox";
            if (lower.Contains("cloudmusic") || lower.Contains("netease")) return "cloudmusic";
            if (lower.Contains("qqmusic")) return "qqmusic";
            if (lower.EndsWith(".exe")) return lower[..^4];
            if (lower.Contains("!"))
            {
                var parts = lower.Split('!');
                if (parts.Length > 1 && parts[1].Length > 3 && parts[1] != "app") return parts[1];
                return parts[0].Split('.').Last();
            }
            return lower;
        }

        private Process? GetProcessSafe(string name)
        {
            try { return Process.GetProcessesByName(name).FirstOrDefault(); } catch { return null; }
        }

        private List<Result> ReturnAndCache(List<Result> res)
        {
            _cachedResults = res;
            return res;
        }

        // ================= UI 渲染层 =================
        public List<Result> Query(Query query)
        {
            RefreshSessions();
            
            _lastRawQuery = query.RawQuery;
            _currentActionKeyword = query.ActionKeyword;
            var parts = query.Search.ToLower().Trim().Split(' ', StringSplitOptions.RemoveEmptyEntries);
            _currentTargetApp = parts.Length > 0 ? parts[0] : "";

            var results = new List<Result>();
            string search = query.Search.ToLower().Trim();
            CleanupStaleCache();

            using var device = _audioEnumerator.GetDefaultAudioEndpoint(DataFlow.Render, Role.Multimedia);

            string friendlyName = device.FriendlyName.ToLower();
            bool isHeadphone = friendlyName.Contains("headphone") || 
                               friendlyName.Contains("耳机") || 
                               friendlyName.Contains("ear") || 
                               friendlyName.Contains("buds") || 
                               friendlyName.Contains("airpods") || 
                               friendlyName.Contains("headset");
            string deviceIcon = isHeadphone ? "Images\\headphone.png" : "Images\\device.png";

            // ---------- 一级菜单 ----------
            if (string.IsNullOrEmpty(search))
            {
                int masterVol = (int)Math.Round(device.AudioEndpointVolume.MasterVolumeLevelScalar * 100);
                results.Add(new Result
                {
                    Title = string.Format(Tr("masterVolume"), masterVol),
                    IcoPath = device.AudioEndpointVolume.Mute ? "Images\\mute.png" : "Images\\app.png",
                    Score = 100000,
                    Action = _ => { _context.API.ChangeQuery($"{_currentActionKeyword} master "); return false; }
                });

                results.Add(new Result
                {
                    Title = string.Format(Tr("currentOutput"), device.FriendlyName),
                    SubTitle = Tr("switchOutputDevice"),
                    IcoPath = deviceIcon,
                    Score = 95000,
                    Action = _ => { _context.API.ChangeQuery($"{_currentActionKeyword} out "); return false; }
                });

                HashSet<string> displayedApps = new(StringComparer.OrdinalIgnoreCase);

                var validSessions = _sessionCache.Values.Where(c => c.IsValid).ToList();
                if (validSessions.Count > 0)
                {
                    var grouped = validSessions
                        .GroupBy(s => s.RealAppName)
                        .ToDictionary(g => g.Key, g => g.OrderByDescending(s => s.IsPlaying).First());

                    foreach (var kvp in grouped)
                    {
                        string realAppName = kvp.Key;
                        var cache = kvp.Value;
                        
                        if (string.IsNullOrWhiteSpace(cache.Title) && GetProcessSafe(realAppName) == null) continue;

                        displayedApps.Add(realAppName);

                        string title = cache.Title;
                        if (!string.IsNullOrEmpty(title) && !string.IsNullOrEmpty(cache.Artist))
                            title = $"{title} - {cache.Artist}";

                        Process? process = GetProcessSafe(realAppName);
                        if (string.IsNullOrEmpty(title) && process != null && !string.IsNullOrEmpty(process.MainWindowTitle))
                            title = process.MainWindowTitle;

                        int vol = 100;
                        var audioSession = FindSession(realAppName, device);
                        if (audioSession != null)
                            vol = (int)Math.Round(audioSession.SimpleAudioVolume.Volume * 100);
                        
                        string ico = process != null ? GetIcon(process) : "Images\\play.png";

                        string subFormat = cache.IsPlaying ? Tr("appPlaying") : Tr("appPaused");
                        results.Add(new Result
                        {
                            Title = string.IsNullOrEmpty(title) ? realAppName : title,
                            SubTitle = string.Format(subFormat, realAppName, vol),
                            IcoPath = ico,
                            Score = cache.IsPlaying ? 85000 : 75000,
                            ContextData = process?.Id,
                            Action = _ => { _context.API.ChangeQuery($"{_currentActionKeyword} {realAppName} "); return false; }
                        });
                    }
                }

                var audioSessions = device.AudioSessionManager.Sessions;
                for (int i = 0; i < audioSessions.Count; i++)
                {
                    var session = audioSessions[i];
                    
                    if (session.IsSystemSoundsSession)
                    {
                        results.Add(new Result
                        {
                            Title = string.Format(Tr("systemSounds"), (int)Math.Round(session.SimpleAudioVolume.Volume * 100)),
                            IcoPath = deviceIcon,
                            Score = 90000,
                            Action = _ => { _context.API.ChangeQuery($"{_currentActionKeyword} sys "); return false; }
                        });
                        continue;
                    }

                    if ((int)session.State != 1) continue;

                    try
                    {
                        var proc = Process.GetProcessById((int)session.GetProcessID);
                        string procName = proc.ProcessName;
                        string lowerName = procName.ToLower();

                        if (_blacklist.Contains(lowerName)) continue;

                        string normalized = NormalizeAppId(lowerName);
                        if (displayedApps.Contains(lowerName) || displayedApps.Contains(normalized)) continue;

                        int vol = (int)Math.Round(session.SimpleAudioVolume.Volume * 100);
                        string title = !string.IsNullOrEmpty(proc.MainWindowTitle) ? proc.MainWindowTitle : procName;

                        results.Add(new Result
                        {
                            Title = title,
                            SubTitle = string.Format(Tr("appVolumeOnly"), procName, vol),
                            IcoPath = GetIcon(proc),
                            Score = 65000,
                            ContextData = proc.Id,
                            Action = _ => { _context.API.ChangeQuery($"{_currentActionKeyword} {lowerName} "); return false; }
                        });
                    }
                    catch { continue; }
                }

                return ReturnAndCache(results);
            }

            // ---------- 二级菜单 ----------
            string targetApp = parts[0];

            if (targetApp == "out")
            {
                foreach (var ep in _audioEnumerator.EnumerateAudioEndPoints(DataFlow.Render, DeviceState.Active))
                {
                    bool isCurrent = ep.ID == device.ID;
                    string epNameLower = ep.FriendlyName.ToLower();
                    bool epIsHeadphone = epNameLower.Contains("headphone") || epNameLower.Contains("耳机") || epNameLower.Contains("ear") || epNameLower.Contains("buds") || epNameLower.Contains("airpods") || epNameLower.Contains("headset");
                    
                    string epId = ep.ID; 
                    results.Add(new Result
                    {
                        Title = ep.FriendlyName,
                        SubTitle = isCurrent ? Tr("inUse") : Tr("clickToSwitch"),
                        IcoPath = epIsHeadphone ? "Images\\headphone.png" : "Images\\device.png",
                        Action = _ =>
                        {
                            if (!isCurrent) SetDefaultAudioDevice(epId);
                            return true;
                        }
                    });
                }
                return ReturnAndCache(results);
            }

            // 数字精确设定音量
            if (parts.Length > 1 && int.TryParse(parts[1], out int parsedVol))
            {
                int targetVol = Math.Clamp(parsedVol, 0, 100);
                results.Add(new Result
                {
                    Title = string.Format(Tr("setVolumeTo"), targetVol),
                    IcoPath = targetApp == "master" ? "Images\\app.png" : "Images\\device.png",
                    Score = 100000,
                    Action = _ => 
                    {
                        SetVolumeExact(targetApp, targetVol);
                        return true; 
                    }
                });
                return ReturnAndCache(results); 
            }

            bool isMuted = false;
            if (targetApp == "master")
                isMuted = device.AudioEndpointVolume.Mute;
            else
            {
                var s = FindSession(targetApp, device);
                if (s != null) isMuted = s.SimpleAudioVolume.Mute;
            }

            bool isPlayingFromSMTC = false;
            var targetCache = GetTargetCache(targetApp);
            var targetSmtcSession = targetCache?.Session;
            
            if (targetCache != null)
                isPlayingFromSMTC = targetCache.IsPlaying;
            else
            {
                var audioSess = FindSession(targetApp, device);
                if (audioSess != null) isPlayingFromSMTC = (int)audioSess.State == 1;
            }

            if (_lastToggleTime.TryGetValue(targetApp, out DateTime toggleTime) &&
                (DateTime.Now - toggleTime).TotalMilliseconds < 2000 &&
                _localPlayState.TryGetValue(targetApp, out bool cachedState))
            {
                isPlayingFromSMTC = cachedState;
            }

            if (targetApp != "master" && targetApp != "sys")
            {
                results.Add(new Result
                {
                    Title = isPlayingFromSMTC ? Tr("pause") : Tr("play"),
                    IcoPath = isPlayingFromSMTC ? "Images\\pause.png" : "Images\\play.png",
                    Score = 100000,
                    Action = c => 
                    {
                        // 1. 本地立刻变动 UI，防呆显示
                        bool newState = !isPlayingFromSMTC;
                        _localPlayState[targetApp] = newState;
                        _lastToggleTime[targetApp] = DateTime.Now;

                        // 立刻强刷一次
                        if (!string.IsNullOrEmpty(_lastRawQuery))
                            _context.API.ChangeQuery(_lastRawQuery, true);

                        // 2. 后台异步执行真实命令，并在之后重置兜底
                        Task.Run(async () =>
                        {
                            if (targetSmtcSession != null)
                                await targetSmtcSession.TryTogglePlayPauseAsync();
                            else
                                SendAppCommand(APPCOMMAND_MEDIA_PLAY_PAUSE);
                            
                            await Task.Delay(400); // 给系统一点反应时间

                            // 销毁预测记录，这样下一次 Query 必读系统底层真实状态
                            _lastToggleTime.TryRemove(targetApp, out _);

                            // 最后兜底强刷一次。如果系统操作失败了，这里会自动拉回原始状态
                            if (!string.IsNullOrEmpty(_lastRawQuery))
                                _context.API.ChangeQuery(_lastRawQuery, true);
                        });

                        return false;
                    }
                });
                results.Add(new Result { Title = Tr("previous"), IcoPath = "Images\\prev.png", Score = 90000, Action = _ => { SendAppCommand(APPCOMMAND_MEDIA_PREVIOUSTRACK); return false; } });
                results.Add(new Result { Title = Tr("next"), IcoPath = "Images\\next.png", Score = 80000, Action = _ => { SendAppCommand(APPCOMMAND_MEDIA_NEXTTRACK); return false; } });
            }

            results.Add(new Result { Title = Tr("volumeUp"), IcoPath = "Images\\vol_up.png", Score = 70000, Action = _ => { AdjustVolumeRelative(targetApp, 10); return false; } });
            results.Add(new Result { Title = Tr("volumeDown"), IcoPath = "Images\\vol_down.png", Score = 60000, Action = _ => { AdjustVolumeRelative(targetApp, -10); return false; } });
            
            results.Add(new Result
            {
                Title = isMuted ? Tr("unmute") : Tr("mute"),
                IcoPath = isMuted ? "Images\\unmute.png" : "Images\\mute.png",
                Score = 50000,
                Action = _ =>
                {
                    ToggleMute(targetApp);
                    return false;
                }
            });

            // ================= “跳转到应用” =================
            if (targetApp != "master" && targetApp != "sys" && targetApp != "out")
            {
                Process? targetProc = null;
                if (targetCache != null && !string.IsNullOrEmpty(targetCache.RealAppName))
                    targetProc = GetProcessSafe(targetCache.RealAppName);
                if (targetProc == null)
                    targetProc = GetProcessSafe(targetApp);

                if (targetProc != null)
                {
                    int pid = targetProc.Id;
                    string pName = targetProc.ProcessName;
                    results.Add(new Result
                    {
                        Title = string.Format(Tr("jumpTo"), pName),
                        IcoPath = GetIcon(targetProc),
                        Score = 1000, 
                        Action = _ =>
                        {
                            try
                            {
                                var p = Process.GetProcessById(pid);
                                IntPtr h = p.MainWindowHandle;
                                if (h != IntPtr.Zero)
                                {
                                    if (IsIconic(h)) ShowWindowAsync(h, 9);
                                    SetForegroundWindow(h);
                                }
                            }
                            catch { }
                            return true; 
                        }
                    });
                }
            }

            return ReturnAndCache(results);
        }

        public List<Result> LoadContextMenus(Result selectedResult)
        {
            if (selectedResult.ContextData is int pid)
            {
                string pName = Tr("appDefaultName");
                try { pName = Process.GetProcessById(pid).ProcessName; } catch { }

                return new List<Result>
                {
                    new Result
                    {
                        Title = string.Format(Tr("jumpTo"), pName),
                        IcoPath = selectedResult.IcoPath,
                        Action = _ =>
                        {
                            try
                            {
                                var p = Process.GetProcessById(pid);
                                IntPtr h = p.MainWindowHandle;
                                if (h != IntPtr.Zero)
                                {
                                    if (IsIconic(h)) ShowWindowAsync(h, 9);
                                    SetForegroundWindow(h);
                                }
                            }
                            catch { }
                            return true;
                        }
                    }
                };
            }
            return new List<Result>();
        }

        // ================= 核心科技：WM_APPCOMMAND 系统级消息投递 =================
        private void SendAppCommand(int command)
        {
            IntPtr hWnd = GetForegroundWindow();
            SendMessageW(hWnd, WM_APPCOMMAND, hWnd, (IntPtr)(command << 16));
        }

        private MediaSessionCache? GetTargetCache(string targetApp)
        {
            var validCaches = _sessionCache.Values.Where(s => s.IsValid).ToList();
            if (!validCaches.Any()) return null;

            var exact = validCaches.FirstOrDefault(s => string.Equals(s.RealAppName, targetApp, StringComparison.OrdinalIgnoreCase));
            if (exact != null) return exact;

            var contains = validCaches.FirstOrDefault(s => s.RealAppName.Contains(targetApp, StringComparison.OrdinalIgnoreCase));
            if (contains != null) return contains;

            return validCaches.FirstOrDefault(s => s.IsPlaying) ?? validCaches.FirstOrDefault();
        }

        private string GetIcon(Process process)
        {
            string name = process.ProcessName;
            if (_iconMemoryCache.TryGetValue(name, out string? cached) && File.Exists(cached))
                return cached;

            try
            {
                string cacheDir = Path.Combine(_context.CurrentPluginMetadata.PluginDirectory, "Cache");
                if (!Directory.Exists(cacheDir)) Directory.CreateDirectory(cacheDir);
                string iconPath = Path.Combine(cacheDir, $"{name}.png");
                if (File.Exists(iconPath))
                {
                    _iconMemoryCache[name] = iconPath;
                    return iconPath;
                }

                string? exePath = null;
                try { exePath = process.MainModule?.FileName; } catch { }
                
                if (string.IsNullOrEmpty(exePath)) return "Images\\play.png";
                using Icon? icon = Icon.ExtractAssociatedIcon(exePath);
                if (icon != null)
                {
                    using Bitmap bmp = icon.ToBitmap();
                    bmp.Save(iconPath, ImageFormat.Png);
                    _iconMemoryCache[name] = iconPath;
                    return iconPath;
                }
            }
            catch { }
            return "Images\\play.png";
        }

        // ================= 精准控音核心引擎 =================
        private void SetVolumeExact(string appName, int target)
        {
            target = Math.Clamp(target, 0, 100);
            using var actionDevice = _audioEnumerator.GetDefaultAudioEndpoint(DataFlow.Render, Role.Multimedia);
            
            if (appName == "master")
            {
                // 使用 WM_APPCOMMAND 阶梯触发法
                if (target > 0)
                {
                    actionDevice.AudioEndpointVolume.MasterVolumeLevelScalar = Math.Clamp((target - 2) / 100f, 0f, 1f);
                    SendAppCommand(APPCOMMAND_VOLUME_UP);
                }
                else
                {
                    actionDevice.AudioEndpointVolume.MasterVolumeLevelScalar = 0.02f;
                    SendAppCommand(APPCOMMAND_VOLUME_DOWN);
                }
            }
            else
            {
                var s = FindSession(appName, actionDevice);
                if (s != null) s.SimpleAudioVolume.Volume = target / 100f;
            }
        }

        private void AdjustVolumeRelative(string appName, int delta)
        {
            int currentVol = 0;
            using var actionDevice = _audioEnumerator.GetDefaultAudioEndpoint(DataFlow.Render, Role.Multimedia);
            
            if (appName == "master")
            {
                currentVol = (int)Math.Round(actionDevice.AudioEndpointVolume.MasterVolumeLevelScalar * 100);
            }
            else
            {
                var s = FindSession(appName, actionDevice);
                if (s != null) currentVol = (int)Math.Round(s.SimpleAudioVolume.Volume * 100);
            }
            
            SetVolumeExact(appName, currentVol + delta); 
        }

        private void ToggleMute(string appName)
        {
            if (appName == "master") SendAppCommand(APPCOMMAND_VOLUME_MUTE);
            else
            {
                using var actionDevice = _audioEnumerator.GetDefaultAudioEndpoint(DataFlow.Render, Role.Multimedia);
                var s = FindSession(appName, actionDevice);
                if (s != null) s.SimpleAudioVolume.Mute = !s.SimpleAudioVolume.Mute;
            }
        }

        private AudioSessionControl? FindSession(string appName, MMDevice device)
        {
            var sessions = device.AudioSessionManager.Sessions;
            for (int i = 0; i < sessions.Count; i++)
            {
                var s = sessions[i];
                if (s == null || s.IsSystemSoundsSession) continue;
                try
                {
                    var proc = Process.GetProcessById((int)s.GetProcessID);
                    if (proc.ProcessName.Contains(appName, StringComparison.OrdinalIgnoreCase))
                        return s;
                }
                catch { }
            }
            return null;
        }

        private void CleanupStaleCache()
        {
            var now = DateTime.Now;
            foreach (var key in _lastToggleTime.Keys.ToList())
            {
                if ((now - _lastToggleTime[key]).TotalSeconds > 5)
                {
                    _lastToggleTime.TryRemove(key, out _);
                    _localPlayState.TryRemove(key, out _);
                }
            }
        }

        [ComImport, Guid("870AF99C-171D-4F9E-AF0D-E63DF40C2BC9"), InterfaceType(ComInterfaceType.InterfaceIsIUnknown)]
        private interface IPolicyConfig
        {
            void G1(); void G2(); void G3(); void G4(); void G5(); void G6();
            void G7(); void G8(); void G9(); void G10();
            void SetDefaultEndpoint([MarshalAs(UnmanagedType.LPWStr)] string id, Role r);
            void G11();
        }
        [ComImport, Guid("870AF99C-171D-4F9E-AF0D-E63DF40C2BC9")]
        private class PolicyConfigClient { }

        private void SetDefaultAudioDevice(string id)
        {
            try
            {
                var config = (IPolicyConfig)new PolicyConfigClient();
                config.SetDefaultEndpoint(id, Role.Multimedia);
                config.SetDefaultEndpoint(id, Role.Communications);
            }
            catch { }
        }
    }
}