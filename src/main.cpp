/**
 * M5StickS3 Firmware v6.0
 * NVS Engine · MQTT State Bus · Bus/Stock/Weather Modules · Carousel UI
 */
#include <Arduino.h>
#include <WiFi.h>
#include <HTTPClient.h>
#include <PubSubClient.h>
#include <ArduinoJson.h>
#include <Preferences.h>
#include <time.h>
#include <qrcode.h>
#include <M5Unified.h>

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------
static constexpr int PORTRAIT_W = 135;
static constexpr int PORTRAIT_H = 240;
static constexpr int LAND_W = 240;
static constexpr int LAND_H = 135;
static constexpr const char* FW_VERSION = "6.0.0";
static constexpr const char* MQTT_HOST = "broker.hivemq.com";
static constexpr uint16_t MQTT_PORT = 1883;
static constexpr size_t MQTT_BUFFER_SIZE = 4096;
static constexpr const char* NTP_SERVER = "pool.ntp.org";
static constexpr long GMT_OFFSET_SEC = 8 * 3600;
static constexpr int DAYLIGHT_OFFSET_SEC = 0;
static constexpr uint32_t ETA_REFRESH_MS = 30000;
static constexpr uint32_t STATE_PUBLISH_MS = 10000;
static constexpr uint32_t MULTI_CLICK_MS = 600;
static constexpr uint32_t LONG_PRESS_MS = 1500;
static constexpr uint8_t MULTI_CLICK_TARGET = 5;
static constexpr int PROFILE_COUNT = 4;
static constexpr int STOCK_SLOTS = 4;
static constexpr int CAROUSEL_CARDS = 7;
static constexpr int STOCK_HISTORY_MAX = 48;
static constexpr int FORECAST_MAX = 9;
static constexpr int WARNING_MAX = 8;
static constexpr int ETA_SLOTS = 3;

static const uint16_t C_BG = 0x0000;
static const uint16_t C_FG = 0xFFFF;
static const uint16_t C_DIM = 0x7BEF;
static const uint16_t C_GREEN = 0x07E0;
static const uint16_t C_RED = 0xF800;
static const uint16_t C_AMBER = 0xFD20;
static const uint16_t C_CYAN = 0x07FF;
static const uint16_t C_WARN_BG = 0xFFE0;
static const uint16_t C_WARN_FG = 0x0000;

// Static memory shield — ArduinoJson v7
static JsonDocument g_jsonDoc;
static char g_mqttPayload[MQTT_BUFFER_SIZE];

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------
enum class AppMode : uint8_t { Bus = 0, Stock, Weather, Count };
enum class UiScreen : uint8_t { Module, Carousel, QrCode };

struct BusStopCfg {
    char co[4] = "KMB";
    char route[12] = "";
    char stop[24] = "";
    char svc[4] = "1";
    char bound[2] = "O";
    char name[32] = "";
    char dest[32] = "";
};

struct BusProfile {
    char name[24] = "";
    BusStopCfg busA;
    BusStopCfg busB;
};

struct StockSlot {
    char symbol[16] = "";
    char name[24] = "";
};

struct WifiCfg {
    char ssid[33] = "";
    char password[65] = "";
};

struct DeviceSettings {
    uint8_t bright = 1;
    uint8_t timeout = 1;
    bool english = false;
    AppMode appMode = AppMode::Bus;
    WifiCfg wifi;
    StockSlot stocks[STOCK_SLOTS];
    int activeStock = 0;
};

struct EtaEntry { char dest[24] = ""; int minutes = -1; bool valid = false; };
struct BusColState { EtaEntry slots[ETA_SLOTS]; char route[12] = ""; char stop[20] = ""; bool ok = false; };

struct WeatherWarning { char code[12] = ""; char name[40] = ""; };
struct ForecastDay {
    char date[10] = "";
    char week[6] = "";
    int minT = 0, maxT = 0, psr = 0;
    char desc[32] = "";
};

struct WeatherState {
    bool has = false;
    int temp = 0, humidity = 0;
    int warnCount = 0;
    WeatherWarning warns[WARNING_MAX];
    int fcCount = 0;
    ForecastDay fc[FORECAST_MAX];
};

struct StockState {
    bool has = false;
    char symbol[16] = "";
    char name[24] = "";
    float price = 0, change = 0, changePct = 0, prevClose = 0;
    int histCount = 0;
    float hist[STOCK_HISTORY_MAX];
};

// Globals
static DeviceSettings g_cfg;
static BusProfile g_profiles[PROFILE_COUNT];
static int g_activeProfile = 0;
static BusColState g_colA, g_colB;
static WeatherState g_weather;
static StockState g_stock;
static String g_deviceId;
static Preferences g_prefs;
static WiFiClient g_wifiClient;
static PubSubClient g_mqtt(g_wifiClient);
static M5Canvas g_canvas(&M5.Display);

static const uint16_t C_DARKGREY = 0x4208;

static UiScreen g_ui = UiScreen::Module;
static int g_menuCardIdx = 0;
static bool g_weatherForecastView = false;
static uint32_t g_lastActivity = 0, g_lastEta = 0, g_lastState = 0;
static bool g_bootTasksDone = false;
static uint8_t g_etaStep = 0;
static uint32_t g_wifiTryMs = 0;
static bool g_ntpDone = false;
static bool g_mqttOk = false;
static char g_lastAction[20] = "";
static uint32_t g_lastActionSeq = 0;
static bool g_frameDirty = true;
static uint32_t g_lastFrameMs = 0;
static uint32_t g_lastFrameHash = 0;

static constexpr int BUS_COL_A_X = 60;
static constexpr int BUS_COL_B_X = 180;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------
static void touch() {
    g_lastActivity = millis();
    g_frameDirty = true;
}

static uint16_t etaColor(int mins) {
    if (mins <= 5) return TFT_RED;
    if (mins <= 10) return TFT_ORANGE;
    return TFT_GREEN;
}

static void drawMc(M5Canvas& c, const lgfx::IFont* font, const char* text, int cx, int cy, uint16_t col) {
    c.setFont(font);
    c.setTextColor(col);
    c.setTextDatum(textdatum_t::middle_center);
    c.drawString(text, cx, cy);
    c.setTextDatum(textdatum_t::top_left);
}

static uint32_t computeFrameHash() {
    uint32_t h = 0x811c9dc5;
    auto mix = [&](uint32_t v) { h ^= v; h *= 0x01000193; };
    mix((uint32_t)g_ui);
    mix((uint32_t)g_cfg.appMode);
    mix((uint32_t)g_menuCardIdx);
    mix((uint32_t)g_activeProfile);
    mix((uint32_t)g_cfg.activeStock);
    mix(g_weatherForecastView ? 1u : 0u);
    mix(g_cfg.english ? 1u : 0u);
    mix(g_cfg.bright);
    mix(g_cfg.timeout);
    mix(g_stock.has ? 1u : 0u);
    if (g_stock.has) mix((uint32_t)(g_stock.price * 100));
    mix(g_weather.has ? 1u : 0u);
    if (g_cfg.appMode == AppMode::Bus && g_ui == UiScreen::Module) {
        for (int i = 0; i < ETA_SLOTS; ++i) {
            mix((uint32_t)g_colA.slots[i].minutes);
            mix(g_colA.slots[i].valid ? 1u : 0u);
            mix((uint32_t)g_colB.slots[i].minutes);
            mix(g_colB.slots[i].valid ? 1u : 0u);
        }
        mix((uint32_t)(time(nullptr) / 60));
    }
    return h;
}

static bool shouldRenderFrame() {
    uint32_t now = millis();
    uint32_t hash = computeFrameHash();
    if (!g_frameDirty && hash == g_lastFrameHash) return false;
    if (g_lastFrameMs && (now - g_lastFrameMs) < 100) return false;
    g_frameDirty = false;
    g_lastFrameHash = hash;
    g_lastFrameMs = now;
    return true;
}

static uint8_t brightVal() {
    static const uint8_t lv[] = {64, 128, 192, 255};
    return lv[g_cfg.bright > 3 ? 1 : g_cfg.bright];
}

static void wakeDisplay() {
    M5.Display.wakeup();
    M5.Display.setBrightness(brightVal());
}

static void drawBootSplash() {
    wakeDisplay();
    M5.Display.fillScreen(C_BG);
    M5.Display.setTextColor(C_CYAN);
    M5.Display.setTextSize(2);
    M5.Display.setCursor(8, 90);
    M5.Display.print("M5 Bus v6");
    M5.Display.setTextSize(1);
    M5.Display.setTextColor(C_DIM);
    M5.Display.setCursor(8, 115);
    M5.Display.print(g_cfg.english ? "Starting..." : "啟動中...");
    touch();
}

static uint32_t timeoutMs() {
    static const uint32_t t[] = {15000, 30000, 60000, 0};
    return t[g_cfg.timeout > 3 ? 1 : g_cfg.timeout];
}

static const char* modeStr(AppMode m) {
    switch (m) {
        case AppMode::Bus: return "bus";
        case AppMode::Stock: return "stock";
        case AppMode::Weather: return "weather";
        default: return "bus";
    }
}

static AppMode modeFrom(const char* s) {
    if (!s) return AppMode::Bus;
    if (!strcmp(s, "stock")) return AppMode::Stock;
    if (!strcmp(s, "weather")) return AppMode::Weather;
    return AppMode::Bus;
}

static String topic(const char* suffix) {
    return String("m5bus_") + g_deviceId + "/" + suffix;
}

static int etaMins(const char* iso) {
    if (!iso) return -1;
    int y, mo, d, h, mi, s;
    if (sscanf(iso, "%d-%d-%dT%d:%d:%d", &y, &mo, &d, &h, &mi, &s) < 6) return -1;
    struct tm t = {};
    t.tm_year = y - 1900; t.tm_mon = mo - 1; t.tm_mday = d;
    t.tm_hour = h; t.tm_min = mi; t.tm_sec = s; t.tm_isdst = -1;
    time_t eta = mktime(&t);
    time_t now = time(nullptr);
    if (eta <= 0 || now <= 0) return -1;
    return (int)lround(difftime(eta, now) / 60.0);
}

static int batteryPct() {
    int mv = M5.Power.getBatteryVoltage();
    if (mv <= 0) return -1;
    int p = map(mv, 3300, 4200, 0, 100);
    return constrain(p, 0, 100);
}

static bool g_spriteLandscape = false;

static void ensureSpriteLayout(bool landscape) {
    const int rot = landscape ? 1 : 2;
    const int w = landscape ? LAND_W : PORTRAIT_W;
    const int h = landscape ? LAND_H : PORTRAIT_H;
    M5.Display.setRotation(rot);
    if (!g_canvas.getBuffer() || g_spriteLandscape != landscape ||
        g_canvas.width() != w || g_canvas.height() != h) {
        if (g_canvas.getBuffer()) g_canvas.deleteSprite();
        g_canvas.setColorDepth(16);
        g_canvas.createSprite(w, h);
        g_spriteLandscape = landscape;
    }
}

static void drawCenteredText(M5Canvas& c, int w, int y, const char* text, uint16_t col) {
    c.setFont(&fonts::Font0);
    c.setTextSize(1);
    c.setTextColor(col);
    int tw = c.textWidth(text);
    c.setCursor((w - tw) / 2, y);
    c.print(text);
}

static void drawCenteredEfont(M5Canvas& c, int w, int y, const char* text, uint16_t col) {
    c.setFont(&fonts::efontTW_12);
    c.setTextColor(col);
    int tw = c.textWidth(text);
    c.setCursor((w - tw) / 2, y);
    c.print(text);
}

static void drawRightEfont(M5Canvas& c, int rightX, int y, const char* text, uint16_t col) {
    c.setFont(&fonts::efontTW_12);
    c.setTextColor(col);
    int tw = c.textWidth(text);
    c.setCursor(rightX - tw, y);
    c.print(text);
}

static bool frameIsLandscape() {
    if (g_ui == UiScreen::Carousel || g_ui == UiScreen::QrCode) return false;
    return g_cfg.appMode == AppMode::Bus || g_cfg.appMode == AppMode::Stock;
}

// ---------------------------------------------------------------------------
// NVS / Embedded DB
// ---------------------------------------------------------------------------
static void saveNvs() {
    g_jsonDoc.clear();
    g_jsonDoc["v"] = 6;
    g_jsonDoc["active_module"] = modeStr(g_cfg.appMode);
    g_jsonDoc["active_profile"] = g_activeProfile;
    g_jsonDoc["active_stock"] = g_cfg.activeStock;

    auto writeBusProfile = [](JsonObject p, const BusProfile& pr) {
        p["name"] = pr.name;
        auto wb = [&](const char* k, const BusStopCfg& b) {
            JsonObject o = p[k].to<JsonObject>();
            o["co"] = b.co; o["route"] = b.route; o["stop"] = b.stop;
            o["svc"] = b.svc; o["bound"] = b.bound; o["name"] = b.name;
            o["dest"] = b.dest;
        };
        wb("busA", pr.busA);
        wb("busB", pr.busB);
    };

    JsonArray profiles = g_jsonDoc["profiles"].to<JsonArray>();
    for (int i = 0; i < PROFILE_COUNT; ++i) {
        JsonObject p = profiles.add<JsonObject>();
        writeBusProfile(p, g_profiles[i]);
    }

    JsonObject mods = g_jsonDoc["modules"].to<JsonObject>();
    JsonObject bus = mods["bus"].to<JsonObject>();
    bus["active_profile"] = g_activeProfile;
    JsonArray busProfiles = bus["profiles"].to<JsonArray>();
    for (int i = 0; i < PROFILE_COUNT; ++i) {
        JsonObject p = busProfiles.add<JsonObject>();
        p["id"] = i;
        writeBusProfile(p, g_profiles[i]);
    }
    JsonObject stock = mods["stock"].to<JsonObject>();
    stock["active_stock"] = g_cfg.activeStock;
    JsonArray watchlist = stock["watchlist"].to<JsonArray>();
    for (int i = 0; i < STOCK_SLOTS; ++i) {
        JsonObject st = watchlist.add<JsonObject>();
        st["symbol"] = g_cfg.stocks[i].symbol;
        st["name"] = g_cfg.stocks[i].name;
    }

    JsonObject s = g_jsonDoc["settings"].to<JsonObject>();
    s["bright"] = g_cfg.bright;
    s["timeout"] = g_cfg.timeout;
    s["english"] = g_cfg.english;
    s["app_mode"] = modeStr(g_cfg.appMode);
    s["wifi"]["ssid"] = g_cfg.wifi.ssid;
    s["wifi"]["password"] = g_cfg.wifi.password;
    JsonArray stocks = s["stocks"].to<JsonArray>();
    for (int i = 0; i < STOCK_SLOTS; ++i) {
        JsonObject st = stocks.add<JsonObject>();
        st["symbol"] = g_cfg.stocks[i].symbol;
        st["name"] = g_cfg.stocks[i].name;
    }
    String out;
    serializeJson(g_jsonDoc, out);
    g_prefs.putString("db_json", out);
}

static void readBus(JsonObjectConst o, BusStopCfg& b) {
    if (o["co"].is<const char*>()) strlcpy(b.co, o["co"], sizeof(b.co));
    if (o["route"].is<const char*>()) strlcpy(b.route, o["route"], sizeof(b.route));
    if (o["stop"].is<const char*>()) strlcpy(b.stop, o["stop"], sizeof(b.stop));
    if (o["stop_id"].is<const char*>()) strlcpy(b.stop, o["stop_id"], sizeof(b.stop));
    if (o["svc"].is<const char*>()) strlcpy(b.svc, o["svc"], sizeof(b.svc));
    if (o["bound"].is<const char*>()) strlcpy(b.bound, o["bound"], sizeof(b.bound));
    if (o["name"].is<const char*>()) strlcpy(b.name, o["name"], sizeof(b.name));
    if (o["dest"].is<const char*>()) strlcpy(b.dest, o["dest"], sizeof(b.dest));
}

static void applyBusProfiles(JsonArrayConst arr) {
    int i = 0;
    for (JsonObjectConst p : arr) {
        if (i >= PROFILE_COUNT) break;
        if (p["name"].is<const char*>()) strlcpy(g_profiles[i].name, p["name"], sizeof(g_profiles[i].name));
        if (p["busA"].is<JsonObjectConst>()) readBus(p["busA"], g_profiles[i].busA);
        if (p["busB"].is<JsonObjectConst>()) readBus(p["busB"], g_profiles[i].busB);
        ++i;
    }
}

static void applyWatchlist(JsonArrayConst arr) {
    int i = 0;
    for (JsonObjectConst x : arr) {
        if (i >= STOCK_SLOTS) break;
        if (x["symbol"].is<const char*>()) strlcpy(g_cfg.stocks[i].symbol, x["symbol"], sizeof(g_cfg.stocks[i].symbol));
        if (x["name"].is<const char*>()) strlcpy(g_cfg.stocks[i].name, x["name"], sizeof(g_cfg.stocks[i].name));
        ++i;
    }
}

static void applyConfig(const char* json, size_t len) {
    g_jsonDoc.clear();
    if (deserializeJson(g_jsonDoc, json, len)) return;

    const char* activeMod = g_jsonDoc["active_module"] | nullptr;
    (void)activeMod; // v6: active_module 只標示 CRM 分頁，不切換裝置畫面

    if (g_jsonDoc["active_profile"].is<int>()) g_activeProfile = g_jsonDoc["active_profile"];
    if (g_jsonDoc["active_stock"].is<int>()) g_cfg.activeStock = g_jsonDoc["active_stock"];

    if (g_jsonDoc["profiles"].is<JsonArrayConst>())
        applyBusProfiles(g_jsonDoc["profiles"].as<JsonArrayConst>());

    JsonObjectConst mods = g_jsonDoc["modules"];
    if (!mods.isNull()) {
        JsonObjectConst bus = mods["bus"];
        if (!bus.isNull()) {
            if (bus["active_profile"].is<int>()) g_activeProfile = bus["active_profile"];
            if (bus["profiles"].is<JsonArrayConst>())
                applyBusProfiles(bus["profiles"].as<JsonArrayConst>());
        }
        JsonObjectConst stock = mods["stock"];
        if (!stock.isNull()) {
            if (stock["active_stock"].is<int>()) g_cfg.activeStock = stock["active_stock"];
            if (stock["watchlist"].is<JsonArrayConst>())
                applyWatchlist(stock["watchlist"].as<JsonArrayConst>());
        }
    }

    if (g_jsonDoc["busA"].is<JsonObjectConst>()) readBus(g_jsonDoc["busA"], g_profiles[g_activeProfile].busA);
    if (g_jsonDoc["busB"].is<JsonObjectConst>()) readBus(g_jsonDoc["busB"], g_profiles[g_activeProfile].busB);

    JsonObjectConst st = g_jsonDoc["settings"];
    if (!st.isNull()) {
        if (st["bright"].is<int>()) g_cfg.bright = st["bright"];
        if (st["timeout"].is<int>()) g_cfg.timeout = st["timeout"];
        if (st["english"].is<bool>()) g_cfg.english = st["english"];
        // app_mode 僅由裝置按鍵/選單切換，MQTT 不覆寫
        if (st["wifi"]["ssid"].is<const char*>()) strlcpy(g_cfg.wifi.ssid, st["wifi"]["ssid"], sizeof(g_cfg.wifi.ssid));
        if (st["wifi"]["password"].is<const char*>()) strlcpy(g_cfg.wifi.password, st["wifi"]["password"], sizeof(g_cfg.wifi.password));
        if (st["stocks"].is<JsonArrayConst>()) applyWatchlist(st["stocks"].as<JsonArrayConst>());
    }
    M5.Display.setBrightness(brightVal());
    saveNvs();
}

static void loadNvs() {
    String json = g_prefs.getString("db_json", "");
    if (json.length()) applyConfig(json.c_str(), json.length());
    if (g_profiles[0].busA.route[0] == '\0') {
        strlcpy(g_profiles[0].name, g_cfg.english ? "Commute" : "返工", sizeof(g_profiles[0].name));
        strlcpy(g_profiles[0].busA.co, "KMB", sizeof(g_profiles[0].busA.co));
        strlcpy(g_profiles[0].busA.route, "76K", sizeof(g_profiles[0].busA.route));
        strlcpy(g_profiles[0].busA.stop, "68C988CE5394BAE7", sizeof(g_profiles[0].busA.stop));
        strlcpy(g_profiles[0].busA.name, g_cfg.english ? "Long Ping" : "朗屏", sizeof(g_profiles[0].busA.name));
        strlcpy(g_profiles[0].busA.dest, g_profiles[0].busA.name, sizeof(g_profiles[0].busA.dest));
        strlcpy(g_profiles[0].busB.co, "KMB", sizeof(g_profiles[0].busB.co));
        strlcpy(g_profiles[0].busB.route, "76K", sizeof(g_profiles[0].busB.route));
        strlcpy(g_profiles[0].busB.stop, "B0D79D5CE512B9EC", sizeof(g_profiles[0].busB.stop));
        strlcpy(g_profiles[0].busB.name, g_cfg.english ? "Sheung Shui" : "上水", sizeof(g_profiles[0].busB.name));
        strlcpy(g_profiles[0].busB.dest, g_profiles[0].busB.name, sizeof(g_profiles[0].busB.dest));
        strlcpy(g_cfg.stocks[0].symbol, "0700.HK", sizeof(g_cfg.stocks[0].symbol));
        strlcpy(g_cfg.stocks[0].name, "Tencent", sizeof(g_cfg.stocks[0].name));
    }
}

// ---------------------------------------------------------------------------
// HTTP ETA
// ---------------------------------------------------------------------------
static bool httpGet(const String& url, String& out) {
    if (WiFi.status() != WL_CONNECTED) return false;
    HTTPClient http;
    http.setTimeout(5000);
    if (!http.begin(url)) return false;
    int code = http.GET();
    if (code != 200) { http.end(); return false; }
    out = http.getString();
    http.end();
    return true;
}

static void parseEta(const String& body, BusColState& col) {
    g_jsonDoc.clear();
    if (deserializeJson(g_jsonDoc, body)) return;
    int slot = 0;
    for (JsonObject item : g_jsonDoc["data"].as<JsonArray>()) {
        if (slot >= ETA_SLOTS) break;
        const char* iso = item["eta"];
        int m = etaMins(iso);
        if (m < 0) continue;
        const char* dest = item["dest_tc"] | item["dest_en"] | "";
        strlcpy(col.slots[slot].dest, dest, sizeof(col.slots[slot].dest));
        col.slots[slot].minutes = m;
        col.slots[slot].valid = true;
        ++slot;
    }
    col.ok = slot > 0;
}

static void fetchCol(const BusStopCfg& cfg, BusColState& col) {
    memset(&col, 0, sizeof(col));
    strlcpy(col.route, cfg.route, sizeof(col.route));
    strlcpy(col.stop, cfg.name[0] ? cfg.name : cfg.stop, sizeof(col.stop));
    if (!cfg.route[0] || !cfg.stop[0]) return;
    String url;
    if (!strcmp(cfg.co, "CTB"))
        url = String("https://rt.data.gov.hk/v2/transport/citybus/eta/CTB/") + cfg.stop + "/" + cfg.route;
    else
        url = String("https://data.etabus.gov.hk/v1/transport/kmb/eta/") + cfg.stop + "/" + cfg.route + "/" + cfg.svc;
    String body;
    if (httpGet(url, body)) parseEta(body, col);
}

static void fetchAllEta() {
    g_etaStep = 1;
    g_lastEta = 0;
}

static void etaTick() {
    if (WiFi.status() != WL_CONNECTED) return;
    if (g_etaStep == 0 && millis() - g_lastEta < ETA_REFRESH_MS) return;
    if (g_etaStep == 0) g_etaStep = 1;
    if (g_etaStep == 1) {
        fetchCol(g_profiles[g_activeProfile].busA, g_colA);
        g_etaStep = 2;
        return;
    }
    if (g_etaStep == 2) {
        fetchCol(g_profiles[g_activeProfile].busB, g_colB);
        g_etaStep = 0;
        g_lastEta = millis();
        g_bootTasksDone = true;
        g_frameDirty = true;
    }
}

static void wifiTick() {
    if (!g_cfg.wifi.ssid[0]) return;
    if (WiFi.status() == WL_CONNECTED) {
        if (!g_ntpDone) {
            static uint32_t ntpStart = 0;
            if (!ntpStart) {
                configTime(GMT_OFFSET_SEC, DAYLIGHT_OFFSET_SEC, NTP_SERVER);
                ntpStart = millis();
            }
            if (time(nullptr) > 1700000000 || millis() - ntpStart > 5000) g_ntpDone = true;
        }
        return;
    }
    if (g_wifiTryMs && millis() - g_wifiTryMs < 10000) return;
    WiFi.mode(WIFI_STA);
    WiFi.begin(g_cfg.wifi.ssid, g_cfg.wifi.password);
    g_wifiTryMs = millis();
}

// ---------------------------------------------------------------------------
// MQTT payload parsers
// ---------------------------------------------------------------------------
static void applyWeather(const char* json, size_t len) {
    g_jsonDoc.clear();
    if (deserializeJson(g_jsonDoc, json, len)) return;
    g_weather.has = true;
    g_weather.temp = g_jsonDoc["current"]["temp"] | 0;
    g_weather.humidity = g_jsonDoc["current"]["humidity"] | 0;
    g_weather.warnCount = 0;
    for (JsonObject w : g_jsonDoc["warnings"].as<JsonArray>()) {
        if (g_weather.warnCount >= WARNING_MAX) break;
        auto& d = g_weather.warns[g_weather.warnCount++];
        strlcpy(d.code, w["code"] | "", sizeof(d.code));
        strlcpy(d.name, w["name"] | "", sizeof(d.name));
    }
    g_weather.fcCount = 0;
    for (JsonObject f : g_jsonDoc["forecast"].as<JsonArray>()) {
        if (g_weather.fcCount >= FORECAST_MAX) break;
        auto& d = g_weather.fc[g_weather.fcCount++];
        strlcpy(d.date, f["date"] | "", sizeof(d.date));
        strlcpy(d.week, f["week"] | "", sizeof(d.week));
        d.minT = f["min"] | 0; d.maxT = f["max"] | 0;
        d.psr = f["psr"] | 0;
        strlcpy(d.desc, f["desc"] | "", sizeof(d.desc));
    }
}

static void applyStock(const char* json, size_t len) {
    g_jsonDoc.clear();
    if (deserializeJson(g_jsonDoc, json, len)) return;
    g_stock.has = true;
    strlcpy(g_stock.symbol, g_jsonDoc["symbol"] | "", sizeof(g_stock.symbol));
    strlcpy(g_stock.name, g_jsonDoc["name"] | "", sizeof(g_stock.name));
    g_stock.price = g_jsonDoc["price"] | 0.0f;
    g_stock.change = g_jsonDoc["change"] | 0.0f;
    g_stock.changePct = g_jsonDoc["changePct"] | g_jsonDoc["change_pct"] | 0.0f;
    g_stock.prevClose = g_jsonDoc["prevClose"] | g_jsonDoc["prev_close"] | (g_stock.price - g_stock.change);
    g_stock.histCount = 0;
    for (JsonVariant v : g_jsonDoc["history"].as<JsonArray>()) {
        if (g_stock.histCount >= STOCK_HISTORY_MAX) break;
        g_stock.hist[g_stock.histCount++] = v.as<float>();
    }
}

// ---------------------------------------------------------------------------
// MQTT Hub
// ---------------------------------------------------------------------------
static void publishRefreshRequest(const char* type) {
    g_jsonDoc.clear();
    g_jsonDoc["type"] = type;
    g_jsonDoc["device"] = g_deviceId;
    g_jsonDoc["ts"] = (uint32_t)time(nullptr);
    size_t n = serializeJson(g_jsonDoc, g_mqttPayload, sizeof(g_mqttPayload));
    g_mqtt.publish(topic("request").c_str(), (const uint8_t*)g_mqttPayload, n, false);
}

static void publishState() {
    g_jsonDoc.clear();
    g_jsonDoc["live"] = true;
    g_jsonDoc["fw"] = FW_VERSION;
    g_jsonDoc["device"] = g_deviceId;
    g_jsonDoc["ip"] = WiFi.localIP().toString();
    g_jsonDoc["battery"] = batteryPct();
    g_jsonDoc["charging"] = M5.Power.isCharging();
    g_jsonDoc["screen"] = modeStr(g_cfg.appMode);
    g_jsonDoc["active_profile"] = g_activeProfile;
    g_jsonDoc["profile_name"] = g_profiles[g_activeProfile].name;
    g_jsonDoc["wifi"] = WiFi.status() == WL_CONNECTED;
    JsonObject wi = g_jsonDoc["wifi_info"].to<JsonObject>();
    wi["ssid"] = WiFi.SSID();
    wi["rssi"] = WiFi.RSSI();
  JsonObject settings = g_jsonDoc["settings"].to<JsonObject>();
    settings["bright"] = g_cfg.bright;
    settings["timeout"] = g_cfg.timeout;
    settings["english"] = g_cfg.english;
    settings["app_mode"] = modeStr(g_cfg.appMode);
    auto wb = [&](const char* k, const BusStopCfg& b) {
        JsonObject o = g_jsonDoc[k].to<JsonObject>();
        o["co"] = b.co; o["route"] = b.route; o["stop"] = b.stop;
        o["name"] = b.name;
        o["dest"] = b.dest;
    };
    wb("busA", g_profiles[g_activeProfile].busA);
    wb("busB", g_profiles[g_activeProfile].busB);
    if (g_lastAction[0]) {
        g_jsonDoc["last_action"] = g_lastAction;
        g_jsonDoc["last_action_seq"] = g_lastActionSeq;
    }
    size_t n = serializeJson(g_jsonDoc, g_mqttPayload, sizeof(g_mqttPayload));
    g_mqtt.publish(topic("state").c_str(), (const uint8_t*)g_mqttPayload, n, false);
}

static void mqttCallback(char* tpc, byte* payload, unsigned int len) {
    String t(tpc);
    if (t.endsWith("/config")) { applyConfig((const char*)payload, len); publishState(); return; }
    if (t.endsWith("/weather")) { applyWeather((const char*)payload, len); return; }
    if (t.endsWith("/stock")) { applyStock((const char*)payload, len); return; }
    if (!t.endsWith("/cmd")) return;
    g_jsonDoc.clear();
    if (deserializeJson(g_jsonDoc, payload, len)) return;
    const char* act = g_jsonDoc["action"] | "";
    uint32_t seq = g_jsonDoc["seq"] | 0;
    if (!strcmp(act, "refresh_eta")) fetchAllEta();
    else if (!strcmp(act, "reboot")) { strlcpy(g_lastAction, act, sizeof(g_lastAction)); g_lastActionSeq = seq; publishState(); delay(200); ESP.restart(); }
    else if (!strcmp(act, "set_profile")) { int p = g_jsonDoc["profile_id"] | 0; if (p >= 0 && p < PROFILE_COUNT) { g_activeProfile = p; saveNvs(); fetchAllEta(); } }
    else if (!strcmp(act, "scan_wifi")) {
        int n = WiFi.scanNetworks(false, true);
        g_jsonDoc.clear();
        JsonArray arr = g_jsonDoc["networks"].to<JsonArray>();
        for (int i = 0; i < n && i < 20; ++i) {
            JsonObject net = arr.add<JsonObject>();
            net["ssid"] = WiFi.SSID(i); net["rssi"] = WiFi.RSSI(i); net["ch"] = WiFi.channel(i);
            net["bssid"] = WiFi.BSSIDstr(i);
        }
        size_t ln = serializeJson(g_jsonDoc, g_mqttPayload, sizeof(g_mqttPayload));
        g_mqtt.publish(topic("wifi_scan").c_str(), (const uint8_t*)g_mqttPayload, ln, false);
        WiFi.scanDelete();
    }
    strlcpy(g_lastAction, act, sizeof(g_lastAction));
    g_lastActionSeq = seq;
    publishState();
}

static void mqttConnect() {
    static bool configReqSent = false;
    if (!g_mqtt.connected()) {
        configReqSent = false;
        String cid = "m5-" + g_deviceId;
        if (g_mqtt.connect(cid.c_str())) {
            g_mqtt.subscribe(topic("config").c_str());
            g_mqtt.subscribe(topic("cmd").c_str());
            g_mqtt.subscribe(topic("weather").c_str());
            g_mqtt.subscribe(topic("stock").c_str());
            g_mqttOk = true;
            if (!configReqSent) {
                publishRefreshRequest("config");
                configReqSent = true;
            }
        }
    } else {
        g_mqtt.loop();
        g_mqttOk = true;
    }
}

// ---------------------------------------------------------------------------
// AppModule base
// ---------------------------------------------------------------------------
class AppModule {
public:
    virtual ~AppModule() = default;
    virtual const char* id() const = 0;
    virtual void onEnter() {}
    virtual void onLoop() {}
    virtual void render(M5Canvas& c, int w, int h) = 0;
    virtual void onBtnAPress() {}
    virtual void onBtnALongPress() {}
    virtual void onBtnBPress() {}
    virtual void onExit() {}
    virtual bool forcePortrait() const { return false; }
    virtual bool forceLandscape() const { return false; }
};

// ---------------------------------------------------------------------------
// BusModule
// ---------------------------------------------------------------------------
class BusModule : public AppModule {
public:
    const char* id() const override { return "bus"; }
    bool forceLandscape() const override { return true; }

    void onLoop() override {
        etaTick();
    }

    void onBtnAPress() override {
        g_activeProfile = (g_activeProfile + 1) % PROFILE_COUNT;
        saveNvs(); fetchAllEta();
    }

    void onBtnALongPress() override { fetchAllEta(); }

    void render(M5Canvas& c, int w, int h) override {
        (void)w;
        (void)h;
        c.fillSprite(C_BG);
        drawCol(c, BUS_COL_A_X, g_colA, g_profiles[g_activeProfile].busA);
        drawCol(c, BUS_COL_B_X, g_colB, g_profiles[g_activeProfile].busB);
    }

private:
    static void shortenLabel(char* dst, size_t n, const char* src) {
        if (!src || !src[0]) { dst[0] = '\0'; return; }
        strlcpy(dst, src, n);
        if (strlen(dst) > 10) {
            dst[9] = '\0';
            strlcat(dst, "..", n);
        }
    }

    static const char* resolveDest(const BusColState& col, const BusStopCfg& cfg, char* buf, size_t n) {
        if (cfg.dest[0]) return cfg.dest;
        for (int i = 0; i < ETA_SLOTS; ++i) {
            if (col.slots[i].valid && col.slots[i].dest[0]) return col.slots[i].dest;
        }
        if (cfg.name[0]) return cfg.name;
        shortenLabel(buf, n, col.stop);
        return buf;
    }

    static int firstEtaMins(const BusColState& col) {
        for (int i = 0; i < ETA_SLOTS; ++i) {
            if (col.slots[i].valid) return col.slots[i].minutes;
        }
        return -1;
    }

    void drawCol(M5Canvas& c, int cx, const BusColState& col, const BusStopCfg& cfg) {
        char destBuf[16];
        const char* dest = resolveDest(col, cfg, destBuf, sizeof(destBuf));
        const char* route = col.route[0] ? col.route : cfg.route;

        char routeLine[40];
        snprintf(routeLine, sizeof(routeLine), "%s %s", route, dest);

        if (g_cfg.english)
            drawMc(c, &fonts::Font2, routeLine, cx, 18, TFT_WHITE);
        else
            drawMc(c, &fonts::efontTW_16, routeLine, cx, 18, TFT_WHITE);

        int mins = firstEtaMins(col);
        if (mins < 0) {
            drawMc(c, &fonts::Font7, "--", cx, 75, C_DIM);
            return;
        }

        int displayMins = mins <= 0 ? 0 : mins;
        char num[8];
        snprintf(num, sizeof(num), "%d", displayMins);
        drawMc(c, &fonts::Font7, num, cx, 75, etaColor(displayMins));

        if (displayMins > 0) {
            if (g_cfg.english)
                drawMc(c, &fonts::Font0, "m", cx, 118, C_DIM);
            else
                drawMc(c, &fonts::efontTW_12, "\xe5\x88\x86", cx, 118, C_DIM);
        }
    }
};

// ---------------------------------------------------------------------------
// StockModule
// ---------------------------------------------------------------------------
class StockModule : public AppModule {
public:
    const char* id() const override { return "stock"; }
    bool forceLandscape() const override { return true; }

    void onBtnAPress() override {
        for (int n = 0; n < STOCK_SLOTS; ++n) {
            g_cfg.activeStock = (g_cfg.activeStock + 1) % STOCK_SLOTS;
            if (g_cfg.stocks[g_cfg.activeStock].symbol[0]) break;
        }
        saveNvs();
        publishRefreshRequest("stock");
    }

    void onBtnALongPress() override { publishRefreshRequest("stock"); }

    void render(M5Canvas& c, int w, int h) override {
        (void)h;
        c.fillSprite(C_BG);
        c.fillRect(0, 114, w, 21, C_DARKGREY);

        if (!g_stock.has) {
            drawCenteredText(c, w, 58,
                g_cfg.english ? "Awaiting stock MQTT..." : "\xe7\xad\x89\xe5\xbe\x85\xe8\x82\xa1\xe7\xa5\xa8 MQTT...",
                C_DIM);
            drawCenteredText(c, w, 122,
                g_cfg.english ? "[A] Next Stock | [B] Menu"
                              : "[\xe8\x97\x8d\xe6\x91\x83] \xe5\x88\x87\xe6\x8f\x9b\xe8\x82\xa1\xe7\xa5\xa8 | [\xe5\x81\xb4\xe6\x91\x83] \xe9\x81\xb8\xe5\x96\xae",
                C_DIM);
            return;
        }

        const bool up = g_stock.change >= 0;
        const uint16_t tc = up ? C_GREEN : C_RED;

        // Left area (x=4..110)
        c.setFont(&fonts::Font0);
        c.setTextSize(1);
        c.setTextColor(C_FG);
        c.setCursor(4, 28);
        c.print(g_stock.symbol);
        c.setTextColor(C_DIM);
        c.setCursor(4, 42);
        c.print(g_stock.name);

        c.setFont(&fonts::Font2);
        c.setTextColor(C_FG);
        c.setCursor(4, 62);
        c.printf("$%.2f", g_stock.price);

        c.fillCircle(10, 92, 7, tc);
        c.setFont(&fonts::Font0);
        c.setTextSize(1);
        c.setTextColor(tc);
        c.setCursor(22, 86);
        c.printf("%+.2f", g_stock.change);
        c.setCursor(22, 98);
        c.printf("%+.1f%%", g_stock.changePct);

        // Right area chart (x=115..236, y=22..112)
        c.drawRect(115, 22, 121, 90, C_DARKGREY);
        drawProfessionalWaveChart(c, 118, 25, 115, 84, tc);

        drawCenteredText(c, w, 122,
            g_cfg.english ? "[A] Next Stock | [B] Menu"
                          : "[\xe8\x97\x8d\xe6\x91\x83] \xe5\x88\x87\xe6\x8f\x9b\xe8\x82\xa1\xe7\xa5\xa8 | [\xe5\x81\xb4\xe6\x91\x83] \xe9\x81\xb8\xe5\x96\xae",
            C_DIM);
    }

private:
    void drawProfessionalWaveChart(M5Canvas& c, int x, int y, int w, int h, uint16_t col) {
        if (g_stock.histCount < 2) return;
        float minV = g_stock.hist[0], maxV = g_stock.hist[0];
        for (int i = 1; i < g_stock.histCount; ++i) {
            minV = min(minV, g_stock.hist[i]);
            maxV = max(maxV, g_stock.hist[i]);
        }
        if (g_stock.prevClose > 0) { minV = min(minV, g_stock.prevClose); maxV = max(maxV, g_stock.prevClose); }
        const float range = max(maxV - minV, 0.01f);
        if (g_stock.prevClose > 0) {
            int baseY = y + h - (int)((g_stock.prevClose - minV) / range * (h - 4));
            for (int dx = x; dx < x + w; dx += 3)
                if (((dx - x) / 3) % 2 == 0) c.drawPixel(dx, baseY, C_DIM);
        }
        int px = x, py = y + h;
        for (int i = 0; i < g_stock.histCount; ++i) {
            int cx = x + (i * (w - 1)) / max(1, g_stock.histCount - 1);
            int cy = y + h - (int)((g_stock.hist[i] - minV) / range * (h - 4));
            if (i > 0) c.drawLine(px, py, cx, cy, col);
            px = cx; py = cy;
        }
        c.fillCircle(px, py, 3, col);
        c.drawCircle(px, py, 4, C_FG);
    }
};

// ---------------------------------------------------------------------------
// WeatherModule
// ---------------------------------------------------------------------------
class WeatherModule : public AppModule {
public:
    const char* id() const override { return "weather"; }
    bool forcePortrait() const override { return true; }

    void onBtnAPress() override { g_weatherForecastView = !g_weatherForecastView; }

    void onBtnALongPress() override { publishRefreshRequest("weather"); }

    void render(M5Canvas& c, int w, int h) override {
        c.fillSprite(C_BG);
        c.setTextColor(C_CYAN);
        c.setTextSize(1);
        c.setCursor(4, 2);
        c.print(g_cfg.english ? "HKO Weather" : "天文台天氣");
        if (!g_weather.has) {
            c.setTextColor(C_DIM);
            c.setCursor(4, 40);
            c.print(g_cfg.english ? "Awaiting weather MQTT..." : "等待天氣 MQTT...");
            return;
        }
        c.setTextColor(C_FG);
        c.setCursor(4, 14);
        c.printf("%d C  %d%% RH", g_weather.temp, g_weather.humidity);
        int y = 30;
        if (!g_weatherForecastView) {
            c.setTextColor(C_AMBER);
            c.setCursor(4, y);
            c.print(g_cfg.english ? "Warnings" : "警告");
            y += 12;
            if (!g_weather.warnCount) {
                c.setTextColor(C_GREEN);
                c.setCursor(8, y);
                c.print(g_cfg.english ? "None" : "無");
            } else {
                for (int i = 0; i < g_weather.warnCount && y < h - 20; ++i) {
                    c.fillRoundRect(4, y, w - 8, 14, 2, C_WARN_BG);
                    c.setTextColor(C_WARN_FG);
                    c.setCursor(8, y + 3);
                    c.printf("%s %s", g_weather.warns[i].code, g_weather.warns[i].name);
                    y += 16;
                }
            }
        } else {
            c.setTextColor(C_AMBER);
            c.setCursor(4, y);
            c.print(g_cfg.english ? "9-Day Forecast" : "九天預報");
            y += 12;
            for (int i = 0; i < g_weather.fcCount && y < h - 12; ++i) {
                const auto& d = g_weather.fc[i];
                c.setTextColor(C_FG);
                c.setCursor(4, y);
                c.printf("%s %s %d-%d", d.date, d.week, d.minT, d.maxT);
                c.setTextColor(C_CYAN);
                c.printf(" PSR%d%%", d.psr);
                y += 11;
                c.setCursor(8, y);
                c.setTextColor(C_DIM);
                c.print(d.desc);
                y += 11;
            }
        }
        c.setTextColor(C_DIM);
        c.setCursor(4, h - 10);
        if (!g_weatherForecastView)
            c.print(g_cfg.english ? "A:9-Day  B:Menu" : "A:九天 B:選單");
        else
            c.print(g_cfg.english ? "A:Live  B:Menu" : "A:即時 B:選單");
    }
};

static BusModule g_bus;
static StockModule g_stockMod;
static WeatherModule g_weatherMod;

static AppModule* modFor(AppMode m) {
    switch (m) {
        case AppMode::Bus: return &g_bus;
        case AppMode::Stock: return &g_stockMod;
        case AppMode::Weather: return &g_weatherMod;
        default: return &g_bus;
    }
}

// ---------------------------------------------------------------------------
// Carousel Menu (7 cards, portrait)
// ---------------------------------------------------------------------------
static const char* cardTitle(int i, bool en) {
    static const char* zh[] = {"目前模組","巴士 Profile","螢幕亮度","休眠時間","顯示語言","配對 QR","儲存離開"};
    static const char* enT[] = {"Active App","Bus Profile","Brightness","Sleep Timeout","Language","Pair QR","Save & Exit"};
    return en ? enT[i] : zh[i];
}

static const char* modeLabel(AppMode m) {
    switch (m) {
        case AppMode::Bus: return "BUS";
        case AppMode::Stock: return "STOCK";
        case AppMode::Weather: return "WEATHER";
        default: return "BUS";
    }
}

static void adjustCarousel() {
    switch (g_menuCardIdx) {
        case 0: g_cfg.appMode = (AppMode)(((int)g_cfg.appMode + 1) % (int)AppMode::Count); break;
        case 1: g_activeProfile = (g_activeProfile + 1) % PROFILE_COUNT; break;
        case 2: g_cfg.bright = (g_cfg.bright + 1) % 4; M5.Display.setBrightness(brightVal()); break;
        case 3: g_cfg.timeout = (g_cfg.timeout + 1) % 4; break;
        case 4: g_cfg.english = !g_cfg.english; break;
        case 5: g_ui = UiScreen::QrCode; return;
        case 6: saveNvs(); g_ui = UiScreen::Module; return;
    }
    saveNvs();
}

static void cardValue(M5Canvas& c, int idx, int cardW) {
    char buf[32];
    uint16_t col = C_CYAN;
    switch (idx) {
        case 0:
            snprintf(buf, sizeof(buf), "%s", modeLabel(g_cfg.appMode));
            break;
        case 1:
            snprintf(buf, sizeof(buf), "P%d", g_activeProfile + 1);
            break;
        case 2:
            snprintf(buf, sizeof(buf), "%d%%", (g_cfg.bright + 1) * 25);
            break;
        case 3: {
            static const char* t[] = {"15s", "30s", "60s", "Off"};
            snprintf(buf, sizeof(buf), "%s", t[g_cfg.timeout > 3 ? 1 : g_cfg.timeout]);
            break;
        }
        case 4:
            snprintf(buf, sizeof(buf), "%s", g_cfg.english ? "EN" : "\xe4\xb8\xad");
            break;
        case 5:
            snprintf(buf, sizeof(buf), "QR");
            col = C_AMBER;
            break;
        case 6:
            snprintf(buf, sizeof(buf), "OK");
            col = C_GREEN;
            break;
        default:
            buf[0] = '\0';
            break;
    }
    c.setFont(&fonts::Font4);
    c.setTextColor(col);
    int tw = c.textWidth(buf);
    c.setCursor((cardW - tw) / 2 + 6, 100);
    c.print(buf);
    c.setFont(&fonts::Font0);
}

static void renderCarousel(M5Canvas& c, int w, int h) {
    (void)w;
    c.fillSprite(C_BG);

    c.setFont(&fonts::Font0);
    c.setTextSize(1);
    c.setTextColor(C_AMBER);
    c.setCursor(8, 8);
    c.printf("MENU (%d/%d)", g_menuCardIdx + 1, CAROUSEL_CARDS);

    c.drawRoundRect(6, 28, 123, 160, 8, TFT_CYAN);

    c.setTextColor(C_FG);
    c.setCursor(12, 45);
    c.print(cardTitle(g_menuCardIdx, g_cfg.english));

    cardValue(c, g_menuCardIdx, w);

    c.setTextColor(C_DIM);
    c.setCursor(8, 210);
    c.print(g_cfg.english ? "[A] Change | [B] Next" : "[A] \xe8\xaa\xbf\xe6\x95\xb4 | [B] \xe4\xb8\x8b\xe4\xb8\x80\xe9\xa0\x85");
    (void)h;
}

static void renderQr() {
    ensureSpriteLayout(false);
    String url = "https://sbgitdept.github.io/m5-bus-controller/?id=" + g_deviceId;
    g_canvas.fillSprite(C_BG);
    g_canvas.setFont(&fonts::Font0);
    g_canvas.setTextSize(1);
    g_canvas.setTextColor(C_FG);
    g_canvas.setCursor(4, 4);
    g_canvas.print(g_cfg.english ? "Scan to Pair" : "\xe6\x8e\x83\xe6\x8f\x8f\xe9\x85\x8d\xe5\xb0\x8d");
    uint8_t buf[qrcode_getBufferSize(3)];
    QRCode qr;
    qrcode_initText(&qr, buf, 3, ECC_LOW, url.c_str());
    int scale = 3, sz = qr.size * scale;
    int ox = (PORTRAIT_W - sz) / 2, oy = 28;
    for (int y = 0; y < qr.size; ++y)
        for (int x = 0; x < qr.size; ++x)
            g_canvas.fillRect(ox + x * scale, oy + y * scale, scale, scale,
                              qrcode_getModule(&qr, x, y) ? C_FG : C_BG);
    g_canvas.setCursor(4, oy + sz + 6);
    g_canvas.println(g_deviceId);
    g_canvas.setCursor(4, PORTRAIT_H - 12);
    g_canvas.setTextColor(C_DIM);
    g_canvas.print(g_cfg.english ? "Any key closes" : "\xe6\x8c\x89\xe9\x8d\xb5\xe9\x97\x9c\xe9\x96\x89");
    g_canvas.pushSprite(0, 0);
}

// ---------------------------------------------------------------------------
// Key Engine
// ---------------------------------------------------------------------------
class KeyEngine {
    uint8_t cntA_ = 0, cntB_ = 0;
    uint32_t lastA_ = 0, lastB_ = 0;

public:
    void update(AppModule* mod) {
        M5.update();
        M5.BtnA.setHoldThresh(LONG_PRESS_MS);
        M5.BtnB.setHoldThresh(LONG_PRESS_MS);
        uint32_t now = millis();

        if (M5.BtnA.wasClicked()) {
            touch();
            if (now - lastA_ > MULTI_CLICK_MS) cntA_ = 0;
            ++cntA_;
            lastA_ = now;
            if (cntA_ < MULTI_CLICK_TARGET) onSingleA(mod);
        }
        if (M5.BtnA.wasHold()) {
            touch();
            onLongA(mod);
        }

        if (M5.BtnB.wasClicked()) {
            touch();
            if (now - lastB_ > MULTI_CLICK_MS) cntB_ = 0;
            ++cntB_;
            lastB_ = now;
            if (cntB_ < MULTI_CLICK_TARGET) onSingleB(mod);
        }

        if (cntA_ && now - lastA_ > MULTI_CLICK_MS) {
            if (cntA_ >= MULTI_CLICK_TARGET) cycleMode();
            cntA_ = 0;
        }
        if (cntB_ && now - lastB_ > MULTI_CLICK_MS) {
            if (cntB_ >= MULTI_CLICK_TARGET) g_ui = UiScreen::QrCode;
            cntB_ = 0;
        }
    }

private:
    void onSingleA(AppModule* mod) {
        if (g_ui == UiScreen::QrCode) { g_ui = UiScreen::Module; return; }
        if (g_ui == UiScreen::Carousel) { adjustCarousel(); return; }
        mod->onBtnAPress();
    }

    void onLongA(AppModule* mod) {
        if (g_ui == UiScreen::Carousel) { saveNvs(); g_ui = UiScreen::Module; return; }
        mod->onBtnALongPress();
    }

    void onSingleB(AppModule* mod) {
        if (g_ui == UiScreen::QrCode) { g_ui = UiScreen::Module; return; }
        if (g_ui == UiScreen::Carousel) {
            g_menuCardIdx = (g_menuCardIdx + 1) % CAROUSEL_CARDS;
            g_frameDirty = true;
            return;
        }
        if (mod) mod->onBtnBPress();
        g_ui = UiScreen::Carousel;
        g_menuCardIdx = 0;
    }

    void cycleMode() {
        g_cfg.appMode = (AppMode)(((int)g_cfg.appMode + 1) % (int)AppMode::Count);
        g_ui = UiScreen::Module;
        saveNvs();
        g_frameDirty = true;
    }
};

static KeyEngine g_keys;
static AppMode g_lastMode = AppMode::Count;

static void renderFrame() {
    if (!shouldRenderFrame()) return;

    if (g_ui == UiScreen::QrCode) { wakeDisplay(); renderQr(); return; }

    wakeDisplay();

    AppModule* mod = modFor(g_cfg.appMode);
    if (g_cfg.appMode != g_lastMode) {
        if (g_lastMode != AppMode::Count) modFor(g_lastMode)->onExit();
        mod->onEnter();
        g_lastMode = g_cfg.appMode;
        g_frameDirty = true;
    }
    mod->onLoop();

    bool landscape = frameIsLandscape();
    ensureSpriteLayout(landscape);
    int w = landscape ? LAND_W : PORTRAIT_W;
    int h = landscape ? LAND_H : PORTRAIT_H;

    if (g_ui == UiScreen::Carousel) renderCarousel(g_canvas, w, h);
    else mod->render(g_canvas, w, h);

    g_canvas.pushSprite(0, 0);

    uint32_t to = timeoutMs();
    if (g_bootTasksDone && to && millis() - g_lastActivity > to) M5.Display.sleep();
}

static void connectWifi() { wifiTick(); }

void setup() {
    auto cfg = M5.config();
    cfg.fallback_board = m5::board_t::board_M5StickS3;
    cfg.internal_imu = true;
    M5.begin(cfg);

    M5.BtnA.setHoldThresh(LONG_PRESS_MS);
    M5.BtnB.setHoldThresh(LONG_PRESS_MS);

    g_lastActivity = millis();
    M5.Display.setRotation(1);
    wakeDisplay();
    M5.Display.fillScreen(C_BG);

    g_prefs.begin("m5bus_v6", false);
    uint8_t mac[6];
    WiFi.macAddress(mac);
    char id[13];
    snprintf(id, sizeof(id), "%02X%02X%02X%02X%02X%02X", mac[0], mac[1], mac[2], mac[3], mac[4], mac[5]);
    g_deviceId = id;

    loadNvs();
    if ((int)g_cfg.appMode >= (int)AppMode::Count) g_cfg.appMode = AppMode::Bus;
    g_ui = UiScreen::Module;
    g_cfg.appMode = AppMode::Bus;  // 開機主頁：巴士 ETA
    drawBootSplash();

    g_mqtt.setServer(MQTT_HOST, MQTT_PORT);
    g_mqtt.setCallback(mqttCallback);
    g_mqtt.setBufferSize(MQTT_BUFFER_SIZE);

    g_lastEta = millis();
}

void loop() {
    g_keys.update(modFor(g_cfg.appMode));
    wifiTick();
    etaTick();
    if (WiFi.status() == WL_CONNECTED) {
        mqttConnect();
        if (g_mqttOk && millis() - g_lastState > STATE_PUBLISH_MS) {
            publishState();
            g_lastState = millis();
        }
    }
    renderFrame();
    delay(100);
}
