/**
 * M5StickS3 Firmware v6.0
 * NVS Engine · MQTT State Bus · Bus/RSSI/Stock/Weather Modules · Carousel UI
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
static constexpr int CAROUSEL_CARDS = 8;
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
enum class AppMode : uint8_t { Bus = 0, Rssi, Stock, Weather, Count };
enum class UiScreen : uint8_t { Module, Carousel, QrCode };

struct BusStopCfg {
    char co[4] = "KMB";
    char route[12] = "";
    char stop[24] = "";
    char svc[4] = "1";
    char bound[2] = "O";
    char name[32] = "";
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

struct RadarCfg {
    char ssid[33] = "";
    char mac[18] = "";
};

struct DeviceSettings {
    uint8_t bright = 1;
    uint8_t timeout = 1;
    bool english = false;
    AppMode appMode = AppMode::Bus;
    WifiCfg wifi;
    RadarCfg radar;
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

static UiScreen g_ui = UiScreen::Module;
static int g_carouselIdx = 0;
static bool g_weatherForecastView = false;
static int g_imuRotation = 0;
static int g_radarRssi = -127, g_radarPct = 0, g_radarCh = 0;
static uint32_t g_lastRssiScan = 0;
static uint32_t g_lastActivity = 0, g_lastEta = 0, g_lastState = 0;
static bool g_bootTasksDone = false;
static uint8_t g_etaStep = 0;
static uint32_t g_wifiTryMs = 0;
static bool g_ntpDone = false;
static bool g_mqttOk = false;
static char g_lastAction[20] = "";
static uint32_t g_lastActionSeq = 0;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------
static void touch() { g_lastActivity = millis(); }

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
        case AppMode::Rssi: return "rssi";
        case AppMode::Stock: return "stock";
        case AppMode::Weather: return "weather";
        default: return "bus";
    }
}

static AppMode modeFrom(const char* s) {
    if (!s) return AppMode::Bus;
    if (!strcmp(s, "rssi") || !strcmp(s, "rssi_monitor")) return AppMode::Rssi;
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

static void setRotation(int r) {
    g_imuRotation = r & 3;
    M5.Display.setRotation(g_imuRotation);
}

static void updateImu4Way(bool enabled) {
    if (!enabled) return;
    auto imu = M5.Imu.getImuData();
    float ax = imu.accel.x, ay = imu.accel.y;
    if (fabsf(ax) < 0.25f && fabsf(ay) < 0.25f) return;
    if (fabsf(ax) > fabsf(ay)) setRotation(ax > 0 ? 1 : 3);
    else setRotation(ay > 0 ? 2 : 0);
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
    JsonObject rssi = mods["rssi"].to<JsonObject>();
    rssi["radar_ssid"] = g_cfg.radar.ssid;
    rssi["radar_mac"] = g_cfg.radar.mac;
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
    s["radar"]["ssid"] = g_cfg.radar.ssid;
    s["radar"]["mac"] = g_cfg.radar.mac;
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
        JsonObjectConst rssi = mods["rssi"];
        if (!rssi.isNull()) {
            const char* ssid = rssi["radar_ssid"] | rssi["ssid"];
            const char* mac = rssi["radar_mac"] | rssi["mac"] | rssi["bssid"];
            if (ssid) strlcpy(g_cfg.radar.ssid, ssid, sizeof(g_cfg.radar.ssid));
            if (mac) strlcpy(g_cfg.radar.mac, mac, sizeof(g_cfg.radar.mac));
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
        if (st["radar"]["ssid"].is<const char*>()) strlcpy(g_cfg.radar.ssid, st["radar"]["ssid"], sizeof(g_cfg.radar.ssid));
        const char* mac = st["radar"]["mac"] | st["radar"]["bssid"];
        if (mac) strlcpy(g_cfg.radar.mac, mac, sizeof(g_cfg.radar.mac));
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
        strlcpy(g_profiles[0].busB.co, "KMB", sizeof(g_profiles[0].busB.co));
        strlcpy(g_profiles[0].busB.route, "76K", sizeof(g_profiles[0].busB.route));
        strlcpy(g_profiles[0].busB.stop, "B0D79D5CE512B9EC", sizeof(g_profiles[0].busB.stop));
        strlcpy(g_profiles[0].busB.name, g_cfg.english ? "Sheung Shui" : "上水", sizeof(g_profiles[0].busB.name));
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
    };
    wb("busA", g_profiles[g_activeProfile].busA);
    wb("busB", g_profiles[g_activeProfile].busB);
    if (g_cfg.appMode == AppMode::Rssi) {
        g_jsonDoc["radar_rssi"] = g_radarRssi;
        g_jsonDoc["radar_pct"] = g_radarPct;
        g_jsonDoc["radar_channel"] = g_radarCh;
    }
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
    virtual bool imu4Way() const { return false; }
};

// ---------------------------------------------------------------------------
// BusModule
// ---------------------------------------------------------------------------
class BusModule : public AppModule {
public:
    const char* id() const override { return "bus"; }
    bool forceLandscape() const override { return true; }
    bool imu4Way() const override { return true; }

    void onLoop() override {
        etaTick();
    }

    void onBtnAPress() override {
        g_activeProfile = (g_activeProfile + 1) % PROFILE_COUNT;
        saveNvs(); fetchAllEta();
    }

    void onBtnALongPress() override { fetchAllEta(); }

    void render(M5Canvas& c, int w, int h) override {
        int cw = w / 2;
        drawCol(c, 0, 0, cw, h, g_colA, g_profiles[g_activeProfile].busA);
        drawCol(c, cw, 0, cw, h, g_colB, g_profiles[g_activeProfile].busB);
        c.setTextSize(1);
        c.setTextColor(C_DIM);
        c.setCursor(2, h - 10);
        c.printf("P%d %s", g_activeProfile + 1, g_profiles[g_activeProfile].name);
        c.setCursor(w - 72, h - 10);
        c.print(g_cfg.english ? "B:Menu Ax5" : "B:選單 A×5");
    }

private:
    void drawCol(M5Canvas& c, int x, int y, int w, int h, const BusColState& col, const BusStopCfg& cfg) {
        c.fillRect(x, y, w, h, C_BG);
        c.drawFastVLine(x + w - 1, y, h, C_DIM);
        c.setTextColor(C_AMBER);
        c.setTextSize(1);
        c.setCursor(x + 2, y + 2);
        c.printf("%s %s", cfg.co, col.route);
        c.setTextColor(C_FG);
        c.setCursor(x + 2, y + 14);
        c.print(col.stop);
        int ry = y + 28;
        for (int i = 0; i < ETA_SLOTS; ++i) {
            if (col.slots[i].valid) {
                c.setFont(&fonts::Font4);
                c.setTextColor(C_CYAN);
                c.setCursor(x + 4, ry);
                c.printf("%d'", col.slots[i].minutes);
                c.setFont(&fonts::Font0);
                c.setTextSize(1);
                c.setTextColor(C_FG);
                c.setCursor(x + 4, ry + 18);
                c.print(col.slots[i].dest);
                ry += 36;
            }
        }
        if (!col.ok) {
            c.setTextSize(1);
            c.setTextColor(C_DIM);
            c.setCursor(x + 4, ry);
            if (WiFi.status() != WL_CONNECTED)
                c.print(g_cfg.english ? "No WiFi" : "無 WiFi");
            else if (!cfg.route[0] || !cfg.stop[0])
                c.print(g_cfg.english ? "No stop" : "未設站點");
            else
                c.print(g_cfg.english ? "Loading..." : "載入中...");
        }
    }
};

// ---------------------------------------------------------------------------
// RssiModule
// ---------------------------------------------------------------------------
class RssiModule : public AppModule {
public:
    const char* id() const override { return "rssi"; }
    bool forcePortrait() const override { return true; }

    void onLoop() override {
        if (millis() - g_lastRssiScan < 2000) return;
        g_lastRssiScan = millis();
        const char* tgt = g_cfg.radar.ssid[0] ? g_cfg.radar.ssid : WiFi.SSID().c_str();
        int n = WiFi.scanNetworks(false, true);
        int best = -127, ch = 0;
        for (int i = 0; i < n; ++i) {
            bool match = g_cfg.radar.mac[0] ? WiFi.BSSIDstr(i).equalsIgnoreCase(g_cfg.radar.mac)
                                            : (WiFi.SSID(i) == tgt);
            if (match && WiFi.RSSI(i) > best) { best = WiFi.RSSI(i); ch = WiFi.channel(i); }
        }
        WiFi.scanDelete();
        if (best > -127) {
            g_radarRssi = best; g_radarCh = ch;
            g_radarPct = constrain(map(best, -90, -30, 0, 100), 0, 100);
        }
    }

    void onBtnAPress() override { g_cfg.appMode = AppMode::Bus; saveNvs(); }

    void onBtnALongPress() override { onLoop(); }

    void render(M5Canvas& c, int w, int h) override {
        c.fillSprite(C_BG);
        c.setTextColor(C_CYAN);
        c.setTextSize(2);
        c.setCursor(4, 4);
        c.print("RSSI");
        c.setTextSize(1);
        c.setTextColor(C_FG);
        c.setCursor(4, 28);
        c.printf("SSID: %s", g_cfg.radar.ssid[0] ? g_cfg.radar.ssid : WiFi.SSID().c_str());
        if (g_cfg.radar.mac[0]) { c.setCursor(4, 40); c.printf("MAC: %s", g_cfg.radar.mac); }
        int barW = w - 16, barH = 20, barY = h / 2 - 8;
        c.drawRect(8, barY, barW, barH, C_DIM);
        int fill = map(g_radarPct, 0, 100, 0, barW - 2);
        uint16_t col = g_radarPct > 60 ? C_GREEN : (g_radarPct > 30 ? C_AMBER : C_RED);
        c.fillRect(9, barY + 1, fill, barH - 2, col);
        c.setTextSize(2);
        c.setTextColor(C_FG);
        c.setCursor(8, barY + barH + 8);
        c.printf("%d dBm", g_radarRssi);
        c.setTextSize(1);
        c.setCursor(8, barY + barH + 32);
        c.printf("%d%%  CH %d", g_radarPct, g_radarCh);
        c.setTextColor(C_DIM);
        c.setCursor(4, h - 10);
        c.print(g_cfg.english ? "A/B:Back Bus" : "A/B:返巴士");
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
        c.fillSprite(C_BG);
        if (!g_stock.has) {
            c.setTextColor(C_DIM);
            c.setCursor(8, h / 2);
            c.print(g_cfg.english ? "Awaiting stock MQTT..." : "等待股票 MQTT...");
            return;
        }
        bool up = g_stock.change >= 0;
        uint16_t tc = up ? C_GREEN : C_RED;
        c.setTextSize(1);
        c.setTextColor(C_FG);
        c.setCursor(4, 2);
        c.printf("%s %s", g_stock.symbol, g_stock.name);
        c.setTextSize(2);
        c.setTextColor(tc);
        c.setCursor(4, 14);
        c.printf("%.2f", g_stock.price);
        c.setTextSize(1);
        c.printf(" %+.2f (%+.1f%%)", g_stock.change, g_stock.changePct);
        drawProfessionalWaveChart(c, 4, 40, w - 8, h - 50, tc);
        c.setTextColor(C_DIM);
        c.setCursor(4, h - 10);
        c.print(g_cfg.english ? "A:Next B:Menu" : "A:換股 B:選單");
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
        float range = max(maxV - minV, 0.01f);
        int baseY = y + h - (int)((g_stock.prevClose - minV) / range * (h - 4));
        for (int dx = x; dx < x + w; dx += 4) c.drawPixel(dx, baseY, C_DIM);
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
static RssiModule g_rssi;
static StockModule g_stockMod;
static WeatherModule g_weatherMod;

static AppModule* modFor(AppMode m) {
    switch (m) {
        case AppMode::Bus: return &g_bus;
        case AppMode::Rssi: return &g_rssi;
        case AppMode::Stock: return &g_stockMod;
        case AppMode::Weather: return &g_weatherMod;
        default: return &g_bus;
    }
}

// ---------------------------------------------------------------------------
// Carousel Menu (8 cards, portrait)
// ---------------------------------------------------------------------------
static const char* cardTitle(int i, bool en) {
    static const char* zh[] = {"目前模組","巴士 Profile","WiFi 目標","螢幕亮度","休眠時間","顯示語言","配對 QR","儲存離開"};
    static const char* enT[] = {"Active App","Bus Profile","WiFi Target","Brightness","Sleep Timeout","Language","Pair QR","Save & Exit"};
    return en ? enT[i] : zh[i];
}

static void adjustCarousel() {
    switch (g_carouselIdx) {
        case 0: g_cfg.appMode = (AppMode)(((int)g_cfg.appMode + 1) % (int)AppMode::Count); break;
        case 1: g_activeProfile = (g_activeProfile + 1) % PROFILE_COUNT; break;
        case 2: {
            if (g_cfg.radar.ssid[0] == '\0' && WiFi.SSID().length())
                strlcpy(g_cfg.radar.ssid, WiFi.SSID().c_str(), sizeof(g_cfg.radar.ssid));
            else
                g_cfg.radar.ssid[0] = '\0';
            break;
        }
        case 3: g_cfg.bright = (g_cfg.bright + 1) % 4; M5.Display.setBrightness(brightVal()); break;
        case 4: g_cfg.timeout = (g_cfg.timeout + 1) % 4; break;
        case 5: g_cfg.english = !g_cfg.english; break;
        case 6: g_ui = UiScreen::QrCode; return;
        case 7: saveNvs(); g_ui = UiScreen::Module; return;
    }
    saveNvs();
}

static void renderCarousel(M5Canvas& c, int w, int h) {
    c.fillSprite(C_BG);
    c.setTextColor(C_AMBER);
    c.setCursor(4, 2);
    c.print(g_cfg.english ? "Carousel Menu" : "系統選單");
    int cardH = 26;
    for (int i = 0; i < CAROUSEL_CARDS; ++i) {
        int y = 16 + i * cardH;
        if (y > h - cardH) break;
        bool act = i == g_carouselIdx;
        if (act) c.drawRoundRect(2, y, w - 4, cardH - 2, 3, C_AMBER);
        c.setTextColor(act ? C_FG : C_DIM);
        c.setCursor(8, y + 8);
        c.print(cardTitle(i, g_cfg.english));
        c.setCursor(w - 52, y + 8);
        c.setTextColor(C_CYAN);
        switch (i) {
            case 0: c.print(modeStr(g_cfg.appMode)); break;
            case 1: c.printf("P%d", g_activeProfile + 1); break;
            case 2: c.print(g_cfg.wifi.ssid[0] ? g_cfg.wifi.ssid : WiFi.SSID()); break;
            case 3: c.printf("%d%%", (g_cfg.bright + 1) * 25); break;
            case 4: { const char* t[] = {"15s","30s","60s","Off"}; c.print(t[g_cfg.timeout]); break; }
            case 5: c.print(g_cfg.english ? "EN" : "中"); break;
            case 6: c.print("QR"); break;
            case 7: c.print("OK"); break;
        }
    }
    c.setTextColor(C_DIM);
    c.setCursor(4, h - 10);
    c.print(g_cfg.english ? "A:adjust B:next" : "A:調整 B:下一項");
}

static void renderQr() {
    String url = "https://sbgitdept.github.io/m5-bus-controller/?id=" + g_deviceId;
    setRotation(0);
    M5.Display.fillScreen(C_BG);
    M5.Display.setTextColor(C_FG);
    M5.Display.setCursor(4, 4);
    M5.Display.print(g_cfg.english ? "Scan to Pair" : "掃描配對");
    uint8_t buf[qrcode_getBufferSize(3)];
    QRCode qr;
    qrcode_initText(&qr, buf, 3, ECC_LOW, url.c_str());
    int scale = 3, sz = qr.size * scale;
    int ox = (PORTRAIT_W - sz) / 2, oy = 28;
    for (int y = 0; y < qr.size; ++y)
        for (int x = 0; x < qr.size; ++x)
            M5.Display.fillRect(ox + x * scale, oy + y * scale, scale, scale,
                                qrcode_getModule(&qr, x, y) ? C_FG : C_BG);
    M5.Display.setCursor(4, oy + sz + 6);
    M5.Display.println(g_deviceId);
    M5.Display.setCursor(4, PORTRAIT_H - 12);
    M5.Display.setTextColor(C_DIM);
    M5.Display.print(g_cfg.english ? "Any key closes" : "按鍵關閉");
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
            g_carouselIdx = (g_carouselIdx + 1) % CAROUSEL_CARDS;
            return;
        }
        if (g_cfg.appMode == AppMode::Rssi) {
            g_cfg.appMode = AppMode::Bus;
            saveNvs();
            return;
        }
        if (mod) mod->onBtnBPress();
        g_ui = UiScreen::Carousel;
        g_carouselIdx = 0;
        setRotation(0);
    }

    void cycleMode() {
        g_cfg.appMode = (AppMode)(((int)g_cfg.appMode + 1) % (int)AppMode::Count);
        g_ui = UiScreen::Module;
        saveNvs();
    }
};

static KeyEngine g_keys;
static AppMode g_lastMode = AppMode::Count;

static void renderFrame() {
    if (g_ui == UiScreen::QrCode) { wakeDisplay(); renderQr(); return; }

    wakeDisplay();

    AppModule* mod = modFor(g_cfg.appMode);
    if (g_cfg.appMode != g_lastMode) {
        if (g_lastMode != AppMode::Count) modFor(g_lastMode)->onExit();
        mod->onEnter();
        g_lastMode = g_cfg.appMode;
    }
    mod->onLoop();

    bool portrait = true;
    if (g_ui == UiScreen::Carousel) portrait = true;
    else if (mod->forceLandscape()) portrait = false;
    else if (mod->forcePortrait()) portrait = true;

    if (portrait) setRotation(0);
    else if (mod->imu4Way()) updateImu4Way(true);
    else setRotation(1);

    int w = portrait ? PORTRAIT_W : LAND_W;
    int h = portrait ? PORTRAIT_H : LAND_H;

    if (!g_canvas.getBuffer() || g_canvas.width() != w || g_canvas.height() != h) {
        if (g_canvas.getBuffer()) g_canvas.deleteSprite();
        g_canvas.setColorDepth(16);
        g_canvas.createSprite(w, h);
    }

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
    M5.Display.setRotation(0);
    wakeDisplay();
    M5.Display.fillScreen(C_BG);

    g_prefs.begin("m5bus_v6", false);
    uint8_t mac[6];
    WiFi.macAddress(mac);
    char id[13];
    snprintf(id, sizeof(id), "%02X%02X%02X%02X%02X%02X", mac[0], mac[1], mac[2], mac[3], mac[4], mac[5]);
    g_deviceId = id;

    loadNvs();
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
    delay(5);
}
