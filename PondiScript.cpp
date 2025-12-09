// Pondi – Sensor Node (ESP32)
// Behavior: wake -> idle -> connect -> send (CO2 + CH4) Notehub then SD card -> cmd check -> wait -> wake
// Notes published: "sensors.qo" (CO2/tempC_x10/rh_x10) and "ch4.qo" (ch4_v_mV/ch4_rs_ohm/ch4_ppm)

#include <Wire.h>
#include <Notecard.h>
#include <esp_sleep.h>
#include <math.h>
#include <esp_now.h>
#include <WiFi.h>
#include "esp_wifi.h"
#include "FS.h"
#include "SD.h"
#include "SPI.h"
#include "secrets.h"

// SD card SPI pins
#define SCK 14 
#define MISO 12
#define MOSI 13
#define CS 15
bool sd_ok = false;

SPIClass spi = SPIClass(HSPI); // SD Card SPI bus

//I2C Buses
TwoWire scdwire(0);   // SDA=6, SCL=5 @100 kHz
TwoWire notewire(1);  // SDA=8, SCL=7 @50 kHz

uint8_t pump_peer_mac[6] = { 0x80,0xB5,0x4E,0xE8,0xAA,0x70 }; //ESP-NOW Peer MAC for pump contr.
static const uint8_t ESP_NOW_CHANNEL = 6; // Keep in sync with pump peer

Notecard notecard; //Notecard & Wifi
static const char* wifi_ssid   = wifi_name;
static const char* wifi_pass   = wifi_passwd;
static const char* product_uid = projectuid;

// State definitions & variables ------------------------------------------------------------------------------
enum State { ST_WAKE, ST_IDLE, ST_CONNECT, ST_SEND, ST_CMD, ST_WAIT };
State state = ST_WAKE;

uint32_t state_start = 0;
uint32_t next_read_at = 0;
bool did_wake_start = false;
bool did_connect    = false;
bool did_send       = false;
bool did_cmd_check  = false;
bool paused         = false;

uint32_t next_paused_check_at = 0;

int last_co2    = -1; // Init data as -1 for checks later
int last_temp10 = 0;
int last_rh10   = 0;

int last_ch4_mv  = -1;
int last_ch4_rs  = -1;
int last_ch4_ppm = -1;

static bool espnow_ready = false;

#define scd40_addr   0x62 //SCD40 commands from datasheet
#define cmd_wakeup   0x36F6
#define cmd_stop     0x3F86
#define cmd_start    0x21B1
#define cmd_read     0xEC05
#define cmd_set_alt  0x2427
#define cmd_persist  0x3615
const uint16_t altitude_m = 1016; // Boone alt

// State timing
const uint32_t dur_wake  = 30000;
const uint32_t dur_idle  = 10000;
const uint32_t dur_send  = 10000;
const uint32_t dur_wait  = 10000;

const uint32_t power_stabilize_ms     = 5000;
const uint32_t paused_check_period_ms = 5UL * 60UL * 1000UL;
#define stop_sleep_minutes 10

// Soft clock that persists across deep sleep (seconds since first boot)
RTC_DATA_ATTR uint64_t soft_epoch_s = 0;   // cumulative seconds
RTC_DATA_ATTR uint32_t awake_ms_anchor = 0;// millis() snapshot at wake

static inline uint64_t soft_now_s() {
  return soft_epoch_s + (uint64_t)((millis() - awake_ms_anchor) / 1000UL);
}

// CH4 & ADC ---------------------------------------------------------------------------------------------------------------
// TGS2611 divider on ADC1_0 (GPIO1) ; Vout = Vin * (RL / Rs + RL)
static const int   adc_pin_ch4      = 1;      // ADC1_CH0 = GPIO1 on ESP32-S3
static const int   adc_samples_fast = 16;     // number of one-shot readings of V across R-Load that are summed and averaged
static const int   adc_n_avg        = 25;     // perform 25 x 16-one-shots and then average
static const float v_supply_node    = 5.16f;   // divider supply (V)
static const float rl_ohms          = 9520.0f; // R-Load

// Power-law anchors
static const float cal_r1 = 21760.0f;  // Rs ohms @ 300 ppm
static const float cal_p1 = 300.0f;
static const float cal_r2 = 4760.0f;   // Rs ohms @ 10k ppm
static const float cal_p2 = 10000.0f;
static const float ch4_n  = logf(cal_p2 / cal_p1) / logf(cal_r2 / cal_r1); // n for p fit
static const float ch4_k  = cal_p1 / powf(cal_r1, ch4_n); // k for p fit

//CH4 heater duty-cycle control------------------------------------------------------------------------------------
static const int  heaterPin            = 37;     // MOSFET gate GPIO
static const int  HEATER_ON_LEVEL      = HIGH;   // HIGH = ON (low-side N-MOSFET)
static const int  HEATER_OFF_LEVEL     = LOW;    // LOW = OFF

// Period 120s, ON 45s (~37.5%); Read CH4 after ≥30s ON for stability
static const uint32_t HEATER_DUTY_PERIOD_MS         = 120000UL;
static const uint32_t HEATER_DUTY_ON_MS             =  45000UL;
static const uint32_t HEATER_MIN_ON_FOR_READ_MS     =  30000UL;

static bool     heaterIsOn       = false;
static bool     heaterDutyEnable = false;
static uint32_t heaterEdgeMs     = 0;
static uint32_t heaterOnStartMs  = 0;

static inline void heaterWrite(bool on) { // to actually control the mosfet switch
  digitalWrite(heaterPin, on ? HEATER_ON_LEVEL : HEATER_OFF_LEVEL);
  if (on) {
    if (!heaterIsOn) {
      heaterOnStartMs = millis();
      Serial.println("[HEATER] ON");
    }
    heaterIsOn = true;
  } else {
    if (heaterIsOn) Serial.println("[HEATER] OFF");
    heaterIsOn = false;
  }
}

static void heaterInitOnce() { // init heater on boot
  pinMode(heaterPin, OUTPUT);
  heaterWrite(false);
  heaterDutyEnable = false;
  heaterEdgeMs = millis();
  Serial.println("[HEATER] init");
}

static void heaterStartDuty() {
  if (!heaterDutyEnable) {
    heaterDutyEnable = true;
    heaterWrite(true);           // start ON so it warms before CH4 read
    heaterEdgeMs = millis();
    Serial.println("[HEATER] duty start");
  }
}

static void heaterStopDuty() {
  if (heaterDutyEnable || heaterIsOn) {
    heaterDutyEnable = false;
    heaterWrite(false);
    Serial.println("[HEATER] duty stop");
  }
}

static uint32_t heaterOnElapsedMs() { // timer to track ON period
  return heaterIsOn ? (millis() - heaterOnStartMs) : 0;
}

static void heaterDutyTick() { 
  if (!heaterDutyEnable) return;
  const uint32_t now = millis();
  const uint32_t elapsed = now - heaterEdgeMs;

  if (heaterIsOn) {
    if (elapsed >= HEATER_DUTY_ON_MS) {
      heaterWrite(false);
      heaterEdgeMs = now;
    }
  } else {
    if (elapsed >= (HEATER_DUTY_PERIOD_MS - HEATER_DUTY_ON_MS)) {
      heaterWrite(true);
      heaterEdgeMs = now;
    }
  }
}

static inline int32_t ms_since(uint32_t start) { return (int32_t)(millis() - start); } //timer

static int readADCmV_fastGroup() { // Average a small group using calibrated millivolts
  uint32_t acc = 0;
  for (int i = 0; i < adc_samples_fast; ++i) {
    acc += (uint32_t)analogReadMilliVolts(adc_pin_ch4);  // calibrated mV
    delayMicroseconds(150);
  }
  return (int)(acc / adc_samples_fast);
}

static void takeOneCH4Reading_avg25() {
  analogReadResolution(12); // Max resolution = 3.1V / 2^(12) - 1 = 3.1V/4095 => .757mV
  analogSetPinAttenuation(adc_pin_ch4, ADC_11db); //11 dB ~ 0-3.1V V full-scale per esp32 docs; allows for accurate readings up to around 6-7000ppm
                                                  // I sure hope emissions from ponds do not surpass this! That's a lot of methane!

  int64_t sum_mv = 0;
  for (int i = 0; i < adc_n_avg; ++i) sum_mv += (int64_t)readADCmV_fastGroup(); // perform 16-averaged-oneshots 25 times 
  const int   mv    = (int)(sum_mv / adc_n_avg);
  const float vnode = mv / 1000.0f;

  int   rs_i  = -1;
  int   ppm_i = -1;

  if (vnode > 0.005f && vnode < (v_supply_node - 0.001f)) { // Vout = Vin * (RL / Rs + RL) => 
                                                            // Rs = RL * (Vin/Vout - 1)
    const float rs = rl_ohms * ((v_supply_node/vnode) - 1);
    const float ppm = fminf(10000.0f, fmaxf(0.0f, ch4_k * powf(rs, ch4_n))); // ppm = k * Rs^n
    rs_i  = (int)lroundf(rs);
    ppm_i = (int)lroundf(ppm);
  }

  last_ch4_mv  = mv;
  last_ch4_rs  = rs_i;
  last_ch4_ppm = ppm_i;

  Serial.printf("CH4(avg25): Vnode=%d mV  Rs=%d ohm  CH4≈ %d ppm\n", mv, rs_i, ppm_i);
}

// SD Card ---------------------------------------------------------------------------------------------------
// functions from "https://RandomNerdTutorials.com/esp32-microsd-card-arduino/"--------------------------

void listDir(fs::FS &fs, const char * dirname, uint8_t levels){
  Serial.printf("Listing directory: %s\n", dirname);

  File root = fs.open(dirname);
  if(!root){
    Serial.println("Failed to open directory");
    return;
  }
  if(!root.isDirectory()){
    Serial.println("Not a directory");
    return;
  }

  File file = root.openNextFile();
  while(file){
    if(file.isDirectory()){
      Serial.print("  DIR : ");
      Serial.println(file.name());
      if(levels){
        listDir(fs, file.name(), levels -1);
      }
    } else {
      Serial.print("  FILE: ");
      Serial.print(file.name());
      Serial.print("  SIZE: ");
      Serial.println(file.size());
    }
    file = root.openNextFile();
  }
}

void createDir(fs::FS &fs, const char * path){
  Serial.printf("Creating Dir: %s\n", path);
  if(fs.mkdir(path)){
    Serial.println("Dir created");
  } else {
    Serial.println("mkdir failed");
  }
}

void removeDir(fs::FS &fs, const char * path){
  Serial.printf("Removing Dir: %s\n", path);
  if(fs.rmdir(path)){
    Serial.println("Dir removed");
  } else {
    Serial.println("rmdir failed");
  }
}

void readFile(fs::FS &fs, const char * path){
  Serial.printf("Reading file: %s\n", path);

  File file = fs.open(path);
  if(!file){
    Serial.println("Failed to open file for reading");
    return;
  }

  Serial.print("Read from file: ");
  while(file.available()){
    Serial.write(file.read());
  }
  file.close();
}

void writeFile(fs::FS &fs, const char * path, const char * message){
  Serial.printf("Writing file: %s\n", path);

  File file = fs.open(path, FILE_WRITE);
  if(!file){
    Serial.println("Failed to open file for writing");
    return;
  }
  if(file.print(message)){
    Serial.println("File written");
  } else {
    Serial.println("Write failed");
  }
  file.close();
}

void appendFile(fs::FS &fs, const char * path, const char * message){
  Serial.printf("Appending to file: %s\n", path);

  File file = fs.open(path, FILE_APPEND);
  if(!file){
    Serial.println("Failed to open file for appending");
    return;
  }
  if(file.print(message)){
    Serial.println("Message appended");
  } else {
    Serial.println("Append failed");
  }
  file.close();
}

void renameFile(fs::FS &fs, const char * path1, const char * path2){
  Serial.printf("Renaming file %s to %s\n", path1, path2);
  if (fs.rename(path1, path2)) {
    Serial.println("File renamed");
  } else {
    Serial.println("Rename failed");
  }
}

void deleteFile(fs::FS &fs, const char * path){
  Serial.printf("Deleting file: %s\n", path);
  if(fs.remove(path)){
    Serial.println("File deleted");
  } else {
    Serial.println("Delete failed");
  }
}

//ESP-NOW TX Callback ----------------------------------------------------------------------------------------
#if ESP_IDF_VERSION_MAJOR >= 5
void espnow_on_send(const wifi_tx_info_t* /*info*/, esp_now_send_status_t status) {
  Serial.printf("[ESP-NOW TX] %s\n", (status == ESP_NOW_SEND_SUCCESS) ? "SUCCESS" : "FAIL");
}
#else
void espnow_on_send(const uint8_t* /*mac*/, esp_now_send_status_t status) {
  Serial.printf("[ESP-NOW TX] %s\n", (status == ESP_NOW_SEND_SUCCESS) ? "SUCCESS" : "FAIL");
}
#endif

bool espnow_init_once() { // For blocking pump flush cycle, connect to pump esp32 per espnow docs
  if (espnow_ready) return true; // return out if already completed
  WiFi.mode(WIFI_STA);
  esp_wifi_set_promiscuous(true); // set true while channel setting then false again; listen to ALL IEEE wifi frames on set channel (6).
                                  // Basically forces the sensor esp32 to pick up the pump esp32 regardless of the MAC address
  esp_wifi_set_channel(ESP_NOW_CHANNEL, WIFI_SECOND_CHAN_NONE);
  esp_wifi_set_promiscuous(false);

  if (esp_now_init() != ESP_OK) {
    Serial.println("ESP-NOW init failed");
    return false;
  }
  esp_now_peer_info_t peer{};
  memcpy(peer.peer_addr, pump_peer_mac, 6);
  peer.ifidx   = WIFI_IF_STA;
  peer.channel = ESP_NOW_CHANNEL;        // important that this is not 0
  peer.encrypt = false;
  esp_err_t perr = esp_now_add_peer(&peer); // add peer by channel & MAC
  Serial.printf("add_peer -> %d\n", (int)perr);
  if (perr == ESP_ERR_ESPNOW_EXIST) {  // if peer error = peer existed, then all good; via espnow error codes
    esp_now_mod_peer(&peer);
    perr = ESP_OK;
  }
  if (perr != ESP_OK) {
    Serial.println("ESP-NOW add peer failed");
    return false;
  }
  esp_now_register_send_cb(espnow_on_send);
  espnow_ready = true;
  Serial.printf("ESP-NOW ready on channel %u\n", (unsigned)ESP_NOW_CHANNEL);
  return true;
}

bool espnow_send_cmd(const char* msg) { // to send pumps ON or pumps OFF command to the pump peer esp32
  if (!espnow_ready) return false;
  esp_err_t tx = esp_now_send(pump_peer_mac, (const uint8_t*)msg, strlen(msg)+1);
  Serial.printf("esp_now_send('%s') -> %d\n", msg, (int)tx);
  return tx == ESP_OK;
}

//SCD40 Helpers -----------------------------------------------------------------------------------------------------
uint8_t scdCRC(const uint8_t data[2]) { //redundancy check req. for scd40
  uint8_t crc = 0xFF;
  for (int i = 0; i < 2; i++) {
    crc ^= data[i];
    for (int b = 0; b < 8; b++) {
      crc = (crc & 0x80) ? (uint8_t)((crc << 1) ^ 0x31) : (uint8_t)(crc << 1);
    }
  }
  return crc;
}

void scdSend(uint16_t cmd, const char* name) { //Send command
  scdwire.beginTransmission(scd40_addr);
  scdwire.write(cmd >> 8); scdwire.write(cmd & 0xFF);
  uint8_t err = scdwire.endTransmission();
  if (name) {
    Serial.print(name);
    if (err == 0) Serial.println(" OK");
    else { Serial.print(" failed: "); Serial.println(err); }
  }
}

bool scdRead(uint8_t *buf, uint8_t len) {//Read data
  if (scdwire.requestFrom(scd40_addr, len) != len) return false;
  for (uint8_t i = 0; i < len; i++) buf[i] = scdwire.read();
  return true;
}

void scd_setAltitude(uint16_t alt_m) {//Set boone alt. for scd40
  uint8_t d[2] = { (uint8_t)(alt_m >> 8), (uint8_t)(alt_m & 0xFF) };
  uint8_t c = scdCRC(d);
  scdwire.beginTransmission(scd40_addr);
  scdwire.write(cmd_set_alt >> 8); scdwire.write(cmd_set_alt & 0xFF);
  scdwire.write(d[0]); scdwire.write(d[1]); scdwire.write(c);
  scdwire.endTransmission();
  scdSend(cmd_persist, "Persist settings");
}

void takeOneCO2Reading() { // Must be every 5 sec not instantaneous
  scdSend(cmd_read, nullptr);
  delay(2);

  uint8_t d[9];
  if (!scdRead(d, 9)) { Serial.println("SCD40: read failed"); return; }

  auto wordAt = [&](int i)->int { // To pull out the co2/temp/rh data from return data
    uint8_t w[2] = { d[i], d[i+1] };
    if (d[i+2] != scdCRC(w)) return -1; //CRC check
    return ((int)w[0] << 8) | w[1];
  };

  const int co2  = wordAt(0); // locations per datasheet
  const int rawt = wordAt(3);
  const int rawh = wordAt(6);
  if (co2 < 0 || rawt < 0 || rawh < 0) { Serial.println("SCD40: CRC error"); return; }

  const float tc = -45.0f + 175.0f * (rawt / 65535.0f); //per datasheet conversions
  const float rh = 100.0f * (rawh / 65535.0f);

  last_co2    = co2;
  last_temp10 = (int)lroundf(tc * 10.0f);
  last_rh10   = (int)lroundf(rh * 10.0f);

  Serial.printf("CO2: %d ppm, Temp: %.1f C, RH: %.1f %%\n", last_co2, tc, rh);
}

// Notecard Helpers ----------------------------------------------------------------------------------------------------
void note_configureWifiOnce() { // config wifi => change to cellular config and change the Setup() command once SIM purchased
  if (!wifi_ssid || !wifi_pass) return;
  J *req = notecard.newRequest("card.wifi");
  if (req) {
    JAddStringToObject(req, "ssid", wifi_ssid);
    JAddStringToObject(req, "password", wifi_pass);
    notecard.sendRequest(req);
  }
}

void note_setHubMode(const char* mode, bool wifiOnly) { // To set to minimum or continuous mode
  J *req = notecard.newRequest("hub.set");
  if (req) {
    JAddStringToObject(req, "product", product_uid);
    JAddStringToObject(req, "mode", mode);
    if (wifiOnly) JAddBoolToObject(req, "wifi", true);
    notecard.sendRequest(req);
  }
  Serial.printf("Notecard mode -> %s\n", mode);
}

bool note_waitConnected(uint32_t timeout_ms) { // Wait until connection is established and then secure
  Serial.println("Waiting for Notehub connection (bounded)...");
  const uint32_t deadline = millis() + timeout_ms;
  for (;;) {
    J *req = notecard.newRequest("hub.status");
    if (req) {
      J *rsp = notecard.requestAndResponse(req);
      if (rsp) {
        bool connected = JGetBool(rsp, "connected");
        const char* status = JGetString(rsp, "status");
        Serial.printf("  connected=%s status=%s\n", connected ? "true" : "false", status ? status : "(null)");
        notecard.deleteResponse(rsp);
        if (connected) { delay(3000); return true; }
      }
    }
    if ((int32_t)(millis() - deadline) >= 0) return false;
    delay(1000);
  }
}

// Publish helpers (two separate notes); I couldn't get 1 note with all data to publish ----------------------------------------------------------
static void note_publish_CO2() { // CO2 Note
  if (last_co2 < 0) { Serial.println("No CO2 data to send."); return; }
  J *req = notecard.newRequest("note.add");
  if (!req) { Serial.println("note.add alloc failed (CO2)"); return; }
  JAddStringToObject(req, "file", "sensors.qo");
  J *body = JCreateObject();
  if (body) {
    JAddNumberToObject(body, "co2",       last_co2);
    JAddNumberToObject(body, "tempC_x10", last_temp10);
    JAddNumberToObject(body, "rh_x10",    last_rh10);
    JAddItemToObject(req, "body", body);
  }
  if (notecard.sendRequest(req)) Serial.println("CO2 note queued OK.");
  else                           Serial.println("CO2 note timeout; will try next cycle.");
}

static void note_publish_CH4() { // CH4 Note
  if (last_ch4_mv < 0 && last_ch4_rs < 0 && last_ch4_ppm < 0) {
    Serial.println("No CH4 data to send.");
    return;
  }
  J *req = notecard.newRequest("note.add");
  if (!req) { Serial.println("note.add alloc failed (CH4)"); return; }
  JAddStringToObject(req, "file", "ch4.qo");
  J *body = JCreateObject();
  if (body) {
    JAddNumberToObject(body, "ch4_v_mV",   (last_ch4_mv  >= 0) ? last_ch4_mv  : 0);
    JAddNumberToObject(body, "ch4_rs_ohm", (last_ch4_rs  >= 0) ? last_ch4_rs  : 0);
    JAddNumberToObject(body, "ch4_ppm",    (last_ch4_ppm >= 0) ? last_ch4_ppm : 0);
    JAddItemToObject(req, "body", body);
  }
  if (notecard.sendRequest(req)) Serial.println("CH4 note queued OK.");
  else                           Serial.println("CH4 note timeout; will try next cycle.");
}

bool note_sendLatest() {
  Serial.println("Sending latest readings to Notehub (CO2 then CH4)...");
  note_publish_CO2();
  delay(100);
  note_publish_CH4();
  return true; // queue regardless; reliability handled by Notehub/device retries
}

//Device Info (device.qo) (Unused rn but could add into dashboard later)------------------------------------------------------------------------
void note_publishDeviceInfo() {
  J *r1 = notecard.newRequest("card.device");
  J *d1 = r1 ? notecard.requestAndResponse(r1) : nullptr;

  J *r2 = notecard.newRequest("card.status");
  J *d2 = r2 ? notecard.requestAndResponse(r2) : nullptr;

  J *add = notecard.newRequest("note.add");
  if (add) {
    JAddStringToObject(add, "file", "device.qo");
    J *b = JCreateObject();
    if (b) {
      const char* uid = d1 ? JGetString(d1,"device")  : nullptr;
      const char* sku = d1 ? JGetString(d1,"sku")     : nullptr;
      const char* ver = d1 ? JGetString(d1,"version") : nullptr;
      const char* st  = d2 ? JGetString(d2,"status")  : nullptr;
      bool conn       = d2 ? JGetBool(d2,"connected") : false;

      JAddStringToObject(b, "device",   uid ? uid : "");
      JAddStringToObject(b, "sku",      sku ? sku : "");
      JAddStringToObject(b, "version",  ver ? ver : "");
      JAddStringToObject(b, "status",   st  ? st  : "");
      JAddBoolToObject  (b, "connected", conn);

      JAddItemToObject(add, "body", b);
    }
    (void)notecard.sendRequest(add);
  }

  if (d1) notecard.deleteResponse(d1);
  if (d2) notecard.deleteResponse(d2);
}

// Sleep & User Commands --------------------------------------------------------------------------------------------------
void goToTimedSleep(uint32_t minutes) {
  scdSend(cmd_stop, "Sleep: SCD40 idle");
  note_setHubMode("minimum", true);
  Serial.printf("Entering deep sleep for %u minute(s).\n", (unsigned)minutes);
  soft_epoch_s += (uint64_t)((millis() - awake_ms_anchor) / 1000UL); //for soft clock offline writes
  soft_epoch_s += (uint64_t)minutes * 60ULL;
  delay(200);
  uint64_t us = (uint64_t)minutes * 60ULL * 1000000ULL;
  esp_sleep_enable_timer_wakeup(us);
  heaterStopDuty(); //ensure heater is off before deep sleep 
  esp_deep_sleep_start();
}

static void issue_FRC(uint16_t refppm) { // Command for forced recalibration to set known point
  scdSend(cmd_stop, "Stop before FRC");
  delay(500);
  uint8_t d[2] = { (uint8_t)(refppm>>8), (uint8_t)(refppm & 0xFF) };
  uint8_t c = scdCRC(d);
  scdwire.beginTransmission(scd40_addr);
  scdwire.write(0x36); scdwire.write(0x2F);
  scdwire.write(d[0]); scdwire.write(d[1]); scdwire.write(c);
  scdwire.endTransmission();
  delay(400);
  scdSend(cmd_persist, "Persist settings");
  delay(300);
  scdSend(cmd_start, "Restart after FRC");
  Serial.println("FRC issued.");
}

void do_flush_blocking() {
  Serial.println("[FLUSH] Preparing rails, pausing everything else..."); // set everything to minimum to allow pumps max current
  scdSend(cmd_stop, "Stop SCD40 for flush");
  note_setHubMode("minimum", true);
  delay(300);

  if (!espnow_init_once()) {
    Serial.println("[FLUSH] ESP-NOW not ready; abort.");
    return;
  }

  const uint32_t flush_ms = 300000UL;  // 5 minutes
  const uint32_t reassert_ms = 2000UL; // resend pump_on every 2s
  uint32_t next_assert = 0;
  const uint32_t end_at = millis() + flush_ms;

  Serial.println("[FLUSH] pump_on");
  (void)espnow_send_cmd("pump_on");

  while ((int32_t)(millis() - end_at) < 0) {
    if ((int32_t)(millis() - next_assert) >= 0) {
      (void)espnow_send_cmd("pump_on"); // counter packet loss
      next_assert = millis() + reassert_ms;
    }
    (void)note_fetchAndExecuteCommand(); // allow remote abort/pause/etc.
    heaterDutyTick();                    // keep heater state alive
    delay(25);
  }

  Serial.println("[FLUSH] pump_off");
  (void)espnow_send_cmd("pump_off");

  Serial.println("[FLUSH] Done. Resuming normal cycle.");
}

bool note_fetchAndExecuteCommand() {
  J *req = notecard.newRequest("note.get");
  if (!req) return false;
  JAddStringToObject(req, "file", "cmd.qi"); // command file sent from webpage
  JAddBoolToObject(req, "delete", true); // delete it
  J *rsp = notecard.requestAndResponse(req); // Get the file then delete
  if (!rsp) return false;

  J *body = JGetObject(rsp, "body");
  if (!body) { notecard.deleteResponse(rsp); return false; }

  const char* cmd = JGetString(body, "cmd");
  const char* arg = JGetString(body, "arg");
  if (!cmd) { notecard.deleteResponse(rsp); return false; }

  Serial.print("[CMD] "); Serial.print(cmd);
  if (arg) { Serial.print(" "); Serial.print(arg); }
  Serial.println();
  //Command actions
  if (!strcasecmp(cmd, "pause")) {
    paused = true;
    scdSend(cmd_stop, "Pause: stop SCD40");
    note_setHubMode("minimum", true);
    Serial.println("Paused.");
  } 
  else if (!strcasecmp(cmd, "resume")) {
    paused = false;
    // fall back into normal state machine loop
    Serial.println("Resumed.");
  }
  else if (!strcasecmp(cmd, "stop")) {
    uint32_t minutes = stop_sleep_minutes;
    if (arg) {
      long v = atol(arg);
      if (v > 0 && v < 24L * 60L) minutes = (uint32_t)v;
    }
    goToTimedSleep(minutes);
  }
  else if (!strcasecmp(cmd, "start")) {
    Serial.println("Start requested: restarting MCU.");
    delay(100);
    ESP.restart();
  }
  else if (!strcasecmp(cmd, "detreq")) {
    paused = true;
    scdSend(cmd_stop, "detreq: stop SCD40");
    note_setHubMode("continuous", true);
    (void)note_waitConnected(20000);
    note_publishDeviceInfo();
    note_setHubMode("minimum", true);
    Serial.println("detreq complete; device remains paused.");
  }
  else if (!strcasecmp(cmd, "frc")) {
    int refppm = arg ? atoi(arg) : 0;
    if (refppm>=350 && refppm<=2000) issue_FRC((uint16_t)refppm);
    else Serial.println("FRC ignored: ppm out of range (350..2000).");
  }
  else if (!strcasecmp(cmd, "flush")) {
    do_flush_blocking();
  }

  notecard.deleteResponse(rsp);
  return true;
}

bool connectAndCheckOnce() {
  Serial.println("[CMD-CHECK] Bringing Notecard online to check commands...");
  note_setHubMode("continuous", true);
  (void)note_waitConnected(20000);
  awake_ms_anchor = millis();   // re-anchor soft clock after the blocking wait

  bool handled_any = false;
  for (int attempts = 0; attempts < 5; ++attempts) {
    bool got = note_fetchAndExecuteCommand();
    if (!got) break;
    handled_any = true;
  }

  note_setHubMode("minimum", true);
  Serial.println("[CMD-CHECK] Done.");
  return handled_any;
}

// Next state func. & enter state serial print / current state timestamp -------------------------------------------------------
State nextState(State p) {
  switch (p) {
    case ST_WAKE:    return ST_IDLE;
    case ST_IDLE:    return ST_CONNECT;
    case ST_CONNECT: return ST_SEND;
    case ST_SEND:    return ST_CMD;
    case ST_CMD:     return ST_WAIT;
    case ST_WAIT:    return ST_WAKE;
  }
  return ST_WAKE;
}

void enterState(State p) {
  state = p;
  state_start = millis();
  did_wake_start = did_connect = did_send = did_cmd_check = false;

  switch (state) {
    case ST_WAKE:    Serial.println("[STATE] WAKE (0–30s)");        heaterStartDuty(); break; //start heater duty cycle
    case ST_IDLE:    Serial.println("[STATE] IDLE (30–40s)");       break;
    case ST_CONNECT: Serial.println("[STATE] CONNECT (auto)");      break;
    case ST_SEND:    Serial.println("[STATE] SEND (~10s)");         break;
    case ST_CMD:     Serial.println("[STATE] CMD-CHECK");           break;
    case ST_WAIT:    Serial.println("[STATE] WAIT (~10s)");         break;
  }
}

// Setup & full system loop cycle ---------------------------------------------------------------------------------------
void setup() {
  Serial.begin(115200); // init serial for command shim
  delay(500);

  scdwire.begin(6, 5, 100000); // init scd40 i2c
  notewire.begin(8, 7, 50000); // init notecard i2c 

  spi.begin(SCK, MISO, MOSI, CS); // init SD card spi

  if (!SD.begin(CS, spi, 40000000)) { // Write data file if it doesn't exist yet, change bus speed to 20Mhz if 40Mhz unreliable
    Serial.println("SD init failed; continuing without SD logging");
    sd_ok = false;} 
  else {
    sd_ok = (SD.cardType() != CARD_NONE);
    if (sd_ok && !SD.exists("/data.csv")) {
      writeFile(SD, "/data.csv", "soft_s,tempC_x10,rh_x10,co2_ppm,ch4_v_mV,ch4_rs_ohm,ch4_ppm\r\n");}
  }

  awake_ms_anchor = millis(); // for soft-clock offline data writing

  notecard.begin(0x17, 50000, notewire); // set bus speed 50khz
  notecard.setDebugOutputStream(Serial); // debug sent to serial output

  note_configureWifiOnce(); // wifi config from password and network name & then set to minimum
  note_setHubMode("minimum", true);

  scdSend(cmd_wakeup, "Wake-up"); delay(500); // 1 time wakeup and set altitude at setup. Writes limited to around 1000cycles so don't abuse
  scd_setAltitude(altitude_m);
  delay(300);
  scdSend(cmd_stop,    "Ensure idle"); delay(300);

  // One-shot command check if we woke from deep sleep
  if (esp_sleep_get_wakeup_cause() == ESP_SLEEP_WAKEUP_TIMER) {
    Serial.println("[BOOT] Woke from deep-sleep timer. Performing one-shot command check.");
    bool handled = connectAndCheckOnce();
    if (!handled) {
      note_setHubMode("minimum", true);
      delay(200);
      goToTimedSleep(stop_sleep_minutes);
    }
  }

  // heater init 
  heaterInitOnce();

  next_paused_check_at = millis() + paused_check_period_ms;
  enterState(ST_WAKE);
}

void loop() {
  // Serial command shim
  if (Serial.available()) {
    String s = Serial.readStringUntil('\n'); s.trim();

    if (s.equalsIgnoreCase("pause")) {
      paused = true;
      scdSend(cmd_stop, "Pause: stop SCD40");
      note_setHubMode("minimum", true);
      next_paused_check_at = millis() + paused_check_period_ms;
      Serial.println("Paused.");
    } else if (s.equalsIgnoreCase("resume")) {
      paused = false;
      Serial.println("Resumed.");
    } else if (s.startsWith("stop")) {
      uint32_t minutes = stop_sleep_minutes;
      int sp = s.indexOf(' ');
      if (sp > 0) {
        long v = s.substring(sp+1).toInt();
        if (v > 0 && v < 24L * 60L) minutes = (uint32_t)v;
      }
      goToTimedSleep(minutes);
    } else if (s.equalsIgnoreCase("start")) {
      Serial.println("Start requested: restarting MCU.");
      delay(100);
      ESP.restart();
    } else if (s.startsWith("frc")) {
      int sp = s.indexOf(' ');
      int val = (sp>0) ? s.substring(sp+1).toInt() : 0;
      if (val>=350 && val<=2000) issue_FRC((uint16_t)val);
      else Serial.println("Usage: frc <ppm> (350..2000)");
    } else if (s.equalsIgnoreCase("detreq")) {
      paused = true;
      scdSend(cmd_stop, "detreq: stop SCD40");
      note_setHubMode("continuous", true);
      (void)note_waitConnected(20000);
      note_publishDeviceInfo();
      note_setHubMode("minimum", true);
      next_paused_check_at = millis() + paused_check_period_ms;
      Serial.println("detreq complete; device remains paused.");
    } else if (s.equalsIgnoreCase("flush")) {
      do_flush_blocking();
    }
  }

  // tick heater duty
  heaterDutyTick();

  if (paused) { // periodically wake Notehub to check for commands, then go back to low power
    if (ms_since(next_paused_check_at) >= 0) {
      bool handled = connectAndCheckOnce();
      note_setHubMode("minimum", true);
      delay(power_stabilize_ms);
      next_paused_check_at = millis() + paused_check_period_ms;
      (void)handled;
    }
    // ensure heater is OFF while paused
    heaterStopDuty();
    delay(25);
    return;
  }

  // Actual State machine
  uint32_t elapsed = millis() - state_start;
  bool state_complete = false;

  switch (state) {
    case ST_WAKE:
      if (!did_wake_start) {
        scdSend(cmd_wakeup, "Wake-up"); delay(500);
        scdSend(cmd_start,  "Start measurement");
        next_read_at = millis() + 5000;// scd40 measurements must be every 5 seconds per datasheet; not instantaneous
        did_wake_start = true;
      }
      if ((int32_t)(millis() - next_read_at) >= 0 && elapsed < dur_wake) {
        takeOneCO2Reading();
        next_read_at += 5000UL;
      }
      if (elapsed >= dur_wake) {
        if (heaterOnElapsedMs() >= HEATER_MIN_ON_FOR_READ_MS) {// ensure heater was ON long enough before CH4 read
          Serial.println("[HEATER] warm enough for CH4 read");
          takeOneCH4Reading_avg25(); 
        } else {
          Serial.println("[HEATER] not warm enough; forcing ON before CH4 read next cycle");
          heaterWrite(true);
          takeOneCH4Reading_avg25(); // still take reading this cycle to retain current behavior, incr. duty cycle if consistent zeroes appear
        }
        scdSend(cmd_stop, "Stop before CONNECT");
        state_complete = true;
      }
      break;

    case ST_IDLE:
      if (elapsed >= dur_idle) state_complete = true;
      break;

    case ST_CONNECT:
      if (!did_connect) {
        note_setHubMode("continuous", true);
        (void)note_waitConnected(20000);   // try up to ~20s, then continue regardless
        awake_ms_anchor = millis();   // re-anchor soft clock after blocking wait
        note_setHubMode("minimum", true);  // back to low power if failed
        did_connect = true;
      }
      state_complete = true;
      break;

    case ST_SEND:
      if (!did_send) { (void)note_sendLatest(); did_send = true; } //Notehub write

      if (sd_ok) { //SD card write
        String dataMessage =
          String((uint32_t)soft_now_s()) + "," +
          String(last_temp10) + "," +
          String(last_rh10)   + "," +
          String(last_co2)    + "," +
          String(last_ch4_mv) + "," +
          String(last_ch4_rs) + "," +
          String(last_ch4_ppm) + "\r\n";
        appendFile(SD, "/data.csv", dataMessage.c_str());
      }

      if (elapsed >= dur_send) state_complete = true;
      break;

    case ST_CMD:
      if (!did_cmd_check) {
        // up to 5 command notes processed; connection reused from ST_CONNECT
        for (int attempts = 0; attempts < 5; ++attempts) {
          bool got = note_fetchAndExecuteCommand();
          if (!got) break;
        }
        note_setHubMode("minimum", true);
        delay(power_stabilize_ms);
        did_cmd_check = true;
      }
      state_complete = true;
      break;

    case ST_WAIT:
      if (elapsed >= dur_wait) state_complete = true;
      break;
  }

  if (state_complete) enterState(nextState(state)); // state_reg <= state_next
  delay(10);
}
