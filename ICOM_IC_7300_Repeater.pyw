import serial
from serial.tools import list_ports
import time
import threading
import os
import json
import pyaudio
import numpy as np
import wave
import traceback
from datetime import datetime
from tkinter import (
    Tk, Label, Button, StringVar, W, E, scrolledtext, OptionMenu, BooleanVar, Frame, Canvas, Checkbutton, filedialog, Entry,
    N, S
)
from scipy import signal

# --- GLOBALE KONFIGURATION ---

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
SAVE_DIR = os.path.join(BASE_DIR, "Audio Data")
CONFIG_FILE = os.path.join(BASE_DIR, "repeater_config.json")
LOG_FILE = os.path.join(BASE_DIR, "repeater_log.txt")

# Kennungs-Konfiguration
ROGER_BEEP_FILE = ""

# CI-V Befehle für ICOM IC-7300
PTT_ON_CMD = b'\xfe\xfe\x94\xe0\x1c\x00\x01\xfd'
PTT_OFF_CMD = b'\xfe\xfe\x94\xe0\x1c\x00\x00\xfd'
SQUELCH_STATUS_CMD = b'\xfe\xfe\x94\xe0\x15\x05\xfd'
SET_USB_MOD_LEVEL_100 = b'\xfe\xfe\x94\xe0\x1a\x05\x00\x65\x02\x55\xfd'

# METER BEFEHLE
SMETER_LEVEL_CMD = b'\xfe\xfe\x94\xe0\x15\x02\xfd' # S-Meter Pegel (0000 bis 0255)
ALC_LEVEL_CMD = b'\xfe\xfe\x94\xe0\x15\x13\xfd'   # NEU: ALC Meter Pegel (0000 bis 0255)

# MAXIMALE METER WERTE (Laut IC-7300 Doku)
MAX_METER_VAL = 255 # Maximalwert für S-Meter und ALC

BAUD_RATE = 19200
TIMEOUT = 0.1

# Audio Parameter (Spezifikation ICOM IC-7300 USB Audio Codec)
CHUNK = 1024
FORMAT = pyaudio.paInt16
CHANNELS = 2
RATE = 48000
MAX_REC_TIME_SEC = 120

# Globale Zustandsvariablen
serial_port = None
is_repeater_enabled = False
is_saving_enabled = False
is_roger_beep_enabled = False
is_recording = False
audio_frames = []
audio_lock = threading.Lock()
squelch_thread = None
stop_squelch_thread = False
alc_thread = None
stop_alc_thread = False # Steuerflag für den ALC Thread
pa = None
stream = None
is_transmitting = False

# Echosperre
last_transmission_end = 0
HANGTIME_AFTER_TX = 2.0

# Audio Indexe
AUDIO_INDEX = None
TX_AUDIO_INDEX = None

# GUI-Elemente
app = None
status_var = None
log_area = None
port_var = None
baud_var = None
tx_audio_var = None
rx_audio_var = None
repeater_enabled_var = None
save_enabled_var = None
roger_beep_enabled_var = None
roger_beep_file_var = None
squelch_status_var = None
rx_meter_canvas = None
tx_meter_canvas = None 
gain_var = None

# --- GLOBALE VARIABLEN FÜR VU-METER (CI-V basiert) ---
RX_METER_LEVEL_LOCK = threading.Lock()
RX_METER_WIDTH = 0
RX_METER_COLOR = 'gray'

# NEU: ALC Meter
TX_METER_LEVEL_LOCK = threading.Lock()
TX_METER_WIDTH = 0
TX_METER_COLOR = 'gray'
max_alc_level = 0
alc_monitoring_active = False # Flag, ob der ALC-Thread läuft

# --- HILFSFUNKTIONEN ---

def log_message(message, is_error=False):
    """Fügt eine Nachricht zum Log-Bereich hinzu."""
    global log_area
    timestamp = datetime.now().strftime("[%H:%M:%S] ")
    full_message = timestamp + message

    try:
        os.makedirs(os.path.dirname(LOG_FILE), exist_ok=True)
        with open(LOG_FILE, 'a', encoding='utf-8') as f:
            f.write(full_message + "\n")
    except Exception as e:
        print(f"[KRITISCHER FEHLER] Log-Datei: {e}")

    if log_area:
        # Die Färbung wird beibehalten, falls WARNUNG/FEHLER/DEBUG noch auftauchen
        color = "red" if is_error else ("orange" if "WARNUNG" in message or "DEBUG" in message else "black") 
        # Füge die Nachricht im GUI-Thread hinzu, um Fehler zu vermeiden
        app.after(0, lambda: log_area.insert("end", full_message + "\n", color))
        app.after(0, lambda: log_area.see("end"))
    else:
        print(f"[{'FEHLER' if is_error else 'INFO'}] {message}")

def list_serial_ports():
    """Listet verfügbare serielle Ports auf."""
    try:
        return [port.device for port in list_ports.comports()]
    except Exception as e:
        log_message(f"FEHLER beim Auflisten der seriellen Ports: {e}", is_error=True)
        return []

def list_audio_devices():
    """Listet verfügbare Audio-Geräte auf."""
    p = None
    devices = {}
    input_fallback_index = None
    output_fallback_index = None

    try:
        p = pyaudio.PyAudio()
        for i in range(p.get_device_count()):
            info = p.get_device_info_by_index(i)
            device_name = info['name']

            # Wir suchen nach spezifischen Audio-Gerätenamen, z.B. "USB Audio CODEC"
            if 'USB Audio CODEC' in device_name:
                if info['maxInputChannels'] > 0:
                    name = f"RX: {device_name}"
                    devices[name] = i
                    if input_fallback_index is None:
                        input_fallback_index = i

                if info['maxOutputChannels'] > 0:
                    name = f"TX: {device_name}"
                    devices[name] = i
                    if output_fallback_index is None:
                        output_fallback_index = i
    except Exception as e:
        log_message(f"FEHLER Audio-Geräte: {e}", is_error=True)
        devices = {
            "RX: System Input": 0,
            "TX: System Output": 1
        }
    finally:
        if p:
            p.terminate()

    return devices, input_fallback_index, output_fallback_index

def send_ci_v_command(command, wait_response=False):
    """Sendet einen CI-V Befehl."""
    global serial_port
    if serial_port and serial_port.is_open:
        try:
            # Setze einen kurzen Timeout für die Antwort, falls keine Antwort erwartet wird
            original_timeout = serial_port.timeout
            serial_port.timeout = TIMEOUT
            
            serial_port.reset_input_buffer()
            serial_port.write(command)

            if wait_response:
                time.sleep(0.01) # Kurze Wartezeit vor dem Lesen
                response = serial_port.read(30) # Lese bis zu 30 Bytes
                serial_port.timeout = original_timeout # Timeout zurücksetzen
                return response
            
            serial_port.timeout = original_timeout # Timeout zurücksetzen
            return None

        except Exception as e:
            # log_message(f"FEHLER CI-V: {e}", is_error=True) # Zu viele Meldungen
            return None
    return None

def read_squelch_status():
    """Liest den Squelch-Status vom ICOM IC-7300 via CI-V Befehl 15 05."""
    response = send_ci_v_command(SQUELCH_STATUS_CMD, wait_response=True)

    if response:
        try:
            # Suchen nach der Startsequenz des Rückgabebefehls (FE FE E0 94 15 05)
            start_sequence = b'\xfe\xfe\xe0\x94\x15\x05'
            if start_sequence in response:
                idx = response.find(start_sequence)
                if idx != -1 and len(response) >= idx + 7:
                    status_byte = response[idx + 6]
                    # 0x01 = Squelch offen (Signal da)
                    return status_byte == 0x01
        except Exception as e:
            log_message(f"FEHLER beim Parsen der Squelch-Antwort: {e}", is_error=True)

    return False

def bcd_to_int(bcd_bytes):
    """Konvertiert 4 BCD-Bytes (DD DD DD DD) in eine Integer-Zahl (0 bis 255)."""
    try:
        # Dies ist die ICOM BCD-Interpretation für Meter:
        # bcd_bytes[0] = Hunderter-Ziffer (00h oder 02h)
        # bcd_bytes[1] = Zehner- und Einer-Ziffer (als BCD)
        
        # BCD-Zahl aus Byte 1 (0-99):
        tens = (bcd_bytes[1] >> 4) * 10 
        ones = bcd_bytes[1] & 0x0F
        
        # BCD-Zahl aus Byte 0 (0-9):
        hundreds = bcd_bytes[0] & 0x0F
        
        return int(hundreds * 100 + tens + ones)

    except Exception:
        return 0

def read_smeter_level():
    """Liest den S-Meter-Pegel (0000 bis 0255) vom ICOM IC-7300 via CI-V Befehl 15 02."""
    response = send_ci_v_command(SMETER_LEVEL_CMD, wait_response=True)
    
    if response:
        try:
            start_sequence = b'\xfe\xfe\xe0\x94\x15\x02'
            
            # Die folgenden DEBUG-Meldungen werden entfernt
            # if response.find(b'\x15\x02') != -1:
            #      log_message(f"DEBUG RX S-METER RESPONSE (RAW): {response.hex()}", is_error=False)
            
            if start_sequence in response:
                idx = response.find(start_sequence)
                
                if idx != -1 and len(response) >= idx + 8: 
                    # Extrahiere nur die ZWEI Datenbytes (Byte 6 und 7)
                    data_bytes = response[idx + 6 : idx + 8] 
                    
                    # Die folgenden DEBUG-Meldungen werden entfernt
                    # log_message(f"DEBUG RX S-METER DATA: {data_bytes.hex()}", is_error=False)

                    # Fülle auf 4 Bytes mit Null-Bytes, da bcd_to_int 4 erwartet.
                    smeter_level = bcd_to_int(data_bytes + b'\x00\x00')
                    
                    return min(smeter_level, MAX_METER_VAL)

        except Exception as e:
            # log_message(f"FEHLER beim Parsen der S-Meter-Antwort: {e}", is_error=True)
            pass

    return 0 # Pegel 0 bei Fehler

def read_alc_level():
    """Liest den ALC-Pegel (0000 bis 0255) vom ICOM IC-7300 via CI-V Befehl 15 13 (NEU)."""
    response = send_ci_v_command(ALC_LEVEL_CMD, wait_response=True)
    
    if response:
        try:
            # Erwartete Antwort: FE FE E0 94 15 13 [DATA (2 Bytes)] FD
            start_sequence = b'\xfe\xfe\xe0\x94\x15\x13'
            
            # Die folgenden DEBUG-Meldungen werden entfernt
            # if response.find(b'\x15\x13') != -1:
            #      log_message(f"DEBUG TX ALC RESPONSE (RAW): {response.hex()}", is_error=False)
            
            if start_sequence in response:
                idx = response.find(start_sequence)
                
                if idx != -1 and len(response) >= idx + 8: 
                    # Extrahiere nur die ZWEI Datenbytes (Byte 6 und 7)
                    data_bytes = response[idx + 6 : idx + 8]
                    
                    # Die folgenden DEBUG-Meldungen werden entfernt
                    # log_message(f"DEBUG TX ALC DATA: {data_bytes.hex()}", is_error=False)
                    
                    # Fülle auf 4 Bytes mit Null-Bytes, da bcd_to_int 4 erwartet.
                    alc_level = bcd_to_int(data_bytes + b'\x00\x00')
                    
                    return min(alc_level, MAX_METER_VAL)

        except Exception as e:
            # log_message(f"FEHLER beim Parsen der ALC-Antwort: {e}", is_error=True)
            pass

    return 0 # Pegel 0 bei Fehler

# --- KONFIGURATION ---
def get_audio_name_by_index(index, device_list):
    """Sucht Audiogerät nach Index."""
    for name, idx in device_list.items():
        if idx == index:
            return name
    return None

def select_roger_beep_file():
    """Öffnet Dialog zur Auswahl der Kennungs-WAV-Datei."""
    global ROGER_BEEP_FILE
    new_path = filedialog.askopenfilename(
        defaultextension=".wav",
        filetypes=[("WAV files", "*.wav")],
        title="Wählen Sie die Kennungs-WAV-Datei"
    )
    if new_path:
        ROGER_BEEP_FILE = new_path
        roger_beep_file_var.set(os.path.basename(new_path))
        log_message(f"INFO: Kennungsdatei ausgewählt: {ROGER_BEEP_FILE}")
        save_config()
    else:
        log_message("INFO: Kennungsdatei-Auswahl abgebrochen.")


def save_config():
    """Speichert Konfiguration."""
    global AUDIO_INDEX, TX_AUDIO_INDEX, is_repeater_enabled, is_saving_enabled, ROGER_BEEP_FILE, is_roger_beep_enabled, gain_var

    is_repeater_enabled = repeater_enabled_var.get()
    is_saving_enabled = save_enabled_var.get()
    is_roger_beep_enabled = roger_beep_enabled_var.get()

    try:
        gain_value = float(gain_var.get())
    except:
        gain_value = 1.5

    config = {
        'port': port_var.get(),
        'baudrate': baud_var.get(),
        'audio_index': AUDIO_INDEX,
        'tx_audio_index': TX_AUDIO_INDEX,
        'repeater_enabled': is_repeater_enabled,
        'is_saving_enabled': is_saving_enabled,
        'roger_beep_enabled': is_roger_beep_enabled,
        'roger_beep_file': ROGER_BEEP_FILE,
        'tx_gain_factor': gain_value
    }
    try:
        with open(CONFIG_FILE, 'w') as f:
            json.dump(config, f, indent=4)
        log_message("INFO: Konfiguration gespeichert.")
    except Exception as e:
        log_message(f"FEHLER Speichern: {e}", is_error=True)

def load_config():
    """Lädt Konfiguration."""
    global AUDIO_INDEX, TX_AUDIO_INDEX, is_repeater_enabled, is_saving_enabled, ROGER_BEEP_FILE, is_roger_beep_enabled

    audio_devices, input_fallback, output_fallback = list_audio_devices()

    AUDIO_INDEX = input_fallback
    TX_AUDIO_INDEX = output_fallback
    tx_gain_factor = 1.5

    try:
        with open(CONFIG_FILE, 'r') as f:
            config = json.load(f)

        ports = list_serial_ports()
        default_port = ports[0] if ports else "COM1"

        port_var.set(config.get('port', default_port))
        baud_var.set(str(config.get('baudrate', BAUD_RATE)))

        AUDIO_INDEX = config.get('audio_index', AUDIO_INDEX)
        TX_AUDIO_INDEX = config.get('tx_audio_index', TX_AUDIO_INDEX)

        is_repeater_enabled = config.get('repeater_enabled', is_repeater_enabled)
        is_saving_enabled = config.get('is_saving_enabled', is_saving_enabled)
        is_roger_beep_enabled = config.get('roger_beep_enabled', False)
        ROGER_BEEP_FILE = config.get('roger_beep_file', "")
        tx_gain_factor = config.get('tx_gain_factor', tx_gain_factor)

        rx_name = get_audio_name_by_index(AUDIO_INDEX, audio_devices)
        if rx_name:
            rx_audio_var.set(rx_name)
        else:
            for name, idx in audio_devices.items():
                if 'RX:' in name or 'Input' in name:
                    rx_audio_var.set(name)
                    AUDIO_INDEX = idx
                    break

        tx_name = get_audio_name_by_index(TX_AUDIO_INDEX, audio_devices)
        if tx_name:
            tx_audio_var.set(tx_name)
        else:
            for name, idx in audio_devices.items():
                if 'TX:' in name or 'Output' in name:
                    tx_audio_var.set(name)
                    TX_AUDIO_INDEX = idx
                    break

        repeater_enabled_var.set(is_repeater_enabled)
        save_enabled_var.set(is_saving_enabled)
        roger_beep_enabled_var.set(is_roger_beep_enabled)
        if ROGER_BEEP_FILE and os.path.exists(ROGER_BEEP_FILE):
             roger_beep_file_var.set(os.path.basename(ROGER_BEEP_FILE))
        else:
             roger_beep_file_var.set("Keine Datei gewählt")
             ROGER_BEEP_FILE = ""

        gain_var.set(f"{tx_gain_factor:.2f}")

        log_message("INFO: Konfiguration geladen.")

    except FileNotFoundError:
        log_message("INFO: Keine Konfiguration, nutze Standardwerte.")
    except Exception as e:
        log_message(f"FEHLER Laden: {e}", is_error=True)

def apply_config(init=False):
    """Wendet Konfiguration an."""
    global serial_port, pa, stream, AUDIO_INDEX, TX_AUDIO_INDEX
    global is_repeater_enabled, is_saving_enabled, is_roger_beep_enabled

    try:
        is_repeater_enabled = repeater_enabled_var.get()
        is_saving_enabled = save_enabled_var.get()
        is_roger_beep_enabled = roger_beep_enabled_var.get()

        if not init:
            send_ci_v_command(PTT_OFF_CMD)

        new_port = port_var.get()
        new_baud = baud_var.get()

        port_changed = (serial_port and serial_port.is_open and
                        (serial_port.port != new_port or serial_port.baudrate != int(new_baud))) or init

        if port_changed:
            stop_squelch_monitoring()
            disconnect_serial()
            if not init:
                send_ci_v_command(PTT_OFF_CMD)
            connect_serial(new_port, new_baud)
            start_squelch_monitoring() # Startet jetzt auch das CI-V S-Meter Polling

        audio_devices, _, _ = list_audio_devices()

        selected_rx_name = rx_audio_var.get()
        rx_idx = audio_devices.get(selected_rx_name)

        if rx_idx is not None:
            if AUDIO_INDEX != rx_idx:
                AUDIO_INDEX = rx_idx
                log_message(f"INFO: RX-Index auf {AUDIO_INDEX} ('{selected_rx_name}') gesetzt.")
                if not init:
                    stop_audio_stream()
        else:
             log_message(f"FEHLER: RX-Gerät '{selected_rx_name}' nicht gefunden.", is_error=True)


        selected_tx_name = tx_audio_var.get()
        tx_idx = audio_devices.get(selected_tx_name)

        if tx_idx is not None:
            if TX_AUDIO_INDEX != tx_idx:
                TX_AUDIO_INDEX = tx_idx
                log_message(f"INFO: TX-Index auf {TX_AUDIO_INDEX} ('{selected_tx_name}') gesetzt.")
        else:
             log_message(f"FEHLER: TX-Gerät '{selected_tx_name}' nicht gefunden.", is_error=True)

        save_config()

        if AUDIO_INDEX is not None:
            if init or not stream or not stream.is_active():
                start_audio_stream()

    except Exception as e:
        status_var.set(f"Konfigurationsfehler: {e}")
        log_message(f"FEHLER apply_config: {e}", is_error=True)

# --- SERIAL ---

def connect_serial(port, baudrate):
    """Stellt serielle Verbindung her."""
    global serial_port
    disconnect_serial()
    try:
        serial_port = serial.Serial(port, int(baudrate), timeout=TIMEOUT)
        status_var.set(f"Verbunden: {port} @ {baudrate}")
        log_message(f"INFO: Serielle Verbindung OK.")

        # Timeout für Transceive-Befehle zurücksetzen
        serial_port.timeout = TIMEOUT 

        send_ci_v_command(SET_USB_MOD_LEVEL_100)
        log_message("INFO: USB MOD-Pegel über CI-V auf 100% (initial) gesetzt.")

    except Exception as e:
        status_var.set(f"Verbindungsfehler: {port}")
        log_message(f"FEHLER Verbindung: {e}", is_error=True)

def disconnect_serial():
    """Schließt serielle Verbindung."""
    global serial_port
    if serial_port and serial_port.is_open:
        serial_port.close()
        serial_port = None
        log_message("INFO: Serielle Verbindung getrennt.")

# --- RX SQUELCH / S-METER MONITORING ---

def squelch_monitoring_loop():
    """Überwacht Squelch-Status und S-Meter-Pegel (RX)."""
    global is_recording, audio_frames, is_transmitting, last_transmission_end
    global stop_squelch_thread, RX_METER_WIDTH, RX_METER_COLOR, RX_METER_LEVEL_LOCK

    log_message("INFO: Squelch/S-Meter-Monitoring (CI-V) gestartet.")

    last_squelch_state = False
    meter_width_max = 300

    while not stop_squelch_thread:
        try:
            current_time = time.time()

            if is_transmitting:
                time.sleep(0.1)
                continue

            if current_time - last_transmission_end < HANGTIME_AFTER_TX:
                time.sleep(0.1)
                continue

            # --------------------------------------------------------
            # LOGIK: S-METER PEGEB & SQUELCH STATUS VON CI-V LESEN
            # --------------------------------------------------------
            
            squelch_open = read_squelch_status()
            smeter_level = read_smeter_level() # Wert 0 bis 255
            
            # Skalierung des ICOM S-Meter Pegels auf die GUI Breite (0 bis 300)
            if smeter_level > 0:
                normalized_level = min(smeter_level, MAX_METER_VAL) / MAX_METER_VAL
                width = int(normalized_level * meter_width_max)
            else:
                width = 0

            # Farbe basierend auf dem Pegel (Orientierung an S-Werten: S5=50, S9=120)
            if smeter_level < 50: 
                color = 'green'
            elif smeter_level < 120: 
                color = 'yellow'
            else: 
                color = 'red'

            # Speichere Pegel-Informationen thread-sicher für den Polling-Loop
            with RX_METER_LEVEL_LOCK:
                RX_METER_WIDTH = width
                RX_METER_COLOR = color

            # GUI Update für Squelch
            if squelch_status_var:
                squelch_status_var.set("🔊" if squelch_open else "🔇")

            # --- Steuerung der Aufnahme ---
            if squelch_open and not last_squelch_state:
                if not is_recording:
                    log_message("-> Squelch OFFEN - Starte Aufnahme")
                    with audio_lock:
                        is_recording = True
                        audio_frames = []

            elif not squelch_open and last_squelch_state:
                if is_recording:
                    bytes_per_sample = pyaudio.get_sample_size(FORMAT)
                    total_bytes = sum(len(f) for f in audio_frames)
                    recording_duration = total_bytes / (RATE * CHANNELS * bytes_per_sample)

                    log_message(f"-> Squelch ZU - Aufnahme beendet ({recording_duration:.2f}s)")
                    is_recording = False

                    if recording_duration < 0.3:
                        log_message(f"-> Aufnahme zu kurz, verwerfe.")
                        with audio_lock:
                            audio_frames = []
                    else:
                        playback_thread = threading.Thread(target=playback_audio_frames)
                        playback_thread.start()

            last_squelch_state = squelch_open
            
            time.sleep(0.15) 

        except Exception as e:
            log_message(f"FEHLER Squelch/S-Meter Loop: {e}", is_error=True)
            time.sleep(0.5)

    log_message("INFO: Squelch/S-Meter-Monitoring beendet.")

def start_squelch_monitoring():
    """Startet Squelch-Monitoring Thread."""
    global squelch_thread, stop_squelch_thread

    stop_squelch_monitoring()

    stop_squelch_thread = False
    squelch_thread = threading.Thread(target=squelch_monitoring_loop, daemon=True)
    squelch_thread.start()

def stop_squelch_monitoring():
    """Stoppt Squelch-Monitoring Thread."""
    global squelch_thread, stop_squelch_thread

    if squelch_thread and squelch_thread.is_alive():
        stop_squelch_thread = True
        squelch_thread.join(timeout=2)


# --- NEU: TX ALC MONITORING ---

def alc_monitoring_loop():
    """Überwacht ALC-Pegel während der Übertragung (TX)."""
    global stop_alc_thread, TX_METER_WIDTH, TX_METER_COLOR, TX_METER_LEVEL_LOCK, max_alc_level, alc_monitoring_active

    log_message("INFO: ALC-Monitoring (CI-V) gestartet.")
    alc_monitoring_active = True
    max_alc_level = 0
    meter_width_max = 300

    while not stop_alc_thread:
        try:
            # Pegel abfragen
            alc_level = read_alc_level() # Wert 0 bis 255
            
            # Maximalen Wert speichern
            if alc_level > max_alc_level:
                max_alc_level = alc_level

            # Skalierung auf GUI Breite (0 bis 300)
            normalized_level = min(alc_level, MAX_METER_VAL) / MAX_METER_VAL
            width = int(normalized_level * meter_width_max)

            # Farbcodierung
            alc_percent = (alc_level / MAX_METER_VAL) * 100
            if alc_percent <= 50: # 0-50% (optimal)
                color = 'green'
            elif alc_percent <= 80: # 50-80% (grenzwertig)
                color = 'yellow'
            else: # 80-100% (Übersteuerung!)
                color = 'red'

            # Speichere Pegel-Informationen thread-sicher für den Polling-Loop
            with TX_METER_LEVEL_LOCK:
                TX_METER_WIDTH = width
                TX_METER_COLOR = color

            time.sleep(0.05) # Schnelleres Polling für Echtzeit-Meter

        except Exception as e:
            log_message(f"FEHLER ALC-Monitoring Loop: {e}", is_error=True)
            time.sleep(0.5)

    # Nach Beendigung den Meter-Status auf 0 setzen
    with TX_METER_LEVEL_LOCK:
        TX_METER_WIDTH = 0
        TX_METER_COLOR = 'gray'

    alc_monitoring_active = False
    log_message("INFO: ALC-Monitoring beendet.")


def start_alc_monitoring():
    """Startet ALC-Monitoring Thread."""
    global alc_thread, stop_alc_thread

    stop_alc_monitoring()

    stop_alc_thread = False
    alc_thread = threading.Thread(target=alc_monitoring_loop, daemon=True)
    alc_thread.start()

def stop_alc_monitoring():
    """Stoppt ALC-Monitoring Thread."""
    global alc_thread, stop_alc_thread

    if alc_thread and alc_thread.is_alive():
        stop_alc_thread = True
        alc_thread.join(timeout=1)

# --- AUDIO AUFNAHME / WIEDERGABE ---

def audio_callback(in_data, frame_count, time_info, status):
    """PyAudio Callback - nimmt nur noch kontinuierlich Audio für die Repeater-Funktion auf."""
    global audio_frames, is_recording
    
    if is_recording and (is_repeater_enabled or is_saving_enabled):
        with audio_lock:
            bytes_per_sample = pyaudio.get_sample_size(FORMAT)
            total_bytes = sum(len(f) for f in audio_frames) + len(in_data)
            current_duration = total_bytes / (RATE * CHANNELS * bytes_per_sample)

            if current_duration < MAX_REC_TIME_SEC:
                audio_frames.append(in_data)

    return (in_data, pyaudio.paContinue)

def save_frames_to_wav(frames, directory, filename):
    """Speichert Frames als WAV."""
    if not frames:
        return

    try:
        os.makedirs(directory, exist_ok=True)
        full_path = os.path.join(directory, filename)

        p = pyaudio.PyAudio()

        with wave.open(full_path, 'wb') as wf:
            wf.setnchannels(CHANNELS)
            wf.setsampwidth(p.get_sample_size(FORMAT))
            wf.setframerate(RATE)

            if isinstance(frames, list):
                wf.writeframes(b''.join(frames))
            elif isinstance(frames, bytes):
                 wf.writeframes(frames)
            else:
                 log_message("FEHLER: Ungültiger Frame-Typ zum Speichern.", is_error=True)
                 return

        log_message(f"AKTION: Gespeichert als: {filename}")
        p.terminate()

    except Exception as e:
        log_message(f"FEHLER Speichern WAV: {e}", is_error=True)


def load_and_play_beep(p_tx, tx_stream):
    """Lädt die Kennungs-WAV-Datei, konvertiert sie falls nötig und spielt sie ab."""
    global ROGER_BEEP_FILE, CHANNELS, RATE, FORMAT, CHUNK
    
    # Der ALC-Thread überwacht bereits im Hintergrund.

    if not ROGER_BEEP_FILE or not os.path.exists(ROGER_BEEP_FILE):
        log_message("WARNUNG: Kennungsdatei nicht konfiguriert oder nicht gefunden.")
        return False

    try:
        with wave.open(ROGER_BEEP_FILE, 'rb') as wf:
            file_channels = wf.getnchannels()
            file_rate = wf.getframerate()
            file_width = wf.getsampwidth()
            required_width = p_tx.get_sample_size(FORMAT)

            frames = wf.readframes(wf.getnframes())
            if not frames: return False

            if file_width == 2: dtype = np.int16
            elif file_width == 1: dtype = np.uint8
            else: return False

            original_samples = np.frombuffer(frames, dtype=dtype)
            
            # Bit-Tiefe Konvertierung
            if file_width != required_width:
                 if file_width == 1 and required_width == 2:
                    original_samples = ((original_samples.astype(np.float32) - 128.0) * 256.0).astype(np.int16)
                    dtype = np.int16

            try: samples_reshaped = original_samples.reshape(-1, file_channels)
            except ValueError: return False

            # Kanal-Konvertierung: Mono -> Stereo
            if file_channels == 1:
                stereo_samples = np.column_stack((samples_reshaped[:, 0], samples_reshaped[:, 0]))
            elif file_channels > 2:
                stereo_samples = samples_reshaped[:, :2]
            else:
                stereo_samples = samples_reshaped

            # Sample-Rate Konvertierung
            if file_rate != RATE:
                resampled_channels = []
                for channel in range(stereo_samples.shape[1]):
                    resampled_channel = signal.resample_poly(stereo_samples[:, channel].astype(np.float64), up=RATE, down=file_rate)
                    resampled_channels.append(resampled_channel)

                stacked_float = np.column_stack(resampled_channels)
                stereo_samples = np.clip(stacked_float, -32768, 32767).astype(np.int16)
            else:
                if stereo_samples.dtype != np.int16:
                    stereo_samples = stereo_samples.astype(np.int16)

            audio_data = stereo_samples.tobytes()

            # Abspielen
            total_bytes = len(audio_data)
            bytes_per_chunk = CHUNK * required_width * CHANNELS

            position = 0
            while position < total_bytes:
                if not tx_stream.is_active(): break

                chunk = audio_data[position:position + bytes_per_chunk]
                if chunk: tx_stream.write(chunk)
                position += bytes_per_chunk

            log_message("-> Kennung beendet.")
            return True

    except Exception as e:
        log_message(f"KRITISCHER FEHLER beim Abspielen der Kennung: {e}", is_error=True)
        return False


def playback_audio_frames():
    """Spielt aufgezeichnetes Audio und optional die Kennung ab."""
    global audio_frames, is_transmitting, last_transmission_end, SET_USB_MOD_LEVEL_100
    global is_repeater_enabled, is_saving_enabled, is_roger_beep_enabled, ROGER_BEEP_FILE, gain_var
    global max_alc_level

    if not audio_frames:
        return

    if not is_repeater_enabled and not is_saving_enabled:
        with audio_lock:
             audio_frames = []
        return

    audio_data = b"".join(audio_frames)

    with audio_lock:
        audio_frames = []

    duration_seconds = len(audio_data) / (RATE * CHANNELS * pyaudio.get_sample_size(FORMAT))

    # SPEICHERN
    if is_saving_enabled:
        now = datetime.now()
        timestamp_str = now.strftime("%Y%m%d_%H%M%S")
        filename = f"RX_{timestamp_str}.wav"
        save_frames_to_wav(audio_data, SAVE_DIR, filename)

    # REPEATER
    if is_repeater_enabled and TX_AUDIO_INDEX is not None:
        is_transmitting = True
        max_alc_level = 0 # Max-Pegel für diese Übertragung zurücksetzen

        send_ci_v_command(SET_USB_MOD_LEVEL_100)
        log_message("      INFO: USB MOD-Pegel über CI-V auf 100% gesetzt.")

        log_message(f"-> Starte Wiedergabe ({duration_seconds:.2f}s)")

        # PTT ON
        time.sleep(0.1)
        send_ci_v_command(PTT_ON_CMD)
        log_message("      PTT ON")

        start_alc_monitoring() # NEU: ALC-Überwachung starten

        tx_stream = None
        p_tx = None
        
        try:
            # --- ANWENDEN DES GAIN-FAKTORS VOR DER WIEDERGABE ---
            audio_array = np.frombuffer(audio_data, dtype=np.int16)

            GAIN_FACTOR = float(gain_var.get())
            if GAIN_FACTOR <= 0:
                GAIN_FACTOR = 1.0

            audio_array = (audio_array * GAIN_FACTOR).astype(np.float64)
            audio_array = np.clip(audio_array, -32768, 32767).astype(np.int16)

            audio_data = audio_array.tobytes()
            # ---------------------------------------------------

            p_tx = pyaudio.PyAudio()

            tx_stream = p_tx.open(
                format=FORMAT,
                channels=CHANNELS,
                rate=RATE,
                output=True,
                output_device_index=TX_AUDIO_INDEX,
                frames_per_buffer=CHUNK
            )

            # WIEDERGABE-LOOP (RX-Audio)
            bytes_per_sample = pyaudio.get_sample_size(FORMAT)
            bytes_per_chunk = CHUNK * CHANNELS * bytes_per_sample

            position = 0
            bytes_remaining = len(audio_data)
            while bytes_remaining > 0:
                chunk_size = min(bytes_per_chunk, bytes_remaining)
                chunk = audio_data[position:position + chunk_size]

                if chunk:
                    tx_stream.write(chunk)
                    position += chunk_size
                    bytes_remaining -= chunk_size
                else:
                    break

            log_message("INFO: RX-Wiedergabe beendet")

            # KENNUNG HINZUFÜGEN
            if is_roger_beep_enabled:
                load_and_play_beep(p_tx, tx_stream)

        except Exception as e:
            error_details = traceback.format_exc()
            log_message(f"KRITISCHER FEHLER Wiedergabe-Stream: {e}", is_error=True)
            log_message(f"STACKTRACE FÜR PYAUDIO FEHLER:\n{error_details}", is_error=True)

        finally:
            stop_alc_monitoring() # NEU: ALC-Überwachung beenden

            # --- NEU: ALC-DIAGNOSE NACH TX ---
            alc_percent = (max_alc_level / MAX_METER_VAL) * 100
            log_message(f"Max. ALC während TX: {max_alc_level}/{MAX_METER_VAL} ({alc_percent:.1f}%)")

            if max_alc_level == 0:
                log_message("WARNUNG: ALC-Pegel 0! KEIN SPRECHSIGNAL AM TRX ERKANNT.", is_error=True)
                log_message("Mögliche Ursachen: falsches TX-Audio-Gerät, zu niedriger Gain, USB-Treiber-Problem.", is_error=True)
            elif max_alc_level < 30:
                 log_message("HINWEIS: ALC sehr niedrig. TX Gain prüfen.", is_error=False)
            elif max_alc_level > 200:
                 log_message("WARNUNG: ALC sehr hoch! Gefahr der Übersteuerung. TX Gain reduzieren.", is_error=True)
            # ----------------------------------

            # PTT OFF
            time.sleep(0.3)
            send_ci_v_command(PTT_OFF_CMD)
            log_message("      PTT OFF")

            if tx_stream:
                tx_stream.stop_stream()
                tx_stream.close()
            if p_tx:
                p_tx.terminate()

            is_transmitting = False
            last_transmission_end = time.time()


def stop_audio_stream():
    """Stoppt und schließt den PyAudio Stream."""
    global stream, pa, is_recording
    is_recording = False
    if stream:
        try:
            if stream.is_active():
                stream.stop_stream()
            stream.close()
            log_message("INFO: RX-Audio-Stream gestoppt und geschlossen.")
        except Exception as e:
            log_message(f"WARNUNG beim Stoppen des Streams: {e}")
        finally:
            stream = None
    if pa:
        try:
            pa.terminate()
            log_message("INFO: PyAudio-Instanz beendet.")
        except Exception as e:
            log_message(f"WARNUNG beim Beenden von PyAudio: {e}")
        finally:
            pa = None


def start_audio_stream():
    """Startet den PyAudio Stream."""
    global pa, stream, AUDIO_INDEX, app

    stop_audio_stream()

    if AUDIO_INDEX is None:
        log_message("FEHLER: RX-Audio-Geräte-Index nicht gesetzt.", is_error=True)
        return

    try:
        pa = pyaudio.PyAudio()

        if AUDIO_INDEX >= pa.get_device_count():
            log_message(f"FEHLER: RX-Gerät Index {AUDIO_INDEX} ist ungültig.", is_error=True)
            pa.terminate()
            return

        stream = pa.open(
            format=FORMAT,
            channels=CHANNELS,
            rate=RATE,
            input=True,
            input_device_index=AUDIO_INDEX,
            frames_per_buffer=CHUNK,
            stream_callback=audio_callback
        )
        stream.start_stream()
        log_message(f"INFO: RX-Audio-Stream auf Index {AUDIO_INDEX} gestartet.")

        # Starte den Meter-Update-Loop (Polling)
        if app and app.winfo_exists():
             if not hasattr(app, '_meter_update_running'):
                 app._meter_update_running = True
                 app.after(50, update_gui_meter) 
             else:
                 pass

    except Exception as e:
        log_message(f"FEHLER Audio-Stream Start: {e}", is_error=True)
        log_message(f"STACKTRACE Audio Start:\n{traceback.format_exc()}", is_error=True)
        stop_audio_stream()


# --- GUI INITIALISIERUNG ---

def update_gui_meter():
    """Aktualisiert das RX S-Meter und das TX ALC-Meter im Haupt-Thread (Polling-Funktion)."""
    global rx_meter_canvas, tx_meter_canvas, app 
    global RX_METER_WIDTH, RX_METER_COLOR, RX_METER_LEVEL_LOCK
    global TX_METER_WIDTH, TX_METER_COLOR, TX_METER_LEVEL_LOCK

    # --- RX S-Meter Update ---
    if rx_meter_canvas and rx_meter_canvas.winfo_exists():
        try:
            with RX_METER_LEVEL_LOCK:
                rx_width = RX_METER_WIDTH
                rx_color = RX_METER_COLOR
            
            rx_meter_canvas.coords('rx_meter_rect', 0, 0, rx_width, 20)
            rx_meter_canvas.itemconfig('rx_meter_rect', fill=rx_color)
        except Exception:
            pass
            
    # --- NEU: TX ALC-Meter Update ---
    if tx_meter_canvas and tx_meter_canvas.winfo_exists():
        try:
            with TX_METER_LEVEL_LOCK:
                tx_width = TX_METER_WIDTH
                tx_color = TX_METER_COLOR
            
            tx_meter_canvas.coords('tx_meter_rect', 0, 0, tx_width, 20)
            tx_meter_canvas.itemconfig('tx_meter_rect', fill=tx_color)
            
            # Farb-Markierungen für ALC-Zonen hinzufügen (Rot-Bereich)
            meter_width_max = 300
            # 80% = 240
            tx_meter_canvas.create_line(meter_width_max * 0.8, 0, meter_width_max * 0.8, 20, fill="red", width=2, tags="alc_marker")
            # 50% = 150
            tx_meter_canvas.create_line(meter_width_max * 0.5, 0, meter_width_max * 0.5, 20, fill="yellow", width=2, tags="alc_marker")


        except Exception:
            pass


    # Rufe die Funktion in 50 Millisekunden erneut auf
    if app and app.winfo_exists():
        app.after(50, update_gui_meter)

def create_gui():
    """Erstellt die Tkinter-GUI."""
    global app, status_var, log_area, port_var, baud_var, tx_audio_var, rx_audio_var, \
           repeater_enabled_var, save_enabled_var, roger_beep_enabled_var, \
           roger_beep_file_var, squelch_status_var, rx_meter_canvas, tx_meter_canvas, gain_var

    app = Tk()
    app.title("Amateurfunk IC-7300 Repeater-Steuerung")

    # --- Variablen ---
    status_var = StringVar(value="Nicht verbunden")
    port_var = StringVar()
    baud_var = StringVar(value=str(BAUD_RATE))
    rx_audio_var = StringVar()
    tx_audio_var = StringVar()
    repeater_enabled_var = BooleanVar(value=False)
    save_enabled_var = BooleanVar(value=False)
    roger_beep_enabled_var = BooleanVar(value=False)
    roger_beep_file_var = StringVar(value="Keine Datei gewählt")
    squelch_status_var = StringVar(value="🔇")
    gain_var = StringVar(value="1.50")

    # --- Frames ---
    main_frame = Frame(app, padx=10, pady=10)
    main_frame.grid(row=0, column=0, sticky=N+S+W+E)
    app.grid_columnconfigure(0, weight=1)
    app.grid_rowconfigure(0, weight=1)

    # --- Sektion 1: Verbindung ---
    conn_frame = Frame(main_frame, padx=5, pady=5, borderwidth=2, relief="groove")
    conn_frame.grid(row=0, column=0, columnspan=2, sticky=W+E, pady=5)
    conn_frame.grid_columnconfigure(1, weight=1)

    Label(conn_frame, text="Status:", font=('Arial', 10, 'bold')).grid(row=0, column=0, sticky=W, padx=5, pady=2)
    Label(conn_frame, textvariable=status_var).grid(row=0, column=1, sticky=W, padx=5, pady=2)

    ports = list_serial_ports()
    port_var.set(ports[0] if ports else "COM1")
    Label(conn_frame, text="COM Port:").grid(row=1, column=0, sticky=W, padx=5, pady=2)
    OptionMenu(conn_frame, port_var, *(ports if ports else ["COM1"])).grid(row=1, column=1, sticky=W+E, padx=5, pady=2)

    Label(conn_frame, text="Baudrate:").grid(row=2, column=0, sticky=W, padx=5, pady=2)
    OptionMenu(conn_frame, baud_var, "9600", "19200", "38400", "57600", "115200").grid(row=2, column=1, sticky=W+E, padx=5, pady=2)

    Button(conn_frame, text="Verbinden/Übernehmen", command=lambda: apply_config()).grid(row=3, column=0, columnspan=2, pady=5, sticky=W+E)

    # --- Sektion 2: Audio/Pegel ---
    audio_frame = Frame(main_frame, padx=5, pady=5, borderwidth=2, relief="groove")
    audio_frame.grid(row=1, column=0, columnspan=2, sticky=W+E, pady=5)
    audio_frame.grid_columnconfigure(1, weight=1)

    audio_devices, _, _ = list_audio_devices()
    audio_names = sorted(audio_devices.keys())
    rx_devices = [name for name in audio_names if name.startswith('RX:')]
    tx_devices = [name for name in audio_names if name.startswith('TX:')]

    Label(audio_frame, text="RX Audio:").grid(row=0, column=0, sticky=W, padx=5, pady=2)
    OptionMenu(audio_frame, rx_audio_var, *(rx_devices if rx_devices else ["Kein RX-Gerät"])).grid(row=0, column=1, sticky=W+E, padx=5, pady=2)

    Label(audio_frame, text="TX Audio:").grid(row=1, column=0, sticky=W, padx=5, pady=2)
    OptionMenu(audio_frame, tx_audio_var, *(tx_devices if tx_devices else ["Kein TX-Gerät"])).grid(row=1, column=1, sticky=W+E, padx=5, pady=2)

    # Pegelanzeige RX (S-Meter)
    Label(audio_frame, text="S-Meter:").grid(row=2, column=0, sticky=W, padx=5, pady=2)
    rx_meter_canvas = Canvas(audio_frame, width=300, height=20, bg='white', borderwidth=1, relief="sunken")
    rx_meter_canvas.grid(row=2, column=1, sticky=W, padx=5, pady=2)
    rx_meter_canvas.create_rectangle(0, 0, 0, 20, fill='gray', tags='rx_meter_rect')

    # NEU: Pegelanzeige TX (ALC-Meter)
    Label(audio_frame, text="ALC-Meter:").grid(row=3, column=0, sticky=W, padx=5, pady=2)
    tx_meter_canvas = Canvas(audio_frame, width=300, height=20, bg='white', borderwidth=1, relief="sunken")
    tx_meter_canvas.grid(row=3, column=1, sticky=W, padx=5, pady=2)
    tx_meter_canvas.create_rectangle(0, 0, 0, 20, fill='gray', tags='tx_meter_rect')

    Label(audio_frame, text="TX Gain (x):").grid(row=4, column=0, sticky=W, padx=5, pady=2)
    Entry(audio_frame, textvariable=gain_var, width=10).grid(row=4, column=1, sticky=W, padx=5, pady=2)


    # --- Sektion 3: Steuerung ---
    ctrl_frame = Frame(main_frame, padx=5, pady=5, borderwidth=2, relief="groove")
    ctrl_frame.grid(row=2, column=0, columnspan=2, sticky=W+E, pady=5)
    ctrl_frame.grid_columnconfigure(0, weight=1)
    ctrl_frame.grid_columnconfigure(1, weight=1)

    Checkbutton(ctrl_frame, text="Repeater Aktiv", variable=repeater_enabled_var, command=save_config).grid(row=0, column=0, sticky=W, padx=5, pady=2)
    Checkbutton(ctrl_frame, text="Aufnahme Speichern", variable=save_enabled_var, command=save_config).grid(row=0, column=1, sticky=W, padx=5, pady=2)

    Checkbutton(ctrl_frame, text="Roger Beep/Kennung", variable=roger_beep_enabled_var, command=save_config).grid(row=1, column=0, sticky=W, padx=5, pady=2)
    Button(ctrl_frame, textvariable=roger_beep_file_var, command=select_roger_beep_file).grid(row=1, column=1, sticky=W+E, padx=5, pady=2)

    Label(ctrl_frame, text="Squelch:").grid(row=2, column=0, sticky=W, padx=5, pady=2)
    Label(ctrl_frame, textvariable=squelch_status_var, font=('Arial', 14)).grid(row=2, column=1, sticky=W, padx=5, pady=2)


    # --- Sektion 4: Log ---
    log_frame = Frame(main_frame, padx=5, pady=5, borderwidth=2, relief="groove")
    log_frame.grid(row=3, column=0, columnspan=2, sticky=W+E+N+S, pady=5)
    main_frame.grid_rowconfigure(3, weight=1)
    log_frame.grid_rowconfigure(0, weight=1)
    log_frame.grid_columnconfigure(0, weight=1)

    Label(log_frame, text="Log-Ausgabe:").grid(row=0, column=0, sticky=W)
    log_area = scrolledtext.ScrolledText(log_frame, wrap='word', height=15)
    log_area.grid(row=1, column=0, sticky=W+E+N+S)
    log_area.tag_config('red', foreground='red')
    log_area.tag_config('orange', foreground='orange') # DEBUG/WARNUNG

    # --- Initialisierung und Start ---
    load_config()
    apply_config(init=True) 

    def on_closing():
        stop_squelch_monitoring()
        stop_alc_monitoring()
        stop_audio_stream()
        disconnect_serial()
        log_message("INFO: Programm beendet.")
        app.destroy()

    app.protocol("WM_DELETE_WINDOW", on_closing)
    app.mainloop()

# --- HAUPT-PROGRAMM ---
if __name__ == "__main__":
    create_gui()