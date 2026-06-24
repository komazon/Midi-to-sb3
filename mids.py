import tkinter as tk
from tkinter import filedialog, messagebox, ttk, scrolledtext
import mido
import json
import zipfile
import os
import hashlib
from datetime import datetime
from pathlib import Path

BASE_DIR = Path(__file__).resolve().parent

# --- ログ関数 ---
def log_message(msg, log_widget=None, log_file="converter.log"):
    timestamp = datetime.now().strftime("%y/%m/%d %H:%M:%S")
    log_line = f"{timestamp} ({msg})"
    if log_widget:
        log_widget.insert(tk.END, log_line + "\n")
        log_widget.see(tk.END)
    try:
        with open(log_file, "a", encoding="utf-8") as f:
            f.write(log_line + "\n")
    except:
        pass

# --- マッピング ---
CHOIR_KEYWORDS = ["合唱", "コーラス", "クワイア", "choir", "chorus"]
CHOIR_SCRATCH_INSTRUMENT = 15
CUICA_SCRATCH_DRUM = 18

def is_choir_track(track_name):
    if not track_name:
        return False
    name_lower = track_name.lower()
    return any(kw.lower() in name_lower for kw in CHOIR_KEYWORDS)

def get_scratch_instrument(midi_program, genre="general", track_name=None):
    if is_choir_track(track_name):
        return CHOIR_SCRATCH_INSTRUMENT
    if 120 <= midi_program <= 127: return None
    if genre == "orchestra":
        if 24 <= midi_program <= 39: return 7
        if 80 <= midi_program <= 119: return 8
    elif genre == "rock":
        if 40 <= midi_program <= 54: return 3
        if 72 <= midi_program <= 79: return 5
        if 80 <= midi_program <= 119: return 20
    elif genre == "vocaloid":
        if 40 <= midi_program <= 54: return 21
        if 56 <= midi_program <= 79: return 20
    elif genre == "pop":
        if 40 <= midi_program <= 54: return 2
    if 0 <= midi_program <= 3: return 1
    if 4 <= midi_program <= 5: return 2
    if 6 <= midi_program <= 7: return 1
    if 8 <= midi_program <= 10: return 17
    if midi_program == 11: return 16
    if midi_program == 12: return 19
    if 13 <= midi_program <= 15: return 19
    if 16 <= midi_program <= 23: return 3
    if 24 <= midi_program <= 25: return 4
    if 26 <= midi_program <= 31: return 5
    if 32 <= midi_program <= 39: return 6
    if 40 <= midi_program <= 44: return 8
    if midi_program == 45: return 7
    if 46 <= midi_program <= 51: return 8
    if 52 <= midi_program <= 54: return 15
    if midi_program == 55: return 1
    if 56 <= midi_program <= 63: return 9
    if 64 <= midi_program <= 70: return 11
    if midi_program == 71: return 10
    if 72 <= midi_program <= 76: return 12
    if 77 <= midi_program <= 79: return 13
    if 80 <= midi_program <= 87: return 20
    if 88 <= midi_program <= 103: return 21
    if 104 <= midi_program <= 111: return 4
    if 112 <= midi_program <= 119: return 18
    return 1

def get_scratch_drum(midi_note):
    banned_notes = {39, 49, 51, 52, 53, 55, 57, 59, 73, 74, 78, 79}
    if midi_note in banned_notes:
        return None
    mapping = {
        35: 2, 36: 2, 38: 1, 40: 1, 37: 3, 42: 6, 44: 6, 46: 5, 54: 7, 75: 9,
        76: 10, 77: 10, 56: 11, 81: 12, 80: 12, 60: 13, 61: 13, 62: 14, 63: 14,
        64: 14, 69: 15,
    }
    result = mapping.get(midi_note, 1)
    if result == CUICA_SCRATCH_DRUM:
        return None
    return result

def get_genre_multiplier(program, genre):
    if genre == "orchestra":
        if 40 <= program <= 79: return 2.0
        if 24 <= program <= 39: return 0.5
    elif genre == "rock":
        if 24 <= program <= 39: return 2.0
        if 40 <= program <= 79: return 0.5
    elif genre == "vocaloid":
        if 80 <= program <= 103: return 2.5
        if 0 <= program <= 7: return 1.5
    elif genre == "pop":
        if 0 <= program <= 31: return 1.5
    return 1.0

# --- クラス定義 ---
class MidiNote:
    def __init__(self, pitch, start_tick, velocity):
        self.pitch = pitch
        self.start_tick = start_tick
        self.velocity = velocity
        self.end_tick = None

class ScratchProjectBuilder:
    STAGE_W = 480
    STAGE_H = 360
    FALL_LEAD_TIME = 2.0
    FALL_TOP_Y = 160
    KEYBOARD_TOP_Y = -100
    KEYBOARD_BOTTOM_Y = -180
    MIN_BAR_HEIGHT_PX = 6
    HEIGHT_ROUND_PX = 4

    def __init__(self, midi_path, main_track_idx, genre, enable_piano_roll=False, log_callback=None):
        self.midi_path = midi_path
        self.main_track_idx = int(main_track_idx)
        self.genre = genre
        self.enable_piano_roll = enable_piano_roll
        self.log_callback = log_callback
        self.midi = mido.MidiFile(midi_path)
        self.ticks_per_beat = self.midi.ticks_per_beat
        self.tempo = 120
        self.tempo_map = []

        # --- 外部画像読み込み（優先） ---
        self.background_image_path = str(BASE_DIR / "data" / "img" / "blackscreen.png")
        self.keyboard_image_path = str(BASE_DIR / "data" / "img" / "piano.png")
        self.use_external_images = False

        # 背景画像の読み込みを試行
        if os.path.exists(self.background_image_path):
            try:
                with open(self.background_image_path, "rb") as f:
                    self.svg_data = f.read()
                self.svg_md5 = hashlib.md5(self.svg_data).hexdigest()
                self.svg_filename = f"{self.svg_md5}.png"
                self._log(f"背景画像を読み込みました: {self.background_image_path}")
                self.use_external_images = True
            except Exception as e:
                self._log(f"背景画像読み込みエラー: {e}、SVGフォールバックを使用")
                self._generate_fallback_background()
        else:
            self._generate_fallback_background()

        # 鍵盤画像を事前に読み込んで保持（_prepare_piano_rollで使う）
        self.keyboard_image_data = None
        if os.path.exists(self.keyboard_image_path):
            try:
                with open(self.keyboard_image_path, "rb") as f:
                    self.keyboard_image_data = f.read()
                self._log(f"鍵盤画像を読み込みました: {self.keyboard_image_path}")
            except Exception as e:
                self._log(f"鍵盤画像読み込みエラー: {e}、自動生成にフォールバック")
                self.keyboard_image_data = None

        # ピアノロール用の状態
        self.pr_ready = False
        self.pr_pitch_min = None
        self.pr_pitch_max = None
        self.pr_key_width = None
        self.pr_height_buckets = {}
        self.pr_track_hues = {}
        self.pr_extra_assets = {}
        self.pr_keyboard_costume = None
        self._log("ScratchProjectBuilder初期化完了")

    def _generate_fallback_background(self):
        """フォールバック用グラデーション背景SVG"""
        self.svg_data = '''
<svg xmlns="http://www.w3.org/2000/svg" width="480" height="360" viewBox="-240 -180 480 360">
  <defs>
    <linearGradient id="bgGrad" x1="0%" y1="0%" x2="100%" y2="100%">
      <stop offset="0%" stop-color="#1a1a2e"/>
      <stop offset="100%" stop-color="#16213e"/>
    </linearGradient>
  </defs>
  <rect width="480" height="360" fill="url(#bgGrad)"/>
</svg>
'''.encode('utf-8')
        self.svg_md5 = hashlib.md5(self.svg_data).hexdigest()
        self.svg_filename = f"{self.svg_md5}.svg"

    def _log(self, msg):
        if self.log_callback:
            self.log_callback(msg)

    def calculate_track_volumes(self):
        self._log("トラック音量計算開始")
        track_scores = {}
        for track_idx, track in enumerate(self.midi.tracks):
            note_count = 0
            total_pitch = 0
            is_drum = False
            current_instrument = 0
            score_multiplier = 1.0
            for msg in track:
                if msg.type == 'program_change':
                    current_instrument = msg.program
                    score_multiplier = get_genre_multiplier(current_instrument, self.genre)
                if getattr(msg, 'channel', None) == 9:
                    is_drum = True
                if msg.type == 'note_on' and msg.velocity > 0:
                    if is_drum and get_scratch_drum(msg.note) is None: continue
                    if not is_drum and get_scratch_instrument(current_instrument, self.genre, track.name) is None: continue
                    note_count += 1
                    total_pitch += msg.note
            score = 0
            if not is_drum and note_count > 0:
                score = note_count * (total_pitch / note_count / 60.0) * score_multiplier
            track_scores[track_idx] = {'score': score, 'is_drum': is_drum}
        other_tracks = [t for t in track_scores if not track_scores[t]['is_drum'] and t != self.main_track_idx]
        other_tracks.sort(key=lambda t: track_scores[t]['score'], reverse=True)
        track_volumes = {}
        track_volumes[self.main_track_idx] = 100
        drum_vol = 80
        sub1_vol, sub2_vol, acc_vol = 80, 60, 40
        if self.genre in ["rock", "vocaloid"]:
            drum_vol = 90
            sub1_vol, sub2_vol, acc_vol = 85, 70, 50
        elif self.genre == "orchestra":
            drum_vol = 60
            sub1_vol, sub2_vol, acc_vol = 75, 55, 35
        for t in track_scores:
            if track_scores[t]['is_drum']:
                track_volumes[t] = drum_vol
        for i, t in enumerate(other_tracks):
            if i == 0: track_volumes[t] = sub1_vol
            elif i == 1: track_volumes[t] = sub2_vol
            else: track_volumes[t] = acc_vol
        self._log(f"音量計算完了: メイン {track_volumes.get(self.main_track_idx, 100)}, 他 {len(other_tracks)}トラック")
        return track_volumes

    def rank_voices(self, track_voices):
        self._log("ボイスランク付け開始")
        for tv in track_voices:
            notes = tv['notes']
            if not notes:
                tv['score'] = 0
                continue
            total_duration = sum(n.end_tick - n.start_tick for n in notes)
            pitches = [n.pitch for n in notes]
            pitch_range = max(pitches) - min(pitches)
            avg_vel = sum(n.velocity for n in notes) / len(notes)
            score = (len(notes) * 10) + (total_duration / 100) + (pitch_range * 5) + (avg_vel / 10)
            mult = get_genre_multiplier(tv['instrument'], self.genre)
            tv['score'] = score * mult

        track_voices.sort(key=lambda x: x['score'], reverse=True)
        for idx, tv in enumerate(track_voices):
            tv['rank'] = idx
            self._log(f"  ランク{idx}: Track{tv['track_idx']} Voice{tv['voice_idx']} (スコア={tv['score']:.1f})")
        self._log(f"ランク付け完了: {len(track_voices)}ボイス")

    def apply_strict_volume_control(self, track_voices, track_volumes):
        self._log("厳格音量調整開始")
        for tv in track_voices:
            if tv['is_main']:
                base_vol = 100
            else:
                base_vol = track_volumes.get(tv['track_idx'], 40)
            rank = tv.get('rank', 0)
            decay = max(0.4, 1.0 - rank * 0.05)
            strict_vol = base_vol * decay
            min_vol = 15 if tv['is_drum'] else 10
            strict_vol = max(min_vol, min(100, strict_vol))
            tv['volume'] = int(round(strict_vol))
            self._log(f"  Track{tv['track_idx']} Voice{tv['voice_idx']} (rank={rank}) → 音量{tv['volume']}")
        self._log(f"厳格音量調整完了: {len(track_voices)}ボイス")

    # ===== ピアノロール関連 =====
    def _tick_to_seconds(self, tick):
        seconds = 0.0
        prev_tick, prev_bpm = self.tempo_map[0]
        for next_tick, next_bpm in self.tempo_map[1:]:
            if tick <= next_tick:
                break
            seconds += (next_tick - prev_tick) * (60.0 / prev_bpm) / self.ticks_per_beat
            prev_tick, prev_bpm = next_tick, next_bpm
        seconds += max(0, tick - prev_tick) * (60.0 / prev_bpm) / self.ticks_per_beat
        return seconds

    def _pitch_to_x(self, pitch):
        """ピッチを鍵盤上のX座標に変換（鍵盤全体の中心が0になるようオフセット）"""
        key_index = pitch - self.pr_pitch_min
        total_width = (self.pr_pitch_max - self.pr_pitch_min + 1) * self.pr_key_width
        return -total_width / 2 + (key_index + 0.5) * self.pr_key_width

    def _duration_to_height_px(self, duration_seconds):
        fall_distance = self.FALL_TOP_Y - self.KEYBOARD_TOP_Y
        pixels_per_second = fall_distance / self.FALL_LEAD_TIME
        height = duration_seconds * pixels_per_second
        height = max(self.MIN_BAR_HEIGHT_PX, height)
        height = round(height / self.HEIGHT_ROUND_PX) * self.HEIGHT_ROUND_PX
        return int(height)

    def _build_keyboard_svg(self, pitch_min, pitch_max, key_width, height):
        """フォールバック用：簡易ピアノ鍵盤のSVGを生成"""
        width = self.STAGE_W
        half_w = width / 2
        half_h = height / 2
        total_keys = pitch_max - pitch_min + 1
        total_width = total_keys * key_width
        offset_x = -total_width / 2

        parts = [
            f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="{-half_w} {-half_h} {width} {height}" '
            f'width="{width}" height="{height}">',
            f'<rect x="{-half_w}" y="{-half_h}" width="{width}" height="{height}" fill="#1a1a1a"/>'
        ]
        for i, pitch in enumerate(range(pitch_min, pitch_max + 1)):
            x = offset_x + i * key_width
            is_black = (pitch % 12) in (1, 3, 6, 8, 10)
            fill = "#1a1a1a" if is_black else "#f5f5f5"
            black_h = height * 0.62
            y = -half_h if is_black else -half_h
            h = black_h if is_black else height
            parts.append(
                f'<rect x="{x:.2f}" y="{y:.2f}" width="{key_width:.2f}" height="{h:.2f}" '
                f'fill="{fill}" stroke="#555555" stroke-width="0.6"/>'
            )
        parts.append('</svg>')
        return "".join(parts).encode('utf-8')

    def _build_notebar_svg(self, width, height):
        half_w = width / 2
        half_h = height / 2
        inner_w = max(width - 1, 1)
        inner_h = max(height - 1, 1)
        svg = (
            f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="{-half_w} {-half_h} {width} {height}" '
            f'width="{width:.2f}" height="{height:.2f}">'
            f'<rect x="{-inner_w/2:.2f}" y="{-inner_h/2:.2f}" width="{inner_w:.2f}" height="{inner_h:.2f}" '
            f'rx="3" ry="3" fill="#ff5a5f" stroke="#7a1115" stroke-width="1.2"/>'
            f'</svg>'
        )
        return svg.encode('utf-8')

    def _prepare_piano_roll(self, track_voices):
        self._log("ピアノロール準備開始")
        pitches = []
        durations = []
        for tv in track_voices:
            if tv['is_drum']:
                continue
            for note in tv['notes']:
                pitches.append(note.pitch)
                onset = self._tick_to_seconds(note.start_tick)
                end = self._tick_to_seconds(note.end_tick)
                durations.append(max(0.0, end - onset))

        if not pitches:
            self._log("ピアノロール準備スキップ: 鍵盤に表示できる音程付きノートがありません")
            self.pr_ready = False
            return

        pitch_min = min(pitches) - 2
        pitch_max = max(pitches) + 2
        min_span = 24
        span = pitch_max - pitch_min + 1
        if span < min_span:
            pad = (min_span - span)
            pitch_min -= pad // 2
            pitch_max += pad - (pad // 2)
        pitch_min = max(0, pitch_min)
        pitch_max = min(127, pitch_max)

        self.pr_pitch_min = pitch_min
        self.pr_pitch_max = pitch_max
        num_keys = pitch_max - pitch_min + 1
        self.pr_key_width = self.STAGE_W / num_keys

        keyboard_height = self.KEYBOARD_TOP_Y - self.KEYBOARD_BOTTOM_Y
        bar_width = max(self.pr_key_width - 2, 2)
        unique_heights = sorted({self._duration_to_height_px(d) for d in durations})
        self.pr_height_buckets = {}
        for h in unique_heights:
            svg_bytes = self._build_notebar_svg(bar_width, h)
            md5 = hashlib.md5(svg_bytes).hexdigest()
            filename = f"{md5}.svg"
            costume_name = f"note_{h}"
            self.pr_extra_assets[filename] = svg_bytes
            self.pr_height_buckets[h] = {
                "name": costume_name,
                "assetId": md5,
                "md5ext": filename,
                "dataFormat": "svg"
            }

        # --- 鍵盤コスチューム（外部画像優先） ---
        if self.keyboard_image_data is not None:
            kb_md5 = hashlib.md5(self.keyboard_image_data).hexdigest()
            kb_filename = f"{kb_md5}.png"
            self.pr_extra_assets[kb_filename] = self.keyboard_image_data
            self.pr_keyboard_costume = {
                "name": "keyboard",
                "assetId": kb_md5,
                "md5ext": kb_filename,
                "dataFormat": "png"
            }
            self._log("鍵盤コスチュームに外部画像を使用")
        else:
            # フォールバック：SVGで鍵盤を生成
            keyboard_svg = self._build_keyboard_svg(pitch_min, pitch_max, self.pr_key_width, keyboard_height)
            kb_md5 = hashlib.md5(keyboard_svg).hexdigest()
            kb_filename = f"{kb_md5}.svg"
            self.pr_extra_assets[kb_filename] = keyboard_svg
            self.pr_keyboard_costume = {
                "name": "keyboard",
                "assetId": kb_md5,
                "md5ext": kb_filename,
                "dataFormat": "svg"
            }
            self._log("鍵盤コスチュームにSVGフォールバックを使用")

        track_idxs = sorted({tv['track_idx'] for tv in track_voices if not tv['is_drum']})
        n = max(len(track_idxs), 1)
        self.pr_track_hues = {t: round(i * 200 / n) % 200 for i, t in enumerate(track_idxs)}

        self.pr_ready = True
        self._log(f"ピアノロール準備完了: 鍵盤範囲={pitch_min}-{pitch_max}, バー種類={len(unique_heights)}")

    def parse_midi(self):
        self._log("MIDI解析開始")
        tempo_events = []
        for track in self.midi.tracks:
            abs_tick = 0
            for msg in track:
                abs_tick += msg.time
                if msg.type == 'set_tempo':
                    bpm = mido.tempo2bpm(msg.tempo)
                    tempo_events.append((abs_tick, bpm))
        tempo_events.sort(key=lambda x: x[0])
        unique = []
        last_tick = -1
        for tick, bpm in tempo_events:
            if tick != last_tick:
                unique.append((tick, bpm))
                last_tick = tick
        initial_bpm = 120
        for track in self.midi.tracks:
            for msg in track:
                if msg.type == 'set_tempo':
                    initial_bpm = round(mido.tempo2bpm(msg.tempo))
                    break
            else:
                continue
            break
        if not unique or unique[0][0] != 0:
            unique.insert(0, (0, initial_bpm))
        self.tempo_map = unique
        self.tempo = initial_bpm
        self._log(f"テンポマップ作成: {len(self.tempo_map)}イベント, 初期BPM={initial_bpm}")

        track_volumes = self.calculate_track_volumes()
        track_voices = []
        for track_idx, track in enumerate(self.midi.tracks):
            abs_tick = 0
            active_notes = {}
            completed_notes = []
            current_instrument = 0
            is_drum = False
            for msg in track:
                abs_tick += msg.time
                if msg.type == 'program_change':
                    current_instrument = msg.program
                if getattr(msg, 'channel', None) == 9:
                    is_drum = True
                if msg.type == 'note_on' and msg.velocity > 0:
                    if is_drum and get_scratch_drum(msg.note) is None: continue
                    if not is_drum and get_scratch_instrument(current_instrument, self.genre, track.name) is None: continue
                    active_notes[msg.note] = MidiNote(msg.note, abs_tick, msg.velocity)
                elif msg.type == 'note_off' or (msg.type == 'note_on' and msg.velocity == 0):
                    if msg.note in active_notes:
                        note = active_notes.pop(msg.note)
                        note.end_tick = abs_tick
                        completed_notes.append(note)
            if not completed_notes:
                continue
            completed_notes.sort(key=lambda n: n.start_tick)
            voices = []
            for note in completed_notes:
                placed = False
                for voice in voices:
                    if voice[-1].end_tick <= note.start_tick:
                        voice.append(note)
                        placed = True
                        break
                if not placed:
                    voices.append([note])
            for voice_idx, voice in enumerate(voices):
                is_main = (track_idx == self.main_track_idx)
                track_voices.append({
                    'track_idx': track_idx,
                    'voice_idx': voice_idx + 1,
                    'notes': voice,
                    'instrument': current_instrument,
                    'track_name': track.name,
                    'is_drum': is_drum,
                    'is_main': is_main,
                    'volume': track_volumes.get(track_idx, 40)
                })

        self.rank_voices(track_voices)
        self.apply_strict_volume_control(track_voices, track_volumes)
        self._log(f"MIDI解析完了: {len(track_voices)}ボイス抽出")
        return track_voices

    def generate_project_json(self, track_voices):
        self._log("プロジェクトJSON生成開始")
        targets = []

        # ステージ（背景）
        # 外部画像が読み込まれていれば dataFormat は png、そうでなければ svg
        bg_format = "png" if self.use_external_images else "svg"
        stage = {
            "isStage": True,
            "name": "Stage",
            "variables": {},
            "lists": {},
            "broadcasts": {},
            "blocks": {},
            "comments": {},
            "currentCostume": 0,
            "costumes": [{"assetId": self.svg_md5, "name": "backdrop1", "md5ext": self.svg_filename, "dataFormat": bg_format}],
            "sounds": [],
            "volume": 100,
            "layerOrder": 0,
            "tempo": self.tempo
        }
        targets.append(stage)

        # ピアノロール用鍵盤スプライト
        if self.enable_piano_roll:
            self._prepare_piano_roll(track_voices)
            if self.pr_ready:
                kb_blocks = {}
                # 1. 旗が押されたとき（次のブロックのIDを "b_keyboard_2" に指定）
                kb_blocks["b_keyboard_1"] = {
                    "opcode": "event_whenflagclicked",
                    "next": "b_keyboard_2",
                    "parent": None,
                    "inputs": {},
                    "fields": {},
                    "shadow": False,
                    "topLevel": True
                }
                # 2. 最前面へ移動する（looks_gotofrontback）を追加！
                kb_blocks["b_keyboard_2"] = {
                    "opcode": "looks_gotofrontback",
                    "next": None,
                    "parent": "b_keyboard_1",
                    "inputs": {},
                    "fields": {
                        "FRONT_BACK": ["front",None]
                    },
                    "shadow": False,
                    "topLevel": False
                }
                keyboard_sprite = {
                    
                    
                    "isStage": False,
                    "name": "鍵盤",
                    "variables": {},
                    "lists": {},
                    "broadcasts": {},
                    "blocks": kb_blocks,
                    "comments": {},
                    "currentCostume": 0,
                    "costumes": [self.pr_keyboard_costume],
                    "sounds": [],
                    "volume": 100,
                    "layerOrder": 1,
                    "visible": True,
                    "x": 0,
                    "y": (self.KEYBOARD_TOP_Y + self.KEYBOARD_BOTTOM_Y) / 2,
                    "size": 100,
                    "direction": 90,
                    "rotationStyle": "all around"
                }
                targets.append(keyboard_sprite)
            else:
                self._log("ピアノロール用の鍵盤スプライト追加をスキップしました")
        layer_base = 2 if (self.enable_piano_roll and self.pr_ready) else 1

        # 各演奏スプライト
        for idx, tv in enumerate(track_voices):
            sprite_name = f"R{tv['rank']}_T{tv['track_idx']}_V{tv['voice_idx']}_Vol{tv['volume']}"
            blocks = {}
            volume = tv['volume']

            def add_block(b_id, opcode, next_id, parent_id, inputs=None, fields=None, top=False, shadow=False):
                blocks[b_id] = {
                    "opcode": opcode,
                    "next": next_id,
                    "parent": parent_id,
                    "inputs": inputs or {},
                    "fields": fields or {},
                    "shadow": shadow,
                    "topLevel": top
                }

            b_counter = 0
            def get_id():
                nonlocal b_counter
                b_counter += 1
                return f"b_{sprite_name}_{b_counter}"

            prev_id = get_id()
            add_block(prev_id, "event_whenflagclicked", None, None, top=True)

            curr_id = get_id()
            blocks[prev_id]["next"] = curr_id
            add_block(curr_id, "sound_setvolumeto", None, prev_id, {"VOLUME": [1, [4, str(volume)]]})
            prev_id = curr_id

            curr_id = get_id()
            blocks[prev_id]["next"] = curr_id
            add_block(curr_id, "music_setTempo", None, prev_id, {"TEMPO": [1, [4, str(self.tempo_map[0][1])]]})
            prev_id = curr_id

            if not tv['is_drum']:
                curr_id = get_id()
                blocks[prev_id]["next"] = curr_id
                inst_scratch = get_scratch_instrument(tv['instrument'], self.genre, tv.get('track_name'))
                add_block(curr_id, "music_setInstrument", None, prev_id, {"INSTRUMENT": [1, [4, str(inst_scratch)]]})
                prev_id = curr_id

            current_tick = 0
            tempo_idx = 0
            for note in tv['notes']:
                while tempo_idx + 1 < len(self.tempo_map) and self.tempo_map[tempo_idx+1][0] <= note.start_tick:
                    next_tick, next_bpm = self.tempo_map[tempo_idx+1]
                    wait_ticks = next_tick - current_tick
                    if wait_ticks > 0.01:
                        wait_beats = wait_ticks / self.ticks_per_beat
                        curr_id = get_id()
                        blocks[prev_id]["next"] = curr_id
                        add_block(curr_id, "music_restForBeats", None, prev_id, {"BEATS": [1, [4, str(wait_beats)]]})
                        prev_id = curr_id
                        current_tick = next_tick
                    curr_id = get_id()
                    blocks[prev_id]["next"] = curr_id
                    add_block(curr_id, "music_setTempo", None, prev_id, {"TEMPO": [1, [4, str(next_bpm)]]})
                    prev_id = curr_id
                    tempo_idx += 1

                wait_ticks = note.start_tick - current_tick
                if wait_ticks > 0.01:
                    wait_beats = wait_ticks / self.ticks_per_beat
                    curr_id = get_id()
                    blocks[prev_id]["next"] = curr_id
                    add_block(curr_id, "music_restForBeats", None, prev_id, {"BEATS": [1, [4, str(wait_beats)]]})
                    prev_id = curr_id
                    current_tick = note.start_tick

                dur_ticks = note.end_tick - note.start_tick
                dur_beats = dur_ticks / self.ticks_per_beat
                curr_id = get_id()
                blocks[prev_id]["next"] = curr_id
                if tv['is_drum']:
                    drum_val = get_scratch_drum(note.pitch)
                    add_block(curr_id, "music_playDrumForBeats", None, prev_id, {
                        "DRUM": [1, [4, str(drum_val)]],
                        "BEATS": [1, [4, str(dur_beats)]]
                    })
                else:
                    add_block(curr_id, "music_playNoteForBeats", None, prev_id, {
                        "NOTE": [1, [4, str(note.pitch)]],
                        "BEATS": [1, [4, str(dur_beats)]]
                    })
                prev_id = curr_id
                current_tick = note.end_tick

            # ピアノロールアニメーション（ドラム以外）
            piano_roll_costumes = []
            sprite_visible = True
            if self.enable_piano_roll and self.pr_ready and not tv['is_drum'] and tv['notes']:
                sprite_visible = False

                vis_id = get_id()
                add_block(vis_id, "event_whenflagclicked", None, None, top=True)
                vis_prev = vis_id

                hide_id = get_id()
                blocks[vis_prev]["next"] = hide_id
                add_block(hide_id, "looks_hide", None, vis_prev)
                vis_prev = hide_id

                hue = self.pr_track_hues.get(tv['track_idx'], 0)
                eff_id = get_id()
                blocks[vis_prev]["next"] = eff_id
                add_block(eff_id, "looks_seteffectto", None, vis_prev,
                           inputs={"VALUE": [1, [4, str(hue)]]},
                           fields={"EFFECT": ["COLOR", None]})
                vis_prev = eff_id

                last_spawn_time = 0.0
                used_costume_names = set()
                for note in tv['notes']:
                    onset = self._tick_to_seconds(note.start_tick)
                    end = self._tick_to_seconds(note.end_tick)
                    duration = max(0.0, end - onset)
                    spawn_time = max(0.0, onset - self.FALL_LEAD_TIME)
                    delta = spawn_time - last_spawn_time

                    if delta > 0.01:
                        wait_id = get_id()
                        blocks[vis_prev]["next"] = wait_id
                        add_block(wait_id, "control_wait", None, vis_prev,
                                   inputs={"DURATION": [1, [4, str(round(delta, 3))]]})
                        vis_prev = wait_id
                        last_spawn_time = spawn_time

                    x_pos = self._pitch_to_x(note.pitch)
                    height_px = self._duration_to_height_px(duration)
                    costume_info = self.pr_height_buckets[height_px]
                    costume_name = costume_info["name"]
                    used_costume_names.add(costume_name)

                    goto_id = get_id()
                    blocks[vis_prev]["next"] = goto_id
                    add_block(goto_id, "motion_gotoxy", None, vis_prev, inputs={
                        "X": [1, [4, str(round(x_pos, 1))]],
                        "Y": [1, [4, str(self.FALL_TOP_Y)]]
                    })
                    vis_prev = goto_id

                    switch_id = get_id()
                    costume_shadow_id = get_id()
                    blocks[vis_prev]["next"] = switch_id
                    add_block(switch_id, "looks_switchcostumeto", None, vis_prev,
                               inputs={"COSTUME": [1, costume_shadow_id]})
                    add_block(costume_shadow_id, "looks_costume", None, switch_id,
                               fields={"COSTUME": [costume_name, None]}, shadow=True)
                    vis_prev = switch_id

                    clone_id = get_id()
                    clone_shadow_id = get_id()
                    blocks[vis_prev]["next"] = clone_id
                    add_block(clone_id, "control_create_clone_of", None, vis_prev,
                               inputs={"CLONE_OPTION": [1, clone_shadow_id]})
                    add_block(clone_shadow_id, "control_create_clone_of_menu", None, clone_id,
                               fields={"CLONE_OPTION": ["_myself_", None]}, shadow=True)
                    vis_prev = clone_id

                clone_hat_id = get_id()
                add_block(clone_hat_id, "control_start_as_clone", None, None, top=True)

                show_id = get_id()
                blocks[clone_hat_id]["next"] = show_id
                add_block(show_id, "looks_show", None, clone_hat_id)

                glide_id = get_id()
                xpos_id = get_id()
                blocks[show_id]["next"] = glide_id
                add_block(glide_id, "motion_glidesecstoxy", None, show_id, inputs={
                    "SECS": [1, [4, str(self.FALL_LEAD_TIME)]],
                    "X": [3, xpos_id, [4, "0"]],
                    "Y": [1, [4, str(self.KEYBOARD_TOP_Y)]]
                })
                add_block(xpos_id, "motion_xposition", None, glide_id)

                delete_id = get_id()
                blocks[glide_id]["next"] = delete_id
                add_block(delete_id, "control_delete_this_clone", None, glide_id)

                for h, info in self.pr_height_buckets.items():
                    if info["name"] in used_costume_names:
                        piano_roll_costumes.append({
                            "assetId": info["assetId"],
                            "name": info["name"],
                            "md5ext": info["md5ext"],
                            "dataFormat": info["dataFormat"]
                        })

            sprite = {
                "isStage": False,
                "name": sprite_name,
                "variables": {},
                "lists": {},
                "broadcasts": {},
                "blocks": blocks,
                "comments": {},
                "currentCostume": 0,
                "costumes": [{"assetId": self.svg_md5, "name": "costume1", "md5ext": self.svg_filename, "dataFormat": "svg"}] + piano_roll_costumes,
                "sounds": [],
                "volume": 100,
                "layerOrder": idx + layer_base,
                "visible": sprite_visible,
                "x": 0,
                "y": 0,
                "size": 100,
                "direction": 90
            }
            targets.append(sprite)

        self._log(f"JSON生成完了: {len(targets)}ターゲット")
        return {
            "targets": targets,
            "monitors": [],
            "extensions": ["music"],
            "meta": {"semver": "3.0.0", "vm": "0.2.0", "agent": "Python Midi2Sb3"}
        }

    def build_sb3(self):
        self._log("sb3ビルド開始")
        track_voices = self.parse_midi()
        project_json = self.generate_project_json(track_voices)
        output_path = f"{os.path.splitext(self.midi_path)[0]}_{self.genre}.sb3"
        with zipfile.ZipFile(output_path, 'w', zipfile.ZIP_DEFLATED) as sb3:
            sb3.writestr('project.json', json.dumps(project_json))
            sb3.writestr(self.svg_filename, self.svg_data)
            for filename, data in self.pr_extra_assets.items():
                sb3.writestr(filename, data)
        self._log(f"sb3出力完了: {output_path}")
        return output_path

# --- GUI ---
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("MIDI to Scratch 3.0 Converter")
        self.geometry("520x580")
        self.midi_path = None
        self.track_names = []

        frm_top = tk.Frame(self)
        frm_top.pack(pady=5, fill=tk.X)

        tk.Label(frm_top, text="Midiファイルを選択してScratch作品を生成します", pady=5).pack()

        self.btn_select = tk.Button(frm_top, text="Midiファイルを選択", command=self.select_file)
        self.btn_select.pack(pady=2)

        self.lbl_file = tk.Label(frm_top, text="未選択", fg="gray")
        self.lbl_file.pack()

        tk.Label(frm_top, text="出力ジャンル設定:").pack(pady=(10,0))
        self.genre_var = tk.StringVar(value="general")
        frame_genres = tk.Frame(frm_top)
        frame_genres.pack()
        genres = [("汎用", "general"), ("オーケストラ", "orchestra"), ("ロック", "rock"), ("POP", "pop"), ("ボカロ", "vocaloid")]
        for text, val in genres:
            tk.Radiobutton(frame_genres, text=text, variable=self.genre_var, value=val).pack(side=tk.LEFT, padx=5)

        tk.Label(frm_top, text="主旋律トラック (自動ランク付け・音量調整):").pack(pady=(10,0))
        self.combo_main = ttk.Combobox(frm_top, state="readonly", width=50)
        self.combo_main.pack(pady=2)

        self.piano_roll_var = tk.BooleanVar(value=False)
        self.chk_piano_roll = tk.Checkbutton(
            frm_top,
            text="ピアノロール風アニメーションを追加（上から鍵盤にノートが降ってくる）",
            variable=self.piano_roll_var
        )
        self.chk_piano_roll.pack(pady=(8, 0))

        self.btn_convert = tk.Button(frm_top, text="sb3ファイルを作成", command=self.convert, state=tk.DISABLED,
                                     bg="#4CAF50", fg="white", font=("", 12, "bold"))
        self.btn_convert.pack(pady=10)

        tk.Label(self, text="--- 操作ログ ---", font=("", 10, "bold")).pack(pady=(5,0))
        self.log_text = scrolledtext.ScrolledText(self, height=14, state='normal', font=("Courier", 9))
        self.log_text.pack(padx=5, pady=5, fill=tk.BOTH, expand=True)
        self.log_message("アプリケーション起動")

    def log_message(self, msg):
        timestamp = datetime.now().strftime("%y/%m/%d %H:%M:%S")
        log_line = f"{timestamp} ({msg})"
        self.log_text.insert(tk.END, log_line + "\n")
        self.log_text.see(tk.END)
        try:
            with open("converter.log", "a", encoding="utf-8") as f:
                f.write(log_line + "\n")
        except:
            pass

    def select_file(self):
        filepath = filedialog.askopenfilename(filetypes=[("MIDI files", "*.mid *.midi")])
        if filepath:
            self.midi_path = filepath
            self.lbl_file.config(text=os.path.basename(filepath), fg="black")
            self.log_message(f"ファイル選択: {os.path.basename(filepath)}")
            self.load_tracks()
            self.btn_convert.config(state=tk.NORMAL)

    def load_tracks(self):
        self.log_message("トラック解析開始")
        try:
            midi = mido.MidiFile(self.midi_path)
            self.track_names = []
            best_track_idx = 0
            best_score = -1
            for i, track in enumerate(midi.tracks):
                name = track.name if track.name else f"Track {i}"
                self.track_names.append(f"{i}: {name}")
                note_count = 0
                total_pitch = 0
                is_drum = False
                current_instrument = 0
                for msg in track:
                    if msg.type == 'program_change':
                        current_instrument = msg.program
                    if getattr(msg, 'channel', None) == 9:
                        is_drum = True
                    if msg.type == 'note_on' and msg.velocity > 0:
                        if is_drum and get_scratch_drum(msg.note) is None: continue
                        if not is_drum and get_scratch_instrument(current_instrument, track_name=name) is None: continue
                        note_count += 1
                        total_pitch += msg.note
                if not is_drum and note_count > 0:
                    avg_pitch = total_pitch / note_count
                    score = note_count * (avg_pitch / 60.0)
                    if score > best_score:
                        best_score = score
                        best_track_idx = i
            self.combo_main['values'] = self.track_names
            if self.track_names:
                self.combo_main.current(best_track_idx)
                self.log_message(f"トラック解析完了: {len(self.track_names)}トラック, メイン候補=Track{best_track_idx}")
        except Exception as e:
            self.log_message(f"トラック解析エラー: {str(e)}")
            messagebox.showerror("エラー", f"Midiの読み込みに失敗しました:\n{e}")

    def convert(self):
        if not self.midi_path:
            return
        selected_idx = 0
        if self.combo_main.get():
            selected_idx = int(self.combo_main.get().split(":")[0])
        self.log_message(f"変換開始: メイントラック={selected_idx}, ジャンル={self.genre_var.get()}, ピアノロール={self.piano_roll_var.get()}")
        try:
            builder = ScratchProjectBuilder(
                self.midi_path, selected_idx, self.genre_var.get(),
                enable_piano_roll=self.piano_roll_var.get(),
                log_callback=self.log_message
            )
            out_file = builder.build_sb3()
            self.log_message(f"変換完了: {os.path.basename(out_file)}")
            messagebox.showinfo("完了", f"Scratch作品を作成しました！\n{out_file}")
        except Exception as e:
            self.log_message(f"変換エラー: {str(e)}")
            messagebox.showerror("エラー", f"変換中にエラーが発生しました:\n{e}")

if __name__ == "__main__":
    app = App()
    app.mainloop()