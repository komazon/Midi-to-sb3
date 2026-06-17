import tkinter as tk
from tkinter import filedialog, messagebox, ttk, scrolledtext
import mido
import json
import zipfile
import os
import hashlib
from datetime import datetime

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
def get_scratch_instrument(midi_program, genre="general"):
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
    return mapping.get(midi_note, 1)

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
    def __init__(self, midi_path, main_track_idx, genre, log_callback=None):
        self.midi_path = midi_path
        self.main_track_idx = int(main_track_idx)
        self.genre = genre
        self.log_callback = log_callback
        self.midi = mido.MidiFile(midi_path)
        self.ticks_per_beat = self.midi.ticks_per_beat
        self.tempo = 120
        self.tempo_map = []
        self.max_concurrent_notes = 6
        self.svg_data = '<svg version="1.1" width="2" height="2" viewBox="-1 -1 2 2" xmlns="http://www.w3.org/2000/svg"></svg>'.encode('utf-8')
        self.svg_md5 = hashlib.md5(self.svg_data).hexdigest()
        self.svg_filename = f"{self.svg_md5}.svg"
        self._log("ScratchProjectBuilder初期化完了")

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
                    if not is_drum and get_scratch_instrument(current_instrument, self.genre) is None: continue
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

    def limit_concurrent_notes(self, track_voices):
        self._log(f"同時発音制限開始 (上限={self.max_concurrent_notes})")
        all_notes = []
        for vi, tv in enumerate(track_voices):
            rank = tv['rank']
            for ni, note in enumerate(tv['notes']):
                all_notes.append((note.start_tick, note.end_tick, vi, ni, rank))
        all_notes.sort(key=lambda x: x[0])

        active = []
        to_remove = set()
        protected_ranks = {0, 1, 2}

        for start, end, vi, ni, rank in all_notes:
            active = [a for a in active if a[0] > start]

            if len(active) >= self.max_concurrent_notes:
                if rank in protected_ranks:
                    unprotected = [a for a in active if a[3] not in protected_ranks]
                    if unprotected:
                        to_remove_unprotected = max(unprotected, key=lambda x: x[3])
                        active.remove(to_remove_unprotected)
                        to_remove.add((to_remove_unprotected[1], to_remove_unprotected[2]))
                        active.append((end, vi, ni, rank))
                    else:
                        self._log(f"  保護ノート強制追加: ボイス{vi}, ノート{ni} (同時発音 {len(active)+1})")
                        active.append((end, vi, ni, rank))
                else:
                    unprotected = [a for a in active if a[3] not in protected_ranks]
                    if unprotected:
                        to_remove_unprotected = max(unprotected, key=lambda x: x[3])
                        active.remove(to_remove_unprotected)
                        to_remove.add((to_remove_unprotected[1], to_remove_unprotected[2]))
                        active.append((end, vi, ni, rank))
                    else:
                        to_remove.add((vi, ni))
                        self._log(f"  非保護ノート削除: ボイス{vi}, ノート{ni} (保護ノートが優先)")
            else:
                active.append((end, vi, ni, rank))

        for vi, tv in enumerate(track_voices):
            new_notes = []
            for ni, note in enumerate(tv['notes']):
                if (vi, ni) not in to_remove:
                    new_notes.append(note)
            tv['notes'] = new_notes
        track_voices[:] = [tv for tv in track_voices if tv['notes']]
        self._log(f"同時発音制限完了: {len(to_remove)}ノート削除, 残りボイス数={len(track_voices)}")

    def parse_midi(self):
        self._log("MIDI解析開始")
        # テンポマップ
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
                    if not is_drum and get_scratch_instrument(current_instrument, self.genre) is None: continue
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
                    'is_drum': is_drum,
                    'is_main': is_main,
                    'volume': track_volumes.get(track_idx, 40)
                })

        self.rank_voices(track_voices)
        self.limit_concurrent_notes(track_voices)
        self._log(f"MIDI解析完了: {len(track_voices)}ボイス抽出")
        return track_voices

    def generate_project_json(self, track_voices):
        self._log("プロジェクトJSON生成開始")
        targets = []

        # ===== ステージ（何もしない） =====
        stage = {
            "isStage": True,
            "name": "Stage",
            "variables": {},
            "lists": {},
            "broadcasts": {},
            "blocks": {},
            "comments": {},
            "currentCostume": 0,
            "costumes": [{"assetId": self.svg_md5, "name": "backdrop1", "md5ext": self.svg_filename, "dataFormat": "svg"}],
            "sounds": [],
            "volume": 100,
            "layerOrder": 0,
            "tempo": self.tempo
        }
        targets.append(stage)

        # ===== 各スプライト（演奏者） =====
        for idx, tv in enumerate(track_voices):
            sprite_name = f"R{tv['rank']}_T{tv['track_idx']}_V{tv['voice_idx']}_Vol{tv['volume']}"
            blocks = {}
            volume = tv['volume']

            def add_block(b_id, opcode, next_id, parent_id, inputs=None, fields=None, top=False):
                blocks[b_id] = {
                    "opcode": opcode,
                    "next": next_id,
                    "parent": parent_id,
                    "inputs": inputs or {},
                    "fields": fields or {},
                    "shadow": False,
                    "topLevel": top
                }

            b_counter = 0
            def get_id():
                nonlocal b_counter
                b_counter += 1
                return f"b_{sprite_name}_{b_counter}"

            # 旗クリックで起動（同期なし・シンプル）
            prev_id = get_id()
            add_block(
                prev_id,
                "event_whenflagclicked",
                None,
                None,
                top=True
            )

            # 音量設定
            curr_id = get_id()
            blocks[prev_id]["next"] = curr_id
            add_block(curr_id, "sound_setvolumeto", None, prev_id, {"VOLUME": [1, [4, str(volume)]]})
            prev_id = curr_id

            # 初期テンポ設定
            curr_id = get_id()
            blocks[prev_id]["next"] = curr_id
            add_block(curr_id, "music_setTempo", None, prev_id, {"TEMPO": [1, [4, str(self.tempo_map[0][1])]]})
            prev_id = curr_id

            # 楽器設定（ドラム以外）
            if not tv['is_drum']:
                curr_id = get_id()
                blocks[prev_id]["next"] = curr_id
                inst_scratch = get_scratch_instrument(tv['instrument'], self.genre)
                add_block(curr_id, "music_setInstrument", None, prev_id, {"INSTRUMENT": [1, [4, str(inst_scratch)]]})
                prev_id = curr_id

            # ノート演奏（テンポ変更処理付き）
            current_tick = 0
            tempo_idx = 0
            for note in tv['notes']:
                # テンポ変更処理
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

                # ノート開始までの待機
                wait_ticks = note.start_tick - current_tick
                if wait_ticks > 0.01:
                    wait_beats = wait_ticks / self.ticks_per_beat
                    curr_id = get_id()
                    blocks[prev_id]["next"] = curr_id
                    add_block(curr_id, "music_restForBeats", None, prev_id, {"BEATS": [1, [4, str(wait_beats)]]})
                    prev_id = curr_id
                    current_tick = note.start_tick

                # ノート演奏
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

            sprite = {
                "isStage": False,
                "name": sprite_name,
                "variables": {},
                "lists": {},
                "broadcasts": {},
                "blocks": blocks,
                "comments": {},
                "currentCostume": 0,
                "costumes": [{"assetId": self.svg_md5, "name": "costume1", "md5ext": self.svg_filename, "dataFormat": "svg"}],
                "sounds": [],
                "volume": 100,
                "layerOrder": idx + 1,
                "visible": True,
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
                        if not is_drum and get_scratch_instrument(current_instrument) is None: continue
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
        self.log_message(f"変換開始: メイントラック={selected_idx}, ジャンル={self.genre_var.get()}")
        try:
            builder = ScratchProjectBuilder(
                self.midi_path, selected_idx, self.genre_var.get(),
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