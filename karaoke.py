import os, sys, io, random, time, json, hashlib, datetime
import logging, socket, subprocess
import multiprocessing as mp
import shutil, psutil
from subprocess import check_output
from collections import *
from tempfile import NamedTemporaryFile
# from contextlib import redirect_stdout, redirect_stderr

import numpy as np

from constants import media_types

import qrcode
import arabic_reshaper
from bidi.algorithm import get_display
from unidecode import unidecode
from lib import omxclient, vlcclient
from lib.get_platform import *
from app import getString
import yt_dlp

STD_VOL = 65536/8/np.sqrt(2)

if get_platform() != "windows":
	from signal import SIGALRM, alarm, signal


def cleanse_modules(name):
	try:
		for module_name in sorted(sys.modules.keys()):
			if module_name.startswith(name):
				del sys.modules[module_name]
		del globals()[name]
	except:
		pass


class Karaoke:
	raspi_wifi_config_ip = "10.0.0.1"
	raspi_wifi_conf_file = "/etc/raspiwifi/raspiwifi.conf"
	raspi_wifi_config_installed = os.path.exists(raspi_wifi_conf_file)
	ref_W, ref_H = 1920, 1080      # reference screen size, control drawing scale

	queue = []
	queue_hash = None
	available_songs = []
	rename_history = {}
	songname_trans = {} # transliteration is used for sorting and initial letter search
	now_playing = None
	now_playing_filename = None
	now_playing_user = None
	now_playing_transpose = 0
	now_playing_slave = ''
	audio_delay = 0
	has_video = True
	has_subtitle = False
	subtitle_delay = 0
	play_speed = 1.0
	show_subtitle = True
	last_vocal_info = 0
	last_vocal_time = 0
	use_DNN_vocal = True
	vocal_process = None
	vocal_device = None
	vocal_mode = 'mixed'
	is_paused = True
	firstSongStarted = False
	switchingSong = False
	qr_code_path = None
	base_path = os.path.dirname(__file__)
	volume_offset = 0
	loop_interval = 500  # in milliseconds
	default_logo_path = os.path.join(base_path, "logo.png")
	logical_volume = None   # for normalized volume
	searched_file_location = False
	play_history = []
	saved_songs = []
	audio_track = 0
	repeat_song = False
	song_stat = {}
	default_favorite_structure = {
		"name":"",
		"song_path":"",
		"play_count":1,
		"user_list":[],
		"last_play":"",
	}
	full_screen=True
	audio_mask=1

	def __init__(self, args):

		# override with supplied constructor args if provided
		self.args = args
		self.nonroot_user = args.nonroot_user
		self.port = args.port
		self.hide_ip = args.hide_ip
		self.hide_raspiwifi_instructions = args.hide_raspiwifi_instructions
		self.omxplayer_adev = 'both'
		self.download_path = args.dl_path
		self.dual_screen = args.dual_screen
		self.high_quality = args.high_quality
		self.splash_delay = int(args.splash_delay)
		self.volume_offset = self.volume = args.volume
		self.youtubedl_path = args.youtubedl_path
		self.omxplayer_path = args.omxplayer_path
		self.use_omxplayer = args.use_omxplayer
		self.use_vlc = args.use_vlc
		self.vlc_path = args.vlc_path
		self.vlc_port = args.vlc_port
		self.logo_path = self.default_logo_path if args.logo_path == None else args.logo_path
		self.show_overlay = args.show_overlay
		self.run_vocal = args.run_vocal
		self.normalize_vol = args.normalize_vol
		self.cookies_opt = args.cookies_opt
		self.stat_file_path = args.song_stat_filepath
		self.save_delays = args.save_delays

		# other initializations
		self.platform = get_platform()
		self.vlcclient = None
		self.omxclient = None
		self.screen = None
		self.player_state = {}
		self.downloading_songs = {}
		self.downloading_songs_pct = {}
		self.log_level = int(args.log_level)

		logging.basicConfig(
			format = "[%(asctime)s] %(levelname)s: %(message)s",
			datefmt = "%Y-%m-%d %H:%M:%S",
			level = self.log_level,
		)

		logging.debug(
			"""
	http port: %s
	hide IP: %s
	hide RaspiWiFi instructions: %s,
	splash_delay: %s
	omx audio device: %s
	dual screen: %s
	high quality video: %s
	download path: %s
	default volume: %s
	youtube-dl path: %s
	omxplayer path: %s
	logo path: %s
	Use OMXPlayer: %s
	Use VLC: %s
	VLC path: %s
	VLC port: %s
	log_level: %s
	show overlay: %s"""
			% (
				self.port,
				self.hide_ip,
				self.hide_raspiwifi_instructions,
				self.splash_delay,
				self.omxplayer_adev,
				self.dual_screen,
				self.high_quality,
				self.download_path,
				self.volume_offset,
				self.youtubedl_path,
				self.omxplayer_path,
				self.logo_path,
				self.use_omxplayer,
				self.use_vlc,
				self.vlc_path,
				self.vlc_port,
				self.log_level,
				self.show_overlay
			)
		)

		if self.save_delays:
			self.init_save_delays()

		# Generate connection URL and QR code, retry in case pi is still starting up
		# and doesn't have an IP yet (occurs when launched from /etc/rc.local)
		end_time = int(time.time()) + 30

		if self.platform == "raspberry_pi":
			while int(time.time()) < end_time:
				addresses_str = check_output(["hostname", "-I"]).strip().decode("utf-8")
				addresses = addresses_str.split(" ")
				self.ip = addresses[0]
				if not self.is_network_connected():
					logging.debug("Couldn't get IP, retrying....")
				else:
					break
		else:
			self.ip = self.get_ip()

		logging.debug("IP address (for QR code and splash screen): " + self.ip)

		self.url = "http://%s:%s" % (self.ip, self.port)

		# # get songs from download_path
		# if not self.searched_file_location:
		# 	self.get_available_songs_in_saved()
		# else:
		self.get_available_songs()

		# get favorite songs
		self.get_song_stat()
		
		# Automatically upgrade yt-dlp if using pip
		if not args.youtubedl_path:
			self.upgrade_youtubedl()

		# clean up old sessions
		self.kill_player()

		if self.show_overlay:
			self.generate_qr_code()

		if self.use_vlc:
			self.vlcclient = vlcclient.VLCClient(port = self.vlc_port, path = self.vlc_path,
			                                     qrcode = (self.qr_code_path if self.show_overlay else None), url = self.url)
			self.vlcclient.K = self
		else:
			self.omxclient = omxclient.OMXClient(path = self.omxplayer_path, adev = self.omxplayer_adev,
			                                     dual_screen = self.dual_screen, volume_offset = self.volume_offset)

	# Other ip-getting methods are unreliable and sometimes return 127.0.0.1
	# https://stackoverflow.com/a/28950776
	def get_ip(self):
		s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
		try:
			# doesn't even have to be reachable
			s.connect(("10.255.255.255", 1))
			IP = s.getsockname()[0]
		except Exception:
			IP = "127.0.0.1"
		finally:
			s.close()
		return IP

	def get_raspi_wifi_conf_vals(self):
		"""Extract values from the RaspiWiFi configuration file."""
		f = open(self.raspi_wifi_conf_file, "r")

		# Define default values.
		#
		# References:
		# - https://github.com/jasbur/RaspiWiFi/blob/master/initial_setup.py (see defaults in input prompts)
		# - https://github.com/jasbur/RaspiWiFi/blob/master/libs/reset_device/static_files/raspiwifi.conf
		#
		server_port = "80"
		ssid_prefix = "RaspiWiFi Setup"
		ssl_enabled = "0"

		# Override the default values according to the configuration file.
		for line in f.readlines():
			if "server_port=" in line:
				server_port = line.split("t=")[1].strip()
			elif "ssid_prefix=" in line:
				ssid_prefix = line.split("x=")[1].strip()
			elif "ssl_enabled=" in line:
				ssl_enabled = line.split("d=")[1].strip()

		return (server_port, ssid_prefix, ssl_enabled)

	def upgrade_youtubedl(self):
		logging.info("Uplifting yt-dlp to latest version")
		try:
			process = subprocess.Popen(['./.venv/bin/python3', '-m', 'pip', 'install', 'yt-dlp[default]', '-U'], shell = (self.platform == "windows"), stdin = subprocess.PIPE, stdout = sys.stdout, stderr = sys.stderr)
			process.wait()
			cleanse_modules('yt_dlp')
			logging.info("yt-dlp Uplifting successful")
		except Exception as e:
			logging.error(f"Error upgrading yt-dlp: {e.str()}")
			pass

	def is_network_connected(self):
		return not len(self.ip) < 7

	def generate_qr_code(self):
		logging.debug("Generating URL QR code")
		self.qr = qrcode.QRCode(version = 1, box_size = 3, border = 4, error_correction = qrcode.constants.ERROR_CORRECT_H)
		self.qr.add_data(self.url)
		self.qr.make()
		img = self.qr.make_image()
		self.qr_code_path = os.path.join(self.base_path, "qrcode.png")
		img.save(self.qr_code_path)

	def get_search_results(self, textToSearch):
		import yt_dlp
		logging.info("Searching YouTube for: " + textToSearch)
		num_results = 15
		yt_search = 'ytsearch%d:%s' % (num_results, textToSearch)
		# cmd = ["-j", "--no-playlist", "--flat-playlist", yt_search]
		# logging.debug("Youtube-dl search command: " + " ".join(cmd))

		ydl_opts = {
			'forcejson': True,
			'noplaylist': True,
			'simulate': True,
			'extract_flat': 'in_playlist',
			'no_progress': True,
			'quiet': True,
			'cookiefile': os.path.join(self.base_path, 'cookies.txt')
		}

		try:
			with yt_dlp.YoutubeDL(ydl_opts) as ydl:
				info = ydl.extract_info(yt_search, download=False)
				result = ydl.sanitize_info(info)
			results = []
			for entry in result['entries']:
				results.append([entry["title"], entry["url"], entry["id"]])
			return results
		except Exception as e:
			logging.error("Error while executing search: " + str(e))
			raise e

	def get_url_info(self, url):
		ydl_opts = {
		    'cookiefile': os.path.join(self.base_path, 'cookies.txt')
		}

		with yt_dlp.YoutubeDL(ydl_opts) as ydl:
			info = ydl.extract_info(url, download=False)
			return ydl.sanitize_info(info)

	def get_downloaded_file_basename(self, url):
		if 'watch?v=' in url:
			youtube_id = url.split("watch?v=")[1].split('&')[0]
		elif 'youtu.be' in url:
			youtube_id = url.split("youtu.be/")[1].split('?')[0]
		else:
			try:
				info = self.get_url_info(url)
				youtube_id = info['id']
			except Exception as e:
				logging.error("Error parsing video id from url [" + url + "]: "+ str(e))
				return None
		try:
			return [i for i in os.listdir(self.download_path+'tmp/') if youtube_id in i][0]
		except:
			pass

		filename = f"{info['title']}---{info['id']}.{info['ext']}"
		return filename if os.path.isfile(self.download_path+'tmp/'+filename) else None


	def download_video(self, song_url = '', enqueue = False, song_added_by = "Pikaraoke", include_subtitles = False, high_quality = False):
		import yt_dlp

		def progress_hook(song_url):
			def my_hook(d):
			    if d['status'] == 'finished':
			        logging.debug('Download complete, now post-processing ...')
			        self.downloading_songs_pct[song_url] = '@-----@100'
			    if d['status'] == 'downloading':
			    	pct = int(d["downloaded_bytes"] / d["total_bytes"] * 100)
			    	full_name = d['filename'].split('tmp/')[1]
			    	ext = full_name.rsplit('.', 1)[1]
			    	true_name = full_name.split('---')[0]
			    	file_name = f"{true_name}.{ext}"
			    	logging.debug(f'Downloading {file_name}, now {pct}%')
			    	self.downloading_songs_pct[song_url] = file_name + '@-----@' + str(pct)
			return my_hook

		logging.info("Downloading video: " + song_url)
		self.downloading_songs[song_url] = 1
		self.downloading_songs_pct.pop(song_url, None)
		dl_path = "%(title)s---%(id)s.%(ext)s"
		# opt_sub = ['--sub-langs', 'all', '--embed-subs'] if include_subtitles else []
		# cmd = ['--fixup', 'force', '--remux-video', 'mp4'] + opt_quality +\
		#       ["-o", self.download_path+'tmp/'+dl_path] + opt_sub + [song_url]

		ydl_opts = {
			'outtmpl': self.download_path+'tmp/'+dl_path,
		    'progress_hooks': [progress_hook(song_url)],
		    'cookiefile': os.path.join(self.base_path, 'cookies.txt')
		}

		with yt_dlp.YoutubeDL(ydl_opts) as ydl:
		    rc = ydl.download([song_url])
		# if rc != 0:
		# 	logging.error("Error code while downloading, retrying without format options ...")
		# 	cmd = ["-o", self.download_path + 'tmp/' + dl_path] + opt_sub + [song_url]
		# 	rc = self.call_yt_dlp(cmd)
		if rc == 0:
			logging.info("Song successfully downloaded: " + song_url)
			self.downloading_songs[song_url] = 0
			bn = self.get_downloaded_file_basename(song_url)
			if bn:
				shutil.move(self.download_path+'tmp/'+bn, self.download_path+bn)
				self.get_available_songs()
				if enqueue:
					self.enqueue(self.download_path+bn, song_added_by)
					self.downloading_songs[song_url] = '00'
			else:
				logging.error("Error queueing song: " + song_url)
				self.downloading_songs[song_url] = '01'
		else:
			logging.error("Error downloading song: " + song_url)
			self.downloading_songs[song_url] = -1
		return rc

	def get_available_songs(self):
		logging.info("Fetching available songs in: " + self.download_path)
		self.songname_trans = {}
		for bn in os.listdir(self.download_path):
			fn = self.download_path + bn
			if not bn.startswith('.') and os.path.isfile(fn):
				if os.path.splitext(fn)[1].lower() in media_types:
					trans = unidecode(self.filename_from_path(fn)).lower()
					# strip leading non-transliterable symbols
					while trans and not trans[0].islower() and not trans[0].isdigit():
						trans = trans[1:]
					self.songname_trans[fn] = trans

		# self.available_songs = sorted(files_grabbed, key = lambda f: str.lower(os.path.basename(f)))
		# logging.info("Path to json file: " + self.json_path_to_saved_file_location)
		# if  os.path.exists(self.json_path_to_saved_file_location):
		# 	logging.info("Path to json file exists: " + self.json_path_to_saved_file_location)
		# 	try:
		# 		with open(self.json_path_to_saved_file_location, 'r') as f:
		# 			self.saved_songs = json.load(f)
		# 		self.saved_songs.update(self.songname_trans)
		# 		self.songname_trans = self.saved_songs
		# 	except Exception as e:
		# 		print(f"Error in loading exisitng songs {e}")
		# else:
		# 	os.makedirs(os.path.dirname(self.json_path_to_saved_file_location), exist_ok=True)
		# 	with open(self.json_path_to_saved_file_location, "w") as f:
		# 		json.dump(self.songname_trans, f)
		self.available_songs = sorted(self.songname_trans, key = self.songname_trans.get)

	def get_all_assoc_files(self, song_path):
		basename = os.path.basename(song_path)
		basestem = os.path.splitext(basename)
		return [self.download_path + basename,
				self.download_path + basestem[0] + '.cdg',
				self.download_path + 'nonvocal/' + basename + '.m4a',
				self.download_path + 'nonvocal/.' + basename + '.m4a',
				self.download_path + 'vocal/' + basename + '.m4a',
				self.download_path + 'vocal/.' + basename + '.m4a']

	def delete_if_exist(self, filename):
		if os.path.isfile(filename):
			try:
				os.remove(filename)
			except:
				pass

	def delete(self, song_path):
		logging.info("Deleting song: " + song_path)

		# delete all associated cdg/vocal/nonvocal files if exist
		for fn in self.get_all_assoc_files(song_path):
			self.delete_if_exist(fn)

		self.get_available_songs()

	def rename_if_exist(self, old_path, new_path):
		if os.path.isfile(old_path):
			try:
				shutil.move(old_path, new_path)
			except:
				pass

	def rename(self, song_path, new_basestem):
		logging.info("Renaming song: '" + song_path + "' to: " + new_basestem)
		ext = os.path.splitext(song_path)
		if len(ext) < 2:
			ext += ['']
		new_basename = new_basestem + ext[1]

		# can handle the case while the file is being processed by vocal splitter, it has been renamed multiple times
		old_basename = os.path.basename(song_path)
		self.rename_history[old_basename] = new_basename
		for k, v in self.rename_history.items():
			if v == old_basename:
				self.rename_history[k] = new_basename

		# rename all associated cdg/vocal/nonvocal files if exist
		for src, tgt in zip(self.get_all_assoc_files(song_path), self.get_all_assoc_files(new_basename)):
			self.rename_if_exist(src, tgt)

		# rename queue entry if inside queue
		for item in self.queue:
			if item['file'] == song_path:
				item['file'] = self.download_path + new_basename
				item['title'] = self.filename_from_path(item['file'])
				break

		self.get_available_songs()

	def filename_from_path(self, file_path):
		rc = os.path.basename(file_path)
		rc = os.path.splitext(rc)[0]
		rc = rc.split("---")[0]  # removes youtube id if present
		return rc

	def kill_player(self):
		if self.use_vlc:
			logging.debug("Killing old VLC processes")
			if self.vlcclient != None:
				self.vlcclient.kill()
		elif self.omxclient != None:
				self.omxclient.kill()

	def play_file(self, file_path, extra_params = [], audio_track=1):
		self.switchingSong = True
		if self.use_vlc:
			if self.save_delays:
				saved_delays = self.delays.get(os.path.basename(file_path), {})
				self.audio_delay = self.audio_delay if self.audio_delay else saved_delays.get('audio_delay', 0)
				self.subtitle_delay = self.subtitle_delay if self.subtitle_delay else saved_delays.get('subtitle_delay', 0)
				self.show_subtitle = False if self.show_subtitle==False else saved_delays.get('show_subtitle', True)
			extra_params1 = []
			logging.info("Playing video in VLC: " + file_path)
			self.now_playing_slave = self.create_temp_file_if_needed(self.try_set_vocal_mode(self.vocal_mode, file_path))
			logging.info("Input Slave: " + self.now_playing_slave)
			if os.path.isfile(self.now_playing_slave):
				extra_params1 += [f'--input-slave={self.now_playing_slave}', f'--audio-track={self.audio_track}']
			if self.audio_delay:
				extra_params1 += [f'--audio-desync={self.audio_delay * 1000}']
			if self.subtitle_delay:
				extra_params1 += [f'--sub-delay={self.subtitle_delay * 10}']
			if self.show_subtitle:
				extra_params1 += [f'--sub-track=0']
			if self.play_speed != 1:
				extra_params1 += [f'--rate={self.play_speed}']
			extra_params1 += ['--file-caching=24000', '--network-caching=24000', '--avcodec-hw=vaapi']
			self.now_playing = self.filename_from_path(file_path)
			self.now_playing_filename = file_path
			self.is_paused = ('--start-paused' in extra_params1)
			if self.normalize_vol and self.logical_volume is not None:
				self.volume = self.logical_volume / np.sqrt(self.compute_volume(file_path))
			if self.now_playing_transpose == 0:
				xml = self.vlcclient.play_file(self.create_temp_file_if_needed(file_path), self.volume, extra_params + extra_params1)
			else:
				xml = self.vlcclient.play_file_transpose(file_path, self.now_playing_transpose, self.volume, extra_params + extra_params1)
			self.has_subtitle = "<info name='Type'>Subtitle</info>" in xml
			self.has_video = "<info name='Type'>Video</info>" in xml
			self.volume = round(float(self.vlcclient.get_val_xml(xml, 'volume')))
			if self.normalize_vol:
				self.media_vol = self.compute_volume(self.now_playing_filename)
				self.logical_volume = self.volume * np.sqrt(self.media_vol)
		else:
			logging.info("Playing video in omxplayer: " + file_path)
			self.omxclient.play_file(file_path)

		self.switchingSong = False

	def play_transposed(self, semitones):
		if self.use_vlc:
			if self.now_playing_transpose == semitones:
				return
			self.now_playing_transpose = semitones
			status_xml = self.vlcclient.command().text if self.is_paused else self.vlcclient.pause(False).text
			info = self.vlcclient.get_info_xml(status_xml)
			posi = info['position']*info['length']
			self.play_file(self.now_playing_filename, [f'--start-time={posi}'] + (['--start-paused'] if self.is_paused else []))
		else:
			logging.error("Not using VLC. Can't transpose track.")

	def is_file_playing(self):
		client = self.vlcclient if self.use_vlc else self.omxclient
		if client is not None and client.is_running():
			return True
		elif self.now_playing_filename:
			self.now_playing = self.now_playing_filename = None
		return False

	def is_song_in_queue(self, song_path):
		return song_path in map(lambda t: t['file'], self.queue)

	def enqueue(self, song_path, user = "Pikaraoke"):
		if (self.is_song_in_queue(song_path)):
			logging.warn("Song is already in queue, will not add: " + song_path)
			return False
		else:
			logging.info("'%s' is adding song to queue: %s" % (user, song_path))
			self.queue.append({"user": user, "file": song_path, "title": self.filename_from_path(song_path)})
			self.update_song_stat(user, song_path)
			self.update_queue_hash()
			return True

	def queue_add_random(self, amount):
		logging.info("Adding %d random songs to queue" % amount)
		songs = list(self.available_songs)  # make a copy
		if len(songs) == 0:
			logging.warn("No available songs!")
			return False
		i = 0
		while i < amount:
			r = random.randint(0, len(songs) - 1)
			if self.is_song_in_queue(songs[r]):
				logging.warn("Song already in queue, trying another... " + songs[r])
			else:
				self.queue.append({"user": "Randomizer", "file": songs[r], "title": self.filename_from_path(songs[r])})
				i += 1
			songs.pop(r)
			if len(songs) == 0:
				self.update_queue_hash()
				logging.warn("Ran out of songs!")
				return False
		self.update_queue_hash()
		return True

	def queue_add_all(self, who):
		who_string = ''
		if who == 1:
			who_string = '咪'
		elif who == 2:
			who_string = '绵'
		elif who == 3:
			who_string = '告五人'
		else:
			who_string = 'placeholder'

		logging.info("Adding songs that starts with %s to queue." % who_string)
		songs = list(self.available_songs)  # make a copy

		if len(songs) == 0:
			logging.warn("No available songs!")
			return 0

		count = 0
		for song_path in songs:
			filename = self.filename_from_path(song_path)
			if filename.startswith(who_string):
				logging.info("Adding song %s to queue." % filename)
				self.queue.append({"user": "Randomizer", "file": song_path, "title": filename})
				count+=1
		self.update_queue_hash()
		return count

	def update_queue_hash(self):
		self.queue_hash = hashlib.md5(json.dumps(self.queue).encode('utf-8')).hexdigest()

	def _queue_clear(self):
		self.queue = []
		self.update_queue_hash()

	def queue_clear(self):
		logging.info("Clearing queue.")
		self._queue_clear()

	def queue_clear_and_skip(self):
		logging.info("Clearing queue and skip current.")
		self._queue_clear()
		self.skip()

	def queue_edit(self, song_name, action, **kwargs):
		if action == "move":
			try:
				src, tgt, size = [int(kwargs[n]) for n in ['src', 'tgt', 'size']]
				if size > len(self.queue):
					# new songs have started while dragging the list
					diff = size - len(self.queue)
					src -= diff
					tgt -= diff
				song = self.queue.pop(src)
				self.queue.insert(tgt, song)
			except:
				logging.error("Invalid move song request: " + str(kwargs))
				return False
		else:
			index = 0
			song = None
			for each in self.queue:
				if song_name in each["file"]:
					song = each
					break
				else:
					index += 1
			if song == None:
				logging.error("Song not found in queue: " + song["file"])
				return False
			if action == "up":
				if index < 1:
					logging.warn("Song is up next, can't bump up in queue: " + song["file"])
					return False
				else:
					logging.info("Bumping song up to the front of queue: " + song["file"])
					del self.queue[index]
					self.queue.insert(0, song)
			elif action == "down":
				if index == len(self.queue) - 1:
					logging.warn("Song is already last, can't bump down in queue: " + song["file"])
					return False
				else:
					logging.info("Bumping song down in queue: " + song["file"])
					del self.queue[index]
					self.queue.insert(index + 1, song)
			elif action == "delete":
				logging.info("Deleting song from queue: " + song["file"])
				del self.queue[index]
			else:
				logging.error("Unrecognized direction: " + action)
				return False
		self.update_queue_hash()
		return True
	
	def randomize(self):
		if self.queue:
			print("Randomize current songs")
			random.shuffle(self.queue)
			self.update_queue_hash() 

	def skip(self):
		if self.is_file_playing():
			logging.info("Skipping: " + self.now_playing)
			if self.use_vlc:
				self.vlcclient.stop()
			else:
				self.omxclient.stop()
			self.reset_now_playing()
			return True
		logging.warning("Tried to skip, but no file is playing!")
		return False

	def seek(self, seek_sec):
		if self.is_file_playing():
			if self.use_vlc:
				self.vlcclient.seek(seek_sec)
			else:
				logging.warning("OMXplayer cannot seek track!")
			return True
		logging.warning("Tried to seek, but no file is playing!")
		return False

	def set_delays_dict(self, filename, key, val, dft_val=0):
		basename = os.path.basename(filename)
		delays = self.delays.get(basename, {})
		if val == dft_val:
			delays.pop(key, None)
		else:
			delays[key] = val
		if delays:
			self.delays[basename] = delays
		else:
			self.delays.pop(basename, {})
		self.delays_dirty = True

	def set_audio_delay(self, delay):
		if delay == '+':
			self.audio_delay += 0.1
		elif delay == '-':
			self.audio_delay -= 0.1
		elif delay == '':
			self.audio_delay = 0
		else:
			try:
				self.audio_delay = float(delay)
			except:
				logging.warning(f"Tried to set audio delay to an invalid value {delay}, ignored!")
				return False

		if self.save_delays:
			self.set_delays_dict(self.now_playing_filename, 'audio_delay', self.audio_delay)

		if self.is_file_playing():
			if self.use_vlc:
				self.vlcclient.command(f"audiodelay&val={self.audio_delay}")
			else:
				logging.warning("OMXplayer cannot set audio delay!")
			return self.audio_delay
		logging.warning("Tried to set audio delay, but no file is playing!")
		return False

	def set_subtitle_delay(self, delay):
		if delay == '+':
			self.subtitle_delay += 0.1
		elif delay == '-':
			self.subtitle_delay -= 0.1
		elif delay == '':
			self.subtitle_delay = 0
		else:
			try:
				self.subtitle_delay = float(delay)
			except:
				logging.warning(f"Tried to set subtitle delay to an invalid value {delay}, ignored!")
				return False

		if self.save_delays:
			self.set_delays_dict(self.now_playing_filename, 'subtitle_delay', self.subtitle_delay)

		if self.is_file_playing():
			if self.use_vlc:
				self.vlcclient.command(f"subdelay&val={self.subtitle_delay}")
			else:
				logging.warning("OMXplayer cannot set subtitle delay!")
			return self.subtitle_delay
		logging.warning("Tried to set subtitle delay, but no file is playing!")
		return False

	def toggle_subtitle(self):
		self.show_subtitle = not self.show_subtitle
		if self.save_delays:
			self.set_delays_dict(self.now_playing_filename, 'show_subtitle', self.show_subtitle, True)
		self.play_vocal(force=True)

	def pause(self):
		if self.is_file_playing():
			logging.info("Toggling pause: " + self.now_playing)
			if self.use_vlc:
				if self.vlcclient.is_playing():
					self.vlcclient.pause()
					self.is_paused = True
				else:
					self.vlcclient.play()
					self.is_paused = False
			else:
				if self.omxclient.is_playing():
					self.omxclient.pause()
					self.is_paused = True
				else:
					self.omxclient.play()
					self.is_paused = False
			return True
		else:
			logging.warning("Tried to pause, but no file is playing!")
			return False

	def vol_up(self):
		if self.is_file_playing():
			if self.use_vlc:
				self.vlcclient.vol_up()
				xml = self.vlcclient.command().text
				self.volume = int(self.vlcclient.get_val_xml(xml, 'volume'))
			else:
				self.volume = self.omxclient.vol_up()
			self.update_logical_vol()
			return self.volume
		else:
			logging.warning("Tried to volume up, but no file is playing!")
			return False

	def vol_down(self):
		if self.is_file_playing():
			if self.use_vlc:
				self.vlcclient.vol_down()
				xml = self.vlcclient.command().text
				self.volume = int(self.vlcclient.get_val_xml(xml, 'volume'))
			else:
				self.volume = self.omxclient.vol_down()
			self.update_logical_vol()
			return self.volume
		else:
			logging.warning("Tried to volume down, but no file is playing!")
			return False

	def vol_set(self, volume):
		if self.is_file_playing():
			if self.use_vlc:
				self.vlcclient.vol_set(volume)
				xml = self.vlcclient.command().text
				self.volume = int(self.vlcclient.get_val_xml(xml, 'volume'))
			else:
				logging.warning("Only VLC player can set volume, ignored!")
				self.volume = self.omxclient.volume_offset
			self.update_logical_vol()
			return self.volume
		else:
			logging.warning("Tried to set volume, but no file is playing!")
			return False

	def play_speed_set(self, speed):
		if self.is_file_playing():
			if self.use_vlc:
				self.vlcclient.playspeed_set(speed)
				xml = self.vlcclient.command().text
				self.play_speed = float(self.vlcclient.get_val_xml(xml, 'rate'))
				logging.info(f"Playback speed set to {self.play_speed}")
			else:
				logging.warning("Only VLC player can set playback speed, ignored!")
			return self.play_speed
		else:
			logging.warning("Tried to set play speed, but no file is playing!")
			return False

	def try_set_vocal_mode(self, mode, now_playing_filename):
		logging.info("Now playing file: " + now_playing_filename)
		if mode not in ['mixed', 'vocal', 'nonvocal']:
			mode = {1: 'nonvocal', 2: 'mixed', 3: 'vocal'}[self.get_vocal_mode()]

		fn, _ = os.path.splitext(os.path.basename(now_playing_filename))
		play_slave = '' if mode == 'mixed' else self.download_path + mode + '/' + ('' if self.use_DNN_vocal else '.') \
		                                       + fn + '.m4a'
		logging.info("playing slave file: " + play_slave)
		if os.path.isfile(play_slave):
			self.vocal_mode = mode
		else:
			play_slave = ''
			self.vocal_mode = 'mixed'
		return play_slave

	def track_select(self, idx=None):
		if idx:
			self.audio_track = idx
		if self.use_vlc:
			status_xml = self.vlcclient.command().text if self.is_paused else self.vlcclient.pause(False).text
			info = self.vlcclient.get_info_xml(status_xml)
			posi = info['position']*info['length']
			self.play_file(self.now_playing_filename, [f'--start-time={posi}'] + (['--start-paused'] if self.is_paused else []), audio_track = idx)
			print("track switch completed")
		else:
			logging.error("Not using VLC. Can't play vocal/nonvocal.")

	def track_select_1(self, idx = None):
		# idx 0: left audio track not setup 1:right setup audio track
		self.switchingSong = True
		if idx:
			self.audio_track = idx
		if self.use_vlc:
			extra_params1 = []
			extra_params1 += [f'--input-slave={self.now_playing_slave}', f'--audio-track={self.audio_track}']
			file_path = self.now_playing_filename
			logging.info("Change audio track in VLC: " + self.now_playing_filename + f" to audio track {idx}")
			status_xml = self.vlcclient.command().text if self.is_paused else self.vlcclient.pause(False).text
			info = self.vlcclient.get_info_xml(status_xml)
			posi = info['position']*info['length']
			extra_params1 += ([f'--start-time={posi}'] + (['--start-paused'] if self.is_paused else []))
			if self.audio_delay:
				extra_params1 += [f'--audio-desync={self.audio_delay * 1000}']
			if self.subtitle_delay:
				extra_params1 += [f'--sub-delay={self.subtitle_delay * 10}']
			if self.show_subtitle:
				extra_params1 += [f'--sub-track=0']
			if self.play_speed != 1:
				extra_params1 += [f'--rate={self.play_speed}']
			self.is_paused = ('--start-paused' in extra_params1)
			if self.normalize_vol and self.logical_volume is not None:
				self.volume = self.logical_volume / np.sqrt(self.compute_volume(file_path))
			if self.now_playing_transpose == 0:
				xml = self.vlcclient.play_file(file_path, self.volume, extra_params1)
			else:
				xml = self.vlcclient.play_file_transpose(file_path, self.now_playing_transpose, self.volume, extra_params1)
			self.has_subtitle = "<info name='Type'>Subtitle</info>" in xml
			self.has_video = "<info name='Type'>Video</info>" in xml
			self.volume = round(float(self.vlcclient.get_val_xml(xml, 'volume')))
			if self.normalize_vol:
				self.media_vol = self.compute_volume(self.now_playing_filename)
				self.logical_volume = self.volume * np.sqrt(self.media_vol)
		else:
			logging.info("Playing video in omxplayer: " + file_path)
			self.omxclient.play_file(file_path)

		self.switchingSong = False

	def play_vocal(self, mode = None, force = False):
		# mode=vocal/nonvocal/mixed, or else (use current)
		if self.use_vlc:
			if mode == "mixed":
				self.audio_track = 0
			elif mode in ['vocal', 'nonvocal']:
				self.audio_track = 1
			else:
				self.audio_track = self.audio_mask - self.audio_track
			play_slave = self.try_set_vocal_mode(mode, self.now_playing_filename)
			if not force and self.now_playing_slave == play_slave:
				return
			status_xml = self.vlcclient.command().text if self.is_paused else self.vlcclient.pause(False).text
			info = self.vlcclient.get_info_xml(status_xml)
			posi = info['position']*info['length']
			self.play_file(self.now_playing_filename, [f'--start-time={posi}'] + (['--start-paused'] if self.is_paused else []))
			self.get_vocal_info(True)
			print("vocal setup completed")
		else:
			logging.error("Not using VLC. Can't play vocal/nonvocal.")

	def get_vocal_mode(self):
		if '/nonvocal/' in self.now_playing_slave.replace('\\', '/'):
			return 1
		elif '/vocal/' in self.now_playing_slave.replace('\\', '/'):
			return 3
		elif self.vocal_mode == 'nonvocal':
			return 1
		elif self.vocal_mode == 'mixed':
			return 2
		elif self.vocal_mode == 'vocal':
			return 3
		return 2

	def get_vocal_info(self, force_update=False):
		tm = time.time()
		if not force_update and tm-self.last_vocal_time < 2:
			return self.last_vocal_info
		if not self.now_playing_filename:
			return 0
		mask = 0
		bn, _ = os.path.splitext(os.path.basename(self.now_playing_filename))
		# if os.path.isfile(f'{self.download_path}nonvocal/{bn}.m4a'):
		if self.vocal_mode == 'nonvocal' or os.path.isfile(f'{self.download_path}nonvocal/{bn}.m4a'):
			mask |= 0b00000001
		# if os.path.isfile(f'{self.download_path}vocal/{bn}.m4a'):
		if self.vocal_mode == 'vocal' or os.path.isfile(f'{self.download_path}vocal/{bn}.m4a'):
			mask |= 0b00000010
		if os.path.isfile(f'{self.download_path}nonvocal/.{bn}.m4a'):
			mask |= 0b00000100
		if os.path.isfile(f'{self.download_path}vocal/.{bn}.m4a'):
			mask |= 0b00001000
		if 'vocal/.' in self.now_playing_slave:
			mask |= 0b10000000
		if self.use_DNN_vocal:
			mask |= 0b01000000
		mask |= (self.get_vocal_mode() << 4)
		self.last_vocal_info = mask
		self.last_vocal_time = tm
		return mask

	def get_state(self):
		if self.use_vlc and self.vlcclient.is_transposing:
			return defaultdict(lambda: None, self.player_state)
		if not self.is_file_playing():
			self.player_state['now_playing'] = None
			return defaultdict(lambda: None, self.player_state)
		new_state = self.vlcclient.get_info_xml() if self.use_vlc else {
			'volume': self.omxclient.volume_offset,
			'state': ('paused' if self.omxclient.paused else 'playing')
		}
		self.player_state.update(new_state)
		result = defaultdict(lambda: None, self.player_state)
		logging.debug(f"Home page player state: {result}")

		return result

	def restart(self):
		if self.is_file_playing():
			if self.use_vlc:
				self.vlcclient.restart()
			else:
				self.omxclient.restart()
			self.is_paused = False
			return True
		else:
			logging.warning("Tried to restart, but no file is playing!")
			return False

	def stop(self):
		self.running = False

	def handle_run_loop(self):
		time.sleep(self.loop_interval / 1000)

	def reset_now_playing(self):
		self.preserve_delay_info()
		self.now_playing = None
		self.now_playing_filename = None
		self.now_playing_user = None
		self.is_paused = True
		self.now_playing_transpose = 0
		self.now_playing_slave = ''
		self.audio_delay = 0
		self.subtitle_delay = 0
		self.show_subtitle = True
		self.has_subtitle = False
		self.has_video = True
		self.last_vocal_info = 0
		self.play_speed = 1

	def streamer_alive(self):
		try:
			return bool([1 for p in psutil.process_iter() if './screencapture.sh' in p.cmdline()])
		except:
			return None

	def streamer_restart(self, delay=0):
		if self.platform in ['windows', 'osx']:
			return
		if os.geteuid()==0 and self.nonroot_user:
			os.system(f"su -l {self.nonroot_user} -c 'sleep {delay} && tmux send-keys -t PiKaraoke:0.3 C-c && tmux send-keys -t PiKaraoke:0.3 Up Enter'")
		else:
			os.system(f"sleep {delay} && tmux send-keys -t PiKaraoke:0.3 C-c && tmux send-keys -t PiKaraoke:0.3 Up Enter")

	def streamer_stop(self, delay=0):
		if self.platform in ['windows', 'osx']:
			return
		if os.geteuid()==0 and self.nonroot_user:
			os.system(f"su -l {self.nonroot_user} -c 'sleep {delay} && tmux send-keys -t PiKaraoke:0.3 C-c'")
		else:
			os.system(f"sleep {delay} && tmux send-keys -t PiKaraoke:0.3 C-c")

	def vocal_alive(self):
		try:
			return bool(self.vocal_process and self.vocal_process.is_alive())\
					or bool([1 for p in psutil.process_iter() if 'vocal_splitter.py' in p.cmdline()])
		except:
			return None

	def vocal_restart(self):
		if self.platform == 'windows' or self.run_vocal:
			import vocal_splitter
			if self.vocal_process is not None and self.vocal_process.is_alive():
				self.vocal_process.kill()
			if shutil.which('ffmpeg'):
				self.vocal_process = mp.Process(target=vocal_splitter.main, args=(['-p', '-d', self.download_path],))
				self.vocal_process.start()
		else:
			if os.geteuid()==0 and self.nonroot_user:
				os.system(f"su -l {self.nonroot_user} -c 'tmux send-keys -t PiKaraoke:0.4 C-c && tmux send-keys -t PiKaraoke:0.4 Up Enter'")
			else:
				os.system(f"tmux send-keys -t PiKaraoke:0.4 C-c && tmux send-keys -t PiKaraoke:0.4 Up Enter")

	def vocal_stop(self):
		if self.vocal_process is not None and self.vocal_process.is_alive():
			self.vocal_process.kill()
		elif self.platform != 'windows':
			if os.geteuid() == 0 and self.nonroot_user:
				os.system(f"su -l {self.nonroot_user} -c 'tmux send-keys -t PiKaraoke:0.4 C-c'")
			else:
				os.system(f"tmux send-keys -t PiKaraoke:0.4 C-c")

	def compute_volume(self, filename):
		try:
			pcm_data = subprocess.check_output(['ffmpeg', '-i', filename, '-vn', '-f', 's16le', '-acodec', 'pcm_s16le', '-'], stderr = subprocess.DEVNULL)
			return np.clip(np.sqrt(np.std(np.frombuffer(pcm_data, dtype = np.int16))/STD_VOL), 0.1, 10)
		except:
			self.normalize_vol = False
			return 1

	def update_logical_vol(self):
		if hasattr(self, 'media_vol'):
			self.logical_volume = self.volume * self.media_vol

	def enable_vol_norm(self, enable):
		self.normalize_vol = enable
		if enable and shutil.which('ffmpeg') is None:
			self.normalize_vol = enable = False
		if enable and self.now_playing_filename:
			self.volume = self.vlcclient.get_info_xml()['volume']
			self.media_vol = self.compute_volume(self.now_playing_filename)
			self.update_logical_vol()
		return str(self.logical_volume)
	
	def set_repeat_on(self):
		self.repeat_song = True
		return 1
	
	def set_repeat_off(self):
		self.repeat_song = False
		return
	
	def get_song_stat(self):
		if os.path.exists(self.stat_file_path):
			try:
				with open(self.stat_file_path, 'r') as f:
					data = json.load(f)
				# Process data...
				self.song_stat.update(data)
				logging.info(f"{self.stat_file_path} favorite songs load succeed")
			except Exception as e:
				# Handle JSON decode error or other file read errors
				os.rename(self.stat_file_path, self.stat_file_path + '.bak')
				with open(self.stat_file_path, 'w') as f:
					json.dump(self.song_stat, f)  # Create a new empty file
				logging.info(f"Target file location has unsupported content format. Move current file to {self.stat_file_path+'.bak'} and created empty favorite songs file.")
		else:
			with open(self.stat_file_path, 'w') as f:
				json.dump(self.song_stat, f)  # Create a new empty file

	def save_song_stat(self):
		try:
			with open(self.stat_file_path, 'w') as f:
				json.dump(self.song_stat, f)
			logging.info(f"Current favorite songs has been saved to {self.stat_file_path}")
		except Exception as e:
			logging.error(f"Favorite songs can't be saved to target location {self.stat_file_path}: {e}")

	def update_song_stat(self, user, song_path):
		song_name = self.filename_from_path(song_path)
		current_song_stat = self.song_stat.setdefault(song_name, {
			"name":song_name,
			"song_path":song_path,
			"play_count":0,
			"user_list":[],
			"last_play":datetime.datetime.now(),
		})
		current_song_stat["play_count"]+=1
		if user not in current_song_stat["user_list"]:
			current_song_stat["user_list"].append(user)
		current_song_stat["last_play"] = datetime.datetime.now().strftime("%m/%d/%Y, %H:%M:%S")
		self.song_stat[song_name] = current_song_stat
		self.save_song_stat()

	def update_song_musician(self, song_path, musician):
		song_name = self.filename_from_path(song_path)
		current_song_stat = self.song_stat.setdefault(song_name, {
			"name":song_name,
			"song_path":song_path,
			"play_count":0,
			"user_list":[],
			"last_play":datetime.datetime.now(),
		})
		current_song_stat["musician"] = musician
		self.song_stat[song_name] = current_song_stat
		self.save_song_stat()

	def get_favorite_song_list(self):
		sorted_songs = sorted(self.song_stat.values(), key=lambda x: x['play_count'], reverse=True)
		return sorted_songs

	def get_song_list_by_musician(self):
		result = {}
		for song, song_stat in song_stat.items():
			if "musician" in song_stat:
				musician = song_stat["musician"]
				if musician not in result:
					result[musician] = []
				result[musician].append(song_stat)
		sorted_result = dict(sorted(result.items()))
		return sorted_result

	def init_save_delays(self):
		self.delays_dirty = False
		try:
			self.delays = eval(open(self.save_delays).read())
		except Exception as e:
			logging.error(f"Error parsing delays file [{self.save_delays}]: {e}")
			self.delays = {}
			with open(self.save_delays, 'w') as fp:
				fp.write(str(self.delays))

	def set_save_delays(self, state):
		if state != bool(self.save_delays):
			if state:
				self.save_delays = self.dft_delays_file
				self.init_save_delays()
			else:
				self.save_delays = None
				self.delete_if_exist(self.dft_delays_file)

	def preserve_delay_info(self):
		if self.save_delays and self.delays_dirty:
			self.delays_dirty = False
			with open(self.save_delays, 'w') as fp:
				fp.write(str(self.delays))
	
	def run(self):
		logging.info("Server started, URL: " + self.url)

		self.running = True

		# Windows does not have tmux, vocal splitter can only be invoked from the main program
		if self.platform == 'windows' or self.run_vocal:
			self.vocal_restart()
		
		head = None

		while self.running:
			try:
				if not self.is_file_playing() and self.now_playing != None:
					self.reset_now_playing()
				if self.repeat_song and head and not self.is_file_playing():
					self.play_file(head['file'])
				if self.queue:
					if not self.is_file_playing():
						self.reset_now_playing()
						i = 0
						while i < (self.splash_delay * 1000):
							self.handle_run_loop()
							i += self.loop_interval
						head = self.queue.pop(0)
						self.play_file(head['file'])
						if not self.firstSongStarted:
							if self.streamer_alive():
								self.streamer_restart(1)
							self.firstSongStarted = True
						self.now_playing_user = head["user"]
						self.update_queue_hash()
				self.handle_run_loop()
			except KeyboardInterrupt:
				logging.warn("Keyboard interrupt: Exiting pikaraoke...")
				self.running = False

		# Clean up before quit
		self.streamer_stop()
		self.vocal_stop()
		(self.vlcclient if self.use_vlc else self.omxclient).stop()
		self.preserve_delay_info()
		time.sleep(1)
		(self.vlcclient if self.use_vlc else self.omxclient).kill()

	def create_temp_file_if_needed(self, original_path):
		if '&' in original_path:
			# temp_files = []
			# base_dir, original_filename = os.path.split(original_path)
			# original_basename, original_ext = os.path.splitext(original_filename)
			# for track_type in ['vocal', 'nonvocal']:
			# 	track_path = os.path.join(base_dir, track_type, f"{original_basename}.m4a")
			# 	if os.path.exists(track_path):
			# 		with NamedTemporaryFile(delete=True, suffix='.m4a', dir=os.path.join(base_dir, track_type)) as temp_file:
			# 			temp_track_path = temp_file.name
			# 			shutil.copy2(track_path, temp_track_path)
			# 			temp_files.append(temp_track_path)
			# 			print(f"Created a temporary {track_type} track file: {temp_track_path}")
			with NamedTemporaryFile(delete=True, suffix=os.path.splitext(original_path)[1]) as temp_file:
				temp_video_path = temp_file.name
			shutil.copy2(original_path, temp_video_path)
			print(f"Created a temporary video file: {temp_video_path}")
			return temp_video_path
		else:
			return original_path