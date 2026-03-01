import socket
import qrcode

s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
s.connect(("10.255.255.255", 1))
ip = s.getsockname()[0]


url = "http://%s:%s" % (ip, '5000')
qr = qrcode.QRCode(version = 1, box_size = 3, border = 4, error_correction = qrcode.constants.ERROR_CORRECT_H)
qr.add_data(url)
qr.make()
print("URL: " + url)
qr.print_ascii()
