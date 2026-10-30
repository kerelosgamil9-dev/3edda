[app]

title = 3edda
package.name = edda
package.domain = org.edda
source.dir = .
# ttf,otf = الخطوط لازم تتضمن في الـ APK
source.include_exts = py,png,jpg,jpeg,kv,atlas,ttf,otf,json,txt
version = 1.0

requirements = python3==3.11.5,hostpython3==3.11.5,kivy==2.3.0,pillow,qrcode,arabic-reshaper,python-bidi==0.4.2,fonttools,pyjnius,android

orientation = portrait
fullscreen = 0

android.permissions = CAMERA,READ_EXTERNAL_STORAGE,WRITE_EXTERNAL_STORAGE,READ_MEDIA_IMAGES,INTERNET,VIBRATE

android.api = 35
android.minapi = 26
android.ndk = 25b
android.archs = arm64-v8a
android.accept_sdk_license = True
android.allow_backup = True

[buildozer]
log_level = 2
warn_on_root = 1
