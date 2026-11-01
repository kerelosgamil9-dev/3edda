# -*- coding: utf-8 -*-
"""
عِدّة | Idda  —  كل أدواتك في مكان واحد  |  All your tools in one place
=========================================================================

Tools / الأدوات
  1. QR generator   إنشاء QR        (link / phone / text -> save + share)
  2. Image compress ضغط الصور       (quality, before/after size, save)
  3. Images to PDF  صور إلى PDF     (many images, ordering, page size)
  4. Text tools     أدوات النصوص    (counters, dedupe, clean spaces, copy)
  5. QR scanner     قارئ QR         (camera / gallery, safe link opening)
  6. Compress PDF   ضغط PDF         (shrink big PDF files, 3 levels, before/after size)
  7. Merge PDF      دمج PDF         (2+ PDF files, you choose the order, one PDF out)

Appearance / المظهر: Light, Dark, or "same as the device" (Settings -> Appearance).

Requirements / المتطلبات (Pydroid 3 -> Pip):
  kivy         (already there)
  pillow       (required)
  pypdf        (required for tools 6 and 7: Compress PDF / Merge PDF - pure Python)
  qrcode       (required for creating QR codes)
  arabic-reshaper  +  python-bidi==0.4.2   (recommended: connects Arabic letters)
  fonttools    (recommended, pure Python, free: lets ONE font draw Arabic + symbols)

QR reading is built in (pure Python + Pillow) -> opencv is NOT needed any more.

Fonts: put Cairo / Tajawal (+ DejaVuSans, NotoSans*Symbols*, NotoEmoji ...) .ttf files
next to this file (or in a "fonts" folder).  On the first start the app builds ONE
font out of them (a few seconds, once) so Arabic, English, numbers and symbols all
share the same size and baseline and no symbol turns into an empty square.

Everything runs locally. Nothing is uploaded anywhere.
"""

import os
import io
import re
import copy
import sys
import json
import math
import time
import wave
import struct
import random
import threading
import datetime
import queue
import weakref
import functools
import unicodedata
import traceback
import webbrowser
from urllib.parse import urlparse

APP_VERSION = "1.0"

# --------------------------------------------------------------------------
# Optional third-party libraries (every one of them is guarded)
# --------------------------------------------------------------------------
try:
    from PIL import Image, ImageDraw, ImageFilter, ImageFont, ImageOps, ImageColor
    HAS_PIL = True
    _RES = getattr(Image, "Resampling", Image)
    LANCZOS = _RES.LANCZOS
    NEAREST = _RES.NEAREST
except Exception:                                   # pragma: no cover
    HAS_PIL = False
    Image = ImageDraw = ImageFilter = ImageFont = ImageOps = ImageColor = None
    LANCZOS = NEAREST = None

try:
    import numpy as np
except Exception:
    np = None

try:
    import cv2
except Exception:
    cv2 = None

try:
    import qrcode as _qrcode_lib
except Exception:
    _qrcode_lib = None

try:
    from pyzbar import pyzbar as _zbar
except Exception:
    _zbar = None

try:
    import pypdf as _pypdf
    HAS_PYPDF = True
except Exception:
    _pypdf = None
    HAS_PYPDF = False

try:
    import arabic_reshaper as _ar_reshaper
    try:
        from bidi.algorithm import get_display as _get_display
    except Exception:
        from bidi import get_display as _get_display
    try:
        _RESHAPER = _ar_reshaper.ArabicReshaper(configuration={"delete_harakat": False})
    except Exception:
        _RESHAPER = None
    HAS_SHAPER = True
except Exception:
    _ar_reshaper = None
    _get_display = None
    _RESHAPER = None
    HAS_SHAPER = False

# --------------------------------------------------------------------------
# Theme: dark (taken from the reference screenshot) + light + "same as the device"
# --------------------------------------------------------------------------
C_DARK = {
    "bg":       "#0E1823",
    "card":     "#1B2A3A",
    "card_hi":  "#243749",
    "line":     "#2B3E51",
    "badge":    "#244A5C",
    "accent":   "#5CE0C6",
    "on_acc":   "#06231F",
    "text":     "#F2F6FA",
    "muted":    "#8FA3B5",
    "danger":   "#F87171",
    "danger_bg": "#3A2029",
    "warn":     "#FBBF24",
    "ok":       "#4ADE80",
    "white":    "#FFFFFF",
    "toggle_off": "#33485C",
    "track":    "#2E4256",
    "menu":     "#2B3E51",
    "loupe":    "#1E3044",
    "toast_info": "#2B4156",
    "toast_ok":   "#17493F",
    "toast_error": "#5A2530",
}

C_LIGHT = {
    "bg":       "#ECF0F5",
    "card":     "#FFFFFF",
    "card_hi":  "#E4EBF3",
    "line":     "#D3DCE7",
    "badge":    "#D3EEE8",
    "accent":   "#0B8577",
    "on_acc":   "#FFFFFF",
    "text":     "#0F1B2A",
    "muted":    "#5A6B7D",
    "danger":   "#D32F2F",
    "danger_bg": "#FBE4E4",
    "warn":     "#B45309",
    "ok":       "#15803D",
    "white":    "#FFFFFF",
    "toggle_off": "#C3CDD9",
    "track":    "#CAD4E0",
    "menu":     "#FFFFFF",
    "loupe":    "#FFFFFF",
    "toast_info": "#26384A",
    "toast_ok":   "#14532D",
    "toast_error": "#7F1D1D",
}

C = dict(C_DARK)          # the colours in use. Changed IN PLACE by apply_theme()
IS_LIGHT = False


def detect_system_dark():
    """True when the phone is set to dark mode. If it cannot be read -> True (the original look)."""
    try:
        from jnius import autoclass
        act = autoclass("org.kivy.android.PythonActivity").mActivity
        ui = int(act.getResources().getConfiguration().uiMode)
        return (ui & 0x30) != 0x10            # UI_MODE_NIGHT_MASK = 0x30, NIGHT_NO = 0x10
    except Exception:
        return True


def resolve_theme(mode):
    """'light' | 'dark' | 'system'  ->  'light' | 'dark'"""
    if mode == "light":
        return "light"
    if mode == "dark":
        return "dark"
    return "dark" if detect_system_dark() else "light"


def apply_theme(mode):
    """Switch the colour table (in place, so every widget built afterwards uses it)."""
    global IS_LIGHT
    name = resolve_theme(mode)
    C.clear()
    C.update(C_LIGHT if name == "light" else C_DARK)
    IS_LIGHT = (name == "light")
    return name


def rgba(hex_color, alpha=1.0):
    h = hex_color.lstrip("#")
    return (int(h[0:2], 16) / 255.0, int(h[2:4], 16) / 255.0,
            int(h[4:6], 16) / 255.0, alpha)


# --------------------------------------------------------------------------
# Translations
# --------------------------------------------------------------------------
_S = [
    # key, arabic, english
    ("app_name", "عِدّة", "3edda"),
    ("tagline", "كل أدواتك في مكان واحد", "All your tools in one place"),
    ("search_hint", "دوّر على أداة…", "Search for a tool…"),
    ("popular", "الأدوات الشائعة", "Popular tools"),
    ("results", "نتائج البحث", "Search results"),
    ("no_results", "مفيش أداة بالاسم ده", "No tool matches your search"),
    ("tool_qr", "إنشاء QR", "Create QR"),
    ("tool_qr_sub", "أنشئ كودًا بسهولة", "Make a code easily"),
    ("tool_compress", "ضغط الصور", "Compress images"),
    ("tool_compress_sub", "وفّر مساحة", "Save space"),
    ("tool_pdf", "صور إلى PDF", "Images to PDF"),
    ("tool_pdf_sub", "اجمع مستنداتك", "Gather your documents"),
    ("tool_text", "أدوات النصوص", "Text tools"),
    ("tool_text_sub", "نظّم النص بسرعة", "Tidy text quickly"),
    ("tool_scan", "قارئ QR", "QR scanner"),
    ("tool_scan_sub", "امسح الكود بالكاميرا", "Scan codes with the camera"),
    ("privacy_title", "ملفاتك تفضل على جهازك", "Your files stay on your device"),
    ("privacy_sub", "نعالج الملفات محليًا قدر الإمكان، من غير رفعها لسيرفر.",
     "We process files locally whenever possible, without uploading them to a server."),
    ("nav_home", "الرئيسية", "Home"),
    ("nav_history", "السجل", "History"),
    ("nav_favorites", "المفضلة", "Favorites"),
    ("nav_settings", "الإعدادات", "Settings"),

    # common
    ("save", "حفظ", "Save"),
    ("share", "مشاركة", "Share"),
    ("copy", "نسخ", "Copy"),
    ("open", "فتح", "Open"),
    ("cancel", "إلغاء", "Cancel"),
    ("ok", "تمام", "OK"),
    ("close", "إغلاق", "Close"),
    ("error", "حصلت مشكلة", "Something went wrong"),
    ("saved_to", "تم الحفظ في {path}", "Saved to {path}"),
    ("copied", "تم النسخ", "Copied"),
    ("fav_added", "أُضيفت للمفضلة", "Added to favorites"),
    ("fav_removed", "أُزيلت من المفضلة", "Removed from favorites"),
    ("working", "جارٍ التنفيذ", "Working"),
    ("need_pil", "هذه الميزة غير متاحة على جهازك", "This feature is not available on your device"),
    ("need_qrlib", "إنشاء الكود غير متاح على جهازك", "Creating codes is not available on your device"),
    ("save_failed", "تعذّر الحفظ", "Could not save"),
    ("exit_again", "اضغط رجوع مرة تانية للخروج", "Press back again to exit"),
    ("share_failed", "المشاركة غير متاحة هنا، المسار: {path}", "Sharing is not available here, path: {path}"),
    ("open_failed", "تعذّر فتح الملف", "Could not open the file"),

    # settings
    ("language", "اللغة", "Language"),
    ("lang_ar_name", "العربية", "العربية"),
    ("lang_en_name", "English", "English"),
    ("sounds", "أصوات النقر", "Click sounds"),
    ("volume", "مستوى الصوت", "Volume"),
    ("vibration", "الاهتزاز عند اللمس", "Haptic feedback"),
    ("shaping", "إصلاح اتصال الحروف العربية", "Fix Arabic letter joining"),
    ("save_location", "أماكن الحفظ", "Save locations"),
    ("clear_history", "مسح السجل", "Clear history"),
    ("history_cleared", "تم مسح السجل", "History cleared"),
    ("about", "عن التطبيق", "About"),
    ("version", "الإصدار {v}", "Version {v}"),
    ("about_text", "عِدّة مجموعة أدوات يومية بتشتغل على جهازك من غير إنترنت.",
     "3edda is a set of everyday tools that work on your device, offline."),
    ("libs_status", "حالة المكتبات", "Library status"),
    ("installed", "مثبّتة", "installed"),
    ("missing", "غير مثبّتة", "missing"),

    # history / favorites
    ("history_empty", "لسه مفيش نشاط", "No activity yet"),
    ("fav_empty", "اضغط مطوّلًا على أي أداة، أو اضغط القلب جوّاها، لتظهر هنا.",
     "Long-press any tool, or tap the heart inside it, and it will show up here."),
    ("t_now", "الآن", "just now"),
    ("t_min", "من {n} د", "{n} min ago"),
    ("t_hour", "من {n} س", "{n} h ago"),
    ("t_day", "من {n} يوم", "{n} d ago"),

    # QR create
    ("qr_content", "المحتوى", "Content"),
    ("qr_hint", "اكتب رابطًا أو رقم هاتف أو نصًا", "Type a link, phone number or text"),
    ("qr_type", "النوع", "Type"),
    ("qr_auto", "تلقائي", "Auto"),
    ("qr_link", "رابط", "Link"),
    ("qr_phone", "هاتف", "Phone"),
    ("qr_text", "نص", "Text"),
    ("qr_color", "اللون", "Color"),
    ("qr_generate", "إنشاء الكود", "Generate code"),
    ("qr_empty", "اكتب شيئًا أولًا", "Type something first"),
    ("qr_placeholder", "الكود هيظهر هنا", "Your code will appear here"),
    ("qr_detected", "تم اعتباره: {kind}", "Treated as: {kind}"),
    ("qr_too_long", "المحتوى طويل جدًا لكود QR", "The content is too long for a QR code"),

    # compress
    ("cp_pick", "اختر صورة", "Choose an image"),
    ("cp_pick_sub", "JPG أو PNG أو WEBP", "JPG, PNG or WEBP"),
    ("cp_change", "تغيير الصورة", "Change image"),
    ("cp_quality", "الجودة", "Quality"),
    ("cp_scale", "الأبعاد", "Dimensions"),
    ("cp_format", "الصيغة", "Format"),
    ("cp_before", "قبل الضغط", "Before"),
    ("cp_after", "بعد الضغط", "After"),
    ("cp_saved_pct", "وفّرت {pct}٪ من الحجم", "Saved {pct}% of the size"),
    ("cp_bigger", "النسخة الجديدة أكبر من الأصلية. جرّب صيغة JPEG أو WEBP، أو صغّر الأبعاد.",
     "The new copy is larger than the original. Try JPEG or WEBP, or reduce the dimensions."),
    ("cp_save", "حفظ النسخة المضغوطة", "Save compressed copy"),
    ("cp_lossless", "صيغة PNG تحفظ الصورة كاملة بدون أي فقد في الجودة، ولهذا شريط الجودة لا يؤثر عليها. للتصغير اختر JPEG أو WEBP أو قلّل الأبعاد.",
     "PNG keeps every pixel (lossless), so the quality slider has no effect on it. To shrink the file choose JPEG or WEBP, or reduce the dimensions."),
    ("cp_no_image", "اختر صورة لتبدأ", "Choose an image to begin"),
    ("cp_open_fail", "تعذّر فتح الصورة", "Could not open this image"),
    ("cp_computing", "جارٍ الحساب", "Calculating"),

    # pdf
    ("pdf_add", "إضافة صور", "Add images"),
    ("pdf_pages", "{n} صفحة", "{n} pages"),
    ("pdf_size", "حجم الصفحة", "Page size"),
    ("pdf_orient", "الاتجاه", "Orientation"),
    ("pdf_auto", "تلقائي", "Auto"),
    ("pdf_portrait", "عمودي", "Portrait"),
    ("pdf_landscape", "أفقي", "Landscape"),
    ("pdf_margin", "الهوامش", "Margins"),
    ("pdf_none", "بدون", "None"),
    ("pdf_small", "صغيرة", "Small"),
    ("pdf_medium", "متوسطة", "Medium"),
    ("pdf_fit", "مطابق للصورة", "Fit image"),
    ("pdf_name", "اسم الملف", "File name"),
    ("pdf_create", "إنشاء PDF", "Create PDF"),
    ("pdf_empty", "أضف صورة واحدة على الأقل", "Add at least one image"),
    ("pdf_empty_hint", "اختر صورة واحدة أو أكثر، وبعدها رتّبها", "Pick one or more images, then reorder them"),
    ("pdf_done", "تم إنشاء الملف", "PDF created"),
    ("pdf_progress", "صفحة {i} من {n}", "Page {i} of {n}"),
    ("pdf_skipped", "تم تخطي {n} صورة لم تُفتح", "Skipped {n} image(s) that could not be opened"),

    # text tools
    ("tx_hint", "اكتب أو الصق النص هنا", "Type or paste your text here"),
    ("tx_words", "كلمات", "Words"),
    ("tx_chars", "حروف", "Letters"),
    ("tx_chars_ns", "بدون مسافات", "No spaces"),
    ("tx_digits", "أرقام", "Digits"),
    ("tx_symbols", "رموز", "Symbols"),
    ("tx_spaces_n", "مسافات", "Spaces"),
    ("tx_lines", "سطور", "Lines"),
    ("tx_dedupe", "إزالة المكرر", "Remove duplicates"),
    ("tx_spaces", "تنظيف المسافات", "Clean spaces"),
    ("tx_empty_lines", "حذف السطور الفارغة", "Remove empty lines"),
    ("tx_sort", "ترتيب السطور", "Sort lines"),
    ("tx_upper", "أحرف كبيرة", "UPPERCASE"),
    ("tx_lower", "أحرف صغيرة", "lowercase"),
    ("tx_tashkeel", "إزالة التشكيل", "Remove diacritics"),
    ("tx_copy", "نسخ النص", "Copy text"),
    ("tx_paste", "لصق", "Paste"),
    ("tx_clear", "مسح", "Clear"),
    ("tx_undo", "تراجع", "Undo"),
    ("tx_cut", "قص", "Cut"),
    ("tx_select_all", "تحديد الكل", "Select all"),
    ("tx_removed_n", "تم حذف {n} سطر مكرر", "Removed {n} duplicate line(s)"),
    ("tx_no_change", "مفيش تغيير", "Nothing changed"),
    ("tx_done", "تم", "Done"),
    ("tx_empty", "النص فاضي", "The text is empty"),

    # scanner
    ("sc_hint", "وجّه الكاميرا ناحية الكود", "Point the camera at a QR code"),
    ("sc_gallery", "من المعرض", "From gallery"),
    ("sc_photo", "التقاط صورة", "Take photo"),
    ("sc_rotate", "تدوير الكاميرا", "Rotate camera"),
    ("sc_capture", "تصوير", "Capture"),
    ("sc_found", "تم العثور على كود", "Code found"),
    ("sc_open_link", "فتح الرابط", "Open link"),
    ("sc_confirm_title", "تأكد قبل الفتح", "Check before opening"),
    ("sc_confirm_msg", "هتفتح الرابط ده:", "You are about to open:"),
    ("sc_domain", "النطاق", "Domain"),
    ("sc_warn_http", "الرابط غير مشفّر (HTTP)", "The link is not encrypted (HTTP)"),
    ("sc_warn_ip", "الرابط يشير إلى عنوان IP مباشر", "The link points to a raw IP address"),
    ("sc_warn_short", "رابط مختصر، الوجهة الحقيقية مخفية", "Shortened link, the real destination is hidden"),
    ("sc_warn_puny", "اسم النطاق فيه حروف قد تكون مموّهة", "The domain has characters that may be disguised"),
    ("sc_warn_at", "الرابط يحتوي علامة @ مشبوهة", "The link contains a suspicious @"),
    ("sc_warn_long", "رابط طويل بشكل غير معتاد", "Unusually long link"),
    ("sc_safe", "مفيش علامات مريبة واضحة، لكن ابقى حذرًا.", "No obvious red flags, but stay careful."),
    ("sc_blocked", "نوع الرابط ده غير آمن وتم منع فتحه.", "This link type is unsafe and opening it was blocked."),
    ("sc_scan_again", "مسح كود جديد", "Scan another"),
    ("sc_no_camera", "الكاميرا غير متاحة، استخدم «من المعرض».", "Camera unavailable, use “From gallery”."),
    ("sc_no_perm", "اسمح للتطبيق باستخدام الكاميرا من إعدادات الهاتف، أو استخدم «من المعرض».",
     "Allow camera access in the phone settings, or use “From gallery”."),
    ("sc_no_decoder", "قراءة الكود غير متاحة على جهازك", "Reading codes is not available on your device"),
    ("sc_not_found", "ماقدرتش ألاقي كود QR في الصورة", "No QR code found in the image"),
    ("sc_call", "اتصال", "Call"),
    ("sc_mail", "إرسال بريد", "Send email"),
    ("sc_map", "فتح الخريطة", "Open map"),
    ("sc_ssid", "اسم الشبكة", "Network name"),
    ("sc_pass", "كلمة المرور", "Password"),
    ("sc_security", "نوع الحماية", "Security"),
    ("sc_copy_pass", "نسخ كلمة المرور", "Copy password"),
    ("kind_url", "رابط", "Link"),
    ("kind_phone", "رقم هاتف", "Phone number"),
    ("kind_email", "بريد إلكتروني", "Email"),
    ("kind_sms", "رسالة SMS", "SMS"),
    ("kind_wifi", "شبكة Wi-Fi", "Wi-Fi network"),
    ("kind_geo", "موقع", "Location"),
    ("kind_contact", "جهة اتصال", "Contact"),
    ("kind_text", "نص", "Text"),

    # file picker
    ("pk_title", "اختر من الملفات", "Choose files"),
    ("pk_select", "تم ({n})", "Done ({n})"),
    ("pk_empty", "المجلد فاضي", "This folder is empty"),
    ("pk_denied", "مفيش صلاحية لفتح المجلد ده", "No permission to open this folder"),
    ("pk_internal", "التخزين", "Storage"),
    ("pk_pictures", "الصور", "Pictures"),
    ("pk_camera", "الكاميرا", "Camera"),
    ("pk_screenshots", "لقطات الشاشة", "Screenshots"),
    ("pk_selected_n", "{n} محددة", "{n} selected"),
    ("pk_download", "التنزيلات", "Downloads"),
    ("pk_more", "بيظهر أول {n} عنصر فقط", "Showing the first {n} items only"),

    # appearance
    ("theme", "المظهر", "Appearance"),
    ("theme_system", "مظهر النظام", "System theme"),
    ("theme_light", "نهاري", "Light"),
    ("theme_dark", "ليلي", "Dark"),

    # new PDF tools (common)
    ("tool_pdftools", "أدوات PDF", "PDF Tools"),
    ("tool_pdftools_sub", "صور، ضغط، دمج، تقسيم، تعديل", "Images, compress, merge, split, edit"),
    ("tool_pdfzip", "ضغط PDF", "Compress PDF"),
    ("tool_pdfzip_sub", "صغّر حجم الملف", "Shrink the file size"),
    ("tool_pdfmerge", "دمج PDF", "Merge PDF"),
    ("tool_pdfmerge_sub", "اجمع ملفات في ملف واحد", "Combine files into one"),
    ("need_pypdf", "الأداة دي محتاجة مكتبة pypdf. ثبّتها من Pip وجرّب تاني.",
     "This tool needs the pypdf library. Install it from Pip and try again."),
    ("pk_documents", "المستندات", "Documents"),
    ("pk_no_pdf", "مفيش ملفات PDF", "No PDF files found"),
    ("pk_search", "دوّر على ملف PDF…", "Search PDF files…"),
    ("pk_scanning", "جارٍ البحث عن ملفات PDF في الجهاز…", "Looking for PDF files on your device…"),
    ("pk_allow_hint", "عشان التطبيق يلاقي كل ملفات PDF في الجهاز لازم تسمح له بالوصول لكل الملفات.",
     "To find every PDF on your device, allow the app to access all files."),
    ("pk_allow_all", "السماح بالوصول لكل الملفات", "Allow access to all files"),
    ("pk_use_system", "اختيار من مدير الملفات", "Choose with the file manager"),
    ("pk_rescan", "إعادة البحث", "Search again"),
    ("pk_found_n", "{n} ملف PDF", "{n} PDF files"),
    ("nt_title_hint", "العنوان", "Title"),
    ("nt_rename_hint", "عدّل العنوان ثم اضغط «تحديث الملاحظة»", "Edit the title, then tap “Update note”"),
    ("nt_save", "حفظ كملاحظة", "Save as note"),
    ("nt_update", "تحديث الملاحظة", "Update note"),
    ("nt_my", "ملاحظاتي", "My notes"),
    ("nt_new", "ملاحظة جديدة", "New note"),
    ("nt_empty", "لسه مفيش ملاحظات.\nاكتب نص واضغط «حفظ كملاحظة».", "No notes yet.\nWrite some text and tap “Save as note”."),
    ("nt_none_found", "مفيش ملاحظة بالاسم ده", "No note matches"),
    ("nt_search", "دوّر في الملاحظات…", "Search notes…"),
    ("nt_hint", "اضغط على ملاحظة لفتحها، واضغط مطولًا لخيارات أكتر", "Tap a note to open it, long-press for more"),
    ("nt_name_q", "اسم الملاحظة", "Note name"),
    ("nt_saved", "تم حفظ الملاحظة", "Note saved"),
    ("nt_updated", "تم تحديث الملاحظة", "Note updated"),
    ("nt_opened", "اتفتحت: {title}", "Opened: {title}"),
    ("nt_delete_q", "حذف الملاحظة؟", "Delete this note?"),
    ("nt_delete_body", "هتتحذف الملاحظة:\n{name}", "This note will be deleted:\n{name}"),
    ("nt_deleted", "تم حذف الملاحظة", "Note deleted"),
    ("nt_export", "حفظ كملف نصي", "Save as text file"),
    ("nt_untitled", "ملاحظة بدون اسم", "Untitled note"),
    ("nt_count", "{n} ملاحظة", "{n} notes"),
    ("delete", "حذف", "Delete"),
    ("rename", "إعادة تسمية", "Rename"),
    ("pk_delete_q", "حذف الملف؟", "Delete this file?"),
    ("pk_delete_body", "هيتحذف نهائيًا من جهازك:\n{name}", "It will be deleted from your device:\n{name}"),
    ("pk_deleted", "تم حذف الملف", "File deleted"),
    ("pk_renamed", "تمت إعادة التسمية", "Renamed"),
    ("pk_name_exists", "فيه ملف بنفس الاسم", "A file with this name already exists"),
    ("pk_action_failed", "تعذّر تنفيذ العملية على الملف", "Could not do this to the file"),
    ("pdf_enc", "الملف ده محمي بكلمة سر", "This file is password-protected"),
    ("pdf_bad", "تعذّر فتح الملف، ممكن يكون تالف", "Could not open the file, it may be damaged"),
    ("pdf_enc_s", "محمي بكلمة سر", "Password-protected"),
    ("pdf_bad_s", "ملف تالف", "Damaged file"),

    # compress PDF
    ("pdfz_pick", "اختر ملف PDF", "Choose a PDF file"),
    ("pdfz_change", "تغيير الملف", "Change file"),
    ("pdfz_none", "اختر ملف PDF لتبدأ", "Choose a PDF to begin"),
    ("pdfz_level", "درجة الضغط", "Compression level"),
    ("pdfz_low", "خفيف", "Light"),
    ("pdfz_med", "متوسط", "Medium"),
    ("pdfz_high", "قوي", "Strong"),
    ("pdfz_low_hint", "جودة صور عالية، وتوفير أقل في الحجم.", "High image quality, smaller saving."),
    ("pdfz_med_hint", "توازن كويس بين الجودة والحجم.", "A good balance of quality and size."),
    ("pdfz_high_hint", "أصغر حجم ممكن، وجودة الصور بتقل شوية.", "Smallest size, images lose a bit of quality."),
    ("pdfz_note", "الضغط بيصغّر الصور اللي جوّا الملف. الملفات اللي كلها نص مش هتصغر كتير.",
     "Compression shrinks the pictures inside the file. Text-only files will not shrink much."),
    ("pdfz_run", "ضغط الملف", "Compress file"),
    ("pdfz_done", "تم ضغط الملف", "File compressed"),
    ("pdfz_est_now", "الحجم الحالي", "Current size"),
    ("pdfz_est_after", "بعد الضغط", "After compressing"),
    ("pdfz_est_calc", "جارٍ حساب الحجم…", "Calculating the size…"),
    ("pdfz_no_gain", "الملف ده متضغط بالفعل ومفيش مساحة تتوفر. جرّب درجة أقوى.",
     "This file is already well compressed. Try a stronger level."),

    # merge PDF
    ("pdfm_add", "إضافة ملفات PDF", "Add PDF files"),
    ("pdfm_count", "{n} ملف · {p} صفحة", "{n} files · {p} pages"),
    ("pdfm_count_n", "{n} ملف", "{n} files"),
    ("pdfm_files_lbl", "عدد الملفات", "Files"),
    ("pdfm_pages_lbl", "عدد الصفحات", "Pages"),
    ("pdfm_hint", "اختر ملفين أو أكتر، وبعدها رتّبهم", "Pick two or more files, then put them in order"),
    ("pdfm_order", "الملف اللي فوق هيبقى أول الصفحات، رتّبهم بالأسهم.",
     "The file on top comes first. Use the arrows to reorder."),
    ("pdfm_need2", "أضف ملفين على الأقل", "Add at least two files"),
    ("pdfm_run", "دمج الملفات", "Merge files"),
    ("pdfm_done", "تم دمج الملفات", "Files merged"),
    ("pdfm_progress", "ملف {i} من {n}", "File {i} of {n}"),
    ("pdfm_skipped", "تم تخطي {n} ملف تعذّر فتحه", "Skipped {n} file(s) that could not be opened"),

    # split PDF (remove pages)
    ("tool_pdfsplit", "تقسيم PDF", "Split PDF"),
    ("tool_pdfsplit_sub", "احذف صفحات من الملف", "Remove pages from a file"),
    ("sp_hint", "اضغط على الصفحات اللي عايز تحذفها، وهيتعمل ملف جديد بالصفحات اللي فضلت.",
     "Tap the pages you want to remove. A new file is made from the pages that are left."),
    ("sp_marked", "الصفحات المحددة للحذف: {n} من {total}", "Pages marked for removal: {n} of {total}"),
    ("sp_all", "تحديد الكل", "Select all"),
    ("sp_none", "إلغاء التحديد", "Clear"),
    ("sp_invert", "عكس التحديد", "Invert"),
    ("sp_run", "إنشاء الملف الجديد", "Create the new file"),
    ("sp_need_mark", "حدد صفحة واحدة على الأقل للحذف", "Mark at least one page to remove"),
    ("sp_need_keep", "لازم تسيب صفحة واحدة على الأقل", "At least one page must stay"),
    ("sp_save_q", "حفظ الملف الجديد", "Save the new file"),
    ("sp_save_body", "هيتحذف {n} صفحة وهيفضل {m} صفحة.\nتحب تحفظه إزاي؟",
     "{n} page(s) will be removed and {m} will stay.\nHow do you want to save it?"),
    ("sp_copy", "حفظ كنسخة", "Save a copy"),
    ("sp_replace", "حفظ وحذف الأصلي", "Save and delete the original"),
    ("sp_done", "تم إنشاء الملف الجديد", "New file created"),
    ("sp_before", "عدد الصفحات قبل", "Pages before"),
    ("sp_removed", "الصفحات المحذوفة", "Pages removed"),
    ("sp_after", "عدد الصفحات بعد", "Pages after"),
    ("sp_orig_deleted", "تم حذف الملف الأصلي", "The original file was deleted"),
    ("sp_orig_failed", "تم الحفظ، لكن تعذّر حذف الملف الأصلي", "Saved, but the original file could not be deleted"),
    ("sp_orig_cache", "تم الحفظ. الملف الأصلي اتاخد من مدير الملفات فمينفعش نحذفه من هنا، احذفه بنفسك لو عايز.",
     "Saved. The original was chosen with the file manager, so it cannot be deleted from here."),

    # edit PDF
    ("tool_pdfedit", "تعديل PDF", "Edit PDF"),
    ("tool_pdfedit_sub", "ارسم واكتب وضيف صور", "Draw, write, add images"),
    ("pe_intro", "افتح ملف PDF وميّز النص أو حط تحته خط أو اشطبه، وارسم بأقلام وألوان، واكتب نصوص، وضيف صور، وبدّل أي نص قديم.",
     "Open a PDF, highlight / underline / strike its text, draw with pens and any colour, write text, add images and replace old text."),
    ("pe_note", "الصفحات اللي بتعدلها بتتحفظ كصورة عالية الجودة (النص جواها مبقاش قابل للتحديد)، والصفحات اللي ماتلمستش بتفضل زي ما هي.",
     "Pages you change are saved as a high-quality picture (their text can no longer be selected). Pages you do not touch stay exactly as they are."),
    ("pe_open", "فتح المحرر", "Open the editor"),
    ("pe_t_select", "تحديد", "Select"),
    ("pe_t_pen", "قلم", "Pen"),
    ("pe_t_eraser", "ممحاة", "Eraser"),
    ("pe_t_text", "نص", "Text"),
    ("pe_t_image", "صورة", "Image"),
    ("pe_t_edit", "تعديل نص", "Edit text"),
    ("pe_t_mark", "تمييز", "Mark text"),
    ("pe_mk_hl", "تمييز", "Highlight"),
    ("pe_mk_ul", "خط تحت", "Underline"),
    ("pe_mk_st", "شطب", "Strike out"),
    ("pe_hint_mark", "اسحب بإصبعك على سطر النص، أو اضغط على كلمة. الخط بيتظبط على النص لوحده.",
     "Swipe along a line of text, or tap a word. The mark fits the text by itself."),
    ("pe_no_text", "مفيش نص هنا، اضغط أو اسحب على النص نفسه", "No text here, tap or swipe on the text itself"),
    ("pe_pen_pen", "قلم", "Pen"),
    ("pe_pen_ball", "جاف", "Ballpoint"),
    ("pe_pen_pencil", "رصاص", "Pencil"),
    ("pe_pen_marker", "هايلايتر", "Highlighter"),
    ("pe_size", "الحجم", "Size"),
    ("pe_color_title", "اختر لون", "Pick a colour"),
    ("pe_hint_select", "اضغط على أي عنصر لتحديده وتحريكه، واسحب الدايرة اللي في الركن لتغيير حجمه. اسحب بإصبعين للتكبير.",
     "Tap an item to select and move it, drag the corner dot to resize it. Use two fingers to zoom."),
    ("pe_hint_text", "اضغط على + عشان يظهر مربع كتابة في نص الشاشة، اكتب فيه، وبعدها حرّكه بإصبعك وكبّره أو صغّره من الدايرة اللي في الركن.",
     "Tap + to put a writing box in the middle of the screen. Type in it, drag it around and resize it with the dot in its corner."),
    ("pe_add_text", "إضافة مربع نص", "Add a text box"),
    ("pe_hint_image", "اختر صورة وهتتضاف على الصفحة، وبعدها حركها وغيّر حجمها.",
     "Choose a picture, it is added to the page, then move and resize it."),
    ("pe_hint_edit", "اضغط على الكلمة أو اسحب على السطر اللي عايز تعدّله أو تحذفه.",
     "Tap a word or swipe along the line you want to change or delete."),
    ("pe_hint_edit2", "اتحدد النص. اختار تحرير أو حذف، أو اضغط على كلمة تانية.",
     "The text is selected. Choose edit or delete, or tap another word."),
    ("pe_edit_do", "تحرير النص", "Edit text"),
    ("pe_delete_text", "حذف النص", "Delete text"),
    ("pe_add_image", "اختيار صورة", "Choose an image"),
    ("pe_edit_text", "تعديل النص", "Edit text"),
    ("pe_clear_page", "مسح كل الرسم في الصفحة", "Clear all drawing on this page"),
    ("pe_text_title", "اكتب النص", "Write the text"),
    ("pe_text_hint", "اكتب هنا", "Type here"),
    ("pe_old_title", "تحرير النص", "Edit the text"),
    ("pe_old_body", "اكتب النص الجديد، وهيتحط مكان النص المحدد بنفس الحجم والسُّمك.", "Type the new text, it replaces the selected text at the same size and weight."),
    ("pe_page", "صفحة {i} / {n}", "Page {i} / {n}"),
    ("pe_unsupported", "المحرر بيشتغل على أندرويد بس", "The editor works on Android only"),
    ("pe_nochange", "مفيش تعديلات تتحفظ", "There are no changes to save"),
    ("pe_save_q", "حفظ الملف المعدّل", "Save the edited file"),
    ("pe_save_body", "هيتم حفظ {n} صفحة معدّلة.\nتحب تحفظه إزاي؟", "{n} edited page(s) will be saved.\nHow do you want to save it?"),
    ("pe_discard_q", "تجاهل التعديلات؟", "Discard the changes?"),
    ("pe_discard_body", "فيه تعديلات لسه ما اتحفظتش، وهتضيع لو خرجت.", "Some changes are not saved and will be lost if you leave."),
    ("pe_discard", "تجاهل", "Discard"),
    ("pe_keep_editing", "كمّل تعديل", "Keep editing"),
    ("pe_exporting", "جارٍ تجهيز صفحة {i} من {n}", "Preparing page {i} of {n}"),
    ("pe_done", "تم حفظ الملف المعدّل", "Edited file saved"),
    ("pe_pages_edited", "الصفحات المعدّلة", "Edited pages"),
    ("pe_image_failed", "تعذّر فتح الصورة", "Could not open the picture"),
]

STRINGS = {"ar": {}, "en": {}}
for _k, _a, _e in _S:
    STRINGS["ar"][_k] = _a
    STRINGS["en"][_k] = _e


class I18N:
    lang = "ar"


def T(key, **fmt):
    s = STRINGS.get(I18N.lang, {}).get(key) or STRINGS["en"].get(key) or key
    if fmt:
        try:
            s = s.format(**fmt)
        except Exception:
            pass
    return s


def tr_both(key):
    """Both languages joined (used for search matching)."""
    return STRINGS["ar"].get(key, "") + " " + STRINGS["en"].get(key, "")


# --------------------------------------------------------------------------
# Arabic helpers
# --------------------------------------------------------------------------
AR_CHARS = "\u0600-\u06FF\u0750-\u077F\u08A0-\u08FF\uFB50-\uFDFF\uFE70-\uFEFF"
AR_RE = re.compile("[" + AR_CHARS + "]")
AR_RUN_RE = re.compile("[" + AR_CHARS + "]+(?:[ \u00a0]+[" + AR_CHARS + "]+)*")
LATIN_RUN_RE = re.compile(
    r"[A-Za-z0-9][A-Za-z0-9._:/\\@#%+=&?~\-]*(?: [A-Za-z0-9][A-Za-z0-9._:/\\@#%+=&?~\-]*)*")
TASHKEEL_RE = re.compile("[\u0610-\u061A\u064B-\u065F\u0670\u06D6-\u06DC\u06DF-\u06E4\u06E7\u06E8\u06EA-\u06ED\u0640]")


def has_arabic(s):
    return bool(AR_RE.search(s or ""))


def shape_line(line):
    """Connect Arabic letters and reorder for left-to-right drawing."""
    if not HAS_SHAPER or not has_arabic(line):
        return line
    try:
        if _RESHAPER is not None:
            return _get_display(_RESHAPER.reshape(line))
        return _get_display(_ar_reshaper.reshape(line))
    except Exception:
        return line


def escape_markup(s):
    return s.replace("&", "&amp;").replace("[", "&bl;").replace("]", "&br;")


def norm_search(s):
    s = TASHKEEL_RE.sub("", (s or "").lower())
    for a, b in (("أ", "ا"), ("إ", "ا"), ("آ", "ا"), ("ى", "ي"), ("ة", "ه")):
        s = s.replace(a, b)
    return s


# --------------------------------------------------------------------------
# Small utilities
# --------------------------------------------------------------------------
def human_size(n):
    try:
        n = float(n)
    except Exception:
        return "-"
    for unit in ("B", "KB", "MB", "GB"):
        if n < 1024 or unit == "GB":
            if unit == "B":
                return "%d B" % n
            return ("%.1f %s" % (n, unit)).replace(".0 ", " ")
        n /= 1024.0
    return "-"


def now_stamp():
    return datetime.datetime.now().strftime("%Y%m%d_%H%M%S")


def safe_name(name, default="file"):
    name = re.sub(r'[\\/:*?"<>|\r\n\t]+', "_", (name or "").strip())
    name = name.strip(" .")
    return name[:80] or default


def unique_path(folder, base, ext):
    base = safe_name(base)
    p = os.path.join(folder, base + ext)
    i = 1
    while os.path.exists(p):
        p = os.path.join(folder, "%s_%d%s" % (base, i, ext))
        i += 1
    return p


def storage_root():
    for p in ("/storage/emulated/0", "/sdcard"):
        if os.path.isdir(p):
            return p
    return os.path.expanduser("~")


def out_dir(kind, fallback_dir):
    """Everything the app saves (QR images, compressed images, PDFs) goes to one folder: 3edda."""
    for base in (storage_root(), os.path.expanduser("~")):
        p = os.path.join(base, "3edda")
        try:
            os.makedirs(p, exist_ok=True)
            if os.access(p, os.W_OK):
                return p
        except Exception:
            pass
    p = os.path.join(fallback_dir, "3edda")
    os.makedirs(p, exist_ok=True)
    return p


def tmp_dir():
    p = os.path.join(APP.user_data_dir, "tmp")
    os.makedirs(p, exist_ok=True)
    return p


def clean_tmp():
    """Delete leftovers of earlier sessions (called once at start)."""
    import shutil
    for sub in ("tmp", "picked"):
        try:
            shutil.rmtree(os.path.join(APP.user_data_dir, sub), ignore_errors=True)
        except Exception:
            pass


def _sdk_int():
    try:
        from jnius import autoclass
        return int(autoclass("android.os.Build$VERSION").SDK_INT)
    except Exception:
        return 0


SAVE_FOLDER = "عِدّة_3edda"           # the one folder everything the app saves goes into


def _ms_write(src, name, mime, base_uri, rel):
    """Create one entry in the MediaStore (folder `rel`) and copy `src` into it. -> content uri (str)."""
    import shutil
    from jnius import autoclass
    cr = _android_activity().getContentResolver()
    String = autoclass("java.lang.String")
    cv = autoclass("android.content.ContentValues")()
    cv.put(String("_display_name"), String(name))
    cv.put(String("mime_type"), String(mime))
    cv.put(String("relative_path"), String(rel))
    uri = cr.insert(base_uri, cv)
    if uri is None:
        raise IOError("insert returned nothing")
    try:
        pfd = cr.openFileDescriptor(uri, "w")
        try:
            fd = pfd.detachFd()
        except Exception:
            fd = os.dup(pfd.getFd())
            pfd.close()
        with open(src, "rb") as a, os.fdopen(fd, "wb") as b:
            shutil.copyfileobj(a, b, 1 << 20)
    except Exception:
        try:
            cr.delete(uri, None, None)             # do not leave an empty entry behind
        except Exception:
            pass
        raise
    return uri.toString()


def published_alive(res):
    """Is a file saved earlier by publish_file() still there? (The user may have deleted it.)"""
    try:
        shown, uri, local = res
        if uri:
            from jnius import autoclass
            cr = _android_activity().getContentResolver()
            pfd = cr.openFileDescriptor(autoclass("android.net.Uri").parse(uri), "r")
            pfd.close()
            return True
        return os.path.isfile(local)
    except Exception:
        return False


def publish_file(src, name, mime, kind, fallback_dir):
    """Put a finished file in the folder SAVE_FOLDER where the user can see it (Files app / Gallery).
    Returns (text_to_show, content_uri_or_None, local_path_to_share). Raises IOError if nothing worked.
    Android 10+ does not allow writing into shared folders by path, so the MediaStore is used first."""
    import shutil
    errors = []
    base_name, ext = os.path.splitext(name)
    alt_name = "%s_%s%s" % (base_name, now_stamp(), ext)

    def note(tag, e):
        errors.append("%s: %s" % (tag, str(e)[:60]))
        try:
            APP.log_error(e)
        except Exception:
            pass

    if platform == "android" and _sdk_int() >= 29:
        from jnius import autoclass
        String = autoclass("java.lang.String")
        tiers = [
            ("downloads", lambda: autoclass("android.provider.MediaStore$Downloads").EXTERNAL_CONTENT_URI,
             "Download/" + SAVE_FOLDER),
            ("files", lambda: autoclass("android.provider.MediaStore$Files").getContentUri(String("external")),
             "Documents/" + SAVE_FOLDER),
        ]
        if kind == "image":
            tiers.append(("images", lambda: autoclass("android.provider.MediaStore$Images$Media").EXTERNAL_CONTENT_URI,
                          "Pictures/" + SAVE_FOLDER))
        for tag, base, rel in tiers:
            for nm in (name, alt_name):
                try:
                    uri = _ms_write(src, nm, mime, base(), rel)
                    return "%s/%s" % (rel, nm), uri, src
                except Exception as e:
                    note(tag, e)
    # older Android, desktop, or Pydroid: a normal folder
    root = storage_root()
    bases = []
    if os.path.isdir(os.path.join(root, "Download")):
        bases.append(os.path.join(root, "Download"))
    bases += [root, os.path.expanduser("~")]
    for base in bases:
        try:
            folder = os.path.join(base, SAVE_FOLDER)
            os.makedirs(folder, exist_ok=True)
            dest = unique_path(folder, base_name, ext)
            shutil.copyfile(src, dest)
            media_scan(dest)
            return dest, None, dest
        except Exception as e:
            note("path", e)
    raise IOError(" | ".join(errors) or "no folder could be written")


def rel_time(ts):
    d = max(0, int(time.time() - ts))
    if d < 60:
        return T("t_now")
    if d < 3600:
        return T("t_min", n=d // 60)
    if d < 86400:
        return T("t_hour", n=d // 3600)
    return T("t_day", n=d // 86400)


class Store:
    """Tiny JSON settings + history file."""
    DEFAULTS = {
        "lang": "ar",
        "sound": True,
        "volume": 0.6,
        "vibrate": True,
        "shape": True,
        "favorites": [],
        "history": [],
        "last_dir": "",
        "last_pdf_dir": "",
        "theme": "system",
        "cam_rot": 0,
        "cam_rot2": -1,
        "font_try": 0,
        "font_fail": "",
        "pdfe_colors": [],
    }

    def __init__(self, folder):
        self.path = os.path.join(folder, "idda_state.json")
        self.data = copy.deepcopy(self.DEFAULTS)
        try:
            with open(self.path, "r", encoding="utf-8") as f:
                loaded = json.load(f)
            if isinstance(loaded, dict):
                self.data.update(loaded)
        except Exception:
            pass

    def get(self, k, default=None):
        return self.data.get(k, self.DEFAULTS.get(k, default))

    def set(self, k, v, save=True):
        self.data[k] = v
        if save:
            self.save()

    def save(self):
        try:
            tmp = self.path + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(self.data, f, ensure_ascii=False)
            os.replace(tmp, self.path)
        except Exception:
            pass


# --------------------------------------------------------------------------
# Fonts: ONE font for the whole UI (chosen by what glyphs it REALLY contains)
# --------------------------------------------------------------------------
import hashlib
try:
    import fontTools.ttLib as _ft_ttlib            # noqa: F401
    HAS_FT = True
except Exception:
    HAS_FT = False

NEED_AR = set(range(0xFE80, 0xFEFD))              # Arabic presentation forms-B
NEED_LATIN = set(ord(c) for c in "AZaz09.:/-@")
_PREF = ["cairo", "tajawal", "almarai", "ibmplex", "notosansarabic", "notonaskh",
         "dejavusans", "segoeui", "tahoma", "droid"]
_SKIP = ("bold", "italic", "oblique", "light", "thin", "black", "medium", "semibold", "extra",
         "emoji", "symbol", "math", "mono", "condensed", "demi", "heavy", "ui-", "cjk")
_FB_SKIP = ("bold", "italic", "oblique", "light", "thin", "black", "medium", "semibold", "extra",
            "condensed", "demi", "heavy", "ui-", "cjk", "mono", "serif", "color", "cbdt")
_SYSTEM_NAMES = ["NotoNaskhArabic-Regular.ttf", "NotoSansArabic-Regular.ttf",
                 "NotoNaskhArabicUI-Regular.ttf", "NotoSansArabicUI-Regular.ttf",
                 "DroidNaskh-Regular.ttf", "DroidSansArabic.ttf", "DejaVuSans.ttf",
                 "segoeui.ttf", "tahoma.ttf"]
_SYSTEM_FALLBACKS = ["NotoSansSymbols-Regular-Subsetted.ttf", "NotoSansSymbols-Regular-Subsetted2.ttf",
                     "NotoSansSymbols2-Regular.ttf", "NotoSansMath-Regular.ttf"]
_CMAP_CACHE = {}
_CMAP_DISK = {"file": "", "data": {}, "dirty": False}


def _enc_ranges(cps):
    out, start, prev = [], None, None
    for c in sorted(cps):
        if start is None:
            start = prev = c
        elif c == prev + 1:
            prev = c
        else:
            out.append([start, prev])
            start = prev = c
    if start is not None:
        out.append([start, prev])
    return out


def _dec_ranges(rs):
    cps = set()
    for a, b in rs:
        cps.update(range(a, b + 1))
    return cps


def cmap_cache_load(folder):
    _CMAP_DISK["file"] = os.path.join(folder, "idda_cmap_cache.json")
    try:
        with open(_CMAP_DISK["file"], "r", encoding="utf-8") as f:
            d = json.load(f)
        if isinstance(d, dict):
            _CMAP_DISK["data"] = d
    except Exception:
        _CMAP_DISK["data"] = {}


def cmap_cache_save():
    if not _CMAP_DISK["dirty"] or not _CMAP_DISK["file"]:
        return
    try:
        os.makedirs(os.path.dirname(_CMAP_DISK["file"]), exist_ok=True)
        with open(_CMAP_DISK["file"], "w", encoding="utf-8") as f:
            json.dump(_CMAP_DISK["data"], f)
        _CMAP_DISK["dirty"] = False
    except Exception:
        pass


def _file_key(path):
    try:
        st = os.stat(path)
        return "%s|%d|%d" % (path, st.st_size, int(st.st_mtime))
    except Exception:
        return path


def _ttf_cmap_parse(path):
    """Set of BMP code points a TrueType/OpenType font has glyphs for."""
    cps = set()
    try:
        with open(path, "rb") as f:
            d = f.read()
        off = 0
        if d[:4] == b"ttcf":
            off = struct.unpack_from(">I", d, 12)[0]
        num = struct.unpack_from(">H", d, off + 4)[0]
        cmap = None
        for i in range(num):
            tag, _cs, o, _l = struct.unpack_from(">4sIII", d, off + 12 + 16 * i)
            if tag == b"cmap":
                cmap = o
                break
        if cmap is not None:
            n = struct.unpack_from(">H", d, cmap + 2)[0]
            for i in range(n):
                pid, eid, so = struct.unpack_from(">HHI", d, cmap + 4 + 8 * i)
                if pid not in (0, 3):
                    continue
                so += cmap
                fmt = struct.unpack_from(">H", d, so)[0]
                if fmt == 4:
                    segx2 = struct.unpack_from(">H", d, so + 6)[0]
                    seg = segx2 // 2
                    ends = so + 14
                    starts = ends + segx2 + 2
                    deltas = starts + segx2
                    ranges = deltas + segx2
                    for k in range(seg):
                        e = struct.unpack_from(">H", d, ends + 2 * k)[0]
                        st = struct.unpack_from(">H", d, starts + 2 * k)[0]
                        dl = struct.unpack_from(">h", d, deltas + 2 * k)[0]
                        ro = struct.unpack_from(">H", d, ranges + 2 * k)[0]
                        for c in range(st, e + 1):
                            if c == 0xFFFF:
                                continue
                            if ro == 0:
                                gid = (c + dl) & 0xFFFF
                            else:
                                a = ranges + 2 * k + ro + 2 * (c - st)
                                gid = struct.unpack_from(">H", d, a)[0] if a + 2 <= len(d) else 0
                                if gid:
                                    gid = (gid + dl) & 0xFFFF
                            if gid:
                                cps.add(c)
                elif fmt == 12:
                    ng = struct.unpack_from(">I", d, so + 12)[0]
                    for k in range(ng):
                        st, e, _g = struct.unpack_from(">III", d, so + 16 + 12 * k)
                        for c in range(st, min(e, 0xFFFF) + 1):
                            cps.add(c)
    except Exception:
        pass
    return cps



def ttf_cmap(path):
    """Set of code points a TrueType font can draw (cached in memory and on disk)."""
    if path in _CMAP_CACHE:
        return _CMAP_CACHE[path]
    key = _file_key(path)
    rs = _CMAP_DISK["data"].get(key)
    if rs is not None:
        cps = _dec_ranges(rs)
    else:
        cps = _ttf_cmap_parse(path)
        if cps:
            _CMAP_DISK["data"][key] = _enc_ranges(cps)
            _CMAP_DISK["dirty"] = True
    _CMAP_CACHE[path] = cps
    return cps


def _pref_idx(path):
    low = os.path.basename(path).lower()
    for i, k in enumerate(_PREF):
        if k in low:
            return i
    return 99


def _bold_partner(path):
    d, fn = os.path.split(path)
    base, ext = os.path.splitext(fn)
    cands = []
    if "Regular" in base:
        cands.append(base.replace("Regular", "Bold"))
    cands += [base + "-Bold", base + "Bold", base + "b", base + "bd"]
    for c in cands:
        p = os.path.join(d, c + ext)
        if os.path.isfile(p):
            return p
    return None


def find_fonts(app_dirs):
    """Choose the best main font (+bold) and the list of helper fonts.
    Returns dict(reg, bold, universal, cover, fallbacks, name)."""
    files, allfiles, seen = [], [], set()
    for dr in app_dirs:
        try:
            for fn in sorted(os.listdir(dr)):
                low = fn.lower()
                if low.endswith((".ttf", ".otf")):
                    p = os.path.join(dr, fn)
                    if p in seen:
                        continue
                    seen.add(p)
                    allfiles.append(p)
                    if not any(k in low for k in _SKIP):
                        files.append(p)
        except Exception:
            continue
    for dr in _system_font_dirs():
        for fn in _SYSTEM_NAMES:
            p = os.path.join(dr, fn)
            if os.path.isfile(p) and p not in seen:
                seen.add(p)
                files.append(p)
                allfiles.append(p)
        for fn in _SYSTEM_FALLBACKS:
            p = os.path.join(dr, fn)
            if os.path.isfile(p) and p not in seen:
                seen.add(p)
                allfiles.append(p)
    best = None
    for p in files:
        cov = ttf_cmap(p)
        if not cov:
            continue
        miss = len(NEED_AR - cov)
        latin = NEED_LATIN <= cov
        good = miss <= 3                                   # a few rare forms can be borrowed
        key = (0 if good else 1, 0 if good else miss, 0 if latin else 1, _pref_idx(p))
        if best is None or key < best[0]:
            best = (key, p, cov, latin, good)
    if best is None:
        return {"reg": None, "bold": None, "universal": False, "cover": None,
                "fallbacks": [], "name": ""}
    _k, reg, cov, latin, good = best
    bold = reg
    bp = _bold_partner(reg)
    if bp:
        bcov = ttf_cmap(bp)
        if bcov and len(NEED_AR - bcov) <= 3:
            bold = bp
    fallbacks, taken = [], {os.path.basename(reg).lower(), os.path.basename(bold).lower()}
    for key in _FALLBACK_NAMES:
        for p in allfiles:
            low = os.path.basename(p).lower()
            if key in low and low not in taken and not any(k in low for k in _FB_SKIP):
                taken.add(low)
                fallbacks.append(p)
    return {"reg": reg, "bold": bold, "universal": bool(latin and good), "cover": cov,
            "fallbacks": fallbacks, "name": os.path.basename(reg)}


def _system_font_dirs():
    dirs = ["/system/fonts", "/system/font", "/usr/share/fonts/truetype/dejavu",
            "/usr/share/fonts/dejavu", "/usr/share/fonts/TTF",
            "C:/Windows/Fonts", "/Library/Fonts", "/System/Library/Fonts/Supplemental"]
    try:
        import matplotlib
        dirs.append(os.path.join(os.path.dirname(matplotlib.__file__), "mpl-data", "fonts", "ttf"))
    except Exception:
        pass
    return dirs


_FALLBACK_NAMES = ("notosansarabic", "notonaskh", "dejavusans", "notosanssymbols2",
                   "notosanssymbols", "notosansmath", "notoemoji")
_COPY_RANGES = (
    (0x0020, 0x024F), (0x02B0, 0x02FF), (0x0600, 0x06FF), (0x0750, 0x077F), (0x08A0, 0x08FF),
    (0x2000, 0x2BFF), (0x3000, 0x303F), (0xFB50, 0xFDFF), (0xFE70, 0xFEFF), (0xFF01, 0xFF5E),
    (0x1F300, 0x1FAFF),
)
_FT_DROP = ("fvar", "gvar", "HVAR", "VVAR", "MVAR", "avar", "cvar", "STAT", "GSUB", "GPOS", "GDEF",
            "kern", "DSIG", "hdmx", "LTSH", "VDMX", "PCLT", "meta", "BASE", "JSTF", "MATH", "morx",
            "feat", "prop", "trak", "cvt ", "fpgm", "prep", "gasp")


def _want_cp(cp):
    for a, b in _COPY_RANGES:
        if a <= cp <= b:
            return True
    return False


def build_ui_font(primary, fallbacks, out_path, progress=None):
    """Copy glyphs the primary font lacks from `fallbacks` (list of paths, in priority
    order). Returns the set of code points the new font can draw, or None on failure."""
    try:
        from fontTools.ttLib import TTFont
        from fontTools.pens.ttGlyphPen import TTGlyphPen
        from fontTools.pens.transformPen import TransformPen
        from fontTools.pens.recordingPen import DecomposingRecordingPen
    except Exception:
        return None
    try:
        dst = TTFont(primary, lazy=False)
        if "glyf" not in dst:
            return None
        upem = dst["head"].unitsPerEm
        for t in _FT_DROP:
            if t in dst:
                del dst[t]
        order = list(dst.getGlyphOrder())
        have = set(dst.getBestCmap().keys())
        glyf, hmtx = dst["glyf"], dst["hmtx"]
        added = {}
        used_names = set(order)
        for fb in fallbacks:
            try:
                src = TTFont(fb, lazy=True)
                if "glyf" not in src:
                    continue
                cmap = src.getBestCmap() or {}
                todo = [(cp, nm) for cp, nm in cmap.items()
                        if cp not in have and cp not in added and _want_cp(cp)]
                if not todo:
                    continue
                k = float(upem) / src["head"].unitsPerEm
                gs = src.getGlyphSet()
                shmtx = src["hmtx"]
                made = {}                                    # source glyph name -> new name
                for cp, nm in todo:
                    if nm in made:
                        added[cp] = made[nm]
                        continue
                    try:
                        rec = DecomposingRecordingPen(gs)
                        gs[nm].draw(rec)
                        pen = TTGlyphPen(None)
                        rec.replay(TransformPen(pen, (k, 0, 0, k, 0, 0)))
                        g = pen.glyph()
                        adv = int(round(shmtx[nm][0] * k))
                    except Exception:
                        continue
                    new = "idda%X" % cp
                    while new in used_names:
                        new += "_"
                    used_names.add(new)
                    glyf.glyphs[new] = g
                    order.append(new)
                    try:
                        g.recalcBounds(glyf)
                        lsb = getattr(g, "xMin", 0) if g.numberOfContours else 0
                    except Exception:
                        lsb = 0
                    hmtx.metrics[new] = (adv, lsb)
                    made[nm] = new
                    added[cp] = new
                src.close()
            except Exception:
                continue
        if not added:
            dst.save(out_path)
            return set(have)
        dst.setGlyphOrder(order)
        glyf.glyphOrder = order
        # unicode cmaps
        need12 = any(cp > 0xFFFF for cp in added)
        for st in dst["cmap"].tables:
            if not st.isUnicode():
                continue
            if st.format == 4:
                for cp, nm in added.items():
                    if cp <= 0xFFFF:
                        st.cmap[cp] = nm
            elif st.format == 12:
                for cp, nm in added.items():
                    st.cmap[cp] = nm
        if need12 and not any(st.format == 12 for st in dst["cmap"].tables):
            from fontTools.ttLib.tables._c_m_a_p import CmapSubtable
            st = CmapSubtable.newSubtable(12)
            st.platformID, st.platEncID, st.language = 3, 10, 0
            st.cmap = {cp: nm for cp, nm in dst.getBestCmap().items()}
            for cp, nm in added.items():
                st.cmap[cp] = nm
            dst["cmap"].tables.append(st)
        if "post" in dst:
            dst["post"].formatType = 3.0
            dst["post"].extraNames = []
            dst["post"].mapping = {}
        dst["maxp"].numGlyphs = len(order)
        dst.save(out_path)
        return set(have) | set(added.keys())
    except Exception:
        try:
            if os.path.exists(out_path):
                os.remove(out_path)
        except Exception:
            pass
        return None


_MERGE_VERSION = "m4"


def font_signature(info):
    parts = [_MERGE_VERSION, info.get("reg") or "", info.get("bold") or ""] + list(info.get("fallbacks") or [])
    h = hashlib.md5()
    for p in parts:
        h.update(_file_key(p).encode("utf-8", "replace"))
    return h.hexdigest()[:10]


def _merged_files(folder, sig):
    return (os.path.join(folder, "idda_reg_%s.ttf" % sig),
            os.path.join(folder, "idda_bold_%s.ttf" % sig),
            os.path.join(folder, "idda_font_%s.json" % sig))


def load_merged_fonts(info, folder):
    """Already-built merged font from an earlier run -> fonts dict, or None."""
    try:
        sig = font_signature(info)
        reg, bold, meta = _merged_files(folder, sig)
        if not (os.path.isfile(reg) and os.path.isfile(meta)):
            return None
        with open(meta, "r", encoding="utf-8") as f:
            m = json.load(f)
        cov = _dec_ranges(m.get("cover") or [])
        if not cov:
            return None
        return {"reg": reg, "bold": bold if os.path.isfile(bold) else reg, "universal": True,
                "cover": cov, "fallbacks": [], "merged": True,
                "name": (info.get("name") or "") + " +"}
    except Exception:
        return None


def build_merged_fonts(info, folder):
    """Blocking (run it in a thread). Builds the one-font file(s). -> fonts dict or None."""
    try:
        os.makedirs(folder, exist_ok=True)
        sig = font_signature(info)
        reg_out, bold_out, meta = _merged_files(folder, sig)
        fbs = list(info.get("fallbacks") or [])
        cov = build_ui_font(info["reg"], fbs, reg_out)
        if not cov:
            return None
        if info.get("bold") and info["bold"] != info["reg"]:
            if not build_ui_font(info["bold"], fbs, bold_out):
                bold_out = reg_out
        else:
            bold_out = reg_out
        with open(meta, "w", encoding="utf-8") as f:
            json.dump({"cover": _enc_ranges(cov)}, f)
        for fn in os.listdir(folder):                       # remove builds of older font sets
            if fn.startswith(("idda_reg_", "idda_bold_", "idda_font_")) and sig not in fn:
                try:
                    os.remove(os.path.join(folder, fn))
                except Exception:
                    pass
        return {"reg": reg_out, "bold": bold_out, "universal": True, "cover": cov,
                "fallbacks": [], "merged": True, "name": (info.get("name") or "") + " +"}
    except Exception:
        return None


def dir_has_images(path, cache, depth=3):
    """True if `path` holds a picture (directly or in a sub-folder up to `depth` levels down)."""
    got = cache.get(path)
    if got is not None:
        return got
    found = False
    subs = []
    try:
        with os.scandir(path) as it:
            for e in it:
                if e.name.startswith("."):
                    continue
                try:
                    if e.is_dir():
                        if e.name != "Android":
                            subs.append(e.path)
                    elif e.name.lower().endswith(IMG_EXTS):
                        found = True
                        break
                except OSError:
                    continue
    except Exception:
        pass
    if not found and depth > 0:
        for sub in subs:
            if dir_has_images(sub, cache, depth - 1):
                found = True
                break
    cache[path] = found
    return found


def make_thumb_png(path, size=256):
    """Square-cropped PNG thumbnail (used by the gallery-style picker)."""
    with Image.open(path) as im0:
        try:
            im0.draft("RGB", (size * 2, size * 2))
        except Exception:
            pass
        im0.load()
        try:
            im = ImageOps.exif_transpose(im0)
        except Exception:
            im = im0
    if im.mode in ("RGBA", "LA", "P"):
        im = flatten_rgb(im.convert("RGBA"))
    elif im.mode != "RGB":
        im = im.convert("RGB")
    im = ImageOps.fit(im, (size, size), LANCZOS)
    return pil_to_png_bytes(im)


# --------------------------------------------------------------------------
# QR: create
# --------------------------------------------------------------------------
URL_LIKE_RE = re.compile(r"^(?:https?://|www\.)\S+$|^[\w\-]+(?:\.[\w\-]+)*\.[A-Za-z]{2,}(?:[/?#:]\S*)?$", re.I)
PHONE_RE = re.compile(r"^\+?[\d\s\-().]{6,20}$")
IPV4_RE = re.compile(r"^(\d{1,3})\.(\d{1,3})\.(\d{1,3})\.(\d{1,3})(?::\d{1,5})?(?:[/?#]\S*)?$")
EMAIL_RE = re.compile(r"^[^@\s]+@[^@\s]+\.[A-Za-z]{2,}$")


def detect_kind(s):
    s = (s or "").strip()
    if not s or "\n" in s or " " in s and not PHONE_RE.match(s):
        return "text"
    if EMAIL_RE.match(s):
        return "email"
    m = IPV4_RE.match(s)
    if m and all(int(g) <= 255 for g in m.groups()[:4]):
        return "link"
    if PHONE_RE.match(s) and sum(ch.isdigit() for ch in s) >= 6:
        return "phone"
    if URL_LIKE_RE.match(s):
        return "link"
    return "text"


def build_payload(text, kind):
    """kind: auto|link|phone|text -> (payload, resolved_kind)"""
    text = (text or "").strip()
    if kind == "auto":
        kind = detect_kind(text)
    if kind == "email":
        return "mailto:" + text, "email"
    if kind == "phone":
        digits = re.sub(r"[^\d+]", "", text)
        return "tel:" + digits, "phone"
    if kind == "link":
        if not re.match(r"^[A-Za-z][A-Za-z0-9+.\-]*://", text):
            text = "https://" + text
        return text, "link"
    return text, "text"


def qr_matrix(data, ec="M"):
    """Return a square list-of-lists of bool (no quiet zone)."""
    if _qrcode_lib is not None:
        levels = {"L": _qrcode_lib.constants.ERROR_CORRECT_L,
                  "M": _qrcode_lib.constants.ERROR_CORRECT_M,
                  "Q": _qrcode_lib.constants.ERROR_CORRECT_Q,
                  "H": _qrcode_lib.constants.ERROR_CORRECT_H}
        q = _qrcode_lib.QRCode(error_correction=levels.get(ec, levels["M"]), box_size=1, border=0)
        q.add_data(data)
        q.make(fit=True)
        return [[bool(c) for c in row] for row in q.get_matrix()]
    if cv2 is not None and np is not None and hasattr(cv2, "QRCodeEncoder_create"):
        enc = cv2.QRCodeEncoder_create()
        img = enc.encode(data)
        if img is None or img.size == 0:
            raise ValueError("encode failed")
        if img.ndim == 3:
            img = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
        dark = img < 128
        ys, xs = np.where(dark)
        crop = dark[ys.min():ys.max() + 1, xs.min():xs.max() + 1]
        row0 = crop[0]
        run = 0
        for v in row0:
            if v:
                run += 1
            else:
                break
        ms = max(1.0, run / 7.0)
        n = int(round(crop.shape[1] / ms))
        mat = []
        for r in range(n):
            yy = int((r + 0.5) * ms)
            mat.append([bool(crop[min(yy, crop.shape[0] - 1), min(int((c + 0.5) * ms), crop.shape[1] - 1)])
                        for c in range(n)])
        return mat
    raise RuntimeError("no-qr-encoder")


def render_qr(matrix, fg="#000000", bg="#FFFFFF", border=4, min_px=1024):
    n = len(matrix)
    total = n + 2 * border
    cell = max(4, -(-min_px // total))
    small = Image.new("RGB", (total, total), ImageColor.getrgb(bg))
    px = small.load()
    fgc = ImageColor.getrgb(fg)
    for y, row in enumerate(matrix):
        for x, v in enumerate(row):
            if v:
                px[x + border, y + border] = fgc
    return small.resize((total * cell, total * cell), NEAREST)


def pil_to_png_bytes(img, max_side=None):
    if max_side and max(img.size) > max_side:
        r = max_side / float(max(img.size))
        img = img.resize((max(1, int(img.width * r)), max(1, int(img.height * r))), LANCZOS)
    buf = io.BytesIO()
    img.save(buf, "PNG")
    return buf.getvalue()


QR_PALETTES = {
    "classic": ("#000000", "Classic"),
    "teal": ("#0F766E", "Teal"),
    "navy": ("#1E3A8A", "Navy"),
    "plum": ("#6B21A8", "Plum"),
    "crimson": ("#9F1239", "Crimson"),
}


# --------------------------------------------------------------------------
# QR: read / classify
# --------------------------------------------------------------------------
# ==========================================================================
# QR reader written in pure Python (needs only Pillow) - no OpenCV needed
# ==========================================================================
_QR_EC_BITS = {"L": 1, "M": 0, "Q": 3, "H": 2}

# version -> {level: (ec codewords per block, [(blocks, data codewords per block), ...])}
_QR_BLOCKS_RAW = """
1  L7:1x19 M10:1x16 Q13:1x13 H17:1x9
2  L10:1x34 M16:1x28 Q22:1x22 H28:1x16
3  L15:1x55 M26:1x44 Q18:2x17 H22:2x13
4  L20:1x80 M18:2x32 Q26:2x24 H16:4x9
5  L26:1x108 M24:2x43 Q18:2x15+2x16 H22:2x11+2x12
6  L18:2x68 M16:4x27 Q24:4x19 H28:4x15
7  L20:2x78 M18:4x31 Q18:2x14+4x15 H26:4x13+1x14
8  L24:2x97 M22:2x38+2x39 Q22:4x18+2x19 H26:4x14+2x15
9  L30:2x116 M22:3x36+2x37 Q20:4x16+4x17 H24:4x12+4x13
10 L18:2x68+2x69 M26:4x43+1x44 Q24:6x19+2x20 H28:6x15+2x16
11 L20:4x81 M30:1x50+4x51 Q28:4x22+4x23 H24:3x12+8x13
12 L24:2x92+2x93 M22:6x36+2x37 Q26:4x20+6x21 H28:7x14+4x15
13 L26:4x107 M22:8x37+1x38 Q24:8x20+4x21 H22:12x11+4x12
14 L30:3x115+1x116 M24:4x40+5x41 Q20:11x16+5x17 H24:11x12+5x13
15 L22:5x87+1x88 M24:5x41+5x42 Q30:5x24+7x25 H24:11x12+7x13
16 L24:5x98+1x99 M28:7x45+3x46 Q24:15x19+2x20 H30:3x15+13x16
17 L28:1x107+5x108 M28:10x46+1x47 Q28:1x22+15x23 H28:2x14+17x15
18 L30:5x120+1x121 M26:9x43+4x44 Q28:17x22+1x23 H28:2x14+19x15
19 L28:3x113+4x114 M26:3x44+11x45 Q26:17x21+4x22 H26:9x13+16x14
20 L28:3x107+5x108 M26:3x41+13x42 Q30:15x24+5x25 H28:15x15+10x16
21 L28:4x116+4x117 M26:17x42 Q28:17x22+6x23 H30:19x16+6x17
22 L28:2x111+7x112 M28:17x46 Q30:7x24+16x25 H24:34x13
23 L30:4x121+5x122 M28:4x47+14x48 Q30:11x24+14x25 H30:16x15+14x16
24 L30:6x117+4x118 M28:6x45+14x46 Q30:11x24+16x25 H30:30x16+2x17
25 L26:8x106+4x107 M28:8x47+13x48 Q30:7x24+22x25 H30:22x15+13x16
26 L28:10x114+2x115 M28:19x46+4x47 Q28:28x22+6x23 H30:33x16+4x17
27 L30:8x122+4x123 M28:22x45+3x46 Q30:8x23+26x24 H30:12x15+28x16
28 L30:3x117+10x118 M28:3x45+23x46 Q30:4x24+31x25 H30:11x15+31x16
29 L30:7x116+7x117 M28:21x45+7x46 Q30:1x23+37x24 H30:19x15+26x16
30 L30:5x115+10x116 M28:19x47+10x48 Q30:15x24+25x25 H30:23x15+25x16
31 L30:13x115+3x116 M28:2x46+29x47 Q30:42x24+1x25 H30:23x15+28x16
32 L30:17x115 M28:10x46+23x47 Q30:10x24+35x25 H30:19x15+35x16
33 L30:17x115+1x116 M28:14x46+21x47 Q30:29x24+19x25 H30:11x15+46x16
34 L30:13x115+6x116 M28:14x46+23x47 Q30:44x24+7x25 H30:59x16+1x17
35 L30:12x121+7x122 M28:12x47+26x48 Q30:39x24+14x25 H30:22x15+41x16
36 L30:6x121+14x122 M28:6x47+34x48 Q30:46x24+10x25 H30:2x15+64x16
37 L30:17x122+4x123 M28:29x46+14x47 Q30:49x24+10x25 H30:24x15+46x16
38 L30:4x122+18x123 M28:13x46+32x47 Q30:48x24+14x25 H30:42x15+32x16
39 L30:20x117+4x118 M28:40x47+7x48 Q30:43x24+22x25 H30:10x15+67x16
40 L30:19x118+6x119 M28:18x47+31x48 Q30:34x24+34x25 H30:20x15+61x16
"""

_QR_BLOCKS = {}


def _qr_parse_blocks():
    for line in _QR_BLOCKS_RAW.strip().splitlines():
        parts = line.split()
        v = int(parts[0])
        d = {}
        for tok in parts[1:]:
            lvl, rest = tok[0], tok[1:]
            ec, groups = rest.split(":")
            d[lvl] = (int(ec), [tuple(int(z) for z in g.split("x")) for g in groups.split("+")])
        _QR_BLOCKS[v] = d


_qr_parse_blocks()


_QR_ALIGN = {
    2: [6, 18], 3: [6, 22], 4: [6, 26], 5: [6, 30], 6: [6, 34], 7: [6, 22, 38], 8: [6, 24, 42],
    9: [6, 26, 46], 10: [6, 28, 50], 11: [6, 30, 54], 12: [6, 32, 58], 13: [6, 34, 62],
    14: [6, 26, 46, 66], 15: [6, 26, 48, 70], 16: [6, 26, 50, 74], 17: [6, 30, 54, 78],
    18: [6, 30, 56, 82], 19: [6, 30, 58, 86], 20: [6, 34, 62, 90], 21: [6, 28, 50, 72, 94],
    22: [6, 26, 50, 74, 98], 23: [6, 30, 54, 78, 102], 24: [6, 28, 54, 80, 106],
    25: [6, 32, 58, 84, 110], 26: [6, 30, 58, 86, 114], 27: [6, 34, 62, 90, 118],
    28: [6, 26, 50, 74, 98, 122], 29: [6, 30, 54, 78, 102, 126], 30: [6, 26, 52, 78, 104, 130],
    31: [6, 30, 56, 82, 108, 134], 32: [6, 34, 60, 86, 112, 138], 33: [6, 30, 58, 86, 114, 142],
    34: [6, 34, 62, 90, 118, 146], 35: [6, 30, 54, 78, 102, 126, 150],
    36: [6, 24, 50, 76, 102, 128, 154], 37: [6, 28, 54, 80, 106, 132, 158],
    38: [6, 32, 58, 84, 110, 136, 162], 39: [6, 26, 54, 82, 110, 138, 166],
    40: [6, 30, 58, 86, 114, 142, 170],
}


def _qr_align_positions(v):
    return _QR_ALIGN.get(v, [])


def _qr_bch(value, poly, top_bit):
    d = value
    while d.bit_length() >= top_bit:
        d ^= poly << (d.bit_length() - top_bit)
    return d


def _qr_format_table():
    table = {}
    for ec_name, ec_bits in _QR_EC_BITS.items():
        for mask in range(8):
            data = (ec_bits << 3) | mask
            code = ((data << 10) | _qr_bch(data << 10, 0x537, 11)) ^ 0x5412
            table[code] = (ec_name, mask)
    return table


_QR_FORMATS = _qr_format_table()


# ---- GF(256) / Reed-Solomon -------------------------------------------------
_GF_EXP = [0] * 512
_GF_LOG = [0] * 256


def _gf_init():
    x = 1
    for i in range(255):
        _GF_EXP[i] = x
        _GF_LOG[x] = i
        x <<= 1
        if x & 0x100:
            x ^= 0x11D
    for i in range(255, 512):
        _GF_EXP[i] = _GF_EXP[i - 255]


_gf_init()


def _gf_mul(a, b):
    if a == 0 or b == 0:
        return 0
    return _GF_EXP[_GF_LOG[a] + _GF_LOG[b]]


def _gf_div(a, b):
    if a == 0:
        return 0
    return _GF_EXP[(_GF_LOG[a] - _GF_LOG[b]) % 255]


def _poly_eval(p, x):
    """p: coefficients, highest degree first."""
    y = p[0]
    for c in p[1:]:
        y = _gf_mul(y, x) ^ c
    return y


def _rs_correct(block, nsym):
    """Return corrected block (data+ec) or None."""
    n = len(block)
    synd = [_poly_eval(block, _GF_EXP[i]) for i in range(nsym)]
    if not any(synd):
        return block
    # Berlekamp-Massey (lowest degree first)
    C, B = [1], [1]
    L, m, b = 0, 1, 1
    for i in range(nsym):
        d = synd[i]
        for j in range(1, L + 1):
            if j < len(C):
                d ^= _gf_mul(C[j], synd[i - j])
        if d == 0:
            m += 1
        elif 2 * L <= i:
            T = C[:]
            coef = _gf_div(d, b)
            C = C + [0] * (len(B) + m - len(C))
            for j in range(len(B)):
                C[j + m] ^= _gf_mul(coef, B[j])
            L, B, b, m = i + 1 - L, T, d, 1
        else:
            coef = _gf_div(d, b)
            C = C + [0] * (len(B) + m - len(C))
            for j in range(len(B)):
                C[j + m] ^= _gf_mul(coef, B[j])
            m += 1
    if L * 2 > nsym:
        return None
    # Chien search: error at position p (0 = first byte) <=> locator root alpha^-(n-1-p)
    err_pos = []
    for p in range(n):
        xinv = _GF_EXP[(255 - (n - 1 - p)) % 255]
        s = 0
        xp = 1
        for c in C:
            s ^= _gf_mul(c, xp)
            xp = _gf_mul(xp, xinv)
        if s == 0:
            err_pos.append(p)
    if len(err_pos) != L:
        return None
    # Forney: omega = S(x)*C(x) mod x^nsym
    omega = [0] * nsym
    for i in range(nsym):
        v = 0
        for j in range(min(i, len(C) - 1) + 1):
            v ^= _gf_mul(C[j], synd[i - j])
        omega[i] = v
    out = list(block)
    for p in err_pos:
        k = n - 1 - p
        xk = _GF_EXP[k % 255]
        xinv = _GF_EXP[(255 - k) % 255]
        num = 0
        xp = 1
        for c in omega:
            num ^= _gf_mul(c, xp)
            xp = _gf_mul(xp, xinv)
        den = 0                                # derivative of C at xinv (odd terms only)
        for j in range(1, len(C), 2):
            den ^= _gf_mul(C[j], _GF_EXP[(255 - k) * (j - 1) % 255] if j > 1 else 1)
        if den == 0:
            return None
        mag = _gf_mul(xk, _gf_div(num, den))
        out[p] ^= mag
    if any(_poly_eval(out, _GF_EXP[i]) for i in range(nsym)):
        return None
    return out


# ---- function patterns / data reading --------------------------------------
_QR_FUNC_CACHE = {}


def _qr_function_map(v):
    if v in _QR_FUNC_CACHE:
        return _QR_FUNC_CACHE[v]
    n = 17 + 4 * v
    f = [[False] * n for _ in range(n)]

    def fill(r0, c0, h, w):
        for r in range(max(0, r0), min(n, r0 + h)):
            for c in range(max(0, c0), min(n, c0 + w)):
                f[r][c] = True
    fill(0, 0, 9, 9)
    fill(0, n - 8, 9, 8)
    fill(n - 8, 0, 8, 9)
    for i in range(n):
        f[6][i] = True
        f[i][6] = True
    pos = _qr_align_positions(v)
    for r in pos:
        for c in pos:
            if (r == 6 and c == 6) or (r == 6 and c == pos[-1]) or (r == pos[-1] and c == 6):
                continue
            fill(r - 2, c - 2, 5, 5)
    if v >= 7:
        fill(n - 11, 0, 3, 6)
        fill(0, n - 11, 6, 3)
    _QR_FUNC_CACHE[v] = f
    return f


_QR_MASKS = (
    lambda i, j: (i + j) % 2 == 0,
    lambda i, j: i % 2 == 0,
    lambda i, j: j % 3 == 0,
    lambda i, j: (i + j) % 3 == 0,
    lambda i, j: (i // 2 + j // 3) % 2 == 0,
    lambda i, j: (i * j) % 2 + (i * j) % 3 == 0,
    lambda i, j: ((i * j) % 2 + (i * j) % 3) % 2 == 0,
    lambda i, j: ((i + j) % 2 + (i * j) % 3) % 2 == 0,
)


def _qr_read_format(m, n):
    """Return (ec_level, mask) or None."""
    def bits(copy):
        val = 0
        for i in range(15):
            if copy == 0:
                if i < 6:
                    b = m[i][8]
                elif i < 8:
                    b = m[i + 1][8]
                else:
                    b = m[n - 15 + i][8]
            else:
                if i < 8:
                    b = m[8][n - i - 1]
                elif i < 9:
                    b = m[8][15 - i - 1 + 1]
                else:
                    b = m[8][15 - i - 1]
            if b:
                val |= 1 << i
        return val
    best, best_d = None, 4
    for raw in (bits(0), bits(1)):
        for code, info in _QR_FORMATS.items():
            d = bin(raw ^ code).count("1")
            if d < best_d:
                best, best_d = info, d
    return best


def _qr_bits_to_text(data, v):
    bits = "".join("{:08b}".format(b) for b in data)
    pos = 0
    out = []
    nb = len(bits)
    eci_enc = None

    def cc_bits(mode):
        k = 0 if v <= 9 else (1 if v <= 26 else 2)
        return {1: (10, 12, 14), 2: (9, 11, 13), 4: (8, 16, 16), 8: (8, 10, 12)}[mode][k]
    while pos + 4 <= nb:
        mode = int(bits[pos:pos + 4], 2)
        pos += 4
        if mode == 0:
            break
        if mode == 7:                                        # ECI
            if pos + 8 > nb:
                break
            first = int(bits[pos:pos + 8], 2)
            if first < 128:
                val, pos = first, pos + 8
            elif first < 192:
                val, pos = int(bits[pos:pos + 16], 2) & 0x3FFF, pos + 16
            else:
                val, pos = int(bits[pos:pos + 24], 2) & 0x1FFFFF, pos + 24
            eci_enc = {20: "shift_jis", 26: "utf-8", 3: "latin-1", 4: "iso8859-2", 27: "ascii",
                       22: "cp1251", 23: "cp1252", 24: "cp1256", 25: "utf-16-be"}.get(val)
            continue
        if mode in (5, 9):                                   # FNC1: no payload
            continue
        if mode == 3:                                        # structured append header
            pos += 16
            continue
        if mode not in (1, 2, 4, 8):
            return None
        cb = cc_bits(mode)
        if pos + cb > nb:
            return None
        cnt = int(bits[pos:pos + cb], 2)
        pos += cb
        if mode == 1:
            s = ""
            while cnt >= 3:
                s += "%03d" % int(bits[pos:pos + 10], 2)
                pos += 10
                cnt -= 3
            if cnt == 2:
                s += "%02d" % int(bits[pos:pos + 7], 2)
                pos += 7
            elif cnt == 1:
                s += "%d" % int(bits[pos:pos + 4], 2)
                pos += 4
            out.append(s.encode("ascii"))
        elif mode == 2:
            tbl = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ $%*+-./:"
            s = ""
            while cnt >= 2:
                x = int(bits[pos:pos + 11], 2)
                pos += 11
                s += tbl[x // 45] + tbl[x % 45]
                cnt -= 2
            if cnt == 1:
                s += tbl[int(bits[pos:pos + 6], 2)]
                pos += 6
            out.append(s.encode("ascii"))
        elif mode == 4:
            if pos + 8 * cnt > nb:
                return None
            out.append(bytes(int(bits[pos + 8 * i:pos + 8 * i + 8], 2) for i in range(cnt)))
            pos += 8 * cnt
        else:                                                # kanji
            bs = bytearray()
            for _ in range(cnt):
                x = int(bits[pos:pos + 13], 2)
                pos += 13
                x = (x // 0xC0 << 8) | (x % 0xC0)
                x += 0x8140 if x < 0x1F00 else 0xC140
                bs += bytes((x >> 8, x & 0xFF))
            out.append(bytes(bs))
    raw = b"".join(out)
    encs = ([eci_enc] if eci_enc else []) + ["utf-8", "shift_jis", "cp1256", "latin-1"]
    for e in encs:
        try:
            return raw.decode(e)
        except Exception:
            continue
    return raw.decode("latin-1", "replace")


def _qr_decode_matrix(m, n):
    v = (n - 17) // 4
    if v < 1 or v > 40 or 17 + 4 * v != n:
        return None
    fmt = _qr_read_format(m, n)
    if fmt is None:
        return None
    level, mask = fmt
    ec_len, groups = _QR_BLOCKS[v][level]
    func = _qr_function_map(v)
    maskf = _QR_MASKS[mask]
    # zig-zag read
    bits = []
    col = n - 1
    up = True
    while col > 0:
        if col == 6:
            col -= 1
        rows = range(n - 1, -1, -1) if up else range(n)
        for r in rows:
            for c in (col, col - 1):
                if not func[r][c]:
                    b = m[r][c]
                    if maskf(r, c):
                        b = not b
                    bits.append(1 if b else 0)
        up = not up
        col -= 2
    total = sum(g[0] * (g[1] + ec_len) for g in groups)
    if len(bits) < total * 8:
        return None
    cw = [int("".join(map(str, bits[i * 8:i * 8 + 8])), 2) for i in range(total)]
    # de-interleave
    block_sizes = []
    for cnt, dlen in groups:
        block_sizes += [dlen] * cnt
    nblocks = len(block_sizes)
    data_blocks = [[] for _ in range(nblocks)]
    ec_blocks = [[] for _ in range(nblocks)]
    idx = 0
    for i in range(max(block_sizes)):
        for b in range(nblocks):
            if i < block_sizes[b]:
                data_blocks[b].append(cw[idx])
                idx += 1
    for i in range(ec_len):
        for b in range(nblocks):
            ec_blocks[b].append(cw[idx])
            idx += 1
    data = []
    for b in range(nblocks):
        fixed = _rs_correct(data_blocks[b] + ec_blocks[b], ec_len)
        if fixed is None:
            return None
        data += fixed[:block_sizes[b]]
    return _qr_bits_to_text(data, v)


def _qr_decode_with_mirror(m, n):
    r = _qr_decode_matrix(m, n)
    if r is None:
        t = [list(row) for row in zip(*m)]
        r = _qr_decode_matrix(t, n)
    return r


# ---- image side: binarize, find finders, sample ----------------------------
import re as _re_qr
_QR_RUN_RE = _re_qr.compile(b"\x01+|\x00+")


def _qr_binarize(gray, mode):
    """gray: PIL 'L' image -> (bytes with 1 = dark, w, h)."""
    w, h = gray.size
    if mode == "otsu":
        hist = gray.histogram()
        total = w * h
        sum_all = sum(i * hist[i] for i in range(256))
        wb = 0
        sum_b = 0.0
        best, thr = -1.0, 128
        for t in range(256):
            wb += hist[t]
            if wb == 0:
                continue
            wf = total - wb
            if wf == 0:
                break
            sum_b += t * hist[t]
            mb = sum_b / wb
            mf = (sum_all - sum_b) / wf
            var = wb * wf * (mb - mf) ** 2
            if var > best:
                best, thr = var, t
        bw = gray.point([255 if i <= thr else 0 for i in range(256)])
    else:
        from PIL import ImageFilter, ImageChops
        r = max(8, min(w, h) // 10)
        blur = gray.filter(ImageFilter.BoxBlur(r))
        diff = ImageChops.subtract(blur, gray, 1.0, 128)           # 128 + (mean - pixel)
        bw = diff.point([255 if i > 128 + 6 else 0 for i in range(256)])
    return bw.point([1 if i else 0 for i in range(256)]).tobytes(), w, h


def _qr_check_ratio(lens):
    total = sum(lens)
    if total < 7:
        return 0.0
    mod = total / 7.0
    tol = mod * 0.6
    if (abs(lens[0] - mod) < tol and abs(lens[1] - mod) < tol and abs(lens[2] - 3 * mod) < 3 * tol
            and abs(lens[3] - mod) < tol and abs(lens[4] - mod) < tol):
        return mod
    return 0.0


def _qr_runs(line):
    return [(m.start(), m.end() - m.start(), line[m.start()]) for m in _QR_RUN_RE.finditer(line)]


def _qr_cross(line, pos):
    """Find the 1:1:3:1:1 run pattern whose centre run contains `pos`. -> (centre, module) or None."""
    runs = _qr_runs(line)
    for i, (st, ln, val) in enumerate(runs):
        if st <= pos < st + ln:
            if val != 1 or i < 2 or i + 2 >= len(runs):
                return None
            lens = [runs[i + k][1] for k in range(-2, 3)]
            mod = _qr_check_ratio(lens)
            if not mod:
                return None
            first = runs[i - 2][0]
            last = runs[i + 2][0] + runs[i + 2][1]
            return (first + last) / 2.0, mod
    return None


def _qr_find_finders(data, w, h, budget=1.0):
    cands = []                                   # [cx, cy, module, count]
    step = 1 if h <= 640 else 2
    import time as _t
    t_end = _t.time() + budget
    for y in range(0, h, step):
        if (y & 15) == 0 and _t.time() > t_end:
            break
        row = data[y * w:(y + 1) * w]
        if 1 not in row:
            continue
        runs = _qr_runs(row)
        for i in range(len(runs) - 4):
            if runs[i][2] != 1:
                continue
            lens = [runs[i + k][1] for k in range(5)]
            mod = _qr_check_ratio(lens)
            if not mod:
                continue
            cx = runs[i][0] + sum(lens) / 2.0
            col = data[int(cx)::w]
            vc = _qr_cross(col, y)
            if vc is None:
                continue
            cy, vmod = vc
            hc = _qr_cross(data[int(cy) * w:(int(cy) + 1) * w], int(cx))
            if hc is None:
                continue
            cx, hmod = hc
            m = (mod + vmod + hmod) / 3.0
            if abs(vmod - hmod) > max(1.5, 0.6 * m):
                continue
            for c in cands:
                if abs(c[0] - cx) < max(c[2], m) * 2.0 and abs(c[1] - cy) < max(c[2], m) * 2.0:
                    k = c[3]
                    c[0] = (c[0] * k + cx) / (k + 1)
                    c[1] = (c[1] * k + cy) / (k + 1)
                    c[2] = (c[2] * k + m) / (k + 1)
                    c[3] = k + 1
                    break
            else:
                cands.append([cx, cy, m, 1])
    return [c for c in cands if c[3] >= 2]


def _qr_triples(cands):
    cands = sorted(cands, key=lambda c: -c[3])[:9]
    out = []
    n = len(cands)
    for i in range(n):
        for j in range(i + 1, n):
            for k in range(j + 1, n):
                t = (cands[i], cands[j], cands[k])
                ms = [c[2] for c in t]
                if max(ms) > 1.7 * min(ms):
                    continue
                d = []
                for a, b in ((0, 1), (0, 2), (1, 2)):
                    d.append(((t[a][0] - t[b][0]) ** 2 + (t[a][1] - t[b][1]) ** 2, (a, b)))
                d.sort()
                s0, s1, s2 = d[0][0], d[1][0], d[2][0]
                if s2 <= 0 or s0 <= 0:
                    continue
                score = abs(s0 - s1) / s1 + abs(s0 + s1 - s2) / s2
                if score > 0.45:
                    continue
                # the corner (top-left) is the point shared by the two short sides
                common = set(d[0][1]) & set(d[1][1])
                tl = common.pop()
                others = [x for x in range(3) if x != tl]
                p_tl = t[tl]
                p_a, p_b = t[others[0]], t[others[1]]
                cr = (p_a[0] - p_tl[0]) * (p_b[1] - p_tl[1]) - (p_a[1] - p_tl[1]) * (p_b[0] - p_tl[0])
                if cr < 0:
                    p_a, p_b = p_b, p_a
                out.append((score, p_tl, p_a, p_b))
    out.sort(key=lambda x: x[0])
    return out[:3]


def _qr_homography(src, dst):
    """4 point pairs -> function (x, y) -> (X, Y)."""
    A = []
    for (x, y), (X, Y) in zip(src, dst):
        A.append([x, y, 1, 0, 0, 0, -X * x, -X * y, X])
        A.append([0, 0, 0, x, y, 1, -Y * x, -Y * y, Y])
    n = 8
    for i in range(n):
        piv = max(range(i, n), key=lambda r: abs(A[r][i]))
        if abs(A[piv][i]) < 1e-12:
            return None
        A[i], A[piv] = A[piv], A[i]
        p = A[i][i]
        A[i] = [v / p for v in A[i]]
        for r in range(n):
            if r != i and A[r][i]:
                f = A[r][i]
                A[r] = [a - f * b for a, b in zip(A[r], A[i])]
    a, b, c, d, e, f, g, hh = [A[i][8] for i in range(8)]

    def fn(x, y):
        den = g * x + hh * y + 1.0
        return (a * x + b * y + c) / den, (d * x + e * y + f) / den
    return fn


def _qr_try_triple(data, w, h, tl, tr, bl):
    mod = (tl[2] + tr[2] + bl[2]) / 3.0
    dist = (((tr[0] - tl[0]) ** 2 + (tr[1] - tl[1]) ** 2) ** 0.5
            + ((bl[0] - tl[0]) ** 2 + (bl[1] - tl[1]) ** 2) ** 0.5) / 2.0
    est = dist / mod + 7.0
    vers = sorted(range(1, 41), key=lambda v: abs(17 + 4 * v - est))
    vers = [v for v in vers[:3] if abs(17 + 4 * v - est) <= 6.5]
    for v in vers:
        n = 17 + 4 * v
        sc = float(n - 7)
        ax, ay = (tr[0] - tl[0]) / sc, (tr[1] - tl[1]) / sc
        bx, by = (bl[0] - tl[0]) / sc, (bl[1] - tl[1]) / sc

        def aff(gx, gy, tl=tl, ax=ax, ay=ay, bx=bx, by=by):
            return (tl[0] + (gx - 3.5) * ax + (gy - 3.5) * bx, tl[1] + (gx - 3.5) * ay + (gy - 3.5) * by)

        def px(x, y):
            xi, yi = int(x + 0.5), int(y + 0.5)
            if 0 <= xi < w and 0 <= yi < h:
                return data[yi * w + xi]
            return 0
        mapper = aff
        if v >= 2:
            gx0 = gy0 = n - 6.5
            best, ties = -1, []
            for oy in range(-6, 7):
                for ox in range(-6, 7):
                    cx, cy = gx0 + ox * 0.5, gy0 + oy * 0.5
                    s = 0
                    for j in range(-2, 3):
                        for i in range(-2, 3):
                            x, y = aff(cx + i, cy + j)
                            want = 1 if max(abs(i), abs(j)) != 1 else 0
                            if px(x, y) == want:
                                s += 1
                    if s > best:
                        best, ties = s, [(cx, cy)]
                    elif s == best:
                        ties.append((cx, cy))
            if best >= 22:
                cx = sum(t[0] for t in ties) / len(ties)
                cy = sum(t[1] for t in ties) / len(ties)
                src = [(3.5, 3.5), (n - 3.5, 3.5), (3.5, n - 3.5), (gx0, gy0)]
                dst = [(tl[0], tl[1]), (tr[0], tr[1]), (bl[0], bl[1]), aff(cx, cy)]
                hm = _qr_homography(src, dst)
                if hm is not None:
                    mapper = hm
        mat = []
        offs = ((0.5, 0.5), (0.25, 0.5), (0.75, 0.5), (0.5, 0.25), (0.5, 0.75))
        for r in range(n):
            row = []
            for c in range(n):
                s = 0
                for ox, oy in offs:
                    x, y = mapper(c + ox, r + oy)
                    s += px(x, y)
                row.append(s >= 3)
            mat.append(row)
        res = _qr_decode_with_mirror(mat, n)
        if res is not None:
            return res
    return None


def _qr_decode_gray_pil(gray):
    """Decode from a PIL 'L' image with the built-in decoder."""
    budget = 0.6 + gray.size[0] * gray.size[1] / 1e6 * 0.5
    for mode in ("otsu", "adaptive"):
        data, w, h = _qr_binarize(gray, mode)
        cands = _qr_find_finders(data, w, h, budget)
        if len(cands) < 3:
            continue
        for _score, tl, tr, bl in _qr_triples(cands):
            res = _qr_try_triple(data, w, h, tl, tr, bl)
            if res:
                return res
    return None


def qr_decode_builtin(img):
    """PIL image -> text or None. Pure Python (Pillow only)."""
    try:
        gray = img.convert("L")
    except Exception:
        return None
    w, h = gray.size
    big = max(w, h)
    if big > 1600:
        scales = [1000.0 / big, 1600.0 / big, 560.0 / big]
    elif big > 1000:
        scales = [1000.0 / big, 560.0 / big]
    elif big > 600:
        scales = [1.0, 0.6]
    elif big < 360:
        scales = [1.0, 2.0]
    else:
        scales = [1.0]
    for s in scales:
        if s == 1.0:
            g = gray
        else:
            g = gray.resize((max(8, int(w * s)), max(8, int(h * s))), 4 if s < 1 else 3)
        try:
            r = _qr_decode_gray_pil(g)
        except Exception:
            r = None
        if r:
            return r
    return None


def decode_qr_gray(gray):
    """gray: numpy uint8 2D array. Returns str or None."""
    if cv2 is None or np is None:
        return None
    variants = [gray]
    h, w = gray.shape[:2]
    if max(h, w) > 1400:
        r = 1200.0 / max(h, w)
        variants.append(cv2.resize(gray, (int(w * r), int(h * r)), interpolation=cv2.INTER_AREA))
    if max(h, w) < 700:
        variants.append(cv2.resize(gray, (w * 2, h * 2), interpolation=cv2.INTER_CUBIC))
    try:
        variants.append(cv2.adaptiveThreshold(gray, 255, cv2.ADAPTIVE_THRESH_GAUSSIAN_C,
                                              cv2.THRESH_BINARY, 31, 8))
    except Exception:
        pass
    variants.append(cv2.bitwise_not(gray))
    detectors = []
    if hasattr(cv2, "wechat_qrcode_WeChatQRCode"):
        try:
            detectors.append(("wechat", cv2.wechat_qrcode_WeChatQRCode()))
        except Exception:
            pass
    detectors.append(("std", cv2.QRCodeDetector()))
    for v in variants:
        for kind, det in detectors:
            try:
                if kind == "wechat":
                    texts, _pts = det.detectAndDecode(v)
                    for t in texts:
                        if t:
                            return t
                else:
                    data, _pts, _st = det.detectAndDecode(v)
                    if data:
                        return data
            except Exception:
                continue
    return None


def decode_qr_pil(img):
    """Decode a QR code from a PIL image. Returns str or None.
    Order: pyzbar (if installed) -> OpenCV (if installed) -> built-in pure-Python reader."""
    if not HAS_PIL:
        return None
    try:
        img = ImageOps.exif_transpose(img)
    except Exception:
        pass
    img = img.convert("RGB")
    if max(img.size) > 2000:
        r = 2000.0 / max(img.size)
        img = img.resize((int(img.width * r), int(img.height * r)), LANCZOS)
    if _zbar is not None:
        try:
            for res in _zbar.decode(img.convert("L")):
                if str(res.type).upper() == "QRCODE":
                    return res.data.decode("utf-8", "replace")
        except Exception:
            pass
    if cv2 is not None and np is not None:
        try:
            gray = cv2.cvtColor(np.array(img), cv2.COLOR_RGB2GRAY)
            r = decode_qr_gray(gray)
            if r:
                return r
        except Exception:
            pass
    return qr_decode_builtin(img)


def can_decode_qr():
    return bool(HAS_PIL)


SHORTENERS = {"bit.ly", "t.co", "tinyurl.com", "goo.gl", "is.gd", "cutt.ly", "rb.gy", "ow.ly",
              "shorturl.at", "rebrand.ly", "buff.ly", "tiny.cc", "lnkd.in", "s.id", "t.ly",
              "v.gd", "shorte.st", "bl.ink", "soo.gd", "clck.ru", "qr.ae"}
_IP_RE = re.compile(r"^(?:\d{1,3}\.){3}\d{1,3}$")


def analyze_url(url):
    """-> dict(url, host, blocked, warnings[list of T keys])"""
    u = (url or "").strip()
    if re.match(r"^www\.", u, re.I):
        u = "https://" + u
    info = {"url": u, "host": "", "blocked": False, "warnings": []}
    try:
        p = urlparse(u)
    except Exception:
        info["blocked"] = True
        return info
    scheme = (p.scheme or "").lower()
    if scheme not in ("http", "https"):
        info["blocked"] = True
        return info
    host = (p.hostname or "").lower()
    info["host"] = host
    w = info["warnings"]
    if scheme == "http":
        w.append("sc_warn_http")
    if _IP_RE.match(host) or (":" in host):
        w.append("sc_warn_ip")
    if host in SHORTENERS or host.replace("www.", "", 1) in SHORTENERS:
        w.append("sc_warn_short")
    if "xn--" in host or any(ord(ch) > 127 for ch in host):
        w.append("sc_warn_puny")
    if "@" in (p.netloc or ""):
        w.append("sc_warn_at")
    if len(u) > 220:
        w.append("sc_warn_long")
    return info


def parse_qr(text):
    """Classify scanned text -> dict(kind, fields[(label_key, value)], value, action)."""
    raw = (text or "").strip()
    low = raw.lower()
    res = {"kind": "text", "fields": [], "value": raw, "action": None, "raw": raw}
    if low.startswith("wifi:"):
        body = raw[5:]
        parts = re.split(r"(?<!\\);", body)
        d = {}
        for part in parts:
            if ":" in part:
                k, v = part.split(":", 1)
                d[k.strip().upper()] = v.replace("\\;", ";").replace("\\:", ":").replace("\\\\", "\\")
        res["kind"] = "wifi"
        res["fields"] = [("sc_ssid", d.get("S", "")), ("sc_security", d.get("T", "") or "-"),
                         ("sc_pass", d.get("P", ""))]
        res["value"] = d.get("P", "")
        res["action"] = "wifi"
    elif low.startswith("tel:"):
        res.update(kind="phone", value=raw[4:].strip(), action="call")
    elif low.startswith("mailto:"):
        res.update(kind="email", value=raw[7:].split("?")[0].strip(), action="mail")
    elif low.startswith(("sms:", "smsto:")):
        body = raw.split(":", 1)[1]
        num = body.split(":")[0].split("?")[0]
        res.update(kind="sms", value=num.strip(), action="sms")
        res["fields"] = [("kind_sms", body)]
    elif low.startswith("geo:"):
        res.update(kind="geo", value=raw[4:].split("?")[0], action="map")
    elif low.startswith("begin:vcard"):
        res["kind"] = "contact"
        fields = []
        for ln in raw.splitlines():
            if ln.upper().startswith(("FN:", "TEL", "EMAIL", "ORG:")):
                fields.append(("kind_contact", ln.split(":", 1)[-1].strip()))
        res["fields"] = fields
    elif re.match(r"^(https?://|www\.)", low) or low.startswith(("javascript:", "file:", "data:", "intent:")):
        res.update(kind="url", action="url")
    elif URL_LIKE_RE.match(raw) and " " not in raw and "\n" not in raw:
        res.update(kind="url", action="url", value="https://" + raw)
    return res


# --------------------------------------------------------------------------
# Images: compress
# --------------------------------------------------------------------------
def load_image_for_edit(path):
    """Open image, apply EXIF rotation, return PIL image (RGB or RGBA)."""
    with Image.open(path) as im0:
        im0.load()
        try:
            im = ImageOps.exif_transpose(im0)
        except Exception:
            im = im0
    if im.mode in ("RGBA", "LA") or (im.mode == "P" and "transparency" in im.info):
        im = im.convert("RGBA")
    elif im.mode != "RGB":
        im = im.convert("RGB")
    return im


def flatten_rgb(im, bg=(255, 255, 255)):
    if im.mode == "RGBA":
        base = Image.new("RGB", im.size, bg)
        base.paste(im, mask=im.split()[3])
        return base
    return im.convert("RGB") if im.mode != "RGB" else im


FORMATS = {
    "JPEG": (".jpg", "JPEG"),
    "WEBP": (".webp", "WEBP"),
    "PNG": (".png", "PNG"),
}


def compress_image(base, quality, scale, fmt):
    """-> (bytes, (w, h)). base: PIL image from load_image_for_edit."""
    im = base
    if scale < 0.999:
        w = max(1, int(round(base.width * scale)))
        h = max(1, int(round(base.height * scale)))
        im = base.resize((w, h), LANCZOS)
    buf = io.BytesIO()
    if fmt == "PNG":
        im.save(buf, "PNG", compress_level=6)
    elif fmt == "WEBP":
        im.save(buf, "WEBP", quality=int(quality), method=4)
    else:
        flatten_rgb(im).save(buf, "JPEG", quality=int(quality), optimize=True)
    return buf.getvalue(), im.size


# --------------------------------------------------------------------------
# Images -> PDF  (own tiny PDF writer: low memory, exact page sizes)
# --------------------------------------------------------------------------
PAGE_SIZES = {
    "A4": (595.276, 841.890),
    "A5": (419.528, 595.276),
    "A3": (841.890, 1190.551),
    "LETTER": (612.0, 792.0),
}
MARGINS = {"none": 0.0, "small": 24.0, "medium": 48.0}


class _PdfWriter:
    def __init__(self, fobj):
        self.f = fobj
        self.offsets = {}
        self.n = 2                     # 1 = catalog, 2 = pages
        self.f.write(b"%PDF-1.4\n%\xe2\xe3\xcf\xd3\n")

    def alloc(self):
        self.n += 1
        return self.n

    def _mark(self, num):
        self.offsets[num] = self.f.tell()
        self.f.write(("%d 0 obj\n" % num).encode("ascii"))

    def obj(self, num, body):
        self._mark(num)
        self.f.write(body if isinstance(body, bytes) else body.encode("latin-1"))
        self.f.write(b"\nendobj\n")

    def stream(self, num, dict_body, data):
        self._mark(num)
        self.f.write(("<< %s /Length %d >>\nstream\n" % (dict_body, len(data))).encode("ascii"))
        self.f.write(data)
        self.f.write(b"\nendstream\nendobj\n")

    def finish(self, kids, info_num):
        self.obj(1, "<< /Type /Catalog /Pages 2 0 R >>")
        self.obj(2, "<< /Type /Pages /Kids [%s] /Count %d >>" %
                 (" ".join("%d 0 R" % k for k in kids), len(kids)))
        start = self.f.tell()
        size = self.n + 1
        self.f.write(("xref\n0 %d\n" % size).encode("ascii"))
        self.f.write(b"0000000000 65535 f \n")
        for num in range(1, size):
            self.f.write(("%010d 00000 n \n" % self.offsets.get(num, 0)).encode("ascii"))
        self.f.write(("trailer\n<< /Size %d /Root 1 0 R /Info %d 0 R >>\nstartxref\n%d\n%%%%EOF\n"
                      % (size, info_num, start)).encode("ascii"))


def _page_geometry(iw, ih, page, orient, margin):
    ar = iw / float(ih)
    if page == "FIT":
        longest = 842.0
    else:
        bw, bh = PAGE_SIZES.get(page, PAGE_SIZES["A4"])
        longest = max(bw, bh)
    if page == "FIT" or margin <= 0:
        # No margins: the page takes the image's own shape (long edge = chosen
        # paper size), so the image fills the whole page with no white bars.
        if iw >= ih:
            pw, ph = longest, longest / ar
        else:
            ph, pw = longest, longest * ar
        pw += 2 * margin
        ph += 2 * margin
    else:
        bw, bh = PAGE_SIZES.get(page, PAGE_SIZES["A4"])
        if orient == "landscape" or (orient == "auto" and iw > ih):
            pw, ph = bh, bw
        else:
            pw, ph = bw, bh
    aw, ah = pw - 2 * margin, ph - 2 * margin
    s = min(aw / iw, ah / ih)
    dw, dh = iw * s, ih * s
    return pw, ph, (pw - dw) / 2.0, (ph - dh) / 2.0, dw, dh


def build_pdf(paths, out_path, page="A4", orient="auto", margin="none",
              jpeg_quality=88, max_px=2600, progress=None):
    """Create a PDF from image files. Returns (pages_written, skipped)."""
    m = MARGINS.get(margin, 0.0)
    kids = []
    tmp = out_path + ".part"
    try:
        _build_pdf_file(tmp, paths, page, orient, m, jpeg_quality, max_px, progress, kids)
    except BaseException:
        try:
            if os.path.exists(tmp):
                os.remove(tmp)
        except Exception:
            pass
        raise
    os.replace(tmp, out_path)
    return len(kids), len(paths) - len(kids)


def _build_pdf_file(tmp, paths, page, orient, m, jpeg_quality, max_px, progress, kids):
    with open(tmp, "wb") as f:
        w = _PdfWriter(f)
        total = len(paths)
        for i, p in enumerate(paths):
            if progress:
                progress(i + 1, total)
            try:
                with Image.open(p) as im0:
                    im0.load()
                    try:
                        im = ImageOps.exif_transpose(im0)
                    except Exception:
                        im = im0
                im = flatten_rgb(im if im.mode in ("RGB", "RGBA") else
                                 (im.convert("RGBA") if im.mode in ("LA", "P") else im.convert("RGB")))
                if max(im.size) > max_px:
                    r = max_px / float(max(im.size))
                    im = im.resize((max(1, int(im.width * r)), max(1, int(im.height * r))), LANCZOS)
                buf = io.BytesIO()
                im.save(buf, "JPEG", quality=int(jpeg_quality), optimize=True)
                jpg = buf.getvalue()
                iw, ih = im.size
            except Exception:
                continue
            pw, ph, x, y, dw, dh = _page_geometry(iw, ih, page, orient, m)
            n_img, n_cnt, n_page = w.alloc(), w.alloc(), w.alloc()
            w.stream(n_img, "/Type /XObject /Subtype /Image /Width %d /Height %d "
                            "/ColorSpace /DeviceRGB /BitsPerComponent 8 /Filter /DCTDecode" % (iw, ih), jpg)
            content = ("q %.3f 0 0 %.3f %.3f %.3f cm /Im0 Do Q" % (dw, dh, x, y)).encode("ascii")
            w.stream(n_cnt, "", content)
            w.obj(n_page, "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 %.3f %.3f] "
                          "/Resources << /XObject << /Im0 %d 0 R >> >> /Contents %d 0 R >>"
                  % (pw, ph, n_img, n_cnt))
            kids.append(n_page)
        if not kids:
            raise ValueError("no-pages")
        n_info = w.alloc()
        stamp = datetime.datetime.now(datetime.timezone.utc).strftime("D:%Y%m%d%H%M%SZ")
        w.obj(n_info, "<< /Producer (3edda) /Creator (3edda) /CreationDate (%s) >>" % stamp)
        w.finish(kids, n_info)


# --------------------------------------------------------------------------
# PDF tools: compress + merge (pypdf; everything stays on the device)
# --------------------------------------------------------------------------
PDF_ZIP_LEVELS = {"low": (80, 2400), "medium": (62, 1700), "high": (42, 1200)}


def _pdf_open(path):
    """Open a PDF; empty-password encrypted files are unlocked. Raises ValueError('encrypted') / ValueError('bad')."""
    try:
        r = _pypdf.PdfReader(path)
    except Exception:
        raise ValueError("bad")
    try:
        if r.is_encrypted:
            ok = 0
            try:
                ok = r.decrypt("")
            except Exception:
                ok = 0
            if not ok:
                raise ValueError("encrypted")
        len(r.pages)
    except ValueError:
        raise
    except Exception:
        raise ValueError("bad")
    return r


def pdf_info(path):
    """(page_count, state) where state is 'ok' | 'encrypted' | 'bad'."""
    if not HAS_PYPDF:
        return 0, "bad"
    try:
        r = _pdf_open(path)
        return len(r.pages), "ok"
    except ValueError as e:
        return 0, str(e) if str(e) in ("encrypted", "bad") else "bad"
    except Exception:
        return 0, "bad"


def pdf_merge(paths, out_path, progress=None):
    """Join PDFs in the given order. Returns (pages_written, skipped_count)."""
    w = _pypdf.PdfWriter()
    pages = 0
    skipped = 0
    n = len(paths)
    for i, p in enumerate(paths):
        if progress:
            progress(i + 1, n)
        try:
            r = _pdf_open(p)
            for page in r.pages:
                w.add_page(page)
                pages += 1
        except Exception:
            skipped += 1
    if pages == 0:
        raise ValueError("nothing to merge")
    tmp = out_path + ".part"
    try:
        with open(tmp, "wb") as f:
            w.write(f)
        os.replace(tmp, out_path)
    finally:
        if os.path.exists(tmp):
            try:
                os.remove(tmp)
            except Exception:
                pass
    return pages, skipped


def pdf_compress(src, out_path, level="medium", progress=None):
    """Shrink a PDF: images are re-encoded (JPEG, smaller dimensions) + streams/objects are deduplicated.
    Returns (original_size, new_size, pages)."""
    quality, max_px = PDF_ZIP_LEVELS.get(level, PDF_ZIP_LEVELS["medium"])
    reader = _pdf_open(src)
    try:
        writer = _pypdf.PdfWriter(clone_from=reader)
    except TypeError:
        writer = _pypdf.PdfWriter()
        for pg in reader.pages:
            writer.add_page(pg)
    pages = list(writer.pages)
    n = len(pages)
    done_ids = set()
    resample = LANCZOS
    for pi, page in enumerate(pages):
        if progress:
            progress(pi + 1, n)
        try:
            imgs = list(page.images)
        except Exception:
            imgs = []
        for img in imgs:
            try:
                ref = img.indirect_reference
                if ref is None or ref.idnum in done_ids:
                    continue
                done_ids.add(ref.idnum)
                obj = ref.get_object()
                if "/SMask" in obj or "/Mask" in obj or obj.get("/ImageMask"):
                    continue                              # keep transparency exactly as it is
                pil = img.image
                if pil is None:
                    continue
                w0, h0 = pil.size
                if w0 * h0 < 120 * 120:
                    continue
                try:
                    orig_len = len(obj._data)
                except Exception:
                    orig_len = len(img.data)
                if pil.mode not in ("RGB", "L"):
                    if pil.mode == "1":
                        continue
                    pil = pil.convert("RGB")
                if max(w0, h0) > max_px:
                    pil = pil.copy()
                    pil.thumbnail((max_px, max_px), resample)
                b = io.BytesIO()
                pil.save(b, "JPEG", quality=quality, optimize=True)
                if b.tell() < orig_len * 0.92:
                    img.replace(pil, quality=quality)
            except Exception:
                continue
        try:
            page.compress_content_streams()
        except Exception:
            pass
    try:
        writer.compress_identical_objects(remove_identicals=True, remove_orphans=True)
    except Exception:
        pass
    tmp = out_path + ".part"
    try:
        with open(tmp, "wb") as f:
            writer.write(f)
        os.replace(tmp, out_path)
    finally:
        if os.path.exists(tmp):
            try:
                os.remove(tmp)
            except Exception:
                pass
    return os.path.getsize(src), os.path.getsize(out_path), n


# --------------------------------------------------------------------------
# Text tools
# --------------------------------------------------------------------------
_LINE_SPLIT_RE = re.compile("\r\n|[\r\n\x0b\x0c\x1c\x1d\x1e\x85\u2028\u2029]")


def norm_newlines(s):
    """CR, CRLF, U+2028 ... (what pasted text often contains) -> plain LF."""
    return _LINE_SPLIT_RE.sub("\n", s or "")


def text_stats(s):
    """-> (words, letters, digits, symbols, spaces, lines).
    Letters never include spaces. Spaces are the ones inside a line: blanks at the very start or
    end of a line (invisible, often left by copy/paste) are not counted."""
    s = norm_newlines(s)
    words = len(re.findall(r"\S+", s))
    letters = digits = symbols = 0
    for ch in s:
        if ch == "\n" or ch.isspace():
            continue
        cat = unicodedata.category(ch)
        if cat[0] == "M" or cat == "Cf":      # diacritics / invisible marks are not counted
            continue
        if ch.isalpha():
            letters += 1
        elif ch.isdigit():
            digits += 1
        else:
            symbols += 1
    spaces = 0
    for ln in s.split("\n"):
        spaces += sum(1 for ch in ln.strip() if ch.isspace())
    lines = 0 if not s else s.count("\n") + 1
    return words, letters, digits, symbols, spaces, lines


def tx_dedupe(s):
    seen, out, removed = set(), [], 0
    for ln in norm_newlines(s).split("\n"):
        key = ln.strip()
        if key and key in seen:
            removed += 1
            continue
        if key:
            seen.add(key)
        out.append(ln)
    return "\n".join(out), removed


def tx_clean_spaces(s):
    s = norm_newlines(s).replace("\u00a0", " ").replace("\u200b", "").replace("\ufeff", "").replace("\t", " ")
    s = re.sub(r" {2,}", " ", s)
    s = "\n".join(ln.strip() for ln in s.split("\n"))
    s = re.sub(r"\n{3,}", "\n\n", s)
    return s.strip()


def tx_remove_empty(s):
    return "\n".join(ln for ln in norm_newlines(s).split("\n") if ln.strip())


def tx_sort(s):
    return "\n".join(sorted(norm_newlines(s).split("\n"), key=lambda x: norm_search(x)))


def tx_strip_tashkeel(s):
    return TASHKEEL_RE.sub("", s)


# --------------------------------------------------------------------------
# Sound effects (synthesised, no asset files)
# --------------------------------------------------------------------------
_SR = 22050


def _tone(freq, ms, vol=0.8, decay=7.0, harm=0.25, f_end=None):
    n = int(_SR * ms / 1000.0)
    out = []
    phase = 0.0
    for i in range(n):
        t = i / float(n)
        f = freq if f_end is None else freq + (f_end - freq) * t
        phase += 2 * math.pi * f / _SR
        env = math.exp(-decay * t) * min(1.0, i / (_SR * 0.002 + 1))
        s = math.sin(phase) + harm * math.sin(2 * phase)
        out.append(s * env * vol / (1 + harm))
    return out


def _gap(ms):
    return [0.0] * int(_SR * ms / 1000.0)


SFX_DEFS = {
    "click": lambda: _tone(1500, 32, 0.55, 9.0),
    "tap": lambda: _tone(980, 26, 0.5, 8.0),
    "nav": lambda: _tone(720, 28, 0.5, 7.0) + _tone(1080, 34, 0.45, 8.0),
    "on": lambda: _tone(760, 40, 0.5, 6.0) + _tone(1180, 70, 0.5, 6.0),
    "off": lambda: _tone(1180, 40, 0.5, 6.0) + _tone(760, 70, 0.5, 6.0),
    "success": lambda: _tone(660, 70, 0.55, 5.0) + _tone(880, 70, 0.55, 5.0) + _tone(1175, 170, 0.55, 5.5),
    "error": lambda: _tone(330, 110, 0.6, 4.0, 0.4) + _gap(10) + _tone(220, 190, 0.6, 4.5, 0.4),
    "pop": lambda: _tone(420, 90, 0.6, 5.0, 0.1, f_end=980),
}


def write_wav(path, samples):
    with wave.open(path, "wb") as w:
        w.setnchannels(1)
        w.setsampwidth(2)
        w.setframerate(_SR)
        frames = bytearray()
        for s in samples:
            v = max(-1.0, min(1.0, s))
            frames += struct.pack("<h", int(v * 30000))
        w.writeframes(bytes(frames))


def ensure_sfx(folder):
    os.makedirs(folder, exist_ok=True)
    paths = {}
    for name, fn in SFX_DEFS.items():
        p = os.path.join(folder, "idda_%s.wav" % name)
        if not os.path.isfile(p) or os.path.getsize(p) < 100:
            try:
                write_wav(p, fn())
            except Exception:
                continue
        paths[name] = p
    return paths


# --------------------------------------------------------------------------
# Icons (drawn with Pillow, so no image assets are needed)
# --------------------------------------------------------------------------
class _Pen:
    def __init__(self, d, n, w, col):
        self.d, self.n, self.w, self.col = d, n, w, col

    def _p(self, pts):
        return [(x * self.n, y * self.n) for x, y in pts]

    def line(self, pts, close=False):
        pts = self._p(pts)
        if close:
            pts = pts + [pts[0]]
        for a, b in zip(pts, pts[1:]):
            self.d.line([a, b], fill=self.col, width=self.w)
        r = self.w / 2.0
        for x, y in pts:
            self.d.ellipse([x - r, y - r, x + r, y + r], fill=self.col)

    def circ(self, cx, cy, r, fill=False):
        h = 0 if fill else self.w / 2.0 / self.n
        box = [(cx - r - h) * self.n, (cy - r - h) * self.n, (cx + r + h) * self.n, (cy + r + h) * self.n]
        if fill:
            self.d.ellipse(box, fill=self.col)
        else:
            self.d.ellipse(box, outline=self.col, width=self.w)

    def ell(self, cx, cy, rx, ry):
        h = self.w / 2.0 / self.n
        box = [(cx - rx - h) * self.n, (cy - ry - h) * self.n, (cx + rx + h) * self.n, (cy + ry + h) * self.n]
        self.d.ellipse(box, outline=self.col, width=self.w)

    def rrect(self, x0, y0, x1, y1, r, fill=False):
        h = 0 if fill else self.w / 2.0 / self.n
        box = [(x0 - h) * self.n, (y0 - h) * self.n, (x1 + h) * self.n, (y1 + h) * self.n]
        if fill:
            self.d.rounded_rectangle(box, radius=r * self.n, fill=self.col)
        else:
            self.d.rounded_rectangle(box, radius=r * self.n, outline=self.col, width=self.w)

    def arc(self, cx, cy, r, a0, a1):
        h = self.w / 2.0 / self.n
        box = [(cx - r - h) * self.n, (cy - r - h) * self.n, (cx + r + h) * self.n, (cy + r + h) * self.n]
        self.d.arc(box, a0, a1, fill=self.col, width=self.w)

    def fillpoly(self, pts):
        self.d.polygon(self._p(pts), fill=self.col)


def _heart_pts(n=72):
    pts = []
    for i in range(n):
        t = 2 * math.pi * i / n
        x = 16 * math.sin(t) ** 3
        y = 13 * math.cos(t) - 5 * math.cos(2 * t) - 2 * math.cos(3 * t) - math.cos(4 * t)
        pts.append((0.5 + x / 16.0 * 0.37, 0.5 - (y + 2.5) / 14.5 * 0.36))
    return pts


def _gear_pts(teeth=8, r_in=0.29, r_out=0.39):
    pts = []
    step = 2 * math.pi / teeth
    for i in range(teeth):
        a = i * step
        for da, r in ((-0.5, r_in), (-0.22, r_out), (0.22, r_out), (0.5, r_in)):
            ang = a + da * step
            pts.append((0.5 + r * math.cos(ang), 0.5 + r * math.sin(ang)))
    return pts


def _ic_home(p):
    p.line([(0.14, 0.47), (0.5, 0.17), (0.86, 0.47)])
    p.line([(0.25, 0.4), (0.25, 0.82), (0.75, 0.82), (0.75, 0.4)])
    p.line([(0.42, 0.82), (0.42, 0.6), (0.58, 0.6), (0.58, 0.82)])


def _ic_history(p):
    p.circ(0.5, 0.5, 0.36)
    p.line([(0.5, 0.27), (0.5, 0.5), (0.66, 0.6)])


def _ic_heart(p):
    p.line(_heart_pts(), close=True)


def _ic_heart_fill(p):
    p.fillpoly(_heart_pts())
    p.line(_heart_pts(), close=True)


def _ic_gear(p):
    p.line(_gear_pts(), close=True)
    p.circ(0.5, 0.5, 0.12)


def _ic_search(p):
    p.circ(0.44, 0.44, 0.27)
    p.line([(0.64, 0.64), (0.84, 0.84)])


def _ic_wrench(p):
    # spanner outline (sampled from a 24-grid path)
    p.line([(0.612, 0.263), (0.611, 0.264), (0.61, 0.265), (0.609, 0.266), (0.608, 0.267), (0.607, 0.269), (0.607, 0.27), (0.606, 0.272), (0.605, 0.273), (0.604, 0.274), (0.604, 0.276), (0.603, 0.277), (0.603, 0.279), (0.602, 0.28), (0.602, 0.282), (0.601, 0.284), (0.601, 0.285), (0.601, 0.287), (0.601, 0.288), (0.601, 0.29), (0.601, 0.292), (0.601, 0.293), (0.601, 0.295), (0.601, 0.297), (0.601, 0.298), (0.601, 0.3), (0.602, 0.301), (0.602, 0.303), (0.603, 0.304), (0.603, 0.306), (0.604, 0.307), (0.604, 0.309), (0.605, 0.31), (0.606, 0.312), (0.607, 0.313), (0.607, 0.315), (0.608, 0.316), (0.609, 0.317), (0.61, 0.318), (0.611, 0.32), (0.612, 0.321), (0.618, 0.326), (0.623, 0.331), (0.628, 0.336), (0.633, 0.341), (0.638, 0.346), (0.643, 0.352), (0.648, 0.357), (0.654, 0.362), (0.659, 0.367), (0.664, 0.372), (0.669, 0.377), (0.674, 0.382), (0.679, 0.387), (0.68, 0.389), (0.682, 0.39), (0.683, 0.391), (0.684, 0.392), (0.685, 0.393), (0.687, 0.393), (0.688, 0.394), (0.69, 0.395), (0.691, 0.396), (0.693, 0.396), (0.694, 0.397), (0.696, 0.397), (0.697, 0.398), (0.699, 0.398), (0.7, 0.399), (0.702, 0.399), (0.703, 0.399), (0.705, 0.399), (0.707, 0.399), (0.708, 0.399), (0.71, 0.399), (0.712, 0.399), (0.713, 0.399), (0.715, 0.399), (0.716, 0.399), (0.718, 0.398), (0.72, 0.398), (0.721, 0.397), (0.723, 0.397), (0.724, 0.396), (0.726, 0.396), (0.727, 0.395), (0.728, 0.394), (0.73, 0.393), (0.731, 0.393), (0.733, 0.392), (0.734, 0.391), (0.735, 0.39), (0.736, 0.389), (0.737, 0.387), (0.743, 0.382), (0.748, 0.377), (0.753, 0.372), (0.758, 0.367), (0.763, 0.362), (0.768, 0.357), (0.773, 0.352), (0.778, 0.347), (0.783, 0.342), (0.788, 0.337), (0.793, 0.332), (0.798, 0.327), (0.803, 0.322), (0.808, 0.317), (0.814, 0.311), (0.819, 0.306), (0.824, 0.301), (0.829, 0.296), (0.834, 0.291), (0.839, 0.286), (0.844, 0.281), (0.849, 0.276), (0.854, 0.271), (0.859, 0.266), (0.864, 0.261), (0.869, 0.256), (0.874, 0.251), (0.879, 0.246), (0.884, 0.241), (0.89, 0.235), (0.895, 0.23), (0.9, 0.244), (0.905, 0.259), (0.909, 0.273), (0.913, 0.288), (0.915, 0.303), (0.916, 0.318), (0.917, 0.333), (0.916, 0.348), (0.915, 0.363), (0.913, 0.378), (0.91, 0.393), (0.906, 0.408), (0.901, 0.422), (0.895, 0.436), (0.888, 0.45), (0.881, 0.463), (0.873, 0.475), (0.864, 0.488), (0.854, 0.499), (0.844, 0.51), (0.833, 0.521), (0.821, 0.53), (0.809, 0.539), (0.796, 0.547), (0.783, 0.555), (0.769, 0.562), (0.755, 0.567), (0.741, 0.572), (0.726, 0.576), (0.712, 0.579), (0.697, 0.582), (0.682, 0.583), (0.666, 0.583), (0.651, 0.583), (0.636, 0.582), (0.621, 0.579), (0.607, 0.576), (0.592, 0.572), (0.578, 0.567), (0.564, 0.561), (0.559, 0.566), (0.554, 0.571), (0.549, 0.576), (0.544, 0.581), (0.539, 0.586), (0.534, 0.591), (0.529, 0.596), (0.524, 0.601), (0.519, 0.606), (0.514, 0.611), (0.509, 0.616), (0.504, 0.621), (0.499, 0.626), (0.494, 0.631), (0.489, 0.636), (0.484, 0.641), (0.479, 0.646), (0.474, 0.651), (0.469, 0.656), (0.464, 0.661), (0.46, 0.665), (0.455, 0.67), (0.45, 0.675), (0.445, 0.68), (0.44, 0.685), (0.435, 0.69), (0.43, 0.695), (0.425, 0.7), (0.42, 0.705), (0.415, 0.71), (0.41, 0.715), (0.405, 0.72), (0.4, 0.725), (0.395, 0.73), (0.39, 0.735), (0.385, 0.74), (0.38, 0.745), (0.375, 0.75), (0.37, 0.755), (0.365, 0.76), (0.36, 0.765), (0.355, 0.77), (0.35, 0.775), (0.345, 0.78), (0.34, 0.785), (0.335, 0.79), (0.33, 0.795), (0.325, 0.8), (0.321, 0.804), (0.316, 0.809), (0.311, 0.814), (0.306, 0.819), (0.301, 0.824), (0.296, 0.829), (0.291, 0.834), (0.286, 0.839), (0.281, 0.844), (0.276, 0.849), (0.271, 0.854), (0.265, 0.858), (0.26, 0.862), (0.253, 0.865), (0.247, 0.868), (0.241, 0.871), (0.234, 0.873), (0.227, 0.874), (0.22, 0.875), (0.213, 0.875), (0.206, 0.875), (0.2, 0.874), (0.193, 0.873), (0.186, 0.871), (0.18, 0.868), (0.173, 0.865), (0.167, 0.862), (0.161, 0.858), (0.156, 0.854), (0.151, 0.849), (0.146, 0.844), (0.142, 0.839), (0.138, 0.833), (0.135, 0.827), (0.132, 0.82), (0.129, 0.814), (0.127, 0.807), (0.126, 0.8), (0.125, 0.794), (0.125, 0.787), (0.125, 0.78), (0.126, 0.773), (0.127, 0.766), (0.129, 0.759), (0.132, 0.753), (0.135, 0.747), (0.138, 0.74), (0.142, 0.735), (0.146, 0.729), (0.151, 0.724), (0.156, 0.719), (0.161, 0.714), (0.166, 0.709), (0.171, 0.704), (0.176, 0.699), (0.181, 0.694), (0.186, 0.689), (0.191, 0.684), (0.196, 0.679), (0.2, 0.675), (0.205, 0.67), (0.21, 0.665), (0.215, 0.66), (0.22, 0.655), (0.225, 0.65), (0.23, 0.645), (0.235, 0.64), (0.24, 0.635), (0.245, 0.63), (0.25, 0.625), (0.255, 0.62), (0.26, 0.615), (0.265, 0.61), (0.27, 0.605), (0.275, 0.6), (0.28, 0.595), (0.285, 0.59), (0.29, 0.585), (0.295, 0.58), (0.3, 0.575), (0.305, 0.57), (0.31, 0.565), (0.315, 0.56), (0.32, 0.555), (0.325, 0.55), (0.33, 0.545), (0.335, 0.54), (0.339, 0.536), (0.344, 0.531), (0.349, 0.526), (0.354, 0.521), (0.359, 0.516), (0.364, 0.511), (0.369, 0.506), (0.374, 0.501), (0.379, 0.496), (0.384, 0.491), (0.389, 0.486), (0.394, 0.481), (0.399, 0.476), (0.404, 0.471), (0.409, 0.466), (0.414, 0.461), (0.419, 0.456), (0.424, 0.451), (0.429, 0.446), (0.434, 0.441), (0.439, 0.436), (0.433, 0.422), (0.428, 0.408), (0.424, 0.393), (0.421, 0.379), (0.418, 0.364), (0.417, 0.349), (0.417, 0.334), (0.417, 0.318), (0.418, 0.303), (0.421, 0.288), (0.424, 0.274), (0.428, 0.259), (0.433, 0.245), (0.438, 0.231), (0.445, 0.217), (0.453, 0.204), (0.461, 0.191), (0.47, 0.179), (0.479, 0.167), (0.49, 0.156), (0.501, 0.146), (0.512, 0.136), (0.525, 0.127), (0.537, 0.119), (0.55, 0.112), (0.564, 0.105), (0.578, 0.099), (0.592, 0.094), (0.607, 0.09), (0.622, 0.087), (0.637, 0.085), (0.652, 0.084), (0.667, 0.083), (0.682, 0.084), (0.697, 0.085), (0.712, 0.087), (0.727, 0.091), (0.741, 0.095), (0.756, 0.1), (0.77, 0.105), (0.765, 0.11), (0.759, 0.116), (0.754, 0.121), (0.749, 0.126), (0.744, 0.131), (0.739, 0.136), (0.734, 0.141), (0.729, 0.146), (0.724, 0.151), (0.719, 0.156), (0.714, 0.161), (0.709, 0.166), (0.704, 0.171), (0.699, 0.176), (0.694, 0.181), (0.689, 0.186), (0.684, 0.191), (0.679, 0.196), (0.674, 0.201), (0.669, 0.206), (0.663, 0.212), (0.658, 0.217), (0.653, 0.222), (0.648, 0.227), (0.643, 0.232), (0.638, 0.237), (0.633, 0.242), (0.628, 0.247), (0.623, 0.252), (0.618, 0.257), (0.613, 0.262)], close=True)


def _ic_image(p):
    # stacked photos
    p.rrect(0.25, 0.083, 0.917, 0.75, 0.083)
    p.circ(0.5, 0.333, 0.083)
    p.line([(0.75, 0.917), (0.743, 0.917), (0.736, 0.917), (0.729, 0.917), (0.722, 0.917), (0.715, 0.917), (0.708, 0.917), (0.701, 0.917), (0.694, 0.917), (0.688, 0.917), (0.681, 0.917), (0.674, 0.917), (0.667, 0.917), (0.66, 0.917), (0.653, 0.917), (0.646, 0.917), (0.639, 0.917), (0.632, 0.917), (0.625, 0.917), (0.618, 0.917), (0.611, 0.917), (0.604, 0.917), (0.597, 0.917), (0.59, 0.917), (0.583, 0.917), (0.576, 0.917), (0.569, 0.917), (0.562, 0.917), (0.556, 0.917), (0.549, 0.917), (0.542, 0.917), (0.535, 0.917), (0.528, 0.917), (0.521, 0.917), (0.514, 0.917), (0.507, 0.917), (0.5, 0.917), (0.493, 0.917), (0.486, 0.917), (0.479, 0.917), (0.472, 0.917), (0.465, 0.917), (0.458, 0.917), (0.451, 0.917), (0.444, 0.917), (0.438, 0.917), (0.431, 0.917), (0.424, 0.917), (0.417, 0.917), (0.41, 0.917), (0.403, 0.917), (0.396, 0.917), (0.389, 0.917), (0.382, 0.917), (0.375, 0.917), (0.368, 0.917), (0.361, 0.917), (0.354, 0.917), (0.347, 0.917), (0.34, 0.917), (0.333, 0.917), (0.326, 0.917), (0.319, 0.917), (0.312, 0.917), (0.306, 0.917), (0.299, 0.917), (0.292, 0.917), (0.285, 0.917), (0.278, 0.917), (0.271, 0.917), (0.264, 0.917), (0.257, 0.917), (0.25, 0.917), (0.243, 0.917), (0.236, 0.917), (0.229, 0.917), (0.222, 0.917), (0.215, 0.917), (0.208, 0.917), (0.201, 0.917), (0.194, 0.917), (0.188, 0.917), (0.181, 0.917), (0.174, 0.917), (0.167, 0.917), (0.161, 0.916), (0.156, 0.916), (0.15, 0.915), (0.145, 0.914), (0.14, 0.912), (0.135, 0.91), (0.13, 0.908), (0.125, 0.906), (0.12, 0.903), (0.116, 0.899), (0.112, 0.896), (0.108, 0.892), (0.104, 0.888), (0.101, 0.884), (0.097, 0.88), (0.094, 0.875), (0.092, 0.87), (0.09, 0.865), (0.088, 0.86), (0.086, 0.855), (0.085, 0.85), (0.084, 0.844), (0.084, 0.839), (0.083, 0.833), (0.083, 0.826), (0.083, 0.819), (0.083, 0.812), (0.083, 0.806), (0.083, 0.799), (0.083, 0.792), (0.083, 0.785), (0.083, 0.778), (0.083, 0.771), (0.083, 0.764), (0.083, 0.757), (0.083, 0.75), (0.083, 0.743), (0.083, 0.736), (0.083, 0.729), (0.083, 0.722), (0.083, 0.715), (0.083, 0.708), (0.083, 0.701), (0.083, 0.694), (0.083, 0.688), (0.083, 0.681), (0.083, 0.674), (0.083, 0.667), (0.083, 0.66), (0.083, 0.653), (0.083, 0.646), (0.083, 0.639), (0.083, 0.632), (0.083, 0.625), (0.083, 0.618), (0.083, 0.611), (0.083, 0.604), (0.083, 0.597), (0.083, 0.59), (0.083, 0.583), (0.083, 0.576), (0.083, 0.569), (0.083, 0.562), (0.083, 0.556), (0.083, 0.549), (0.083, 0.542), (0.083, 0.535), (0.083, 0.528), (0.083, 0.521), (0.083, 0.514), (0.083, 0.507), (0.083, 0.5), (0.083, 0.493), (0.083, 0.486), (0.083, 0.479), (0.083, 0.472), (0.083, 0.465), (0.083, 0.458), (0.083, 0.451), (0.083, 0.444), (0.083, 0.438), (0.083, 0.431), (0.083, 0.424), (0.083, 0.417), (0.083, 0.41), (0.083, 0.403), (0.083, 0.396), (0.083, 0.389), (0.083, 0.382), (0.083, 0.375), (0.083, 0.368), (0.083, 0.361), (0.083, 0.354), (0.083, 0.347), (0.083, 0.34), (0.083, 0.333), (0.083, 0.326), (0.083, 0.319), (0.083, 0.312), (0.083, 0.306), (0.083, 0.299), (0.083, 0.292), (0.083, 0.285), (0.083, 0.278), (0.083, 0.271), (0.083, 0.264), (0.083, 0.257), (0.083, 0.25)])
    p.line([(0.917, 0.542), (0.912, 0.537), (0.907, 0.533), (0.901, 0.529), (0.896, 0.526), (0.89, 0.523), (0.884, 0.52), (0.878, 0.518), (0.872, 0.516), (0.865, 0.514), (0.859, 0.513), (0.852, 0.512), (0.846, 0.512), (0.839, 0.512), (0.833, 0.513), (0.826, 0.514), (0.82, 0.516), (0.813, 0.518), (0.807, 0.52), (0.801, 0.523), (0.795, 0.526), (0.79, 0.529), (0.785, 0.533), (0.779, 0.537), (0.775, 0.542), (0.769, 0.546), (0.763, 0.549), (0.757, 0.553), (0.751, 0.557), (0.745, 0.561), (0.74, 0.565), (0.734, 0.569), (0.728, 0.573), (0.722, 0.576), (0.716, 0.58), (0.71, 0.584), (0.704, 0.588), (0.699, 0.592), (0.693, 0.596), (0.687, 0.6), (0.681, 0.603), (0.675, 0.607), (0.669, 0.611), (0.663, 0.615), (0.658, 0.619), (0.652, 0.623), (0.646, 0.627), (0.64, 0.63), (0.634, 0.634), (0.628, 0.638), (0.622, 0.642), (0.616, 0.646), (0.611, 0.65), (0.605, 0.654), (0.599, 0.657), (0.593, 0.661), (0.587, 0.665), (0.581, 0.669), (0.575, 0.673), (0.57, 0.677), (0.564, 0.681), (0.558, 0.684), (0.552, 0.688), (0.546, 0.692), (0.54, 0.696), (0.534, 0.7), (0.529, 0.704), (0.523, 0.708), (0.517, 0.711), (0.511, 0.715), (0.505, 0.719), (0.499, 0.723), (0.493, 0.727), (0.488, 0.731), (0.482, 0.735), (0.476, 0.738), (0.47, 0.742), (0.464, 0.746), (0.458, 0.75)])


def _ic_qr(p):
    for (x, y) in ((3, 3), (16, 3), (3, 16)):
        p.rrect(x / 24.0, y / 24.0, (x + 5) / 24.0, (y + 5) / 24.0, 0.04)
    p.line([(0.875, 0.667), (0.868, 0.667), (0.861, 0.667), (0.854, 0.667), (0.847, 0.667), (0.84, 0.667), (0.833, 0.667), (0.826, 0.667), (0.819, 0.667), (0.812, 0.667), (0.806, 0.667), (0.799, 0.667), (0.792, 0.667), (0.785, 0.667), (0.778, 0.667), (0.771, 0.667), (0.764, 0.667), (0.757, 0.667), (0.75, 0.667), (0.745, 0.667), (0.739, 0.667), (0.734, 0.668), (0.728, 0.67), (0.723, 0.671), (0.718, 0.673), (0.713, 0.675), (0.708, 0.678), (0.704, 0.681), (0.699, 0.684), (0.695, 0.687), (0.691, 0.691), (0.687, 0.695), (0.684, 0.699), (0.681, 0.704), (0.678, 0.708), (0.675, 0.713), (0.673, 0.718), (0.671, 0.723), (0.67, 0.728), (0.668, 0.734), (0.667, 0.739), (0.667, 0.745), (0.667, 0.75), (0.667, 0.757), (0.667, 0.764), (0.667, 0.771), (0.667, 0.778), (0.667, 0.785), (0.667, 0.792), (0.667, 0.799), (0.667, 0.806), (0.667, 0.812), (0.667, 0.819), (0.667, 0.826), (0.667, 0.833), (0.667, 0.84), (0.667, 0.847), (0.667, 0.854), (0.667, 0.861), (0.667, 0.868), (0.667, 0.875)])
    p.line([(0.875, 0.875), (0.875, 0.875)])
    p.line([(0.5, 0.292), (0.5, 0.299), (0.5, 0.306), (0.5, 0.312), (0.5, 0.319), (0.5, 0.326), (0.5, 0.333), (0.5, 0.34), (0.5, 0.347), (0.5, 0.354), (0.5, 0.361), (0.5, 0.368), (0.5, 0.375), (0.5, 0.382), (0.5, 0.389), (0.5, 0.396), (0.5, 0.403), (0.5, 0.41), (0.5, 0.417), (0.5, 0.422), (0.499, 0.428), (0.498, 0.433), (0.497, 0.438), (0.496, 0.443), (0.494, 0.449), (0.491, 0.454), (0.489, 0.458), (0.486, 0.463), (0.483, 0.467), (0.479, 0.472), (0.476, 0.476), (0.472, 0.479), (0.467, 0.483), (0.463, 0.486), (0.458, 0.489), (0.454, 0.491), (0.449, 0.494), (0.443, 0.496), (0.438, 0.497), (0.433, 0.498), (0.428, 0.499), (0.422, 0.5), (0.417, 0.5), (0.41, 0.5), (0.403, 0.5), (0.396, 0.5), (0.389, 0.5), (0.382, 0.5), (0.375, 0.5), (0.368, 0.5), (0.361, 0.5), (0.354, 0.5), (0.347, 0.5), (0.34, 0.5), (0.333, 0.5), (0.326, 0.5), (0.319, 0.5), (0.312, 0.5), (0.306, 0.5), (0.299, 0.5), (0.292, 0.5)])
    p.line([(0.125, 0.5), (0.125, 0.5)])
    p.line([(0.5, 0.125), (0.5, 0.125)])
    p.line([(0.5, 0.667), (0.5, 0.667)])
    p.line([(0.667, 0.5), (0.674, 0.5), (0.681, 0.5), (0.688, 0.5), (0.694, 0.5), (0.701, 0.5), (0.708, 0.5)])
    p.line([(0.875, 0.5), (0.875, 0.5)])
    p.line([(0.5, 0.875), (0.5, 0.868), (0.5, 0.861), (0.5, 0.854), (0.5, 0.847), (0.5, 0.84), (0.5, 0.833)])


def _ic_text(p):
    p.line([(0.2, 0.2), (0.8, 0.2)])
    p.line([(0.2, 0.2), (0.2, 0.3)])
    p.line([(0.8, 0.2), (0.8, 0.3)])
    p.line([(0.5, 0.2), (0.5, 0.82)])
    p.line([(0.38, 0.82), (0.62, 0.82)])


def _ic_doc(p):
    p.rrect(0.2, 0.14, 0.8, 0.86, 0.1)
    p.line([(0.34, 0.4), (0.66, 0.4)])
    p.line([(0.34, 0.6), (0.58, 0.6)])


def _ic_shield(p):
    p.line([(0.5, 0.12), (0.82, 0.25), (0.82, 0.5), (0.5, 0.88), (0.18, 0.5), (0.18, 0.25)], close=True)
    p.line([(0.36, 0.5), (0.46, 0.6), (0.66, 0.4)])


def _ic_back(p):
    p.line([(0.8, 0.5), (0.22, 0.5)])
    p.line([(0.48, 0.22), (0.2, 0.5), (0.48, 0.78)])


def _ic_camera(p):
    p.rrect(0.12, 0.28, 0.88, 0.8, 0.09)
    p.line([(0.36, 0.28), (0.42, 0.18), (0.58, 0.18), (0.64, 0.28)])
    p.circ(0.5, 0.54, 0.15)


def _ic_share(p):
    p.circ(0.28, 0.5, 0.085)
    p.circ(0.72, 0.26, 0.085)
    p.circ(0.72, 0.74, 0.085)
    p.line([(0.35, 0.46), (0.65, 0.3)])
    p.line([(0.35, 0.54), (0.65, 0.7)])


def _ic_copy(p):
    p.rrect(0.34, 0.12, 0.84, 0.64, 0.08)
    p.line([(0.24, 0.3), (0.2, 0.3), (0.16, 0.34), (0.16, 0.84), (0.2, 0.88), (0.64, 0.88), (0.68, 0.84), (0.68, 0.8)])


def _ic_save(p):
    p.line([(0.5, 0.14), (0.5, 0.6)])
    p.line([(0.3, 0.42), (0.5, 0.62), (0.7, 0.42)])
    p.line([(0.16, 0.62), (0.16, 0.84), (0.84, 0.84), (0.84, 0.62)])


def _ic_trash(p):
    p.line([(0.18, 0.28), (0.82, 0.28)])
    p.line([(0.4, 0.28), (0.4, 0.17), (0.6, 0.17), (0.6, 0.28)])
    p.line([(0.27, 0.28), (0.31, 0.84), (0.69, 0.84), (0.73, 0.28)])
    p.line([(0.44, 0.45), (0.44, 0.68)])
    p.line([(0.56, 0.45), (0.56, 0.68)])


def _ic_up(p):
    p.line([(0.22, 0.62), (0.5, 0.34), (0.78, 0.62)])


def _ic_down(p):
    p.line([(0.22, 0.38), (0.5, 0.66), (0.78, 0.38)])


def _ic_plus(p):
    p.line([(0.5, 0.2), (0.5, 0.8)])
    p.line([(0.2, 0.5), (0.8, 0.5)])


def _ic_close(p):
    p.line([(0.24, 0.24), (0.76, 0.76)])
    p.line([(0.76, 0.24), (0.24, 0.76)])


def _ic_check(p):
    p.line([(0.2, 0.52), (0.42, 0.74), (0.82, 0.28)])


def _ic_link(p):
    p.line([(0.46, 0.22), (0.2, 0.22), (0.2, 0.8), (0.78, 0.8), (0.78, 0.54)])
    p.line([(0.56, 0.16), (0.84, 0.16), (0.84, 0.44)])
    p.line([(0.84, 0.16), (0.48, 0.52)])


def _ic_globe(p):
    p.circ(0.5, 0.5, 0.36)
    p.ell(0.5, 0.5, 0.15, 0.36)
    p.line([(0.14, 0.5), (0.86, 0.5)])


def _ic_volume(p):
    p.line([(0.16, 0.4), (0.3, 0.4), (0.5, 0.22), (0.5, 0.78), (0.3, 0.6), (0.16, 0.6)], close=True)
    p.arc(0.5, 0.5, 0.18, -50, 50)
    p.arc(0.5, 0.5, 0.31, -50, 50)


def _ic_vibrate(p):
    p.rrect(0.36, 0.16, 0.64, 0.84, 0.07)
    p.line([(0.2, 0.34), (0.2, 0.66)])
    p.line([(0.8, 0.34), (0.8, 0.66)])
    p.line([(0.09, 0.42), (0.09, 0.58)])
    p.line([(0.91, 0.42), (0.91, 0.58)])


def _ic_info(p):
    p.circ(0.5, 0.5, 0.36)
    p.line([(0.5, 0.46), (0.5, 0.68)])
    p.circ(0.5, 0.32, 0.03, fill=True)


def _ic_paste(p):
    p.rrect(0.2, 0.2, 0.8, 0.86, 0.08)
    p.rrect(0.36, 0.1, 0.64, 0.28, 0.05)
    p.line([(0.34, 0.5), (0.66, 0.5)])
    p.line([(0.34, 0.68), (0.56, 0.68)])


def _ic_undo(p):
    p.line([(0.36, 0.24), (0.2, 0.4), (0.36, 0.56)])
    p.line([(0.2, 0.4), (0.62, 0.4)])
    p.arc(0.62, 0.58, 0.18, -90, 90)


def _ic_rotate(p):
    p.arc(0.5, 0.5, 0.3, 40, 340)
    p.line([(0.8, 0.2), (0.82, 0.4), (0.62, 0.38)])


def _ic_warn(p):
    p.line([(0.5, 0.14), (0.88, 0.8), (0.12, 0.8)], close=True)
    p.line([(0.5, 0.4), (0.5, 0.58)])
    p.circ(0.5, 0.69, 0.025, fill=True)


def _ic_phone(p):
    p.rrect(0.3, 0.1, 0.7, 0.9, 0.09)
    p.line([(0.44, 0.78), (0.56, 0.78)])


def _ic_mail(p):
    p.rrect(0.12, 0.24, 0.88, 0.76, 0.07)
    p.line([(0.14, 0.3), (0.5, 0.56), (0.86, 0.3)])


def _ic_wifi(p):
    p.arc(0.5, 0.78, 0.46, 225, 315)
    p.arc(0.5, 0.78, 0.29, 225, 315)
    p.circ(0.5, 0.78, 0.045, fill=True)


def _ic_folder(p):
    p.line([(0.12, 0.28), (0.12, 0.78), (0.88, 0.78), (0.88, 0.34), (0.46, 0.34), (0.38, 0.24), (0.12, 0.24)],
           close=True)


def _ic_sparkle(p):
    p.line([(0.5, 0.12), (0.58, 0.42), (0.88, 0.5), (0.58, 0.58), (0.5, 0.88), (0.42, 0.58), (0.12, 0.5), (0.42, 0.42)],
           close=True)


def _ic_compress(p):
    p.line([(0.5, 0.1), (0.5, 0.38)])
    p.line([(0.36, 0.26), (0.5, 0.4), (0.64, 0.26)])
    p.line([(0.5, 0.9), (0.5, 0.62)])
    p.line([(0.36, 0.74), (0.5, 0.6), (0.64, 0.74)])
    p.line([(0.16, 0.5), (0.84, 0.5)])


def _ic_merge(p):
    p.line([(0.2, 0.16), (0.2, 0.4), (0.5, 0.58)])
    p.line([(0.8, 0.16), (0.8, 0.4), (0.5, 0.58)])
    p.line([(0.5, 0.58), (0.5, 0.88)])
    p.line([(0.37, 0.75), (0.5, 0.89), (0.63, 0.75)])


def _ic_sun(p):
    p.circ(0.5, 0.5, 0.16)
    for k in range(8):
        a = k * math.pi / 4.0
        p.line([(0.5 + 0.28 * math.cos(a), 0.5 + 0.28 * math.sin(a)),
                (0.5 + 0.4 * math.cos(a), 0.5 + 0.4 * math.sin(a))])


def _ic_pen(p):
    p.line([(0.2, 0.8), (0.27, 0.58), (0.66, 0.19), (0.81, 0.34), (0.42, 0.73)], close=True)
    p.line([(0.56, 0.29), (0.71, 0.44)])


def _ic_eraser(p):
    p.line([(0.14, 0.6), (0.5, 0.2), (0.86, 0.52), (0.58, 0.82), (0.4, 0.82)], close=True)
    p.line([(0.32, 0.4), (0.68, 0.72)])


def _ic_cursor(p):
    p.line([(0.3, 0.14), (0.3, 0.78), (0.46, 0.64), (0.58, 0.9), (0.69, 0.84), (0.57, 0.59), (0.78, 0.56)], close=True)


def _ic_redo(p):
    p.line([(0.64, 0.24), (0.8, 0.4), (0.64, 0.56)])
    p.line([(0.8, 0.4), (0.38, 0.4)])
    p.arc(0.38, 0.58, 0.18, 90, 270)


def _ic_highlight(p):
    p.line([(0.36, 0.54), (0.62, 0.2), (0.82, 0.38), (0.52, 0.68)], close=True)
    p.line([(0.36, 0.54), (0.3, 0.72), (0.52, 0.68)])
    p.line([(0.16, 0.88), (0.84, 0.88)])


def _ic_scissors(p):
    p.circ(0.28, 0.76, 0.1)
    p.circ(0.72, 0.76, 0.1)
    p.line([(0.34, 0.68), (0.7, 0.14)])
    p.line([(0.66, 0.68), (0.3, 0.14)])


def _ic_textbox(p):
    p.rrect(0.14, 0.24, 0.86, 0.76, 0.05)
    p.line([(0.34, 0.4), (0.66, 0.4)])
    p.line([(0.5, 0.4), (0.5, 0.64)])


def _ic_fit(p):
    p.line([(0.16, 0.38), (0.16, 0.16), (0.38, 0.16)])
    p.line([(0.62, 0.16), (0.84, 0.16), (0.84, 0.38)])
    p.line([(0.84, 0.62), (0.84, 0.84), (0.62, 0.84)])
    p.line([(0.38, 0.84), (0.16, 0.84), (0.16, 0.62)])


_ICONS = {
    "pen": _ic_pen, "eraser": _ic_eraser, "cursor": _ic_cursor, "redo": _ic_redo,
    "scissors": _ic_scissors, "highlight": _ic_highlight, "textbox": _ic_textbox, "fit": _ic_fit,
    "compress": _ic_compress, "merge": _ic_merge, "sun": _ic_sun,
    "home": _ic_home, "history": _ic_history, "heart": _ic_heart, "heart_fill": _ic_heart_fill,
    "gear": _ic_gear, "search": _ic_search, "wrench": _ic_wrench, "qr": _ic_qr, "image": _ic_image,
    "text": _ic_text, "doc": _ic_doc, "shield": _ic_shield, "back": _ic_back, "camera": _ic_camera,
    "share": _ic_share, "copy": _ic_copy, "save": _ic_save, "trash": _ic_trash, "up": _ic_up,
    "down": _ic_down, "plus": _ic_plus, "close": _ic_close, "check": _ic_check, "link": _ic_link,
    "globe": _ic_globe, "volume": _ic_volume, "vibrate": _ic_vibrate, "info": _ic_info,
    "paste": _ic_paste, "undo": _ic_undo, "rotate": _ic_rotate, "warn": _ic_warn, "phone": _ic_phone,
    "mail": _ic_mail, "wifi": _ic_wifi, "folder": _ic_folder, "sparkle": _ic_sparkle,
}

_ICON_CACHE = {}


def icon_png(name, color, px=96, flip=False):
    """PNG bytes of a transparent icon."""
    key = (name, color, px, flip)
    if key in _ICON_CACHE:
        return _ICON_CACHE[key]
    ss = 4
    n = px * ss
    im = Image.new("RGBA", (n, n), (0, 0, 0, 0))
    d = ImageDraw.Draw(im)
    w = max(2, int(n * 0.075))
    pen = _Pen(d, n, w, ImageColor.getrgb(color) + (255,))
    fn = _ICONS.get(name, _ic_info)
    fn(pen)
    im = im.resize((px, px), LANCZOS)
    if flip:
        im = im.transpose(Image.FLIP_LEFT_RIGHT if hasattr(Image, "FLIP_LEFT_RIGHT") else 0)
    data = pil_to_png_bytes(im)
    _ICON_CACHE[key] = data
    return data


# --------------------------------------------------------------------------
# Platform helpers (Android intents via pyjnius, everything is guarded)
# --------------------------------------------------------------------------
def _android_activity():
    from jnius import autoclass
    return autoclass("org.kivy.android.PythonActivity").mActivity


def media_scan(path):
    try:
        from jnius import autoclass
        MSC = autoclass("android.media.MediaScannerConnection")
        MSC.scanFile(_android_activity(), [path], None, None)
    except Exception:
        pass


def _relax_file_uri():
    try:
        from jnius import autoclass
        SM = autoclass("android.os.StrictMode")
        B = autoclass("android.os.StrictMode$VmPolicy$Builder")
        SM.setVmPolicy(B().build())
    except Exception:
        pass


def share_text(text):
    try:
        from jnius import autoclass
        Intent = autoclass("android.content.Intent")
        String = autoclass("java.lang.String")
        i = Intent(Intent.ACTION_SEND)
        i.setType("text/plain")
        i.putExtra(Intent.EXTRA_TEXT, String(text))
        _android_activity().startActivity(Intent.createChooser(i, String("3edda")))
        return True
    except Exception:
        return False


def share_file(path, mime, uri_str=None):
    try:
        from jnius import autoclass, cast
        _relax_file_uri()
        Intent = autoclass("android.content.Intent")
        String = autoclass("java.lang.String")
        File = autoclass("java.io.File")
        Uri = autoclass("android.net.Uri")
        i = Intent(Intent.ACTION_SEND)
        i.setType(mime)
        uri = cast("android.os.Parcelable", Uri.parse(uri_str) if uri_str else Uri.fromFile(File(path)))
        i.putExtra(Intent.EXTRA_STREAM, uri)
        i.addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION)
        _android_activity().startActivity(Intent.createChooser(i, String("3edda")))
        return True
    except Exception:
        return False


def open_file_external(path, mime, uri_str=None):
    try:
        from jnius import autoclass
        _relax_file_uri()
        Intent = autoclass("android.content.Intent")
        File = autoclass("java.io.File")
        Uri = autoclass("android.net.Uri")
        i = Intent(Intent.ACTION_VIEW)
        i.setDataAndType(Uri.parse(uri_str) if uri_str else Uri.fromFile(File(path)), mime)
        i.addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION)
        i.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK)
        _android_activity().startActivity(i)
        return True
    except Exception:
        return False


def open_uri(uri):
    """Open any URI (https, tel, mailto, geo, sms) with the system."""
    try:
        from jnius import autoclass
        Intent = autoclass("android.content.Intent")
        Uri = autoclass("android.net.Uri")
        act = Intent.ACTION_DIAL if uri.startswith("tel:") else Intent.ACTION_VIEW
        i = Intent(act, Uri.parse(uri))
        i.addFlags(Intent.FLAG_ACTIVITY_NEW_TASK)
        _android_activity().startActivity(i)
        return True
    except Exception:
        pass
    try:
        return bool(webbrowser.open(uri))
    except Exception:
        return False


def top_inset_px():
    """Height (px) of the status bar / camera cut-out, so the UI starts below it."""
    try:
        from kivy.utils import platform as _pf
        if _pf != "android":
            return 0
        from kivy.metrics import dp as _dp
        best = 0
        try:
            act = _android_activity()
            res = act.getResources()
            rid = res.getIdentifier("status_bar_height", "dimen", "android")
            if rid > 0:
                best = int(res.getDimensionPixelSize(rid))
        except Exception:
            pass
        try:                                   # display cut-out (Android 9+)
            act = _android_activity()
            wi = act.getWindow().getDecorView().getRootWindowInsets()
            if wi is not None:
                dc = wi.getDisplayCutout()
                if dc is not None:
                    best = max(best, int(dc.getSafeInsetTop()))
        except Exception:
            pass
        return max(best, int(_dp(34)))
    except Exception:
        return 0


def vibrate_ms(ms=18):
    try:
        from jnius import autoclass
        ctx = _android_activity()
        vib = ctx.getSystemService(autoclass("android.content.Context").VIBRATOR_SERVICE)
        vib.vibrate(int(ms))
    except Exception:
        pass


def request_android_perms(kinds=("camera", "storage")):
    """Ask for permissions only when the feature is used (not on app start)."""
    if platform != "android":
        return
    try:
        from android.permissions import request_permissions, Permission
        perms = []
        if "camera" in kinds:
            perms.append(Permission.CAMERA)
        if "storage" in kinds:
            if _sdk_int() < 33:                    # Android 13+ never needs it (no "photos and videos" permission)
                perms += [Permission.READ_EXTERNAL_STORAGE, Permission.WRITE_EXTERNAL_STORAGE]
        if perms:
            request_permissions(list(set(perms)))
    except Exception:
        pass


def ensure_camera_permission(cb):
    """Ask for the camera and call cb(granted) when the answer is known (right away if already allowed).
    The camera must only be opened AFTER the answer, otherwise the first visit always fails."""
    if platform != "android":
        cb(True)
        return
    try:
        from android.permissions import request_permissions, check_permission, Permission
        if check_permission(Permission.CAMERA):
            cb(True)
            return

        def answer(perms, grants):
            ok = bool(grants) and all(grants)
            Clock.schedule_once(lambda dt: cb(ok), 0)
        request_permissions([Permission.CAMERA], answer)
    except Exception:
        cb(True)


# ===========================================================================
#                          KIVY  USER  INTERFACE
# ===========================================================================
from kivy.config import Config
from kivy.utils import platform as _kplat
Config.set("kivy", "exit_on_escape", "0")
if _kplat not in ("android", "ios"):
    Config.set("input", "mouse", "mouse,disable_multitouch")

from kivy.app import App
from kivy.animation import Animation
from kivy.clock import Clock
from kivy.core.clipboard import Clipboard
from kivy.core.image import Image as CoreImage
from kivy.core.text import Label as CoreLabel
from kivy.core.window import Window
from kivy.graphics import (Color, Ellipse, Line, PopMatrix, PushMatrix,
                           Rectangle, Rotate, RoundedRectangle,
                           StencilPop, StencilPush, StencilUnUse, StencilUse)
from kivy.metrics import dp, sp
from kivy.properties import (BooleanProperty, DictProperty, ListProperty,
                             NumericProperty, ObjectProperty, StringProperty)
from kivy.uix.anchorlayout import AnchorLayout
from kivy.uix.behaviors import ButtonBehavior
from kivy.uix.boxlayout import BoxLayout
from kivy.uix.floatlayout import FloatLayout
from kivy.uix.gridlayout import GridLayout
from kivy.uix.image import Image as KImage
from kivy.uix.label import Label
from kivy.uix.modalview import ModalView
from kivy.uix.screenmanager import Screen, ScreenManager, SlideTransition
from kivy.uix.scrollview import ScrollView
from kivy.uix.stacklayout import StackLayout
from kivy.uix.textinput import TextInput
from kivy.uix.widget import Widget
from kivy.utils import platform

APP = None            # the running IddaApp instance (set in IddaApp.__init__)

try:
    from kivy.base import ExceptionHandler, ExceptionManager

    class _SafeHandler(ExceptionHandler):
        def handle_exception(self, inst):
            try:
                if APP is not None:
                    APP.report(inst)
                else:
                    traceback.print_exc()
            except Exception:
                pass
            return ExceptionManager.PASS

    ExceptionManager.add_handler(_SafeHandler())
except Exception:
    pass
IMG_EXTS = (".jpg", ".jpeg", ".png", ".webp", ".bmp", ".gif", ".tif", ".tiff")


# --------------------------------------------------------------------------
# helpers
# --------------------------------------------------------------------------
def guard(fn):
    """Never let a UI callback crash the whole app."""
    @functools.wraps(fn)
    def wrapper(*a, **k):
        try:
            return fn(*a, **k)
        except Exception as e:                       # pragma: no cover
            if APP is not None:
                APP.report(e)
            else:
                traceback.print_exc()
    return wrapper


def run_bg(work, done=None):
    """Run work() in a thread; call done(result, error) on the UI thread."""
    def target():
        res = err = None
        try:
            res = work()
        except Exception as e:                       # pragma: no cover
            err = e
            traceback.print_exc()
        if done is not None:
            Clock.schedule_once(lambda dt: done(res, err), 0)
    threading.Thread(target=target, daemon=True).start()


def col(c):
    """'accent' | '#RRGGBB' | tuple -> rgba tuple"""
    if isinstance(c, str):
        return rgba(C[c]) if c in C else rgba(c)
    return tuple(c)


def mirror(items):
    """Order a row written in LTR for the current direction and centre
    fixed-height children vertically."""
    items = list(items)
    for w in items:
        if w.size_hint_y is None and not w.pos_hint:
            w.pos_hint = {"center_y": 0.5}
    return list(reversed(items)) if APP.rtl else items


def hrow(items, height=None, spacing=10, **kw):
    """Horizontal row written in LTR order, auto-mirrored for Arabic."""
    row = BoxLayout(orientation="horizontal", spacing=dp(spacing), **kw)
    if height is not None:
        row.size_hint_y = None
        row.height = dp(height)
    for w in mirror(items):
        row.add_widget(w)
    return row


def vgap(h):
    return Widget(size_hint_y=None, height=dp(h))


def short_path(p, keep=2):
    parts = [x for x in p.replace("\\", "/").split("/") if x]
    return ("…/" + "/".join(parts[-(keep + 1):])) if len(parts) > keep + 1 else p


def make_img(**kw):
    im = KImage(**kw)
    if hasattr(KImage, "fit_mode"):
        im.fit_mode = "contain"
    else:
        im.allow_stretch = True
        im.keep_ratio = True
    return im


def find_asset(name):
    """Path of a picture shipped inside the app (next to main.py), or None."""
    dirs = []
    try:
        dirs.append(os.path.dirname(os.path.abspath(__file__)))
    except Exception:
        pass
    dirs.append(os.getcwd())
    for d in dirs:
        p = os.path.join(d, name)
        if os.path.isfile(p):
            return p
    return None


_TEX_CACHE = {}


def icon_tex(name, color="accent", flip=False):
    c = C[color] if color in C else color
    key = (name, c, flip)
    if key not in _TEX_CACHE:
        data = icon_png(name, c, 128, flip)
        _TEX_CACHE[key] = CoreImage(io.BytesIO(data), ext="png").texture
    return _TEX_CACHE[key]


def png_texture(png_bytes, nearest=False):
    tex = CoreImage(io.BytesIO(png_bytes), ext="png").texture
    if nearest:
        tex.mag_filter = "nearest"
        tex.min_filter = "nearest"
    return tex


# --------------------------------------------------------------------------
# Text engine: fonts + Arabic shaping + manual RTL wrapping
# --------------------------------------------------------------------------
_PUNCT_RE = re.compile("[()\\[\\]{}\u00ab\u00bb\u2026<>]")


class TextEngine:
    """One font for everything -> every run has the same size and baseline."""
    reg = None
    bold = None
    universal = False
    merged = False
    cover = None
    name = ""
    lat_reg = "Roboto"
    lat_bold = "Roboto"
    shape_on = True
    _cl = {}
    _fb = []                       # [(path, coverage)] helpers (only when no merged font)

    @classmethod
    def setup(cls, fonts, shape_on=True):
        from kivy.resources import resource_find
        cls.lat_reg = resource_find("data/fonts/Roboto-Regular.ttf") or "Roboto"
        cls.lat_bold = resource_find("data/fonts/Roboto-Bold.ttf") or cls.lat_reg
        cls.reg = fonts.get("reg")
        cls.bold = fonts.get("bold") or cls.reg
        cls.universal = bool(fonts.get("universal"))
        cls.merged = bool(fonts.get("merged"))
        cls.cover = fonts.get("cover")
        cls.name = fonts.get("name") or (os.path.basename(cls.reg) if cls.reg else "")
        cls.shape_on = shape_on
        cls._cl = {}
        cls._fb = []
        if cls.reg and not cls.merged:
            for p in fonts.get("fallbacks") or []:
                try:
                    cov = ttf_cmap(p)
                except Exception:
                    cov = None
                if cov:
                    cls._fb.append((p, cov))
            if not cls.universal:                      # Latin letters must never turn into empty squares
                cls._fb.insert(0, (cls.lat_reg, set(range(32, 0x250))))

    @classmethod
    def _fb_has(cls, o):
        for _p, cov in cls._fb:
            if o in cov:
                return True
        return False

    @classmethod
    def fix_missing(cls, line, primary_only=False):
        """Replace presentation-form glyphs nobody can draw by base letters
        (so we never draw an empty square)."""
        cov = cls.cover
        if not cov or not line:
            return line
        out = []
        for ch in line:
            o = ord(ch)
            if 0xFB50 <= o <= 0xFEFF and o not in cov and (primary_only or not cls._fb_has(o)):
                dec = unicodedata.decomposition(ch).split()
                if len(dec) >= 2 and dec[0].startswith("<"):
                    out.append("".join(reversed([chr(int(h, 16)) for h in dec[1:]])))
                    continue
            out.append(ch)
        return "".join(out)

    @classmethod
    def can_shape(cls):
        return HAS_SHAPER and cls.shape_on

    @classmethod
    def font(cls, bold=False, ar=False):
        if cls.reg:
            return cls.bold if bold else cls.reg
        return cls.lat_bold if bold else cls.lat_reg

    @classmethod
    def input_font(cls, text=""):
        """Always the same font (switching fonts made the text box jump up and down)."""
        return cls.reg or cls.lat_reg

    @classmethod
    def _core(cls, font, size):
        key = (font, round(size, 1))
        cl = cls._cl.get(key)
        if cl is None:
            cl = CoreLabel(font_name=font, font_size=size)
            cls._cl[key] = cl
        return cl

    @classmethod
    def _w(cls, s, font, size):
        try:
            return cls._core(font, size).get_extents(s)[0]
        except Exception:
            return len(s) * size * 0.55

    @classmethod
    def measure(cls, s, bold=False, size=None):
        size = size or sp(14)
        font = cls.font(bold, APP.ar if APP else False)
        if cls.can_shape():
            s = cls.fix_missing(shape_line(s))
        return cls._w(s, font, size)

    @classmethod
    def plain(cls, s):
        if not s or not cls.can_shape():
            return s
        return "\n".join(cls.fix_missing(shape_line(x)) for x in s.split("\n"))

    @classmethod
    def wrap_logical(cls, s, max_w, font, size):
        out = []
        for para in s.split("\n"):
            cur = ""
            for w in para.split(" "):
                test = (cur + " " + w) if cur else w
                if cur and cls._w(shape_line(test), font, size) > max_w:
                    out.append(cur)
                    cur = w
                else:
                    cur = test
            out.append(cur)
        return "\n".join(out)

    @classmethod
    def markup(cls, s, bold, ui_ar):
        out = []
        for line in (s or "").split("\n"):
            if cls.can_shape() and has_arabic(line):
                line = cls.fix_missing(shape_line(line))
            out.append(cls._runs(line))
        return "\n".join(out)

    @classmethod
    def _runs(cls, line):
        """Plain text. Only a character the main font cannot draw (and only when no merged
        font exists) is drawn with a helper font, so we never get an empty square."""
        if not line:
            return ""
        cov = cls.cover
        if cls.merged or not cls.reg or not cov or not cls._fb:
            return escape_markup(line)
        out, buf, cur = [], [], None

        def flush():
            if buf:
                t = escape_markup("".join(buf))
                out.append("[font=%s]%s[/font]" % (cur, t) if cur else t)

        for ch in line:
            o = ord(ch)
            if ch.isspace() or o in cov:
                f = cur if (ch.isspace() and buf) else None
            else:
                f = None
                for p, c in cls._fb:
                    if o in c:
                        f = p
                        break
            if buf and f != cur:
                flush()
                buf = []
            cur = f
            buf.append(ch)
        flush()
        return "".join(out)


# --------------------------------------------------------------------------
# Labels
# --------------------------------------------------------------------------
class TLabel(Label):
    key = StringProperty("")
    raw = StringProperty("")
    fmt = DictProperty({})
    wrap = BooleanProperty(False)
    is_bold = BooleanProperty(False)
    auto_h = BooleanProperty(False)

    def __init__(self, **kw):
        kw.setdefault("markup", True)
        kw.setdefault("color", rgba(C["text"]))
        kw.setdefault("font_size", sp(15))
        kw.setdefault("halign", "right" if APP.rtl else "left")
        wrap = kw.get("wrap", False)
        kw.setdefault("valign", "top" if wrap else "middle")
        if not wrap:
            kw.setdefault("shorten", True)
            kw.setdefault("shorten_from", "left" if APP.rtl else "right")
            kw.setdefault("max_lines", 1)
        super().__init__(**kw)
        self._last_w = -1
        self.bind(key=self._refresh, raw=self._refresh, fmt=self._refresh,
                  is_bold=self._refresh, font_size=self._refresh)
        self.bind(width=self._on_size)
        if not self.wrap:
            self.bind(height=self._on_size)
        self.bind(texture_size=self._on_tex)
        self._on_size()
        self._refresh()

    def _on_size(self, *a):
        if self.wrap:
            self.text_size = (max(1.0, self.width), None)
            if abs(self.width - self._last_w) > 0.5:
                self._last_w = self.width
                self._refresh()
        else:
            self.text_size = (max(1.0, self.width), max(1.0, self.height))

    def _on_tex(self, *a):
        if self.wrap and self.auto_h:
            self.height = self.texture_size[1] + dp(2)

    def _refresh(self, *a):
        s = T(self.key, **self.fmt) if self.key else self.raw
        font = TextEngine.font(self.is_bold, APP.ar)
        self.font_name = font
        self.bold = bool(self.is_bold and TextEngine.reg and TextEngine.bold == TextEngine.reg)
        if (self.wrap and TextEngine.can_shape() and self.width > 24 and has_arabic(s)):
            s = TextEngine.wrap_logical(s, self.width * 0.97, font, self.font_size)
        self.text = TextEngine.markup(s, self.is_bold, APP.ar)


def L(key=None, raw=None, size=15, color="text", bold=False, wrap=False, h=None,
      halign=None, fmt=None, fill=False, **kw):
    lbl = TLabel(key=key or "", raw=raw or "", fmt=fmt or {}, is_bold=bold, wrap=wrap,
                 font_size=sp(size), color=col(color), **kw)
    if fill:
        lbl.size_hint_y = 1
    else:
        lbl.size_hint_y = None
        if wrap:
            lbl.auto_h = True
            lbl.height = dp(size * 1.45)
        else:
            lbl.height = dp(h) if h else dp(size * 1.45 + 6)
    if halign:
        lbl.halign = halign
    return lbl


# --------------------------------------------------------------------------
# Containers and buttons
# --------------------------------------------------------------------------
class RoundBox(BoxLayout):
    bg = ListProperty([0, 0, 0, 0])
    radius = NumericProperty(0)
    outline = ListProperty([])
    pressed = BooleanProperty(False)

    def __init__(self, **kw):
        kw.setdefault("bg", rgba(C["card"]))
        kw.setdefault("radius", dp(20))
        super().__init__(**kw)
        with self.canvas.before:
            self._col = Color(*self._eff())
            self._rect = RoundedRectangle(pos=self.pos, size=self.size, radius=[self.radius])
            self._ocol = Color(0, 0, 0, 0)
            self._oline = Line(width=1.0)
        self.bind(pos=self._upd, size=self._upd, bg=self._upd, radius=self._upd,
                  outline=self._upd, pressed=self._upd)
        self._upd()

    def _eff(self):
        r, g, b, a = self.bg
        if self.pressed:
            d = -.07 if IS_LIGHT else .07
            return (min(1, max(0, r + d)), min(1, max(0, g + d)), min(1, max(0, b + d)), a)
        return (r, g, b, a)

    def _upd(self, *a):
        self._col.rgba = self._eff()
        self._rect.pos = self.pos
        self._rect.size = self.size
        self._rect.radius = [self.radius]
        if self.outline and self.width > 4 and self.height > 4:
            self._ocol.rgba = self.outline
            r = max(0.0, min(self.radius, self.width / 2.0 - 1, self.height / 2.0 - 1))
            self._oline.rounded_rectangle = (self.x, self.y, self.width, self.height, r)
            self._oline.width = dp(1.2)
        else:
            self._ocol.rgba = (0, 0, 0, 0)


class Tappable(ButtonBehavior):
    sfx = "click"

    def on_press(self):
        if self.sfx and APP is not None:
            APP.feedback(self.sfx)
        super().on_press()


class Card(Tappable, RoundBox):
    """A pressable RoundBox."""

    def on_state(self, inst, st):
        self.pressed = (st == "down")


class Icon(KImage):
    def __init__(self, name, color="accent", size=24, mirror_rtl=False, **kw):
        kw.setdefault("size_hint", (None, None))
        kw["size"] = (dp(size), dp(size))
        super().__init__(**kw)
        if hasattr(KImage, "fit_mode"):
            self.fit_mode = "contain"
        else:
            self.allow_stretch = True
            self.keep_ratio = True
        self._mirror = mirror_rtl
        self.set_icon(name, color)

    def set_icon(self, name, color="accent"):
        self.texture = icon_tex(name, color, flip=bool(self._mirror and APP.rtl))


class IconBtn(Card):
    def __init__(self, icon, color="accent", size=44, icon_size=22, bg="card",
                 on_tap=None, mirror_rtl=False, radius=14, **kw):
        pad = (size - icon_size) / 2.0
        super().__init__(bg=col(bg), radius=dp(radius), size_hint=(None, None),
                         size=(dp(size), dp(size)), padding=dp(pad), **kw)
        self.icon = Icon(icon, color, icon_size, mirror_rtl=mirror_rtl)
        self.add_widget(self.icon)
        self._tap = on_tap

    def set_icon(self, name, color="accent"):
        self.icon.set_icon(name, color)

    def on_release(self):
        if self._tap:
            guard(self._tap)()


class Btn(Card):
    VARIANTS = {
        "primary": ("accent", "on_acc", "on_acc", None),
        "secondary": ("card_hi", "text", "accent", None),
        "ghost": ((0, 0, 0, 0), "text", "accent", "line"),
        "danger": ("danger_bg", "danger", "danger", None),
    }

    def __init__(self, key=None, raw=None, icon=None, variant="primary", on_tap=None,
                 height_dp=52, font=15, auto_w=False, fmt=None, **kw):
        bg, tc, ic, ol = self.VARIANTS[variant]
        super().__init__(bg=col(bg), radius=dp(min(18, height_dp / 2.0)), size_hint_y=None,
                         height=dp(height_dp), padding=[dp(14), 0], **kw)
        if ol:
            self.outline = col(ol)
        self._tap = on_tap
        self._font = font
        self._tc = tc
        text = T(key, **(fmt or {})) if key else (raw or "")
        tw = TextEngine.measure(text, True, sp(font)) + dp(6)
        self.label = L(key=key, raw=raw, size=font, color=tc, bold=True, fmt=fmt, fill=True,
                       halign="center", size_hint_x=None, width=tw)
        items = []
        if icon:
            self.icon = Icon(icon, ic, font + 5)
            holder = AnchorLayout(size_hint_x=None, width=dp(font + 5))
            holder.add_widget(self.icon)
            items.append(holder)
            items.append(Widget(size_hint_x=None, width=dp(8)))
        items.append(self.label)
        inner_w = sum(w.width for w in items)
        self.inner = BoxLayout(orientation="horizontal", size_hint=(None, 1), width=inner_w)
        for w in mirror(items):
            self.inner.add_widget(w)
        self._auto_w = auto_w
        if auto_w:
            self.size_hint_x = None
            self.width = inner_w + dp(32)
            self.add_widget(self.inner)
        else:
            self.add_widget(Widget())
            self.add_widget(self.inner)
            self.add_widget(Widget())
        self.bind(disabled=self._on_dis)

    def set_text(self, raw):
        self.label.key = ""            # a label made from a text key ignores `raw` until the key is cleared
        self.label.raw = raw
        self.label.width = TextEngine.measure(raw, True, sp(self._font)) + dp(6)
        w = sum(c.width for c in self.inner.children)
        self.inner.width = w
        if self._auto_w:
            self.width = w + dp(32)

    def _on_dis(self, inst, v):
        self.opacity = 0.4 if v else 1.0

    def on_release(self):
        if self._tap:
            guard(self._tap)()


class Spinner(Widget):
    def __init__(self, **kw):
        kw.setdefault("size_hint", (None, None))
        kw.setdefault("size", (dp(44), dp(44)))
        super().__init__(**kw)
        with self.canvas:
            Color(*rgba(C["accent"]))
            self._arc = Line(circle=(0, 0, 1, 0, 270), width=dp(3), cap="round")
        self._a = 0
        self._ev = Clock.schedule_interval(self._tick, 1 / 30.0)
        self.bind(pos=self._tick, size=self._tick)

    def _tick(self, *a):
        self._a = (self._a + 10) % 360
        r = max(2, min(self.width, self.height) / 2.0 - dp(3))
        self._arc.circle = (self.center_x, self.center_y, r, self._a, self._a + 270)

    def stop(self):
        if self._ev:
            self._ev.cancel()
            self._ev = None


class Toggle(Tappable, Widget):
    active = BooleanProperty(False)
    knob_t = NumericProperty(0.0)

    def __init__(self, active=False, on_change=None, **kw):
        kw.setdefault("size_hint", (None, None))
        kw.setdefault("size", (dp(54), dp(32)))
        super().__init__(**kw)
        self.sfx = ""
        self._cb = on_change
        self.active = bool(active)
        self.knob_t = 1.0 if self.active else 0.0
        with self.canvas:
            self._c1 = Color(*rgba(C["toggle_off"]))
            self._track = RoundedRectangle(pos=self.pos, size=self.size, radius=[dp(16)])
            self._c2 = Color(1, 1, 1, 1)
            self._knob = Ellipse(pos=self.pos, size=(dp(26), dp(26)))
        self.bind(pos=self._draw, size=self._draw, knob_t=self._draw)
        self._draw()

    def _draw(self, *a):
        off, on = rgba(C["toggle_off"]), rgba(C["accent"])
        self._c1.rgba = tuple(off[i] + (on[i] - off[i]) * self.knob_t for i in range(4))
        self._track.pos = self.pos
        self._track.size = self.size
        self._track.radius = [self.height / 2.0]
        d = self.height - dp(6)
        self._knob.size = (d, d)
        self._knob.pos = (self.x + dp(3) + self.knob_t * (self.width - d - dp(6)), self.y + dp(3))

    def set_active(self, v, notify=False):
        self.active = bool(v)
        Animation(knob_t=1.0 if self.active else 0.0, duration=0.14).start(self)
        if notify and self._cb:
            try:
                self._cb(self.active)
            except Exception as e:
                if APP is not None:
                    APP.report(e)

    @guard
    def on_release(self):
        self.set_active(not self.active, notify=True)
        APP.feedback("on" if self.active else "off")


class SliderX(Widget):
    value = NumericProperty(0)
    vmin = NumericProperty(0)
    vmax = NumericProperty(100)
    step = NumericProperty(1)
    __events__ = ("on_commit",)

    def __init__(self, **kw):
        kw.setdefault("size_hint_y", None)
        kw.setdefault("height", dp(40))
        super().__init__(**kw)
        with self.canvas:
            Color(*rgba(C["track"]))
            self._track = RoundedRectangle(pos=self.pos, size=(1, 1), radius=[dp(3)])
            Color(*rgba(C["accent"]))
            self._fill = RoundedRectangle(pos=self.pos, size=(1, 1), radius=[dp(3)])
            Color(*rgba(C["accent"]))
            self._knob = Ellipse(pos=self.pos, size=(dp(24), dp(24)))
            Color(*rgba(C["bg"]))
            self._dot = Ellipse(pos=self.pos, size=(dp(10), dp(10)))
        self.bind(pos=self._draw, size=self._draw, value=self._draw, vmin=self._draw, vmax=self._draw)
        self._draw()

    def _frac(self):
        span = float(self.vmax - self.vmin) or 1.0
        return max(0.0, min(1.0, (self.value - self.vmin) / span))

    def _draw(self, *a):
        pad = dp(14)
        x0, w = self.x + pad, max(1.0, self.width - 2 * pad)
        cy = self.center_y
        th = dp(6)
        self._track.pos = (x0, cy - th / 2)
        self._track.size = (w, th)
        fw = w * self._frac()
        self._fill.pos = (x0, cy - th / 2)
        self._fill.size = (max(0.1, fw), th)
        k = dp(24)
        self._knob.size = (k, k)
        self._knob.pos = (x0 + fw - k / 2, cy - k / 2)
        dsz = dp(10)
        self._dot.size = (dsz, dsz)
        self._dot.pos = (x0 + fw - dsz / 2, cy - dsz / 2)

    def _set_x(self, x):
        pad = dp(14)
        x0, w = self.x + pad, max(1.0, self.width - 2 * pad)
        f = max(0.0, min(1.0, (x - x0) / w))
        v = self.vmin + f * (self.vmax - self.vmin)
        if self.step:
            v = round(v / self.step) * self.step
        self.value = max(self.vmin, min(self.vmax, v))

    def on_touch_down(self, touch):
        if self.disabled or not self.collide_point(*touch.pos):
            return False
        touch.grab(self)
        self._set_x(touch.x)
        return True

    def on_touch_move(self, touch):
        if touch.grab_current is self:
            self._set_x(touch.x)
            return True
        return False

    def on_touch_up(self, touch):
        if touch.grab_current is self:
            touch.ungrab(self)
            try:
                self.dispatch("on_commit")
            except Exception as e:
                if APP is not None:
                    APP.report(e)
            return True
        return False

    def on_commit(self):
        pass


class Chip(Card):
    def __init__(self, text, **kw):
        w = TextEngine.measure(text, True, sp(14)) + dp(34)
        super().__init__(size_hint=(None, None), size=(w, dp(40)), radius=dp(20),
                         padding=[dp(4), 0], **kw)
        self.lbl = L(raw=text, size=14, bold=True, fill=True, halign="center")
        self.add_widget(self.lbl)
        self.set_selected(False)

    def set_selected(self, sel):
        self.bg = col("accent") if sel else col("card_hi")
        self.lbl.color = col("on_acc") if sel else col("text")


class ChipGroup(StackLayout):
    value = ObjectProperty(None, allownone=True)

    def __init__(self, options, value=None, on_change=None, **kw):
        super().__init__(orientation="rl-tb" if APP.rtl else "lr-tb", spacing=dp(8),
                         size_hint_y=None, **kw)
        self.bind(minimum_height=self.setter("height"))
        self._cb = on_change
        self._chips = {}
        for val, text in options:
            chip = Chip(text)
            chip.bind(on_release=lambda inst, v=val: self._pick(v))
            self._chips[val] = chip
            self.add_widget(chip)
        self.select(value)

    def select(self, value):
        self.value = value
        for v, chip in self._chips.items():
            chip.set_selected(v == value)

    @guard
    def _pick(self, v):
        self.select(v)
        if self._cb:
            self._cb(v)


class ActionChips(StackLayout):
    """Wrapping group of small secondary buttons."""

    def __init__(self, items, **kw):
        super().__init__(orientation="rl-tb" if APP.rtl else "lr-tb", spacing=dp(8),
                         size_hint_y=None, **kw)
        self.bind(minimum_height=self.setter("height"))
        for key, icon, cb in items:
            b = Btn(key=key, icon=icon, variant="secondary", on_tap=cb, height_dp=44, font=13,
                    auto_w=True)
            b.size_hint = (None, None)
            b.height = dp(44)
            self.add_widget(b)


class Swatch(Tappable, Widget):
    selected = BooleanProperty(False)

    def __init__(self, color_hex, **kw):
        kw.setdefault("size_hint", (None, None))
        kw.setdefault("size", (dp(42), dp(42)))
        super().__init__(**kw)
        self._hex = color_hex
        with self.canvas:
            self._ring_c = Color(*rgba(C["accent"], 0))
            self._ring = Ellipse(pos=self.pos, size=self.size)
            self._fill_c = Color(*rgba(color_hex))
            self._fill = Ellipse(pos=self.pos, size=self.size)
        self.bind(pos=self._draw, size=self._draw, selected=self._draw)
        self._draw()

    def _draw(self, *a):
        self._ring.pos = self.pos
        self._ring.size = self.size
        self._ring_c.rgba = rgba(C["text"], 1.0 if self.selected else 0.0)
        g = dp(5)
        self._fill.pos = (self.x + g, self.y + g)
        self._fill.size = (self.width - 2 * g, self.height - 2 * g)


class SwatchRow(BoxLayout):
    def __init__(self, options, value, on_change=None, **kw):
        super().__init__(orientation="horizontal", spacing=dp(8), size_hint_y=None,
                         height=dp(46), **kw)
        self._cb = on_change
        self._sw = {}
        items = []
        for key, hexcol in options:
            s = Swatch(hexcol)
            s.bind(on_release=lambda inst, k=key: self._pick(k))
            self._sw[key] = s
            items.append(s)
        items.append(Widget())
        for w in mirror(items):
            self.add_widget(w)
        self.select(value)

    def select(self, key):
        for k, s in self._sw.items():
            s.selected = (k == key)

    @guard
    def _pick(self, key):
        self.select(key)
        if self._cb:
            self._cb(key)


# --------------------------------------------------------------------------
# Text input
# --------------------------------------------------------------------------
class EditMenu(RoundBox):
    """Small floating menu (paste / copy / cut / select all) shown on long press."""
    cur = None
    _bound = False

    def __init__(self, items, **kw):
        super().__init__(orientation="horizontal", bg=rgba(C["menu"]), radius=dp(16),
                         size_hint=(None, None), padding=[dp(4), dp(4)], spacing=dp(2), **kw)
        self.outline = col("line")
        btns = []
        total = dp(8)
        for key, cb in items:
            text = T(key)
            w = TextEngine.measure(text, True, sp(14)) + dp(28)
            b = Card(bg=(0, 0, 0, 0), radius=dp(12), size_hint=(None, 1), width=w)
            b.add_widget(L(raw=text, size=14, bold=True, fill=True, halign="center"))
            b.bind(on_release=lambda inst, c=cb: EditMenu._run(c))
            btns.append(b)
            total += w + dp(2)
        self.size = (total, dp(46))
        for b in mirror(btns):
            self.add_widget(b)

    @staticmethod
    def _run(cb):
        # keep the long-press selection alive while the action runs (copy/cut need it)
        ti = None
        try:
            ti = TInput.active
        except Exception:
            pass
        try:
            cb()
        except Exception as e:
            if APP is not None:
                APP.report(e)
        finally:
            EditMenu.hide()
            try:
                if ti is not None:
                    ti._lp_hold = False
            except Exception:
                pass

    @classmethod
    def show(cls, items, x, y):
        cls.hide()
        if not items:
            return
        m = cls(items)
        px = max(dp(8), min(x - m.width / 2.0, Window.width - m.width - dp(8)))
        py = max(dp(8), min(y + dp(64), Window.height - m.height - dp(8)))
        m.pos = (px, py)
        Window.add_widget(m)
        cls.cur = m
        if not cls._bound:
            Window.bind(on_touch_down=cls._win_touch)
            cls._bound = True

    @classmethod
    def show_anchored(cls, items, cx, above_y, below_y, lo, hi):
        """Show the menu next to a selection WITHOUT covering the selected text or its handles.
        above_y: bottom edge of the menu when it sits above the selection.
        below_y: top edge of the menu when it sits below the selection's handles.
        lo / hi: lowest / highest y the menu may use (above the keyboard, under the status bar)."""
        cls.hide()
        if not items:
            return
        m = cls(items)
        mh = m.height
        px = max(dp(8), min(cx - m.width / 2.0, Window.width - m.width - dp(8)))
        if above_y is not None and above_y + mh <= hi:
            py = above_y
        elif below_y is not None and below_y - mh >= lo:
            py = below_y - mh
        else:                                       # no room on either side: stay inside the allowed zone
            py = above_y if above_y is not None else lo
            py = max(lo, min(py, hi - mh))
        m.pos = (px, py)
        Window.add_widget(m)
        cls.cur = m
        if not cls._bound:
            Window.bind(on_touch_down=cls._win_touch)
            cls._bound = True

    @classmethod
    def hide(cls):
        m = cls.cur
        cls.cur = None
        if m is not None and m.parent is not None:
            try:
                Window.remove_widget(m)
            except Exception:
                pass

    @staticmethod
    def _win_touch(win, touch):
        m = EditMenu.cur
        if m is not None and not m.collide_point(*touch.pos):
            EditMenu.hide()
        return False


_WORD_EXTRA = "_'’-"


def _is_word_char(ch):
    return ch.isalnum() or ch in _WORD_EXTRA or unicodedata.category(ch).startswith("M") or ch == "ـ"




class SelHandle(Widget):
    """Our own selection handle: a teardrop under the text (added to the Window).
    It does its own touch handling, so it never depends on Kivy's Selector handles."""
    R = 10          # dp, radius of the round part

    def __init__(self, owner, which, **kw):
        super().__init__(size_hint=(None, None), size=(dp(52), dp(52)), **kw)
        self.owner, self.which = owner, which
        with self.canvas:
            Color(*rgba(C["accent"]))
            PushMatrix()
            self._rot = Rotate(angle=45, origin=(0, 0))
            self._corner = Rectangle()
            PopMatrix()
            self._dot = Ellipse()
        self.bind(pos=self._redraw, size=self._redraw)
        self._redraw()

    def _redraw(self, *a):
        r = dp(self.R)
        cx = self.center_x
        cy = self.top - r * 1.4142 - dp(1)          # centre of the round part; the point is at `top`
        self._dot.pos = (cx - r, cy - r)
        self._dot.size = (2 * r, 2 * r)
        self._corner.pos = (cx, cy)                  # the quarter that, turned 45 deg, becomes the point
        self._corner.size = (r, r)
        self._rot.origin = (cx, cy)

    def set_tip(self, x, y):
        """The point of the drop sits at window point (x, y)."""
        self.center_x = x
        self.top = y + dp(1)
        self._redraw()
        try:
            self.canvas.ask_update()
        except Exception:
            pass

    def on_touch_down(self, touch):
        if self.opacity < 0.5 or self.parent is None or not self.collide_point(*touch.pos):
            return False
        touch.grab(self)
        try:
            self.owner._drag_start(self, touch)
        except Exception as e:
            if APP is not None:
                APP.report(e)
        return True

    def on_touch_move(self, touch):
        if touch.grab_current is self:
            try:
                self.owner._dg_apply()
            except Exception as e:
                if APP is not None:
                    APP.report(e)
            return True
        return False

    def on_touch_up(self, touch):
        if touch.grab_current is self:
            touch.ungrab(self)
            try:
                self.owner._drag_end()
            except Exception as e:
                if APP is not None:
                    APP.report(e)
            return True
        return False


class Loupe(Widget):
    """Magnifier bubble shown above the finger while a selection handle is dragged: the text
    line being touched, enlarged, with the selection highlighted and a caret where the handle is."""
    SCALE = 1.6
    W = 220          # dp

    def __init__(self, **kw):
        super().__init__(size_hint=(None, None), size=(dp(self.W), dp(70)), **kw)
        self._tex_cache = {}

    def _texture(self, text, font, size):
        if not text.strip():
            return None
        key = (text, font, round(size, 1))
        tex = self._tex_cache.get(key)
        if tex is None:
            cl = CoreLabel(text=text, font_name=font, font_size=size, color=rgba(C["text"]))
            cl.refresh()
            tex = cl.texture
            if len(self._tex_cache) > 12:
                self._tex_cache.clear()
            self._tex_cache[key] = tex
        return tex

    def update(self, ti, idx, tip_x, tip_y):
        lines = ti._lines
        if not lines:
            return
        col0, row = ti.get_cursor_from_index(int(idx))
        row = max(0, min(int(row), len(lines) - 1))
        line = lines[row]
        col0 = max(0, min(int(col0), len(line)))
        size = ti.font_size * self.SCALE
        font = ti.font_name
        cl = TextEngine._core(font, size)
        vis = TInput._visual
        rtl = bool(TextEngine.can_shape() and has_arabic(line))

        def wid(sub):
            return cl.get_extents(vis(sub))[0] if sub else 0

        full = wid(line)
        cx = (full - wid(line[:col0])) if rtl else wid(line[:col0])
        tex = self._texture(vis(line), font, size)
        th = tex.height if tex is not None else int(size * 1.3)
        bw, bh = dp(self.W), th + dp(18)
        pad = dp(8)
        wv = bw - 2 * pad
        x0 = cx - wv / 2.0                                   # text-pixel at the left edge of the bubble
        dy = ti.line_height + ti.line_spacing
        lim = Window.height - top_inset_px() - dp(4)
        bottom = tip_y + dy + dp(14)
        if bottom + bh > lim:
            bottom = tip_y - dp(60) - bh                     # no room above: go below the finger
        bottom = max(dp(4), bottom)
        left = max(dp(6), min(tip_x - bw / 2.0, Window.width - bw - dp(6)))
        self.pos, self.size = (left, bottom), (bw, bh)
        inner = left + pad
        cv = self.canvas
        cv.clear()
        with cv:
            Color(*rgba(C["loupe"]))
            RoundedRectangle(pos=(left, bottom), size=(bw, bh), radius=[dp(18)])
            Color(*rgba(C["accent"]))
            Line(rounded_rectangle=(left, bottom, bw, bh, dp(18)), width=dp(1.4))
            # selection highlight on this row
            f, t = ti._selection_from, ti._selection_to
            if f is not None and t is not None and int(f) != int(t):
                a_, b_ = (int(f), int(t)) if int(f) < int(t) else (int(t), int(f))
                (s1c, s1r), (s2c, s2r) = ti.get_cursor_from_index(a_), ti.get_cursor_from_index(b_)
                if s1r <= row <= s2r:
                    ca = s1c if row == s1r else 0
                    cb = s2c if row == s2r else len(line)
                    if rtl:
                        hl, hr = full - wid(line[:cb]), full - wid(line[:ca])
                    else:
                        hl, hr = wid(line[:ca]), wid(line[:cb])
                    gl = max(inner, inner + hl - x0)
                    gr = min(inner + wv, inner + hr - x0)
                    if gr > gl:
                        Color(*rgba(C["accent"], 0.38))
                        Rectangle(pos=(gl, bottom + dp(6)), size=(gr - gl, bh - dp(12)))
            # the enlarged text (only the part that fits the bubble)
            if tex is not None and tex.width > 1:
                a = int(max(0, x0))
                b = int(min(tex.width, x0 + wv) + 0.999)
                if b > a:
                    reg = tex.get_region(a, 0, b - a, tex.height)
                    Color(1, 1, 1, 1)
                    Rectangle(texture=reg, pos=(inner + (a - x0), bottom + (bh - th) / 2.0),
                              size=(b - a, tex.height))
            # caret = where the handle is
            Color(*rgba(C["accent"]))
            Rectangle(pos=(inner + wv / 2.0 - dp(1), bottom + dp(5)), size=(dp(2), bh - dp(10)))
        if self.parent is None:
            Window.add_widget(self)

    def hide(self):
        if self.parent is not None:
            try:
                self.parent.remove_widget(self)
            except Exception:
                pass

    def on_touch_down(self, touch):
        return False


class TInput(TextInput):
    """TextInput that connects Arabic letters while typing (the text itself is
    never changed, only the way each line is drawn)."""
    active = None          # the input that currently has focus
    LONG_PRESS = 0.45
    instances = weakref.WeakSet()

    def __init__(self, hint="", **kw):
        kw.setdefault("use_bubble", False)          # we show our own menu (EditMenu)
        kw.setdefault("use_handles", False)         # Kivy's handles are replaced by our own SelHandle
        kw.setdefault("background_normal", "")
        kw.setdefault("background_active", "")
        kw.setdefault("background_disabled_normal", "")
        kw.setdefault("background_color", (0, 0, 0, 0))
        kw.setdefault("foreground_color", rgba(C["text"]))
        kw.setdefault("cursor_color", rgba(C["accent"]))
        kw.setdefault("selection_color", rgba(C["accent"], 0.35))
        kw.setdefault("hint_text_color", rgba(C["muted"]))
        kw.setdefault("font_size", sp(16))
        kw.setdefault("write_tab", False)
        self._hint_raw = hint or ""
        kw.setdefault("font_name", TextEngine.input_font())
        kw["hint_text"] = self._hint_raw          # raw: shaped at draw time
        kw["unfocus_on_touch"] = False            # we dismiss the keyboard ourselves
        super().__init__(**kw)
        self.bind(text=self._on_txt, focus=self._on_focus_state, selection_text=self._on_sel_text)
        TInput.instances.add(self)
        self._on_txt(self, self.text)

    # -- drawing helpers
    @staticmethod
    def _visual(s):
        if not s or not TextEngine.can_shape() or not has_arabic(s):
            return s
        body = s.rstrip("\n")
        return TextEngine.fix_missing(shape_line(body), primary_only=True) + s[len(body):]

    def _create_line_label(self, text, hint=False):
        return super()._create_line_label(self._visual(text), hint)

    def _get_text_width(self, text, tab_width, _label_cached):
        return super()._get_text_width(self._visual(text), tab_width, _label_cached)

    def cursor_offset(self):
        """Arabic lines are drawn right-to-left, so measure from the right end."""
        try:
            row, col = int(self.cursor_row), int(self.cursor_col)
            lines = self._lines
            if row < len(lines) and has_arabic(lines[row]) and TextEngine.can_shape():
                full = self._get_text_width(lines[row], self.tab_width, self._label_cached)
                pre = self._get_text_width(lines[row][:col], self.tab_width, self._label_cached) if col else 0
                return max(0, full - pre)
        except Exception:
            pass
        return super().cursor_offset()

    def get_cursor_from_xy(self, x, y):
        """Touch -> cursor. Arabic lines are drawn right-to-left, so the column
        must be measured from the right end (otherwise dragging goes backwards)."""
        col0, row = super().get_cursor_from_xy(x, y)
        try:
            lines = self._lines
            if not lines or not TextEngine.can_shape():
                return col0, row
            row = max(0, min(int(row), len(lines) - 1))
            line = lines[row]
            if not has_arabic(line):
                return col0, row
            padl, padr = self.padding[0], self.padding[2]
            view_w = self.width - padl - padr
            full = self._get_text_width(line, self.tab_width, self._label_cached)
            halign = getattr(self, "halign", "left")
            if halign == "right":
                xoff = view_w - full
            elif halign == "center":
                xoff = (view_w - full) / 2.0
            else:
                xoff = 0
            base = self.x + padl + xoff - self.scroll_x      # screen x of the line's left end

            def pos(c):
                pre = self._get_text_width(line[:c], self.tab_width, self._label_cached) if c else 0
                return base + full - pre                      # col c sits `pre` away from the right end

            lo, hi = 0, len(line)
            while lo < hi:
                mid = (lo + hi) // 2
                if pos(mid) > x:
                    lo = mid + 1
                else:
                    hi = mid
            if lo > 0 and abs(pos(lo - 1) - x) < abs(pos(lo) - x):
                lo -= 1
            return lo, row
        except Exception:
            return col0, row

    _sel_rows = None       # {row: (left, right, bottom, height, is_rtl)} of the highlight actually drawn

    def _update_graphics_selection(self, *a, **k):
        self._sel_rows = {}
        try:
            return super()._update_graphics_selection(*a, **k)
        finally:
            self._pos_handles_soon()

    def _draw_selection(self, *a):
        """Arabic lines are drawn right-to-left, so the selected part must be measured from
        the right end of the line (otherwise the highlight and the handles move backwards).
        The rectangle that ends up on screen is remembered, so the selection handles can be
        put exactly on its two ends."""
        grp0 = len(self.canvas.get_group("selection"))
        super()._draw_selection(*a)
        try:
            pos, size, line_num, (s1c, s1r), (s2c, s2r), lines, gtw, tabw, lc = a[:9]
            if line_num >= len(lines):
                return
            line = lines[line_num]
            new = self.canvas.get_group("selection")[grp0:]
            rect = None
            for ins in new:
                if hasattr(ins, "size") and hasattr(ins, "pos"):
                    rect = ins
            if rect is None:
                return
            rtl = bool(TextEngine.can_shape() and has_arabic(line))
            if rtl:
                base = pos[0] - self.scroll_x
                full = gtw(line, tabw, lc)
                ca = s1c if line_num == s1r else 0
                cb = s2c if line_num == s2r else len(line)
                right = base + full - (gtw(line[:ca], tabw, lc) if ca else 0)
                left = base + full - (gtw(line[:cb], tabw, lc) if cb else 0)
                lo = self.x + self.padding[0]
                hi = self.right - self.padding[2]
                left, right = max(left, lo), min(right, hi)
                if right < left:
                    right = left
                rect.pos = (left, rect.pos[1])
                rect.size = (right - left, rect.size[1])
            if self._sel_rows is None:
                self._sel_rows = {}
            self._sel_rows[line_num] = (rect.pos[0], rect.pos[0] + rect.size[0], rect.pos[1],
                                        rect.size[1], rtl)
        except Exception:
            pass

    # ------------------------------------------------------------------
    # Text geometry: ONE place that knows where a text index is on screen.
    # Handles, floating menu and touch -> cursor all rely on the same maths,
    # so Arabic (right-to-left) lines are measured from their RIGHT end everywhere.
    # ------------------------------------------------------------------
    def _row_geom(self, row):
        """-> (line, full_width, left_x, is_rtl) of one text row (this widget's own coordinates)."""
        line = self._lines[row]
        padl, padr = self.padding[0], self.padding[2]
        view_w = self.width - padl - padr
        full = self._get_text_width(line, self.tab_width, self._label_cached)
        halign = getattr(self, "halign", "left")
        if halign == "right":
            xoff = view_w - full
        elif halign == "center":
            xoff = (view_w - full) / 2.0
        else:
            xoff = 0
        rtl = bool(TextEngine.can_shape() and has_arabic(line))
        return line, full, self.x + padl + xoff - self.scroll_x, rtl

    def _index_point(self, index):
        """Window position of a text index -> (x, y_of_row_bottom, row, is_rtl) or None."""
        try:
            lines = self._lines
            if not lines:
                return None
            col, row = self.get_cursor_from_index(int(index))
            row = max(0, min(int(row), len(lines) - 1))
            line, full, left, rtl = self._row_geom(row)
            col = max(0, min(int(col), len(line)))
            pre = self._get_text_width(line[:col], self.tab_width, self._label_cached) if col else 0
            x = left + (full - pre if rtl else pre)
            dy = self.line_height + self.line_spacing
            y = self.top - self.padding[1] + self.scroll_y - (row + 1) * dy
            wx, wy = self.to_window(x, y)
            return wx, wy, row, rtl
        except Exception:
            return None

    def _edge_point(self, kind, idx):
        """Window position of the START or END edge of the highlighted selection.
        Taken from the rectangle really drawn (so the handle always sits on the highlight);
        falls back to the text maths if that row has no rectangle."""
        try:
            col, row = self.get_cursor_from_index(int(idx))
            info = (self._sel_rows or {}).get(int(row))
            if info is not None:
                left, right, yb, _h, rtl = info
                if kind == "start":
                    x = right if rtl else left
                else:
                    x = left if rtl else right
                wx, wy = self.to_window(x, yb)
                return wx, wy, int(row), rtl
        except Exception:
            pass
        return self._index_point(idx)

    def _view_bounds(self):
        """Visible vertical range (window y: bottom, top) of the box the text is shown in."""
        sv = getattr(self, "_sv", None)
        try:
            if sv is not None:
                _sx, sy = sv.to_window(sv.x, sv.y)
                return sy, sy + sv.height
            _sx, sy = self.to_window(self.x, self.y)
            return sy, sy + self.height
        except Exception:
            return 0.0, float(Window.height)

    def _row_visible(self, y_bottom):
        lo, hi = self._view_bounds()
        mid = y_bottom + (self.line_height + self.line_spacing) / 2.0
        return lo - dp(2) <= mid <= hi + dp(2)

    def _park_handle(self, h):
        """Hide a selection handle without removing it (and without letting it eat touches)."""
        try:
            h.opacity = 0
            h.pos = (-9999, -9999)
        except Exception:
            pass

    # -- our own selection handles ------------------------------------------------------
    def _handles_get(self):
        hs = getattr(self, "_own_hs", None)
        if hs is None:
            hs = self._own_hs = (SelHandle(self, "a"), SelHandle(self, "b"))
        return hs

    def _loupe_hide(self):
        lp = getattr(self, "_loupe", None)
        if lp is not None:
            lp.hide()

    def _loupe_update(self, dg):
        try:
            lp = getattr(self, "_loupe", None)
            if lp is None:
                lp = self._loupe = Loupe()
            h = dg["h"]
            lp.update(self, dg["idx"], h.center_x, h.top)
        except Exception as e:
            now = time.time()
            if now - getattr(self, "_lp_err_t", 0) > 5 and APP is not None:
                self._lp_err_t = now
                APP.report(e)

    def _handles_hide(self):
        if getattr(self, "_dg", None):
            return                                   # a handle is being dragged right now
        self._loupe_hide()
        for h in (getattr(self, "_own_hs", None) or ()):
            self._park_handle(h)
            if h.parent is not None:
                try:
                    h.parent.remove_widget(h)
                except Exception:
                    pass

    def _place_handle(self, h, pt, dragged=False):
        if pt is None:
            self._park_handle(h)
            return
        x, yb, _row, _rtl = pt
        if not self._row_visible(yb):
            if not dragged:
                self._park_handle(h)                 # its text point is scrolled out of the box
                return
            lo, hi = self._view_bounds()
            yb = max(lo, min(yb, hi - (self.line_height + self.line_spacing)))
        h.opacity = 1
        h.set_tip(x, yb)

    def _position_handles(self, mode="both", *a, **k):
        """Put the two selection handles under the start / end of the selection."""
        try:
            sel = bool(self.selection_text) and self._selection_from is not None \
                and self._selection_to is not None
            dg = getattr(self, "_dg", None)
            if not self.text or not (sel or dg) or getattr(self, "_focus_lost", False):
                self._handles_hide()
                return
            ha, hb = self._handles_get()
            f, t = int(self._selection_from), int(self._selection_to)
            i0, i1 = min(f, t), max(f, t)
            if dg:
                other = hb if dg["h"] is ha else ha
                kd = "start" if dg["idx"] <= dg["fixed"] else "end"
                ko = "end" if kd == "start" else "start"
                pairs = ((dg["h"], dg["idx"], True, kd), (other, dg["fixed"], False, ko))
            else:
                pairs = ((ha, i0, False, "start"), (hb, i1, False, "end"))
            for h, idx, dragged, kind in pairs:
                if h.parent is None:
                    Window.add_widget(h)
                self._place_handle(h, self._edge_point(kind, idx), dragged)
            if dg:
                self._loupe_update(dg)
            else:
                self._loupe_hide()
        except Exception as e:
            # never swallow this silently: a hidden error here = "no handles at all"
            now = time.time()
            if now - getattr(self, "_ph_err_t", 0) > 5 and APP is not None:
                self._ph_err_t = now
                APP.report(e)

    # -- dragging a handle: the finger decides the new end of the selection ---------------
    def _drag_start(self, h, touch):
        f, t = int(self._selection_from), int(self._selection_to)
        i0, i1 = min(f, t), max(f, t)
        ha, hb = self._handles_get()
        mine, other = (i0, i1) if h is ha else (i1, i0)
        self._dg = {"h": h, "idx": mine, "fixed": other, "touch": touch}
        self._hd_active = True
        self._lp_hold = False
        self._lp_sel = None
        EditMenu.hide()
        ev = getattr(self, "_dg_ev", None)
        if ev is not None:
            ev.cancel()
        self._dg_ev = Clock.schedule_interval(self._dg_tick, 1 / 30.0)

    def _dg_apply(self):
        """Selection end = the text point just above the finger (inside the box)."""
        dg = getattr(self, "_dg", None)
        if not dg or not self._lines:
            return
        t = dg["touch"]
        lo, hi = self._view_bounds()
        dy = self.line_height + self.line_spacing
        ty = max(lo + dy * 0.5, min(t.y + dp(34), hi - dy * 0.5))
        xl, yl = self.to_widget(t.x, ty)
        col0, row = self.get_cursor_from_xy(xl, yl)
        row = max(0, min(int(row), len(self._lines) - 1))
        col0 = max(0, min(int(col0), len(self._lines[row])))
        idx = self.cursor_index((col0, row))
        if idx == dg["fixed"] or idx == dg["idx"]:
            self._position_handles()
            return
        dg["idx"] = idx
        a, b = (idx, dg["fixed"]) if idx < dg["fixed"] else (dg["fixed"], idx)
        self.select_text(a, b)
        try:
            self._update_graphics_selection()        # redraw the highlight NOW, in step with the handle
        except Exception:
            pass
        self._position_handles()

    def _dg_tick(self, dt):
        dg = getattr(self, "_dg", None)
        if dg and getattr(dg.get("touch"), "time_end", -1) > 0:
            self._drag_end()
            return
        if not dg:
            ev = getattr(self, "_dg_ev", None)
            if ev is not None:
                ev.cancel()
            self._dg_ev = None
            return
        try:
            sv = getattr(self, "_sv", None)
            t = dg["touch"]
            room = (self.height - sv.height) if sv is not None else 0
            if sv is not None and room > 2:
                _sx, sy = sv.to_window(sv.x, sv.y)
                top, bot = sy + sv.height, sy
                m = dp(24)
                direction = 0
                depth = 0.0
                if t.y + dp(34) > top - m:
                    direction, depth = -1, t.y + dp(34) - (top - m)       # toward earlier text
                elif t.y < bot + dp(6):
                    direction, depth = 1, (bot + dp(6)) - t.y             # toward later text
                if direction:
                    step = dp(3) + min(depth, dp(100)) / dp(100) * dp(18)
                    off = room * (1 - sv.scroll_y)
                    new = max(0.0, min(room, off + direction * step))
                    if abs(new - off) > 0.01:
                        sv.scroll_y = 1 - new / room
            self._dg_apply()
        except Exception:
            pass

    def _drag_end(self):
        ev = getattr(self, "_dg_ev", None)
        if ev is not None:
            ev.cancel()
        self._dg_ev = None
        self._dg = None
        self._hd_active = False
        self._hd_quiet = time.time() + 0.6
        self._position_handles()
        Clock.schedule_once(lambda dt: self._reshow_sel_menu(), 0.08)

    def _pos_handles_soon(self):
        ev = getattr(self, "_ph_ev", None)
        if ev is not None:
            try:
                ev.cancel()
            except Exception:
                pass
        self._ph_ev = Clock.schedule_once(lambda dt: self._position_handles(), 0.03)

    def _reshow_handles(self, dt=0):
        try:
            if self.selection_text and self.focus:
                self._show_handles(0)
                self._position_handles()
        except Exception:
            pass

    def _ensure_handles(self):
        """Make sure the selection handles are on screen whenever there is a selection."""
        try:
            if not self.selection_text:
                return
            if not self.focus:
                self.focus = True
            self._reshow_handles()
            self._sel_watch_start()
            # Kivy sometimes hides them right after a long press -> look again shortly after
            Clock.schedule_once(self._reshow_handles, 0.05)
        except Exception:
            pass

    # keep the handles alive while a selection exists (Kivy hides them on some touches)
    def _on_sel_text(self, inst, val):
        if val:
            self._sel_watch_start()
        else:
            # a long-press restore may bring the selection back a moment later -> wait a bit
            Clock.schedule_once(
                lambda dt: None if (self.selection_text or getattr(self, "_dg", None))
                else self._handles_hide(), 0.15)

    def _sel_watch_start(self):
        if getattr(self, "_sw_ev", None) is None:
            self._sw_ev = Clock.schedule_interval(self._sel_watch, 1 / 20.0)

    def _sel_watch_stop(self):
        ev = getattr(self, "_sw_ev", None)
        if ev is not None:
            try:
                ev.cancel()
            except Exception:
                pass
        self._sw_ev = None

    def _sel_watch(self, dt):
        try:
            if self.get_root_window() is None:
                self._sel_watch_stop()
                self._handles_hide()
                return
            dg = getattr(self, "_dg", None)
            if dg:
                t = dg.get("touch")
                if t is not None and getattr(t, "time_end", -1) > 0:
                    self._drag_end()                         # the finger is gone but the drag never ended
                return
            if getattr(self, "_hd_active", False):
                self._hd_active = False
            if self.selection_text:
                self._idle_ticks = 0
            else:
                self._idle_ticks = getattr(self, "_idle_ticks", 0) + 1
                if self._idle_ticks > 40 and not self.focus:
                    self._sel_watch_stop()
            self._position_handles()
        except Exception:
            pass

    def _hide_our_handles(self):
        return

    def _place_our_handles(self):
        self._ensure_handles()

    def _rescue_handles(self):
        self._position_handles()

    def _clamp_handles(self):
        self._position_handles()

    # -- where the floating menu may go (never over the selected text or its handles)
    def _menu_zone(self):
        try:
            hi = Window.height - top_inset_px() - dp(6)
        except Exception:
            hi = Window.height - dp(40)
        try:
            kb = float(getattr(Window, "keyboard_height", 0) or 0)
        except Exception:
            kb = 0.0
        return kb + dp(6), hi

    def _sel_menu_anchor(self):
        """(centre_x, top_of_selection_y, bottom_of_selection_y) in window coordinates, or None."""
        try:
            f, t = self._selection_from, self._selection_to
            if f is None or t is None or int(f) == int(t):
                return None
            a, b = (int(f), int(t)) if int(f) < int(t) else (int(t), int(f))
            pa, pb = self._index_point(a), self._index_point(b)
            if pa is None or pb is None:
                return None
            lo, hi = self._view_bounds()
            top_y = pa[1] + self.line_height + self.line_spacing      # top edge of the first selected row
            bot_y = pb[1]                                            # bottom edge of the last selected row
            if top_y < lo or bot_y > hi:
                return None                                          # the selection is scrolled out of view
            top_in, bot_in = top_y <= hi, bot_y >= lo               # are the two ends really inside the box?
            top_y, bot_y = min(top_y, hi), max(bot_y, lo)
            if pa[2] == pb[2]:
                cx = (pa[0] + pb[0]) / 2.0
            else:
                sv = getattr(self, "_sv", None)
                cx = (sv.to_window(sv.x, sv.y)[0] + sv.width / 2.0) if sv is not None else self.center_x
            return cx, top_y, bot_y, top_in, bot_in
        except Exception:
            return None

    # -- state
    def _on_txt(self, inst, text):
        self._lp_hold = False
        EditMenu.hide()
        src = text or self._hint_raw
        f = TextEngine.input_font()
        if f != self.font_name:                    # only when the font itself was rebuilt
            self.font_name = f
        if hasattr(TextInput, "halign"):
            want = "right" if has_arabic(src) else "left"
            if self.halign != want:
                self.halign = want

    def _focus_lost_check(self, dt=0):
        # the focus really is gone (not just a quick False -> True bounce): drop the handles
        if not self.focus and not getattr(self, "_dg", None):
            self._focus_lost = True
            self._handles_hide()

    def _on_focus_state(self, inst, f):
        if f:
            self._focus_lost = False
            self._sel_watch_start()
            TInput.active = self
            try:
                self.show_keyboard()
            except Exception:
                pass
        else:
            EditMenu.hide()
            Clock.schedule_once(self._focus_lost_check, 0.35)
            if TInput.active is self:
                TInput.active = None

    # -- long press: select the word under the finger / show paste menu on empty space
    def _long_touch(self, dt=0, *a):
        return                                       # Kivy's own long-press bubble is replaced

    def _lp_cancel(self):
        ev = getattr(self, "_lp_ev", None)
        if ev is not None:
            ev.cancel()
        self._lp_ev = None

    # -- dragging the caret: the finger moves the cursor, a magnifier shows where it is
    def _caret_drag(self, touch):
        if not self._lines:
            return
        lo, hi = self._view_bounds()
        dy = self.line_height + self.line_spacing
        ty = max(lo + dy * 0.5, min(touch.y + dp(10), hi - dy * 0.5))
        xl, yl = self.to_widget(touch.x, ty)
        col0, row = self.get_cursor_from_xy(xl, yl)
        row = max(0, min(int(row), len(self._lines) - 1))
        col0 = max(0, min(int(col0), len(self._lines[row])))
        if (col0, row) != tuple(self.cursor):
            self.cursor = (col0, row)
        idx = self.cursor_index((col0, row))
        lp = getattr(self, "_loupe", None)
        if lp is None:
            lp = self._loupe = Loupe()
        lp.update(self, idx, touch.x, touch.y)

    def _caret_drag_end(self):
        self._g_caret = False
        self._loupe_hide()

    def can_scroll_text(self):
        return False                      # scrolling is done by the ScrollView around the box

    def _max_scroll(self):
        return 0.0

    def _content_h(self):
        """Real height of all the lines + padding."""
        n = max(1, len(self._lines))
        return n * (self.line_height + self.line_spacing) + self.padding[1] + self.padding[3]

    # Long press / drag-scroll are detected at window level (see TextGestures) so they work
    # no matter what the surrounding ScrollView does with the touch.
    def on_touch_move(self, touch):
        if getattr(self, "_g_scrolling", False):
            return True
        # Let Kivy handle selection-handle drags and normal interaction.
        # Only swallow moves that are pure finger-drag-to-select (no handle grabbed).
        for name in ("_handle_left", "_handle_middle", "_handle_right"):
            h = getattr(self, name, None)
            if h is not None and touch.grab_current is h:
                return super().on_touch_move(touch)
        # finger drag on the text itself: don't turn it into a giant selection
        if touch.grab_current is self or getattr(self, "_selection_touch", None) is touch:
            return True
        return super().on_touch_move(touch)

    def on_touch_up(self, touch):
        self._lp_cancel()
        if getattr(self, "_g_scrolling", False):
            self._g_scrolling = False
            try:
                touch.ungrab(self)
            except Exception:
                pass
            self._position_handles()
            if self.selection_text:                    # the menu was hidden while scrolling: bring it back
                Clock.schedule_once(lambda dt: self._reshow_sel_menu(), 0.15)
            return True
        try:
            ret = super().on_touch_up(touch)
        finally:
            if getattr(self, "_lp_hold", False):
                self._lp_restore()
                for d in (0.03, 0.1, 0.25, 0.5):
                    Clock.schedule_once(lambda dt: self._lp_restore(), d)
                # keep the hold longer so the floating menu has time to act on the selection
                Clock.schedule_once(lambda dt: self._lp_release(), 2.5)
        return ret

    # -- keep the long-press selection alive after the finger is lifted
    def cancel_selection(self, *a, **k):
        if getattr(self, "_lp_hold", False):
            return                                   # Kivy's touch-up tries to wipe the word
        return super().cancel_selection(*a, **k)

    def _lp_release(self):
        self._lp_hold = False
        # keep _lp_sel so a late restore can still work if needed

    def _lp_restore(self):
        sel = getattr(self, "_lp_sel", None)
        if not sel:
            return
        if not getattr(self, "_lp_hold", False) and self.selection_text:
            return
        try:
            i0, i1 = sel
            if (self._selection_from != i0 or self._selection_to != i1
                    or not self.selection_text):
                self.select_text(i0, i1)
            end_rc = self.get_cursor_from_index(i1)
            if tuple(self.cursor) != tuple(end_rc):
                self.cursor = end_rc
            try:
                self._ensure_handles()
            except Exception:
                pass
        except Exception:
            pass

    # -- dragging the selection handles: auto-scroll the text box + show the menu on release
    def _handle_pressed(self, instance, *a):
        self._lp_hold = False
        self._lp_sel = None
        self._hd_inside = True          # allow edge-scroll from the first frame of the drag
        self._hd_active = True
        self._hd_inst = instance
        return super()._handle_pressed(instance, *a)

    def _handle_move(self, instance, touch, *a):
        self._hd_active = True
        self._hd_inst, self._hd_touch = instance, touch
        EditMenu.hide()
        # clamp the touch Y into the visible text box before Kivy maps it to a cursor,
        # otherwise a finger past the top/bottom jumps the selection to line 0 / last line
        t = touch
        sv = getattr(self, "_sv", None)
        if sv is not None:
            try:
                _sx, sy = sv.to_window(sv.x, sv.y)
                top, bot = sy + sv.height, sy
                margin = dp(8)
                cy = min(max(t.y, bot + margin), top - margin)
                if abs(cy - t.y) > 0.5:
                    # temporary synthetic touch position for the cursor mapping only
                    old_y = t.y
                    t.y = cy
                    try:
                        ret = super()._handle_move(instance, t, *a)
                    finally:
                        t.y = old_y
                else:
                    ret = super()._handle_move(instance, t, *a)
            except Exception:
                ret = super()._handle_move(instance, t, *a)
        else:
            ret = super()._handle_move(instance, t, *a)
        self._clamp_handles()
        if getattr(self, "_hd_ev", None) is None:
            self._hd_ev = Clock.schedule_interval(self._hd_tick, 1 / 30.0)
        return ret

    def _hd_stop(self):
        self._hd_active = False
        ev = getattr(self, "_hd_ev", None)
        if ev is not None:
            ev.cancel()
        self._hd_ev = None

    def _hd_tick(self, dt):
        try:
            self._hd_tick_inner(dt)
        finally:
            if getattr(self, "_hd_active", False):
                self._clamp_handles()

    def _hd_extend_by_row(self, inst, direction):
        """Move the selection endpoint of the dragged handle by one row (direction: -1 up, +1 down)."""
        try:
            if self._selection_from is None or self._selection_to is None:
                return
            i0 = min(self._selection_from, self._selection_to)
            i1 = max(self._selection_from, self._selection_to)
            # which end is this handle controlling?
            # Kivy: left handle tracks the smaller index, right handle the larger
            hl = getattr(self, "_handle_left", None)
            moving_start = (inst is hl)
            lines = self._lines
            if not lines:
                return
            if moving_start:
                row, col = self.get_cursor_from_index(i0)[1], self.get_cursor_from_index(i0)[0]
                row = max(0, min(len(lines) - 1, row + direction))
                col = min(col, len(lines[row]))
                new_i = self.cursor_index((col, row))
                if new_i >= i1:
                    new_i = max(0, i1 - 1)
                self.select_text(new_i, i1)
            else:
                row, col = self.get_cursor_from_index(i1)[1], self.get_cursor_from_index(i1)[0]
                row = max(0, min(len(lines) - 1, row + direction))
                # when extending downward put cursor at end of the new line; upward keep col
                if direction > 0:
                    col = len(lines[row])
                else:
                    col = min(col, len(lines[row]))
                new_i = self.cursor_index((col, row))
                if new_i <= i0:
                    new_i = min(len(self.text), i0 + 1)
                self.select_text(i0, new_i)
            try:
                self._show_handles(0)
            except Exception:
                pass
            self._position_handles()
        except Exception:
            pass

    def _hd_tick_inner(self, dt):
        try:
            sv = getattr(self, "_sv", None)
            t = getattr(self, "_hd_touch", None)
            inst = getattr(self, "_hd_inst", None)
            if t is None or inst is None or not self._hd_active:
                self._hd_stop()
                return
            if getattr(t, "time_end", -1) > 0:
                self._hd_finish(inst)
                return
            if sv is None:
                return
            room = self.height - sv.height
            if room <= 2:
                return
            _sx, sy = sv.to_window(sv.x, sv.y)
            top, bot = sy + sv.height, sy
            m = dp(40)
            # finger in the middle: nothing to do (handle_move already updates selection)
            if bot + m <= t.y <= top - m:
                return
            if t.y > top - m:
                depth, direction = t.y - (top - m), -1     # scroll toward earlier text
            elif t.y < bot + m:
                depth, direction = (bot + m) - t.y, 1      # scroll toward later text
            else:
                return
            # scroll speed grows with how far past the edge the finger is
            step = dp(3) + min(depth, dp(100)) / dp(100) * dp(18)
            off = room * (1 - sv.scroll_y)
            new = max(0.0, min(room, off + direction * step))
            if abs(new - off) < 0.01:
                # cannot scroll further: still extend selection one row at a time
                self._hd_extend_by_row(inst, direction)
                return
            sv.scroll_y = 1 - new / room
            # extend selection toward the edge we are scrolling into (row by row),
            # NEVER call handle_move with an out-of-bounds touch (that jumped to line 0)
            self._hd_extend_by_row(inst, direction)
        except Exception:
            pass

    def _hd_finish(self, instance):
        if not getattr(self, "_hd_active", False):
            return
        self._hd_stop()
        self._hd_quiet = time.time() + 0.6
        try:
            self._update_selection(True)
        except Exception:
            pass
        Clock.schedule_once(lambda d: self._position_handles(), 0.04)
        if self.selection_text:
            Clock.schedule_once(lambda d: self._menu_after_handle(instance), 0.08)

    def _handle_released(self, instance, *a):
        was = getattr(self, "_hd_active", False)
        try:
            super()._handle_released(instance, *a)
        except Exception:
            pass
        if was:
            self._hd_finish(instance)
        else:
            self._hd_stop()

    def _menu_after_handle(self, inst):
        try:
            self._position_handles()
            self._open_menu()
        except Exception:
            pass

    def _reshow_sel_menu(self):
        try:
            if self.selection_text and self.focus and not getattr(self, "_g_scrolling", False):
                self._open_menu()
        except Exception:
            pass

    def copy(self, data=""):
        """Copy selection (or explicit data) to the clipboard. More reliable on Android."""
        try:
            text = data if data else (self.selection_text or "")
            if not text:
                return
            Clipboard.copy(text)
        except Exception:
            pass

    def cut(self):
        """Cut selection: copy then delete, without letting cancel_selection wipe it early."""
        try:
            text = self.selection_text or ""
            if not text:
                return
            Clipboard.copy(text)
            self.delete_selection()
        except Exception:
            pass

    def paste(self):
        try:
            data = Clipboard.paste()
        except Exception:
            data = ""
        if isinstance(data, bytes):
            data = data.decode("utf-8", "ignore")
        if not data:
            return
        self.focus = True
        try:
            if self.selection_text:
                self.delete_selection()
        except Exception:
            pass
        try:
            self.insert_text(data)
        except Exception:
            self.text = (self.text or "") + data

    def _menu_select_all(self):
        self.focus = True
        self.select_all()
        self._ensure_handles()
        Clock.schedule_once(lambda dt: self._open_menu(*(getattr(self, "_lp_pos", None)
                                                       or getattr(self, "_last_pos", None)
                                                       or (None, None))), 0.15)

    def on_double_tap(self, *a):
        try:
            super().on_double_tap(*a)
        except Exception:
            pass
        pos = getattr(self, "_last_pos", None)
        if pos:
            Clock.schedule_once(lambda dt: self._open_menu(*pos), 0.12)

    def _is_blank_spot(self, x, y, col0, row):
        """True when the finger is on empty space (below the text, or past the end of a line)."""
        if not self.text:
            return True
        try:
            lines = self._lines
            lh = self.line_height + self.line_spacing
            top_last = self.top - self.padding[1] + self.scroll_y - (len(lines) - 1) * lh
            if y < top_last - lh - dp(6):
                return True
            line = lines[row]
            return not line.strip()
        except Exception:
            return False

    @guard
    def _lp_fire(self, dt):
        self._lp_ev = None
        self._lp_done = True
        wx, wy = self._lp_pos                          # window coordinates (for the menu)
        x, y = self.to_widget(wx, wy)                  # the box's own coordinates (for the text)
        self.focus = True
        col0, row = self.get_cursor_from_xy(x, y)
        if self._is_blank_spot(x, y, col0, row):
            self.cancel_selection()
            if self.text:
                self.cursor = (col0, row)
            self._open_menu(wx, wy)
            return
        line = self._lines[row]
        col0 = max(0, min(col0, len(line)))
        a = None
        for d in (0, -1, 1, -2, 2):
            c = col0 + d
            if 0 <= c < len(line) and _is_word_char(line[c]):
                a = c
                break
        if a is None:
            self.cancel_selection()
            self.cursor = (col0, row)
            self._open_menu(wx, wy)
            return
        s = a
        while s > 0 and _is_word_char(line[s - 1]):
            s -= 1
        e = a + 1
        while e < len(line) and _is_word_char(line[e]):
            e += 1
        i0 = self.cursor_index((s, row))
        i1 = self.cursor_index((e, row))
        self.select_text(i0, i1)
        self._lp_sel = (i0, i1)
        self._lp_hold = True
        self._lp_pos = (wx, wy)
        try:
            self._show_handles(0)
        except Exception:
            pass
        self._ensure_handles()
        for d in (0.1, 0.25, 0.6):
            Clock.schedule_once(lambda dt: self._position_handles(), d)
        APP.feedback("pop")
        self._open_menu(wx, wy)

    def _open_menu(self, x=None, y=None):
        # if long-press selected a word but Kivy briefly cleared it, restore first
        try:
            if getattr(self, "_lp_hold", False):
                self._lp_restore()
        except Exception:
            pass
        items = []
        has_sel = bool(self.selection_text)
        if not has_sel and getattr(self, "_lp_sel", None):
            try:
                i0, i1 = self._lp_sel
                self.select_text(i0, i1)
                has_sel = bool(self.selection_text)
            except Exception:
                pass
        if has_sel:
            items.append(("tx_cut", self.cut))
            items.append(("copy", self.copy))
        try:
            clip = Clipboard.paste()
        except Exception:
            clip = ""
        if clip:
            items.append(("tx_paste", self.paste))
        if self.text and (not has_sel or len(self.selection_text or "") < len(self.text)):
            items.append(("tx_select_all", self._menu_select_all))
        anchor = self._sel_menu_anchor() if has_sel else None
        if anchor is not None:
            cx, top_y, bot_y, top_in, bot_in = anchor
            lo, hi = self._menu_zone()
            box_lo, box_hi = self._view_bounds()
            mh = dp(46)
            if top_in:
                # start of the selection is visible: ABOVE it (or BELOW the handles when no room)
                EditMenu.show_anchored(items, cx, top_y + dp(10), bot_y - sp(45) - dp(8), lo, hi)
            elif bot_in:
                # start is scrolled away: sit just under the last selected row / its handle
                EditMenu.show_anchored(items, cx, None, bot_y - sp(45) - dp(8), lo, hi)
            else:
                # the selection fills the whole box: float INSIDE the box (top), never over the header
                EditMenu.show_anchored(items, cx, box_hi - mh - dp(10), None, lo, hi)
        elif not has_sel and x is not None and y is not None:
            EditMenu.show(items, x, y)


class TextGestures:
    """Window-level touch watcher: long press (select word / paste menu) and drag-scrolling
    of a long text box. Window handlers always see the original touch, so this keeps working
    inside ScrollViews."""
    st = None
    _bound = False

    @classmethod
    def bind(cls):
        if not cls._bound:
            Window.bind(on_touch_down=cls.down, on_touch_move=cls.move, on_touch_up=cls.up)
            cls._bound = True

    @staticmethod
    def _top_modal():
        for w in Window.children:                  # first ModalView = the one drawn on top
            if isinstance(w, ModalView):
                return w
        return None

    @staticmethod
    def _inside(w, root):
        # NOTE: Window.parent is the Window itself, so a plain "while w is not None" never ends
        n = 0
        while w is not None and w is not Window and n < 200:
            if w is root:
                return True
            w = w.parent
            n += 1
        return False

    @classmethod
    def _find(cls, touch):
        if EditMenu.cur is not None and APP._hit(EditMenu.cur, touch):
            return None
        top = cls._top_modal()
        for ti in list(TInput.instances):
            try:
                if ti.get_root_window() is None or ti.disabled or ti.opacity < 0.1:
                    continue
                # a dialog / full-screen list is open: only ITS text boxes may take the touch.
                # (Before, the box of the screen behind it could win, so typing went to a hidden box.)
                if top is not None and not cls._inside(ti, top):
                    continue
                if not APP._hit(ti, touch):
                    continue
                sv = getattr(ti, "_sv", None)
                if sv is not None and not APP._hit(sv, touch):
                    continue
                for h in (getattr(ti, "_own_hs", None) or ()):
                    if h.parent is not None and h.opacity > 0.5 and h.collide_point(*touch.pos):
                        return None
                return ti
            except Exception:
                continue
        return None

    @classmethod
    def down(cls, win, touch):
        cls.st = None
        try:
            if getattr(touch, "is_mouse_scrolling", False):
                return False
            ti = cls._find(touch)
            if ti is None:
                return False
            ti._g_scrolling = False
            ti._g_caret = False
            ti._lp_done = False
            ti._lp_hold = False
            ti._lp_sel = None
            ti._lp_cancel()
            ti._lp_pos = ti._last_pos = (touch.x, touch.y)
            ti._lp_ev = Clock.schedule_once(ti._lp_fire, TInput.LONG_PRESS)
            sv = getattr(ti, "_sv", None)
            off0 = 0.0
            if sv is not None:
                off0 = max(0.0, ti.height - sv.height) * (1 - sv.scroll_y)
            cls.st = {"ti": ti, "uid": touch.uid, "x": touch.x, "y": touch.y, "s": ti.scroll_y, "off": off0}
        except Exception as e:
            if APP is not None:
                APP.report(e)
        return False

    @classmethod
    def move(cls, win, touch):
        st = cls.st
        if not st or st["uid"] != touch.uid:
            return False
        try:
            ti = st["ti"]
            dx, dy = touch.x - st["x"], touch.y - st["y"]
            if math.hypot(dx, dy) > dp(12):
                ti._lp_cancel()
            if getattr(ti, "_g_caret", False):
                ti._caret_drag(touch)
                return False
            if (not ti._g_scrolling and not getattr(ti, "_lp_done", False) and not ti.selection_text
                    and math.hypot(dx, dy) > dp(8) and abs(dx) > abs(dy)):
                ti._g_caret = True
                ti._lp_cancel()
                EditMenu.hide()
                ti._caret_drag(touch)
                return False
            sv = getattr(ti, "_sv", None)
            room = (ti.height - sv.height) if sv is not None else 0
            if sv is not None and room > 2:
                if ti._g_scrolling or (abs(dy) > dp(8) and abs(dy) > abs(dx)):
                    ti._g_scrolling = True
                    ti._lp_cancel()
                    EditMenu.hide()                              # a menu must not float over moving text
                    off = max(0.0, min(room, st["off"] + dy))   # finger up -> later text
                    sv.scroll_y = 1 - off / room
                    ti._position_handles()                       # handles travel with their text
        except Exception as e:
            if APP is not None:
                APP.report(e)
        return False

    @classmethod
    def up(cls, win, touch):
        for ti in list(TInput.instances):          # a selection-handle drag ends with its finger
            try:
                if getattr(ti, "_hd_active", False) and getattr(ti, "_hd_touch", None) is touch:
                    ti._hd_finish(ti._hd_inst)
            except Exception:
                pass
        st = cls.st
        if st and st["uid"] == touch.uid:
            ti = st["ti"]
            try:
                ti._lp_cancel()
                was_caret = getattr(ti, "_g_caret", False)
                if was_caret:
                    ti._caret_drag_end()
                tapped = ((not was_caret) and (not ti._g_scrolling) and not getattr(ti, "_lp_done", False)
                          and math.hypot(touch.x - st["x"], touch.y - st["y"]) < dp(14))
                if tapped:
                    Clock.schedule_once(lambda dt: cls._tap_done(ti), 0.12)
            except Exception:
                pass
            cls.st = None
        return False

    @classmethod
    def _tap_done(cls, ti):
        try:
            # Always re-open the keyboard on a short tap inside the field
            ti.focus = True
            try:
                ti.show_keyboard()
            except Exception:
                pass
            # some Android keyboards need a bounce
            Clock.schedule_once(lambda dt: cls._kb_nudge(ti), 0.12)
        except Exception:
            pass

    @classmethod
    def _kb_nudge(cls, ti):
        try:
            if not ti.focus:
                ti.focus = True
            ti.show_keyboard()
        except Exception:
            pass


from kivy.uix.stencilview import StencilView
from kivy.properties import NumericProperty as _NumProp


class ClipBox(Widget):
    """Plain clipping window around one tall child. It never touches the touch events
    (so taps, cursor and keyboard work exactly like a normal TextInput); the text is moved by
    TextGestures through `scroll_y` (1 = top of the text, 0 = bottom).
    The clip rectangle is drawn here (not by StencilView) and is a few dp SMALLER than the
    card at the top and bottom, so a half line can never show above / below the rounded
    border.  The text padding (12dp) is bigger than the inset, so no text is ever cut."""
    scroll_y = _NumProp(1.0)
    INSET = 5          # dp, top and bottom

    def __init__(self, **kw):
        super().__init__(**kw)
        self.child = None
        with self.canvas.before:
            StencilPush()
            self._clip_a = Rectangle()
            StencilUse()
        with self.canvas.after:
            StencilUnUse()
            self._clip_b = Rectangle()
            StencilPop()
        self._off = 0.0            # how far the text is scrolled down, in pixels (the real position)
        self._internal = False
        self.bind(pos=self._lay, size=self._on_geom, scroll_y=self._on_sy)

    def _room(self):
        w = self.child
        return max(0.0, w.height - self.height) if w is not None else 0.0

    def _on_sy(self, *a):
        if not self._internal:                       # somebody moved the view: remember where (in px)
            self._off = self._room() * (1 - self.scroll_y)
        self._lay()

    def _on_geom(self, *a):
        """Text or box changed height: keep the SAME pixel position (clamped), so nothing jumps."""
        room = self._room()
        off = max(0.0, min(self._off, room))
        self._off = off
        self._internal = True
        try:
            self.scroll_y = (1 - off / room) if room > 0 else 1.0
        finally:
            self._internal = False
        self._lay()

    def _clip_update(self):
        ins = dp(self.INSET)
        h = max(0.0, self.height - 2 * ins)
        for r in (self._clip_a, self._clip_b):
            r.pos = (self.x, self.y + ins)
            r.size = (self.width, h)

    def set_child(self, w):
        self.child = w
        w.size_hint = (None, None)
        self.add_widget(w)
        w.bind(height=self._on_geom)
        self._lay()

    def _lay(self, *a):
        self._clip_update()
        w = self.child
        if w is None:
            return
        w.width = self.width
        w.x = self.x
        room = max(0.0, w.height - self.height)
        w.top = self.top + room * (1 - self.scroll_y)

    def on_touch_down(self, touch):
        if not self.collide_point(*touch.pos):     # the child is taller than the window
            return False
        return super().on_touch_down(touch)


class InputBox(RoundBox):
    def __init__(self, hint="", multiline=False, height_dp=54, input_type="text", **kw):
        super().__init__(bg=col("card"), radius=dp(16), size_hint_y=None,
                         height=dp(height_dp), padding=[dp(4), 0], **kw)
        fs = sp(16)
        self.sv = None
        self._fit_evs = []
        if multiline:
            pad = [dp(12), dp(12), dp(12), dp(12)]
        else:
            py = max(dp(6), (dp(height_dp) - fs * 1.4) / 2.0)
            pad = [dp(12), py, dp(12), py]
        self.input = TInput(hint=hint, multiline=multiline, padding=pad, input_type=input_type,
                            font_size=fs)
        self.input.bind(focus=self._on_focus)
        if multiline:
            # fixed-size box; the text lives in its own ScrollView so it can be dragged up/down
            self.sv = ClipBox()
            self.input._sv = self.sv
            self.sv.set_child(self.input)
            self.add_widget(self.sv)
            self.input.bind(text=self._sched_fit, width=self._sched_fit, font_size=self._sched_fit)
            self.sv.bind(height=self._sched_fit)
            self.input.bind(cursor=self._sched_follow)
            self.input.bind(scroll_y=self._keep_zero, scroll_x=self._keep_zero)
            try:
                self.input.bind(_lines=self._sched_fit)
            except Exception:
                pass
            self._sched_fit()
        else:
            self.add_widget(self.input)

    @staticmethod
    def _keep_zero(inst, v):
        # the box is as tall as its text, so Kivy's own scrolling must stay at 0 -- otherwise
        # every touch -> (column, row) conversion is shifted and lands on the last line
        if v:
            inst.scroll_y = 0
            inst.scroll_x = 0

    def can_scroll(self):
        return self.sv is not None and self.input.height > self.sv.height + 2

    def _sched_fit(self, *a):
        # Kivy rebuilds its line list a moment after the text changes: measure on the very next
        # frame (so no empty gap shows under the text) and again a few times to be sure
        for ev in (getattr(self, "_fit_evs", None) or ()):
            try:
                ev.cancel()
            except Exception:
                pass
        self._fit_evs = [Clock.schedule_once(self._fit, d) for d in (0, 0.05, 0.15, 0.4)]

    def _fit(self, dt=0):
        try:
            ti, sv = self.input, self.sv
            h = max(sv.height, ti._content_h() + dp(4))
            if abs(ti.height - h) > 1:
                ti.height = h                      # ClipBox keeps the scroll position in pixels
            ti.scroll_y = 0
            if h <= sv.height + 1:
                sv.scroll_y = 1                    # everything fits: show it from the top
            self._follow()                         # and keep the cursor in view
        except Exception:
            pass

    def _sched_follow(self, *a):
        Clock.schedule_once(self._follow, 0.06)

    def _follow(self, dt=0):
        """Keep the cursor inside the visible part of the box while typing / moving it."""
        try:
            ti, sv = self.input, self.sv
            if getattr(ti, "_hd_active", False) or time.time() < getattr(ti, "_hd_quiet", 0):
                return                                       # a selection handle is being dragged
            room = ti.height - sv.height
            if room <= 1:
                return
            dy = ti.line_height + ti.line_spacing
            top = ti.padding[1] + ti.cursor_row * dy          # distance from the top of the text
            off = room * (1 - sv.scroll_y)                     # how far the view is scrolled down
            if top < off:
                off = top - dp(4)
            elif top + dy > off + sv.height - ti.padding[3]:
                off = top + dy - sv.height + ti.padding[3]
            sv.scroll_y = max(0.0, min(1.0, 1 - off / room))
        except Exception:
            pass

    def _on_focus(self, inst, f):
        self.outline = col("accent") if f else []
        if f:
            Clock.schedule_once(self._reveal, 0.4)

    def _reveal(self, dt):
        """Scroll so this box sits near the top, i.e. above the keyboard."""
        try:
            sv = self.parent
            n = 0
            # NOTE: Window.parent is the Window itself: without this stop the loop never ends when the
            # box is not inside a ScrollView (dialogs, full-screen lists) and the whole app freezes
            while sv is not None and sv is not Window and not isinstance(sv, ScrollView) and n < 200:
                sv = sv.parent
                n += 1
            if not isinstance(sv, ScrollView) or not sv.children:
                return
            body = sv.children[0]
            scrollable = body.height - sv.height
            if scrollable <= 1:
                return
            dist = body.to_window(body.x, body.top)[1] - self.to_window(self.x, self.top)[1]
            offset = max(0.0, dist - dp(90))
            Animation(scroll_y=max(0.0, min(1.0, 1 - offset / scrollable)), d=0.2).start(sv)
        except Exception:
            pass


def unfocus_all(widget):
    try:
        for w in widget.walk(restrict=True):
            if isinstance(w, TextInput) and w.focus:
                w.focus = False
        Window.release_all_keyboards()
    except Exception:
        pass


# --------------------------------------------------------------------------
# Toast, busy overlay, dialogs
# --------------------------------------------------------------------------
class ToastBox(RoundBox):
    pass


def show_toast(text, kind="info", seconds=2.4):
    maxw = min(Window.width - dp(40), dp(380))
    parts = text.split("\n")
    widths = [TextEngine.measure(p, False, sp(14)) + dp(40) for p in parts]
    tw = max(widths)
    w = min(maxw, tw)
    lines = sum(max(1, int(math.ceil(x / max(1.0, maxw)))) for x in widths)
    h = dp(26) + lines * dp(20)
    bg = C.get("toast_" + kind, C["toast_info"])
    box = ToastBox(bg=rgba(bg), radius=dp(16), size_hint=(None, None), size=(w, h),
                   padding=[dp(16), dp(8)])
    box.add_widget(L(raw=text, size=14, color="white", wrap=True, fill=True, halign="center"))
    kb = 0
    try:
        kb = float(getattr(Window, "keyboard_height", 0) or 0)
    except Exception:
        pass
    box.pos = ((Window.width - w) / 2.0, dp(96) + kb)      # stay above the keyboard
    box.opacity = 0
    Window.add_widget(box)
    anim = Animation(opacity=1, d=0.15) + Animation(opacity=1, d=seconds) + Animation(opacity=0, d=0.3)
    anim.bind(on_complete=lambda *a: Window.remove_widget(box) if box.parent else None)
    anim.start(box)


def _modal_kwargs(**extra):
    kw = dict(background="", background_color=(0, 0, 0, 0), auto_dismiss=False)
    if hasattr(ModalView, "overlay_color"):
        kw["overlay_color"] = (0, 0, 0, 0.68)
    else:
        kw["background_color"] = (0, 0, 0, 0.68)
    kw.update(extra)
    return kw


class _Veil(Widget):
    """Full-screen flat colour that blocks touches; its alpha is animated."""
    a = NumericProperty(0)

    def __init__(self, bg, **kw):
        super().__init__(size_hint=(None, None), pos=(0, 0), size=Window.size, **kw)
        with self.canvas:
            self._col = Color(bg[0], bg[1], bg[2], 0)
            self._rect = Rectangle(pos=self.pos, size=self.size)
        self.bind(a=lambda i, v: setattr(self._col, "a", v))
        Window.bind(size=self._fit)

    def _fit(self, w, size):
        self.size = size
        self._rect.size = size

    def on_touch_down(self, touch):
        return True

    def on_touch_move(self, touch):
        return True

    def on_touch_up(self, touch):
        return True


class Busy(ModalView):
    def __init__(self, text="", **kw):
        super().__init__(**_modal_kwargs(size_hint=(None, None), size=(dp(230), dp(160))))
        card = RoundBox(orientation="vertical", bg=col("card"), radius=dp(24), padding=dp(18),
                        spacing=dp(12))
        self.spin = Spinner()
        holder = AnchorLayout(anchor_x="center", anchor_y="center")
        holder.add_widget(self.spin)
        card.add_widget(holder)
        self.lbl = L(raw=text or T("working"), size=14, color="muted", halign="center", wrap=True)
        card.add_widget(self.lbl)
        self.add_widget(card)

    def set_text(self, text):
        self.lbl.raw = text

    def on_dismiss(self):
        self.spin.stop()


class Dialog(ModalView):
    def __init__(self, title="", body="", buttons=(), extra=(), dismissable=True, **kw):
        super().__init__(**_modal_kwargs(size_hint=(None, None), auto_dismiss=dismissable))
        self._has_input = any(isinstance(e, InputBox) for e in extra)
        w = min(Window.width - dp(32), dp(420))
        card = RoundBox(orientation="vertical", bg=col("card"), radius=dp(26), padding=dp(20),
                        spacing=dp(12), size_hint_y=None)
        card.bind(minimum_height=card.setter("height"))
        if title:
            card.add_widget(L(raw=title, size=19, bold=True, wrap=True))
        if body:
            card.add_widget(L(raw=body, size=14, color="muted", wrap=True))
        for ex in extra:
            card.add_widget(ex)
        if buttons:
            card.add_widget(vgap(2))
            row = BoxLayout(orientation="horizontal", spacing=dp(10), size_hint_y=None, height=dp(48))
            items = []
            for text, variant, cb in buttons:
                items.append(Btn(raw=text, variant=variant, height_dp=48, font=14,
                                 on_tap=lambda c=cb: self._press(c)))
            for b in mirror(items):
                row.add_widget(b)
            card.add_widget(row)
        self.size = (w, card.height)
        card.bind(height=lambda inst, h: setattr(self, "height", h))
        self.add_widget(card)

    def _align_center(self, *a):
        """Dialogs that contain a text box are lifted so the keyboard does not hide their buttons."""
        try:
            if getattr(self, "_has_input", False) and getattr(self, "_is_open", True):
                self.center_x = Window.width / 2.0
                self.top = Window.height - top_inset_px() - dp(96)
                return
        except Exception:
            pass
        sup = getattr(super(), "_align_center", None)
        if sup is not None:
            sup(*a)

    def _press(self, cb):
        self.dismiss()
        if cb:
            cb()


# --------------------------------------------------------------------------
# File picker (works with plain storage permissions, no SAF needed)
# --------------------------------------------------------------------------
class FileRow(Card):
    """A folder row."""

    def __init__(self, path, name, on_tap=None, **kw):
        super().__init__(bg=col("card"), radius=dp(16), size_hint_y=None, height=dp(54),
                         padding=[dp(14), dp(6)], spacing=dp(12), **kw)
        self.path = path
        self._tap = on_tap
        icon_box = AnchorLayout(size_hint_x=None, width=dp(30))
        icon_box.add_widget(Icon("folder", "accent", 24))
        for w in mirror([icon_box, L(raw=name, size=15, fill=True)]):
            self.add_widget(w)

    def on_release(self):
        if self._tap:
            guard(self._tap)(self)


class ThumbLoader:
    """One background worker that makes square thumbnails, newest first."""
    tex = {}
    gen = 0
    _q = None

    @classmethod
    def _start(cls):
        if cls._q is None:
            cls._q = queue.Queue()
            threading.Thread(target=cls._run, daemon=True).start()

    @classmethod
    def _run(cls):
        while True:
            gen, path, cb = cls._q.get()
            if gen != cls.gen:
                continue
            try:
                png = make_thumb_png(path)
            except Exception:
                continue
            Clock.schedule_once(lambda dt, p=path, b=png, c=cb: c(p, b), 0)

    @classmethod
    def request(cls, path, cb):
        cls._start()
        cls._q.put((cls.gen, path, cb))

    @classmethod
    def new_generation(cls):
        cls.gen += 1


class ThumbTile(Tappable, FloatLayout):
    def __init__(self, path, size, on_tap, **kw):
        super().__init__(size_hint=(None, None), size=(size, size), **kw)
        self.sfx = "tap"
        self.path = path
        self._tap = on_tap
        with self.canvas.before:
            Color(*rgba(C["card"]))
            self._bg = RoundedRectangle(pos=self.pos, size=self.size, radius=[dp(10)])
        with self.canvas.after:
            self._dim_c = Color(0, 0, 0, 0)
            self._dim = RoundedRectangle(pos=self.pos, size=self.size, radius=[dp(10)])
        self.bind(pos=self._upd, size=self._upd)
        self.img = make_img(size_hint=(1, 1), pos_hint={"x": 0, "y": 0})
        self.add_widget(self.img)
        self.mark = RoundBox(bg=col("accent"), radius=dp(13), size_hint=(None, None),
                             size=(dp(26), dp(26)), pos_hint={"right": 0.96, "top": 0.96})
        self.mark_lbl = L(raw="", size=13, bold=True, color="on_acc", fill=True, halign="center")
        self.mark.add_widget(self.mark_lbl)
        self.mark.opacity = 0
        self.add_widget(self.mark)
        tex = ThumbLoader.tex.get(path)
        if tex is not None:
            self.img.texture = tex

    def _upd(self, *a):
        self._bg.pos = self.pos
        self._bg.size = self.size
        self._dim.pos = self.pos
        self._dim.size = self.size

    def set_png(self, png):
        tex = png_texture(png)
        if len(ThumbLoader.tex) > 400:
            ThumbLoader.tex.clear()
        ThumbLoader.tex[self.path] = tex
        self.img.texture = tex

    def set_mark(self, text):
        on = bool(text)
        self.mark.opacity = 1 if on else 0
        self.mark_lbl.raw = text
        self._dim_c.rgba = (0, 0, 0, 0.38 if on else 0)

    def on_release(self):
        if self._tap:
            guard(self._tap)(self)


# --------------------------------------------------------------------------
# Android's own photo picker (Google Photos, Gallery ...) for the "from gallery" buttons
# --------------------------------------------------------------------------
_REQ_PICK = 7311
_MIME_EXT = {"application/pdf": ".pdf", "image/jpeg": ".jpg", "image/png": ".png", "image/webp": ".webp", "image/gif": ".gif",
             "image/bmp": ".bmp", "image/tiff": ".tif"}


def _uri_name(cr, uri):
    """File name of a content:// Uri, or None."""
    try:
        cur = cr.query(uri, None, None, None, None)
        if cur is not None:
            try:
                if cur.moveToFirst():
                    i = cur.getColumnIndex("_display_name")
                    if i >= 0:
                        return cur.getString(i)
            finally:
                cur.close()
    except Exception:
        pass
    return None


def _copy_uris_to_cache(uris, exts=IMG_EXTS, default_ext=".jpg", stem="photo"):
    """Copy picked content:// images into the app folder so the tools can open them as normal files."""
    import shutil
    from jnius import autoclass
    cr = autoclass("org.kivy.android.PythonActivity").mActivity.getContentResolver()
    # a NEW folder for every pick: adding images a second time must not delete the first ones
    d = os.path.join(APP.user_data_dir, "picked", "%d_%04d" % (int(time.time()), random.randint(0, 9999)))
    os.makedirs(d, exist_ok=True)
    out = []
    for i, uri in enumerate(uris):
        name = _uri_name(cr, uri) or ("%s_%d" % (stem, i + 1))
        name = re.sub(r'[\\/:*?"<>|]+', "_", name).strip() or ("%s_%d" % (stem, i + 1))
        if not name.lower().endswith(tuple(exts)):
            try:
                name += _MIME_EXT.get(str(cr.getType(uri)), default_ext)
            except Exception:
                name += default_ext
        dest = os.path.join(d, name)
        if os.path.exists(dest):
            dest = os.path.join(d, "%d_%s" % (i + 1, name))
        pfd = cr.openFileDescriptor(uri, "r")
        try:
            fd = pfd.detachFd()
        except Exception:
            fd = os.dup(pfd.getFd())
            pfd.close()
        with os.fdopen(fd, "rb") as src, open(dest, "wb") as dst:
            shutil.copyfileobj(src, dst, 1 << 20)
        out.append(dest)
    return out


def pick_images_system(callback, multiple=False):
    """Open Android's photo picker. Returns True if it was launched. Returns False when this host
    cannot receive the result (for example Pydroid), so the caller falls back to the built-in picker."""
    try:
        from android import activity               # python-for-android (APK) only
        from jnius import autoclass
        act = autoclass("org.kivy.android.PythonActivity").mActivity
        Intent = autoclass("android.content.Intent")
        sdk = int(autoclass("android.os.Build$VERSION").SDK_INT)
    except Exception:
        return False
    handler = []

    def unbind():
        for h in handler:
            try:
                activity.unbind(on_activity_result=h)
            except Exception:
                pass
        del handler[:]

    def on_result(request, result, data):
        if request != _REQ_PICK:
            return
        unbind()
        uris = []
        try:
            if result == -1 and data is not None:
                clip = data.getClipData()
                if clip is not None:
                    uris = [clip.getItemAt(i).getUri() for i in range(clip.getItemCount())]
                elif data.getData() is not None:
                    uris = [data.getData()]
        except Exception:
            traceback.print_exc()
        if uris:
            Clock.schedule_once(lambda dt: _import_picked(uris, callback), 0)

    def classic():
        i = Intent(Intent.ACTION_GET_CONTENT)
        i.addCategory(Intent.CATEGORY_OPENABLE)
        if multiple:
            i.putExtra(Intent.EXTRA_ALLOW_MULTIPLE, True)
        i.setType("image/*")
        return i

    def photo_picker():
        i = Intent("android.provider.action.PICK_IMAGES")
        if multiple:
            i.putExtra("android.provider.extra.PICK_IMAGES_MAX", 50)
        i.setType("image/*")
        return i

    # Single image: the modern photo picker. Several images: the classic picker (it always accepts
    # a plain true/false "allow multiple" flag, the photo picker needs a number that can be mis-typed).
    makers = [photo_picker, classic] if (sdk >= 33 and not multiple) else [classic, photo_picker]
    for make in makers:
        try:
            intent = make()
            handler.append(on_result)
            activity.bind(on_activity_result=on_result)
            act.startActivityForResult(intent, _REQ_PICK)
            return True
        except Exception as e:
            try:
                APP.log_error(e)
            except Exception:
                pass
            unbind()
    return False


def has_all_files_access():
    """Android 11+: can the app see every folder (needed to find PDFs saved by other apps)?"""
    if platform != "android":
        return True
    try:
        from jnius import autoclass
        if autoclass("android.os.Build$VERSION").SDK_INT < 30:
            return True
        return bool(autoclass("android.os.Environment").isExternalStorageManager())
    except Exception:
        return True


def open_all_files_settings():
    """Open the system screen where the user turns on 'all files access' for this app."""
    try:
        from jnius import autoclass
        act = autoclass("org.kivy.android.PythonActivity").mActivity
        Intent = autoclass("android.content.Intent")
        Settings = autoclass("android.provider.Settings")
        Uri = autoclass("android.net.Uri")
        try:
            act.startActivity(Intent(Settings.ACTION_MANAGE_APP_ALL_FILES_ACCESS_PERMISSION,
                                     Uri.parse("package:" + act.getPackageName())))
        except Exception:
            act.startActivity(Intent(Settings.ACTION_MANAGE_ALL_FILES_ACCESS_PERMISSION))
        return True
    except Exception as e:
        try:
            APP.log_error(e)
        except Exception:
            pass
        return False


def pick_pdfs_system(callback, multiple=False):
    """Android's own document picker for PDF files. Returns True if it was launched (False on hosts
    that cannot receive the result, e.g. Pydroid -> the caller then uses the built-in PDF picker)."""
    try:
        from android import activity               # python-for-android (APK) only
        from jnius import autoclass
        act = autoclass("org.kivy.android.PythonActivity").mActivity
        Intent = autoclass("android.content.Intent")
    except Exception:
        return False
    handler = []

    def unbind():
        for h in handler:
            try:
                activity.unbind(on_activity_result=h)
            except Exception:
                pass
        del handler[:]

    def on_result(request, result, data):
        if request != _REQ_PICK:
            return
        unbind()
        uris = []
        try:
            if result == -1 and data is not None:
                clip = data.getClipData()
                if clip is not None:
                    uris = [clip.getItemAt(i).getUri() for i in range(clip.getItemCount())]
                elif data.getData() is not None:
                    uris = [data.getData()]
        except Exception:
            traceback.print_exc()
        if uris:
            Clock.schedule_once(lambda dt: _import_picked(uris, callback, (".pdf",), ".pdf", "document"), 0)

    try:
        intent = Intent(Intent.ACTION_GET_CONTENT)
        intent.addCategory(Intent.CATEGORY_OPENABLE)
        if multiple:
            intent.putExtra(Intent.EXTRA_ALLOW_MULTIPLE, True)
        intent.setType("application/pdf")
        handler.append(on_result)
        activity.bind(on_activity_result=on_result)
        act.startActivityForResult(intent, _REQ_PICK)
        return True
    except Exception as e:
        try:
            APP.log_error(e)
        except Exception:
            pass
        unbind()
        return False


def _import_picked(uris, callback, exts=IMG_EXTS, default_ext=".jpg", stem="photo"):
    APP.busy_show(T("working"))

    def work():
        return _copy_uris_to_cache(uris, exts, default_ext, stem)

    def done(res, err):
        APP.busy_hide()
        if err or not res:
            APP.feedback("error")
            APP.toast(T("error"), "error")
            return
        guard(callback)(res)
    run_bg(work, done)


class FilePicker(ModalView):
    """Gallery-style picker: folders on top, image thumbnails below."""
    MAX_IMAGES = 600
    back_closes = True

    def __init__(self, on_done, multiple=False, exts=IMG_EXTS, start=None, **kw):
        super().__init__(**_modal_kwargs(size_hint=(1, 1), background_color=rgba(C["bg"])))
        self.on_done = on_done
        self.multiple = multiple
        self.selected = []
        self.tiles = {}
        self._gen = 0
        self._has_img = {}
        self._n_imgs = 0
        self.dirs_box = None
        root = RoundBox(orientation="vertical", bg=col("bg"), radius=0,
                        padding=[dp(14), dp(10) + top_inset_px(), dp(14), dp(10)], spacing=dp(10))
        close = IconBtn("close", "text", on_tap=self.dismiss)
        self.title = L("pk_title", size=19, bold=True, fill=True)
        self.confirm = Btn(raw="", variant="primary", height_dp=44, font=14, auto_w=True,
                           on_tap=self._finish)
        self.confirm.size_hint = (None, None)
        self.confirm.height = dp(44)
        header_items = [close, self.title]
        if multiple:
            header_items.append(self.confirm)
        root.add_widget(hrow(header_items, height=48))
        roots = self._roots()
        root.add_widget(ChipGroup([(p, n) for n, p in roots], None, self._go_root))
        self.path_lbl = L(raw="", size=12, color="muted", halign="left")
        root.add_widget(self.path_lbl)
        self.sv = ScrollView(do_scroll_x=False, bar_width=dp(3), bar_color=rgba(C["accent"], .5),
                             always_overscroll=False)
        self.box = BoxLayout(orientation="vertical", size_hint_y=None, spacing=dp(8),
                             padding=[0, 0, 0, dp(20)])
        self.box.bind(minimum_height=self.box.setter("height"))
        self.sv.add_widget(self.box)
        root.add_widget(self.sv)
        self.add_widget(root)
        self._update_confirm()
        base = start or APP.store.get("last_dir")
        if not base or not os.path.isdir(base):
            base = roots[0][1] if roots else os.path.expanduser("~")
        self.cwd = base
        self._render()

    def _roots(self):
        base = storage_root()
        out = []
        for key, sub in (("pk_camera", "DCIM/Camera"), ("pk_screenshots", "Pictures/Screenshots"),
                         ("pk_screenshots", "DCIM/Screenshots"), ("pk_pictures", "Pictures"),
                         ("pk_download", "Download")):
            p = os.path.join(base, sub)
            if os.path.isdir(p) and not any(x[1] == p for x in out) and not any(x[0] == T(key) for x in out):
                out.append((T(key), p))
        out.append((T("pk_internal"), base))
        return out

    @guard
    def _go_root(self, path):
        self.cwd = path
        self._render()

    def _update_confirm(self):
        n = len(self.selected)
        self.confirm.set_text(T("pk_select", n=n))
        self.confirm.disabled = (n == 0)

    def _render(self):
        ThumbLoader.new_generation()
        self._gen += 1
        gen = self._gen
        self.box.clear_widgets()
        self.tiles = {}
        self.dirs_box = None
        self.path_lbl.raw = self.cwd
        parent = os.path.dirname(self.cwd.rstrip("/")) or "/"
        if parent != self.cwd:
            self.box.add_widget(FileRow(parent, "..", on_tap=self._open_dir))
        try:
            entries = list(os.scandir(self.cwd))
        except PermissionError:
            self.box.add_widget(L("pk_denied", size=14, color="warn", wrap=True))
            return
        except Exception:
            self.box.add_widget(L("pk_empty", size=14, color="muted", wrap=True))
            return
        dirs, imgs = [], []
        for e in entries:
            if e.name.startswith("."):
                continue
            try:
                if e.is_dir():
                    dirs.append(e)
                elif e.name.lower().endswith(IMG_EXTS):
                    imgs.append((e.stat().st_mtime, e.path))
            except Exception:
                continue
        dirs.sort(key=lambda e: e.name.lower())
        imgs.sort(reverse=True)
        self._n_imgs = len(imgs)
        # only folders that really contain pictures are listed (checked in the background)
        self.dirs_box = BoxLayout(orientation="vertical", size_hint_y=None, spacing=dp(8))
        self.dirs_box.bind(minimum_height=self.dirs_box.setter("height"))
        self.box.add_widget(self.dirs_box)
        if dirs:
            cand = [(e.name, e.path) for e in dirs]
            cache = self._has_img

            def work():
                return [(n, p) for n, p in cand if n != "Android" and dir_has_images(p, cache)]
            run_bg(work, lambda res, err, g=gen: self._dirs_ready(g, res or []))
        if imgs:
            gap = dp(6)
            tile = (Window.width - dp(28) - 2 * gap) / 3.0
            grid = GridLayout(cols=3, spacing=gap, size_hint_y=None, col_force_default=True,
                              row_force_default=True, col_default_width=tile,
                              row_default_height=tile,
                              orientation="rl-tb" if APP.rtl else "lr-tb")
            grid.bind(minimum_height=grid.setter("height"))
            for _t, path in imgs[:self.MAX_IMAGES]:
                tl = ThumbTile(path, tile, self._tap_img)
                self.tiles[path] = tl
                grid.add_widget(tl)
                if path not in ThumbLoader.tex:
                    ThumbLoader.request(path, self._thumb_ready)
            self.box.add_widget(grid)
            if len(imgs) > self.MAX_IMAGES:
                self.box.add_widget(L("pk_more", fmt={"n": self.MAX_IMAGES}, size=12, color="muted", wrap=True))
            self._marks()
        elif not dirs:
            self.box.add_widget(L("pk_empty", size=14, color="muted", wrap=True))
        self.sv.scroll_y = 1

    def _dirs_ready(self, gen, res):
        if gen != self._gen or self.dirs_box is None:
            return
        self.dirs_box.clear_widgets()
        for name, path in res:
            self.dirs_box.add_widget(FileRow(path, name, on_tap=self._open_dir))
        if not res and not self._n_imgs:
            self.dirs_box.add_widget(L("pk_empty", size=14, color="muted", wrap=True))

    def _thumb_ready(self, path, png):
        tl = self.tiles.get(path)
        if tl is not None:
            tl.set_png(png)

    def _marks(self):
        for path, tl in self.tiles.items():
            if path in self.selected:
                tl.set_mark(str(self.selected.index(path) + 1) if self.multiple else "✓")
            else:
                tl.set_mark("")

    def _open_dir(self, row):
        self.cwd = row.path
        self._render()

    def _tap_img(self, tile):
        if not self.multiple:
            self.selected = [tile.path]
            self._finish()
            return
        if tile.path in self.selected:
            self.selected.remove(tile.path)
        else:
            self.selected.append(tile.path)
        self._marks()
        self._update_confirm()

    def _finish(self):
        if not self.selected:
            return
        APP.store.set("last_dir", self.cwd)
        paths = list(self.selected)
        self.dismiss()
        guard(self.on_done)(paths)


def _pdf_roots():
    base = storage_root()
    out = []
    for key, sub in (("pk_download", "Download"), ("pk_documents", "Documents")):
        p = os.path.join(base, sub)
        if os.path.isdir(p) and not any(x[1] == p for x in out):
            out.append((T(key), p))
    out.append((T("pk_internal"), base))
    return out


def _scan_roots():
    roots = [storage_root()]
    try:
        for n in os.listdir("/storage"):
            p = os.path.join("/storage", n)
            if n not in ("emulated", "self") and os.path.isdir(p) and os.access(p, os.R_OK):
                roots.append(p)
    except Exception:
        pass
    return roots


def scan_all_pdfs(limit=3000):
    out, seen = [], set()
    for r in _scan_roots():
        for item in scan_pdfs(r, limit=limit):
            if item[1] not in seen:
                seen.add(item[1])
                out.append(item)
    out.sort(reverse=True)
    return out[:limit]


def scan_pdfs(root, limit=3000, max_depth=9):
    """Every .pdf file under `root` (newest first): [(mtime, path, size)]. Hidden and app-private folders are skipped."""
    out = []
    root = root.rstrip("/") or "/"
    base_depth = root.count("/")
    for cur, dns, fns in os.walk(root):
        depth = cur.count("/") - base_depth
        if depth >= max_depth:
            dns[:] = []
        else:
            dns[:] = [d for d in dns if not d.startswith(".")]
            if os.path.basename(cur) == "Android" and os.path.dirname(cur) == root:
                dns[:] = [d for d in dns if d == "media"]      # keep WhatsApp etc. documents, skip app data
        for f in fns:
            if f.lower().endswith(".pdf") and not f.startswith("."):
                p = os.path.join(cur, f)
                try:
                    st = os.stat(p)
                    if st.st_size > 0:
                        out.append((st.st_mtime, p, st.st_size))
                except Exception:
                    continue
        if len(out) >= limit:
            break
    out.sort(reverse=True)
    return out


class PDFFileRow(Card):
    """One PDF file in the picker (name, size + folder, and the selection number)."""

    def __init__(self, path, sub, on_tap=None, on_long=None, **kw):
        super().__init__(bg=col("card"), radius=dp(16), size_hint_y=None, height=dp(66),
                         padding=[dp(12), dp(6)], spacing=dp(12), **kw)
        self.path = path
        self._tap = on_tap
        self._on_long = on_long
        self._lp = False
        self._ev = None
        ib = AnchorLayout(size_hint_x=None, width=dp(30))
        ib.add_widget(Icon("doc", "accent", 24))
        txt = BoxLayout(orientation="vertical", spacing=dp(1))
        txt.add_widget(L(raw=os.path.basename(path), size=14.5, fill=True))
        txt.add_widget(L(raw=sub, size=12, color="muted", fill=True))
        self.mark = RoundBox(bg=col("accent"), radius=dp(13), size_hint=(None, None), size=(dp(26), dp(26)))
        self.mark_lbl = L(raw="", size=13, bold=True, color="on_acc", fill=True, halign="center")
        self.mark.add_widget(self.mark_lbl)
        self.mark.opacity = 0
        mh = AnchorLayout(size_hint_x=None, width=dp(30))
        mh.add_widget(self.mark)
        # "open" button: look at the PDF in another app before adding it
        oh = AnchorLayout(size_hint_x=None, width=dp(46))
        oh.add_widget(IconBtn("link", "accent", size=40, icon_size=20, bg="card_hi", on_tap=self._open))
        for w in mirror([ib, txt, oh, mh]):
            self.add_widget(w)

    @guard
    def _open(self):
        open_pdf_viewer(self.path)

    def set_mark(self, text):
        on = bool(text)
        self.mark.opacity = 1 if on else 0
        self.mark_lbl.raw = text
        self.outline = col("accent") if on else []

    # long press -> actions menu (share / rename / delete)
    def on_press(self):
        super().on_press()
        self._lp = False
        if self._on_long:
            self._ev = Clock.schedule_once(self._long, 0.5)

    def on_state(self, inst, st):
        super().on_state(inst, st)
        if st == "normal" and self._ev:
            self._ev.cancel()             # finger lifted or the list started scrolling
            self._ev = None

    @guard
    def _long(self, dt):
        self._ev = None
        self._lp = True
        APP.feedback("pop")
        self._on_long(self)

    def on_release(self):
        if self._ev:
            self._ev.cancel()
            self._ev = None
        if self._lp:
            self._lp = False
            return
        if self._tap:
            guard(self._tap)(self)


class PDFPicker(FilePicker):
    """Lists ALL the PDF files on the device in one list (newest first) with a search box.
    Tap the files in the order you want them (1, 2, 3 ...)."""
    MAX_IMAGES = 500

    def __init__(self, on_done, multiple=False, **kw):
        self._all = []
        self._scanned = False
        self._q = ""
        super().__init__(on_done, multiple=multiple, exts=(".pdf",), **kw)
        # search box between the status line and the list
        self.search = InputBox(hint=T("pk_search"), height_dp=48)
        self.search.input.bind(text=lambda i, t: guard(self._on_query)(t))
        self.sv.parent.add_widget(self.search, index=1)
        self._start_scan()

    def _roots(self):
        return []                       # no folder chips: everything is in one list

    def _start_scan(self):
        self._scanned = False
        self._render()

        def done(res, err):
            self._all = res or []
            self._scanned = True
            self._render()
        run_bg(scan_all_pdfs, done)

    def _ask_access(self):
        if not open_all_files_settings():
            return
        self._polls = 0

        def poll(dt):
            self._polls += 1
            if has_all_files_access():
                self._start_scan()
                return False
            return self._polls < 120            # stop checking after ~2 minutes
        Clock.schedule_interval(poll, 1.0)

    def _use_system(self):
        self.dismiss()
        if not pick_pdfs_system(self.on_done, self.multiple):
            APP.toast(T("error"), "error")

    def _on_query(self, text):
        self._q = text
        self._render()

    def _finish(self):
        if not self.selected:
            return
        paths = list(self.selected)
        self.dismiss()
        guard(self.on_done)(paths)

    # ---- long press: share / rename / delete
    def _actions(self, row):
        path = row.path
        box = []

        def go(fn):
            def run():
                box[0].dismiss()
                guard(fn)(path)
            return run
        extra = [Btn(key="share", icon="share", variant="secondary", height_dp=46, font=14, on_tap=go(self._do_share)),
                 Btn(key="rename", icon="text", variant="secondary", height_dp=46, font=14, on_tap=go(self._ask_rename)),
                 Btn(key="delete", icon="trash", variant="danger", height_dp=46, font=14, on_tap=go(self._ask_delete))]
        dlg = Dialog(title=os.path.basename(path), extra=extra,
                     buttons=[(T("cancel"), "ghost", None)])
        box.append(dlg)
        dlg.open()

    def _do_share(self, path):
        uri = content_uri_for_path(path)
        if not share_file(path, "application/pdf", uri):
            APP.toast(T("share_failed", path=os.path.basename(path)), "error")

    def _ask_delete(self, path):
        Dialog(title=T("pk_delete_q"), body=T("pk_delete_body", name=os.path.basename(path)),
               buttons=[(T("cancel"), "secondary", None),
                        (T("delete"), "danger", lambda: guard(self._do_delete)(path))]).open()

    def _do_delete(self, path):
        try:
            os.remove(path)
        except Exception as e:
            APP.log_error(e)
            APP.feedback("error")
            APP.toast(T("pk_action_failed"), "error")
            return
        media_scan(path)
        self._all = [x for x in self._all if x[1] != path]
        if path in self.selected:
            self.selected.remove(path)
            self._update_confirm()
        APP.feedback("success")
        APP.toast(T("pk_deleted"), "ok")
        self._render_keep_scroll()

    def _ask_rename(self, path):
        stem = os.path.splitext(os.path.basename(path))[0]
        box = InputBox(hint=T("rename"), height_dp=52)
        box.input.text = stem
        Dialog(title=T("rename"), extra=[box],
               buttons=[(T("cancel"), "secondary", None),
                        (T("ok"), "primary", lambda: guard(self._do_rename)(path, box.input.text))]).open()

    def _do_rename(self, path, text):
        stem = safe_name(re.sub(r"\.pdf\s*$", "", (text or "").strip(), flags=re.I), "")
        if not stem:
            return
        new = os.path.join(os.path.dirname(path), stem + ".pdf")
        if new == path:
            return
        if os.path.exists(new):
            APP.feedback("error")
            APP.toast(T("pk_name_exists"), "error")
            return
        try:
            os.rename(path, new)
        except Exception as e:
            APP.log_error(e)
            APP.feedback("error")
            APP.toast(T("pk_action_failed"), "error")
            return
        media_scan(path)
        media_scan(new)
        self._all = [((x[0], new, x[2]) if x[1] == path else x) for x in self._all]
        self.selected = [new if x == path else x for x in self.selected]
        APP.feedback("success")
        APP.toast(T("pk_renamed"), "ok")
        self._render_keep_scroll()

    def _render_keep_scroll(self):
        y = self.sv.scroll_y
        self._render()
        Clock.schedule_once(lambda dt: setattr(self.sv, "scroll_y", y), 0)

    def _render(self):
        self.box.clear_widgets()
        self.tiles = {}
        if not self._scanned:
            self.path_lbl.raw = T("pk_scanning")
            return
        q = norm_search(self._q.strip())
        items = [x for x in self._all if not q or q in norm_search(os.path.basename(x[1]))]
        self.path_lbl.raw = T("pk_found_n", n=len(items))
        if not has_all_files_access():                  # Android 11+: without this only part of the device is visible
            self.box.add_widget(L("pk_allow_hint", size=13, color="muted", wrap=True))
            self.box.add_widget(Btn(key="pk_allow_all", icon="plus", on_tap=self._ask_access))
        if not items:
            self.box.add_widget(L("pk_no_pdf", size=14, color="muted", wrap=True))
            if not self._all:
                self.box.add_widget(Btn(key="pk_rescan", variant="secondary", on_tap=self._start_scan))
                self.box.add_widget(Btn(key="pk_use_system", variant="ghost", on_tap=self._use_system))
            return
        for _t, path, size in items[:self.MAX_IMAGES]:
            sub = "%s  ·  %s" % (human_size(size), os.path.basename(os.path.dirname(path)))
            row = PDFFileRow(path, sub, self._tap_img, on_long=self._actions)
            self.tiles[path] = row
            self.box.add_widget(row)
        if len(items) > self.MAX_IMAGES:
            self.box.add_widget(L("pk_more", fmt={"n": self.MAX_IMAGES}, size=12, color="muted", wrap=True))
        self._marks()
        self.sv.scroll_y = 1


# --------------------------------------------------------------------------
# Built-in PDF viewer (Android's own PdfRenderer: no extra library, nothing leaves the device)
# --------------------------------------------------------------------------
_PDF_RENDERER_OK = []


def pdf_renderer_available():
    if not _PDF_RENDERER_OK:
        ok = False
        if platform == "android":
            try:
                from jnius import autoclass
                autoclass("android.graphics.pdf.PdfRenderer")
                ok = True
            except Exception:
                ok = False
        _PDF_RENDERER_OK.append(ok)
    return _PDF_RENDERER_OK[0]


class PdfRenderEngine:
    """Owns the PdfRenderer. PdfRenderer is not thread-safe, so every call runs on ONE worker thread."""

    def __init__(self, path):
        self.path = path
        self.q = queue.Queue()
        self.closed = False
        self.pfd = None
        self.r = None
        threading.Thread(target=self._loop, daemon=True).start()

    def submit(self, fn, cb=None):
        self.q.put((fn, cb))

    def _loop(self):
        while True:
            item = self.q.get()
            if item is None:
                break
            fn, cb = item
            res = err = None
            try:
                res = fn()
            except Exception as e:
                err = e
            if cb is not None and not self.closed:
                Clock.schedule_once(lambda dt, c=cb, r=res, e=err: c(r, e), 0)
        for obj in (self.r, self.pfd):
            try:
                if obj is not None:
                    obj.close()
            except Exception:
                pass

    def close(self):
        self.closed = True
        self.q.put(None)

    def call_sync(self, fn, timeout=180):
        """Run fn on the worker thread and wait for it. Only from a background thread, never from the UI."""
        ev = threading.Event()
        box = []

        def wrapped():
            try:
                box.append((fn(), None))
            except Exception as e:
                box.append((None, e))
            finally:
                ev.set()
        self.submit(wrapped)
        if not ev.wait(timeout) or not box:
            raise IOError("timeout")
        if box[0][1] is not None:
            raise box[0][1]
        return box[0][0]

    # ---- everything below runs on the worker thread
    def open(self):
        from jnius import autoclass
        File = autoclass("java.io.File")
        PFD = autoclass("android.os.ParcelFileDescriptor")
        PR = autoclass("android.graphics.pdf.PdfRenderer")
        self.pfd = PFD.open(File(self.path), PFD.MODE_READ_ONLY)
        self.r = PR(self.pfd)
        sizes = []
        for i in range(self.r.getPageCount()):
            p = self.r.openPage(i)
            sizes.append((max(1, p.getWidth()), max(1, p.getHeight())))
            p.close()
        return sizes

    def render(self, idx, width_px, out_path):
        from jnius import autoclass
        Bitmap = autoclass("android.graphics.Bitmap")
        Config = autoclass("android.graphics.Bitmap$Config")
        Fmt = autoclass("android.graphics.Bitmap$CompressFormat")
        Canvas = autoclass("android.graphics.Canvas")
        FOS = autoclass("java.io.FileOutputStream")
        Page = autoclass("android.graphics.pdf.PdfRenderer$Page")
        p = self.r.openPage(idx)
        try:
            w, h = p.getWidth(), p.getHeight()
            hp = max(1, int(width_px * h / float(max(1, w))))
            bmp = Bitmap.createBitmap(int(width_px), hp, Config.ARGB_8888)
            Canvas(bmp).drawARGB(255, 255, 255, 255)    # PdfRenderer draws on transparent; drawARGB has one signature only
            p.render(bmp, None, None, Page.RENDER_MODE_FOR_DISPLAY)
        finally:
            p.close()
        fos = FOS(out_path)
        try:
            bmp.compress(Fmt.JPEG, 88, fos)
        finally:
            fos.close()
            bmp.recycle()
        return out_path


class _PdfPage(Widget):
    """One page: grey placeholder until its picture is ready."""

    def __init__(self, idx, width, height, **kw):
        super().__init__(size_hint=(None, None), size=(width, height), **kw)
        self.idx = idx
        with self.canvas:
            Color(0.93, 0.93, 0.93, 1)
            self._bg = Rectangle(pos=self.pos, size=self.size)
            self._ic = Color(1, 1, 1, 0)
            self._img = Rectangle(pos=self.pos, size=self.size)
        self.bind(pos=self._u, size=self._u)

    def _u(self, *a):
        self._bg.pos = self._img.pos = self.pos
        self._bg.size = self._img.size = self.size

    def set_tex(self, tex):
        self._img.texture = tex
        self._ic.a = 1 if tex is not None else 0


class PDFViewer(ModalView):
    """Look at a PDF inside the app: pages load as you scroll, 1x / 2x / 3x zoom."""
    PAD = 6
    GAP = 10

    def __init__(self, path, **kw):
        super().__init__(**_modal_kwargs(size_hint=(1, 1), background_color=rgba(C["bg"])))
        self.path = path
        self.zoom = 1
        self.pages = []
        self.sizes = []
        self.tops = []
        self.rendered = set()
        self.pending = set()
        self._wanted = set()
        self._fails = {}
        self._err_shown = False
        self._gen = 0
        self._ev = None
        self._disp_w = 1
        self.dir = os.path.join(tmp_dir(), "pv_%d" % int(time.time() * 1000))
        os.makedirs(self.dir, exist_ok=True)
        self.engine = PdfRenderEngine(path)
        root = RoundBox(orientation="vertical", bg=col("bg"), radius=0,
                        padding=[dp(8), dp(10) + top_inset_px(), dp(8), dp(10)], spacing=dp(8))
        close = IconBtn("close", "text", on_tap=self.dismiss)
        self.title = L(raw=os.path.basename(path), size=16, bold=True, fill=True)
        self.page_lbl = L(raw="", size=12.5, color="muted", fill=True, size_hint_x=None, width=dp(70),
                          halign="center")
        self.zoom_btn = Btn(raw="1×", variant="secondary", height_dp=44, font=14, auto_w=True,
                            on_tap=self._cycle_zoom)
        self.zoom_btn.size_hint = (None, None)
        self.zoom_btn.height = dp(44)
        root.add_widget(hrow([close, self.title, self.page_lbl, self.zoom_btn], height=48))
        self.sv = ScrollView(do_scroll_x=False, do_scroll_y=True, bar_width=dp(3),
                             bar_color=rgba(C["accent"], .5), always_overscroll=False,
                             scroll_type=["bars", "content"])
        self.box = BoxLayout(orientation="vertical", size_hint=(None, None), spacing=dp(self.GAP),
                             padding=[dp(self.PAD), 0, dp(self.PAD), dp(20)])
        self.box.bind(minimum_height=self.box.setter("height"))
        self.sv.add_widget(self.box)
        self.sv.bind(scroll_y=self._sched, height=self._sched)
        self.box.bind(height=self._sched)
        root.add_widget(self.sv)
        self.add_widget(root)
        self.box.width = Window.width
        self.engine.submit(self.engine.open, self._opened)

    def _fail(self, err):
        msg = str(err).lower()
        APP.feedback("error")
        APP.toast(T("pdf_enc") if ("password" in msg or "security" in msg) else T("pdf_bad"), "error")
        self.dismiss()

    def _opened(self, sizes, err):
        if err or not sizes:
            self._fail(err or "bad")
            return
        self.sizes = sizes
        self._build()

    def _build(self):
        self._gen += 1
        self.pending.clear()
        self.rendered.clear()
        self._wanted = set()
        self._fails = {}
        self.box.clear_widgets()
        self.pages = []
        self.tops = []
        width = Window.width * self.zoom
        self.box.width = width
        self.sv.do_scroll_x = self.zoom > 1
        self._disp_w = max(50, int(width - 2 * dp(self.PAD)))
        y = 0.0
        for i, (pw, ph) in enumerate(self.sizes):
            h = max(40, int(self._disp_w * ph / float(pw)))
            pg = _PdfPage(i, self._disp_w, h)
            self.pages.append(pg)
            self.tops.append(y)
            y += h + dp(self.GAP)
            self.box.add_widget(pg)
        self.sv.scroll_y = 1
        self.sv.scroll_x = 0
        self.page_lbl.raw = "1 / %d" % len(self.pages)
        self._sched()

    def _cycle_zoom(self):
        if not self.pages:
            return
        self.zoom = {1: 2, 2: 3, 3: 1}[self.zoom]
        self.zoom_btn.set_text("%d×" % self.zoom)
        self._build()

    def _sched(self, *a):
        if self._ev is not None:
            self._ev.cancel()
        self._ev = Clock.schedule_once(guard(lambda dt: self._update()), 0.08)

    def _update(self):
        if not self.pages or self.sv.height <= 0:
            return
        sv_h = float(self.sv.height)
        view_lo = self.sv.to_window(self.sv.x, self.sv.y)[1]
        view_hi = view_lo + sv_h
        mid = (view_lo + view_hi) / 2.0
        want, cur, best = [], 0, None
        for i, pg in enumerate(self.pages):
            lo = pg.to_window(pg.x, pg.y)[1]
            hi = lo + pg.height
            if hi >= view_lo - sv_h * 0.5 and lo <= view_hi + sv_h * 0.5:
                want.append((abs((lo + hi) / 2.0 - mid), i))
            d = abs((lo + hi) / 2.0 - mid)
            if best is None or d < best:
                best, cur = d, i
        want.sort()
        want = [i for _d, i in want]
        self.page_lbl.raw = "%d / %d" % (cur + 1, len(self.pages))
        self._wanted = set(want)
        for i in list(self.rendered):                      # free the pictures that are far away
            if i not in self._wanted:
                self.rendered.discard(i)
                self.pages[i].set_tex(None)
        for i in want:
            if i not in self.rendered and i not in self.pending and self._fails.get(i, 0) < 2:
                self._request(i)

    def _request(self, i):
        self.pending.add(i)
        gen = self._gen
        wpx = min(2160, self._disp_w)
        out = os.path.join(self.dir, "%d_%d.jpg" % (gen, i))

        def work():
            if gen != self._gen or i not in self._wanted:
                return None                                 # scrolled away already
            return self.engine.render(i, wpx, out)
        self.engine.submit(work, lambda res, err, i=i, g=gen: self._got(g, i, res, err))

    def _got(self, gen, i, path, err):
        if gen != self._gen:
            self._rm(path)
            return
        self.pending.discard(i)
        if err or not path:
            self._rm(path)
            if err:
                self._fails[i] = self._fails.get(i, 0) + 1
                try:
                    APP.log_error(err)
                except Exception:
                    pass
                if not self._err_shown:                     # say what went wrong (once), not a silent blank page
                    self._err_shown = True
                    APP.toast(("%s: %s" % (type(err).__name__, err))[:140], "error", 6)
            self._sched()                                   # a skipped page is asked again if still visible
            return
        try:
            if i in self._wanted and i < len(self.pages):
                self.pages[i].set_tex(CoreImage(path, nocache=True).texture)
                self.rendered.add(i)
        except Exception:
            traceback.print_exc()
        self._rm(path)

    @staticmethod
    def _rm(path):
        try:
            if path:
                os.remove(path)
        except Exception:
            pass

    def on_dismiss(self, *a):
        try:
            self.engine.close()
        except Exception:
            pass
        try:
            import shutil
            shutil.rmtree(self.dir, ignore_errors=True)
        except Exception:
            pass


def content_uri_for_path(path):
    """content:// uri of a file that lives in shared storage (found through the MediaStore), or None.
    Other apps cannot read a plain file path any more on Android 10+, they need this."""
    try:
        from jnius import autoclass
        cr = _android_activity().getContentResolver()
        String = autoclass("java.lang.String")
        Files = autoclass("android.provider.MediaStore$Files")
        base = Files.getContentUri(String("external"))
        arr = autoclass("java.lang.String")
        cur = cr.query(base, [String("_id")], String("_data=?"), [String(path)], None)
        if cur is None:
            return None
        try:
            if cur.moveToFirst():
                fid = cur.getLong(0)
                return autoclass("android.content.ContentUris").withAppendedId(base, fid).toString()
        finally:
            cur.close()
    except Exception:
        pass
    return None


def open_pdf_viewer(path, uri=None):
    """Show a PDF inside the app; another app only if the built-in viewer cannot be used."""
    if path and os.path.isfile(path) and pdf_renderer_available():
        PDFViewer(path).open()
        return
    if not open_file_external(path, "application/pdf", uri):
        APP.toast(T("open_failed"), "error")


# --------------------------------------------------------------------------
# Tool registry
# --------------------------------------------------------------------------
TOOLS = [
    {"id": "qr", "icon": "qr", "title": "tool_qr", "sub": "tool_qr_sub",
     "kw": "qr code barcode generate create make رمز باركود انشاء كود"},
    {"id": "compress", "icon": "image", "title": "tool_compress", "sub": "tool_compress_sub",
     "kw": "image photo picture compress resize reduce size jpeg webp صورة صور ضغط تصغير حجم"},
    {"id": "pdftools", "icon": "doc", "title": "tool_pdftools", "sub": "tool_pdftools_sub",
     "kw": "pdf tools convert images photos document pages compress reduce shrink size merge combine join "
           "أدوات ادوات تحويل صور مستند ملف ضغط تصغير حجم دمج ضم جمع تقسيم تعديل بي دي اف"},
    {"id": "pdf", "icon": "doc", "title": "tool_pdf", "sub": "tool_pdf_sub", "hidden": True,
     "kw": "pdf convert images photos document pages تحويل صور مستند ملف"},
    {"id": "text", "icon": "text", "title": "tool_text", "sub": "tool_text_sub",
     "kw": "text words count characters clean duplicate lines spaces نص كلمات حروف عد تنظيف مسافات"},
    {"id": "scan", "icon": "camera", "title": "tool_scan", "sub": "tool_scan_sub",
     "kw": "qr scan scanner camera read مسح قارئ كاميرا قراءة"},
    {"id": "pdfzip", "icon": "compress", "title": "tool_pdfzip", "sub": "tool_pdfzip_sub", "hidden": True,
     "kw": "pdf compress reduce shrink size smaller ضغط تصغير حجم ملف بي دي اف"},
    {"id": "pdfmerge", "icon": "merge", "title": "tool_pdfmerge", "sub": "tool_pdfmerge_sub", "hidden": True,
     "kw": "pdf merge combine join documents order دمج ضم جمع ملفات ترتيب"},
    {"id": "pdfsplit", "icon": "scissors", "title": "tool_pdfsplit", "sub": "tool_pdfsplit_sub", "hidden": True,
     "kw": "pdf split cut delete remove pages extract تقسيم تقطيع حذف مسح صفحات فصل قص ملف بي دي اف"},
    {"id": "pdfedit", "icon": "pen", "title": "tool_pdfedit", "sub": "tool_pdfedit_sub", "hidden": True,
     "kw": "pdf edit draw write text image annotate sign pen highlight تعديل تحرير رسم كتابة نص صورة قلم توقيع هايلايتر ملف بي دي اف"},
]
TOOL_BY_ID = {t["id"]: t for t in TOOLS}
TABS = ["home", "history", "favorites", "settings"]
TAB_ICONS = {"home": "home", "history": "history", "favorites": "heart", "settings": "gear"}


class PageScroll(ScrollView):
    """A page ScrollView that leaves drags to a long text box (so the text box can scroll
    by itself) instead of scrolling the whole page."""

    def _scrollable_input_at(self, touch):
        try:
            for w in self.walk(restrict=True):
                if isinstance(w, InputBox) and w.can_scroll() and w.collide_point(*touch.pos):
                    return w
        except Exception:
            pass
        return None

    def on_touch_down(self, touch):
        if self.collide_point(*touch.pos):
            # children of a ScrollView live in the scrolled frame: convert the touch exactly
            # like ScrollView itself does before handing it to them
            touch.push()
            try:
                touch.apply_transform_2d(self.to_local)
                box = self._scrollable_input_at(touch)
                ret = bool(box.dispatch("on_touch_down", touch)) if box is not None else None
            finally:
                touch.pop()
            if box is not None:
                return ret        # only the text box gets it: no page scrolling, no buttons below
        return super().on_touch_down(touch)


def make_scroll(pad=(20, 8, 20, 28), spacing=14):
    sv = PageScroll(do_scroll_x=False, bar_width=dp(3), bar_color=rgba(C["accent"], .5),
                    bar_inactive_color=rgba(C["accent"], .15), scroll_type=["bars", "content"],
                    always_overscroll=False)
    body = BoxLayout(orientation="vertical", size_hint_y=None, spacing=dp(spacing),
                     padding=[dp(p) for p in pad])
    body.bind(minimum_height=body.setter("height"))
    sv.add_widget(body)
    return sv, body


def section(key):
    return L(key, size=14, color="muted", bold=True)


def setting_card():
    c = RoundBox(orientation="vertical", bg=col("card"), radius=dp(22), padding=dp(16),
                 spacing=dp(14), size_hint_y=None)
    c.bind(minimum_height=c.setter("height"))
    return c


# --------------------------------------------------------------------------
# Screen bases
# --------------------------------------------------------------------------
class AppScreen(Screen):
    show_nav = False

    def __init__(self, name, **kw):
        super().__init__(name=name, **kw)
        with self.canvas.before:
            Color(*rgba(C["bg"]))
            self._bgr = Rectangle(pos=self.pos, size=self.size)
        self.bind(pos=self._ubg, size=self._ubg)

    def _ubg(self, *a):
        self._bgr.pos = self.pos
        self._bgr.size = self.size

    def refresh(self):
        pass

    def on_pre_leave(self, *a):
        unfocus_all(self)


class TabScreen(AppScreen):
    show_nav = True
    title_key = ""

    def __init__(self, name, **kw):
        super().__init__(name, **kw)
        root = BoxLayout(orientation="vertical")
        root.add_widget(L(self.title_key, size=28, bold=True, h=48,
                          size_hint_x=1, padding=(dp(20), 0)))
        self.sv, self.body = make_scroll(pad=(20, 4, 20, 24))
        root.add_widget(self.sv)
        self.add_widget(root)
        self.build()

    def build(self):
        pass

    def on_pre_enter(self, *a):
        self.refresh()


class ToolScreen(AppScreen):
    title_key = ""
    bottom_pad = 28        # screens with text boxes get extra room for the keyboard

    def __init__(self, tool_id, **kw):
        super().__init__(tool_id, **kw)
        self.tool_id = tool_id
        root = BoxLayout(orientation="vertical")
        self.back_btn = IconBtn("back", "text", on_tap=lambda: APP.back(), mirror_rtl=True)
        self.heart = IconBtn("heart", "accent", on_tap=self._fav)
        title = L(self.title_key, size=22, bold=True, fill=True)
        hdr = hrow([self.back_btn, title, self.heart], spacing=12,
                   padding=[dp(16), dp(12), dp(16), dp(8)], height=68)
        root.add_widget(hdr)
        self.sv, self.body = make_scroll(pad=(20, 8, 20, self.bottom_pad))
        root.add_widget(self.sv)
        self.add_widget(root)
        self._heart_state()
        self.build_body()

    def _heart_state(self):
        fav = self.tool_id in APP.store.get("favorites")
        self.heart.set_icon("heart_fill" if fav else "heart", "accent")

    def _fav(self):
        APP.toggle_fav(self.tool_id)
        self._heart_state()

    def build_body(self):
        pass

    def on_pre_enter(self, *a):
        self._heart_state()


# --------------------------------------------------------------------------
# Home
# --------------------------------------------------------------------------
class ToolCard(Card):
    def __init__(self, tool, wide=False, **kw):
        self.tool = tool
        self._lp = False
        self._ev = None
        fav = tool["id"] in APP.store.get("favorites")
        if wide:
            super().__init__(bg=col("card"), radius=dp(24), orientation="horizontal",
                             size_hint_y=None, height=dp(88), padding=dp(16), spacing=dp(14), **kw)
            badge = RoundBox(bg=col("card_hi"), radius=dp(16), size_hint=(None, None),
                             size=(dp(54), dp(54)), padding=dp(14))
            badge.add_widget(Icon(tool["icon"], "accent", 26))
            txt = BoxLayout(orientation="vertical", spacing=dp(2))
            txt.add_widget(L(tool["title"], size=17, bold=True, fill=True))
            txt.add_widget(L(tool["sub"], size=12.5, color="muted", fill=True))
            items = [badge, txt]
            if fav:
                items.append(Icon("heart_fill", "accent", 16))
            for w in mirror(items):
                self.add_widget(w)
        else:
            super().__init__(bg=col("card"), radius=dp(24), orientation="vertical",
                             size_hint_y=None, height=dp(138), padding=dp(16), spacing=dp(4), **kw)
            top = [Icon(tool["icon"], "accent", 28), Widget()]
            if fav:
                top.append(Icon("heart_fill", "accent", 14))
            self.add_widget(hrow(top, height=32))
            self.add_widget(Widget())
            self.add_widget(L(tool["title"], size=17, bold=True, h=26))
            self.add_widget(L(tool["sub"], size=12.5, color="muted", h=20))

    def on_press(self):
        super().on_press()
        self._lp = False
        self._ev = Clock.schedule_once(self._long, 0.55)

    def on_state(self, inst, st):
        super().on_state(inst, st)
        if st == "normal" and self._ev:
            self._ev.cancel()
            self._ev = None

    @guard
    def _long(self, dt):
        self._lp = True
        APP.feedback("pop")
        APP.toggle_fav(self.tool["id"])

    @guard
    def on_release(self):
        if self._ev:
            self._ev.cancel()
            self._ev = None
        if self._lp:
            return
        APP.open_tool(self.tool["id"])


class HomeScreen(AppScreen):
    show_nav = True

    def __init__(self, **kw):
        super().__init__("home", **kw)
        sv, body = make_scroll(pad=(20, 10, 20, 24), spacing=16)
        self.body = body
        logo = find_asset("logo.png")
        if logo:
            # the app logo (rounded square picture) instead of the plain wrench badge
            badge = BoxLayout(size_hint=(None, None), size=(dp(60), dp(60)))
            badge.add_widget(make_img(source=logo))
        else:
            badge = RoundBox(bg=col("badge"), radius=dp(18), size_hint=(None, None),
                             size=(dp(56), dp(56)), padding=dp(12))
            badge.add_widget(Icon("wrench", "accent", 32))
        head = BoxLayout(orientation="vertical", spacing=0)
        head.add_widget(L("app_name", size=32, bold=True, h=52))
        head.add_widget(L("tagline", size=16, color="muted", h=28))
        body.add_widget(hrow([head, badge], height=84))
        # search
        self.search = InputBox(hint=T("search_hint"), height_dp=56)
        self.search.input.bind(text=lambda i, t: guard(self.render_tools)(t))
        sbox = RoundBox(bg=col("card"), radius=dp(18), size_hint_y=None, height=dp(56),
                        padding=[dp(16), 0], spacing=dp(6))
        self.search.bg = (0, 0, 0, 0)
        self.search.size_hint_y = 1
        sbox.add_widget(hrow([Icon("search", "muted", 22), self.search], spacing=4))
        body.add_widget(sbox)
        self.sec = L("popular", size=19, bold=True, h=34)
        body.add_widget(self.sec)
        self.tools_box = BoxLayout(orientation="vertical", spacing=dp(12), size_hint_y=None)
        self.tools_box.bind(minimum_height=self.tools_box.setter("height"))
        body.add_widget(self.tools_box)
        self.add_widget(sv)
        self.render_tools("")

    def render_tools(self, query=""):
        q = norm_search(query.strip())
        self.tools_box.clear_widgets()
        found = []
        for t in TOOLS:
            if t.get("hidden") and not q:
                continue                     # the tools inside the PDF group only show up when searching
            hay = norm_search(tr_both(t["title"]) + " " + tr_both(t["sub"]) + " " + t["kw"])
            if not q or all(part in hay for part in q.split()):
                found.append(t)
        if q:
            # a search finds the tool itself, not the group that contains it:
            # the group is shown only when none of its own tools match
            if any(t["id"] in ("pdf", "pdfzip", "pdfmerge", "pdfsplit", "pdfedit") for t in found):
                found = [t for t in found if t["id"] != "pdftools"]
        self.sec.key = "results" if q else "popular"
        if not found:
            self.tools_box.add_widget(L("no_results", size=15, color="muted", wrap=True))
            return
        i = 0
        while i < len(found):
            left = found[i]
            if i + 1 < len(found) and not (not q and left["id"] == "scan"):
                row = BoxLayout(orientation="horizontal", spacing=dp(12), size_hint_y=None, height=dp(138))
                pair = [ToolCard(left), ToolCard(found[i + 1])]
                for w in mirror(pair):
                    row.add_widget(w)
                self.tools_box.add_widget(row)
                i += 2
            else:
                self.tools_box.add_widget(ToolCard(left, wide=True))
                i += 1

    def refresh(self):
        self.render_tools(self.search.input.text)

    def on_pre_enter(self, *a):
        self.refresh()


class FavoritesScreen(TabScreen):
    title_key = "nav_favorites"

    def refresh(self):
        self.body.clear_widgets()
        favs = [TOOL_BY_ID[i] for i in APP.store.get("favorites") if i in TOOL_BY_ID]
        if not favs:
            self.body.add_widget(vgap(60))
            holder = AnchorLayout(size_hint_y=None, height=dp(70))
            holder.add_widget(Icon("heart", "muted", 56))
            self.body.add_widget(holder)
            self.body.add_widget(L("fav_empty", size=15, color="muted", wrap=True, halign="center"))
            return
        for t in favs:
            self.body.add_widget(ToolCard(t, wide=True))


class HistoryScreen(TabScreen):
    title_key = "nav_history"

    def refresh(self):
        self.body.clear_widgets()
        items = APP.store.get("history") or []
        if not items:
            self.body.add_widget(vgap(60))
            holder = AnchorLayout(size_hint_y=None, height=dp(70))
            holder.add_widget(Icon("history", "muted", 56))
            self.body.add_widget(holder)
            self.body.add_widget(L("history_empty", size=15, color="muted", wrap=True, halign="center"))
            return
        for it in items[:60]:
            t = TOOL_BY_ID.get(it.get("tool"))
            if not t:
                continue
            card = Card(bg=col("card"), radius=dp(18), size_hint_y=None, height=dp(72),
                        padding=[dp(14), dp(8)], spacing=dp(12))
            card.bind(on_release=lambda inst, tid=t["id"]: APP.open_tool(tid))
            txt = BoxLayout(orientation="vertical", spacing=dp(1))
            txt.add_widget(L(t["title"], size=15, bold=True, fill=True))
            txt.add_widget(L(raw=it.get("detail", ""), size=12.5, color="muted", fill=True))
            when = L(raw=rel_time(it.get("ts", 0)), size=11.5, color="muted", fill=True,
                     size_hint_x=None, width=dp(74), halign="left" if APP.rtl else "right")
            for w in mirror([Icon(t["icon"], "accent", 24), txt, when]):
                card.add_widget(w)
            self.body.add_widget(card)
        self.body.add_widget(vgap(4))
        self.body.add_widget(Btn(key="clear_history", icon="trash", variant="danger",
                                 on_tap=self._clear, height_dp=48, font=14))

    def _clear(self):
        APP.store.set("history", [])
        APP.toast(T("history_cleared"))
        self.refresh()


class SettingsScreen(TabScreen):
    title_key = "nav_settings"

    def build(self):
        b = self.body
        st = APP.store
        # language
        c = setting_card()
        c.add_widget(hrow([Icon("globe", "accent", 22), L("language", size=16, bold=True, fill=True)],
                          height=30, spacing=10))
        c.add_widget(ChipGroup([("ar", T("lang_ar_name")), ("en", T("lang_en_name"))],
                               I18N.lang, on_change=lambda v: APP.set_lang(v)))
        b.add_widget(c)
        # appearance: light / dark / same as the device
        c = setting_card()
        c.add_widget(hrow([Icon("sun", "accent", 22), L("theme", size=16, bold=True, fill=True)],
                          height=30, spacing=10))
        c.add_widget(ChipGroup([("system", T("theme_system")), ("light", T("theme_light")),
                                ("dark", T("theme_dark"))],
                               st.get("theme"), on_change=lambda v: APP.set_theme(v)))
        b.add_widget(c)
        # sound / haptics
        c = setting_card()
        c.add_widget(self._toggle_row("volume", "sounds", st.get("sound"), self._on_sound))
        vol = SliderX(vmin=0, vmax=100, step=5, value=int(st.get("volume") * 100))
        vol.bind(on_commit=self._on_volume)
        c.add_widget(L("volume", size=13, color="muted", h=22))
        c.add_widget(vol)
        c.add_widget(self._toggle_row("vibrate", "vibration", st.get("vibrate"), self._on_vib))
        b.add_widget(c)
        # about
        c = setting_card()
        c.add_widget(L("about", size=16, bold=True, h=26))
        c.add_widget(L("about_text", size=13.5, color="muted", wrap=True))
        c.add_widget(L("version", fmt={"v": APP_VERSION}, size=12.5, color="muted", h=22))
        b.add_widget(c)

    def _toggle_row(self, icon, key, value, cb):
        tg = Toggle(active=bool(value), on_change=cb)
        return hrow([Icon(icon, "accent", 22), L(key, size=15.5, fill=True), tg], height=40, spacing=12)

    def _on_sound(self, v):
        APP.store.set("sound", v)

    def _on_vib(self, v):
        APP.store.set("vibrate", v)
        if v:
            vibrate_ms(30)

    def _on_volume(self, slider):
        APP.store.set("volume", slider.value / 100.0)
        APP.feedback("tap")


# --------------------------------------------------------------------------
# Tool: QR generator
# --------------------------------------------------------------------------
class QRCreateScreen(ToolScreen):
    bottom_pad = 330
    title_key = "tool_qr"

    def build_body(self):
        b = self.body
        self.kind = "auto"
        self.palette = "classic"
        self.img = None
        self.payload = ""
        self._saved = None
        self._ev = None
        self._warned = False
        b.add_widget(section("qr_content"))
        self.inp = InputBox(hint=T("qr_hint"), multiline=True, height_dp=104)
        self.inp.input.bind(text=lambda i, t: self._sched())
        b.add_widget(self.inp)
        b.add_widget(section("qr_type"))
        b.add_widget(ChipGroup([("auto", T("qr_auto")), ("link", T("qr_link")),
                                ("phone", T("qr_phone")), ("text", T("qr_text"))],
                               "auto", on_change=self._set_kind))
        b.add_widget(section("qr_color"))
        b.add_widget(SwatchRow([(k, v[0]) for k, v in QR_PALETTES.items()], "classic", self._set_pal))
        self.info = L(raw="", size=13, color="accent", h=22)
        b.add_widget(self.info)
        self.pv = RoundBox(bg=col("card"), radius=dp(26), size_hint=(None, None),
                           size=(dp(268), dp(268)), padding=dp(16))
        self.pv_img = make_img(opacity=0)
        self.ph = BoxLayout(orientation="vertical", spacing=dp(8))
        holder = AnchorLayout(anchor_x="center", anchor_y="bottom")
        holder.add_widget(Icon("qr", "muted", 58))
        self.ph.add_widget(holder)
        self.ph.add_widget(L("qr_placeholder", size=13.5, color="muted", h=26, halign="center"))
        self.pv.add_widget(self.ph)
        wrap = AnchorLayout(size_hint_y=None, height=dp(268))
        wrap.add_widget(self.pv)
        b.add_widget(wrap)
        b.add_widget(Btn(key="qr_generate", icon="sparkle", on_tap=self._generate))
        self.save_btn = Btn(key="save", icon="save", variant="secondary", on_tap=self._save)
        self.share_btn = Btn(key="share", icon="share", variant="secondary", on_tap=self._share)
        self.save_btn.disabled = self.share_btn.disabled = True
        b.add_widget(hrow([self.save_btn, self.share_btn], height=52, spacing=12))

    def _set_kind(self, v):
        self.kind = v
        self._render()

    def _set_pal(self, v):
        self.palette = v
        self._render()

    def _sched(self):
        if self._ev:
            self._ev.cancel()
        self._ev = Clock.schedule_once(lambda dt: self._render(), 0.45)

    def _clear_preview(self):
        self.img = None
        self._saved = None
        self.pv_img.opacity = 0
        if self.pv_img.parent:
            self.pv.remove_widget(self.pv_img)
        if not self.ph.parent:
            self.pv.add_widget(self.ph)
        self.pv.bg = col("card")
        self.save_btn.disabled = self.share_btn.disabled = True
        self.info.raw = ""

    @guard
    def _generate(self):
        if not self.inp.input.text.strip():
            APP.feedback("error")
            APP.toast(T("qr_empty"), "error")
            return
        if self._render(explicit=True):
            APP.feedback("success")
            APP.log_event("qr", self.payload[:80])

    def _render(self, explicit=False):
        txt = self.inp.input.text.strip()
        if not txt:
            self._clear_preview()
            return False
        if not HAS_PIL:
            APP.toast(T("need_pil"), "error")
            return False
        payload, kind = build_payload(txt, self.kind)
        try:
            m = qr_matrix(payload, "M")
        except RuntimeError:
            if not self._warned or explicit:
                APP.toast(T("need_qrlib"), "error")
                self._warned = True
            return False
        except Exception:
            self._clear_preview()
            APP.toast(T("qr_too_long"), "error")
            return False
        self.payload = payload
        fg = QR_PALETTES[self.palette][0]
        self.img = render_qr(m, fg=fg)
        self._saved = None
        self.pv_img.texture = png_texture(pil_to_png_bytes(self.img, 700), nearest=True)
        self.pv.bg = col("white")
        if self.ph.parent:
            self.pv.remove_widget(self.ph)
        if not self.pv_img.parent:
            self.pv.add_widget(self.pv_img)
        self.pv_img.opacity = 1
        self.save_btn.disabled = self.share_btn.disabled = False
        if self.kind == "auto":
            names = {"link": "qr_link", "phone": "qr_phone", "email": "kind_email", "text": "qr_text"}
            self.info.raw = T("qr_detected", kind=T(names.get(kind, "qr_text")))
        else:
            self.info.raw = ""
        return True

    def _write(self):
        """Save the picture where the Gallery can see it. -> (shown_text, uri, local_path) or None."""
        if self.img is None:
            return None
        if self._saved and published_alive(self._saved):
            return self._saved                       # already saved and still there
        self._saved = None                           # deleted meanwhile (or never saved): save again
        name = "QR_%s.png" % now_stamp()
        tmp = os.path.join(tmp_dir(), name)
        self.img.save(tmp, "PNG")
        self._saved = publish_file(tmp, name, "image/png", "image", APP.user_data_dir)
        return self._saved

    @guard
    def _save(self):
        try:
            res = self._write()
        except Exception as e:
            APP.save_failed(e)
            return
        if res:
            APP.feedback("success")
            APP.toast(T("saved_to", path=res[0]), "ok")
            APP.log_event("qr", res[0])

    @guard
    def _share(self):
        try:
            res = self._write()
        except Exception as e:
            APP.save_failed(e)
            return
        if res and not share_file(res[2], "image/png", res[1]):
            APP.toast(T("share_failed", path=res[0]))


# --------------------------------------------------------------------------
# Tool: image compressor
# --------------------------------------------------------------------------
class CompressScreen(ToolScreen):
    title_key = "tool_compress"

    def build_body(self):
        b = self.body
        self.src = None
        self.base = None
        self.orig = 0
        self.result = None
        self.quality = 70
        self.scale = 1.0
        self.fmt = "JPEG"
        self._job = 0
        self._ev = None
        self._running = False
        self._again = False
        # pick card
        self.pick_t = L("cp_pick", size=16.5, bold=True, fill=True)
        self.pick_s = L("cp_pick_sub", size=12.5, color="muted", fill=True)
        txt = BoxLayout(orientation="vertical", spacing=dp(2))
        txt.add_widget(self.pick_t)
        txt.add_widget(self.pick_s)
        pick = Card(bg=col("card"), radius=dp(22), size_hint_y=None, height=dp(86),
                    padding=dp(16), spacing=dp(14))
        badge = RoundBox(bg=col("card_hi"), radius=dp(16), size_hint=(None, None),
                         size=(dp(54), dp(54)), padding=dp(14))
        badge.add_widget(Icon("image", "accent", 26))
        for w in mirror([badge, txt]):
            pick.add_widget(w)
        pick.bind(on_release=lambda *a: self._pick())
        b.add_widget(pick)
        # preview
        self.pv_card = RoundBox(bg=col("card"), radius=dp(22), size_hint_y=None, height=dp(230),
                                padding=dp(10))
        self.pv = make_img()
        self.pv_ph = L("cp_no_image", size=14, color="muted", fill=True, halign="center")
        self.pv_card.add_widget(self.pv_ph)
        b.add_widget(self.pv_card)
        # controls
        c = setting_card()
        self.q_val = L(raw="70%", size=15, bold=True, color="accent", fill=True,
                       size_hint_x=None, width=dp(60), halign="left" if APP.rtl else "right")
        c.add_widget(hrow([L("cp_quality", size=15, bold=True, fill=True), self.q_val], height=28))
        self.slider = SliderX(vmin=10, vmax=100, step=1, value=70)
        self.slider.bind(value=self._on_q, on_commit=lambda *a: self._schedule(0.05))
        c.add_widget(self.slider)
        c.add_widget(L("cp_scale", size=15, bold=True, h=26))
        c.add_widget(ChipGroup([(1.0, "100%"), (0.75, "75%"), (0.5, "50%"), (0.25, "25%")], 1.0,
                               on_change=self._on_scale))
        c.add_widget(L("cp_format", size=15, bold=True, h=26))
        self.fmt_group = ChipGroup([("JPEG", "JPEG"), ("WEBP", "WEBP"), ("PNG", "PNG")], "JPEG",
                                   on_change=self._on_fmt)
        c.add_widget(self.fmt_group)
        self.note = L("cp_lossless", size=12.5, color="muted", wrap=True)
        self.note.opacity = 0
        c.add_widget(self.note)
        b.add_widget(c)
        # stats
        self.stats = setting_card()
        self.s_before = L(raw="-", size=14.5, bold=True, fill=True, size_hint_x=None, width=dp(190),
                          halign="left" if APP.rtl else "right")
        self.s_after = L(raw="-", size=14.5, bold=True, color="accent", fill=True, size_hint_x=None,
                         width=dp(190), halign="left" if APP.rtl else "right")
        self.stats.add_widget(hrow([L("cp_before", size=14.5, color="muted", fill=True), self.s_before], height=26))
        self.stats.add_widget(hrow([L("cp_after", size=14.5, color="muted", fill=True), self.s_after], height=26))
        self.s_saved = L(raw="", size=15.5, bold=True, color="ok", wrap=True, halign="center")
        self.stats.add_widget(self.s_saved)
        b.add_widget(self.stats)
        self.save_btn = Btn(key="cp_save", icon="save", on_tap=self._save)
        self.save_btn.disabled = True
        b.add_widget(self.save_btn)

    # -- picking / loading
    def _pick(self):
        APP.pick_files(self._picked, multiple=False)

    @guard
    def _picked(self, paths):
        if not paths:
            return
        path = paths[0]
        APP.busy_show(T("cp_computing"))

        def work():
            return load_image_for_edit(path)

        def done(res, err):
            APP.busy_hide()
            if err or res is None:
                APP.feedback("error")
                APP.toast(T("cp_open_fail"), "error")
                return
            self.src, self.base = path, res
            self.orig = os.path.getsize(path)
            ext = os.path.splitext(path)[1].lower()
            want = "PNG" if ext == ".png" else ("WEBP" if ext == ".webp" else "JPEG")
            self.fmt = want                      # same format as the original = no surprise growth
            try:
                self.fmt_group.select(want)
                self.note.opacity = 1 if want == "PNG" else 0
            except Exception:
                pass
            self.pick_t.key = ""
            self.pick_s.key = ""
            self.pick_t.raw = os.path.basename(path)
            self.pick_s.raw = "%dx%d  ·  %s" % (res.width, res.height, human_size(self.orig))
            self.s_before.raw = "%s  ·  %dx%d" % (human_size(self.orig), res.width, res.height)
            self._schedule(0.02)
        run_bg(work, done)

    # -- controls
    def _on_q(self, inst, v):
        self.quality = int(v)
        self.q_val.raw = "%d%%" % self.quality
        self._schedule(0.4)

    def _on_scale(self, v):
        self.scale = float(v)
        self._schedule(0.05)

    def _on_fmt(self, v):
        self.fmt = v
        self.note.opacity = 1 if v == "PNG" else 0
        self._schedule(0.05)

    def _schedule(self, delay):
        if self.base is None:
            return
        if self._ev:
            self._ev.cancel()
        self._ev = Clock.schedule_once(self._compute, delay)

    @guard
    def _compute(self, dt):
        if self._running:                  # one job at a time, the newest settings win
            self._again = True
            return
        self._running = True
        self._again = False
        self._job += 1
        job = self._job
        base, q, sc, fmt = self.base, self.quality, self.scale, self.fmt
        self.s_after.raw = T("cp_computing")

        def work():
            data, dims = compress_image(base, q, sc, fmt)
            th = Image.open(io.BytesIO(data))
            try:
                th.draft("RGB", (1000, 1000))       # fast partial JPEG decode for the preview
            except Exception:
                pass
            th.load()
            th = th.convert("RGBA") if th.mode not in ("RGB", "RGBA") else th
            return data, dims, pil_to_png_bytes(th, 900)

        def done(res, err):
            self._running = False
            if self._again:
                self._schedule(0.02)
                return
            if job != self._job:
                return
            if err or res is None:
                self.s_after.raw = "-"
                return
            data, dims, png = res
            self.result = (data, dims)
            self.s_after.raw = "%s  ·  %dx%d" % (human_size(len(data)), dims[0], dims[1])
            if self.pv_ph.parent:
                self.pv_card.remove_widget(self.pv_ph)
            if not self.pv.parent:
                self.pv_card.add_widget(self.pv)
            self.pv.texture = png_texture(png)
            pct = int(round((1 - len(data) / float(max(1, self.orig))) * 100))
            if pct > 0:
                self.s_saved.color = col("ok")
                self.s_saved.raw = T("cp_saved_pct", pct=pct)
            else:
                self.s_saved.color = col("warn")
                self.s_saved.raw = T("cp_bigger")
            self.save_btn.disabled = False
        run_bg(work, done)

    @guard
    def _save(self):
        if not self.result or not self.src:
            return
        data, dims = self.result
        ext = FORMATS[self.fmt][0]
        stem = os.path.splitext(os.path.basename(self.src))[0]
        name = "%s_idda_q%d%s" % (safe_name(stem, "image"), self.quality, ext)
        tmp = os.path.join(tmp_dir(), name)
        with open(tmp, "wb") as f:
            f.write(data)
        mime = {"JPEG": "image/jpeg", "WEBP": "image/webp", "PNG": "image/png"}.get(self.fmt, "image/jpeg")
        try:
            shown, _uri, _loc = publish_file(tmp, name, mime, "image", APP.user_data_dir)
        except Exception as e:
            APP.save_failed(e)
            return
        APP.feedback("success")
        APP.toast(T("saved_to", path=shown), "ok")
        APP.log_event("compress", "%s → %s" % (human_size(self.orig), human_size(len(data))))


# --------------------------------------------------------------------------
# Tool: images -> PDF
# --------------------------------------------------------------------------
class PDFScreen(ToolScreen):
    bottom_pad = 330
    title_key = "tool_pdf"

    def build_body(self):
        b = self.body
        self.paths = []
        self.thumbs = {}
        self.page = "A4"
        self.orient = "auto"
        self.margin = "none"
        self.last_pdf = None
        b.add_widget(Btn(key="pdf_add", icon="plus", on_tap=self._add))
        self.count = L(raw="", size=14, color="muted", bold=True, h=24)
        b.add_widget(self.count)
        self.list_box = BoxLayout(orientation="vertical", spacing=dp(10), size_hint_y=None)
        self.list_box.bind(minimum_height=self.list_box.setter("height"))
        b.add_widget(self.list_box)
        c = setting_card()
        c.add_widget(L("pdf_size", size=15, bold=True, h=26))
        c.add_widget(ChipGroup([("A4", "A4"), ("LETTER", "Letter"), ("A5", "A5"), ("A3", "A3"),
                                ("FIT", T("pdf_fit"))], "A4", on_change=lambda v: setattr(self, "page", v)))
        c.add_widget(L("pdf_orient", size=15, bold=True, h=26))
        c.add_widget(ChipGroup([("auto", T("pdf_auto")), ("portrait", T("pdf_portrait")),
                                ("landscape", T("pdf_landscape"))], "auto",
                               on_change=lambda v: setattr(self, "orient", v)))
        c.add_widget(L("pdf_margin", size=15, bold=True, h=26))
        c.add_widget(ChipGroup([("none", T("pdf_none")), ("small", T("pdf_small")),
                                ("medium", T("pdf_medium"))], "none",
                               on_change=lambda v: setattr(self, "margin", v)))
        c.add_widget(L("pdf_name", size=15, bold=True, h=26))
        self.name_box = InputBox(hint="PDF", height_dp=50)
        self.name_box.input.text = "3edda"
        c.add_widget(self.name_box)
        b.add_widget(c)
        self.create_btn = Btn(key="pdf_create", icon="doc", on_tap=self._create)
        b.add_widget(self.create_btn)
        self.result_box = BoxLayout(orientation="vertical", spacing=dp(10), size_hint_y=None)
        self.result_box.bind(minimum_height=self.result_box.setter("height"))
        b.add_widget(self.result_box)
        self._render_list()

    @guard
    def _add(self):
        APP.pick_files(self._added, multiple=True)

    @guard
    def _added(self, paths):
        for p in paths:
            if p not in self.paths:
                self.paths.append(p)
        self._render_list()

    def _render_list(self):
        self.list_box.clear_widgets()
        n = len(self.paths)
        self.count.raw = T("pdf_pages", n=n) if n else T("pdf_empty_hint")
        for i, p in enumerate(self.paths):
            self.list_box.add_widget(self._row(i, p))
            if p not in self.thumbs:
                self.thumbs[p] = None
                self._load_thumb(p)

    def _row(self, i, p):
        row = RoundBox(bg=col("card"), radius=dp(18), size_hint_y=None, height=dp(76),
                       padding=[dp(10), dp(8)], spacing=dp(10))
        th = RoundBox(bg=col("card_hi"), radius=dp(12), size_hint=(None, None), size=(dp(58), dp(58)),
                      padding=dp(2))
        img = make_img()
        if self.thumbs.get(p) is not None:
            img.texture = self.thumbs[p]
        th.add_widget(img)
        th._img = img
        row._th = th
        txt = BoxLayout(orientation="vertical", spacing=dp(1))
        txt.add_widget(L(raw="%d.  %s" % (i + 1, os.path.basename(p)), size=14, fill=True))
        try:
            meta = human_size(os.path.getsize(p))
        except Exception:
            meta = ""
        txt.add_widget(L(raw=meta, size=12, color="muted", fill=True))
        up = IconBtn("up", "text", size=36, icon_size=18, bg="card_hi", radius=12,
                     on_tap=lambda i=i: self._move(i, -1))
        down = IconBtn("down", "text", size=36, icon_size=18, bg="card_hi", radius=12,
                       on_tap=lambda i=i: self._move(i, 1))
        rm = IconBtn("trash", "danger", size=36, icon_size=18, bg="danger_bg", radius=12,
                     on_tap=lambda i=i: self._remove(i))
        up.disabled = (i == 0)
        down.disabled = (i == len(self.paths) - 1)
        for w in mirror([th, txt, up, down, rm]):
            row.add_widget(w)
        self._rows = getattr(self, "_rows", {})
        self._rows[p] = row
        return row

    def _load_thumb(self, p):
        def work():
            with Image.open(p) as im0:
                try:
                    im0.draft("RGB", (240, 240))
                except Exception:
                    pass
                im0.load()
                try:
                    im = ImageOps.exif_transpose(im0)
                except Exception:
                    im = im0
            im = im.convert("RGB")
            im.thumbnail((200, 200))
            return pil_to_png_bytes(im)

        def done(res, err):
            if res is None:
                return
            tex = png_texture(res)
            self.thumbs[p] = tex
            row = getattr(self, "_rows", {}).get(p)
            if row is not None:
                row._th._img.texture = tex
        run_bg(work, done)

    @guard
    def _move(self, i, d):
        j = i + d
        if 0 <= j < len(self.paths):
            self.paths[i], self.paths[j] = self.paths[j], self.paths[i]
            self._render_list()

    @guard
    def _remove(self, i):
        if 0 <= i < len(self.paths):
            del self.paths[i]
            self._render_list()

    @guard
    def _create(self):
        if not self.paths:
            APP.feedback("error")
            APP.toast(T("pdf_empty"), "error")
            return
        if not HAS_PIL:
            APP.toast(T("need_pil"), "error")
            return
        name = safe_name(self.name_box.input.text, "3edda") + ".pdf"
        out = unique_path(tmp_dir(), safe_name(self.name_box.input.text, "3edda"), ".pdf")
        paths, page, orient, margin = list(self.paths), self.page, self.orient, self.margin
        APP.busy_show(T("working"))

        def prog(i, n):
            Clock.schedule_once(lambda dt: APP.busy_text(T("pdf_progress", i=i, n=n)), 0)

        def work():
            written_skipped = build_pdf(paths, out, page=page, orient=orient, margin=margin, progress=prog)
            pub = publish_file(out, name, "application/pdf", "pdf", APP.user_data_dir)
            return written_skipped, pub

        def done(res, err):
            APP.busy_hide()
            if err or not res:
                if err is not None:
                    APP.save_failed(err)
                else:
                    APP.feedback("error")
                    APP.toast(T("error"), "error")
                return
            (written, skipped), pub = res
            self.last_pdf = pub[0]
            APP.feedback("success")
            msg = T("pdf_done")
            if skipped:
                msg += " · " + T("pdf_skipped", n=skipped)
            APP.toast(msg, "ok")
            APP.log_event("pdf", "%s · %s" % (name, T("pdf_pages", n=written)))
            self.name_box.input.text = "3edda"
            self._show_result(pub)
        run_bg(work, done)

    def _show_result(self, pub):
        shown, uri, local = pub
        self.result_box.clear_widgets()
        card = setting_card()
        card.add_widget(hrow([Icon("check", "ok", 22), L("pdf_done", size=16, bold=True, fill=True)],
                             height=30, spacing=10))
        card.add_widget(L(raw=short_path(shown, 3), size=12.5, color="muted", wrap=True, halign="left"))
        btns = hrow([Btn(key="share", icon="share", variant="secondary", height_dp=46, font=14,
                         on_tap=lambda: self._share(local, uri, shown)),
                     Btn(key="open", icon="link", variant="secondary", height_dp=46, font=14,
                         on_tap=lambda: self._open(local, uri))], height=46, spacing=10)
        card.add_widget(btns)
        self.result_box.add_widget(card)

    def _share(self, path, uri, shown):
        if not share_file(path, "application/pdf", uri):
            APP.toast(T("share_failed", path=shown))

    def _open(self, path, uri):
        open_pdf_viewer(path, uri)


class _PdfOutMixin:
    """Result card (info lines + share / open) used by the two new PDF tools."""

    def _show_result(self, pub, title_key, rows=(), note=None, note_color="ok"):
        shown, uri, local = pub
        self.result_box.clear_widgets()
        card = setting_card()
        card.add_widget(hrow([Icon("check", "ok", 22), L(title_key, size=16, bold=True, fill=True)],
                             height=30, spacing=10))
        for key, val, color in rows:
            lbl = L(raw=val, size=14.5, bold=True, color=color, fill=True, size_hint_x=None, width=dp(190),
                    halign="left" if APP.rtl else "right")
            card.add_widget(hrow([L(key, size=14.5, color="muted", fill=True), lbl], height=26))
        if note:
            card.add_widget(L(raw=note, size=15.5, bold=True, color=note_color, wrap=True, halign="center"))
        card.add_widget(L(raw=short_path(shown, 3), size=12.5, color="muted", wrap=True, halign="left"))
        card.add_widget(hrow([Btn(key="share", icon="share", variant="secondary", height_dp=46, font=14,
                                  on_tap=lambda: self._share(local, uri, shown)),
                              Btn(key="open", icon="link", variant="secondary", height_dp=46, font=14,
                                  on_tap=lambda: self._open(local, uri))], height=46, spacing=10))
        self.result_box.add_widget(card)

    def _share(self, path, uri, shown):
        if not share_file(path, "application/pdf", uri):
            APP.toast(T("share_failed", path=shown))

    def _open(self, path, uri):
        open_pdf_viewer(path, uri)

    def _pdf_error(self, err):
        msg = str(err)
        if isinstance(err, ValueError) and msg == "encrypted":
            APP.feedback("error")
            APP.toast(T("pdf_enc"), "error")
        elif isinstance(err, ValueError) and msg in ("bad", "nothing to merge"):
            APP.feedback("error")
            APP.toast(T("pdf_bad"), "error")
        else:
            APP.save_failed(err)


class PDFZipScreen(_PdfOutMixin, ToolScreen):
    """Tool 6: make a big PDF smaller."""
    bottom_pad = 40
    title_key = "tool_pdfzip"

    def build_body(self):
        b = self.body
        self.src = None
        self.info = None
        self.level = "medium"
        self._est = {}                  # level -> (before, after, pages, temp_file) | None   (real results)
        self._est_run = set()
        self._est_gen = 0
        self.pick_btn = Btn(raw=T("pdfz_pick"), icon="plus", on_tap=self._pick)
        b.add_widget(self.pick_btn)
        self.file_box = BoxLayout(orientation="vertical", spacing=dp(8), size_hint_y=None)
        self.file_box.bind(minimum_height=self.file_box.setter("height"))
        b.add_widget(self.file_box)
        c = setting_card()
        c.add_widget(L("pdfz_level", size=15, bold=True, h=26))
        c.add_widget(ChipGroup([("low", T("pdfz_low")), ("medium", T("pdfz_med")), ("high", T("pdfz_high"))],
                               "medium", on_change=self._set_level))
        self.level_hint = L("pdfz_med_hint", size=13, color="muted", wrap=True)
        c.add_widget(self.level_hint)
        self.est_box = BoxLayout(orientation="vertical", spacing=dp(6), size_hint_y=None)
        self.est_box.bind(minimum_height=self.est_box.setter("height"))
        c.add_widget(self.est_box)
        c.add_widget(L("pdfz_note", size=12.5, color="muted", wrap=True))
        b.add_widget(c)
        b.add_widget(Btn(key="pdfz_run", icon="compress", on_tap=self._run))
        self.result_box = BoxLayout(orientation="vertical", spacing=dp(10), size_hint_y=None)
        self.result_box.bind(minimum_height=self.result_box.setter("height"))
        b.add_widget(self.result_box)
        self._render_file()
        self._render_est()

    def _set_level(self, v):
        self.level = v
        self.level_hint.key = {"low": "pdfz_low_hint", "medium": "pdfz_med_hint", "high": "pdfz_high_hint"}[v]
        self._estimate()

    # ---- size preview: the file is really compressed in the background, so the number is exact
    def _est_reset(self):
        self._est_gen += 1
        for v in self._est.values():
            try:
                if v:
                    os.remove(v[3])
            except Exception:
                pass
        self._est = {}
        self._est_run = set()

    def _estimate(self):
        if not (self.src and HAS_PYPDF and HAS_PIL):
            self._render_est()
            return
        level, src, gen = self.level, self.src, self._est_gen
        if level in self._est or level in self._est_run:
            self._render_est()
            return
        out = unique_path(tmp_dir(), "est_" + level, ".pdf")
        self._est_run.add(level)

        def work():
            before, after, pages = pdf_compress(src, out, level, None)
            return (before, after, pages, out)

        def done(res, err):
            if gen != self._est_gen:                        # another file was chosen meanwhile
                try:
                    os.remove(out)
                except Exception:
                    pass
                return
            self._est_run.discard(level)
            self._est[level] = res if (res and err is None) else None
            if self._est[level] is None:
                try:
                    os.remove(out)
                except Exception:
                    pass
            self._render_est()
        run_bg(work, done)
        self._render_est()

    def _est_row(self, key, val, color="text"):
        lbl = L(raw=val, size=14.5, bold=True, color=color, fill=True, size_hint_x=None, width=dp(190),
                halign="left" if APP.rtl else "right")
        return hrow([L(key, size=14.5, color="muted", fill=True), lbl], height=26)

    def _render_est(self):
        self.est_box.clear_widgets()
        if not self.src:
            return
        try:
            now = os.path.getsize(self.src)
        except Exception:
            return
        self.est_box.add_widget(self._est_row("pdfz_est_now", human_size(now)))
        if not (HAS_PYPDF and HAS_PIL):                     # the library is missing: say so instead of waiting forever
            self.est_box.add_widget(L("need_pypdf", size=12.5, color="warn", wrap=True))
            return
        if self.level in self._est and self._est[self.level] is None:
            return                                          # encrypted / damaged: the file card already says so
        res = self._est.get(self.level)
        if not res:
            if self.level in self._est_run:
                self.est_box.add_widget(self._est_row("pdfz_est_after", T("pdfz_est_calc"), "muted"))
            return
        before, after = res[0], res[1]
        if after >= before * 0.98:
            self.est_box.add_widget(self._est_row("pdfz_est_after", human_size(before), "warn"))
            self.est_box.add_widget(L("pdfz_no_gain", size=12.5, color="warn", wrap=True))
            return
        pct = max(1, int(round((1 - after / float(max(1, before))) * 100)))
        self.est_box.add_widget(self._est_row("pdfz_est_after", human_size(after), "accent"))
        self.est_box.add_widget(L(raw=T("cp_saved_pct", pct=pct), size=12.5, color="ok", wrap=True))

    @guard
    def _pick(self):
        APP.pick_pdfs(self._picked, multiple=False)

    @guard
    def _picked(self, paths):
        if not paths:
            return
        self.src = paths[0]
        self.info = None
        self._est_reset()
        self.result_box.clear_widgets()
        self.pick_btn.set_text(T("pdfz_change"))
        self._render_file()
        self._estimate()
        p = self.src

        def done(res, err):
            if p != self.src:
                return
            self.info = res or (0, "bad")
            self._render_file()
        if HAS_PYPDF:
            run_bg(lambda: pdf_info(p), done)

    def _render_file(self):
        self.file_box.clear_widgets()
        if not self.src:
            self.file_box.add_widget(L("pdfz_none", size=14, color="muted", wrap=True))
            return
        row = RoundBox(bg=col("card"), radius=dp(18), size_hint_y=None, height=dp(76),
                       padding=[dp(12), dp(8)], spacing=dp(12))
        ic = RoundBox(bg=col("card_hi"), radius=dp(12), size_hint=(None, None), size=(dp(52), dp(52)),
                      padding=dp(13))
        ic.add_widget(Icon("doc", "accent", 26))
        txt = BoxLayout(orientation="vertical", spacing=dp(1))
        txt.add_widget(L(raw=os.path.basename(self.src), size=14.5, bold=True, fill=True))
        try:
            meta = human_size(os.path.getsize(self.src))
        except Exception:
            meta = ""
        color = "muted"
        if self.info:
            pages, state = self.info
            if state == "ok":
                meta += "  ·  " + T("pdf_pages", n=pages)
            elif state == "encrypted":
                meta += "  ·  " + T("pdf_enc_s")
                color = "warn"
            else:
                meta += "  ·  " + T("pdf_bad_s")
                color = "warn"
        txt.add_widget(L(raw=meta, size=12, color=color, fill=True))
        for w in mirror([ic, txt]):
            row.add_widget(w)
        self.file_box.add_widget(row)

    @guard
    def _run(self):
        if not self.src:
            APP.feedback("error")
            APP.toast(T("pdfz_none"), "error")
            return
        if not (HAS_PYPDF and HAS_PIL):
            APP.toast(T("need_pypdf"), "error", 4)
            return
        src, level = self.src, self.level
        base = safe_name(os.path.splitext(os.path.basename(src))[0], "3edda") + "_compressed"
        name = base + ".pdf"
        out = unique_path(tmp_dir(), base, ".pdf")
        APP.busy_show(T("working"))

        def prog(i, n):
            Clock.schedule_once(lambda dt: APP.busy_text(T("pdf_progress", i=i, n=n)), 0)

        est = self._est.get(level)

        def work():
            if est and os.path.isfile(est[3]):               # already compressed for the preview: reuse it
                import shutil
                shutil.copyfile(est[3], out)
                before, after, pages = est[0], est[1], est[2]
            else:
                before, after, pages = pdf_compress(src, out, level, prog)
            if after >= before * 0.98:                       # nothing worth keeping
                try:
                    os.remove(out)
                except Exception:
                    pass
                return ("nogain", before, after, pages, None)
            pub = publish_file(out, name, "application/pdf", "pdf", APP.user_data_dir)
            return ("ok", before, after, pages, pub)

        def done(res, err):
            APP.busy_hide()
            if err is not None or not res:
                if err is not None:
                    self._pdf_error(err)
                else:
                    APP.feedback("error")
                    APP.toast(T("error"), "error")
                return
            kind, before, after, pages, pub = res
            if kind == "nogain":
                self.result_box.clear_widgets()
                card = setting_card()
                card.add_widget(hrow([Icon("warn", "warn", 22), L("pdfz_no_gain", size=14.5, wrap=True, fill=True)],
                                     height=60, spacing=10))
                self.result_box.add_widget(card)
                APP.toast(T("pdfz_no_gain"), "info", 3.5)
                return
            pct = max(1, int(round((1 - after / float(max(1, before))) * 100)))
            APP.feedback("success")
            APP.toast(T("pdfz_done"), "ok")
            APP.log_event("pdfzip", "%s · %s → %s" % (name, human_size(before), human_size(after)))
            self._show_result(pub, "pdfz_done",
                              rows=[("cp_before", human_size(before), "text"),
                                    ("cp_after", human_size(after), "accent")],
                              note=T("cp_saved_pct", pct=pct))
        run_bg(work, done)


class PDFMergeScreen(_PdfOutMixin, ToolScreen):
    """Tool 7: join two or more PDF files, in the order the user chooses, into one PDF."""
    bottom_pad = 330
    title_key = "tool_pdfmerge"

    def build_body(self):
        b = self.body
        self.paths = []
        self.pinfo = {}
        self._rows = {}
        b.add_widget(Btn(key="pdfm_add", icon="plus", on_tap=self._add))
        self.count = L(raw="", size=14, color="muted", bold=True, h=24)
        b.add_widget(self.count)
        self.list_box = BoxLayout(orientation="vertical", spacing=dp(10), size_hint_y=None)
        self.list_box.bind(minimum_height=self.list_box.setter("height"))
        b.add_widget(self.list_box)
        c = setting_card()
        c.add_widget(L("pdf_name", size=15, bold=True, h=26))
        self.name_box = InputBox(hint="PDF", height_dp=50)
        self.name_box.input.text = "3edda_merged"
        c.add_widget(self.name_box)
        b.add_widget(c)
        b.add_widget(Btn(key="pdfm_run", icon="merge", on_tap=self._create))
        self.result_box = BoxLayout(orientation="vertical", spacing=dp(10), size_hint_y=None)
        self.result_box.bind(minimum_height=self.result_box.setter("height"))
        b.add_widget(self.result_box)
        self._render_list()

    @guard
    def _add(self):
        APP.pick_pdfs(self._added, multiple=True)

    @guard
    def _added(self, paths):
        new = []
        for p in paths:
            if p not in self.paths:
                self.paths.append(p)
                new.append(p)
        self._render_list()
        if HAS_PYPDF:
            for p in new:
                self._load_info(p)

    def _load_info(self, p):
        def done(res, err):
            self.pinfo[p] = res or (0, "bad")
            row = self._rows.get(p)
            if row is not None:
                self._fill_meta(row, p)
            self._update_count()
        run_bg(lambda: pdf_info(p), done)

    def _meta(self, p):
        try:
            sz = human_size(os.path.getsize(p))
        except Exception:
            sz = ""
        pages, state = self.pinfo.get(p, (0, None))
        if state == "ok":
            return sz + "  ·  " + T("pdf_pages", n=pages), "muted"
        if state == "encrypted":
            return sz + "  ·  " + T("pdf_enc_s"), "warn"
        if state == "bad":
            return sz + "  ·  " + T("pdf_bad_s"), "warn"
        return sz, "muted"

    def _fill_meta(self, row, p):
        text, color = self._meta(p)
        row._meta.raw = text
        row._meta.color = col(color)

    def _update_count(self):
        n = len(self.paths)
        if not n:
            self.count.raw = T("pdfm_hint")
        elif all(self.pinfo.get(p, (0, None))[1] for p in self.paths):
            total = sum(self.pinfo[p][0] for p in self.paths)
            self.count.raw = T("pdfm_count", n=n, p=total)
        else:
            self.count.raw = T("pdfm_count_n", n=n)

    def _render_list(self):
        self.list_box.clear_widgets()
        self._rows = {}
        self._update_count()
        if len(self.paths) >= 2:
            self.list_box.add_widget(L("pdfm_order", size=12.5, color="muted", wrap=True))
        for i, p in enumerate(self.paths):
            self.list_box.add_widget(self._row(i, p))

    def _row(self, i, p):
        row = RoundBox(bg=col("card"), radius=dp(18), size_hint_y=None, height=dp(76),
                       padding=[dp(10), dp(8)], spacing=dp(10))
        badge = RoundBox(bg=col("card_hi"), radius=dp(12), size_hint=(None, None), size=(dp(52), dp(52)),
                         padding=dp(13))
        badge.add_widget(Icon("doc", "accent", 26))
        txt = BoxLayout(orientation="vertical", spacing=dp(1))
        txt.add_widget(L(raw="%d.  %s" % (i + 1, os.path.basename(p)), size=14, fill=True))
        row._meta = L(raw="", size=12, color="muted", fill=True)
        self._fill_meta(row, p)
        txt.add_widget(row._meta)
        up = IconBtn("up", "text", size=36, icon_size=18, bg="card_hi", radius=12,
                     on_tap=lambda i=i: self._move(i, -1))
        down = IconBtn("down", "text", size=36, icon_size=18, bg="card_hi", radius=12,
                       on_tap=lambda i=i: self._move(i, 1))
        rm = IconBtn("trash", "danger", size=36, icon_size=18, bg="danger_bg", radius=12,
                     on_tap=lambda i=i: self._remove(i))
        up.disabled = (i == 0)
        down.disabled = (i == len(self.paths) - 1)
        for w in mirror([badge, txt, up, down, rm]):
            row.add_widget(w)
        self._rows[p] = row
        return row

    @guard
    def _move(self, i, d):
        j = i + d
        if 0 <= j < len(self.paths):
            self.paths[i], self.paths[j] = self.paths[j], self.paths[i]
            self._render_list()

    @guard
    def _remove(self, i):
        if 0 <= i < len(self.paths):
            del self.paths[i]
            self._render_list()

    @guard
    def _create(self):
        if len(self.paths) < 2:
            APP.feedback("error")
            APP.toast(T("pdfm_need2"), "error")
            return
        if not HAS_PYPDF:
            APP.toast(T("need_pypdf"), "error", 4)
            return
        base = safe_name(self.name_box.input.text, "3edda_merged")
        name = base + ".pdf"
        out = unique_path(tmp_dir(), base, ".pdf")
        paths = list(self.paths)
        APP.busy_show(T("working"))

        def prog(i, n):
            Clock.schedule_once(lambda dt: APP.busy_text(T("pdfm_progress", i=i, n=n)), 0)

        def work():
            pages, skipped = pdf_merge(paths, out, prog)
            pub = publish_file(out, name, "application/pdf", "pdf", APP.user_data_dir)
            return (pages, skipped), pub

        def done(res, err):
            APP.busy_hide()
            if err is not None or not res:
                if err is not None:
                    self._pdf_error(err)
                else:
                    APP.feedback("error")
                    APP.toast(T("error"), "error")
                return
            (pages, skipped), pub = res
            APP.feedback("success")
            msg = T("pdfm_done")
            if skipped:
                msg += " · " + T("pdfm_skipped", n=skipped)
            APP.toast(msg, "ok", 3.2)
            APP.log_event("pdfmerge", "%s · %s" % (name, T("pdf_pages", n=pages)))
            self.name_box.input.text = "3edda_merged"
            self._show_result(pub, "pdfm_done",
                              rows=[("pdfm_files_lbl", str(len(paths) - skipped), "text"),
                                    ("pdfm_pages_lbl", str(pages), "accent")])
        run_bg(work, done)


# --------------------------------------------------------------------------
# PDF tools 8 + 9 -- split (remove pages) and edit.  Pure helpers first (no UI).
# --------------------------------------------------------------------------
PDFE_W0 = 1000.0                                  # every page is this many "units" wide inside the editor
PDFE_SC = 1.6                                     # units -> pixels of the pictures shown on screen
PDFE_PENS = {"pen": (1.0, 1.0), "ball": (0.6, 1.0), "pencil": (0.85, 0.7), "marker": (3.0, 0.35)}   # width x, opacity
PDFE_COLORS = ["#000000", "#FFFFFF", "#E53935", "#FB8C00", "#FDD835", "#43A047", "#00897B",
               "#1E88E5", "#3949AB", "#8E24AA", "#EC407A", "#795548", "#757575"]
_PDFE_FONTS = {}


def pdfe_rgb(hexc):
    h = (hexc or "#000000").lstrip("#")
    try:
        return (int(h[0:2], 16), int(h[2:4], 16), int(h[4:6], 16))
    except Exception:
        return (0, 0, 0)


def pdfe_hex(rgb):
    return "#%02X%02X%02X" % tuple(int(max(0, min(255, round(v)))) for v in rgb[:3])


def pdfe_font(px):
    """The app font (the same one the UI uses) at `px` pixels, for drawing text onto a page picture."""
    path = TextEngine.reg or TextEngine.lat_reg
    px = max(6, int(px))
    key = (path, px)
    f = _PDFE_FONTS.get(key)
    if f is None:
        try:
            f = ImageFont.truetype(path, px, layout_engine=ImageFont.Layout.BASIC)   # text is shaped by shape_line already
        except Exception:
            try:
                f = ImageFont.truetype(path, px)
            except Exception:
                f = ImageFont.load_default()
        if len(_PDFE_FONTS) > 60:
            _PDFE_FONTS.clear()
        _PDFE_FONTS[key] = f
    return f


def _pdfe_tw(font, s):
    try:
        return float(font.getlength(s))
    except Exception:
        try:
            return float(font.getsize(s)[0])
        except Exception:
            return len(s) * 8.0


def _pdfe_shape(s):
    if TextEngine.can_shape():
        return TextEngine.fix_missing(shape_line(s))
    return s


def pdfe_wrap(text, font, max_w):
    lines = []
    for para in (text or "").split("\n"):
        cur = ""
        for w in para.split(" "):
            test = (cur + " " + w) if cur else w
            if cur and _pdfe_tw(font, _pdfe_shape(test)) > max_w:
                lines.append(cur)
                cur = w
            else:
                cur = test
        lines.append(cur)
    return lines


def pdfe_text_width(text, size_px):
    """Width of the longest line when nothing is wrapped (pixels)."""
    font = pdfe_font(int(round(size_px)))        # the same size the picture of the text will really use
    # + 3 %: the page is saved at another resolution than the screen, so the letters never measure exactly the same
    return 1.03 * max([_pdfe_tw(font, _pdfe_shape(x)) for x in (text or " ").split("\n")] or [0.0])


def pdfe_text_pil(text, hexc, size_px, box_px, thin=0.0):
    """Transparent RGBA picture of a (wrapped) text. Used for the screen AND for the saved PDF.
    `thin` = how many pixels thinner the strokes should be (the app font is heavier than most documents)."""
    px = max(6, int(round(size_px)))
    font = pdfe_font(px)
    pad = max(2, int(px * 0.12))
    width = max(8, int(box_px))
    lines = pdfe_wrap(text, font, max(px, width - 2 * pad))
    lh = int(px * 1.32)
    img = Image.new("RGBA", (width, lh * len(lines) + 2 * pad), (0, 0, 0, 0))
    d = ImageDraw.Draw(img)
    fill = pdfe_rgb(hexc) + (255,)
    for i, line in enumerate(lines):
        sh = _pdfe_shape(line)
        x = (width - pad - _pdfe_tw(font, sh)) if has_arabic(line) else pad
        d.text((x, pad + i * lh), sh, font=font, fill=fill)
    steps = int(round(thin / 0.5)) if thin and thin >= 0.25 else 0
    if steps > 0:
        try:
            S = 4                                            # work on a 4x picture: one step = half a pixel off the strokes
            a = img.getchannel("A")
            a = a.resize((img.width * S, img.height * S), Image.BICUBIC)
            for _i in range(min(steps, 4)):
                a = a.filter(ImageFilter.MinFilter(3))
            a = a.resize(img.size, Image.BOX)
            a = a.point(lambda v: min(255, int(v * 1.7)))    # thin strokes come out pale: make them as dark as the page's
            img.putalpha(a)
        except Exception:
            traceback.print_exc()
    return img


def pdfe_sample(pil, box):
    """(background colour, text colour) inside a box (pixels) of a page picture."""
    try:
        x0, y0, x1, y1 = [int(v) for v in box]
        x0, y0 = max(0, x0), max(0, y0)
        x1, y1 = min(pil.width, x1), min(pil.height, y1)
        if x1 - x0 < 2 or y1 - y0 < 2:
            return (255, 255, 255), (0, 0, 0)
        reg = pil.crop((x0, y0, x1, y1)).convert("RGB")
        small = reg.resize((max(1, min(48, reg.width)), max(1, min(48, reg.height))), NEAREST)
        cols = small.getcolors(maxcolors=48 * 48) or [(1, (255, 255, 255))]
        bg = max(cols, key=lambda c: c[0])[1]
        far = max(cols, key=lambda c: sum(abs(c[1][i] - bg[i]) for i in range(3)))[1]
        if sum(abs(far[i] - bg[i]) for i in range(3)) < 90:
            lum = 0.3 * bg[0] + 0.59 * bg[1] + 0.11 * bg[2]
            far = (0, 0, 0) if lum > 140 else (255, 255, 255)
        return tuple(bg), tuple(far)
    except Exception:
        return (255, 255, 255), (0, 0, 0)


def pdfe_gap_thr(gaps, h, default):
    """How many empty columns separate two WORDS (not two letters) on this line.  The gaps of a line are of two
    kinds - small ones between letters, bigger ones between words - and the line itself tells where the border is."""
    g = sorted(x for x in gaps if x <= 1.0 * h)          # bigger gaps are cell edges / columns, not spaces
    if len(g) < 4:
        return default
    best = None
    for s in range(1, len(g)):
        a, b = g[:s], g[s:]
        ma, mb = sum(a) / len(a), sum(b) / len(b)
        sse = sum((x - ma) ** 2 for x in a) + sum((x - mb) ** 2 for x in b)
        if best is None or sse < best[0]:
            best = (sse, s, ma, mb)
    _sse, s, ma, mb = best
    if mb >= 1.8 * max(ma, 1.0) and mb - ma >= 0.12 * h:
        return max(0.18 * h, min(0.8 * h, (g[s - 1] + g[s]) / 2.0))
    return default


def pdfe_words(cols, h, skip=None):
    """Words of a line from its ink columns: [(first_col, last_col)], letters of one word joined by the line's own spacing.
    Columns in `skip` (table borders) are never part of a word and always separate the words on their two sides."""
    runs, start, last, cut = [], None, 0, False
    for i, c in enumerate(cols):
        if skip is not None and skip[i]:
            if start is not None:
                runs.append((start, last, cut))
                start = None
            cut = True
        elif c:
            if start is None:
                start = i
                cut_here = cut
                cut = False
            last = i
        elif start is not None:
            runs.append((start, last, cut_here))
            start = None
    if start is not None:
        runs.append((start, last, cut_here))
    if not runs:
        return []
    gaps = [runs[i + 1][0] - runs[i][1] - 1 for i in range(len(runs) - 1) if not runs[i + 1][2]]
    thr = pdfe_gap_thr(gaps, h, max(3, int(0.32 * h)))
    words = [(runs[0][0], runs[0][1])]
    for r in runs[1:]:
        if not r[2] and r[0] - words[-1][1] - 1 < thr:
            words[-1] = (words[-1][0], r[1])
        else:
            words.append((r[0], r[1]))
    return words


def _pdfe_core(binimg):
    """(first_row, last_row + 1) of the real height of a line of text: the rows that carry a proper amount of ink
    (a stray dot or one long tail does not count).  `binimg` = 0 / 255 picture."""
    bb = binimg.getbbox()
    if not bb:
        return None
    img = binimg.crop((bb[0], 0, bb[2], binimg.size[1]))      # only the part that holds text, so the counts are exact
    h = img.size[1]
    cnt = list(img.resize((1, h), _PDFE_BOX).tobytes())
    mx = max(cnt)
    if mx <= 0:
        return None
    rows = [i for i, v in enumerate(cnt) if v >= 0.05 * mx]
    return rows[0], rows[-1] + 1


def _pdfe_vrun(binimg):
    """The longest vertical run of ink in a picture of text (pixels): the height of the tallest upright letters (alef, lam)."""
    w, h = binimg.size
    if w < 1 or h < 1:
        return 0
    data = binimg.tobytes()
    best = 0
    for x in range(w):
        col = data[x::w]
        if not any(col):
            continue
        m = max(len(s) for s in col.split(b"\x00"))
        if m > best:
            best = m
    return best


def _pdfe_stroke(binimg):
    """Typical thickness of the strokes (pixels): the average length of the horizontal runs of ink, without the
    long ones (the base line of a word is not a stroke)."""
    w, h = binimg.size
    if w < 2 or h < 2:
        return 0.0
    data = binimg.tobytes()
    runs = []
    for y in range(h):
        row = data[y * w:(y + 1) * w]
        if any(row):
            runs.extend(len(s) for s in row.split(b"\x00") if s)
    if not runs:
        return 0.0
    runs.sort()
    med = runs[len(runs) // 2]
    keep = [r for r in runs if r <= 2.2 * med] or runs
    return sum(keep) / float(len(keep))


_PDFE_REF = {}
_PDFE_REF2 = {}
_PDFE_REF3 = {}


def pdfe_stroke_ratio():
    """Thickness of the strokes divided by the font size, for the font the editor writes with."""
    key = (TextEngine.reg, TextEngine.lat_reg)
    r = _PDFE_REF3.get(key)
    if r is None:
        r = 0.09
        try:
            pic = pdfe_text_pil("احمد رشاد عبدالحميد حسين", "#000000", 100.0, 4000)
            s = _pdfe_stroke(pic.getchannel("A").point(lambda v: 255 if v > 128 else 0))
            if s >= 1:
                r = s / 100.0
        except Exception:
            traceback.print_exc()
        _PDFE_REF3[key] = r
    return r




def pdfe_alef_ratio():
    """Height of the tallest upright letters divided by the font size, for the font the editor writes with."""
    key = (TextEngine.reg, TextEngine.lat_reg)
    r = _PDFE_REF2.get(key)
    if r is None:
        r = 0.75
        try:
            pic = pdfe_text_pil("الطالب الكبير", "#000000", 100.0, 1500)
            m = _pdfe_vrun(pic.getchannel("A").point(lambda v: 255 if v > 128 else 0))
            if m > 10:
                r = m / 100.0
        except Exception:
            traceback.print_exc()
        _PDFE_REF2[key] = r
    return r




def pdfe_ink_ratio():
    """Height of the body of a typical Arabic line of text divided by its font size, for the font the editor writes with."""
    key = (TextEngine.reg, TextEngine.lat_reg)
    r = _PDFE_REF.get(key)
    if r is None:
        r = 0.7
        try:
            pic = pdfe_text_pil("احمد رشاد عبدالحميد حسين", "#000000", 100.0, 4000)
            c = _pdfe_core(pic.getchannel("A").point(lambda v: 255 if v > 128 else 0))
            if c:
                r = (c[1] - c[0]) / 100.0
        except Exception:
            traceback.print_exc()
        _PDFE_REF[key] = r
    return r


def pdfe_match_style(text, tall_u, stroke_u, z0):
    """Size and weight of a typed line so that it looks like the text around it: the text is drawn, measured the same
    way the page was measured, and corrected until the tall letters and the strokes agree.  -> (size, thinning)."""
    k = PDFE_SC
    line = (text or "").split("\n")[0]
    if not line.strip():
        return z0, 0.0

    def render(z, thin_px):
        w = pdfe_text_width(line, z * k) + z * k * 0.6 + 8
        return pdfe_text_pil(line, "#000000", z * k, w, thin_px).getchannel("A").point(lambda v: 255 if v > 128 else 0)
    z, thin = z0, 0.0
    try:
        for rnd in range(2):
            if tall_u:
                m = _pdfe_vrun(render(z, thin))
                ref = pdfe_alef_ratio() * z * k
                if m < 0.7 * ref:                            # no tall letter in this text: assume the usual ones
                    m = ref
                if m > 3:
                    z = max(0.6 * z0, min(1.6 * z0, z * tall_u * k / m))
                    z = max(8.0, min(140.0, z))
            if stroke_u:
                best = None
                for t in (0.0, 0.5, 1.0, 1.5):
                    err = abs(_pdfe_stroke(render(z, t)) - stroke_u * k)
                    if best is None or err < best[0] - 0.04:
                        best = (err, t)
                thin = best[1]
    except Exception:
        traceback.print_exc()
    return z, thin / k


def pdfe_ink_masks(pil, box, bg, grow="auto"):
    """The letters inside `box` (units) of a page picture, as pictures made only of ink.
    -> (erase_mask, ink_alpha, left, top) in pixels, or None.
      erase_mask : where to paint the paper colour to take the letters away (slightly fatter than the letters)
      ink_alpha  : the letters themselves (soft edges), to copy them somewhere else
    Table lines are never touched.  A line is recognised because it CONTINUES outside the box (a ruled line
    goes on to the left and right / above and below); the base stroke of an Arabic word stops where the word
    stops, so it is taken away together with the word."""
    from PIL import ImageChops
    k = pil.width / PDFE_W0
    if grow == "auto":      # take a little more than the box, as far as the neighbouring words leave room
        try:
            cx = pdfe_line_ctx(pil, box)
        except Exception:
            cx = None
        gl = max(0.8, min(4.0, 0.45 * (cx["near_l"] if cx else 99.0)))
        gr = max(0.8, min(4.0, 0.45 * (cx["near_r"] if cx else 99.0)))
        gv = 3.0
    else:
        gl = gr = gv = float(grow)
    x0, y0, x1, y1 = [int(round(v * k)) for v in box]
    x0, y0 = max(0, x0 - int(round(gl * k))), max(0, y0 - int(round(gv * k)))
    x1, y1 = min(pil.width, x1 + int(round(gr * k))), min(pil.height, y1 + int(round(gv * k)))
    if x1 - x0 < 2 or y1 - y0 < 2:
        return None
    reach = max(3, int(round(3 * k)))
    cx0, cy0 = max(0, x0 - reach), max(0, y0 - reach)
    cx1, cy1 = min(pil.width, x1 + reach), min(pil.height, y1 + reach)
    ctx = pil.crop((cx0, cy0, cx1, cy1)).convert("L")
    bgl = int(round(0.3 * bg[0] + 0.59 * bg[1] + 0.11 * bg[2]))
    ink = ctx.point(lambda v, b=bgl: 255 if abs(v - b) > 32 else 0)
    ox, oy = x0 - cx0, y0 - cy0
    w, h = x1 - x0, y1 - y0
    cw, ch = ctx.size
    inner = ink.crop((ox, oy, ox + w, oy + h))

    def _frac(img, n, horizontal):
        data = img.resize((1, n) if horizontal else (n, 1), _PDFE_BOX).tobytes()
        return [v / 255.0 for v in data]
    row_in = _frac(inner, h, True)
    col_in = _frac(inner, w, False)
    side_l = _frac(ink.crop((0, oy, ox, oy + h)), h, True) if ox >= 2 else None
    side_r = _frac(ink.crop((ox + w, oy, cw, oy + h)), h, True) if cw - (ox + w) >= 2 else None
    side_u = _frac(ink.crop((ox, 0, ox + w, oy)), w, False) if oy >= 2 else None
    side_d = _frac(ink.crop((ox, oy + h, ox + w, ch)), w, False) if ch - (oy + h) >= 2 else None

    def _lines(own, sides, whole):
        flags = []
        sides = [s for s in sides if s is not None]
        for i, f in enumerate(own):
            if f < 0.6:
                flags.append(False)
            elif sides:
                flags.append(any(s[i] > 0.75 for s in sides))       # a table line goes on at least on one side
            else:
                flags.append(whole and f > 0.9)
        return flags
    rows = _lines(row_in, (side_l, side_r), True)         # horizontal ruled lines
    cols = _lines(col_in, (side_u, side_d), False)        # vertical ruled lines
    pad = max(1, int(round(0.8 * k)))
    protect = Image.new("L", (w, h), 0)
    pd = ImageDraw.Draw(protect)
    for i, f in enumerate(rows):
        if f:
            pd.rectangle([0, max(0, i - pad), w, min(h, i + pad)], fill=255)
    for i, f in enumerate(cols):
        if f:
            pd.rectangle([max(0, i - pad), 0, min(w, i + pad), h], fill=255)
    erase = inner.filter(ImageFilter.MaxFilter(max(3, int(round(4 * k)) | 1)))     # soft edges of the letters too
    erase = ImageChops.subtract(erase, protect)
    gray = ctx.crop((ox, oy, ox + w, oy + h))
    alpha = gray.point(lambda v, b=bgl: max(0, min(255, (abs(v - b) - 12) * 5)))
    alpha = ImageChops.subtract(alpha, protect)
    return erase, alpha, x0, y0


def pdfe_ink_patch(pil, box, bg):
    """Take the old text away WITHOUT leaving a box: only the letters inside `box` (units) are painted over
    with the paper colour `bg`; whatever is behind (cell colours, lines, watermark) stays.
    -> (RGBA picture, left, top) in pixels of `pil`, or None."""
    res = pdfe_ink_masks(pil, box, bg)
    if not res:
        return None
    erase, _alpha, x0, y0 = res
    patch = Image.new("RGBA", erase.size, tuple(bg) + (0,))
    patch.putalpha(erase)
    return patch, x0, y0


def pdfe_move_pics(pil, box, dx, bg):
    """The letters inside `box` (units) moved sideways by `dx` units.
    -> (erase_patch RGBA, ghost RGBA, left, top, new_left) in pixels of `pil`, or None."""
    res = pdfe_ink_masks(pil, box, bg, grow=1.0)
    if not res:
        return None
    erase, alpha, x0, y0 = res
    w, h = erase.size
    ghost = pil.crop((x0, y0, x0 + w, y0 + h)).convert("RGBA")
    ghost.putalpha(alpha)
    patch = Image.new("RGBA", erase.size, tuple(bg) + (0,))
    patch.putalpha(erase)
    k = pil.width / PDFE_W0
    return patch, ghost, x0, y0, x0 + int(round(dx * k))


def pdfe_apply_raster(im, objs):
    """Apply the objects that change the page picture itself (taken-away text, moved text) to `im` (RGBA, in place)."""
    k = im.width / PDFE_W0
    for o in objs:
        t = o.get("t")
        try:
            if t == "e":
                res = pdfe_ink_patch(im, (o["x"], o["y"], o["x"] + o["w"], o["y"] + o["h"]), pdfe_rgb(o["c"]))
                if res:
                    im.paste(res[0], (res[1], res[2]), res[0])
            elif t == "g":
                res = pdfe_move_pics(im, (o["x"], o["y"], o["x"] + o["w"], o["y"] + o["h"]), o["dx"], pdfe_rgb(o["c"]))
                if res:
                    patch, ghost, x0, y0, nx = res
                    im.paste(patch, (x0, y0), patch)
                    im.paste(ghost, (nx, y0), ghost)
        except Exception:
            traceback.print_exc()
    return im


def pdfe_raster(base, objs):
    """The page picture as it looks after the objects that change it (RGB). `base` itself stays untouched."""
    ras = [o for o in objs if o.get("t") in ("e", "g")]
    if not ras:
        return base
    return pdfe_apply_raster(base.convert("RGBA"), ras).convert("RGB")


def pdfe_line_ctx(pil, box, extra=()):
    """Look along the line of text that holds `box` (units). -> dict:
      lim_l / lim_r   : how far text may reach on each side: the next table border or the page edge
      left / right    : (from, to) span of the words standing on that side of the box inside the same cell, or None
      near_l / near_r : distance from the box to the nearest ink on that side (99 = nothing near)
      core            : (top, bottom) of the body of the line in this cell (its real letter height), or None
    `extra` = more things standing on the line (spans (from, to) in units)."""
    k = pil.width / PDFE_W0
    W = pil.width
    bx0, by0, bx1, by1 = box
    ya, yb = max(0, int(round(by0 * k))), min(pil.height, int(round(by1 * k)))
    res = {"lim_l": 6.0, "lim_r": PDFE_W0 - 6.0, "left": None, "right": None, "near_l": 99.0, "near_r": 99.0, "core": None,
           "tall": None, "stroke": None}
    if yb - ya < 3:
        return res
    try:
        strip = pil.crop((0, ya, W, yb)).convert("L")
        hist = strip.histogram()
        bg = max(range(256), key=lambda i: hist[i])
        ink = strip.point(lambda v, b=bg: 255 if abs(v - b) > 48 else 0)
        h = yb - ya

        def _cols(img):
            return [v / 255.0 for v in img.resize((W, 1), _PDFE_BOX).tobytes()]
        own = _cols(ink)
        gap = max(2, int(round(3.5 * k)))
        up = _cols(pil.crop((0, max(0, ya - gap - 2), W, max(0, ya - 2))).convert("L").point(
            lambda v, b=bg: 255 if abs(v - b) > 48 else 0)) if ya - 2 > 1 else None
        dn = _cols(pil.crop((0, min(pil.height, yb + 2), W, min(pil.height, yb + 2 + gap))).convert("L").point(
            lambda v, b=bg: 255 if abs(v - b) > 48 else 0)) if pil.height - (yb + 2) > 1 else None
        border = []
        for i in range(W):
            b = own[i] > 0.85 and (up is not None or dn is not None)
            if b and up is not None and up[i] <= 0:
                b = False
            if b and dn is not None and dn[i] <= 0:
                b = False
            border.append(b)
        bl, br = None, None
        lo_px, hi_px = bx0 * k, bx1 * k
        for i in range(W):
            if border[i]:
                if i < lo_px and (bl is None or i > bl):
                    bl = i
                if i > hi_px and (br is None or i < br):
                    br = i
        marg = 3.0
        res["lim_l"] = (bl + 1) / k + marg if bl is not None else 6.0
        res["lim_r"] = br / k - marg if br is not None else PDFE_W0 - 6.0
        for i in range(min(W - 1, int(lo_px) - 1), -1, -1):          # nearest ink on the left
            if border[i] or own[i] > 0:
                res["near_l"] = (lo_px - i) / k
                break
        for i in range(max(0, int(hi_px) + 1), W):                   # ... and on the right
            if border[i] or own[i] > 0:
                res["near_r"] = (i - hi_px) / k
                break
        words = [(s / k, (e + 1) / k) for s, e in pdfe_words([v > 0 for v in own], h, border)]
        words += [tuple(e) for e in extra]
        left = [wd for wd in words if wd[1] <= bx0 + 0.5 and wd[0] >= res["lim_l"] - 2.0]
        right = [wd for wd in words if wd[0] >= bx1 - 0.5 and wd[1] <= res["lim_r"] + 2.0]
        if left:
            res["left"] = (min(a for a, _ in left), max(b for _, b in left))
        if right:
            res["right"] = (min(a for a, _ in right), max(b for _, b in right))
        # the body of the line inside this cell
        cl = max(0, int(res["lim_l"] * k) - int(2 * k))
        cr = min(W, int(res["lim_r"] * k) + int(2 * k))
        wy0, wy1 = max(0, ya - h), min(pil.height, yb + h)
        if cr - cl > 8 and wy1 - wy0 > 4:
            win = pil.crop((cl, wy0, cr, wy1)).convert("L").point(lambda v, b=bg: 255 if abs(v - b) > 48 else 0)
            ww_, wh_ = win.size
            fr = [v / 255.0 for v in win.resize((1, wh_), _PDFE_BOX).tobytes()]
            hs = [(f * ww_ >= 3 and f < 0.8) for f in fr]
            la, lb = ya - wy0, yb - wy0
            tl = max(int(4.2 * k), int(0.25 * h))
            gp_, i = 0, la
            while i > 0 and gp_ <= tl:
                i -= 1
                if fr[i] >= 0.8:
                    break
                if hs[i]:
                    la, gp_ = i, 0
                else:
                    gp_ += 1
            gp_, i = 0, lb
            while i < wh_ - 1 and gp_ <= tl:
                i += 1
                if fr[i] >= 0.8:
                    break
                if hs[i]:
                    lb, gp_ = i, 0
                else:
                    gp_ += 1
            line = win.crop((0, la, ww_, lb + 1))
            c = _pdfe_core(line)
            if c:
                res["core"] = ((wy0 + la + c[0]) / k, (wy0 + la + c[1]) / k)
            tl_ = _pdfe_vrun(line)
            if tl_ > 3:
                res["tall"] = tl_ / k
            try:                                             # sharper: at half contrast, the way a typed text is measured
                gl_ = pil.crop((cl, wy0 + la, cr, wy0 + lb + 1)).convert("L")
                dev = max(abs(v - bg) for v in gl_.getextrema())
                if dev >= 60:
                    mid = gl_.point(lambda v, b=bg, t=dev * 0.5: 255 if abs(v - b) > t else 0)
                    c = _pdfe_core(mid)
                    if c:
                        res["core"] = ((wy0 + la + c[0]) / k, (wy0 + la + c[1]) / k)
                    tl_ = _pdfe_vrun(mid)
                    if tl_ > 3:
                        res["tall"] = tl_ / k
                    st = _pdfe_stroke(mid)
                    if st >= 1:
                        res["stroke"] = st / k
            except Exception:
                traceback.print_exc()
    except Exception:
        traceback.print_exc()
    return res


def pdfe_text_band(pil, x0, x1, y):
    """Find the line of text under a finger. (x0, x1) is the swept range, y the height (editor units).
    The result hugs the words that were touched: (left, top, right, bottom) in units, or None when
    there is no text there.  Works on the page picture, so it also works for scanned PDFs."""
    try:
        k = pil.width / PDFE_W0
        lo, hi = min(x0, x1) * k, max(x0, x1) * k
        cy = y * k
        reach = 70 * k                                   # look a little beyond the swept range: whole words are needed
        sx0, sx1 = int(max(0, lo - reach)), int(min(pil.width, hi + reach))
        ty0, ty1 = int(max(0, cy - 70 * k)), int(min(pil.height, cy + 70 * k))
        if sx1 - sx0 < 4 or ty1 - ty0 < 4:
            return None
        strip = pil.crop((sx0, ty0, sx1, ty1)).convert("L")
        hist = strip.histogram()
        bg = max(range(256), key=lambda i: hist[i])
        ink = strip.point(lambda v, b=bg: 255 if abs(v - b) > 48 else 0)
        w, h = ink.size
        rows = [v / 255.0 for v in (ink.resize((1, h), _PDFE_BOX).tobytes())]
        has = [(f * w >= 7 and f < 0.8) for f in rows]     # a few ink dots (a cell border) is no text; a row that is almost all ink is a table line
        r0 = int(cy - ty0)
        r0 = max(0, min(h - 1, r0))
        reach_rows = int(45 * k)
        if not has[r0]:
            near = [d for d in range(1, reach_rows) if (r0 - d >= 0 and has[r0 - d]) or (r0 + d < h and has[r0 + d])]
            if not near:
                return None
            d = near[0]
            r0 = r0 - d if (r0 - d >= 0 and has[r0 - d]) else r0 + d
        tol = max(2, int(4.2 * k))          # a letter's dots / hamza can float a little above or below its body: they belong to the line
        ya = yb = r0

        def _grow(tl):
            nonlocal ya, yb
            gap = 0
            i = ya
            while i > 0 and gap <= tl:                      # up
                i -= 1
                if rows[i] >= 0.8:                          # a table line: never go through it into the next row
                    break
                if has[i]:
                    ya, gap = i, 0
                else:
                    gap += 1
            gap = 0
            i = yb
            while i < h - 1 and gap <= tl:                  # down
                i += 1
                if rows[i] >= 0.8:
                    break
                if has[i]:
                    yb, gap = i, 0
                else:
                    gap += 1
        _grow(tol)
        _grow(max(tol, int(0.25 * (yb - ya + 1))))          # the dots of a letter can float well above its body: they belong to the word

        # the words must be seen WHOLE: from here on look along the whole width of the page, not only near the finger
        # (a long word used to be cut where the strip ended, and the cut-off rest of it was left behind)
        full = pil.crop((0, ty0, pil.width, ty1)).convert("L")
        ink = full.point(lambda v, b=bg: 255 if abs(v - b) > 48 else 0)
        w, h = ink.size
        sx0 = 0
        band = ink.crop((0, ya, w, yb + 1))
        cols = [v > 0 for v in band.resize((w, 1), _PDFE_BOX).tobytes()]
        words = pdfe_words(cols, yb - ya + 1)               # the space between words is measured on the line itself
        if not words:
            return None
        # thin upright strokes that go on above and below the line are cell borders, not letters
        def _outside(row):
            if row < 0 or row >= h or rows[row] >= 0.8:
                return None                                  # off the strip, or a table line: tells nothing
            return [v > 0 for v in ink.crop((0, row, w, row + 1)).tobytes()]
        up, dn = _outside(ya - tol - 2), _outside(yb + tol + 2)
        borders = []
        for wd in words:
            if wd[1] - wd[0] + 1 <= max(6, 0.3 * (yb - ya + 1)):
                a_ = up is not None and any(up[wd[0]:wd[1] + 1])
                b_ = dn is not None and any(dn[wd[0]:wd[1] + 1])
                if a_ and b_:
                    borders.append(wd)
        words = [wd for wd in words if wd not in borders]
        if not words:
            return None
        a, b = lo - sx0, hi - sx0

        def cell(wd):
            return sum(1 for bd in borders if bd[0] < wd[0])
        hit = [wd for wd in words if wd[1] >= a - 2 and wd[0] <= b + 2]
        if hit:                                              # a swipe across a border only takes the cell where it began
            first = min(hit, key=lambda wd: abs((wd[0] + wd[1]) / 2.0 - a))
            hit = [wd for wd in hit if cell(wd) == cell(first)]
        if not hit:                                         # nothing exactly under the finger: the nearest word
            mid = (a + b) / 2.0
            hit = [min(words, key=lambda wd: min(abs(wd[0] - mid), abs(wd[1] - mid)))]
            if min(abs(hit[0][0] - mid), abs(hit[0][1] - mid)) > 60 * k:
                return None
        left, right = hit[0][0], hit[-1][1]
        pad = 0.5 * k
        return ((sx0 + left - pad) / k, (ty0 + ya - pad) / k, (sx0 + right + 1 + pad) / k, (ty0 + yb + 1 + pad) / k)
    except Exception:
        traceback.print_exc()
        return None

_PDFE_BOX = getattr(getattr(Image, "Resampling", Image), "BOX", None) if Image is not None else None
PDFE_MARK_DEF = {"hl": "#FDD835", "ul": "#E53935", "st": "#E53935"}


def pdfe_marker_geom(o):
    """(x, y, w, h, opacity) of what a text marker really paints: a highlight, an underline or a strike line."""
    x, y, w, h = o["x"], o["y"], o["w"], o["h"]
    if o.get("k") == "hl":
        return x, y, w, h, 0.42
    th = max(1.5, h * 0.085)
    if o.get("k") == "ul":
        return x, y + h - th * 1.4, w, th, 1.0
    return x, y + h / 2.0 - th / 2.0, w, th, 1.0



def pdfe_stroke_mask(o, k):
    """Mask ('L' picture, 0..255 = opacity of the colour) of one stroke at scale `k` pixels per unit.
    Returns (mask, x0, y0) with the position of its top-left corner in pixels, or None."""
    pts = o.get("p") or []
    if not pts:
        return None
    mul, alpha = PDFE_PENS.get(o.get("pen"), PDFE_PENS["pen"])
    wpx = max(1.0, o.get("w", 5.0) * mul * k)
    xs = [p[0] * k for p in pts]
    ys = [p[1] * k for p in pts]
    m = wpx / 2.0 + 3
    x0, y0 = int(min(xs) - m), int(min(ys) - m)
    x1, y1 = int(max(xs) + m) + 1, int(max(ys) + m) + 1
    bw, bh = max(2, x1 - x0), max(2, y1 - y0)
    ss = 2 if bw * bh <= 3000000 else 1
    mask = Image.new("L", (bw * ss, bh * ss), 0)
    d = ImageDraw.Draw(mask)
    poly = [((x - x0) * ss, (y - y0) * ss) for x, y in zip(xs, ys)]
    r = wpx * ss / 2.0
    if len(poly) > 1:
        try:
            d.line(poly, fill=255, width=max(1, int(round(wpx * ss))), joint="curve")
        except Exception:
            d.line(poly, fill=255, width=max(1, int(round(wpx * ss))))
    for (cx, cy) in (poly if len(poly) <= 400 else (poly[0], poly[-1])):
        d.ellipse([cx - r, cy - r, cx + r, cy + r], fill=255)
    if ss != 1:
        mask = mask.resize((bw, bh), LANCZOS)
    if alpha < 1.0:
        mask = mask.point(lambda v, a=alpha: int(v * a))
    return mask, x0, y0


def pdfe_load_image(path, w_px, h_px):
    im = Image.open(path)
    try:
        im.draft("RGB", (int(w_px * 2), int(h_px * 2)))
    except Exception:
        pass
    try:
        im = ImageOps.exif_transpose(im)
    except Exception:
        pass
    im = im.convert("RGBA")
    return im.resize((max(1, int(w_px)), max(1, int(h_px))), LANCZOS)


def pdfe_composite(base, objs):
    """Draw everything the user added onto a page picture (RGB). Objects are in editor units."""
    k = base.width / PDFE_W0
    im = pdfe_apply_raster(base.convert("RGBA"), objs)          # 1) text taken away / moved, in the order it happened
    for o in objs:                                              # 2) everything drawn on top
        t = o.get("t")
        try:
            if t == "r":
                x, y, w, h = o["x"] * k, o["y"] * k, o["w"] * k, o["h"] * k
                ImageDraw.Draw(im).rectangle([x, y, x + w, y + h], fill=pdfe_rgb(o["c"]) + (255,))
            elif t == "m":
                mx, my, mw, mh, ma = pdfe_marker_geom(o)
                bx0, by0 = int(round(mx * k)), int(round(my * k))
                bw, bh = max(1, int(round(mw * k))), max(1, int(round(mh * k)))
                im.paste(pdfe_rgb(o["c"]) + (255,), (bx0, by0, bx0 + bw, by0 + bh), Image.new("L", (bw, bh), int(255 * ma)))
            elif t == "i":
                pic = pdfe_load_image(o["f"], o["w"] * k, o["h"] * k)
                im.paste(pic, (int(round(o["x"] * k)), int(round(o["y"] * k))), pic)
            elif t == "t":
                pic = pdfe_text_pil(o["s"], o["c"], o["z"] * k, o["w"] * k, o.get("th", 0.0) * k)
                im.paste(pic, (int(round(o["x"] * k)), int(round(o["y"] * k))), pic)
            elif t == "s":
                res = pdfe_stroke_mask(o, k)
                if res:
                    mask, x0, y0 = res
                    im.paste(pdfe_rgb(o["c"]) + (255,), (x0, y0, x0 + mask.width, y0 + mask.height), mask)
        except Exception:
            traceback.print_exc()                   # one broken item must not lose the whole page
    return im.convert("RGB")


def pdfe_page_pdf(im, page_w_pts):
    """A one-page PDF (bytes) that holds the picture and is exactly as big as the original page."""
    res = im.width * 72.0 / max(1.0, float(page_w_pts))
    buf = io.BytesIO()
    im.save(buf, "PDF", resolution=res, quality=88)
    return buf.getvalue()


def _pdf_write(writer, out_path):
    tmp = out_path + ".part"
    try:
        with open(tmp, "wb") as f:
            writer.write(f)
        os.replace(tmp, out_path)
    finally:
        if os.path.exists(tmp):
            try:
                os.remove(tmp)
            except Exception:
                pass


def pdfe_build_pdf(src, out_path, page_bytes):
    """Copy the PDF; the pages in `page_bytes` ({index: one-page PDF bytes}) are swapped for the edited ones."""
    r = _pdf_open(src)
    w = _pypdf.PdfWriter()
    for i, page in enumerate(r.pages):
        if i in page_bytes:
            w.add_page(_pypdf.PdfReader(io.BytesIO(page_bytes[i])).pages[0])
        else:
            w.add_page(page)
    _pdf_write(w, out_path)
    return len(r.pages)


def pdf_remove_pages(src, out_path, remove):
    """New PDF without the pages in `remove` (0-based indexes). Returns (pages_before, pages_after)."""
    r = _pdf_open(src)
    n = len(r.pages)
    keep = [i for i in range(n) if i not in remove]
    if not keep or len(keep) == n:
        raise ValueError("nothing")
    w = _pypdf.PdfWriter()
    for i in keep:
        w.add_page(r.pages[i])
    _pdf_write(w, out_path)
    return n, len(keep)


def pdfe_sv_image(hue, size=96):
    """Saturation / brightness square of a colour picker for one hue (0..1)."""
    s = Image.new("L", (size, 1))
    s.putdata([int(i * 255 / (size - 1)) for i in range(size)])
    s = s.resize((size, size))
    v = Image.new("L", (1, size))
    v.putdata([int(255 - i * 255 / (size - 1)) for i in range(size)])
    v = v.resize((size, size))
    h = Image.new("L", (size, size), int(max(0.0, min(1.0, hue)) * 255))
    return Image.merge("HSV", (h, s, v)).convert("RGB")


def pdfe_hue_image(w=256, h=8):
    r = Image.new("L", (w, 1))
    r.putdata([int(i * 255 / (w - 1)) for i in range(w)])
    r = r.resize((w, h))
    full = Image.new("L", (w, h), 255)
    return Image.merge("HSV", (r, full, full)).convert("RGB")


def delete_original_pdf(path):
    """Delete the PDF the user chose. -> 'deleted' | 'cache' (it was only a private copy) | 'failed'."""
    try:
        if os.path.abspath(path).startswith(os.path.abspath(APP.user_data_dir)):
            return "cache"
        os.remove(path)
        media_scan(path)
        return "deleted"
    except Exception as e:
        try:
            APP.log_error(e)
        except Exception:
            pass
        return "failed"


def ask_save_mode(title, body, on_copy, on_replace):
    """Dialog with three stacked buttons: save a copy / save and delete the original / cancel."""
    holder = []

    def pick(fn):
        holder[0].dismiss()
        if fn:
            guard(fn)()
    extra = [Btn(key="sp_copy", icon="copy", on_tap=lambda: pick(on_copy)),
             Btn(key="sp_replace", icon="trash", variant="danger", on_tap=lambda: pick(on_replace)),
             Btn(key="cancel", variant="ghost", on_tap=lambda: pick(None))]
    dlg = Dialog(title=title, body=body, extra=extra)
    holder.append(dlg)
    dlg.open()


def pil_to_texture(im):
    """Kivy texture from a Pillow picture (RGBA)."""
    from kivy.graphics.texture import Texture
    im = im.convert("RGBA")
    tex = Texture.create(size=im.size, colorfmt="rgba")
    tex.blit_buffer(im.tobytes(), colorfmt="rgba", bufferfmt="ubyte")
    tex.flip_vertical()
    return tex


def _orig_note(state):
    """(text, colour) that tells what happened to the original file."""
    if state == "deleted":
        return T("sp_orig_deleted"), "ok"
    if state == "failed":
        return T("sp_orig_failed"), "warn"
    if state == "cache":
        return T("sp_orig_cache"), "warn"
    return None, "ok"


class PageTile(Tappable, FloatLayout):
    """One page of the PDF as a small picture; a tap marks it (red + bin) for deletion."""

    def __init__(self, idx, w, h, on_tap, **kw):
        super().__init__(size_hint=(None, None), size=(w, h), **kw)
        self.sfx = "tap"
        self.idx = idx
        self._tap = on_tap
        with self.canvas.before:
            Color(*rgba("#E5E7EB"))
            self._bg = RoundedRectangle(pos=self.pos, size=self.size, radius=[dp(8)])
        with self.canvas.after:
            self._dim_c = Color(0.86, 0.12, 0.12, 0)
            self._dim = RoundedRectangle(pos=self.pos, size=self.size, radius=[dp(8)])
        self.bind(pos=self._upd, size=self._upd)
        self.img = make_img(size_hint=(1, 1), pos_hint={"x": 0, "y": 0})
        self.add_widget(self.img)
        self.num = RoundBox(bg=(0, 0, 0, 0.62), radius=dp(9), size_hint=(None, None), size=(dp(32), dp(20)),
                            pos_hint={"center_x": 0.5, "y": 0.03})
        self.num.add_widget(L(raw=str(idx + 1), size=11.5, bold=True, color="#FFFFFF", fill=True, halign="center"))
        self.add_widget(self.num)
        self.bin = Icon("trash", "#FFFFFF", 34, pos_hint={"center_x": 0.5, "center_y": 0.5})
        self.bin.opacity = 0
        self.add_widget(self.bin)

    def _upd(self, *a):
        for r in (self._bg, self._dim):
            r.pos = self.pos
            r.size = self.size

    def set_marked(self, on):
        self._dim_c.a = 0.58 if on else 0
        self.bin.opacity = 1 if on else 0

    def on_release(self):
        if self._tap:
            guard(self._tap)(self)


class PDFSplitScreen(_PdfOutMixin, ToolScreen):
    """Tool 8: choose a PDF, mark the pages to delete, get a new PDF with the pages that are left."""
    bottom_pad = 40
    title_key = "tool_pdfsplit"
    COLS = 3
    MAX_THUMBS = 400

    def build_body(self):
        b = self.body
        self.src = None
        self.info = None
        self.marked = set()
        self.tiles = []
        self.total = 0
        self.engine = None
        self._gen = 0
        self._tdir = None
        self.pick_btn = Btn(raw=T("pdfz_pick"), icon="plus", on_tap=self._pick)
        b.add_widget(self.pick_btn)
        self.file_box = BoxLayout(orientation="vertical", spacing=dp(8), size_hint_y=None)
        self.file_box.bind(minimum_height=self.file_box.setter("height"))
        b.add_widget(self.file_box)
        self.work_box = BoxLayout(orientation="vertical", spacing=dp(12), size_hint_y=None)
        self.work_box.bind(minimum_height=self.work_box.setter("height"))
        b.add_widget(self.work_box)
        self.result_box = BoxLayout(orientation="vertical", spacing=dp(10), size_hint_y=None)
        self.result_box.bind(minimum_height=self.result_box.setter("height"))
        b.add_widget(self.result_box)
        self._render_file()

    # ---- state
    def _close_engine(self):
        self._gen += 1
        if self.engine is not None:
            try:
                self.engine.close()
            except Exception:
                pass
            self.engine = None
        if self._tdir:
            try:
                import shutil
                shutil.rmtree(self._tdir, ignore_errors=True)
            except Exception:
                pass
            self._tdir = None

    def _reset_work(self):
        self._close_engine()
        self.marked = set()
        self.tiles = []
        self.total = 0
        self.work_box.clear_widgets()

    def on_leave(self, *a):
        try:
            self._reset_work()
            self.src = None
            self.info = None
            self.result_box.clear_widgets()
            self.pick_btn.set_text(T("pdfz_pick"))
            self._render_file()
        except Exception:
            pass

    # ---- choosing the file
    @guard
    def _pick(self):
        APP.pick_pdfs(self._picked, multiple=False)

    @guard
    def _picked(self, paths):
        if not paths:
            return
        if not HAS_PYPDF:
            APP.toast(T("need_pypdf"), "error", 4)
            return
        self._reset_work()
        self.result_box.clear_widgets()
        self.src = paths[0]
        self.info = None
        self.pick_btn.set_text(T("pdfz_change"))
        self._render_file()
        p, gen = self.src, self._gen

        def done(res, err):
            if p != self.src or gen != self._gen:
                return
            self.info = res or (0, "bad")
            self._render_file()
            pages, state = self.info
            if state != "ok" or pages < 1:
                APP.feedback("error")
                APP.toast(T("pdf_enc") if state == "encrypted" else T("pdf_bad"), "error")
                return
            self._build_tiles(pages)
            self._start_engine(gen)
        run_bg(lambda: pdf_info(p), done)

    def _render_file(self):
        self.file_box.clear_widgets()
        if not self.src:
            self.file_box.add_widget(L("pdfz_none", size=14, color="muted", wrap=True))
            return
        row = RoundBox(bg=col("card"), radius=dp(18), size_hint_y=None, height=dp(76),
                       padding=[dp(12), dp(8)], spacing=dp(12))
        ic = RoundBox(bg=col("card_hi"), radius=dp(12), size_hint=(None, None), size=(dp(52), dp(52)), padding=dp(13))
        ic.add_widget(Icon("doc", "accent", 26))
        txt = BoxLayout(orientation="vertical", spacing=dp(1))
        txt.add_widget(L(raw=os.path.basename(self.src), size=14.5, bold=True, fill=True))
        try:
            meta = human_size(os.path.getsize(self.src))
        except Exception:
            meta = ""
        color = "muted"
        if self.info:
            pages, state = self.info
            if state == "ok":
                meta += "  ·  " + T("pdf_pages", n=pages)
            else:
                meta += "  ·  " + (T("pdf_enc_s") if state == "encrypted" else T("pdf_bad_s"))
                color = "warn"
        txt.add_widget(L(raw=meta, size=12, color=color, fill=True))
        for w in mirror([ic, txt]):
            row.add_widget(w)
        self.file_box.add_widget(row)

    # ---- the page grid
    def _build_tiles(self, pages):
        self.total = pages
        self.marked = set()
        self.tiles = []
        wb = self.work_box
        wb.clear_widgets()
        wb.add_widget(L("sp_hint", size=13.5, color="muted", wrap=True))
        self.sum = L(raw="", size=14.5, bold=True, color="accent", wrap=True)
        wb.add_widget(self.sum)
        wb.add_widget(ActionChips([("sp_all", "check", self._all), ("sp_none", "close", self._none),
                                   ("sp_invert", "rotate", self._invert)]))
        gap = dp(8)
        avail = Window.width - dp(40)
        self.tw = (avail - gap * (self.COLS - 1)) / float(self.COLS)
        self.th = self.tw * 1.414
        self.grid = GridLayout(cols=self.COLS, spacing=gap, size_hint_y=None, row_force_default=True,
                               row_default_height=self.th, col_force_default=True, col_default_width=self.tw)
        self.grid.bind(minimum_height=self.grid.setter("height"))
        for i in range(pages):
            t = PageTile(i, self.tw, self.th, self._toggle)
            self.tiles.append(t)
            self.grid.add_widget(t)
        wb.add_widget(self.grid)
        self.run_btn = Btn(key="sp_run", icon="scissors", on_tap=self._run)
        wb.add_widget(self.run_btn)
        self._update_sum()

    def _update_sum(self):
        self.sum.raw = T("sp_marked", n=len(self.marked), total=self.total)
        self.run_btn.disabled = not self.marked

    def _toggle(self, tile):
        if tile.idx in self.marked:
            self.marked.discard(tile.idx)
            tile.set_marked(False)
        else:
            self.marked.add(tile.idx)
            tile.set_marked(True)
        self._update_sum()

    def _set_marks(self, new):
        self.marked = set(new)
        for t in self.tiles:
            t.set_marked(t.idx in self.marked)
        self._update_sum()

    def _all(self):
        self._set_marks(range(self.total))

    def _none(self):
        self._set_marks(())

    def _invert(self):
        self._set_marks(i for i in range(self.total) if i not in self.marked)

    # ---- thumbnails (only when the phone can draw PDF pages; otherwise the numbers are enough)
    def _start_engine(self, gen):
        if not pdf_renderer_available():
            return
        self._tdir = os.path.join(tmp_dir(), "sp_%d" % int(time.time() * 1000))
        os.makedirs(self._tdir, exist_ok=True)
        self.engine = PdfRenderEngine(self.src)
        eng = self.engine
        eng.submit(eng.open, lambda sizes, err: self._opened(gen, sizes, err))

    def _opened(self, gen, sizes, err):
        if gen != self._gen or err or not sizes:
            return
        pw, ph = sizes[0]
        self.th = self.tw * ph / float(pw)
        self.grid.row_default_height = self.th
        for t in self.tiles:
            t.height = self.th
        self._thumb(gen, 0)

    def _thumb(self, gen, i):
        eng = self.engine
        if gen != self._gen or eng is None or i >= min(self.total, self.MAX_THUMBS):
            return
        out = os.path.join(self._tdir, "%d.jpg" % i)
        eng.submit(lambda: eng.render(i, 360, out), lambda res, err: self._thumb_done(gen, i, res))

    def _thumb_done(self, gen, i, res):
        if gen != self._gen:
            PDFViewer._rm(res)
            return
        if res and i < len(self.tiles):
            try:
                self.tiles[i].img.texture = CoreImage(res, nocache=True).texture
            except Exception:
                pass
        PDFViewer._rm(res)
        Clock.schedule_once(lambda dt: self._thumb(gen, i + 1), 0)

    # ---- saving
    @guard
    def _run(self):
        n, total = len(self.marked), self.total
        if n < 1:
            APP.feedback("error")
            APP.toast(T("sp_need_mark"), "error")
            return
        if n >= total:
            APP.feedback("error")
            APP.toast(T("sp_need_keep"), "error")
            return
        ask_save_mode(T("sp_save_q"), T("sp_save_body", n=n, m=total - n),
                      lambda: self._save(False), lambda: self._save(True))

    def _save(self, replace):
        src, marked, total = self.src, set(self.marked), self.total
        stem = safe_name(os.path.splitext(os.path.basename(src))[0], "3edda")
        name = stem + "_new.pdf"
        out = unique_path(tmp_dir(), stem + "_new", ".pdf")
        APP.busy_show(T("working"))

        def work():
            before, after = pdf_remove_pages(src, out, marked)
            pub = publish_file(out, name, "application/pdf", "pdf", APP.user_data_dir)
            state = delete_original_pdf(src) if replace else "kept"
            return before, after, pub, state

        def done(res, err):
            APP.busy_hide()
            if err is not None or not res:
                if err is not None:
                    self._pdf_error(err)
                return
            before, after, pub, state = res
            APP.feedback("success")
            APP.toast(T("sp_done"), "ok")
            APP.log_event("pdfsplit", "%s · %s → %s" % (name, T("pdf_pages", n=before), T("pdf_pages", n=after)))
            note, ncol = _orig_note(state)
            self._show_result(pub, "sp_done",
                              rows=[("sp_before", T("pdf_pages", n=before), "text"),
                                    ("sp_removed", str(before - after), "warn"),
                                    ("sp_after", T("pdf_pages", n=after), "accent")],
                              note=note, note_color=ncol)
            if state in ("deleted", "cache"):                # the old file is gone (or was only a copy): start fresh
                self._reset_work()
                self.src = None
                self.info = None
                self.pick_btn.set_text(T("pdfz_pick"))
                self._render_file()
        run_bg(work, done)


# --------------------------------------------------------------------------
# Tool 9: PDF editor
# --------------------------------------------------------------------------
class PDFESwatch(Card):
    """A round colour button."""

    def __init__(self, hexc, selected, on_tap, **kw):
        super().__init__(bg=rgba(hexc), radius=dp(17), size_hint=(None, None), size=(dp(34), dp(34)),
                         padding=dp(6), **kw)
        self.outline = col("accent") if selected else col("line")
        self._tap = on_tap
        if selected:
            lum = sum(pdfe_rgb(hexc)) / 3.0
            self.add_widget(Icon("check", "#000000" if lum > 150 else "#FFFFFF", 22))

    def on_release(self):
        if self._tap:
            guard(self._tap)()


def pdfe_color_row(current, on_pick, on_custom, recent=()):
    """Horizontal row of colours: the "+" button opens the picker (any colour), then the palette."""
    sv = ScrollView(do_scroll_x=True, do_scroll_y=False, size_hint_y=None, height=dp(44), bar_width=0)
    row = BoxLayout(orientation="horizontal", size_hint=(None, 1), spacing=dp(8), padding=[dp(2), dp(5)])
    items = [IconBtn("plus", "accent", size=34, icon_size=18, radius=17, bg="card_hi", on_tap=on_custom)]
    colors = list(PDFE_COLORS) + [c for c in recent if c.upper() not in PDFE_COLORS]
    cur = (current or "").upper()
    for hx in colors:
        items.append(PDFESwatch(hx, hx.upper() == cur, lambda h=hx: on_pick(h)))
    for w in items:
        row.add_widget(w)
    row.width = len(items) * dp(34) + (len(items) - 1) * dp(8) + dp(4)
    sv.add_widget(row)
    return sv


class PDFESV(Widget):
    """Saturation / brightness square of the colour picker."""

    def __init__(self, st, on_change, **kw):
        super().__init__(size_hint_y=None, height=dp(190), **kw)
        self.st = st
        self._cb = on_change
        with self.canvas:
            Color(1, 1, 1, 1)
            self._rect = Rectangle(pos=self.pos, size=self.size)
            self._kc = Color(1, 1, 1, 1)
            self._knob = Line(circle=(0, 0, dp(9)), width=dp(2))
            self._kc2 = Color(0, 0, 0, 1)
            self._knob2 = Line(circle=(0, 0, dp(11)), width=dp(1))
        self.bind(pos=self._upd, size=self._upd)
        self.set_hue(st["h"])

    def set_hue(self, h):
        self.st["h"] = h
        self._rect.texture = pil_to_texture(pdfe_sv_image(h))
        self._upd()

    def _upd(self, *a):
        self._rect.pos = self.pos
        self._rect.size = self.size
        cx = self.x + self.st["s"] * self.width
        cy = self.y + self.st["v"] * self.height
        self._knob.circle = (cx, cy, dp(9))
        self._knob2.circle = (cx, cy, dp(11))

    def _set(self, touch):
        self.st["s"] = max(0.0, min(1.0, (touch.x - self.x) / max(1.0, self.width)))
        self.st["v"] = max(0.0, min(1.0, (touch.y - self.y) / max(1.0, self.height)))
        self._upd()
        self._cb()

    def on_touch_down(self, touch):
        if not self.collide_point(*touch.pos):
            return False
        touch.grab(self)
        self._set(touch)
        return True

    def on_touch_move(self, touch):
        if touch.grab_current is self:
            self._set(touch)
            return True
        return False

    def on_touch_up(self, touch):
        if touch.grab_current is self:
            touch.ungrab(self)
            return True
        return False


class PDFEHue(Widget):
    def __init__(self, st, on_change, **kw):
        super().__init__(size_hint_y=None, height=dp(34), **kw)
        self.st = st
        self._cb = on_change
        with self.canvas:
            Color(1, 1, 1, 1)
            self._rect = Rectangle(pos=self.pos, size=self.size, texture=pil_to_texture(pdfe_hue_image()))
            Color(1, 1, 1, 1)
            self._knob = Line(circle=(0, 0, dp(12)), width=dp(2.2))
        self.bind(pos=self._upd, size=self._upd)
        self._upd()

    def _upd(self, *a):
        bh = dp(18)
        self._rect.pos = (self.x, self.center_y - bh / 2)
        self._rect.size = (self.width, bh)
        self._knob.circle = (self.x + self.st["h"] * self.width, self.center_y, dp(12))

    def _set(self, touch):
        self.st["h"] = max(0.0, min(1.0, (touch.x - self.x) / max(1.0, self.width)))
        self._upd()
        self._cb()

    def on_touch_down(self, touch):
        if not self.collide_point(*touch.pos):
            return False
        touch.grab(self)
        self._set(touch)
        return True

    def on_touch_move(self, touch):
        if touch.grab_current is self:
            self._set(touch)
            return True
        return False

    def on_touch_up(self, touch):
        if touch.grab_current is self:
            touch.ungrab(self)
            return True
        return False


def open_color_dialog(initial, on_ok):
    """Pick ANY colour: hue bar + saturation/brightness square."""
    import colorsys
    r, g, b = [c / 255.0 for c in pdfe_rgb(initial)]
    h, s, v = colorsys.rgb_to_hsv(r, g, b)
    st = {"h": h, "s": s, "v": v}
    prev = RoundBox(bg=rgba(initial), radius=dp(12), size_hint_y=None, height=dp(44))
    hexl = L(raw=initial.upper(), size=15, bold=True, fill=True, halign="center", size_hint_x=None, width=dp(100))

    def cur_hex():
        rr, gg, bb = colorsys.hsv_to_rgb(st["h"], st["s"], st["v"])
        return pdfe_hex((rr * 255, gg * 255, bb * 255))

    def changed():
        hx = cur_hex()
        prev.bg = rgba(hx)
        hexl.raw = hx
    sv = PDFESV(st, changed)
    hue = PDFEHue(st, lambda: (sv.set_hue(st["h"]), changed()))
    Dialog(title=T("pe_color_title"), extra=[sv, hue, hrow([prev, hexl], height=44)],
           buttons=[(T("cancel"), "secondary", None), (T("ok"), "primary", lambda: guard(on_ok)(cur_hex()))]).open()


class PDFEPreview(Widget):
    """Little sample of the current pen (colour, thickness, opacity)."""

    def __init__(self, **kw):
        super().__init__(size_hint=(None, None), size=(dp(64), dp(40)), **kw)
        self.bind(pos=self.show, size=self.show)
        self._args = ("pen", "#000000", 5.0)

    def show(self, *a):
        pen, hexc, w = self._args
        mul, alpha = PDFE_PENS[pen]
        r, g, b = [c / 255.0 for c in pdfe_rgb(hexc)]
        th = max(2.0, min(dp(30), w * mul * 1.6))
        self.canvas.clear()
        with self.canvas:
            Color(r, g, b, alpha)
            Line(points=[self.x + dp(10), self.center_y, self.right - dp(10), self.center_y],
                 width=max(1.0, th / 2.0), cap="round")

    def set(self, pen, hexc, w):
        self._args = (pen, hexc, w)
        self.show()


class PDFEToolBtn(Card):
    def __init__(self, icon, on_tap, **kw):
        super().__init__(bg=col("card"), radius=dp(14), size_hint_y=None, height=dp(48), padding=dp(4), **kw)
        self._name = icon
        self._tap = on_tap
        self.icon = Icon(icon, "text", 24)
        holder = AnchorLayout()
        holder.add_widget(self.icon)
        self.add_widget(holder)

    def set_active(self, on):
        self.bg = col("accent") if on else col("card")
        self.icon.set_icon(self._name, "on_acc" if on else "text")

    def on_release(self):
        if self._tap:
            guard(self._tap)()


class PDFEPage(StencilView):
    """The page being edited: shows the picture + everything added, and handles touches
    (draw / erase / select, move, resize / pinch to zoom / drag to move the page)."""

    def __init__(self, ed, **kw):
        super().__init__(**kw)
        self.ed = ed
        self.W = PDFE_W0
        self.H = PDFE_W0 * 1.414
        self.tex = None
        self.s = 1.0
        self.ox = self.oy = 0.0
        self._user = False
        self._tc = {}
        self._g = None
        self._pinch = None
        self._fit_s = 1.0
        self.bind(pos=self._geom, size=self._geom)

    # ---- view
    def set_page(self, h, tex=None):
        self.H = h
        self.tex = tex
        self._g = None
        self.fit()

    def set_tex(self, tex):
        self.tex = tex
        self.redraw()

    def _geom(self, *a):
        if self._user:
            self._clamp()
            self.redraw()
        else:
            self.fit()

    def fit(self):
        self._user = False
        if self.width < 10 or self.height < 10:
            return
        m = dp(8)
        self.s = max(0.01, min((self.width - 2 * m) / self.W, (self.height - 2 * m) / self.H))
        self._fit_s = self.s
        self.ox = self.x + (self.width - self.W * self.s) / 2.0
        self.oy = self.y + (self.height - self.H * self.s) / 2.0
        self.redraw()

    def _clamp(self):
        keep = dp(60)
        pw, ph = self.W * self.s, self.H * self.s
        self.ox = max(self.x + keep - pw, min(self.x + self.width - keep, self.ox))
        self.oy = max(self.y + keep - ph, min(self.y + self.height - keep, self.oy))

    def to_page(self, x, y):
        return (x - self.ox) / self.s, self.H - (y - self.oy) / self.s

    # ---- drawing
    def redraw(self, *a):
        ed = self.ed
        s, ox, oy, H = self.s, self.ox, self.oy, self.H

        def X(x):
            return ox + x * s

        def Y(y):
            return oy + (H - y) * s
        c = self.canvas
        c.clear()
        with c:
            Color(*rgba(C["card"]))
            Rectangle(pos=self.pos, size=self.size)
            Color(1, 1, 1, 1)
            Rectangle(pos=(ox, oy), size=(self.W * s, H * s))
            if self.tex is not None:
                Color(1, 1, 1, 1)
                Rectangle(texture=self.tex, pos=(ox, oy), size=(self.W * s, H * s))
            lst = ed.objs()
            for o in [x for x in lst if x["t"] in ("e", "g")] + [x for x in lst if x["t"] not in ("e", "g")]:
                try:
                    self._draw_obj(o, X, Y, s)
                except Exception:
                    traceback.print_exc()
            pend = ed.pending
            if pend is not None and ed.tool == "edit":
                ar, ag, ab, _a = rgba(C["accent"])
                Color(ar, ag, ab, 0.28)
                Rectangle(pos=(X(pend[0]), Y(pend[3])), size=((pend[2] - pend[0]) * s, (pend[3] - pend[1]) * s))
                Color(ar, ag, ab, 1)
                Line(rectangle=(X(pend[0]), Y(pend[3]), (pend[2] - pend[0]) * s, (pend[3] - pend[1]) * s), width=dp(1.2))
                for hx in (pend[0], pend[2]):
                    Ellipse(pos=(X(hx) - dp(6), Y((pend[1] + pend[3]) / 2.0) - dp(6)), size=(dp(12), dp(12)))
            sel = ed.sel
            if sel is not None and ed.tool in ("select", "text", "image"):
                bx, by, bw, bh = ed.bbox(sel)
                if sel["t"] == "t" and not (sel["s"] or "").strip():
                    ar, ag, ab, _a = rgba(C["accent"])
                    Color(ar, ag, ab, 0.14)
                    Rectangle(pos=(X(bx), Y(by + bh)), size=(bw * s, bh * s))
                Color(*rgba(C["accent"]))
                Line(rectangle=(X(bx), Y(by + bh), bw * s, bh * s), width=dp(1.2), dash_length=dp(5), dash_offset=dp(4))
                hp = ed.handle_pos(sel)
                if hp:
                    r = dp(10)
                    Color(*rgba(C["accent"]))
                    Ellipse(pos=(X(hp[0]) - r, Y(hp[1]) - r), size=(2 * r, 2 * r))
                    Color(1, 1, 1, 1)
                    Ellipse(pos=(X(hp[0]) - r / 2, Y(hp[1]) - r / 2), size=(r, r))

    def _draw_obj(self, o, X, Y, s):
        t = o["t"]
        if t == "s":
            mul, alpha = PDFE_PENS[o["pen"]]
            r, g, b = [v / 255.0 for v in pdfe_rgb(o["c"])]
            if alpha < 1.0:
                tx = self.ed.stroke_tex(o)
                if tx:
                    tex, x, y, w, h = tx
                    Color(1, 1, 1, 1)
                    Rectangle(texture=tex, pos=(X(x), Y(y + h)), size=(w * s, h * s))
                    return
            flat = []
            for (x, y) in o["p"]:
                flat += [X(x), Y(y)]
            Color(r, g, b, alpha)
            Line(points=flat, width=max(1.0, o["w"] * mul * s / 2.0), cap="round", joint="round")
        elif t == "t":
            tex, w, h = self.ed.text_tex(o)
            Color(1, 1, 1, 1)
            Rectangle(texture=tex, pos=(X(o["x"]), Y(o["y"] + h)), size=(w * s, h * s))
        elif t == "i":
            tex = self.ed.img_tex(o["f"])[0]
            Color(1, 1, 1, 1)
            Rectangle(texture=tex, pos=(X(o["x"]), Y(o["y"] + o["h"])), size=(o["w"] * s, o["h"] * s))
        elif t == "r":
            r, g, b = [v / 255.0 for v in pdfe_rgb(o["c"])]
            Color(r, g, b, 1)
            Rectangle(pos=(X(o["x"]), Y(o["y"] + o["h"])), size=(o["w"] * s, o["h"] * s))
        elif t in ("e", "g"):
            for tex, x, y, w, h in (self.ed.erase_tex(o) or ()):
                Color(1, 1, 1, 1)
                Rectangle(texture=tex, pos=(X(x), Y(y + h)), size=(w * s, h * s))
        elif t == "m":
            r, g, b = [v / 255.0 for v in pdfe_rgb(o["c"])]
            mx, my, mw, mh, ma = pdfe_marker_geom(o)
            Color(r, g, b, ma)
            Rectangle(pos=(X(mx), Y(my + mh)), size=(mw * s, mh * s))

    # ---- touches
    def on_touch_down(self, touch):
        if not self.collide_point(*touch.pos) or getattr(touch, "is_mouse_scrolling", False):
            return False
        touch.grab(self)
        self._tc[touch.uid] = touch
        if len(self._tc) >= 2:
            self._cancel_gesture()
            self._pinch_begin()
        elif self.ed.ready:
            self._begin(touch)
        return True

    def on_touch_move(self, touch):
        if touch.grab_current is not self or touch.uid not in self._tc:
            return False
        if self._pinch:
            self._pinch_move()
        elif self._g:
            self._move(touch)
        return True

    def on_touch_up(self, touch):
        if touch.grab_current is not self:
            return False
        touch.ungrab(self)
        self._tc.pop(touch.uid, None)
        if self._pinch:
            if len(self._tc) < 2:
                self._pinch = None
                self._g = None
        elif self._g:
            self._end(touch)
        return True

    def _cancel_gesture(self):
        g = self._g
        self._g = None
        if g and g.get("kind") in ("draw", "rect", "erase", "band"):
            self.redraw()

    def _pinch_begin(self):
        ts = list(self._tc.values())[:2]
        d = math.hypot(ts[0].x - ts[1].x, ts[0].y - ts[1].y)
        cx, cy = (ts[0].x + ts[1].x) / 2.0, (ts[0].y + ts[1].y) / 2.0
        self._pinch = {"d": max(8.0, d), "s": self.s,
                       "px": (cx - self.ox) / self.s, "py": (cy - self.oy) / self.s}

    def _pinch_move(self):
        ts = list(self._tc.values())[:2]
        if len(ts) < 2:
            return
        p = self._pinch
        d = math.hypot(ts[0].x - ts[1].x, ts[0].y - ts[1].y)
        cx, cy = (ts[0].x + ts[1].x) / 2.0, (ts[0].y + ts[1].y) / 2.0
        fit = getattr(self, "_fit_s", self.s)
        self.s = max(fit * 0.5, min(fit * 8.0, p["s"] * d / p["d"]))
        self.ox = cx - p["px"] * self.s
        self.oy = cy - p["py"] * self.s
        self._user = True
        self._clamp()
        self.redraw()

    def _begin(self, touch):
        ed = self.ed
        px, py = self.to_page(touch.x, touch.y)
        tool = ed.tool
        if tool == "pen":
            if ed.sel is not None:
                ed.sel = None
            mul, alpha = PDFE_PENS[ed.pen]
            r, g, b = [v / 255.0 for v in pdfe_rgb(ed.color)]
            flat = [touch.x, touch.y]
            with self.canvas:
                Color(r, g, b, alpha)
                line = Line(points=flat + flat, width=max(1.0, ed.pw * mul * self.s / 2.0), cap="round", joint="round")
            self._g = {"kind": "draw", "pts": [(px, py)], "flat": flat, "line": line, "last": (touch.x, touch.y)}
        elif tool == "eraser":
            self._g = {"kind": "erase", "pushed": False, "ring": None}
            self._erase(touch)
        elif tool in ("edit", "mark"):
            band = pdfe_text_band(ed.det(), px, px, py) if ed.page_pil is not None else None
            if band is not None:                    # the text line under the finger: it follows the finger along the line
                ar, ag, ab, _a = rgba(C["accent"])
                with self.canvas:
                    Color(ar, ag, ab, 0.35)
                    box = Rectangle(pos=(touch.x, touch.y), size=(1, 1))
                self._g = {"kind": "band", "x0": px, "y0": py, "px": px, "py": py, "box": box, "band": band}
                self._band_live(self._g)
            else:
                with self.canvas:
                    Color(*rgba(C["accent"]))
                    line = Line(rectangle=(touch.x, touch.y, 1, 1), width=dp(1.4), dash_length=dp(5), dash_offset=dp(4))
                self._g = {"kind": "rect", "x0": px, "y0": py, "sx": touch.x, "sy": touch.y, "line": line, "px": px, "py": py}
        else:
            sel = ed.sel
            tol = dp(14) / self.s
            if sel is not None:
                hp = ed.handle_pos(sel)
                if hp and math.hypot(px - hp[0], py - hp[1]) <= dp(26) / self.s:
                    self._g = {"kind": "resize", "o": sel, "base": dict(sel), "began": False}
                    return
            o = ed.hit(px, py, tol)
            if o is not None:
                if o is not sel:
                    ed.select(o)
                if o["t"] == "e":
                    self._g = {"kind": "none"}
                    return
                self._g = {"kind": "move", "o": o, "sx": px, "sy": py, "moved": False}
            else:
                if sel is not None:
                    ed.select(None)
                self._g = {"kind": "pan", "lx": touch.x, "ly": touch.y, "moved": 0.0, "p0": (px, py)}

    def _move(self, touch):
        g = self._g
        ed = self.ed
        k = g["kind"]
        px, py = self.to_page(touch.x, touch.y)
        if k == "draw":
            lx, ly = g["last"]
            if math.hypot(touch.x - lx, touch.y - ly) < dp(1.6):
                return
            g["last"] = (touch.x, touch.y)
            g["pts"].append((px, py))
            g["flat"].extend([touch.x, touch.y])
            g["line"].points = g["flat"]
        elif k == "erase":
            self._erase(touch)
        elif k == "band":
            g["px"], g["py"] = px, py
            self._band_live(g)
        elif k == "rect":
            x0, y0 = g["sx"], g["sy"]
            g["line"].rectangle = (min(x0, touch.x), min(y0, touch.y), abs(touch.x - x0), abs(touch.y - y0))
            g["px"], g["py"] = px, py
        elif k == "pan":
            dx, dy = touch.x - g["lx"], touch.y - g["ly"]
            g["lx"], g["ly"] = touch.x, touch.y
            g["moved"] += math.hypot(dx, dy)
            if g["moved"] > dp(6):
                self.ox += dx
                self.oy += dy
                self._user = True
                self._clamp()
                self.redraw()
        elif k == "move":
            if not g["moved"]:
                if math.hypot(px - g["sx"], py - g["sy"]) * self.s < dp(6):
                    return
                g["moved"] = True
                g["o"] = ed.begin_edit(g["o"])
                g["base"] = dict(g["o"])
            n, b = g["o"], g["base"]
            dx, dy = px - g["sx"], py - g["sy"]
            if n["t"] == "s":
                n["p"] = [(x + dx, y + dy) for (x, y) in b["p"]]
            else:
                n["x"], n["y"] = b["x"] + dx, b["y"] + dy
            self.redraw()
        elif k == "resize":
            if not g["began"]:
                g["began"] = True
                g["o"] = ed.begin_edit(g["o"])
            n, b = g["o"], g["base"]
            bx, by, bw, bh = ed.bbox(b)
            if b["t"] in ("t", "i"):
                d0 = max(1.0, math.hypot(bw, bh))
                f = max(0.1, min(12.0, math.hypot(px - bx, py - by) / d0))
                if b["t"] == "t":
                    n["z"] = max(6.0, min(240.0, b["z"] * f))
                    n["w"] = max(20.0, min(PDFE_W0 * 2, b["w"] * f))
                else:
                    n["w"], n["h"] = b["w"] * f, b["h"] * f
            elif b["t"] in ("r", "m"):
                n["w"], n["h"] = max(4.0, px - bx), max(4.0, py - by)
            self.redraw()

    def _band_live(self, g):
        """Show the swept part of the text line while the finger moves."""
        by0, by1 = g["band"][1], g["band"][3]
        xa, xb = sorted((g["x0"], g["px"]))
        xa, xb = max(xa, g["band"][0]) if xb - xa > 1 else g["band"][0], max(xb, g["band"][0] + 3)
        g["box"].pos = (self.ox + min(xa, xb) * self.s, self.oy + (self.H - by1) * self.s)
        g["box"].size = (max(dp(6), abs(xb - xa) * self.s), (by1 - by0) * self.s)

    def _end(self, touch):
        g = self._g
        self._g = None
        ed = self.ed
        k = g["kind"]
        if k == "draw":
            pts = g["pts"]
            if len(pts) == 1:
                pts = pts + [(pts[0][0] + 0.02, pts[0][1])]
            ed.commit_stroke(pts)
        elif k == "erase":
            self.redraw()
        elif k == "resize":
            ed._learn_bias(ed.sel)
            ed._build_opts()
        elif k == "band":
            self.redraw()
            x0, x1 = sorted((g["x0"], g["px"]))
            b = pdfe_text_band(ed.det(), x0, x1, g["y0"])
            if b is None:
                APP.toast(T("pe_no_text"), "info")
            elif ed.tool == "mark":
                ed.add_marker(b)
            else:
                ed.select_text(b)
        elif k == "rect":
            x0, y0, x1, y1 = g["x0"], g["y0"], g["px"], g["py"]
            self.redraw()
            if ed.tool == "mark":
                APP.toast(T("pe_no_text"), "info")
            elif abs(x1 - x0) * self.s > dp(10) and abs(y1 - y0) * self.s > dp(8):
                rx0, rx1, ry0, ry1 = min(x0, x1), max(x0, x1), min(y0, y1), max(y0, y1)
                b = pdfe_text_band(ed.det(), rx0, rx1, (ry0 + ry1) / 2.0) if ed.page_pil is not None else None
                if b is not None:                       # snap to the words of ONE line (no tall boxes over many rows)
                    ed.select_text(b)
                elif ry1 - ry0 > 60:
                    APP.toast(T("pe_no_text"), "info")
                else:
                    ed.select_text((rx0, ry0, rx1, ry1))
        elif k == "pan":
            pass                                    # (text boxes come from the + button now)
        ed.end_edit()

    def _erase(self, touch):
        ed = self.ed
        g = self._g
        px, py = self.to_page(touch.x, touch.y)
        if ed.erase_at(px, py, ed.erw, g):
            self.redraw()
        r = ed.erw * self.s
        if g.get("ring") is None:
            with self.canvas:
                Color(*rgba(C["accent"]))
                g["ring"] = Line(circle=(touch.x, touch.y, r), width=dp(1.2))
        else:
            g["ring"].circle = (touch.x, touch.y, r)


class PDFEditor(ModalView):
    """Full-screen PDF editor: pen / eraser / text / images / cover-and-replace old text."""
    back_closes = True
    RES = 1500
    EXPORT_W = 1700
    TOOLS = [("select", "cursor", "pe_t_select"), ("pen", "pen", "pe_t_pen"), ("mark", "highlight", "pe_t_mark"),
             ("eraser", "eraser", "pe_t_eraser"), ("text", "text", "pe_t_text"), ("image", "image", "pe_t_image"),
             ("edit", "textbox", "pe_t_edit")]

    def __init__(self, path, on_saved=None, **kw):
        super().__init__(**_modal_kwargs(size_hint=(1, 1), background_color=rgba(C["bg"])))
        self.path = path
        self.on_saved = on_saved
        self.sizes = []
        self.page = 0
        self.ann = {}
        self.undo_st = []
        self.redo_st = []
        self.tool = "select"
        self.pen = "pen"
        self.color = "#E53935"
        self.tcolor = "#000000"
        self.pending = None                   # the text chosen with the "edit text" tool: (left, top, right, bottom)
        self.mkind = "hl"
        self.mcolor = PDFE_MARK_DEF["hl"]
        self.pw = 5.0
        self.erw = 16.0
        self.tsize = 34.0
        self.sel = None
        self.dirty = False
        self.ready = False
        self.loading = True
        self._editing = None
        self._gen = 0
        self._tcache = {}
        self._icache = {}
        self.page_pil = None
        self._det = None                      # cache: the page picture after the edits that change it
        self._live_box = None
        self._serial = 0
        self._err_shown = False
        self.dir = os.path.join(tmp_dir(), "pe_%d" % int(time.time() * 1000))
        os.makedirs(self.dir, exist_ok=True)
        self.engine = PdfRenderEngine(path)
        root = RoundBox(orientation="vertical", bg=col("bg"), radius=0,
                        padding=[dp(8), dp(8) + top_inset_px(), dp(8), dp(8)], spacing=dp(6))
        self.undo_b = IconBtn("undo", "text", size=42, icon_size=21, on_tap=self.do_undo)
        self.redo_b = IconBtn("redo", "text", size=42, icon_size=21, on_tap=self.do_redo)
        self.save_b = IconBtn("save", "on_acc", size=42, icon_size=21, bg="accent", on_tap=self._save)
        close = IconBtn("close", "text", size=42, icon_size=21, on_tap=self.dismiss)
        title = L(raw=os.path.basename(path), size=15, bold=True, fill=True)
        root.add_widget(hrow([close, title, self.undo_b, self.redo_b, self.save_b], height=44, spacing=6))
        self.prev_b = IconBtn("up", "text", size=38, icon_size=20, on_tap=lambda: self.goto(self.page - 1))
        self.next_b = IconBtn("down", "text", size=38, icon_size=20, on_tap=lambda: self.goto(self.page + 1))
        self.fit_b = IconBtn("fit", "text", size=38, icon_size=20, on_tap=lambda: self.view.fit())
        self.page_lbl = L(raw="", size=13.5, bold=True, fill=True, halign="center")
        root.add_widget(hrow([self.prev_b, self.page_lbl, self.next_b, self.fit_b], height=40, spacing=6))
        self.view = PDFEPage(self)
        root.add_widget(self.view)
        self.opts = BoxLayout(orientation="vertical", spacing=dp(6), size_hint_y=None)
        self.opts.bind(minimum_height=self.opts.setter("height"))
        card = RoundBox(orientation="vertical", bg=col("card"), radius=dp(18), padding=[dp(10), dp(8)],
                        size_hint_y=None)
        card.bind(minimum_height=card.setter("height"))
        card.add_widget(self.opts)
        root.add_widget(card)
        row = BoxLayout(orientation="horizontal", spacing=dp(6), size_hint_y=None, height=dp(48))
        self.tool_btns = {}
        btns = []
        for tid, icon, _k in self.TOOLS:
            b = PDFEToolBtn(icon, lambda t=tid: self.set_tool(t))
            self.tool_btns[tid] = b
            btns.append(b)
        for b in mirror(btns):
            row.add_widget(b)
        root.add_widget(row)
        self.add_widget(root)
        self._upd_ur()
        self.set_tool("select")
        self.engine.submit(self.engine.open, self._opened)

    # ---- opening / pages
    def _opened(self, sizes, err):
        if err or not sizes:
            APP.feedback("error")
            msg = str(err).lower()
            APP.toast(T("pdf_enc") if ("password" in msg or "security" in msg) else T("pdf_bad"), "error")
            self.dismiss(force=True)
            return
        self.sizes = sizes
        self.ready = True
        self.goto(0)

    def goto(self, i):
        if not (0 <= i < len(self.sizes)):
            return
        self._drop_empty()
        self.page = i
        self.sel = None
        self.pending = None
        self._editing = None
        self._gen += 1
        self.loading = True
        pw, ph = self.sizes[i]
        self.page_pil = None
        self.view.set_page(PDFE_W0 * ph / float(pw), None)
        self.page_lbl.raw = T("pe_page", i=i + 1, n=len(self.sizes))
        self.prev_b.opacity = 1 if i > 0 else 0.35
        self.next_b.opacity = 1 if i < len(self.sizes) - 1 else 0.35
        gen = self._gen
        out = os.path.join(self.dir, "p%d_%d.jpg" % (gen, i))
        eng = self.engine
        eng.submit(lambda: eng.render(i, self.RES, out), lambda res, err: self._page_ready(gen, res, err))
        self._build_opts()

    def _page_ready(self, gen, res, err):
        if gen != self._gen:
            PDFViewer._rm(res)
            return
        if err or not res:
            if not self._err_shown:
                self._err_shown = True
                try:
                    APP.log_error(err or "render")
                except Exception:
                    pass
                APP.toast(T("pdf_bad"), "error")
            return
        try:
            self.page_pil = Image.open(res).convert("RGB")
            self.loading = False
            self.view.set_tex(CoreImage(res, nocache=True).texture)
        except Exception:
            traceback.print_exc()
        PDFViewer._rm(res)

    # ---- annotations store
    def objs(self):
        return self.ann.setdefault(self.page, [])

    def _snap(self):
        return {k: list(v) for k, v in self.ann.items()}

    def push_undo(self):
        self.undo_st.append(self._snap())
        del self.undo_st[:-60]
        self.redo_st = []
        self.dirty = True
        self._upd_ur()

    def _after_hist(self):
        self.pending = None
        self.sel = None
        self._editing = None
        self.dirty = any(self.ann.values())
        self.view.redraw()
        self._build_opts()
        self._upd_ur()

    def do_undo(self):
        if self.undo_st:
            self.redo_st.append(self._snap())
            self.ann = self.undo_st.pop()
            self._after_hist()

    def do_redo(self):
        if self.redo_st:
            self.undo_st.append(self._snap())
            self.ann = self.redo_st.pop()
            self._after_hist()

    def _upd_ur(self):
        self.undo_b.opacity = 1 if self.undo_st else 0.35
        self.redo_b.opacity = 1 if self.redo_st else 0.35

    def add_obj(self, o):
        self.push_undo()
        self.objs().append(o)
        self.sel = o
        self._editing = o
        self.view.redraw()
        self._build_opts()

    def begin_edit(self, o):
        """The object is about to change: remember the old state once, and return the copy to change."""
        if o is self._editing:
            return o
        self.push_undo()
        lst = self.objs()
        n = dict(o)
        for i, x in enumerate(lst):
            if x is o:
                lst[i] = n
                break
        self.sel = n
        self._editing = n
        return n

    def end_edit(self):
        self._editing = None

    def remove_obj(self, o):
        self.push_undo()
        lst = self.objs()
        for i, x in enumerate(lst):
            if x is o:
                del lst[i]
                break
        self.sel = None
        self._editing = None
        self.view.redraw()
        self._build_opts()

    def select(self, o):
        self.sel = o
        self._editing = None
        self.view.redraw()
        self._build_opts()

    def add_marker(self, b):
        """Highlight / underline / strike the text line b = (left, top, right, bottom)."""
        self.push_undo()
        self.objs().append({"t": "m", "k": self.mkind, "c": self.mcolor, "x": b[0], "y": b[1],
                            "w": max(4.0, b[2] - b[0]), "h": max(4.0, b[3] - b[1])})
        self.view.redraw()

    def commit_stroke(self, pts):
        o = {"t": "s", "pen": self.pen, "c": self.color, "w": self.pw, "p": list(pts)}
        self.push_undo()
        self.objs().append(o)
        self.view.redraw()

    def erase_at(self, px, py, r, g):
        lst = self.objs()
        hit = [o for o in lst
               if (o["t"] == "s" and self._near(o, px, py, r + o["w"] * PDFE_PENS[o["pen"]][0] / 2.0))
               or (o["t"] == "m" and o["x"] - 2 <= px <= o["x"] + o["w"] + 2 and o["y"] - 2 <= py <= o["y"] + o["h"] + 2)]
        if not hit:
            return False
        if g is not None and not g.get("pushed"):
            g["pushed"] = True
            self.push_undo()
        lst[:] = [o for o in lst if not any(o is h for h in hit)]
        if self.sel is not None and any(self.sel is h for h in hit):
            self.sel = None
        return True

    def clear_drawings(self):
        lst = self.objs()
        if any(o["t"] == "s" for o in lst):
            self.push_undo()
            lst[:] = [o for o in lst if o["t"] != "s"]
            self.view.redraw()

    # ---- geometry
    @staticmethod
    def _near(o, px, py, r):
        pts = o["p"]
        if len(pts) == 1:
            return math.hypot(px - pts[0][0], py - pts[0][1]) <= r
        for (ax, ay), (bx, by) in zip(pts, pts[1:]):
            dx, dy = bx - ax, by - ay
            L2 = dx * dx + dy * dy
            t = 0.0 if L2 == 0 else max(0.0, min(1.0, ((px - ax) * dx + (py - ay) * dy) / L2))
            if math.hypot(px - (ax + t * dx), py - (ay + t * dy)) <= r:
                return True
        return False

    def bbox(self, o):
        t = o["t"]
        if t == "s":
            xs = [p[0] for p in o["p"]]
            ys = [p[1] for p in o["p"]]
            m = o["w"] * PDFE_PENS[o["pen"]][0] / 2.0
            return min(xs) - m, min(ys) - m, max(xs) - min(xs) + 2 * m, max(ys) - min(ys) + 2 * m
        if t == "t":
            return o["x"], o["y"], o["w"], self.text_tex(o)[2]
        return o["x"], o["y"], o["w"], o["h"]

    def handle_pos(self, o):
        if o["t"] in ("s", "e", "g"):
            return None
        x, y, w, h = self.bbox(o)
        return x + w, y + h

    def hit(self, px, py, tol):
        for o in reversed(self.objs()):
            if o["t"] == "g":
                continue
            if o["t"] == "s":
                if self._near(o, px, py, tol + o["w"] * PDFE_PENS[o["pen"]][0] / 2.0):
                    return o
            else:
                x, y, w, h = self.bbox(o)
                if x - tol <= px <= x + w + tol and y - tol <= py <= y + h + tol:
                    return o
        return None

    # ---- pictures of text / images / soft strokes
    def text_tex(self, o):
        key = (o["s"], o["c"], round(o["z"], 2), round(o["w"], 2), round(o.get("th", 0.0), 2))
        r = self._tcache.get(key)
        if r is None:
            im = pdfe_text_pil(o["s"], o["c"], o["z"] * PDFE_SC, o["w"] * PDFE_SC, o.get("th", 0.0) * PDFE_SC)
            r = (pil_to_texture(im), im.width / PDFE_SC, im.height / PDFE_SC)
            if len(self._tcache) > 100:
                self._tcache.clear()
            self._tcache[key] = r
        return r

    def img_tex(self, path):
        r = self._icache.get(path)
        if r is None:
            im = Image.open(path)
            try:
                im.draft("RGB", (1600, 1600))
            except Exception:
                pass
            try:
                im = ImageOps.exif_transpose(im)
            except Exception:
                pass
            iw, ih = im.size
            im = im.convert("RGBA")
            im.thumbnail((1400, 1400), LANCZOS)
            r = (pil_to_texture(im), iw, ih)
            if len(self._icache) > 10:
                self._icache.clear()
            self._icache[path] = r
        return r

    def det(self):
        """The page picture as the user SEES it: the page plus the text that was taken away or moved.
        This is what the text tools look at (so a moved word is found where it now stands)."""
        base = self.page_pil
        if base is None:
            return None
        ras = [o for o in self.objs() if o["t"] in ("e", "g")]
        if not ras:
            return base
        key = (self.page, id(base), tuple(o.get("_n", id(o)) for o in ras))
        c = self._det
        if c is not None and c[0] == key:
            return c[1]
        im = pdfe_raster(base, ras)
        self._det = (key, im)
        return im

    def raster_before(self, o):
        """The page picture as it was just before object `o` was made."""
        base = self.page_pil
        if base is None:
            return None
        ras = []
        for x in self.objs():
            if x is o:
                break
            if x["t"] in ("e", "g"):
                ras.append(x)
        return pdfe_raster(base, ras) if ras else base

    def _tex_for(self, o, base):
        """Screen pictures of a taken-away ("e") or moved ("g") text, made from picture `base`."""
        k = base.width / PDFE_W0
        box = (o["x"], o["y"], o["x"] + o["w"], o["y"] + o["h"])
        r = []
        if o["t"] == "g":
            res = pdfe_move_pics(base, box, o["dx"], pdfe_rgb(o["c"]))
            if res:
                patch, ghost, px, py, nx = res
                r = [(pil_to_texture(patch), px / k, py / k, patch.width / k, patch.height / k),
                     (pil_to_texture(ghost), nx / k, py / k, ghost.width / k, ghost.height / k)]
        else:
            res = pdfe_ink_patch(base, box, pdfe_rgb(o["c"]))
            if res:
                patch, px, py = res
                r = [(pil_to_texture(patch), px / k, py / k, patch.width / k, patch.height / k)]
        o["_tx"] = r
        return r

    def erase_tex(self, o):
        """Pictures that take the old letters away (and show moved letters in their new place). -> list of
        (texture, x, y, w, h) in units, or None."""
        r = o.get("_tx")
        if r is None:
            base = self.raster_before(o)
            if base is None:
                return None
            r = self._tex_for(o, base)
        return r or None

    def stroke_tex(self, o):
        """Pencil / highlighter: drawn once as a picture so overlapping parts do not get darker.
        -> (texture, x, y, w, h) in units (1 unit = 1 pixel here), or None."""
        r = o.get("_tx")
        if r is None:
            res = pdfe_stroke_mask(o, 1.0)
            if not res:
                return None
            mask, x0, y0 = res
            im = Image.new("RGBA", mask.size, pdfe_rgb(o["c"]) + (0,))
            im.putalpha(mask)
            r = (pil_to_texture(im), x0, y0, mask.width, mask.height, o["p"][0])
            o["_tx"] = r
        tex, x0, y0, w, h, p0 = r
        dx, dy = o["p"][0][0] - p0[0], o["p"][0][1] - p0[1]       # the stroke was moved: move the picture too
        return tex, x0 + dx, y0 + dy, w, h

    # ---- tools and options
    def set_tool(self, t):
        self._drop_empty()
        self.tool = t
        self.pending = None
        self.sel = None
        self._editing = None
        for k, b in self.tool_btns.items():
            b.set_active(k == t)
        self.view.redraw()
        self._build_opts()

    def _slider(self, key, vmin, vmax, value, on_change):
        sl = SliderX(vmin=vmin, vmax=vmax, value=value, step=0.5, size_hint_x=1, height=dp(36))
        sl.bind(value=lambda i, v: on_change(v))
        sl.bind(on_commit=lambda *a: self.end_edit())
        lbl = L(key, size=13, color="muted", fill=True, size_hint_x=None, width=dp(62))
        return hrow([lbl, sl], height=38, spacing=6), sl

    def _remember(self, hx):
        cur = [c for c in (APP.store.get("pdfe_colors", []) or []) if c.upper() != hx.upper()]
        APP.store.set("pdfe_colors", ([hx] + cur)[:8])

    def _recent(self):
        return list(APP.store.get("pdfe_colors", []) or [])

    def _color_row(self, current, on_pick):
        def custom():
            open_color_dialog(current, lambda hx: (self._remember(hx), on_pick(hx)))
        return pdfe_color_row(current, on_pick, custom, self._recent())

    def _hint(self, key):
        self.opts.add_widget(L(key, size=13, color="muted", wrap=True))

    def _build_opts(self):
        ob = self.opts
        ob.clear_widgets()
        t, sel = self.tool, self.sel
        if t == "pen":
            chips = ChipGroup([(k, T("pe_pen_" + k)) for k in ("pen", "ball", "pencil", "marker")], self.pen,
                              on_change=self._set_pen)
            ob.add_widget(chips)
            ob.add_widget(self._color_row(self.color, self._set_color))
            row, sl = self._slider("pe_size", 1, 40, self.pw, self._set_pw)
            self.preview = PDFEPreview()
            self.preview.set(self.pen, self.color, self.pw)
            ob.add_widget(hrow([row, self.preview], height=40, spacing=4))
        elif t == "mark":
            ob.add_widget(ChipGroup([(k, T("pe_mk_" + k)) for k in ("hl", "ul", "st")], self.mkind,
                                    on_change=self._set_mkind))
            ob.add_widget(self._color_row(self.mcolor, self._set_mcolor))
            self._hint("pe_hint_mark")
        elif t == "eraser":
            row, sl = self._slider("pe_size", 5, 60, self.erw, lambda v: setattr(self, "erw", v))
            ob.add_widget(row)
            ob.add_widget(Btn(key="pe_clear_page", icon="trash", variant="secondary", height_dp=42, font=13,
                              on_tap=self.clear_drawings))
        elif t == "image" and sel is None:
            self._hint("pe_hint_image")
            ob.add_widget(Btn(key="pe_add_image", icon="image", height_dp=44, font=14, on_tap=self.pick_image))
        elif t == "edit":
            if self.pending is not None:
                self._hint("pe_hint_edit2")
                ob.add_widget(hrow([Btn(key="pe_edit_do", icon="text", height_dp=44, font=14, on_tap=self.edit_pending),
                                    Btn(key="pe_delete_text", icon="trash", variant="danger", height_dp=44, font=14,
                                        on_tap=self.delete_pending)], height=44, spacing=8))
            else:
                self._hint("pe_hint_edit")
        elif sel is not None:
            self._sel_opts(sel)
        else:
            self._hint("pe_hint_text" if t == "text" else "pe_hint_select")
            if t == "text":
                ob.add_widget(Btn(key="pe_add_text", icon="plus", height_dp=46, font=14, on_tap=self.add_text_box))

    def _sel_opts(self, o):
        ob = self.opts
        items = [Btn(key="delete", icon="trash", variant="danger", height_dp=42, font=13, auto_w=True,
                     on_tap=lambda: self.remove_obj(self.sel))]
        if o["t"] == "t":
            box = InputBox(hint=T("pe_text_hint"), multiline=True, height_dp=74)
            box.input.text = o["s"]
            box.input.bind(text=lambda inst, v: self._live_text(v))        # what you type shows in the box on the page
            ob.add_widget(box)
            self._live_box = box
        if o["t"] == "i":
            items.insert(0, Btn(key="pe_add_image", icon="image", variant="secondary", height_dp=42, font=13,
                                auto_w=True, on_tap=self.pick_image))
        ob.add_widget(hrow(items, height=42, spacing=8))
        if o["t"] == "t":
            row, sl = self._slider("pe_size", 10, 140, o["z"], self._set_text_size)
            ob.add_widget(row)
        if o["t"] in ("t", "r", "s", "m"):
            ob.add_widget(self._color_row(o["c"], self._set_sel_color))

    # option callbacks
    def _set_mkind(self, v):
        self.mkind = v
        self.mcolor = PDFE_MARK_DEF[v]
        self._build_opts()

    def _set_mcolor(self, hx):
        self.mcolor = hx
        self._build_opts()

    def _set_pen(self, v):
        self.pen = v
        self._build_opts()

    def _set_color(self, hx):
        self.color = hx
        self._build_opts()

    def _set_pw(self, v):
        self.pw = v
        if getattr(self, "preview", None) is not None:
            self.preview.set(self.pen, self.color, self.pw)

    def _learn_bias(self, o):
        """You set the size of an edited text by hand: the next edits will start from that correction."""
        try:
            if o is not None and o["t"] == "t" and o.get("za"):
                APP.store.set("pdfe_size_bias", max(0.5, min(1.6, o["z"] / o["za"])), save=False)
                Clock.unschedule(self._save_bias)
                Clock.schedule_once(self._save_bias, 1.0)
        except Exception:
            traceback.print_exc()

    def _save_bias(self, dt):
        APP.store.save()

    def _set_text_size(self, v):
        o = self.sel
        if o is None or o["t"] != "t" or abs(o["z"] - v) < 0.01:
            return
        n = self.begin_edit(o)
        n["z"] = v
        self.tsize = v
        self._learn_bias(n)
        self.view.redraw()

    def _set_sel_color(self, hx):
        o = self.sel
        if o is None:
            return
        n = self.begin_edit(o)
        n["c"] = hx
        n.pop("_tx", None)
        if o["t"] == "t":
            self.tcolor = hx
        self.end_edit()
        self.view.redraw()
        self._build_opts()

    # ---- text
    def _text_dialog(self, title_key, initial, on_ok, on_cancel=None, body_key=None, pic=None):
        box = InputBox(hint=T("pe_text_hint"), multiline=True, height_dp=110)
        box.input.text = initial
        extra = [box]
        if pic is not None:                                  # the original text, as a picture, to read it while you type
            try:
                extra.insert(0, make_img(texture=pil_to_texture(pic), size_hint_y=None, height=dp(64)))
            except Exception:
                traceback.print_exc()
        Dialog(title=T(title_key), body=T(body_key) if body_key else "", extra=extra,
               buttons=[(T("cancel"), "secondary", on_cancel),
                        (T("ok"), "primary", lambda: guard(on_ok)(box.input.text))]).open()

    def _live_text(self, text):
        """Typing in the writing box: the text of the selected box on the page follows, letter by letter."""
        o = self.sel
        if o is None or o["t"] != "t" or o["s"] == text:
            return
        n = self.begin_edit(o)
        n["s"] = text
        self.view.redraw()

    def _drop_empty(self):
        """Text boxes that were left empty are not kept."""
        for lst in self.ann.values():
            lst[:] = [o for o in lst if not (o["t"] == "t" and not (o["s"] or "").strip())]
        if self.sel is not None and self.sel["t"] == "t" and not (self.sel["s"] or "").strip():
            self.sel = None

    def add_text_box(self):
        """The + button: an empty writing box appears in the middle of what is on screen; type in it, move it, resize it."""
        self._drop_empty()
        v = self.view
        try:
            cx, cy = v.to_page(v.x + v.width / 2.0, v.y + v.height / 2.0)
        except Exception:
            cx, cy = PDFE_W0 / 2.0, v.H / 2.0
        z = self.tsize
        w = PDFE_W0 * 0.6
        x = max(8.0, min(cx - w / 2.0, PDFE_W0 - w - 8.0))
        y = max(4.0, min(cy - z * 0.8, v.H - z * 1.8))
        self.add_obj({"t": "t", "s": "", "c": self.tcolor, "z": z, "x": x, "y": y, "w": w})

        def focus(dt):
            try:
                self._live_box.input.focus = True
            except Exception:
                pass
        Clock.schedule_once(focus, 0.25)

    def add_text_at(self, px, py):
        def ok(text):
            text = (text or "").rstrip()
            if not text.strip():
                return
            z = self.tsize
            nat = pdfe_text_width(text, z * PDFE_SC) / PDFE_SC + z * 0.4
            w = max(60.0, min(520.0, nat))
            x = max(8.0, min(px, PDFE_W0 - w - 8))
            y = max(4.0, min(py, self.view.H - z * 1.5))
            self.add_obj({"t": "t", "s": text, "c": self.tcolor, "z": z, "x": x, "y": y, "w": w})
        self._text_dialog("pe_text_title", "", ok)

    def edit_text(self):
        o = self.sel
        if o is None or o["t"] != "t":
            return

        def ok(text):
            text = (text or "").rstrip()
            if not text.strip():
                return
            n = self.begin_edit(o)
            n["s"] = text
            self.end_edit()
            self.view.redraw()
        self._text_dialog("pe_edit_text", o["s"], ok)

    def select_text(self, b):
        """The user touched / swept some old text: remember where, show the choices (edit / delete)."""
        self.pending = (b[0], b[1], b[2], b[3])
        self.sel = None
        self.view.redraw()
        self._build_opts()

    def _pending_colors(self):
        x0, y0, x1, y1 = self.pending
        bg, fg = (255, 255, 255), (0, 0, 0)
        if self.page_pil is not None:
            pic = self.det()
            k = pic.width / PDFE_W0
            bg, fg = pdfe_sample(pic, (x0 * k, y0 * k, x1 * k, y1 * k))
        return bg, fg

    def _erase_obj(self, bg):
        x0, y0, x1, y1 = self.pending
        self._serial += 1
        return {"t": "e", "c": pdfe_hex(bg), "x": x0, "y": y0, "w": x1 - x0, "h": y1 - y0, "_n": self._serial}

    def delete_pending(self):
        """Take the chosen text away (only its letters are painted over, so no box is left behind)."""
        if self.pending is None:
            return
        bg, _fg = self._pending_colors()
        base = self.det()
        erase = self._erase_obj(bg)
        if base is not None:
            self._tex_for(erase, base)
        self.push_undo()
        self.objs().append(erase)
        self.pending = None
        self.view.redraw()
        self._build_opts()

    def _line_ctx(self, box):
        """What stands on the line of `box`: the cell / page limits and the words on each side of it."""
        base = self.det()
        if base is None:
            return None
        y0, y1 = box[1], box[3]
        extra = []
        for o in self.objs():                       # text typed earlier on the same line is a neighbour too
            if o["t"] == "t":
                bx, by, bw, bh = self.bbox(o)
                if by < y1 and by + bh > y0:
                    extra.append((bx, bx + bw))
        return pdfe_line_ctx(base, box, extra)

    def _shift_typed(self, a, b, y0, y1, dx):
        """Typed text (and highlights) that stand between a and b on the line move along with the words they sit with."""
        lst = self.objs()
        for i, o in enumerate(lst):
            if o["t"] == "t":
                bx, by, bw, bh = self.bbox(o)
            elif o["t"] == "m":
                bx, by, bw, bh = o["x"], o["y"], o["w"], o["h"]
            else:
                continue
            if bx >= a - 1.5 and bx + bw <= b + 1.5 and by < y1 and by + bh > y0:
                n = dict(o)
                n["x"] = o["x"] + dx
                lst[i] = n

    def edit_pending(self):
        """Take the chosen text away and write new text in its place.  A longer text pushes the words beside it
        aside (as far as the cell / page allows); if there is still not enough room the new text gets smaller."""
        if self.pending is None:
            return
        x0, y0, x1, y1 = self.pending
        bg, fg = self._pending_colors()
        w, h = x1 - x0, y1 - y0
        fgx = pdfe_hex(fg)
        erase = self._erase_obj(bg)

        def ok(text):
            text = (text or "").rstrip()
            if not text.strip():
                return
            base = self.det()
            nl = text.count("\n") + 1
            z = max(10.0, min(140.0, h / nl * 0.82))
            rtl = has_arabic(text)
            ctx = self._line_ctx((x0, y0, x1, y1)) if nl == 1 and base is not None else None
            core = ctx.get("core") if ctx else None
            za = None
            th = 0.0
            if core and core[1] - core[0] > 3:               # same letter height as the text around it
                z = max(8.0, min(140.0, (core[1] - core[0]) / pdfe_ink_ratio()))
                if ctx.get("tall") or ctx.get("stroke"):     # then corrected until it MEASURES the same (height and weight)
                    z, th = pdfe_match_style(text, ctx.get("tall"), ctx.get("stroke"), z)
                za = z                                       # what the measuring says ...
                z = max(8.0, min(140.0, z * float(APP.store.get("pdfe_size_bias", 1.0) or 1.0)))   # ... and what you taught me

            def nat_w(zz):
                return pdfe_text_width(text, zz * PDFE_SC) / PDFE_SC + zz * 0.4
            nat = nat_w(z)
            dx, nb = 0.0, None
            if nl == 1 and base is not None and nat > w:
                if ctx is not None:
                    lim_l, lim_r = ctx["lim_l"], ctx["lim_r"]
                    nb = ctx["left"] if rtl else ctx["right"]          # the words in the way (Arabic grows to the left)
                    gap_min = max(5.0, 0.3 * h)                        # the normal space between two words
                    if rtl:
                        free = max(0.0, (x0 - nb[1] - gap_min) if nb else (x0 - lim_l))
                        room = max(0.0, nb[0] - lim_l) if nb else 0.0
                    else:
                        free = max(0.0, (nb[0] - x1 - gap_min) if nb else (lim_r - x1))
                        room = max(0.0, lim_r - nb[1]) if nb else 0.0
                    need = nat - w
                    sh = min(max(0.0, need - free), room)
                    avail = w + min(need, free) + sh
                    if nat > avail and avail > 4.0:                    # no more room anywhere: make the text smaller
                        z = max(8.0, z * avail / nat)
                        nat = nat_w(z)
                        need = max(0.0, nat - w)
                        sh = min(max(0.0, need - free), room)
                    if nb and sh > 0.5:
                        dx = -sh if rtl else sh
            ww = max(w, min(nat, PDFE_W0 - 6))
            x = (x1 - ww) if rtl else x0                               # Arabic grows to the left, like the old text
            x = max(3.0, min(x, PDFE_W0 - ww - 3))
            if base is not None:
                self._tex_for(erase, base)
            self.push_undo()
            lst = self.objs()
            lst.append(erase)
            if dx:
                pad = 0.2 * h
                self._serial += 1
                move = {"t": "g", "c": pdfe_hex(bg), "x": nb[0] - 1.5, "y": y0 - pad, "w": nb[1] - nb[0] + 3.0,
                        "h": h + 2 * pad, "dx": dx, "_n": self._serial}
                self._tex_for(move, base)
                lst.append(move)
                self._shift_typed(nb[0], nb[1], y0, y1, dx)
            ty = y0
            if core:                                         # and on the same height as the text around it
                try:
                    c2 = _pdfe_core(pdfe_text_pil(text, "#000000", z * PDFE_SC, ww * PDFE_SC, th * PDFE_SC).getchannel("A").point(
                        lambda v: 255 if v > 128 else 0))
                    if c2:
                        ty = max(0.0, (core[0] + core[1]) / 2.0 - (c2[0] + c2[1]) / 2.0 / PDFE_SC)
                except Exception:
                    traceback.print_exc()
            tobj = {"t": "t", "s": text, "c": fgx, "z": z, "x": x, "y": ty, "w": ww}
            if th:
                tobj["th"] = th
            if za:
                tobj["za"] = za                              # so a size you set by hand can teach the next edit
            lst.append(tobj)
            self.pending = None
            self.sel = tobj                                  # stays selected: its writing box + size are right there
            self._editing = None
            self.view.redraw()
            self._build_opts()
        self._text_dialog("pe_old_title", "", ok, body_key="pe_old_body")

    # ---- images
    def pick_image(self):
        APP.pick_files(self._img_picked, multiple=False)

    @guard
    def _img_picked(self, paths):
        if not paths:
            return
        try:
            tex, iw, ih = self.img_tex(paths[0])
        except Exception as e:
            APP.log_error(e)
            APP.feedback("error")
            APP.toast(T("pe_image_failed"), "error")
            return
        H = self.view.H
        w = PDFE_W0 * 0.4
        h = w * ih / float(max(1, iw))
        if h > H * 0.7:
            h = H * 0.7
            w = h * iw / float(max(1, ih))
        o = {"t": "i", "f": paths[0], "x": (PDFE_W0 - w) / 2.0, "y": max(0.0, (H - h) / 2.0), "w": w, "h": h}
        if self.tool not in ("select", "text", "image"):
            self.tool = "select"
            for k, b in self.tool_btns.items():
                b.set_active(k == "select")
        self.add_obj(o)

    # ---- closing / saving
    def dismiss(self, *a, **kw):
        if kw.get("force") or not self.dirty:
            return super().dismiss(*a, **kw)
        Dialog(title=T("pe_discard_q"), body=T("pe_discard_body"),
               buttons=[(T("pe_keep_editing"), "secondary", None),
                        (T("pe_discard"), "danger", lambda: super(PDFEditor, self).dismiss(force=True))]).open()

    def on_dismiss(self, *a):
        try:
            self.engine.close()
        except Exception:
            pass
        try:
            import shutil
            shutil.rmtree(self.dir, ignore_errors=True)
        except Exception:
            pass

    def _save(self):
        self._drop_empty()
        pages = sorted(i for i, o in self.ann.items() if o)
        if not pages:
            APP.feedback("error")
            APP.toast(T("pe_nochange"), "error")
            return
        ask_save_mode(T("pe_save_q"), T("pe_save_body", n=len(pages)),
                      lambda: self._export(False), lambda: self._export(True))

    def _export(self, replace):
        pages = sorted(i for i, o in self.ann.items() if o)
        ann = {i: list(self.ann[i]) for i in pages}
        sizes, src, eng, ew = list(self.sizes), self.path, self.engine, self.EXPORT_W
        stem = safe_name(os.path.splitext(os.path.basename(src))[0], "3edda")
        name = stem + "_edited.pdf"
        out = unique_path(tmp_dir(), stem + "_edited", ".pdf")
        folder = self.dir
        APP.busy_show(T("working"))

        def work():
            data = {}
            for n, i in enumerate(pages):
                Clock.schedule_once(lambda dt, n=n: APP.busy_text(T("pe_exporting", i=n + 1, n=len(pages))), 0)
                pic = os.path.join(folder, "x%d.jpg" % i)
                eng.call_sync(lambda i=i, pic=pic: eng.render(i, ew, pic))
                base = Image.open(pic)
                base.load()
                im = pdfe_composite(base.convert("RGB"), ann[i])
                data[i] = pdfe_page_pdf(im, sizes[i][0])
                PDFViewer._rm(pic)
            total = pdfe_build_pdf(src, out, data)
            pub = publish_file(out, name, "application/pdf", "pdf", APP.user_data_dir)
            state = delete_original_pdf(src) if replace else "kept"
            return pub, len(pages), total, state

        def done(res, err):
            APP.busy_hide()
            if err is not None or not res:
                if err is not None:
                    APP.save_failed(err)
                return
            self.dirty = False
            APP.feedback("success")
            APP.log_event("pdfedit", "%s · %s" % (name, T("pdf_pages", n=res[2])))
            self.dismiss(force=True)
            if self.on_saved:
                guard(self.on_saved)(res)
        run_bg(work, done)


class PDFEditScreen(_PdfOutMixin, ToolScreen):
    """Tool 9 entry: choose a PDF, the editor opens; the saved file is shown here."""
    bottom_pad = 40
    title_key = "tool_pdfedit"

    def build_body(self):
        b = self.body
        self.src = None
        self.info = None
        c = setting_card()
        c.add_widget(L("pe_intro", size=14, wrap=True))
        c.add_widget(L("pe_note", size=12.5, color="muted", wrap=True))
        b.add_widget(c)
        self.pick_btn = Btn(raw=T("pdfz_pick"), icon="plus", on_tap=self._pick)
        b.add_widget(self.pick_btn)
        self.file_box = BoxLayout(orientation="vertical", spacing=dp(8), size_hint_y=None)
        self.file_box.bind(minimum_height=self.file_box.setter("height"))
        b.add_widget(self.file_box)
        self.open_btn = Btn(key="pe_open", icon="pen", variant="secondary", on_tap=self._open_editor)
        self.open_btn.opacity = 0
        self.open_btn.disabled = True
        b.add_widget(self.open_btn)
        self.result_box = BoxLayout(orientation="vertical", spacing=dp(10), size_hint_y=None)
        self.result_box.bind(minimum_height=self.result_box.setter("height"))
        b.add_widget(self.result_box)
        self._render_file()

    @guard
    def _pick(self):
        APP.pick_pdfs(self._picked, multiple=False)

    @guard
    def _picked(self, paths):
        if not paths:
            return
        if not (HAS_PYPDF and HAS_PIL):
            APP.toast(T("need_pypdf"), "error", 4)
            return
        self.src = paths[0]
        self.info = None
        self.result_box.clear_widgets()
        self.pick_btn.set_text(T("pdfz_change"))
        self._render_file()
        p = self.src

        def done(res, err):
            if p != self.src:
                return
            self.info = res or (0, "bad")
            self._render_file()
            if self.info[1] == "ok" and self.info[0] > 0:
                self._open_editor()
            else:
                APP.feedback("error")
                APP.toast(T("pdf_enc") if self.info[1] == "encrypted" else T("pdf_bad"), "error")
        run_bg(lambda: pdf_info(p), done)

    def _render_file(self):
        self.file_box.clear_widgets()
        ok = bool(self.src and self.info and self.info[1] == "ok")
        self.open_btn.opacity = 1 if ok else 0
        self.open_btn.disabled = not ok
        if not self.src:
            self.file_box.add_widget(L("pdfz_none", size=14, color="muted", wrap=True))
            return
        row = RoundBox(bg=col("card"), radius=dp(18), size_hint_y=None, height=dp(76),
                       padding=[dp(12), dp(8)], spacing=dp(12))
        ic = RoundBox(bg=col("card_hi"), radius=dp(12), size_hint=(None, None), size=(dp(52), dp(52)), padding=dp(13))
        ic.add_widget(Icon("doc", "accent", 26))
        txt = BoxLayout(orientation="vertical", spacing=dp(1))
        txt.add_widget(L(raw=os.path.basename(self.src), size=14.5, bold=True, fill=True))
        try:
            meta = human_size(os.path.getsize(self.src))
        except Exception:
            meta = ""
        color = "muted"
        if self.info:
            pages, state = self.info
            if state == "ok":
                meta += "  ·  " + T("pdf_pages", n=pages)
            else:
                meta += "  ·  " + (T("pdf_enc_s") if state == "encrypted" else T("pdf_bad_s"))
                color = "warn"
        txt.add_widget(L(raw=meta, size=12, color=color, fill=True))
        for w in mirror([ic, txt]):
            row.add_widget(w)
        self.file_box.add_widget(row)

    @guard
    def _open_editor(self):
        if not self.src:
            return
        if not pdf_renderer_available():
            APP.feedback("error")
            APP.toast(T("pe_unsupported"), "error", 4)
            return
        PDFEditor(self.src, on_saved=self._saved).open()

    def _saved(self, res):
        pub, edited, total, state = res
        APP.toast(T("pe_done"), "ok")
        note, ncol = _orig_note(state)
        self._show_result(pub, "pe_done",
                          rows=[("pe_pages_edited", "%d / %d" % (edited, total), "accent")],
                          note=note, note_color=ncol)
        if state in ("deleted", "cache"):
            self.src = None
            self.info = None
            self.pick_btn.set_text(T("pdfz_pick"))
            self._render_file()

    def on_leave(self, *a):
        try:
            self.result_box.clear_widgets()
        except Exception:
            pass


# --------------------------------------------------------------------------
# Tool: text tools
# --------------------------------------------------------------------------
class PDFToolsScreen(ToolScreen):
    """One entry for all the PDF tools: Images to PDF, Compress PDF, Merge PDF."""
    title_key = "tool_pdftools"
    SUB_TOOLS = ("pdf", "pdfzip", "pdfmerge", "pdfsplit", "pdfedit")

    def build_body(self):
        self.body.spacing = dp(12)
        self.fill_cards()

    def fill_cards(self):
        self.body.clear_widgets()
        for tid in self.SUB_TOOLS:
            self.body.add_widget(ToolCard(TOOL_BY_ID[tid], wide=True))

    def on_pre_enter(self, *a):
        super().on_pre_enter(*a)
        self.fill_cards()                       # refresh the favourite hearts


# --------------------------------------------------------------------------
# Notes (saved text that you can come back to later)
# --------------------------------------------------------------------------
class Notes:
    """Notes live in one small JSON file inside the app folder: [{id, title, text, ts}]."""
    _items = None

    @classmethod
    def _path(cls):
        return os.path.join(APP.user_data_dir, "idda_notes.json")

    @classmethod
    def _load(cls):
        if cls._items is None:
            cls._items = []
            try:
                with open(cls._path(), "r", encoding="utf-8") as f:
                    data = json.load(f)
                if isinstance(data, list):
                    cls._items = [n for n in data if isinstance(n, dict) and n.get("id")]
            except Exception:
                pass
        return cls._items

    @classmethod
    def _write(cls):
        tmp = cls._path() + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(cls._load(), f, ensure_ascii=False)
        os.replace(tmp, cls._path())

    @classmethod
    def all(cls):
        return sorted(cls._load(), key=lambda n: n.get("ts", 0), reverse=True)

    @classmethod
    def get(cls, nid):
        for n in cls._load():
            if n.get("id") == nid:
                return n
        return None

    @classmethod
    def add(cls, title, text):
        n = {"id": "%d%04d" % (int(time.time() * 1000), random.randint(0, 9999)),
             "title": title, "text": text, "ts": time.time()}
        cls._load().append(n)
        try:
            cls._write()
        except Exception:
            cls._load().remove(n)
            raise
        return n

    @classmethod
    def update(cls, nid, **fields):
        n = cls.get(nid)
        if n is None:
            return None
        old = dict(n)
        n.update(fields)
        n["ts"] = time.time()
        try:
            cls._write()
        except Exception:
            n.clear()
            n.update(old)
            raise
        return n

    @classmethod
    def delete(cls, nid):
        n = cls.get(nid)
        if n is None:
            return
        items = cls._load()
        i = items.index(n)
        items.remove(n)
        try:
            cls._write()
        except Exception:
            items.insert(i, n)
            raise


def default_note_title(text):
    for line in (text or "").splitlines():
        line = line.strip()
        if line:
            return line[:40]
    return T("nt_untitled")


class NoteRow(Card):
    """One note in the list: title, a short preview and when it was last changed."""

    def __init__(self, note, on_tap, on_long, **kw):
        super().__init__(bg=col("card"), radius=dp(16), size_hint_y=None, height=dp(74),
                         padding=[dp(14), dp(8)], spacing=dp(12), **kw)
        self.note = note
        self._tap = on_tap
        self._on_long = on_long
        self._lp = False
        self._ev = None
        ib = AnchorLayout(size_hint_x=None, width=dp(30))
        ib.add_widget(Icon("text", "accent", 24))
        preview = " ".join((note.get("text") or "").split())[:70]
        txt = BoxLayout(orientation="vertical", spacing=dp(1))
        txt.add_widget(L(raw=note.get("title") or T("nt_untitled"), size=15, bold=True, fill=True))
        txt.add_widget(L(raw=preview, size=12.5, color="muted", fill=True))
        when = L(raw=rel_time(note.get("ts", 0)), size=11.5, color="muted", fill=True,
                 size_hint_x=None, width=dp(70), halign="left" if APP.rtl else "right")
        for w in mirror([ib, txt, when]):
            self.add_widget(w)

    def on_press(self):
        super().on_press()
        self._lp = False
        self._ev = Clock.schedule_once(self._long, 0.5)

    def on_state(self, inst, st):
        super().on_state(inst, st)
        if st == "normal" and self._ev:
            self._ev.cancel()
            self._ev = None

    @guard
    def _long(self, dt):
        self._ev = None
        self._lp = True
        APP.feedback("pop")
        self._on_long(self.note)

    def on_release(self):
        if self._ev:
            self._ev.cancel()
            self._ev = None
        if self._lp:
            self._lp = False
            return
        guard(self._tap)(self.note)


class NotesPicker(ModalView):
    """Full-screen list of the saved notes."""
    back_closes = True

    def __init__(self, screen, **kw):
        super().__init__(**_modal_kwargs(size_hint=(1, 1), background_color=rgba(C["bg"])))
        self.screen = screen
        self._q = ""
        root = RoundBox(orientation="vertical", bg=col("bg"), radius=0,
                        padding=[dp(14), dp(10) + top_inset_px(), dp(14), dp(10)], spacing=dp(10))
        close = IconBtn("close", "text", on_tap=self.dismiss)
        root.add_widget(hrow([close, L("nt_my", size=19, bold=True, fill=True)], height=48))
        self.search = InputBox(hint=T("nt_search"), height_dp=48)
        self.search.input.bind(text=lambda i, t: guard(self._on_query)(t))
        root.add_widget(self.search)
        root.add_widget(Btn(key="nt_new", icon="plus", variant="secondary", height_dp=46, font=14,
                            on_tap=self._new))
        self.info = L(raw="", size=12, color="muted", halign="left")
        root.add_widget(self.info)
        self.sv = ScrollView(do_scroll_x=False, bar_width=dp(3), bar_color=rgba(C["accent"], .5),
                             always_overscroll=False)
        self.box = BoxLayout(orientation="vertical", size_hint_y=None, spacing=dp(8),
                             padding=[0, 0, 0, dp(20)])
        self.box.bind(minimum_height=self.box.setter("height"))
        self.sv.add_widget(self.box)
        root.add_widget(self.sv)
        self.add_widget(root)
        self._render()

    def _on_query(self, text):
        self._q = text
        self._render()

    def _render(self, keep_scroll=False):
        y = self.sv.scroll_y
        self.box.clear_widgets()
        allnotes = Notes.all()
        q = norm_search(self._q.strip())
        items = [n for n in allnotes
                 if not q or q in norm_search((n.get("title") or "") + " " + (n.get("text") or ""))]
        self.info.raw = T("nt_count", n=len(allnotes)) if allnotes else ""
        if not items:
            self.box.add_widget(L("nt_none_found" if allnotes else "nt_empty", size=14, color="muted",
                                  wrap=True, halign="center"))
        else:
            if not q:
                self.box.add_widget(L("nt_hint", size=12, color="muted", wrap=True))
            for n in items:
                self.box.add_widget(NoteRow(n, self._open, self._actions))
        if keep_scroll:
            Clock.schedule_once(lambda dt: setattr(self.sv, "scroll_y", y), 0)
        else:
            self.sv.scroll_y = 1

    def _open(self, note):
        self.dismiss()
        self.screen.open_note(note["id"])

    def _new(self):
        self.dismiss()
        self.screen.new_note()

    # ---- long press: share / rename / save as a file / delete
    def _actions(self, note):
        holder = []

        def go(fn):
            def run():
                holder[0].dismiss()
                guard(fn)(note)
            return run
        extra = [Btn(key="share", icon="share", variant="secondary", height_dp=46, font=14, on_tap=go(self._share)),
                 Btn(key="rename", icon="text", variant="secondary", height_dp=46, font=14, on_tap=go(self._ask_rename)),
                 Btn(key="nt_export", icon="save", variant="secondary", height_dp=46, font=14, on_tap=go(self._export)),
                 Btn(key="delete", icon="trash", variant="danger", height_dp=46, font=14, on_tap=go(self._ask_delete))]
        dlg = Dialog(title=note.get("title") or T("nt_untitled"), extra=extra,
                     buttons=[(T("cancel"), "ghost", None)])
        holder.append(dlg)
        dlg.open()

    def _share(self, note):
        if not share_text(note.get("text") or ""):
            APP.toast(T("error"), "error")

    def _ask_rename(self, note):
        self.dismiss()
        self.screen.open_note(note["id"], focus_title=True)

    def _export(self, note):
        name = safe_name(note.get("title"), "note") + ".txt"
        tmp = os.path.join(tmp_dir(), name)
        with open(tmp, "w", encoding="utf-8") as f:
            f.write(note.get("text") or "")
        try:
            shown, _uri, _loc = publish_file(tmp, name, "text/plain", "file", APP.user_data_dir)
        except Exception as e:
            APP.save_failed(e)
            return
        APP.feedback("success")
        APP.toast(T("saved_to", path=shown), "ok")

    def _ask_delete(self, note):
        Dialog(title=T("nt_delete_q"), body=T("nt_delete_body", name=note.get("title") or T("nt_untitled")),
               buttons=[(T("cancel"), "secondary", None),
                        (T("delete"), "danger", lambda: guard(self._do_delete)(note))]).open()

    def _do_delete(self, note):
        try:
            Notes.delete(note["id"])
        except Exception as e:
            APP.save_failed(e)
            return
        if self.screen.note_id == note["id"]:
            self.screen.note_id = None
            self.screen._note_btn_state()
        APP.feedback("success")
        APP.toast(T("nt_deleted"), "ok")
        self._render(keep_scroll=True)


class TextScreen(ToolScreen):
    bottom_pad = 330
    title_key = "tool_text"

    def build_body(self):
        b = self.body
        self.undo_stack = []
        self._busy_set = False
        self.note_id = None                    # the saved note that is open in the box (None = a new text)
        self.title_box = InputBox(hint=T("nt_title_hint"), height_dp=52)    # the note's title, above the text
        b.add_widget(self.title_box)
        self.inp = InputBox(hint=T("tx_hint"), multiline=True, height_dp=230)
        self.inp.input.bind(text=self._on_text)
        b.add_widget(self.inp)
        self.stat = {}
        rows = []
        for group in ((("w", "tx_words"), ("c", "tx_chars"), ("d", "tx_digits")),
                      (("y", "tx_symbols"), ("n", "tx_spaces_n"), ("l", "tx_lines"))):
            cells = []
            for k, lab in group:
                box = RoundBox(orientation="vertical", bg=col("card"), radius=dp(16),
                               padding=[dp(6), dp(8)], spacing=dp(0))
                v = L(raw="0", size=20, bold=True, color="accent", h=30, halign="center")
                box.add_widget(v)
                box.add_widget(L(lab, size=11, color="muted", h=18, halign="center"))
                self.stat[k] = v
                cells.append(box)
            rows.append(hrow(cells, height=66, spacing=8))
        for r in rows:
            b.add_widget(r)
        b.add_widget(ActionChips([
            ("tx_dedupe", "sparkle", self._dedupe),
            ("tx_spaces", "sparkle", self._spaces),
            ("tx_empty_lines", "trash", self._empty),
            ("tx_sort", "up", self._sort),
            ("tx_upper", "text", self._upper),
            ("tx_lower", "text", self._lower),
            ("tx_tashkeel", "text", self._tashkeel),
        ]))
        b.add_widget(Btn(key="tx_copy", icon="copy", on_tap=self._copy))
        b.add_widget(hrow([Btn(key="tx_paste", icon="paste", variant="secondary", on_tap=self._paste, height_dp=48, font=14),
                           Btn(key="tx_undo", icon="undo", variant="secondary", on_tap=self._undo, height_dp=48, font=14),
                           Btn(key="tx_clear", icon="close", variant="danger", on_tap=self._clear, height_dp=48, font=14)],
                          height=48, spacing=8))
        # notes: save the text with a name and come back to it later
        self.note_btn = Btn(key="nt_save", icon="save", variant="secondary", on_tap=self._save_note, height_dp=48, font=14)
        b.add_widget(hrow([self.note_btn,
                           Btn(key="nt_my", icon="folder", variant="secondary", on_tap=self._open_notes,
                               height_dp=48, font=14)],
                          height=48, spacing=8))

    # ---- notes
    def _note_btn_state(self):
        self.note_btn.set_text(T("nt_update") if (self.note_id and Notes.get(self.note_id)) else T("nt_save"))

    @guard
    def _save_note(self):
        if not self._need_text():
            return
        title = (self.title_box.input.text or "").strip()[:60]
        existing = Notes.get(self.note_id) if self.note_id else None
        try:
            if existing:
                title = title or existing.get("title") or default_note_title(self.text)
                Notes.update(self.note_id, title=title, text=self.text)
                msg = T("nt_updated")
            else:
                title = title or default_note_title(self.text)
                self.note_id = Notes.add(title, self.text)["id"]
                msg = T("nt_saved")
        except Exception as e:
            APP.save_failed(e)
            return
        if self.title_box.input.text.strip() != title:
            self.title_box.input.text = title
        self._note_btn_state()
        APP.feedback("success")
        APP.toast(msg, "ok")
        APP.log_event("text", msg)

    @guard
    def _open_notes(self):
        try:
            self.inp.input.focus = False
        except Exception:
            pass
        NotesPicker(self).open()

    def _set_text_keep_undo(self, new):
        if self.text:
            self.undo_stack.append(self.text)
            del self.undo_stack[:-30]
        ti = self.inp.input
        ti.text = new
        try:
            ti.cancel_selection()
        except Exception:
            pass
        try:
            ti.cursor = (0, 0)
        except Exception:
            pass

    def open_note(self, nid, focus_title=False):
        n = Notes.get(nid)
        if not n:
            return
        self._set_text_keep_undo(n.get("text") or "")
        self.title_box.input.text = n.get("title") or ""
        self.note_id = nid
        self._note_btn_state()
        if focus_title:
            APP.toast(T("nt_rename_hint"))
            Clock.schedule_once(self._focus_title, 0.45)
        else:
            APP.toast(T("nt_opened", title=n.get("title") or T("nt_untitled")))

    def _focus_title(self, dt):
        try:
            ti = self.title_box.input
            ti.focus = True
            ti.select_all()
        except Exception:
            pass

    def new_note(self):
        self._set_text_keep_undo("")
        self.title_box.input.text = ""
        self.note_id = None
        self._note_btn_state()

    def on_pre_enter(self, *a):
        super().on_pre_enter(*a)
        self._note_btn_state()                 # the note may have been renamed or deleted meanwhile

    @property
    def text(self):
        return self.inp.input.text

    def _on_text(self, inst, t):
        w, c, d, y, n, l = text_stats(t)
        for k, v in (("w", w), ("c", c), ("d", d), ("y", y), ("n", n), ("l", l)):
            self.stat[k].raw = str(v)

    def _apply(self, new, msg=None):
        old = self.text
        if new == old:
            APP.toast(T("tx_no_change"))
            return
        self.undo_stack.append(old)
        del self.undo_stack[:-30]
        ti = self.inp.input
        ti.text = new
        try:
            ti.cancel_selection()
        except Exception:
            pass
        try:
            ti.cursor = (0, 0)
        except Exception:
            pass
        APP.feedback("success")
        APP.toast(msg or T("tx_done"), "ok")
        APP.log_event("text", (msg or T("tx_done")))

    def _need_text(self):
        if not self.text.strip():
            APP.feedback("error")
            APP.toast(T("tx_empty"), "error")
            return False
        return True

    @guard
    def _dedupe(self):
        if self._need_text():
            new, n = tx_dedupe(self.text)
            self._apply(new, T("tx_removed_n", n=n))

    @guard
    def _spaces(self):
        if self._need_text():
            self._apply(tx_clean_spaces(self.text))

    @guard
    def _empty(self):
        if self._need_text():
            self._apply(tx_remove_empty(self.text))

    @guard
    def _sort(self):
        if self._need_text():
            self._apply(tx_sort(self.text))

    @guard
    def _upper(self):
        if self._need_text():
            self._apply(self.text.upper())

    @guard
    def _lower(self):
        if self._need_text():
            self._apply(self.text.lower())

    @guard
    def _tashkeel(self):
        if self._need_text():
            self._apply(tx_strip_tashkeel(self.text))

    @guard
    def _copy(self):
        ti = self.inp.input
        # prefer the current selection; fall back to the whole text
        data = ""
        try:
            data = (ti.selection_text or "").replace("\x00", "")
        except Exception:
            data = ""
        if not data:
            data = self.text
        if not (data or "").strip():
            APP.feedback("error")
            APP.toast(T("tx_empty"), "error")
            return
        try:
            Clipboard.copy(data)
        except Exception:
            APP.feedback("error")
            APP.toast(T("error"), "error")
            return
        APP.feedback("success")
        APP.toast(T("copied"), "ok")
        APP.log_event("text", T("copied"))

    @guard
    def _paste(self):
        try:
            t = Clipboard.paste() or ""
        except Exception:
            t = ""
        if isinstance(t, bytes):
            t = t.decode("utf-8", "ignore")
        if not t:
            return
        ti = self.inp.input
        self.undo_stack.append(self.text)
        del self.undo_stack[:-30]
        ti.focus = True
        # replace selection if any, otherwise insert at cursor / append
        if ti.selection_text:
            try:
                ti.delete_selection()
            except Exception:
                pass
            try:
                ti.insert_text(t)
            except Exception:
                ti.text = (ti.text or "") + t
        else:
            try:
                if hasattr(ti, "insert_text"):
                    ti.insert_text(t)
                else:
                    ti.text = (ti.text or "") + t
            except Exception:
                ti.text = (ti.text or "") + t

    @guard
    def _undo(self):
        if self.undo_stack:
            self.inp.input.text = self.undo_stack.pop()
            try:
                self.inp.input.cancel_selection()
            except Exception:
                pass
        else:
            APP.toast(T("tx_no_change"))

    @guard
    def _clear(self):
        self.note_id = None                    # an emptied box starts a new note
        self.title_box.input.text = ""
        self._note_btn_state()
        if self.text:
            self.undo_stack.append(self.text)
            del self.undo_stack[:-30]
            self.inp.input.text = ""
            try:
                self.inp.input.cancel_selection()
            except Exception:
                pass


# --------------------------------------------------------------------------
# Tool: QR scanner
# --------------------------------------------------------------------------
class ScanFrame(Widget):
    """Camera picture + dimmed surround + corner brackets, ALL drawn by this one widget from
    ONE centre point. (Before, the camera was a separate widget that was rotated on its own and
    was even added on top of the brackets, so the frame never matched the picture.)
    The picture is cropped to fill the box ("cover"), turned by `rot` degrees and clipped to the
    rounded corners; the bright square in the middle is exactly where the code should be held."""
    HOLE = 0.62          # side of the square, as a fraction of the shorter side of the box

    def __init__(self, **kw):
        super().__init__(**kw)
        self.texture = None
        self.rot = 0
        r = dp(24)
        with self.canvas:
            StencilPush()
            Color(1, 1, 1, 1)
            self._mask = RoundedRectangle(radius=[r])
            StencilUse()
            self._img_col = Color(1, 1, 1, 0)
            PushMatrix()
            self._rot = Rotate(angle=0, origin=(0, 0))
            self._img = Rectangle()
            PopMatrix()
            self._dim_col = Color(0, 0, 0, 0)
            self._dim = [Rectangle() for _ in range(4)]
            Color(*rgba(C["accent"]))
            self._ln = [Line(width=dp(3), cap="round") for _ in range(4)]
            StencilUnUse()
            Color(1, 1, 1, 1)
            self._mask2 = RoundedRectangle(radius=[r])
            StencilPop()
        self.bind(pos=self.redraw, size=self.redraw)

    def set_texture(self, tex, rot):
        self.texture = tex
        self.rot = rot
        self.redraw()

    def redraw(self, *a):
        x, y, w, h = self.x, self.y, self.width, self.height
        if w < 4 or h < 4:
            return
        for m in (self._mask, self._mask2):
            m.pos = (x, y)
            m.size = (w, h)
        cx, cy = x + w / 2.0, y + h / 2.0
        tex = self.texture
        shown = False
        if tex is not None:
            try:
                tw, th = tex.size
            except Exception:
                tw = th = 0
            if tw > 1 and th > 1:
                swap = (int(self.rot) % 180) == 90
                cw, ch = (th, tw) if swap else (tw, th)
                sc = max(w / float(cw), h / float(ch))        # "cover": fill the whole box
                iw, ih = tw * sc, th * sc
                self._img.texture = tex
                self._img.pos = (cx - iw / 2.0, cy - ih / 2.0)
                self._img.size = (iw, ih)
                self._rot.origin = (cx, cy)
                self._rot.angle = self.rot
                shown = True
        self._img_col.a = 1 if shown else 0
        self._dim_col.a = 0.5 if shown else 0
        # the clear square in the exact centre
        s = min(w, h) * self.HOLE
        x0, y0, x1, y1 = cx - s / 2.0, cy - s / 2.0, cx + s / 2.0, cy + s / 2.0
        self._dim[0].pos, self._dim[0].size = (x, y1), (w, y + h - y1)         # above
        self._dim[1].pos, self._dim[1].size = (x, y), (w, y0 - y)              # below
        self._dim[2].pos, self._dim[2].size = (x, y0), (x0 - x, s)             # left
        self._dim[3].pos, self._dim[3].size = (x1, y0), (x + w - x1, s)        # right
        k = s * 0.2
        self._ln[0].points = [x0, y0 + k, x0, y0, x0 + k, y0]
        self._ln[1].points = [x1 - k, y0, x1, y0, x1, y0 + k]
        self._ln[2].points = [x0, y1 - k, x0, y1, x0 + k, y1]
        self._ln[3].points = [x1 - k, y1, x1, y1, x1, y1 - k]


class ScanScreen(ToolScreen):
    title_key = "tool_scan"

    def build_body(self):
        b = self.body
        self.cam = None
        self.scanning = False
        self.busy = False
        self.flip_first = False
        self._tick_ev = None
        r = APP.store.get("cam_rot2")
        if r is None or int(r) < 0:
            r = 270 if platform == "android" else 0       # Android camera pictures arrive turned sideways
        self.rot = int(r) % 360
        self._pv_ev = None
        self.view = FloatLayout(size_hint_y=None, height=dp(340))
        with self.view.canvas.before:
            Color(*rgba("#0A121A"))
            self._vbg = RoundedRectangle(pos=self.view.pos, size=self.view.size, radius=[dp(24)])
        self.view.bind(pos=self._lay, size=self._lay)
        self.frame = ScanFrame(size_hint=(1, 1), pos_hint={"x": 0, "y": 0})
        self.view.add_widget(self.frame)
        self.hint = L("sc_hint", size=13.5, color="white", wrap=True, halign="center",
                      size_hint=(1, None), pos_hint={"x": 0, "y": 0.02})
        self.view.add_widget(self.hint)
        b.add_widget(self.view)
        b.add_widget(Btn(key="sc_capture", icon="camera", on_tap=self._capture, height_dp=52, font=15))
        self.rot_btn = Btn(key="sc_rotate", icon="rotate", variant="secondary", on_tap=self._rotate,
                           height_dp=48, font=13.5)
        b.add_widget(hrow([Btn(key="sc_gallery", icon="image", variant="secondary", on_tap=self._gallery,
                               height_dp=48, font=13.5),
                           self.rot_btn], height=48, spacing=8))
        self.result = BoxLayout(orientation="vertical", spacing=dp(12), size_hint_y=None)
        self.result.bind(minimum_height=self.result.setter("height"))
        b.add_widget(self.result)

    # ---- camera plumbing
    def _lay(self, *a):
        self._vbg.pos = self.view.pos
        self._vbg.size = self.view.size

    @guard
    def _preview(self, dt):
        """Copy the newest camera picture into the frame widget (it draws picture + brackets)."""
        cam = self.cam
        if cam is None:
            return
        try:
            self.frame.set_texture(cam.texture, self.rot)
        except Exception:
            pass

    def _has_plyer_camera(self):
        if platform != "android":
            return False
        try:
            from plyer import camera  # noqa: F401
            return True
        except Exception:
            return False

    def on_enter(self, *a):
        self._start()

    def on_leave(self, *a):
        self._stop()

    def _start(self):
        self.result.clear_widgets()
        if not can_decode_qr():
            self.hint.key = "sc_no_decoder"
            self.hint.pos_hint = {"x": 0, "center_y": 0.5}
            self.frame.opacity = 0               # no frame on top of the message
            self.rot_btn.disabled = True
            return
        self.frame.opacity = 1
        self.hint.pos_hint = {"x": 0, "y": 0.02}
        self.hint.key = "sc_hint"
        self.rot_btn.disabled = False
        self._gen = getattr(self, "_gen", 0) + 1
        self._cam_tries = 0
        gen = self._gen
        ensure_camera_permission(lambda ok: self._perm_done(ok, gen))

    def _perm_done(self, ok, gen):
        if gen != getattr(self, "_gen", 0) or self.manager is None or self.manager.current != self.name:
            return                                   # the user already left this screen
        if not ok:
            self.hint.key = "sc_no_perm"
            self.hint.pos_hint = {"x": 0, "center_y": 0.5}
            self.frame.opacity = 0
            self.rot_btn.disabled = True
            return
        self._open_camera()

    def _open_camera(self):
        try:
            from kivy.uix.camera import Camera
            # The Camera object only supplies pictures (self.cam.texture). It is NOT put on screen:
            # ScanFrame draws it, so picture, dimming and brackets always share one centre.
            self.cam = Camera(index=0, resolution=(640, 480), play=True)
            self.frame.set_texture(None, self.rot)
            self._pv_ev = Clock.schedule_interval(self._preview, 1 / 30.0)
            self.scanning = True
            self._tick_ev = Clock.schedule_interval(self._tick, 0.4)
            gen = self._gen
            Clock.schedule_once(lambda dt: self._cam_watch(gen), 3.0)
        except Exception:
            self.cam = None
            self.hint.key = "sc_no_camera"
            self.hint.pos_hint = {"x": 0, "center_y": 0.5}
            self.frame.opacity = 0
            self.rot_btn.disabled = True

    def _cam_watch(self, gen):
        """No picture 3 seconds after opening (slow phones, permission just granted): open it once more."""
        if gen != getattr(self, "_gen", 0) or self.cam is None or self.cam.texture:
            return
        if self._cam_tries >= 2:
            self._stop()
            self.hint.key = "sc_no_camera"
            self.hint.pos_hint = {"x": 0, "center_y": 0.5}
            self.frame.opacity = 0
            self.rot_btn.disabled = True
            return
        self._cam_tries += 1
        tries = self._cam_tries
        self._stop()
        self._cam_tries = tries
        self._gen = gen
        self._open_camera()

    def _stop(self):
        self._gen = getattr(self, "_gen", 0) + 1       # answers that arrive late are ignored
        self.scanning = False
        if self._tick_ev:
            self._tick_ev.cancel()
            self._tick_ev = None
        if self._pv_ev:
            self._pv_ev.cancel()
            self._pv_ev = None
        if self.cam is not None:
            try:
                self.cam.play = False
            except Exception:
                pass
            self.cam = None
        try:
            self.frame.set_texture(None, self.rot)
        except Exception:
            pass

    @guard
    def _rotate(self):
        self.rot = (self.rot + 90) % 360
        APP.store.set("cam_rot2", self.rot)
        self.frame.set_texture(self.frame.texture, self.rot)

    @guard
    def _capture(self):
        """Capture button: decode the live frame now (or use the system camera)."""
        if not can_decode_qr():
            APP.feedback("error")
            APP.toast(T("sc_no_decoder"), "error")
            return
        if self.cam is not None and self.cam.texture:
            self.busy = False
            self._tick(0, manual=True)
        elif self._has_plyer_camera():
            self._photo()
        else:
            self._start()                            # camera not open yet: try again

    @guard
    def _tick(self, dt, manual=False):
        if self.cam is None or not self.cam.texture:
            return
        if not manual and (not self.scanning or self.busy):
            return
        tex = self.cam.texture
        try:
            pixels, size = tex.pixels, tex.size
        except Exception:
            return
        self.busy = True
        flip_first = self.flip_first

        def work():
            if cv2 is not None and np is not None:
                arr = np.frombuffer(pixels, dtype=np.uint8).reshape(size[1], size[0], 4)
                gray = cv2.cvtColor(arr, cv2.COLOR_RGBA2GRAY)
                flipped = cv2.flip(gray, 0)
                seq = [(flipped, True), (gray, False)] if flip_first else [(gray, False), (flipped, True)]
                for g, fl in seq:
                    r = decode_qr_gray(g)
                    if r:
                        return r, fl
                return None
            img = Image.frombytes("RGBA", tuple(size), pixels).convert("RGB")
            r = decode_qr_pil(img)              # the built-in reader also reads mirrored / flipped codes
            return (r, False) if r else None

        def done(res, err):
            self.busy = False
            if res and (self.scanning or manual):
                text, flipped = res
                self.flip_first = bool(flipped)
                self._found(text)
            elif manual:
                APP.feedback("error")
                APP.toast(T("sc_not_found"), "error")
        run_bg(work, done)

    # ---- other sources
    @guard
    def _gallery(self):
        APP.pick_files(self._from_files, multiple=False)

    @guard
    def _from_files(self, paths):
        if paths:
            self._decode_path(paths[0])

    def _decode_path(self, path):
        if not can_decode_qr():
            APP.toast(T("sc_no_decoder"), "error")
            return
        APP.busy_show(T("working"))

        def work():
            with Image.open(path) as im0:
                try:
                    im0.draft("RGB", (2400, 2400))      # cheap downscale for huge JPEGs
                except Exception:
                    pass
                im0.load()
                im = im0
            return decode_qr_pil(im)

        def done(res, err):
            APP.busy_hide()
            if res:
                self._found(res)
            else:
                APP.feedback("error")
                APP.toast(T("sc_not_found"), "error")
        run_bg(work, done)

    @guard
    def _photo(self):
        from plyer import camera
        target = os.path.join(APP.user_data_dir, "idda_scan_photo.jpg")
        camera.take_picture(filename=target,
                            on_complete=lambda p: Clock.schedule_once(lambda dt: self._decode_path(p or target), 0))

    # ---- results
    def _found(self, text):
        self.scanning = False
        if self.cam is not None:
            try:
                self.cam.play = False
            except Exception:
                pass
        APP.feedback("success")
        if APP.store.get("vibrate"):
            vibrate_ms(40)
        info = parse_qr(text)
        APP.log_event("scan", T("kind_" + info["kind"]) + ": " + info["raw"][:60].replace("\n", " "))
        self._show(info)

    def _show(self, info):
        self.result.clear_widgets()
        card = setting_card()
        kind_text = T("kind_" + info["kind"])
        badge_w = TextEngine.measure(kind_text, True, sp(12.5)) + dp(24)
        badge = RoundBox(bg=col("accent"), radius=dp(10), size_hint=(None, None),
                         size=(badge_w, dp(26)), padding=[dp(4), 0])
        badge.add_widget(L(raw=kind_text, size=12.5, bold=True, color="on_acc", fill=True, halign="center"))
        card.add_widget(hrow([Icon("check", "ok", 22), L("sc_found", size=16, bold=True, fill=True), badge],
                             height=30, spacing=10))
        if info["kind"] == "wifi":
            for lk, v in info["fields"]:
                if lk == "sc_pass" and not v:
                    continue
                card.add_widget(hrow([L(lk, size=13, color="muted", fill=True),
                                      L(raw=v, size=14.5, bold=True, fill=True, halign="left" if not APP.rtl else "right")],
                                     height=26))
        else:
            box = RoundBox(bg=col("bg"), radius=dp(14), padding=dp(12), size_hint_y=None)
            lbl = L(raw=info["raw"][:1500], size=14, wrap=True, halign="left")
            box.add_widget(lbl)
            lbl.bind(height=lambda w, h: setattr(box, "height", h + dp(24)))
            box.height = lbl.height + dp(24)
            card.add_widget(box)
        actions = self._actions(info)
        for row in actions:
            card.add_widget(row)
        card.add_widget(Btn(key="sc_scan_again", icon="rotate", variant="ghost", on_tap=self._again,
                            height_dp=46, font=14))
        self.result.add_widget(card)

    def _actions(self, info):
        raw, kind, act = info["raw"], info["kind"], info["action"]
        main = []
        if act == "url":
            main.append(Btn(key="sc_open_link", icon="link", on_tap=lambda: self._confirm_open(info["value"]),
                            height_dp=48, font=14))
        elif act == "call":
            main.append(Btn(key="sc_call", icon="phone", on_tap=lambda: open_uri("tel:" + info["value"]),
                            height_dp=48, font=14))
        elif act == "mail":
            main.append(Btn(key="sc_mail", icon="mail", on_tap=lambda: open_uri("mailto:" + info["value"]),
                            height_dp=48, font=14))
        elif act == "map":
            main.append(Btn(key="sc_map", icon="link", on_tap=lambda: open_uri("geo:" + info["value"]),
                            height_dp=48, font=14))
        elif act == "sms":
            main.append(Btn(key="sc_mail", icon="mail", on_tap=lambda: open_uri("sms:" + info["value"]),
                            height_dp=48, font=14))
        elif act == "wifi" and info["value"]:
            main.append(Btn(key="sc_copy_pass", icon="copy", on_tap=lambda: self._copy(info["value"]),
                            height_dp=48, font=14))
        rows = []
        if main:
            rows.append(hrow(main, height=48, spacing=8))
        rows.append(hrow([Btn(key="copy", icon="copy", variant="secondary", on_tap=lambda: self._copy(raw),
                              height_dp=46, font=14),
                          Btn(key="share", icon="share", variant="secondary", on_tap=lambda: self._share(raw),
                              height_dp=46, font=14)], height=46, spacing=8))
        return rows

    @guard
    def _copy(self, text):
        Clipboard.copy(text)
        APP.feedback("success")
        APP.toast(T("copied"), "ok")

    @guard
    def _share(self, text):
        if not share_text(text):
            Clipboard.copy(text)
            APP.toast(T("copied"), "ok")

    @guard
    def _confirm_open(self, url):
        a = analyze_url(url)
        if a["blocked"]:
            APP.feedback("error")
            Dialog(title=T("sc_confirm_title"), body=T("sc_blocked"),
                   buttons=[(T("close"), "secondary", None)]).open()
            return
        extra = [hrow([L("sc_domain", size=12.5, color="muted", fill=True,
                         size_hint_x=None, width=dp(70)),
                       L(raw=a["host"], size=17, bold=True, color="accent", fill=True,
                         halign="left" if not APP.rtl else "right")], height=30, spacing=8),
                 L(raw=a["url"][:300], size=12.5, color="muted", wrap=True, halign="left")]
        if a["warnings"]:
            for k in a["warnings"]:
                extra.append(hrow([Icon("warn", "warn", 18), L(k, size=13, color="warn", wrap=True,
                                                               size_hint_x=1)], spacing=8,
                                  height=30))
        else:
            extra.append(L("sc_safe", size=13, color="ok", wrap=True))
        Dialog(title=T("sc_confirm_title"), body=T("sc_confirm_msg"), extra=extra,
               buttons=[(T("cancel"), "secondary", None),
                        (T("open"), "danger" if a["warnings"] else "primary",
                         lambda: self._do_open(a["url"]))]).open()

    @guard
    def _do_open(self, url):
        if not open_uri(url):
            APP.toast(T("open_failed"), "error")

    @guard
    def _again(self):
        self.result.clear_widgets()
        if self.cam is not None:
            try:
                self.cam.play = True
            except Exception:
                pass
            self.scanning = True
        else:
            self._start()


# --------------------------------------------------------------------------
# Bottom navigation
# --------------------------------------------------------------------------
class NavItem(Tappable, BoxLayout):
    def __init__(self, name, **kw):
        super().__init__(orientation="vertical", padding=[0, dp(10), 0, dp(6)], spacing=dp(4), **kw)
        self.sfx = "nav"
        self.name = name
        self.icon = Icon(TAB_ICONS[name], "muted", 27)
        top = AnchorLayout(anchor_x="center", anchor_y="center")
        top.add_widget(self.icon)
        self.dot = RoundBox(bg=(0, 0, 0, 0), radius=dp(2), size_hint=(None, None), size=(dp(18), dp(4)))
        bot = AnchorLayout(anchor_x="center", anchor_y="center", size_hint_y=None, height=dp(6))
        bot.add_widget(self.dot)
        self.add_widget(top)
        self.add_widget(bot)

    def set_active(self, on):
        name = TAB_ICONS[self.name]
        if on and name == "heart":
            name = "heart_fill"
        self.icon.set_icon(name, "accent" if on else "muted")
        self.dot.bg = col("accent") if on else (0, 0, 0, 0)

    def on_release(self):
        guard(APP.switch_tab)(self.name)


class NavBar(BoxLayout):
    def __init__(self, **kw):
        super().__init__(orientation="vertical", size_hint_y=None, height=dp(71), **kw)
        self.add_widget(RoundBox(bg=col("line"), radius=0, size_hint_y=None, height=dp(1)))
        row = BoxLayout(orientation="horizontal", padding=[dp(10), 0])
        self.items = {}
        its = []
        for n in TABS:
            it = NavItem(n)
            self.items[n] = it
            its.append(it)
        for w in mirror(its):
            row.add_widget(w)
        self.add_widget(row)
        self._h = dp(71)

    def set_active(self, name):
        for n, it in self.items.items():
            it.set_active(n == name)

    def show(self, flag):
        self.height = self._h if flag else 0
        self.opacity = 1 if flag else 0
        self.disabled = not flag


# --------------------------------------------------------------------------
# Application
# --------------------------------------------------------------------------
class IddaApp(App):
    title = "3edda"

    def __init__(self, **kw):
        global APP
        super().__init__(**kw)
        APP = self
        self.ar = True
        self.rtl = True
        self.sounds = {}
        self._exit_t = 0
        self._busy = None

    # ---- lifecycle
    def build(self):
        self.store = Store(self.user_data_dir)
        lang = self.store.get("lang")
        I18N.lang = lang if lang in ("ar", "en") else "ar"
        self.ar = (I18N.lang == "ar")
        # Keep the whole UI laid out in the Arabic (RTL) style even when
        # the user switches the language to English — icons and rows stay put.
        self.rtl = True
        self._apply_theme()
        if platform not in ("android", "ios"):
            Window.size = (400, 820)
        clean_tmp()
        self._reload_fonts()
        self._init_sfx()
        Window.bind(on_keyboard=self._on_key)
        Window.bind(on_touch_up=self._kb_dismiss)
        TextGestures.bind()
        self.holder = BoxLayout()
        if not HAS_PIL:
            self.holder.add_widget(Label(text="3edda", color=(1, 1, 1, 1)))
            return self.holder
        self._build_ui("home")
        Clock.schedule_once(self._late_init, 0.7)
        Clock.schedule_once(guard(self._start_font_merge), 1.2)
        return self.holder

    def _font_dirs(self):
        dirs = []
        try:
            here = os.path.dirname(os.path.abspath(__file__))
            dirs += [here, os.path.join(here, "fonts")]
        except Exception:
            pass
        dirs += [os.getcwd(), os.path.join(storage_root(), "3edda"), os.path.join(storage_root(), "idda"),
                 os.path.join(storage_root(), "Download"), os.path.join(storage_root(), "Download", "fonts"),
                 os.path.join(self.user_data_dir, "fonts")]
        # any folder directly inside the storage that holds font files (e.g. a folder named with Arabic letters)
        try:
            _root = storage_root()
            for _n in sorted(os.listdir(_root)):
                if _n == "Android" or _n.startswith("."):
                    continue
                _d = os.path.join(_root, _n)
                try:
                    if os.path.isdir(_d) and any(f.lower().endswith((".ttf", ".otf")) for f in os.listdir(_d)):
                        dirs.append(_d)
                except Exception:
                    pass
        except Exception:
            pass
        out = []
        for d in dirs:
            if d not in out and os.path.isdir(d):
                out.append(d)
        return out

    def _reload_fonts(self):
        folder = os.path.join(self.user_data_dir, "fonts")
        try:
            os.makedirs(folder, exist_ok=True)
        except Exception:
            pass
        cmap_cache_load(folder)
        info = find_fonts(self._font_dirs())
        self._font_info = info
        self._font_folder = folder
        merged = None
        if info.get("reg") and info.get("fallbacks"):
            merged = load_merged_fonts(info, folder)
        TextEngine.setup(merged or info, True)
        cmap_cache_save()
        self._need_merge = bool(info.get("reg") and info.get("fallbacks") and not merged and HAS_FT
                                and self.store.get("font_fail", "") != font_signature(info))

    def _start_font_merge(self, dt=0):
        if not getattr(self, "_need_merge", False):
            return
        self._need_merge = False
        info, folder = self._font_info, self._font_folder
        run_bg(lambda: build_merged_fonts(info, folder), self._font_merged)

    def _font_merged(self, res, err):
        if not res:
            try:
                self.store.set("font_fail", font_signature(self._font_info))
            except Exception:
                pass
            return
        # The new font is saved for the next start. Only switch to it right now when the user is on
        # a main tab (rebuilding would wipe a half-typed text or an open tool).
        if self.sm.current in TABS:
            TextEngine.setup(res, True)
            self.rebuild(self.sm.current)

    def _init_sfx(self):
        try:
            from kivy.core.audio import SoundLoader
            paths = ensure_sfx(os.path.join(self.user_data_dir, "sfx"))
            for name, p in paths.items():
                s = SoundLoader.load(p)
                if s:
                    self.sounds[name] = s
        except Exception:
            pass

    def _late_init(self, dt):
        # Permissions are requested only when the user actually opens the
        # camera (Scan) or the file picker — not on every cold start.
        pass

    # ---- building the UI
    def _build_ui(self, start="home"):
        for old in list(getattr(self, "screens", {}).values()):
            try:
                if hasattr(old, "_stop"):
                    old._stop()
            except Exception:
                pass
        self.holder.clear_widgets()
        root = BoxLayout(orientation="vertical")
        self.sm = ScreenManager(transition=SlideTransition(duration=0.2))
        self.nav = NavBar()
        self.screens = {}
        inset = top_inset_px()
        if inset:
            root.add_widget(Widget(size_hint_y=None, height=inset))
        root.add_widget(self.sm)
        root.add_widget(self.nav)
        self.holder.add_widget(root)
        self.stack = [start]
        scr = self._screen(start)
        self.sm.current = start
        self.nav.show(scr.show_nav)
        self.nav.set_active(start if start in TABS else None)

    def _screen(self, name):
        if name in self.screens:
            return self.screens[name]
        factories = {
            "home": HomeScreen, "history": lambda: HistoryScreen("history"),
            "favorites": lambda: FavoritesScreen("favorites"),
            "settings": lambda: SettingsScreen("settings"),
            "qr": lambda: QRCreateScreen("qr"), "compress": lambda: CompressScreen("compress"),
            "pdf": lambda: PDFScreen("pdf"), "text": lambda: TextScreen("text"),
            "scan": lambda: ScanScreen("scan"),
            "pdfzip": lambda: PDFZipScreen("pdfzip"), "pdftools": lambda: PDFToolsScreen("pdftools"), "pdfmerge": lambda: PDFMergeScreen("pdfmerge"),
            "pdfsplit": lambda: PDFSplitScreen("pdfsplit"), "pdfedit": lambda: PDFEditScreen("pdfedit"),
        }
        scr = factories[name]()
        self.screens[name] = scr
        self.sm.add_widget(scr)
        return scr

    def rebuild(self, start="home"):
        Clock.schedule_once(guard(lambda dt: self._build_ui(start)), 0.12)

    # ---- navigation
    def _direction(self, forward):
        return "left" if (forward != self.rtl) else "right"

    def go(self, name, forward=True):
        scr = self._screen(name)
        if name == self.sm.current:
            return
        self.sm.transition.direction = self._direction(forward)
        self.sm.current = name
        self.nav.show(scr.show_nav)
        self.nav.set_active(name if name in TABS else None)

    def open_tool(self, tid):
        self.stack.append(tid)
        self.go(tid, True)

    def switch_tab(self, name):
        cur = self.sm.current
        if cur == name:
            return
        fwd = (TABS.index(name) > TABS.index(cur)) if cur in TABS else True
        self.stack = [name]
        self.go(name, fwd)

    def back(self):
        if len(self.stack) > 1:
            self.stack.pop()
            self.go(self.stack[-1], False)
        elif self.sm.current != "home":
            self.stack = ["home"]
            self.go("home", False)
        else:
            now = time.time()
            if now - self._exit_t < 2.0:
                self.stop()
            else:
                self._exit_t = now
                self.toast(T("exit_again"))

    @staticmethod
    def _hit(widget, touch):
        """Is the touch (window coordinates) over `widget`? Works inside ScrollViews."""
        try:
            wx, wy = widget.to_window(widget.x, widget.y)
            return wx <= touch.x <= wx + widget.width and wy <= touch.y <= wy + widget.height
        except Exception:
            return widget.collide_point(*touch.pos)

    def _kb_dismiss(self, window, touch):
        ti = TInput.active
        if ti is None or not ti.focus:
            return False
        try:
            tapped = math.hypot(touch.x - touch.ox, touch.y - touch.oy) < dp(14)
            if not tapped or self._hit(ti, touch):
                return False
            if EditMenu.cur is not None and self._hit(EditMenu.cur, touch):
                return False                      # tapping the paste / select-all menu keeps focus
            # cursor / selection handles and the copy-paste bubble belong to the input
            for h in tuple(getattr(ti, "_own_hs", None) or ()):
                try:
                    if h.parent is not None and h.opacity > 0.5 and h.collide_point(*touch.pos):
                        return False
                except Exception:
                    pass
            if getattr(ti, "_dg", None):
                return False                      # a selection handle is being dragged
            Clock.schedule_once(lambda dt: self._kb_close(ti), 0.08)
        except Exception:
            pass
        return False

    def _kb_close(self, ti):
        if TInput.active is ti and ti.focus:
            ti.focus = False

    def _on_key(self, window, key, *a):
        if key == 27:
            top = None
            for w in Window.children:               # first ModalView = the one on top
                if isinstance(w, ModalView):
                    top = w
                    break
            if top is not None and getattr(top, "back_closes", False):
                top.dismiss()                       # back closes a picker / notes list instead of leaving the screen
                return True
            guard(self.back)()
            return True
        return False

    # ---- settings / state
    def set_lang(self, lang):
        if lang == I18N.lang:
            return
        self.store.set("lang", lang)
        I18N.lang = lang
        self.ar = (lang == "ar")
        # Layout direction stays RTL (Arabic system) so icon positions never jump
        self.rtl = True
        self.rebuild("settings")

    def _apply_theme(self):
        apply_theme(self.store.get("theme"))
        Window.clearcolor = rgba(C["bg"])

    def _swap_ui(self, start, bg, before=None):
        """Change the whole UI without a visible mix of old and new colours:
        fade a flat veil (the new background colour) over the screen, rebuild underneath, fade it out."""
        try:
            from kivy.animation import Animation
            veil = _Veil(bg)
            Window.add_widget(veil)
        except Exception:
            if before:
                guard(before)()
            self.rebuild(start)
            return

        def covered(*a):
            try:
                if before:
                    before()
                self._build_ui(start)
            except Exception as e:
                try:
                    self.log_error(e)
                except Exception:
                    pass

            def reveal(dt):
                def gone(*b):
                    try:
                        Window.unbind(size=veil._fit)
                        Window.remove_widget(veil)
                    except Exception:
                        pass
                an = Animation(a=0, duration=0.22, t="out_quad")
                an.bind(on_complete=gone)
                an.start(veil)
            Clock.schedule_once(reveal, 0.06)
        an = Animation(a=1, duration=0.14, t="in_quad")
        an.bind(on_complete=lambda *b: Clock.schedule_once(covered, 0))
        an.start(veil)

    def set_theme(self, mode):
        if mode not in ("system", "light", "dark") or mode == self.store.get("theme"):
            return
        self.store.set("theme", mode)
        target = resolve_theme(mode)
        bg = rgba((C_LIGHT if target == "light" else C_DARK)["bg"])
        self._swap_ui("settings", bg, self._apply_theme)         # colours change only while the veil covers

    def on_resume(self):
        """Back from the background: follow the phone's dark/light switch when "same as device" is on."""
        try:
            if self.store.get("theme") == "system" and HAS_PIL and self.sm.current in TABS:
                if (resolve_theme("system") == "light") != IS_LIGHT:
                    target = resolve_theme("system")
                    bg = rgba((C_LIGHT if target == "light" else C_DARK)["bg"])
                    self._swap_ui(self.sm.current, bg, self._apply_theme)
        except Exception:
            pass
        return True

    def toggle_fav(self, tid):
        now = time.time()
        if tid == getattr(self, "_fav_id", None) and now - getattr(self, "_fav_t", 0) < 0.5:
            return
        self._fav_id, self._fav_t = tid, now
        favs = list(self.store.get("favorites"))
        if tid in favs:
            favs.remove(tid)
            self.toast(T("fav_removed"))
        else:
            favs.append(tid)
            self.toast(T("fav_added"), "ok")
        self.store.set("favorites", favs)
        for n in ("home", "favorites"):
            if n in self.screens:
                self.screens[n].refresh()

    def log_event(self, tool, detail):
        h = list(self.store.get("history") or [])
        h.insert(0, {"tool": tool, "ts": time.time(), "detail": detail})
        self.store.set("history", h[:100])

    # ---- feedback
    def feedback(self, name):
        try:
            if self.store.get("sound") and name in self.sounds:
                s = self.sounds[name]
                try:
                    s.volume = max(0.0, min(1.0, float(self.store.get("volume"))))
                    s.stop()
                    s.play()
                except Exception:
                    pass
        except Exception:
            pass
        try:
            if name in ("click", "tap", "nav", "pop") and self.store.get("vibrate"):
                vibrate_ms(14)
        except Exception:
            pass

    def toast(self, text, kind="info", seconds=2.4):
        try:
            show_toast(text, kind, seconds)
        except Exception:
            pass

    def busy_show(self, text=""):
        self.busy_hide()
        self._busy = Busy(text)
        self._busy.open()

    def busy_text(self, text):
        if self._busy is not None:
            self._busy.set_text(text)

    def busy_hide(self):
        if self._busy is not None:
            try:
                self._busy.dismiss()
            except Exception:
                pass
            self._busy = None

    def pick_files(self, callback, multiple=False, exts=IMG_EXTS):
        # images: Android's own picker (Google Photos). It needs NO permission, so none is asked.
        if tuple(exts) == tuple(IMG_EXTS) and pick_images_system(callback, multiple):
            return
        # only the built-in picker (hosts without the system picker) has to read the storage itself
        request_android_perms(("storage",))
        FilePicker(callback, multiple=multiple, exts=exts).open()

    def pick_pdfs(self, callback, multiple=False):
        """Choose PDF files: ONE list with every PDF on the device (the system picker is only a fallback button)."""
        # Android 11+ uses the "all files access" screen inside the picker; the old storage
        # permission (and its photos/videos question) only matters on Android 10 and older.
        if platform != "android" or _sdk_int() < 30:
            request_android_perms(("storage",))
        PDFPicker(callback, multiple=multiple).open()

    def save_failed(self, exc):
        """Saving failed in every way: say so (with a short reason) instead of pretending it worked."""
        self.log_error(exc)
        self.busy_hide()
        self.feedback("error")
        self.toast("%s\n%s" % (T("save_failed"), str(exc)[:110]), "error", 6)

    def log_error(self, exc):
        """Write an error to the log file only (nothing is shown to the user)."""
        try:
            with open(os.path.join(self.user_data_dir, "idda_error.log"), "a", encoding="utf-8") as f:
                f.write("\n[%s]\n%s\n" % (datetime.datetime.now().isoformat(),
                                          "".join(traceback.format_exception(type(exc), exc, exc.__traceback__))))
        except Exception:
            pass

    def report(self, exc):
        try:
            with open(os.path.join(self.user_data_dir, "idda_error.log"), "a", encoding="utf-8") as f:
                f.write("\n[%s]\n%s\n" % (datetime.datetime.now().isoformat(),
                                          "".join(traceback.format_exception(type(exc), exc, exc.__traceback__))))
        except Exception:
            pass
        traceback.print_exc()
        self.busy_hide()
        self.toast(T("error"), "error")


if __name__ == "__main__":
    try:
        IddaApp().run()
    except Exception:
        traceback.print_exc()
