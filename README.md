#  Process Monitor
<div align="left">
  <br><br>
  <a href="https://t.me/NullError_ir" target="_blank">
    <img src="https://img.shields.io/badge/Telegram-black?style=for-the-badge&logo=Telegram" alt="Telegram" />
  </a>
</div>
<br>

![https://img.shields.io/badge/License-MIT-green.svg](https://img.shields.io/badge/License-MIT-green.svg)

![https://img.shields.io/badge/Version-1.0-red.svg](https://img.shields.io/badge/Version-1.0-red.svg)


یک ابزار مانیتورینگ فرآیندهای سیستم مبتنی بر ترمینال (TUI) که با زبان **Go** نوشته شده است. این برنامه با تمرکز بر کارایی، تحلیل امنیتی و ارائه یک تجربه کاربری مدرن و چشم‌نواز طراحی شده است. 

![ ](screenshots/Screenshots.png)


-----

## ✨ ویژگی‌ها

  * **لیست زنده پروسس ها:** نمایش لحظه‌ای تمام فرآیندهای سیستم به همراه روابط (Parents - children).
  * **جزئیات پروسس :** نمایش جزئیات کامل هر فرآیند شامل منابع مصرفی (CPU و حافظه)، فایل‌های باز شده و اتصالات شبکه.
  * **تحلیل پروسس:** مجهز به یک موتور قوانین ساده برای شناسایی فعالیت‌های مشکوک (مانند اجرا از مسیرهای نامعتبر یا باینری‌های حذف شده).
  * **مانیتورینگ شبکه:** نمایش تمام اتصالات شبکه برای هر فرآیند به همراه IP لوکال، IP ریموت و IP عمومی اینترنت شما.
  * **جستجو و فیلتر آنی:** قابلیت جستجوی سریع در میان تمام فرآیندها بر اساس نام، PID 
  * **حالت فریز (Freeze):**  فرآیند در پنل جزئیات آن "فریز" می‌شود تا بتوانید اطلاعات را با دقت بررسی، کپی یا اسکرین‌شات تهیه کنید، در حالی که لیست فرآیندها زنده باقی می‌ماند.

-----

## ⚙️ پیش‌نیازها

برای اجرا و توسعه این پروژه، تنها به نصب بودن **Go** (نسخه 1.18 یا جدیدتر) بر روی سیستم خود نیاز دارید.

-----

## 🛠️ نصب و اجرا

اجرای برنامه بسیار ساده است. مراحل زیر را در ترمینال خود دنبال کنید:

**۱. کلون کردن مخزن:**
ابتدا پروژه را از گیت‌هاب کلون کنید:

```bash
git clone https://github.com/Null-Err0r/Process-Monitor.git
cd Process-Monitor
```

**۲. دریافت وابستگی‌ها:**
دستور زیر را اجرا کنید تا تمام پکیج‌ها و ماژول‌های مورد نیاز به طور خودکار دانلود شوند:

```bash
go mod tidy
```

**۳. اجرای برنامه:**
حالا برنامه را به سادگی با دستور زیر اجرا کنید:

```bash
go run main.go
```

-----

## 📦 ساخت فایل اجرایی (Build)

شما می‌توانید به راحتی فایل اجرایی (Binary) این برنامه را برای سیستم‌عامل‌های مختلف بسازید. این فایل‌ها به صورت مستقل و بدون نیاز به Go قابل اجرا هستند.

### لینوکس (Linux)

```bash
GOOS=linux GOARCH=amd64 go build -ldflags="-s -w" -o procmonitor-linux main.go
upx --best --lzma procmonitor-linux
```

فایل خروجی `procmonitor-linux` خواهد بود.

### ویندوز (Windows)

```bash
GOOS=windows GOARCH=amd64 go build -ldflags="-s -w" -o procmonitor.exe main.go
upx --best --lzma procmonitor.exe
```

فایل خروجی `procmonitor.exe` خواهد بود.

### مک (macOS)

**برای مک‌های مبتنی بر اینتل (Intel):**

```bash
GOOS=darwin GOARCH=amd64 go build -ldflags="-s -w" -o procmonitor-macos-intel main.go
upx --best --lzma procmonitor-macos-intel
```

**برای مک‌های مبتنی بر اپل سیلیکون (Apple Silicon - M1/M2/M3):**

```bash
GOOS=darwin GOARCH=arm64 go build -ldflags="-s -w" -o procmonitor-macos-arm main.go
upx --best --lzma procmonitor-macos-arm
```

فایل‌های خروجی `procmonitor-macos-intel` و `procmonitor-macos-arm` خواهند بود.

-----

## 📄 مجوز (License)


![Repo Badge](https://visitor-badge.laobi.icu/badge?page_id=null-err0r.Process-Monitor) 
