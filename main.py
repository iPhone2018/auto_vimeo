#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Vimeo 批量注册 + 视频上传管理工具 - 人工校验等待版 v4
===============================================
变更：hCaptcha人机验证不再直接失败
- 脚本仅触发校验弹窗，不做任何自动识别/绕过
- 日志提示用户手动完成验证码
- 轮询检测校验完成，校验通过后自动继续注册流程
- 最大超时保护，支持stop_event中断等待
修复：注册完成后浏览器关闭导致程序停止的bug
- 原因：finally 中手动 _force_close() 与 with sync_playwright() 自动清理冲突
- 解决：移除 finally 手动关闭，让 with 语句自动管理；增加全面异常捕获
"""

from __future__ import annotations

import base64
import json
import os
import queue
import random
import re
import string
import sys
import threading
import time
import uuid
import warnings
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from threading import Event
from typing import Any, Callable, Dict, List, Optional, Tuple

import requests
from urllib3.exceptions import InsecureRequestWarning

warnings.filterwarnings("ignore", category=InsecureRequestWarning)
# 在文件顶部全局位置定义
LINK_FILE_LOCK = threading.Lock()

try:
    import tkinter as tk
    from tkinter import filedialog, messagebox, scrolledtext, ttk
except ImportError:
    print("GUI模式需要tkinter，当前环境不支持")
    sys.exit(1)

try:
    from playwright.sync_api import Page, sync_playwright
except ImportError:
    print("需要安装 playwright: pip install playwright")
    sys.exit(1)

# =============================================================================
# 1. 常量配置
# =============================================================================
class Config:
    CHUNK_SIZE: int = 10 * 1024 * 1024
    REQUEST_TIMEOUT: int = 300
    MAX_WAIT_AVAILABLE: int = 300
    POLL_BACKOFF_INITIAL: float = 2.0
    POLL_BACKOFF_MAX: float = 30.0
    POLL_BACKOFF_MULTIPLIER: float = 2.0
    # 新增：人工验证码最大等待秒数
    MAX_WAIT_MANUAL_CAPTCHA: int = 180
    CAPTCHA_POLL_INTERVAL: float = 1.5

    DEFAULT_PASSWORD: str = "Admin@coc1"
    EMAIL_USER_MIN: int = 9
    EMAIL_USER_MAX: int = 15
    EMAIL_DOMAIN_LEN: int = 4
    VIEWPORT: Dict[str, int] = {"width": 1280, "height": 800}
    USER_AGENT: str = (
        "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
        "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36"
    )
    API_BASE: str = "https://api.vimeo.com"
    API_VERSION: str = "application/vnd.vimeo.*+json;version=3.4"
    API_VERSION_3410: str = "application/vnd.vimeo.*+json;version=3.4.10"
    VIDEO_EXTENSIONS: Tuple[str, ...] = (".mp4", ".mov", ".avi", ".mkv", ".wmv")
    LINKS_FILENAME: str = "links.txt"

# =============================================================================
# 2. 数据模型
# =============================================================================
@dataclass
class VideoCreationResult:
    video_id: str
    upload_link: str
    video_link: str

@dataclass
class UploadContext:
    session: requests.Session
    jwt_token: str
    user_id: str
    log: Callable[[str], None]
    stop_event: Optional[Event] = None

class TaskStoppedException(Exception):
    pass

# =============================================================================
# 3. 工具函数
# =============================================================================
DOMAIN_LIST = [
    "qq.com",
    "163.com",
    "126.com",
    "yeah.net",
    "foxmail.com",
    "139.com",
    "189.cn",
    "wo.cn",
    "sina.com.cn",
    "outlook.com"
]


def random_qq_email() -> Tuple[str, str]:
    """高熵随机邮箱，格式合法，依靠大随机空间实现几乎不重复，无内存池"""
    EMAIL_USER_MIN = 8
    EMAIL_USER_MAX = 14
    # 首字符必须字母，过系统校验
    first = random.choice(string.ascii_lowercase)
    rest_len = random.randint(EMAIL_USER_MIN - 1, EMAIL_USER_MAX - 1)
    rest = "".join(random.choices(
        string.ascii_lowercase + string.digits + "_-",
        k=rest_len
    ))
    username = first + rest
    domain = random.choice(DOMAIN_LIST)
    email = f"{username}@{domain}"
    return email, username

def decode_jwt(jwt_str: Optional[str]) -> Tuple[Optional[str], str]:
    if not jwt_str:
        return None, ""
    try:
        payload_b64 = jwt_str.split(".")[1]
        payload_b64 += "=" * (4 - len(payload_b64) % 4)
        payload: Dict[str, Any] = json.loads(base64.b64decode(payload_b64))
        return str(payload.get("user_id")), str(payload.get("scopes", ""))[:60]
    except Exception:
        return None, ""

def build_api_headers(jwt_token: str, accept: Optional[str] = None) -> Dict[str, str]:
    headers: Dict[str, str] = {
        "Authorization": f"jwt {jwt_token}",
        "Accept": accept or Config.API_VERSION,
        "Accept-Language": "en-US,en;q=0.9",
        "Origin": "https://vimeo.com",
        "Referer": "https://vimeo.com/",
        "Cache-Control": "no-cache",
        "Pragma": "no-cache",
    }
    return headers

def create_requests_session(cookies: Dict[str, str]) -> requests.Session:
    session = requests.Session()
    session.headers.update({
        "User-Agent": Config.USER_AGENT,
        "Accept": "application/json, text/plain, */*",
        "Accept-Language": "en-US,en;q=0.9",
    })
    for name, value in cookies.items():
        session.cookies.set(name, value, domain=".vimeo.com")
    return session

def append_link(link: str, output_dir: str, filename: str = Config.LINKS_FILENAME) -> None:
    path = Path(output_dir) / filename
    with LINK_FILE_LOCK:
        with open(path, "a", encoding="utf-8") as f:
            f.write(link + "\n")

def get_video_files(video_dir: str) -> List[str]:
    if not video_dir or not os.path.isdir(video_dir):
        return []
    return [f for f in os.listdir(video_dir) if f.lower().endswith(Config.VIDEO_EXTENSIONS)]

# =============================================================================
# 4. Vimeo API 服务层
# =============================================================================
class VimeoAPIService:
    def __init__(self, ctx: UploadContext):
        self.ctx = ctx

    def _log(self, msg: str) -> None:
        self.ctx.log(msg)

    def _check_stop(self) -> None:
        if self.ctx.stop_event and self.ctx.stop_event.is_set():
            self._log("🛑 检测到停止信号，中断API操作")
            raise TaskStoppedException()

    def _post(self, url: str, json_body: Optional[Dict] = None, headers: Optional[Dict] = None) -> requests.Response:
        h = build_api_headers(self.ctx.jwt_token)
        if headers:
            h.update(headers)
        return self.ctx.session.post(url, json=json_body, headers=h, timeout=Config.REQUEST_TIMEOUT, verify=False)

    def _patch(self, url: str, json_body: Optional[Dict] = None, headers: Optional[Dict] = None) -> requests.Response:
        h = build_api_headers(self.ctx.jwt_token)
        if headers:
            h.update(headers)
        return self.ctx.session.patch(url, json=json_body, headers=h, timeout=Config.REQUEST_TIMEOUT, verify=False)

    def _get(self, url: str, headers: Optional[Dict] = None) -> requests.Response:
        h = build_api_headers(self.ctx.jwt_token)
        if headers:
            h.update(headers)
        return self.ctx.session.get(url, headers=h, timeout=Config.REQUEST_TIMEOUT, verify=False)

    def create_video(self, file_path: str) -> Optional[VideoCreationResult]:
        self._check_stop()
        file_size = os.path.getsize(file_path)
        file_name = os.path.basename(file_path)
        self._log(f"创建视频工单: {file_name} ({file_size} bytes)")

        body = {
            "upload": {"approach": "gcs", "size": file_size, "mime_type": "video/mp4"},
            "name": file_name,
            "folder_id": None,
        }
        url = f"{Config.API_BASE}/users/{self.ctx.user_id}/videos?fields=upload.gcs,uri"
        resp = self._post(url, body, {"Content-Type": "application/json"})

        if resp.status_code not in (200, 201):
            self._log(f"创建视频失败: {resp.status_code} {resp.text[:200]}")
            return None

        data = resp.json()
        uri = data.get("uri", "")
        upload_info_list = data.get("upload", {}).get("gcs", [])
        if not upload_info_list:
            self._log("无GCS上传链接")
            return None

        video_id = uri.split("/")[-1]
        return VideoCreationResult(
            video_id=video_id,
            upload_link=upload_info_list[0]["upload_link"],
            video_link=f"https://vimeo.com/{video_id}",
        )

    def upload_file(self, upload_link: str, file_path: str) -> Optional[str]:
        self._check_stop()
        file_size = os.path.getsize(file_path)
        self._log(f"开始GCS分片上传 | total={file_size}, chunk={Config.CHUNK_SIZE}")

        offset = 0
        final_resp: Optional[Dict[str, Any]] = None

        with open(file_path, "rb") as f:
            while True:
                self._check_stop()
                chunk = f.read(Config.CHUNK_SIZE)
                if not chunk:
                    break
                end_byte = offset + len(chunk) - 1
                headers = {
                    "Content-Type": "video/mp4",
                    "Content-Length": str(len(chunk)),
                    "Content-Range": f"bytes {offset}-{end_byte}/{file_size}",
                }
                resp = self.ctx.session.put(upload_link, data=chunk, headers=headers, timeout=Config.REQUEST_TIMEOUT, verify=False)
                if resp.status_code not in (200, 308):
                    self._log(f"分片失败 offset={offset}, code={resp.status_code}")
                    return None
                offset += len(chunk)
                self._log(f"分片完成 {offset}/{file_size}")
                if resp.status_code == 200:
                    final_resp = resp.json()

        if not final_resp:
            self._log("未收到最终GCS响应")
            return None

        upload_id = final_resp.get("metadata", {}).get("umbrellabird_upload_id")
        if not upload_id:
            self._log("GCS返回无 umbrellabird_upload_id")
            return None

        self._log(f"获取 upload_attempt_id = {upload_id}")
        self._report_probe()
        return upload_id

    def _report_probe(self) -> None:
        probe_uuid = str(uuid.uuid4())
        url = f"https://global.upload.vimeo.com/probe/{probe_uuid}"
        body = {"ContentType": "video/mp4", "Id": probe_uuid, "Blacklisted": False}
        headers = {"Content-Type": "application/json", "Accept": "application/json"}
        try:
            resp = self.ctx.session.put(url, json=body, headers=headers, timeout=Config.REQUEST_TIMEOUT, verify=False)
            if resp.status_code == 200:
                self._log("Probe探针上报成功")
        except Exception as e:
            self._log(f"Probe上报失败（可忽略）: {e}")

    def wait_until_available(self, video_id: str) -> bool:
        self._log(f"轮询等待视频 {video_id} 变为 available...")
        fields = "video.status,video.uri,video.name,video.link"
        url = (
            f"{Config.API_BASE}/users/{self.ctx.user_id}/folders/root"
            f"?direction=desc&per_page=25&sort=last_user_action_event_date"
            f"&page=1&fields={fields}"
        )

        wait_time = Config.POLL_BACKOFF_INITIAL
        elapsed = 0
        while elapsed < Config.MAX_WAIT_AVAILABLE:
            self._check_stop()
            time.sleep(wait_time)
            elapsed += wait_time

            resp = self._get(url)
            if resp.status_code != 200:
                wait_time = min(wait_time * Config.POLL_BACKOFF_MULTIPLIER, Config.POLL_BACKOFF_MAX)
                continue
            for item in resp.json().get("data", []):
                vid = item.get("video", {}).get("uri", "").split("/")[-1]
                status = item.get("video", {}).get("status", "")
                if vid == video_id:
                    if status == "available":
                        self._log(f"视频 {video_id} 已可用")
                        return True
                    self._log(f"视频状态: {status}，继续等待...")
            wait_time = min(wait_time * Config.POLL_BACKOFF_MULTIPLIER, Config.POLL_BACKOFF_MAX)
        self._log("等待超时，视频未变为available")
        return False

    def complete_upload(self, video_id: str, upload_attempt_id: str, title: str) -> bool:
        self._check_stop()
        url = f"{Config.API_BASE}/videos/{video_id}/upload_attempts/{upload_attempt_id}/complete"
        body = {"title": title}
        resp = self._post(url, body)
        if resp.status_code == 200:
            self._log("complete 上报成功")
            return True
        self._log(f"complete 失败: {resp.status_code} {resp.text[:200]}")
        return False

    def get_current_version_uri(self, video_id: str) -> Optional[str]:
        fields = "metadata.connections.versions.current_uri"
        url = f"{Config.API_BASE}/videos/{video_id}?fields={fields}"
        resp = self._get(url, {"Accept": Config.API_VERSION_3410})
        if resp.status_code != 200:
            self._log(f"获取版本URI失败: {resp.status_code}")
            return None
        return resp.json().get("metadata", {}).get("connections", {}).get("versions", {}).get("current_uri")

    def update_metadata(self, video_id: str, title: str, intro: str) -> bool:
        self._check_stop()
        self._log(f"更新标题: {title}")
        resp = self._patch(
            f"{Config.API_BASE}/videos/{video_id}?fields=name",
            {"name": title},
            {"Accept": "*/*"},
        )
        self._log(f"标题更新状态: {resp.status_code}")

        version_uri = self.get_current_version_uri(video_id)
        if not version_uri:
            self._log("无法获取版本URI，跳过描述更新")
            return False

        version_id = version_uri.split("/")[-1]
        desc_delta = json.dumps({"ops": [{"insert": intro}]}, ensure_ascii=False)
        resp = self._patch(
            f"{Config.API_BASE}/videos/{video_id}/versions/{version_id}?fields=description",
            {"description": desc_delta},
            {"Accept": Config.API_VERSION_3410},
        )
        self._log(f"描述更新状态: {resp.status_code}")
        return resp.status_code == 200

# =============================================================================
# 5. 浏览器自动化服务层 [v4 人工校验等待逻辑]
# =============================================================================
# =============================================================================
# 5. 浏览器自动化服务层 [v4‑fix 修复hCaptcha双iframe strict模式报错]
# =============================================================================
class VimeoBrowserService:
    def __init__(self, log_callback: Callable[[str], None], stop_event: Optional[Event] = None):
        self.log = log_callback
        self.stop_event = stop_event

    def _check_stop(self) -> None:
        if self.stop_event and self.stop_event.is_set():
            self.log("🛑 检测到停止信号，中断浏览器操作")
            raise TaskStoppedException()

    def register_and_extract(
        self, email: str, password: str, name: str
    ) -> Tuple[Optional[str], Optional[Dict[str, str]], Optional[str]]:
        jwt_token: Optional[str] = None
        cookies: Optional[Dict[str, str]] = None
        user_id: Optional[str] = None

        with sync_playwright() as p:
            browser = p.chromium.launch(headless=False, channel="chrome")
            context = browser.new_context(
                viewport=Config.VIEWPORT,
                user_agent=Config.USER_AGENT,
            )
            page = context.new_page()

            try:
                self._check_stop()
                self._navigate_to_join(page)
                self._check_stop()
                self._fill_registration_form(page, email, password, name)
                self._check_stop()
                self._handle_post_registration_flow(page, name)
                self._check_stop()

                jwt_token = self._extract_jwt(page)
                cookies = {c["name"]: c["value"] for c in context.cookies()}
                user_id, scopes = decode_jwt(jwt_token)
                self.log(f"JWT解析: user_id={user_id}, scopes={scopes}")

            except TaskStoppedException:
                self.log("浏览器任务被中断")
                raise
            except Exception as e:
                self.log(f"❌ 浏览器操作异常: {e}")
                raise

        return jwt_token, cookies, user_id

    def _navigate_to_join(self, page: Page) -> None:
        self.log("🌐 正在访问注册页面...")
        for attempt in range(3):
            self._check_stop()
            try:
                page.goto("https://vimeo.com/join", timeout=30000, wait_until="domcontentloaded")
                break
            except Exception as e:
                self.log(f"  导航尝试 {attempt + 1}/3 失败: {e}")
                if attempt < 2:
                    time.sleep(3)
        else:
            raise RuntimeError("无法加载注册页面")

        try:
            page.wait_for_load_state("networkidle", timeout=15000)
        except Exception:
            pass

        try:
            page.wait_for_selector("text=Just a moment", timeout=3000)
            self.log("检测到Cloudflare挑战，等待中...")
            page.wait_for_url("**/join**", timeout=20000)
        except Exception:
            pass

    def _wait_manual_captcha(self, page: Page) -> None:
        """
        修复版：只定位真实challenge iframe(title="hCaptcha challenge")
        避开aria‑hidden占位iframe，杜绝strict mode violation
        """
        self.log("⚠️ 已触发hCaptcha人机验证，请**手动在浏览器完成验证码**，脚本等待校验完成...")
        start_time = time.time()
        # ✅ 只匹配真正的人机挑战弹窗iframe，过滤隐藏占位iframe
        challenge_iframe = page.locator('iframe[title="hCaptcha challenge"]')

        # 等待challenge iframe出现（说明弹出验证框）
        try:
            challenge_iframe.wait_for(timeout=30000)
        except Exception:
            # 极少数情况：hcaptcha无弹窗直接后台完成，直接返回
            self.log("ℹ️ 未检测到hCaptcha弹窗，跳过人工等待")
            return

        # 轮询：等待iframe被页面移除 = 用户完成验证
        while time.time() - start_time < Config.MAX_WAIT_MANUAL_CAPTCHA:
            self._check_stop()
            cnt = challenge_iframe.count()
            if cnt == 0:
                self.log("✅ 检测到人机验证已手动完成，继续注册流程")
                # 给页面足够时间处理token、跳转，防止立刻填密码报错
                page.wait_for_timeout(2500)
                return
            time.sleep(Config.CAPTCHA_POLL_INTERVAL)

        raise RuntimeError(f"人工验证码等待超时 {Config.MAX_WAIT_MANUAL_CAPTCHA}s，任务失败")

    def _fill_registration_form(self, page: Page, email: str, password: str, name: str) -> None:
        self.log("正在填写注册表单...")

        email_input = page.locator("#unified_auth_email")
        email_input.wait_for(state="visible", timeout=12000)
        email_input.fill(email)
        self.log(f"  填入邮箱: {email}")

        continue_btn = page.locator('button[form="unified_auth_email_form"]').first
        continue_btn.wait_for(state="visible", timeout=8000)
        continue_btn.click()
        self.log("  点击邮箱提交按钮，跳转密码页...")

        try:
            page.wait_for_load_state("networkidle", timeout=15000)
        except Exception:
            pass

        # ========== 修复：用精准选择器判断是否出现hCaptcha挑战 ==========
        challenge_iframe = page.locator('iframe[title="hCaptcha challenge"]')
        if challenge_iframe.count() > 0:
            self._wait_manual_captcha(page)

        pw_inputs = page.locator('input[type="password"]')
        pw_inputs.first.wait_for(state="visible", timeout=12000)
        pw_inputs.first.fill(password)
        if pw_inputs.count() > 1:
            pw_inputs.nth(1).fill(password)

        name_input = page.locator('input[name="display_name"], input[name="name"], input[id*="name"]')
        if name_input.count() > 0 and name_input.first.is_visible():
            name_input.first.fill(name)

        self._click_marketing_checkbox(page)
        self._click_submit_button(page)

        try:
            page.wait_for_url("**/survey**", timeout=12000)
        except Exception:
            page.wait_for_load_state("networkidle", timeout=6000)

        if "/join" in page.url and "/survey" not in page.url:
            self._check_registration_errors(page)

    def _click_marketing_checkbox(self, page: Page) -> None:
        selectors = [
            'input#marketing_opt_in',
            'label:has-text("我同意接收时事通讯、更新和优惠信息")',
            '.chakra-checkbox:has(input#marketing_opt_in)',
            'input[type="checkbox"]',
            'input[name*="agree"], input[name*="accept"], input[name*="tos"]',
            'input[id*="agree"], input[id*="accept"], input[id*="tos"]',
        ]
        for sel in selectors:
            boxes = page.locator(sel)
            for i in range(boxes.count()):
                box = boxes.nth(i)
                if not box.is_visible():
                    continue
                try:
                    visual = box.locator('xpath=./following-sibling::span[contains(@class, "chakra-checkbox__control")]')
                    if visual.is_visible():
                        visual.click()
                        self.log("  已勾选营销复选框")
                        return
                    label = box.locator('xpath=../span[contains(@class, "chakra-checkbox__label")]')
                    if label.is_visible():
                        label.click()
                        self.log("  已勾选营销复选框")
                        return
                except Exception:
                    pass
                if not box.is_checked():
                    box.click()
                    self.log("  已勾选营销复选框")
                    return

    def _click_submit_button(self, page: Page) -> None:
        selectors = [
            'button[type="submit"]',
            'button:has-text("Join")', 'button:has-text("加入")',
            'button:has-text("Continue")', 'button:has-text("继续")',
            'button:has-text("Sign up")', 'button:has-text("注册")',
            'button:has-text("Create account")', 'button:has-text("创建账户")',
        ]
        for sel in selectors:
            btn = page.locator(sel)
            if btn.count() > 0 and btn.first.is_visible():
                btn.first.click()
                self.log(f"  点击提交: {sel}")
                return
        all_btns = page.locator("button")
        for i in range(all_btns.count()):
            b = all_btns.nth(i)
            if b.is_visible():
                self.log("  点击第一个可见按钮")
                b.click()
                return

    def _check_registration_errors(self, page: Page) -> None:
        error_selectors = ['[role="alert"]', '.error', '.form-error']
        for sel in error_selectors:
            el = page.locator(sel).first
            if el.is_visible():
                text = (el.inner_text() or "").strip()
                if len(text) > 2:
                    self.log(f"  注册页错误: {text[:200]}")
                    return
        self.log("  仍在注册页，但未发现明显错误，继续执行...")

    def _handle_post_registration_flow(self, page: Page, name: str) -> None:
        self.log("正在处理注册后流程...")
        for step in range(10):
            self._check_stop()
            url = page.url
            self.log(f"  步骤 {step + 1}: {url[:80]}")

            if step >= 2 and "/join" in url and "/survey" not in url:
                self.log("  注册似乎卡在/join，可能失败")
                break

            if not self._is_registration_flow_url(url):
                self.log("  已离开注册流程")
                break

            self._dismiss_modals(page)
            self._fill_name_if_empty(page, name)

            clicked = False
            if self._click_button_by_texts(page, ["Skip", "跳过", "Skip for now", "Maybe later", "稍后", "Not now",
                                                  "以后再说", "No thanks", "不用了"]):
                clicked = True
            elif self._click_button_by_texts(page, ["Continue", "继续", "Next", "下一步", "Get started", "开始", "Join",
                                                    "加入", "Sign up", "注册", "Start free trial", "免费试用"]):
                clicked = True
            elif self._click_submit_or_any_button(page):
                clicked = True

            if clicked:
                try:
                    page.wait_for_load_state("networkidle", timeout=3000)
                except Exception:
                    pass
            else:
                page.wait_for_timeout(500)

    def _is_registration_flow_url(self, url: str) -> bool:
        keywords = ["survey", "paywall", "join", "upgrade", "billing", "subscribe", "plan", "pricing"]
        return any(kw in url for kw in keywords)

    def _dismiss_modals(self, page: Page) -> None:
        try:
            page.keyboard.press("Escape")
            page.wait_for_timeout(500)
        except Exception:
            pass

    def _fill_name_if_empty(self, page: Page, name: str) -> None:
        inputs = page.locator(
            'input[name="display_name"], input[name="name"], '
            'input[id*="name"], input[placeholder*="name"], input[placeholder*="Name"], input[placeholder*="名称"]'
        )
        if inputs.count() > 0 and inputs.first.is_visible() and not inputs.first.input_value():
            inputs.first.fill(name)
            self.log("  填写名称")

    def _click_button_by_texts(self, page: Page, texts: List[str]) -> bool:
        for text in texts:
            btn = page.locator(f'button:has-text("{text}"), a:has-text("{text}")')
            for i in range(btn.count()):
                b = btn.nth(i)
                if b.is_visible():
                    b.click()
                    self.log(f"  点击: {text}")
                    return True
        return False

    def _click_submit_or_any_button(self, page: Page) -> bool:
        for sel in ['button[type="submit"]', 'input[type="submit"]']:
            btn = page.locator(sel)
            if btn.count() > 0 and btn.first.is_visible():
                btn.first.click()
                self.log("  点击submit按钮")
                return True
        all_btns = page.locator("button")
        for i in range(all_btns.count()):
            b = all_btns.nth(i)
            if b.is_visible():
                b.click()
                self.log("  点击第一个可见按钮")
                return True
        return False

    def _extract_jwt(self, page: Page) -> Optional[str]:
        try:
            page.wait_for_load_state("networkidle", timeout=3000)
        except Exception:
            pass
        self.log("正在提取JWT...")

        try:
            html = page.content()
            m = re.search(r'<script\s+id="__NEXT_DATA__"[^>]*>(.*?)</script>', html, re.DOTALL)
            if m:
                data = json.loads(m.group(1))
                token = data.get("props", {}).get("pageProps", {}).get("viewerBootstrap", {}).get("jwt", "")
                if token:
                    self.log(f"JWT via __NEXT_DATA__: {token[:50]}...")
                    return token
        except Exception as e:
            self.log(f"  __NEXT_DATA__方式失败: {e}")

        try:
            html = page.content()
            m = re.search(r'"jwt"\s*:\s*"([^"]+)"', html)
            if m:
                token = m.group(1)
                self.log(f"JWT via regex: {token[:50]}...")
                return token
        except Exception as e:
            self.log(f"  regex方式失败: {e}")

        self.log("⚠️ 无法提取JWT")
        return None


# =============================================================================
# 6. 单次上传任务协调器
# =============================================================================
class SingleUploadTask:
    def __init__(
        self,
        task_id: int,
        titles: List[str],
        intros: List[str],
        video_dir: str,
        output_dir: str,
        interval: int = 5,
        log_callback: Optional[Callable[[str], None]] = None,
        stop_event: Optional[Event] = None,
    ):
        self.task_id = task_id
        self.titles = titles
        self.intros = intros
        self.video_dir = video_dir
        self.output_dir = output_dir
        self.interval = interval
        self.stop_event = stop_event
        self._external_log = log_callback
        self.email = ""
        self.password = ""
        self.name = ""

    def _log(self, msg: str) -> None:
        timestamp = datetime.now().strftime("%H:%M:%S")
        line = f"[{timestamp}] [用户#{self.task_id}] {msg}"
        print(line)
        if self._external_log:
            self._external_log(line)

    def run(self) -> str:
        self.email, self.name = random_qq_email()
        self.password = Config.DEFAULT_PASSWORD

        self._log(f"📧 邮箱: {self.email}")
        self._log(f"📂 视频目录: {self.video_dir}")
        self._log(f"🎯 本账号将上传 {len(self.titles)} 个视频（max_pub={len(self.titles)}）")

        video_files = get_video_files(self.video_dir)
        self._log(f"📂 发现视频文件: {len(video_files)} 个")
        if not video_files:
            return "错误: 视频目录为空"

        browser = VimeoBrowserService(log_callback=self._log, stop_event=self.stop_event)
        try:
            jwt_token, cookies, user_id = browser.register_and_extract(
                self.email, self.password, self.name
            )
        except TaskStoppedException:
            return "任务已停止"
        except Exception as e:
            self._log(f"❌ 注册阶段异常: {e}")
            return f"错误: 注册失败 - {e}"

        if not jwt_token or not user_id:
            return "错误: 注册成功但无法提取JWT或user_id"

        self._log(f"✅ 注册完成，jwt={jwt_token[:30]}..., user_id={user_id}")
        self._log(f"📤 准备上传 {len(self.titles)} 个视频...")

        try:
            session = create_requests_session(cookies)
            ctx = UploadContext(
                session=session, jwt_token=jwt_token, user_id=user_id,
                log=self._log, stop_event=self.stop_event
            )
            api = VimeoAPIService(ctx)
        except Exception as e:
            self._log(f"❌ 创建API会话失败: {e}")
            return f"错误: API会话创建失败 - {e}"

        success_count = 0
        for idx, (title, intro) in enumerate(zip(self.titles, self.intros), 1):
            if self.stop_event and self.stop_event.is_set():
                self._log("🛑 收到停止信号，终止上传")
                break

            self._log(f"\n📁 [{idx}/{len(self.titles)}] 开始上传: {title[:40]}...")
            video_file = random.choice(video_files)
            video_path = os.path.join(self.video_dir, video_file)

            try:
                ok = self._upload_single_video(api, video_path, title, intro)
            except TaskStoppedException:
                self._log("🛑 上传流程被中断")
                break
            except Exception as e:
                self._log(f"❌ 第 {idx} 个视频上传异常: {e}")
                continue

            if not ok:
                self._log(f"❌ 第 {idx} 个视频上传失败，继续下一个...")
                continue

            success_count += 1

            if idx < len(self.titles):
                self._log(f"⏳ 等待 {self.interval} 秒后继续...")
                for _ in range(self.interval):
                    if self.stop_event and self.stop_event.is_set():
                        self._log("🛑 等待期间收到停止信号")
                        break
                    time.sleep(1)
        try:
            session.close()
            self._log("📤 账号所有上传任务完成，关闭HTTP会话")
        except Exception:
            pass
        self._log(f"\n✅ 任务完成，成功上传 {success_count}/{len(self.titles)} 个视频")
        return f"成功上传 {success_count} 个视频"

    def _upload_single_video(self, api: VimeoAPIService, video_path: str, title: str, intro: str) -> bool:
        creation = api.create_video(video_path)
        if not creation:
            return False

        upload_attempt_id = api.upload_file(creation.upload_link, video_path)
        if not upload_attempt_id:
            return False

        if not api.wait_until_available(creation.video_id):
            return False

        file_name = os.path.basename(video_path)
        api.complete_upload(creation.video_id, upload_attempt_id, file_name)
        api.update_metadata(creation.video_id, title, intro)

        self._log(f"🔗 视频地址: {creation.video_link}")
        append_link(creation.video_link, self.output_dir)
        return True

# =============================================================================
# 7. 任务调度器
# =============================================================================
class TaskScheduler:
    def __init__(
        self,
        title_files: List[str],
        intro_files: List[str],
        output_dir: str,
        video_dir: str,
        thread_count: int,
        interval: int = 5,
        max_pub: int = 10,
        log_callback: Optional[Callable[[str], None]] = None,
        progress_callback: Optional[Callable[[Dict[str, Any]], None]] = None,
    ):
        self.title_files = title_files
        self.intro_files = intro_files
        self.output_dir = output_dir
        self.video_dir = video_dir
        self.thread_count = thread_count
        self.interval = interval
        self.max_pub = max_pub
        self.log_callback = log_callback
        self.progress_callback = progress_callback

        self.stop_event = Event()
        self.pause_event = Event()
        self.lock = threading.Lock()
        self.completed = 0
        self._running = False
        self.executor: Optional[ThreadPoolExecutor] = None

    def _log(self, msg: str) -> None:
        timestamp = datetime.now().strftime("%H:%M:%S")
        line = f"[{timestamp}] {msg}"
        print(line)
        if self.log_callback:
            self.log_callback(line)

    def run(self) -> None:
        with self.lock:
            if self._running:
                self._log("已有任务在运行中，跳过")
                return
            self._running = True
            self.stop_event.clear()

        try:
            self._show_config()
            title_pool = self._load_titles()
            intro_pools = self._load_intros()
            if not title_pool or not intro_pools:
                return

            self.executor = ThreadPoolExecutor(max_workers=self.thread_count)
            futures: Dict[Any, int] = {}
            user_idx = 0

            while not self.stop_event.is_set():
                done = [f for f in list(futures.keys()) if f.done()]
                for f in done:
                    idx = futures.pop(f)
                    try:
                        result = f.result()
                        self._log(f"   [完成] 用户 #{idx}: {result}")
                    except TaskStoppedException:
                        self._log(f"   [停止] 用户 #{idx}: 任务被中断")
                    except Exception as e:
                        self._log(f"   [错误] 用户 #{idx}: {e}")

                if self.pause_event.is_set():
                    time.sleep(0.5)
                    continue

                if len(futures) >= self.thread_count:
                    time.sleep(0.5)
                    continue

                user_idx += 1
                count = min(self.max_pub, len(title_pool))
                titles = random.sample(title_pool, count)
                intros = self._compose_intros(intro_pools, count)

                self._log(f"   [提交] 用户 #{user_idx} - 将上传 {count} 个视频（max_pub={self.max_pub}）")
                future = self.executor.submit(
                    self._run_single_task,
                    task_id=user_idx,
                    titles=titles,
                    intros=intros,
                )
                futures[future] = user_idx

            self._log("收到停止信号，终止提交新任务")
            for f in list(futures.keys()):
                f.cancel()
        finally:
            if self.executor:
                try:
                    self.executor.shutdown(wait=False, cancel_futures=True)
                except Exception:
                    pass
                self.executor = None
            with self.lock:
                self._running = False
            self._log(f"✅ 调度结束，累计完成: {self.completed} 个视频")

    def _run_single_task(self, task_id: int, titles: List[str], intros: List[str]) -> str:
        task = SingleUploadTask(
            task_id=task_id,
            titles=titles,
            intros=intros,
            video_dir=self.video_dir,
            output_dir=self.output_dir,
            interval=self.interval,
            log_callback=self.log_callback,
            stop_event=self.stop_event,
        )
        try:
            result = task.run()
        except TaskStoppedException:
            result = "任务被停止"
        except Exception as e:
            self._log(f"[严重错误] 用户 #{task_id} 任务线程崩溃: {e}")
            import traceback
            self._log(traceback.format_exc())
            result = f"任务崩溃: {e}"

        with self.lock:
            import re as _re
            m = _re.search(r'(\d+)', result)
            if m and "成功" in result:
                self.completed += int(m.group(1))
        if self.progress_callback:
            self.progress_callback({"current": self.completed, "status": f"已完成 {self.completed} 个视频"})
        return result

    def _show_config(self) -> None:
        self._log("=" * 60)
        self._log("🚀 Vimeo 批量上传任务启动")
        self._log(f"   标题文件: {len(self.title_files)} 个")
        self._log(f"   简介文件: {len(self.intro_files)} 个")
        self._log(f"   输出目录: {self.output_dir}")
        self._log(f"   视频目录: {self.video_dir}")
        self._log(f"   并发数: {self.thread_count}")
        self._log(f"   发布间隔: {self.interval} 秒（每次上传一个视频后等待）")
        self._log(f"   单账号上限: {self.max_pub} 个视频")
        self._log(f"   人工验证码最大等待: {Config.MAX_WAIT_MANUAL_CAPTCHA} 秒")
        self._log("=" * 60)

    def _load_titles(self) -> List[str]:
        self._log("\n📖 读取标题池...")
        pool: List[str] = []
        for fp in self.title_files:
            path = Path(fp)
            if not path.exists():
                self._log(f"⚠️ 跳过不存在文件: {fp}")
                continue
            try:
                with open(path, "r", encoding="utf-8") as f:
                    for line in f:
                        line = line.strip()
                        if line:
                            pool.append(line)
                self._log(f"   从 [{path.name}] 读取")
            except Exception as e:
                self._log(f"⚠️ 读取失败 [{fp}]: {e}")
        pool = list(dict.fromkeys(pool))
        self._log(f"   去重后: {len(pool)} 个")
        if not pool:
            self._log("❌ 标题池为空")
        return pool

    def _load_intros(self) -> List[List[str]]:
        self._log("\n📖 读取简介池...")
        pools: List[List[str]] = []
        for fp in self.intro_files:
            path = Path(fp)
            if not path.exists():
                self._log(f"⚠️ 跳过不存在文件: {fp}")
                continue
            try:
                lines = [line.strip() for line in open(path, "r", encoding="utf-8") if line.strip()]
                if lines:
                    pools.append(lines)
                    self._log(f"   从 [{path.name}] 读取 {len(lines)} 行")
            except Exception as e:
                self._log(f"⚠️ 读取失败 [{fp}]: {e}")
        if not pools:
            self._log("❌ 简介池为空")
        return pools

    @staticmethod
    def _compose_intros(intro_pools: List[List[str]], count: int) -> List[str]:
        return ["".join(random.choice(pool) for pool in intro_pools) for _ in range(count)]

    def stop(self) -> None:
        self._log("🛑 正在停止所有任务...")
        self.stop_event.set()
        self.pause_event.set()
        if self.executor:
            try:
                self.executor.shutdown(wait=False, cancel_futures=True)
            except Exception:
                pass
            self.executor = None
        self._log("🛑 已停止")

    def pause(self) -> None:
        self._log("⏸ 正在暂停...")
        self.stop_event.set()
        self.pause_event.set()
        if self.executor:
            try:
                self.executor.shutdown(wait=False, cancel_futures=True)
            except Exception:
                pass
            self.executor = None
        self._log("⏸ 已暂停")

    def resume(self) -> None:
        self._log("▶ 继续运行")
        self.stop_event.clear()
        self.pause_event.clear()

# =============================================================================
# 8. GUI 构建器
# =============================================================================
class VimeoGUI:
    def __init__(self):
        self.root = tk.Tk()
        self.root.title("Vimeo 批量注册工具 - 人工校验版 v4")
        self.root.geometry("1100x900")
        self.root.minsize(1000, 800)

        self.scheduler: Optional[TaskScheduler] = None
        self.log_queue: queue.Queue = queue.Queue()

        self.title_dir_var = tk.StringVar(value="")
        self.intro_dir_var = tk.StringVar(value="")
        self.video_dir_var = tk.StringVar(value="")
        self.output_dir_var = tk.StringVar(value="")
        self.title_paths: List[str] = []
        self.intro_paths: List[str] = []
        self.title_checks: Dict[str, Tuple[tk.IntVar, str]] = {}
        self.intro_checks: Dict[str, Tuple[tk.IntVar, str]] = {}

        self._build_ui()
        self._start_refresh_loop()

    def _build_ui(self) -> None:
        self._build_header()
        main = tk.Frame(self.root, padx=15, pady=10)
        main.pack(fill=tk.BOTH, expand=True)

        self._build_config_section(main)
        self._build_file_lists(main)
        self._build_selected_paths(main)
        self._build_buttons(main)
        self._build_progress(main)
        self._build_log(main)
        self._build_status_bar()

        self._add_log("工具已启动，请依次选择目录并勾选文件后点击「启动」")
        self._add_log("提示：遇到hCaptcha时，请手动在弹出Chrome浏览器完成验证码，脚本会自动继续")

    def _build_header(self) -> None:
        frame = tk.Frame(self.root, bg="#2c5aa0")
        frame.pack(fill=tk.X)
        tk.Label(frame, text="📝 Vimeo 批量注册工具", font=("微软雅黑", 16, "bold"),
                 fg="white", bg="#2c5aa0", pady=12).pack()

    def _build_config_section(self, parent: tk.Widget) -> None:
        cfg = tk.LabelFrame(parent, text="配置选项", font=("微软雅黑", 10, "bold"))
        cfg.pack(fill=tk.X, pady=5)

        num_frame = tk.Frame(cfg)
        num_frame.pack(fill=tk.X, pady=5, padx=10)
        self.thread_spin = self._add_number_input(num_frame, "浏览器数:", 1, 6, 3, "建议 1~6", width=10)
        self.max_pub_spin = self._add_number_input(num_frame, "单账号最大发布数:", 1, 100, 10, "个", width=14)
        self.interval_spin = self._add_number_input(num_frame, "发布间隔:", 1, 300, 5, "秒（每次上传一个视频后等待）", width=10)

        self._add_dir_row(cfg, "标题目录:", self.title_dir_var, self._on_title_dir_changed)
        self._add_dir_row(cfg, "简介目录:", self.intro_dir_var, self._on_intro_dir_changed)
        self._add_dir_row(cfg, "视频目录:", self.video_dir_var, None)
        self._add_dir_row(cfg, "输出目录:", self.output_dir_var, None)

    def _add_number_input(self, parent: tk.Widget, label: str, min_v: int, max_v: int,
                          default: int, hint: str, width: int = 10) -> tk.Spinbox:
        tk.Label(parent, text=label, font=("微软雅黑", 10, "bold"), width=width, anchor=tk.W).pack(side=tk.LEFT)
        spin = tk.Spinbox(parent, from_=min_v, to=max_v, width=8, font=("微软雅黑", 10))
        spin.pack(side=tk.LEFT, padx=5)
        spin.delete(0, tk.END)
        spin.insert(0, str(default))
        tk.Label(parent, text=hint, font=("微软雅黑", 9), fg="#666").pack(side=tk.LEFT)
        return spin

    def _add_dir_row(self, parent: tk.Widget, label: str, var: tk.StringVar,
                     on_changed: Optional[Callable[[str], None]]) -> None:
        frame = tk.Frame(parent)
        frame.pack(fill=tk.X, pady=5, padx=10)
        tk.Label(frame, text=label, font=("微软雅黑", 10, "bold"), width=10, anchor=tk.W).pack(side=tk.LEFT)
        tk.Entry(frame, textvariable=var, width=50, font=("微软雅黑", 9), state="readonly").pack(side=tk.LEFT, padx=5)

        def choose():
            d = filedialog.askdirectory(title=f"选择{label[:-1]}")
            if d:
                var.set(d)
                if on_changed:
                    on_changed(d)

        tk.Button(frame, text="浏览...", command=choose, font=("微软雅黑", 9), width=8).pack(side=tk.LEFT)

    def _build_file_lists(self, parent: tk.Widget) -> None:
        frame = tk.Frame(parent)
        frame.pack(fill=tk.X, pady=5)

        self.title_list_frame, self.title_scrollable = self._create_checklist(
            frame, "标题文件列表（勾选添加）", side=tk.LEFT
        )
        self.intro_list_frame, self.intro_scrollable = self._create_checklist(
            frame, "简介文件列表（勾选添加）", side=tk.RIGHT
        )

    def _create_checklist(self, parent: tk.Widget, title: str, side: tk._Side) -> Tuple[tk.LabelFrame, tk.Frame]:
        lf = tk.LabelFrame(parent, text=title, font=("微软雅黑", 10, "bold"), height=200)
        lf.pack(side=side, fill=tk.BOTH, expand=True, padx=(0 if side == tk.LEFT else 5, 5 if side == tk.LEFT else 0))
        lf.pack_propagate(False)

        canvas = tk.Canvas(lf, bg="#1e1e1e", highlightthickness=0)
        scrollbar = tk.Scrollbar(lf, orient=tk.VERTICAL, command=canvas.yview)
        scrollable = tk.Frame(canvas, bg="#1e1e1e")

        scrollable.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0, 0), window=scrollable, anchor="nw", width=480)
        canvas.configure(yscrollcommand=scrollbar.set)
        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        return lf, scrollable

    def _on_title_dir_changed(self, directory: str) -> None:
        self._refresh_checklist(
            directory, self.title_scrollable, self.title_checks, self.title_paths,
            self.title_input, self._on_title_toggled
        )

    def _on_intro_dir_changed(self, directory: str) -> None:
        self._refresh_checklist(
            directory, self.intro_scrollable, self.intro_checks, self.intro_paths,
            self.intro_input, self._on_intro_toggled
        )

    def _refresh_checklist(self, directory: str, container: tk.Frame, check_vars: Dict,
                           path_list: List[str], text_widget: tk.Text, toggle_cmd: Callable) -> None:
        for w in container.winfo_children():
            w.destroy()
        check_vars.clear()
        path_list.clear()
        text_widget.delete("1.0", tk.END)

        if not directory or not os.path.isdir(directory):
            tk.Label(container, text="请先选择有效目录", font=("微软雅黑", 10), bg="#1e1e1e", fg="#888").pack(pady=20)
            return

        txt_files = sorted([f for f in os.listdir(directory) if f.lower().endswith(".txt")])
        if not txt_files:
            tk.Label(container, text="未找到 .txt 文件", font=("微软雅黑", 10), bg="#1e1e1e", fg="#888").pack(pady=20)
            return

        for fname in txt_files:
            display = Path(fname).stem
            var = tk.IntVar(value=0)
            full = os.path.join(directory, fname)
            check_vars[display] = (var, full)
            cb = tk.Checkbutton(
                container, text=f"  {display}", variable=var,
                font=("微软雅黑", 10), fg="white", bg="#1e1e1e",
                selectcolor="#333", activebackground="#1e1e1e", activeforeground="white",
                anchor=tk.W, command=lambda d=display: toggle_cmd(d)
            )
            cb.pack(fill=tk.X, padx=5, pady=2)

    def _on_title_toggled(self, display_name: str) -> None:
        self._toggle_item(display_name, self.title_checks, self.title_paths, self.title_input)

    def _on_intro_toggled(self, display_name: str) -> None:
        self._toggle_item(display_name, self.intro_checks, self.intro_paths, self.intro_input)

    def _toggle_item(self, display_name: str, check_vars: Dict, path_list: List[str], text_widget: tk.Text) -> None:
        var, full_path = check_vars[display_name]
        if var.get() == 1:
            if full_path not in path_list:
                path_list.append(full_path)
        else:
            if full_path in path_list:
                path_list.remove(full_path)
        text_widget.delete("1.0", tk.END)
        text_widget.insert(tk.END, "\n".join(path_list))

    def _build_selected_paths(self, parent: tk.Widget) -> None:
        frame = tk.Frame(parent)
        frame.pack(fill=tk.X, pady=5)
        self.title_input = self._create_path_text(frame, "已选标题文件路径", tk.LEFT)
        self.intro_input = self._create_path_text(frame, "已选简介文件路径", tk.RIGHT)

    def _create_path_text(self, parent: tk.Widget, title: str, side: tk._Side) -> tk.Text:
        lf = tk.LabelFrame(parent, text=title, font=("微软雅黑", 10, "bold"))
        lf.pack(side=side, fill=tk.BOTH, expand=True, padx=(0 if side == tk.LEFT else 5, 5 if side == tk.LEFT else 0))
        text = tk.Text(lf, font=("Consolas", 9), wrap=tk.WORD, height=3,
                       bg="#1e1e1e", fg="#d4d4d4", insertbackground="white")
        text.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        scroll = tk.Scrollbar(lf, command=text.yview)
        scroll.pack(side=tk.RIGHT, fill=tk.Y)
        text.config(yscrollcommand=scroll.set)
        return text

    def _build_buttons(self, parent: tk.Widget) -> None:
        frame = tk.Frame(parent)
        frame.pack(fill=tk.X, pady=10)
        self.start_btn = tk.Button(frame, text="▶ 启动", bg="#4CAF50", fg="white",
                                   font=("微软雅黑", 12, "bold"), width=15, command=self._on_start)
        self.start_btn.pack(side=tk.LEFT, padx=5)
        self.pause_btn = tk.Button(frame, text="⏸ 暂停", bg="#FF9800", fg="white",
                                   font=("微软雅黑", 12, "bold"), width=12, state=tk.DISABLED,
                                   command=self._on_pause)
        self.pause_btn.pack(side=tk.LEFT, padx=5)

    def _build_progress(self, parent: tk.Widget) -> None:
        frame = tk.LabelFrame(parent, text="处理进度", font=("微软雅黑", 10, "bold"))
        frame.pack(fill=tk.X, pady=5)

        self.task_label = tk.Label(frame, text="就绪", font=("微软雅黑", 11, "bold"), fg="#333", anchor=tk.W)
        self.task_label.pack(fill=tk.X, padx=10, pady=5)

        prog_frame = tk.Frame(frame)
        prog_frame.pack(fill=tk.X, padx=10, pady=2)
        tk.Label(prog_frame, text="视频进度:", font=("微软雅黑", 9), width=12, anchor=tk.W).pack(side=tk.LEFT)
        self.progress_var = tk.DoubleVar(value=0)
        self.progress_bar = ttk.Progressbar(prog_frame, variable=self.progress_var, maximum=100, length=750)
        self.progress_bar.pack(side=tk.LEFT, fill=tk.X, expand=True)
        self.progress_label = tk.Label(prog_frame, text="0", font=("微软雅黑", 9), width=8)
        self.progress_label.pack(side=tk.LEFT, padx=5)

        self.stats_label = tk.Label(frame, text="已完成: 0 个视频 | 状态: 就绪", font=("微软雅黑", 9), fg="#666", anchor=tk.W)
        self.stats_label.pack(fill=tk.X, padx=10, pady=5)

    def _build_log(self, parent: tk.Widget) -> None:
        frame = tk.LabelFrame(parent, text="运行日志", font=("微软雅黑", 10, "bold"))
        frame.pack(fill=tk.BOTH, expand=True, pady=5)
        self.log_text = scrolledtext.ScrolledText(
            frame, font=("Consolas", 9), wrap=tk.WORD, state=tk.DISABLED,
            bg="#1e1e1e", fg="#d4d4d4", insertbackground="white"
        )
        self.log_text.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

    def _build_status_bar(self) -> None:
        self.status_bar = tk.Label(self.root, text="就绪", bd=1, relief=tk.SUNKEN, anchor=tk.W, font=("微软雅黑", 9))
        self.status_bar.pack(side=tk.BOTTOM, fill=tk.X)

    def _on_start(self) -> None:
        if not self._validate_inputs():
            return

        out_dir = self.output_dir_var.get()
        os.makedirs(out_dir, exist_ok=True)

        try:
            thread_count = int(self.thread_spin.get())
            interval = int(self.interval_spin.get())
            max_pub = int(self.max_pub_spin.get())
        except ValueError:
            messagebox.showerror("错误", "数值配置必须是有效整数")
            return

        self._log_config_summary(thread_count, interval, max_pub)

        self.scheduler = TaskScheduler(
            title_files=self.title_paths,
            intro_files=self.intro_paths,
            output_dir=out_dir,
            video_dir=self.video_dir_var.get(),
            thread_count=thread_count,
            interval=interval,
            max_pub=max_pub,
            log_callback=self._add_log,
            progress_callback=self._update_progress,
        )
        self.start_btn.config(state=tk.DISABLED)
        self.pause_btn.config(state=tk.NORMAL)
        self.status_bar.config(text="处理中...")
        threading.Thread(target=self.scheduler.run, daemon=True).start()

    def _validate_inputs(self) -> bool:
        checks = [
            (self.title_dir_var.get(), "请选择标题目录"),
            (self.intro_dir_var.get(), "请选择简介目录"),
            (self.output_dir_var.get(), "请选择输出目录"),
            (self.video_dir_var.get(), "请选择视频目录"),
        ]
        for val, msg in checks:
            if not val:
                messagebox.showerror("错误", msg)
                return False
        if not self.title_paths:
            messagebox.showerror("错误", "请至少勾选一个标题文件")
            return False
        if not self.intro_paths:
            messagebox.showerror("错误", "请至少勾选一个简介文件")
            return False
        return True

    def _log_config_summary(self, tc: int, interval: int, max_pub: int) -> None:
        self._add_log("=" * 60)
        self._add_log("📋 配置汇总")
        self._add_log(f"   浏览器数: {tc}")
        self._add_log(f"   单账号最大发布: {max_pub}")
        self._add_log(f"   发布间隔: {interval}秒（每次上传一个视频后等待）")
        self._add_log(f"   标题目录: {self.title_dir_var.get()}")
        self._add_log(f"   简介目录: {self.intro_dir_var.get()}")
        self._add_log(f"   视频目录: {self.video_dir_var.get()}")
        self._add_log(f"   输出目录: {self.output_dir_var.get()}")
        self._add_log("=" * 60)

    def _on_pause(self) -> None:
        if not self.scheduler:
            return
        if self.pause_btn.cget("text") == "⏸ 暂停":
            self.scheduler.pause()
            self.pause_btn.config(text="▶ 继续")
            self.status_bar.config(text="已暂停")
            self.start_btn.config(state=tk.DISABLED)
        else:
            self._resume()

    def _resume(self) -> None:
        if not self.scheduler:
            return
        old_count = self.scheduler.completed
        self.scheduler.resume()

        out_dir = self.output_dir_var.get()
        try:
            tc = int(self.thread_spin.get())
            interval = int(self.interval_spin.get())
            max_pub = int(self.max_pub_spin.get())
        except ValueError:
            tc, interval, max_pub = 3, 5, 10

        self.scheduler = TaskScheduler(
            title_files=self.title_paths,
            intro_files=self.intro_paths,
            output_dir=out_dir,
            video_dir=self.video_dir_var.get(),
            thread_count=tc,
            interval=interval,
            max_pub=max_pub,
            log_callback=self._add_log,
            progress_callback=self._update_progress,
        )
        self.scheduler.completed = old_count
        self.pause_btn.config(text="⏸ 暂停")
        self.status_bar.config(text="处理中...")
        threading.Thread(target=self.scheduler.run, daemon=True).start()

    def _add_log(self, msg: str) -> None:
        self.log_queue.put(msg)

    def _update_progress(self, data: Dict[str, Any]) -> None:
        self.log_queue.put(("progress", data))

    def _start_refresh_loop(self) -> None:
        self._refresh_ui()
        self.root.after(200, self._start_refresh_loop)

    def _refresh_ui(self) -> None:
        try:
            while True:
                item = self.log_queue.get_nowait()
                if isinstance(item, tuple) and item[0] == "progress":
                    d = item[1]
                    self.progress_var.set(d["current"] % 100)
                    self.progress_label.config(text=str(d["current"]))
                    self.task_label.config(text=f"状态: {d['status']}")
                    self.stats_label.config(text=f"已完成: {d['current']} 个视频 | 状态: {d['status']}")
                else:
                    self._insert_log_line(item)
        except queue.Empty:
            pass

    def _insert_log_line(self, msg: str) -> None:
        self.log_text.config(state=tk.NORMAL)
        self.log_text.insert(tk.END, msg + "\n")
        self.log_text.see(tk.END)
        self.log_text.config(state=tk.DISABLED)

    def run(self) -> None:
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)
        self.root.mainloop()

    def _on_close(self) -> None:
        if self.scheduler:
            self.scheduler.stop()
        self.root.destroy()


# =============================================================================
# 9. 入口
# =============================================================================
def main() -> None:
    app = VimeoGUI()
    app.run()


if __name__ == "__main__":
    main()
