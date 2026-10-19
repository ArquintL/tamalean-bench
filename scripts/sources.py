"""Reading a file of a pinned source: from a local clone when one is configured, otherwise by
downloading it at the pinned commit, or out of the archive pinned by its sha256.

Downloaded files are data: nothing here executes them.
"""

import io
import subprocess
import time
import urllib.parse
import urllib.request
import zipfile

import benchlib

USER_AGENT = "tamalean-bench fetch_models.py"


def _download(url, tries=4):
    last = None
    for i in range(tries):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
            with urllib.request.urlopen(req, timeout=120) as r:
                return r.read()
        except Exception as e:  # network errors are retried, then reported
            last = e
            time.sleep(2 * (i + 1))
    raise RuntimeError(f"cannot download {url}: {last}")


def raw_url(source, path):
    """The URL of `path` at the source's pinned commit, for a git source."""
    repo = source["repo"].removesuffix(".git").rstrip("/")
    quoted = urllib.parse.quote(path)
    if repo.startswith("https://github.com/"):
        owner_repo = repo[len("https://github.com/"):]
        return f"https://raw.githubusercontent.com/{owner_repo}/{source['commit']}/{quoted}"
    if repo.startswith("https://gitlab.com/"):
        return f"{repo}/-/raw/{source['commit']}/{quoted}"
    raise ValueError(f"no raw URL for {repo}")


def is_archive(source):
    return "archive_url" in source


class SourceReader:
    """Reads files of the manifest's sources.  `mirrors` maps a source id to a local git clone
    that has the pinned commit (bench.local.toml, [mirrors]); a clone is read with `git show`,
    so a sparse or partial clone works too."""

    def __init__(self, mirrors=None, archive_dir=None, offline=False):
        self.mirrors = mirrors or {}
        self.archive_dir = archive_dir or (benchlib.CACHE / "archives")
        self.offline = offline
        self._zips = {}

    def _archive(self, source):
        sid = source["id"]
        if sid in self._zips:
            return self._zips[sid]
        want = source["archive_sha256"]
        local = self.archive_dir / f"{want}.zip"
        data = None
        if local.exists():
            data = local.read_bytes()
        elif sid in self.mirrors and str(self.mirrors[sid]).endswith(".zip"):
            data = open(self.mirrors[sid], "rb").read()
        elif not self.offline:
            data = _download(source["archive_url"])
        if data is None:
            raise RuntimeError(f"{sid}: archive not available offline")
        got = benchlib.sha256_bytes(data)
        if got != want:
            raise RuntimeError(f"{sid}: archive sha256 {got}, the manifest pins {want}")
        if not local.exists():
            local.parent.mkdir(parents=True, exist_ok=True)
            local.write_bytes(data)
        z = zipfile.ZipFile(io.BytesIO(data))
        self._zips[sid] = z
        return z

    def read(self, source, path):
        """The bytes of `path` (relative to the source's root) at the pinned commit or in the
        pinned archive, and its git mode ('100755' for an executable) when known."""
        if is_archive(source):
            z = self._archive(source)
            info = z.getinfo(source.get("archive_root", "") + path)
            mode = "100755" if (info.external_attr >> 16) & 0o111 else "100644"
            return z.read(info), mode
        sid = source["id"]
        if sid in self.mirrors:
            clone = str(self.mirrors[sid])
            spec = f"{source['commit']}:{path}"
            data = subprocess.run(["git", "-C", clone, "show", spec], check=True,
                                  capture_output=True).stdout
            tree = subprocess.run(["git", "-C", clone, "ls-tree", source["commit"], "--", path],
                                  check=True, capture_output=True, text=True).stdout.split()
            mode = tree[0] if tree else None
            return data, mode
        if self.offline:
            raise RuntimeError(f"{sid}: no local clone and offline")
        return _download(raw_url(source, path)), None
