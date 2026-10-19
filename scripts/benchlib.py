"""Shared code of the benchmark scripts: the manifest, the models' ids and where their files go.

Every script runs with `python3 -I` from any directory; paths are resolved from this file.
"""

import hashlib
import json
import os
import re
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MODELS = ROOT / "models"
MANIFEST = MODELS / "manifest.toml"
CACHE = ROOT / "cache"
RESULTS = ROOT / "results"
PROOFS = ROOT / "proofs"
RUNS = ROOT / "runs"
BENCH = ROOT / "Bench"
CONFIG = ROOT / "bench.local.toml"  # gitignored: local settings such as the proof backup directory

# Kinds of manifest entry that get a directory under models/ (with an id).
RUN_KINDS = ("model",)


# --------------------------------------------------------------------------------------------
# The manifest
# --------------------------------------------------------------------------------------------

def load_manifest(path=MANIFEST):
    with open(path, "rb") as f:
        return tomllib.load(f)


# Keys whose value is an array of tables ([[...]]); every other list of tables is written inline.
_ARRAY_TABLES = {"paper", "source", "model", "tamarin_ci"}


def _toml_str(s):
    out = ['"']
    for ch in s:
        if ch == '"':
            out.append('\\"')
        elif ch == "\\":
            out.append("\\\\")
        elif ch == "\n":
            out.append("\\n")
        elif ch == "\t":
            out.append("\\t")
        elif ch == "\r":
            out.append("\\r")
        elif ord(ch) < 0x20 or ord(ch) == 0x7F:
            out.append("\\u%04x" % ord(ch))
        else:
            out.append(ch)
    out.append('"')
    return "".join(out)


def _toml_key(k):
    return k if re.fullmatch(r"[A-Za-z0-9_-]+", k) else _toml_str(k)


def _toml_value(v):
    if isinstance(v, bool):
        return "true" if v else "false"
    if isinstance(v, int):
        return str(v)
    if isinstance(v, float):
        return repr(v)
    if isinstance(v, str):
        return _toml_str(v)
    if isinstance(v, dict):
        return "{ " + ", ".join(f"{_toml_key(k)} = {_toml_value(x)}" for k, x in v.items()) + " }"
    if isinstance(v, list):
        return "[" + ", ".join(_toml_value(x) for x in v) + "]"
    raise TypeError(f"cannot write {type(v)} to TOML")


def _emit_table(lines, table, prefix):
    subtables = []
    for k, v in table.items():
        if k in _ARRAY_TABLES and isinstance(v, list) and v and all(isinstance(r, dict) for r in v):
            subtables.append((k, v))
        else:
            lines.append(f"{_toml_key(k)} = {_toml_value(v)}")
    for k, rows in subtables:
        name = f"{prefix}.{k}" if prefix else k
        for row in rows:
            lines.append("")
            lines.append(f"[[{name}]]")
            _emit_table(lines, row, name)


def dump_manifest(m, path=MANIFEST, header=()):
    """Write the manifest back, in the layout it was generated with, after the header lines."""
    lines = [f"# {h}" if h else "#" for h in header]
    for k, v in m.items():
        if k in _ARRAY_TABLES:
            continue
        lines.append("")
        lines.append(f"[{k}]")
        _emit_table(lines, v, k)
    for k in ("paper", "source"):
        for row in m.get(k, []):
            lines.append("")
            lines.append(f"[[{k}]]")
            _emit_table(lines, row, k)
    text = "\n".join(lines) + "\n"
    tomllib.loads(text)  # never write a manifest that does not read back
    Path(path).write_text(text, encoding="utf-8")


MANIFEST_HEADER = (
    "The benchmark's models and the papers they belong to.",
    "",
    "Each [[source]] is a repository at a pinned commit or an archive pinned by its sha256; each",
    "[[source.model]] is one of its .spthy files.  An entry with an `id` is a model of the",
    "benchmark: models/<id>/ holds its SOURCE.txt, and its files (`files`, each with its sha256)",
    "are copied there when the source's license allows redistribution, or fetched into cache/<id>/",
    "by scripts/fetch_models.py otherwise.  Stored proofs, generated targets and variants that do",
    "not terminate are listed without an id.  `tamarin_args` are the flags Tamarin runs the model",
    "with (scripts/run_tamarin.py), and `lean_scope` says whether the Lean side runs it.",
    "Reported times are the authors' or Tamarin's own CI's; our measurements are in results/.",
    "The [meta].fields entry describes the remaining fields.",
)


def papers_by_key(m):
    return {p["key"]: p for p in m["paper"]}


def iter_models(m, with_id=True):
    """(source, model) for every model of the benchmark (every entry with an id)."""
    for s in m["source"]:
        for x in s.get("model", []):
            if with_id and "id" not in x:
                continue
            yield s, x


def model_by_id(m):
    return {x["id"]: (s, x) for s, x in iter_models(m)}


# --------------------------------------------------------------------------------------------
# Files
# --------------------------------------------------------------------------------------------

def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def sha256_bytes(b):
    return hashlib.sha256(b).hexdigest()


def model_home(source, model):
    """The directory that holds the model's files: models/<id>/ when the files may be
    redistributed, cache/<id>/ otherwise.  SOURCE.txt is always in models/<id>/."""
    return (MODELS if model["redistributable"] else CACHE) / model["id"]


def model_entry(model):
    for f in model["files"]:
        if f["role"] == "model":
            return f
    raise KeyError(f"{model['id']}: no file with role 'model'")


def model_path(source, model):
    """The model's .spthy file, where the scripts expect it."""
    return model_home(source, model) / model_entry(model)["dest"]


def workdir(source, model):
    """The directory Tamarin runs the model in: the model file's own directory, so that the
    relative paths of its oracle and its includes resolve as in the source."""
    return model_path(source, model).parent


def is_diff(model):
    return bool(model.get("diff"))


def lean_in_scope(model):
    return model.get("lean_scope", "").startswith("trace")


def id_to_filename(model_id):
    """A model's id as one file name (for flat directories such as runs/)."""
    return model_id.replace("/", "__")


# --------------------------------------------------------------------------------------------
# Results
# --------------------------------------------------------------------------------------------

def results_path(tool, model_id):
    return RESULTS / tool / f"{model_id}.json"


def load_result(tool, model_id):
    p = results_path(tool, model_id)
    if p.exists():
        return json.loads(p.read_text(encoding="utf-8"))
    return None


def scrub_paths(obj):
    """`obj` without this machine's paths: the checkout's own path is dropped (paths in it are
    relative to the repository) and the home directory becomes `~`.  Results are committed."""
    if isinstance(obj, str):
        return obj.replace(str(ROOT) + os.sep, "").replace(str(Path.home()), "~")
    if isinstance(obj, list):
        return [scrub_paths(v) for v in obj]
    if isinstance(obj, dict):
        return {k: scrub_paths(v) for k, v in obj.items()}
    return obj


def write_json(path, data):
    path = Path(path)
    if RESULTS in path.parents:
        data = scrub_paths(data)
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    os.replace(tmp, path)


def local_config():
    """Settings that differ per machine (bench.local.toml, not committed), overridden by the
    environment: BENCH_PROOF_BACKUP (where Tamarin's proofs are copied), BENCH_PYTHON2 (a Python 2
    interpreter for the oracles written for Python 2)."""
    cfg = {}
    if CONFIG.exists():
        with open(CONFIG, "rb") as f:
            cfg = tomllib.load(f)
    for key, env in (("proof_backup", "BENCH_PROOF_BACKUP"), ("python2", "BENCH_PYTHON2")):
        if os.environ.get(env):
            cfg[key] = os.environ[env]
    return cfg


def backup_proofs(model_id):
    """Copy proofs/<id>/ to the backup directory (bench.local.toml `proof_backup`, or the
    environment variable BENCH_PROOF_BACKUP), when one is set."""
    import shutil
    dest = local_config().get("proof_backup")
    src = PROOFS / model_id
    if not dest or not src.exists():
        return False
    d = Path(dest) / model_id
    d.mkdir(parents=True, exist_ok=True)
    for f in src.iterdir():
        if f.is_file():
            shutil.copy2(f, d / f.name)
    return True
