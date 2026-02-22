"""Shared utilities for skill-governance pre-commit hooks.

Combines the shared-module pattern (from data-engineering-skills) with
v1.3 hook logic (from soc-security-skills): shared-references support,
flat-key budgets, override resolution, and robust classify_file.
"""

import json
import math
import os
import subprocess

TOKEN_RATIO = 1.33
DEFAULT_CEILING = 5500
WARN_THRESHOLD = 0.90


# ---------------------------------------------------------------------------
# Repository helpers
# ---------------------------------------------------------------------------

def find_repo_root():
    """Find the git repository root directory.

    Falls back to walking up looking for pipeline/config/ if git is
    unavailable, then to cwd as last resort.
    """
    try:
        result = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            capture_output=True, text=True, check=True,
        )
        return result.stdout.strip()
    except (subprocess.CalledProcessError, FileNotFoundError):
        pass

    # Fallback: walk up from this script looking for pipeline/config/
    d = os.path.dirname(os.path.abspath(__file__))
    while True:
        if os.path.isdir(os.path.join(d, "pipeline", "config")):
            return d
        parent = os.path.dirname(d)
        if parent == d:
            break
        d = parent

    return os.getcwd()


def load_budgets(repo_root=None):
    """Load budget configuration from pipeline/config/budgets.json."""
    if repo_root is None:
        repo_root = find_repo_root()
    config_path = os.path.join(repo_root, "pipeline", "config", "budgets.json")
    with open(config_path, "r", encoding="utf-8") as f:
        return json.load(f)


def is_excluded(filepath, repo_root=None):
    """Check if a filepath is in an excluded directory."""
    if repo_root is None:
        repo_root = find_repo_root()
    rel_path = os.path.relpath(filepath, repo_root)
    parts = rel_path.replace("\\", "/").split("/")
    excluded_dirs = {"pipeline", "eval-cases", "node_modules", ".github", "templates"}
    for part in parts:
        if part in excluded_dirs:
            return True
    return False


# ---------------------------------------------------------------------------
# File classification (v1.3 -- supports shared-references)
# ---------------------------------------------------------------------------

def classify_file(filepath, repo_root=None):
    """Classify a file as coordinator, specialist, standalone, reference, or skip.

    Supports both ``references/`` and ``shared-references/`` paths.

    Returns one of: 'coordinator', 'specialist', 'standalone', 'reference', 'skip'
    """
    if repo_root is None:
        repo_root = find_repo_root()

    rel_path = os.path.relpath(filepath, repo_root).replace("\\", "/")
    parts = rel_path.split("/")
    basename = os.path.basename(filepath)

    # Excluded paths
    if is_excluded(filepath, repo_root):
        return "skip"

    # Reference files: references/*.md or shared-references/**/*.md
    if "references" in parts or "shared-references" in parts:
        if basename.endswith(".md"):
            return "reference"

    # Only SKILL.md files beyond this point
    if basename != "SKILL.md":
        return "skip"

    skill_dir = os.path.dirname(filepath)

    # Coordinator: SKILL.md with sibling skills/ directory
    if os.path.isdir(os.path.join(skill_dir, "skills")):
        return "coordinator"

    # Specialist: SKILL.md inside a skills/*/ path
    if "skills" in parts:
        return "specialist"

    # Standalone
    return "standalone"


# ---------------------------------------------------------------------------
# Word / token counting
# ---------------------------------------------------------------------------

def count_body_words(filepath):
    """Count words in a markdown file, excluding YAML frontmatter."""
    try:
        with open(filepath, "r", encoding="utf-8") as f:
            content = f.read()
    except (OSError, UnicodeDecodeError):
        return 0

    # Strip YAML frontmatter
    if content.startswith("---"):
        end = content.find("---", 3)
        if end != -1:
            content = content[end + 3:]

    return len(content.split())


def estimate_tokens(word_count_or_filepath):
    """Estimate token count.

    Accepts either an integer word count or a filepath (str path to a file).
    When given a filepath the full file text is used (frontmatter included)
    to match the soc-security context-load behaviour.
    """
    if isinstance(word_count_or_filepath, (int, float)):
        return int(math.ceil(word_count_or_filepath * TOKEN_RATIO))

    # Treat as filepath
    filepath = word_count_or_filepath
    try:
        with open(filepath, "r", encoding="utf-8") as f:
            text = f.read()
    except (OSError, UnicodeDecodeError):
        return 0
    word_count = len(text.split())
    return int(math.ceil(word_count * TOKEN_RATIO))


# ---------------------------------------------------------------------------
# Budget limits (flat-key format with override support)
# ---------------------------------------------------------------------------

def get_budget_for_type(file_type, budgets=None):
    """Get (max_words, max_tokens) for a file classification type.

    Uses flat-key budgets.json format: coordinator_max_words, etc.
    """
    if budgets is None:
        budgets = load_budgets()

    budget_map = {
        "coordinator": ("coordinator_max_words", "coordinator_max_tokens"),
        "specialist": ("specialist_max_words", "specialist_max_tokens"),
        "standalone": ("standalone_max_words", "standalone_max_tokens"),
        "reference": ("reference_max_words", "reference_max_tokens"),
    }

    if file_type not in budget_map:
        return None, None

    words_key, tokens_key = budget_map[file_type]
    return budgets.get(words_key), budgets.get(tokens_key)


def get_budget_limits(rel_path, classification, budgets):
    """Get word and token limits for a file, checking overrides first.

    Overrides can use either the classification-prefixed keys
    (e.g. specialist_max_words) or the shorthand keys (max_words).
    """
    overrides = budgets.get("overrides", {})
    normalized = rel_path.replace("\\", "/")

    if normalized in overrides:
        override = overrides[normalized]
        # Check classification-prefixed keys first, then shorthand
        word_key = f"{classification}_max_words"
        token_key = f"{classification}_max_tokens"
        max_words = override.get(word_key) or override.get("max_words")
        if max_words:
            max_tokens = override.get(token_key) or override.get(
                "max_tokens", int(math.ceil(max_words * TOKEN_RATIO))
            )
            return max_words, max_tokens

    # Fall back to global defaults
    return get_budget_for_type(classification, budgets)


def get_context_ceiling(key, repo_root, budgets):
    """Get the max_simultaneous_tokens ceiling for a suite or specialist.

    Checks for per-specialist override first, then global default.
    key: relative path from repo root (e.g. 'skills/threat-model-skill').
    """
    overrides = budgets.get("overrides", {})
    norm_key = key.replace("\\", "/").rstrip("/")

    if norm_key in overrides and "max_simultaneous_tokens" in overrides[norm_key]:
        return overrides[norm_key]["max_simultaneous_tokens"]

    return budgets.get("max_simultaneous_tokens", DEFAULT_CEILING)
