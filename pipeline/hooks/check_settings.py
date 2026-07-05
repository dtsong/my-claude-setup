#!/usr/bin/env python3
"""Pre-commit guard for settings.json (issue #64, AC-017/AC-018).

settings.json is live production config (symlinked to ~/.claude/settings.json),
so a malformed edit breaks the running harness with no staging. This hook is
the staging gate: structural validation against pipeline/config/settings.schema.json
via a built-in minimal validator (no external deps), plus governance lint rules:

  L1  model must be a tier alias (opus|sonnet|haiku|fable|claude), never a pinned claude-* ID
  L2  no "[1m]" context suffix anywhere (conflicts with CLAUDE_CODE_DISABLE_1M_CONTEXT)
  L3  no my-claude-setup-private paths in hook commands (fresh clones must not break)

Exit 0 on pass, 1 with findings on stderr.
"""

import json
import os
import re
import sys

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SCHEMA_PATH = os.path.join(REPO, "pipeline", "config", "settings.schema.json")


def validate(instance, schema, path="$"):
    """Minimal JSON-Schema subset validator: type, required, properties,
    patternProperties, additionalProperties, items, pattern, enum."""
    errors = []
    stype = schema.get("type")
    typemap = {"object": dict, "array": list, "string": str, "number": (int, float), "boolean": bool}
    if stype and not isinstance(instance, typemap[stype]):
        return [f"{path}: expected {stype}, got {type(instance).__name__}"]
    if isinstance(instance, bool) and stype == "number":
        return [f"{path}: expected number, got boolean"]

    if stype == "object":
        for key in schema.get("required", []):
            if key not in instance:
                errors.append(f"{path}: missing required key '{key}'")
        props = schema.get("properties", {})
        pattern_props = schema.get("patternProperties", {})
        for key, value in instance.items():
            subschema = None
            if key in props:
                subschema = props[key]
            else:
                for pat, ps in pattern_props.items():
                    if re.match(pat, key):
                        subschema = ps
                        break
            if subschema is not None:
                errors.extend(validate(value, subschema, f"{path}.{key}"))
            elif schema.get("additionalProperties") is False and (props or pattern_props):
                errors.append(f"{path}: unexpected key '{key}'")
    elif stype == "array":
        item_schema = schema.get("items")
        if item_schema:
            for i, item in enumerate(instance):
                errors.extend(validate(item, item_schema, f"{path}[{i}]"))
    elif stype == "string":
        pat = schema.get("pattern")
        if pat and not re.match(pat, instance):
            errors.append(f"{path}: '{instance}' does not match {pat}")
    if "enum" in schema and instance not in schema["enum"]:
        errors.append(f"{path}: '{instance}' not in {schema['enum']}")
    return errors


TIER_ALIASES = {"opus", "sonnet", "haiku", "fable"}


def lint(settings, raw):
    errors = []
    model = settings.get("model")
    if isinstance(model, str) and model not in TIER_ALIASES:
        errors.append(f"L1 model: '{model}' is not a tier alias; use one of {sorted(TIER_ALIASES)} (pinned IDs and bare 'claude' forbidden)")
    if "[1m]" in raw:
        errors.append("L2: '[1m]' suffix present; conflicts with CLAUDE_CODE_DISABLE_1M_CONTEXT stance")
    hooks = settings.get("hooks")
    for event, entries in (hooks.items() if isinstance(hooks, dict) else []):
        for entry in (entries if isinstance(entries, list) else []):
            if not isinstance(entry, dict):
                continue
            inner = entry.get("hooks")
            for hook in (inner if isinstance(inner, list) else []):
                if isinstance(hook, dict) and "my-claude-setup-private" in hook.get("command", ""):
                    errors.append(f"L3 hooks.{event}: private-repo path in command; route through hooks/telemetry-dispatch.sh")
    return errors


def check_file(path, schema_path=SCHEMA_PATH):
    try:
        raw = open(path, encoding="utf-8").read()
        settings = json.loads(raw)
    except (OSError, json.JSONDecodeError) as exc:
        return [f"{path}: unreadable or invalid JSON ({exc})"]
    schema = json.load(open(schema_path, encoding="utf-8"))
    return [f"{path}: {e}" for e in validate(settings, schema) + lint(settings, raw)]


def main(argv):
    targets = [a for a in argv if a.endswith("settings.json")] or [os.path.join(REPO, "settings.json")]
    findings = []
    for t in targets:
        findings.extend(check_file(t))
    if findings:
        print("check_settings: settings.json failed the staging gate:", file=sys.stderr)
        for f in findings:
            print(f"  - {f}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
