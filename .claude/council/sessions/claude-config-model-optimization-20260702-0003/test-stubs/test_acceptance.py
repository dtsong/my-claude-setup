# Generated from acceptance-contract.md (session claude-config-model-optimization-20260702-0003)
# Each stub must fail first (RED). Framework: pytest (repo has no JS test surface).
import json
import os
import subprocess
from pathlib import Path

# parents: [0] test-stubs, [1] session, [2] sessions, [3] council, [4] .claude, [5] repo root
REPO = str(Path(__file__).resolve().parents[5])


def run_dispatcher(env_overrides, args=(), clean=False):
    dispatcher = os.path.join(REPO, "hooks", "telemetry-dispatch.sh")
    if clean:
        env = {"PATH": os.environ["PATH"]}
    else:
        env = {k: v for k, v in os.environ.items() if k != "CLAUDE_TELEMETRY_HOOK"}
    env.update(env_overrides)
    return subprocess.run(
        ["bash", dispatcher, *args],
        env=env, capture_output=True, text=True, timeout=15,
    )


class TestUS001TelemetryDispatcher:
    def _fake_hook(self, tmp_path, body="import sys; print('ran:' + ':'.join(sys.argv[1:]))\n"):
        hook = tmp_path / "fake_telemetry.py"
        hook.write_text(body)
        return hook

    def test_ac_001_dispatcher_env_var_forwarding(self, tmp_path):
        """GIVEN CLAUDE_TELEMETRY_HOOK points to a real file WHEN the dispatcher runs
        THEN it runs python3 on it forwarding args (including args with spaces)."""
        hook = self._fake_hook(tmp_path)
        r = run_dispatcher({"CLAUDE_TELEMETRY_HOOK": str(hook)}, args=("argA", "arg with space"))
        assert r.returncode == 0
        assert r.stdout.strip() == "ran:argA:arg with space"

    def test_ac_001_default_path_resolution(self, tmp_path):
        """GIVEN no env var WHEN the default private-repo hook exists under $HOME
        THEN the dispatcher resolves and runs it (the production path)."""
        hook_dir = tmp_path / "Development" / "my-claude-setup-private" / "hooks"
        hook_dir.mkdir(parents=True)
        (hook_dir / "session_telemetry.py").write_text("print('default-ran')\n")
        r = run_dispatcher({"HOME": str(tmp_path)}, clean=True)
        assert r.returncode == 0
        assert r.stdout.strip() == "default-ran"

    def test_ac_003_missing_default_noop(self, tmp_path):
        """GIVEN the default hook path does not exist (fresh clone, no private repo)
        WHEN the dispatcher runs THEN it exits 0 with no stdout and no stderr."""
        r = run_dispatcher({"HOME": str(tmp_path)}, clean=True)
        assert r.returncode == 0
        assert r.stdout == ""
        assert r.stderr == ""

    def test_ac_003_explicit_env_var_missing_warns(self, tmp_path):
        """GIVEN CLAUDE_TELEMETRY_HOOK is explicitly set to a missing path
        WHEN the dispatcher runs THEN it stays non-blocking (exit 0) but warns on
        stderr: an explicit configuration error is never fully silent."""
        r = run_dispatcher({"CLAUDE_TELEMETRY_HOOK": str(tmp_path / "absent.py")})
        assert r.returncode == 0
        assert r.stdout == ""
        assert "CLAUDE_TELEMETRY_HOOK" in r.stderr

    def test_hook_failure_never_exits_2(self, tmp_path):
        """GIVEN the private hook exits 2 (a blocking code in the hooks protocol)
        WHEN the dispatcher runs THEN it normalizes to exit 1 with contextual stderr,
        so telemetry can never block Claude (worst case would be the Stop event)."""
        hook = self._fake_hook(tmp_path, body="import sys; sys.exit(2)\n")
        r = run_dispatcher({"CLAUDE_TELEMETRY_HOOK": str(hook)})
        assert r.returncode == 1
        assert "exit 2" in r.stderr
        assert "telemetry-dispatch" in r.stderr

    def test_ac_002_settings_wiring(self):
        """GIVEN settings.json WHEN parsed THEN all five telemetry events route
        through the dispatcher and no private-repo path remains in public config."""
        s = json.load(open(os.path.join(REPO, "settings.json")))
        assert "my-claude-setup-private" not in json.dumps(s)
        events = ["SessionStart", "PostToolUse", "PostToolUseFailure", "Stop", "SessionEnd"]
        for ev in events:
            cmds = [h["command"] for e in s["hooks"][ev] for h in e["hooks"]]
            assert any("telemetry-dispatch.sh" in c for c in cmds), f"{ev} not wired"


class TestUS005RoutingTable:
    def test_ac_013_routing_schema_shape(self):
        """GIVEN skills/council/model-routing.json WHEN parsed
        THEN it contains tiers, profiles.max-plan, profiles.api-billed, spawn_sites
        (all required sites), and egress_policy per external destination."""
        raise NotImplementedError("Not implemented - AC-013 pending")

    def test_ac_014_routing_validator(self):
        """GIVEN the routing validator WHEN fed a pinned claude-* ID in a tier slot,
        a spawn site missing a profile entry, or an external destination without
        egress_policy THEN validation fails for each case."""
        raise NotImplementedError("Not implemented - AC-014 pending")


class TestUS006SettingsSchemaGuard:
    HOOK = os.path.join(REPO, "pipeline", "hooks", "check_settings.py")

    def _run(self, target):
        return subprocess.run(
            ["python3", self.HOOK, str(target)],
            capture_output=True, text=True, timeout=15,
        )

    def test_ac_017_settings_schema_hook(self):
        """GIVEN the settings.json schema pre-commit hook WHEN run on current
        settings.json THEN it passes."""
        r = self._run(os.path.join(REPO, "settings.json"))
        assert r.returncode == 0, r.stderr

    def test_ac_018_schema_negative_cases(self, tmp_path):
        """GIVEN fixture settings with (a) pinned claude-* model ID, (b) [1m] suffix,
        (c) absolute private-repo path in a hook command WHEN validated
        THEN the hook fails on each."""
        base = json.load(open(os.path.join(REPO, "settings.json")))

        pinned = dict(base, model="claude-fable-5")
        suffixed = dict(base, model="opus[1m]")
        private = json.loads(json.dumps(base))
        private["hooks"]["Stop"][0]["hooks"][0]["command"] = (
            'python3 "$HOME/Development/my-claude-setup-private/hooks/session_telemetry.py"'
        )
        bare_claude = dict(base, model="claude")
        cases = {"pinned.settings.json": (pinned, "L1"),
                 "bare-claude.settings.json": (bare_claude, "L1"),
                 "suffixed.settings.json": (suffixed, "L2"),
                 "private.settings.json": (private, "L3")}
        for name, (fixture, marker) in cases.items():
            p = tmp_path / name
            p.write_text(json.dumps(fixture, indent=2))
            r = self._run(p)
            assert r.returncode == 1, f"{name} unexpectedly passed"
            assert marker in r.stderr, f"{name}: expected {marker} finding, got: {r.stderr}"

    def test_malformed_hooks_shape_fails_cleanly(self, tmp_path):
        """GIVEN hooks with the wrong shape (list instead of dict, non-dict entries)
        WHEN validated THEN the hook exits 1 with gate findings, never a traceback."""
        base = json.load(open(os.path.join(REPO, "settings.json")))
        for name, hooks_value in {
            "hooks-list.settings.json": ["not", "a", "dict"],
            "hooks-strentry.settings.json": {"Stop": ["not-a-dict-entry"]},
        }.items():
            p = tmp_path / name
            p.write_text(json.dumps(dict(base, hooks=hooks_value), indent=2))
            r = self._run(p)
            assert r.returncode == 1, f"{name} unexpectedly passed"
            assert "Traceback" not in r.stderr, f"{name} crashed: {r.stderr}"
            assert "failed the staging gate" in r.stderr
