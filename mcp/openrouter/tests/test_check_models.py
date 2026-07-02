"""Tests for check_models.py (issue #62): no network, live_ids is monkeypatched."""

import check_models


def test_referenced_ids_collects_tasks_and_lenses_skips_sentinel():
    routing = {
        "tasks": {"classification": "openai/gpt-5.4-nano", "scoring": "claude"},
        "lenses": {"scout": "google/gemini-3.5-flash"},
    }
    assert check_models.referenced_ids(routing) == {
        "openai/gpt-5.4-nano",
        "google/gemini-3.5-flash",
    }


def test_main_missing_routing_table_exits_1(monkeypatch, capsys):
    monkeypatch.setattr(check_models, "load_routing", lambda: {})
    assert check_models.main() == 1
    assert "missing or invalid" in capsys.readouterr().err


def test_main_no_referenced_ids_exits_0(monkeypatch, capsys):
    monkeypatch.setattr(check_models, "load_routing",
                        lambda: {"tasks": {"scoring": "claude"}, "defaults": {"fallback": "claude"}})
    assert check_models.main() == 0
    assert "nothing to verify" in capsys.readouterr().out


def test_main_network_failure_exits_1(monkeypatch, capsys):
    monkeypatch.setattr(check_models, "load_routing",
                        lambda: {"tasks": {"classification": "openai/gpt-5.4-nano"}})

    def boom(**kwargs):
        raise OSError("network down")

    monkeypatch.setattr(check_models, "live_ids", boom)
    assert check_models.main() == 1
    assert "IDs unverified" in capsys.readouterr().err


def test_main_stale_id_exits_1_and_lists_it(monkeypatch, capsys):
    monkeypatch.setattr(check_models, "load_routing",
                        lambda: {"tasks": {"classification": "vendor/retired-model"}})
    monkeypatch.setattr(check_models, "live_ids", lambda **kw: {"vendor/current-model"})
    assert check_models.main() == 1
    assert "vendor/retired-model" in capsys.readouterr().err


def test_main_all_live_exits_0(monkeypatch, capsys):
    monkeypatch.setattr(check_models, "load_routing",
                        lambda: {"tasks": {"classification": "openai/gpt-5.4-nano"}})
    monkeypatch.setattr(check_models, "live_ids", lambda **kw: {"openai/gpt-5.4-nano"})
    assert check_models.main() == 0
    assert "all 1 referenced IDs are live" in capsys.readouterr().out
