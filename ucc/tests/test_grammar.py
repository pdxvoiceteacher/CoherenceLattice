from __future__ import annotations

from pathlib import Path

from ucc.models import load_uccmodule_json
from ucc.validate_grammar import validate_basic_structure, check_authority_alignment
from ucc.evaluate_grammar import quick_heuristic_score, to_dict
from ucc.executor_grammar import UCCExecutor


def test_load_and_validate_examples():
    repo = Path(__file__).resolve().parents[1]
    m = load_uccmodule_json(repo / "examples" / "coso_lm2_treasurer_memo.json")
    validate_basic_structure(m)
    warnings = check_authority_alignment(m)
    assert isinstance(warnings, list)


def test_scorecard_runs():
    repo = Path(__file__).resolve().parents[1]
    m = load_uccmodule_json(repo / "examples" / "prisma_abstract.json")
    scores = quick_heuristic_score(m)
    d = to_dict(scores)
    # all keys exist and are bounded
    for k in ["alignment","robustness","clarity","safety_escalation","usability","governance","total"]:
        assert k in d
    assert 0 <= d["alignment"] <= 5


def test_executor_dummy():
    repo = Path(__file__).resolve().parents[1]
    m = load_uccmodule_json(repo / "examples" / "prisma_abstract.json")

    def dummy_llm(prompt: str, ctx: dict) -> str:
        return "[DUMMY RESPONSE]"

    ex = UCCExecutor(m, llm_fn=dummy_llm)
    out = ex.run("Summarize a systematic review on X.", extra_context={"note": "test"})
    assert "outline" in out and "final_text" in out