from __future__ import annotations

from typing import Callable, Dict, Any, Optional

from .models import UCCModule


class UCCExecutor:
    """
    Thin runtime executor skeleton (“grammar executor”).

    It does not bind to any provider; it only expects an llm_fn:
        (prompt: str, ctx: dict) -> str
    """
    def __init__(self, module: UCCModule, llm_fn: Callable[[str, Dict[str, Any]], str]):
        self.module = module
        self.llm_fn = llm_fn

    def build_outline_prompt(self, user_input: str, extra_context: Optional[Dict[str, Any]] = None) -> str:
        m = self.module
        extra_context = extra_context or {}
        sections = "\n".join([f"- {s}" for s in m.reporting.sections])
        steps = "\n".join([f"{i+1}. {s}" for i, s in enumerate(m.reasoning_steps)])

        return (
            f"UCC MODULE: {m.meta.module_id} ({m.meta.version})\\n"
            f"TITLE: {m.meta.name}\\n"
            f"DOMAIN: {', '.join(m.meta.domain)}\\n"
            f"JURISDICTION: {', '.join(m.meta.jurisdiction)}\\n\\n"
            f"USER INPUT:\\n{user_input}\\n\\n"
            f"REQUIRED REASONING STEPS (do not skip/reorder):\\n{steps}\\n\\n"
            f"REQUIRED OUTPUT SECTIONS (in order):\\n{sections}\\n\\n"
            f"CONTEXT (machine): {extra_context}\\n\\n"
            "TASK: Produce an outline that includes all required sections, and note any missing evidence needed."
        )

    def build_final_prompt(self, outline: str, user_input: str, extra_context: Optional[Dict[str, Any]] = None) -> str:
        m = self.module
        extra_context = extra_context or {}
        disclaimers = "\\n".join([f"- {d}" for d in m.reporting.disclaimers]) if m.reporting.disclaimers else "- (none)"

        return (
            f"UCC MODULE: {m.meta.module_id} ({m.meta.version})\\n"
            f"TITLE: {m.meta.name}\\n\\n"
            f"USER INPUT:\\n{user_input}\\n\\n"
            f"OUTLINE:\\n{outline}\\n\\n"
            f"CONTEXT (machine): {extra_context}\\n\\n"
            "TASK: Write the final text following the outline.\\n"
            f"APPEND REQUIRED DISCLAIMERS:\\n{disclaimers}\\n"
        )

    def run(self, user_input: str, extra_context: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
        ctx = extra_context or {}
        outline_prompt = self.build_outline_prompt(user_input, ctx)
        outline = self.llm_fn(outline_prompt, ctx)

        final_prompt = self.build_final_prompt(outline, user_input, ctx)
        final_text = self.llm_fn(final_prompt, ctx)

        return {"outline": outline, "final_text": final_text}