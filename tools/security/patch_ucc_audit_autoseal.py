from __future__ import annotations

import re
from pathlib import Path

TARGET = Path("ucc/src/ucc/audit.py")

MARKER = "COHERENCELEDGER_AUTOSEAL"

BLOCK = r"""
# {MARKER}: optional ledger anchoring (env-gated, cross-platform)
import os
if os.getenv("COHERENCELEDGER_ENABLE", "").lower() in {"1","true","yes"}:
    strict = os.getenv("COHERENCELEDGER_STRICT", "").lower() in {"1","true","yes"}
    try:
        from pathlib import Path
        from coherenceledger.anchor import anchor_ucc_audit_bundle
    except Exception as e:
        if strict:
            raise
        try:
            import logging
            logging.getLogger(__name__).warning("coherenceledger unavailable; skipping auto-seal: %s", e)
        except Exception:
            pass
    else:
        # repo root inferred from this file's location: CoherenceLattice/ucc/src/ucc/audit.py
        repo_root = Path(__file__).resolve().parents[3]
        keystore = Path(os.getenv(
            "COHERENCELEDGER_KEYSTORE",
            str(repo_root / ".secrets" / "coherenceledger_keystore.json")
        ))
        ledger = Path(os.getenv(
            "COHERENCELEDGER_LEDGER",
            str(repo_root / "ledger.jsonl")
        ))
        purpose = os.getenv("COHERENCELEDGER_PURPOSE", "ucc.audit.anchor")

        if not keystore.exists():
            if strict:
                raise FileNotFoundError(f"CoherenceLedger keystore not found: {keystore}")
            try:
                import logging
                logging.getLogger(__name__).warning("CoherenceLedger keystore missing; skipping auto-seal: %s", keystore)
            except Exception:
                pass
        else:
            try:
                ledger.parent.mkdir(parents=True, exist_ok=True)
                report_path = outdir / "report.json"
                report_arg = report_path if report_path.exists() else None
                # 'path' is the audit_bundle.json path in this function
                anchor_ucc_audit_bundle(
                    ledger_path=ledger,
                    keystore_path=keystore,
                    audit_bundle_path=path,
                    report_json_path=report_arg,
                    repo_root=repo_root,
                    purpose=purpose,
                )
            except Exception as e:
                if strict:
                    raise
                try:
                    import logging
                    logging.getLogger(__name__).warning("CoherenceLedger auto-seal failed; continuing: %s", e)
                except Exception:
                    pass
""".strip("\n")


def main() -> None:
    if not TARGET.exists():
        raise SystemExit(f"Target not found: {TARGET}")

    txt = TARGET.read_text(encoding="utf-8")
    if MARKER in txt:
        print("Already patched (marker present).")
        return

    lines = txt.splitlines(True)

    # Find the line defining the audit bundle path
    idx = None
    for i, line in enumerate(lines):
        if 'outdir / "audit_bundle.json"' in line:
            idx = i
            break
    if idx is None:
        raise SystemExit("Could not find the audit_bundle.json path line.")

    indent = re.match(r"\s*", lines[idx]).group(0)

    # Find the first 'return' at the same indentation level after that line
    insert_at = None
    for j in range(idx + 1, len(lines)):
        if lines[j].startswith(indent) and re.match(rf"{re.escape(indent)}return\b", lines[j]):
            insert_at = j
            break
    if insert_at is None:
        raise SystemExit("Could not find insertion point (no return at same indent after audit_bundle line).")

    block = "\n" + "\n".join(indent + ln if ln else ln for ln in BLOCK.format(MARKER=MARKER).splitlines()) + "\n\n"
    lines.insert(insert_at, block)

    TARGET.write_text("".join(lines), encoding="utf-8")
    print("Patched ucc/src/ucc/audit.py with COHERENCELEDGER_AUTOSEAL hook.")


if __name__ == "__main__":
    main()
