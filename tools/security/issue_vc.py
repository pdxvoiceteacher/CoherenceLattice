from __future__ import annotations
import json
from pathlib import Path
import os

from ucc.vc_issuer import issue_vc
from ucc.vc_registry import load_registry, save_registry, add_vc


def main() -> int:
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--subject-did", required=True)
    ap.add_argument("--type", action="append", required=True, help="Credential type(s), e.g. MemberCredential")
    ap.add_argument("--claims", default="{}", help="JSON object with subject claims")
    ap.add_argument("--registry", default="governance/identity/vc_registry.json")
    ap.add_argument("--out", default=None)
    ap.add_argument("--keystore", default=os.getenv("COHERENCELEDGER_KEYSTORE", ".secrets/coherenceledger_keystore.json"))
    args = ap.parse_args()

    ks = Path(args.keystore)
    issuer_did = os.getenv("UCC_ISSUER_DID", None)
    if not issuer_did:
        # reuse keystore DID
        from coherenceledger.keystore import KeyStore
        did, _ = KeyStore(path=ks).load_keypair()
        issuer_did = did.did

    claims = json.loads(args.claims)

    vc = issue_vc(
        issuer_did=issuer_did,
        subject_did=args.subject_did,
        types=args.type,
        subject_claims=claims,
        keystore_path=ks,
    )

    reg_path = Path(args.registry)
    reg = load_registry(reg_path)
    add_vc(reg, vc)
    save_registry(reg_path, reg)

    out_path = Path(args.out) if args.out else (reg_path.parent / f"vc_{vc['id'].replace(':','_')}.json")
    out_path.write_text(json.dumps(vc, indent=2, sort_keys=True, ensure_ascii=False) + "\n", encoding="utf-8", newline="\n")
    print(f"Wrote VC: {out_path}")
    print(f"Registry updated: {reg_path}")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
