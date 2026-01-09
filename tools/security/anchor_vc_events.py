from __future__ import annotations
import json
from pathlib import Path
import os

from coherenceledger.schemas import LedgerEvent
from coherenceledger.ledger import Ledger
from coherenceledger.keystore import KeyStore
from coherenceledger.crypto import b64encode

from ucc.vc_issuer import vc_sha256


def main() -> int:
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--ledger", default=os.getenv("COHERENCELEDGER_LEDGER", "ledger.jsonl"))
    ap.add_argument("--keystore", default=os.getenv("COHERENCELEDGER_KEYSTORE", ".secrets/coherenceledger_keystore.json"))
    ap.add_argument("--vc", help="Path to VC JSON (for issue anchoring)")
    ap.add_argument("--revoke", help="VC id to revoke")
    ap.add_argument("--reason", default="revoked")
    args = ap.parse_args()

    ledger_path = Path(args.ledger)
    keystore_path = Path(args.keystore)

    led = Ledger(path=ledger_path)
    led.verify()

    ks = KeyStore(path=keystore_path)
    did, kp = ks.load_keypair()

    if args.vc:
        vc = json.loads(Path(args.vc).read_text(encoding="utf-8-sig"))
        payload = {
            "artifact_type":"ucc.identity.vc",
            "vc_id": vc["id"],
            "vc_sha256": vc_sha256(vc),
            "issuer_did": vc["issuer"],
            "subject_did": (vc.get("credentialSubject") or {}).get("id",""),
            "types": vc.get("type", []),
        }
        ev = LedgerEvent.create_unsigned(actor_did=did.did, purpose="identity.vc.issue", event_type="identity.vc.issue", payload=payload, prev_seal=led.last_seal())
        sig = kp.sign(ev.signing_payload())
        ev.signature = b64encode(sig)
        ev.public_key_b64 = b64encode(kp.public_bytes_raw())
        led.append(ev)
        led.verify()
        print(f"Anchored VC issue: {vc['id']}")
        return 0

    if args.revoke:
        payload = {"artifact_type":"ucc.identity.vc", "vc_id": args.revoke, "reason": args.reason}
        ev = LedgerEvent.create_unsigned(actor_did=did.did, purpose="identity.vc.revoke", event_type="identity.vc.revoke", payload=payload, prev_seal=led.last_seal())
        sig = kp.sign(ev.signing_payload())
        ev.signature = b64encode(sig)
        ev.public_key_b64 = b64encode(kp.public_bytes_raw())
        led.append(ev)
        led.verify()
        print(f"Anchored VC revoke: {args.revoke}")
        return 0

    raise SystemExit("Provide --vc or --revoke")

if __name__ == "__main__":
    raise SystemExit(main())
