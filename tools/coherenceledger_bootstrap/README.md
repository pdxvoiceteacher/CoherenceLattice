# coherenceledger bootstrap

This is a minimal, **open-source** bootstrap for:

- `did:key` (Ed25519) identity keys
- signed, hash-chained **append-only** ledgers (JSONL)
- anchoring a UCC `audit_bundle.json` (and optional `report.json`) into the ledger

It is designed to be dropped into the CoherenceLattice repo (under `ucc/` or `python/`) as a first step toward:
- blockchain anchoring of audit bundles
- decentralized identity + verifiable credentials
- ZK-gated actions and voting

## Quick demo

```bash
# from this folder
python -m venv .venv
. .venv/bin/activate   # or Windows: .\.venv\Scripts\activate
pip install -e ".[dev]"

# generate key
python -m coherenceledger keygen --keystore ./keystore.json

# anchor a UCC audit bundle
python -m coherenceledger anchor-ucc \
  --keystore ./keystore.json \
  --ledger ./ledger.jsonl \
  --audit-bundle /path/to/your/audit_bundle.json \
  --report /path/to/your/report.json \
  --repo-root /path/to/CoherenceLattice

# verify ledger
python -m coherenceledger verify --ledger ./ledger.jsonl
```

## Why a file-ledger first?

CoherenceLattice already produces hash-bound `audit_bundle.json` artifacts for reproducibility.
This module adds:
- a DID-signed event wrapper
- a hash-chain that detects tampering
- a clean interface to later *anchor* those seals to an actual blockchain (EVM, Cosmos, or a lattice-native chain).
