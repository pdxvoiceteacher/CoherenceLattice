import re
from pathlib import Path

p = Path(".github/workflows/coherenceledger.yml")
txt = p.read_text(encoding="utf-8").replace("\r\n", "\n").replace("\r", "\n")
lines = txt.split("\n")

out = []
i = 0
while i < len(lines):
    ln = lines[i]
    # remove empty list-item lines
    if re.match(r"^\s*-\s*$", ln):
        i += 1
        continue

    m = re.match(r"^(\s*)-\s+name:\s*(.+)\s*$", ln)
    if not m:
        out.append(ln)
        i += 1
        continue

    step_indent = len(m.group(1))
    out.append(ln)
    i += 1

    block = []
    while i < len(lines):
        ln2 = lines[i]
        if ln2.strip() == "":
            block.append(ln2); i += 1; continue
        ind2 = len(re.match(r"^\s*", ln2).group(0))
        if ind2 <= step_indent and re.match(r"^\s*-\s+", ln2):
            break
        if ind2 <= step_indent and re.match(r"^\S", ln2):
            break
        block.append(ln2); i += 1

    has_action = any(re.match(r"^\s*(run|uses):\s*", b) for b in block)
    if not has_action:
        block.append(" " * (step_indent + 2) + 'run: echo "noop"')

    out.extend(block)

p.write_text("\n".join(out).rstrip("\n") + "\n", encoding="utf-8", newline="\n")
print("OK")
