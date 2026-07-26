#!/bin/sh
# Verify the FormalDeps port against the upstream commit it claims to come
# from, by comparing the *statements* of every theorem and lemma present in
# both.  Proofs necessarily differ (the port was adapted to Lean/Mathlib
# v4.31 APIs); statements must not.
#
#   sh FormalDeps/verify-port.sh
#
# Requires curl and python3, and network access to raw.githubusercontent.com.
# Exits nonzero if any shared statement differs.
set -eu

UPSTREAM_REPO=${UPSTREAM_REPO:-Thmoas-Guan/mathlib4_fork}
UPSTREAM_REV=${UPSTREAM_REV:-0ff6e01f56}
ROOT=$(cd "$(dirname "$0")/.." && pwd)
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

echo "comparing FormalDeps/Port against $UPSTREAM_REPO@$UPSTREAM_REV"

cd "$ROOT"
for rel in $(cd FormalDeps/Port && find Mathlib -name '*.lean' | sort); do
  flat=$(echo "$rel" | tr '/' '_')
  url="https://raw.githubusercontent.com/$UPSTREAM_REPO/$UPSTREAM_REV/$rel"
  if ! curl -sSf -o "$WORK/$flat" "$url"; then
    echo "could not fetch $rel from upstream"
    exit 1
  fi
done

python3 - "$ROOT" "$WORK" <<'PY'
import glob, os, re, sys

root, work = sys.argv[1], sys.argv[2]

def statements(path):
    """Map declaration name -> statement text (everything before ':=')."""
    text = re.sub(r'/-.*?-/', '', open(path).read(), flags=re.S)
    decl = re.compile(
        r'^(?:private |protected |noncomputable )*(?:theorem|lemma) '
        r'([A-Za-z_][\w.\'₀-₉]*)', re.M)
    out = {}
    for m in decl.finditer(text):
        head = re.split(r':=', text[m.start():m.start() + 4000], maxsplit=1)[0]
        out[m.group(1)] = re.sub(r'\s+', ' ', head).strip()
    return out

# Differences that are known to be pure name resolution, not mathematics.
# Each entry is (declaration name, reason).  Anything not listed here fails.
ALLOWED = {
    'Submodule.smul_top_eq_comap_smul_top_of_surjective':
        'writes `_root_.Submodule.comap` where upstream writes `comap`; '
        'the two resolve to the same constant',
}

compared = differing = 0
for port in sorted(glob.glob(os.path.join(
        root, 'FormalDeps/Port/Mathlib/**/*.lean'), recursive=True)):
    rel = os.path.relpath(port, os.path.join(root, 'FormalDeps/Port'))
    up = os.path.join(work, rel.replace('/', '_'))
    if not os.path.exists(up):
        continue
    a, b = statements(up), statements(port)
    for name in sorted(set(a) & set(b)):
        compared += 1
        if a[name] != b[name]:
            if name in ALLOWED:
                print(f'known    {rel}  {name}: {ALLOWED[name]}')
                continue
            differing += 1
            print(f'DIFFERS  {rel}  {name}')
            print(f'  upstream: {a[name]}')
            print(f'  port    : {b[name]}')
    dropped = sorted(set(a) - set(b))
    added = sorted(set(b) - set(a))
    if dropped:
        print(f'note: {rel}: not carried over: {" ".join(dropped)}')
    if added:
        print(f'ADDED    {rel}: {" ".join(added)}')
        differing += len(added)

print(f'compared {compared} shared statements; {differing} differ')
sys.exit(1 if differing else 0)
PY
