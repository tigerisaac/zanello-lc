#!/bin/zsh
# Shadow-compile the FormalDeps homological port against this project's Mathlib.
#
# The files keep their upstream `Mathlib.*` module names, so they are compiled
# with a LEAN_PATH "shadow" tree: a clone of Mathlib's compiled olean tree in
# which the ported oleans overwrite their stock counterparts. Run from the
# repository root after `lake build` (or `lake exe cache get`):
#
#   zsh FormalDeps/shadowbuild.sh
set -u
REPO=${0:a:h:h}
PORT=$REPO/FormalDeps
SHADOW=${SHADOW:-/tmp/leanproof-shadowmath}
cd "$REPO"

if [ ! -d "$SHADOW/Mathlib" ]; then
  echo "Seeding shadow olean tree at $SHADOW (APFS clone)..."
  mkdir -p "$SHADOW"
  cp -Rc .lake/packages/mathlib/.lake/build/lib/lean/Mathlib "$SHADOW/"
fi
BASE_LEAN_PATH=$(lake env printenv LEAN_PATH)

# Dependency order. The last four files are not yet ported (see README.md).
FILES=(
  Mathlib/Algebra/Category/ModuleCat/Baer.lean
  Mathlib/RingTheory/Regular/Category.lean
  Mathlib/RingTheory/Regular/Depth.lean
  Mathlib/RingTheory/Regular/Ischebeck.lean
  Mathlib/RingTheory/Regular/AuslanderBuchsbaum.lean
  Mathlib/RingTheory/GlobalDimension.lean
  Mathlib/RingTheory/CohenMacaulay/Basic.lean
  Mathlib/RingTheory/RegularLocalRing/Basic.lean
  Mathlib/RingTheory/CohenMacaulay/Maximal.lean
  Mathlib/RingTheory/RegularLocalRing/GlobalDimension.lean
  Mathlib/RingTheory/RegularLocalRing/RegularRing/Basic.lean
  Mathlib/RingTheory/RegularLocalRing/RegularRing/Polynomial.lean
  Mathlib/RingTheory/RegularLocalRing/RegularRing/GlobalDimension.lean
  Mathlib/RingTheory/RegularLocalRing/RegularRing/Syzygy.lean
)

fails=0
for f in "${FILES[@]}"; do
  out="$SHADOW/${f%.lean}.olean"
  mkdir -p "$(dirname "$out")"
  if LEAN_PATH="$SHADOW:$BASE_LEAN_PATH" lean -R "$PORT" -o "$out" "$PORT/$f" 2>&1; then
    echo "PASS  $f"
  else
    echo "FAIL  $f"
    fails=$((fails + 1))
  fi
done
echo "done ($fails failures)"
exit $(( fails > 0 ))
