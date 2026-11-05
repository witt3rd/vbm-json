ATK_DESC="remove the suite's call from scripts/land-direct (the gate-defining diff is no longer judged by the attacks)"
ATK_GATES=('scripts/relabel-attacks.sh --check-wired'); ATK_GATE_FILES=(scripts/relabel-attacks.sh)
atk_apply() { sed -i '/relabel/d' scripts/land-direct; }
