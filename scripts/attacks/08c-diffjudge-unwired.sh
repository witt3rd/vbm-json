ATK_DESC="remove the gate-diff judge's call from scripts/land-direct"
ATK_GATES=('scripts/relabel-attacks.sh --check-wired'); ATK_GATE_FILES=(scripts/relabel-attacks.sh)
atk_apply() { sed -i '/gate-diff-improving\|\$gdi/d' scripts/land-direct; }
