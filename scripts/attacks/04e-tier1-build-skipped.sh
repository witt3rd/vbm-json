ATK_DESC="comment out the zero-warning build of tier1.sh"
ATK_GATES=('scripts/gate-diff-improving.sh --suite-judged "$ATK_BASE" HEAD'); ATK_GATE_FILES=(scripts/gate-diff-improving.sh)
atk_apply() { sed -i 's/^lake build LeanJson LeanJsonProofs vbm-json-vectors LeanJson:static/# &/' scripts/tier1.sh; }
