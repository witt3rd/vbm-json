ATK_DESC="add LeanJson/ to the none: line of scripts/tests-map.txt (a change to the library selects no test)"
ATK_GATES=('scripts/gate-diff-improving.sh --suite-judged "$ATK_BASE" HEAD'); ATK_GATE_FILES=(scripts/gate-diff-improving.sh)
atk_apply() { sed -i 's#^none:#none: LeanJson/#' scripts/tests-map.txt; }
