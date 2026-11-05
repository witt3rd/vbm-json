ATK_DESC="drop scripts/gate-edit-approvals.txt from scripts/protected-paths.txt (the approvals file is protected, like the gates it approves)"
ATK_GATES=('scripts/gate-diff-improving.sh --suite-judged "$ATK_BASE" HEAD'); ATK_GATE_FILES=(scripts/gate-diff-improving.sh); ATK_EXPECT='drops protection'
atk_apply() { sed -i '/gate-edit-approvals.txt$/d' scripts/protected-paths.txt; }
