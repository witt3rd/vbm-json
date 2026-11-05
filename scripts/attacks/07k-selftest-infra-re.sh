ATK_DESC="neuter scripts/infra-re.sh (a sourced classifier that exits ends land-direct with success): scripts/test_land_direct.sh must FAIL"
ATK_GATES=('scripts/test_land_direct.sh'); ATK_GATE_FILES=(scripts/test_land_direct.sh)
atk_apply() { neuter scripts/infra-re.sh; }
