ATK_DESC="approve and edit in ONE change: a tier1.sh line removed and the approval record for exactly that diff added to scripts/gate-edit-approvals.txt (the lander's rule: an approval lands alone, read from main)"
ATK_GATES=('bash -c ". scripts/land/lib/approvals.sh; ga_judge_run \"\$PWD\" \"\$ATK_BASE\" scripts/gate-edit-approvals.txt 7 scripts/tier1.sh \"\$(mktemp -d)\""'); ATK_GATE_FILES=(scripts/land/lib/approvals.sh); ATK_EXPECT='ALONE'
atk_apply() {
  n=$(first_line_matching scripts/tier1.sh 'cannot'); sed -i "${n}d" scripts/tier1.sh; git add -A; git commit -q -m "the edit"
  h=$(bash -c '. scripts/land/lib/approvals.sh; ga_hash . "$ATK_BASE" HEAD scripts/tier1.sh')
  echo "scripts/tier1.sh | $h | self-approved | $(date -u +%F)" >> scripts/gate-edit-approvals.txt
}
