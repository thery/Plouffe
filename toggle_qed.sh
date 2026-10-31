#!/bin/sh
# Switch the long native computations (comp*_def in Million1-4 and Billion1-4)
# between Admitted (fast) and Qed (full check).
#   ./toggle_qed.sh admit   Time Qed. -> (* Time Qed. *) Admitted.
#   ./toggle_qed.sh qed     back to Time Qed.
#   ./toggle_qed.sh million build the Million files (Billion commented out in _CoqProject)
#   ./toggle_qed.sh billion build the Billion files (Million commented out)
set -e
cd "$(dirname "$0")"
F="Million[1-4].v Billion[1-4].v"
case "$1" in
  admit)
    perl -0pi -e 's/(native_cast_no_check[^\n]*\n)Time Qed\./$1(*\nTime Qed.\n*)\nAdmitted./g' $F ;;
  qed)
    perl -0pi -e 's/(native_cast_no_check[^\n]*\n)\(\*\nTime Qed\.\n\*\)\nAdmitted\./$1Time Qed./g' $F ;;
  million)
    perl -pi -e 's/^#(Million\d*\.v)/$1/; s/^(Billion\d*\.v)/#$1/' _CoqProject ;;
  billion)
    perl -pi -e 's/^#(Billion\d*\.v)/$1/; s/^(Million\d*\.v)/#$1/' _CoqProject ;;
  *) echo "usage: $0 qed|admit|million|billion"; exit 1 ;;
esac
A=$(cat $F | grep -c "^Admitted\." || true)
echo "Built: $(grep -E '^(Million|Billion)\.v' _CoqProject | sed 's/\.v//') ; Admitted: $A ; Qed: $((8 - A))"
