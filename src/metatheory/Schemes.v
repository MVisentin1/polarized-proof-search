From LJF Require Import LJF_Rules LJF4_Rules LJFPS_Rules LJFC_Rules.

Scheme ufcL_mut := Induction for ufcL Sort Prop
  with lfcL_mut := Induction for lfcL Sort Prop
  with rfcL_mut := Induction for rfcL Sort Prop.

Combined Scheme LJF_mutind_all from ufcL_mut, lfcL_mut, rfcL_mut.

Scheme bct4_mut := Induction for bct4 Sort Prop
  with ept4_mut := Induction for ept4 Sort Prop
  with lfc4_mut := Induction for lfc4 Sort Prop
  with rfc4_mut := Induction for rfc4 Sort Prop.

Combined Scheme LJF4_mutind_all from bct4_mut, ept4_mut, lfc4_mut, rfc4_mut.

Scheme bct_mut := Induction for bct Sort Prop
  with ept_mut := Induction for ept Sort Prop
  with lfc_mut := Induction for lfc Sort Prop
  with rfc_mut := Induction for rfc Sort Prop.

Combined Scheme LJFPS_mutind_all from bct_mut, ept_mut, lfc_mut, rfc_mut.

Scheme bctC_mut := Induction for bctC Sort Prop
  with eptC_mut := Induction for eptC Sort Prop
  with lfcC_mut := Induction for lfcC Sort Prop
  with rfcC_mut := Induction for rfcC Sort Prop.

Combined Scheme LJFC_mutind_all from bct_mut, ept_mut, lfc_mut, rfc_mut.

Scheme bct4_mut_async := Induction for bct4 Sort Prop
  with ept4_mut_async := Induction for ept4 Sort Prop.
Combined Scheme LJF4_mutind_async from bct4_mut_async, ept4_mut_async.

Scheme bct_mut_async := Induction for bct Sort Prop
  with ept_mut_async := Induction for ept Sort Prop.
Combined Scheme LJFPS_mutind_async from bct_mut_async, ept_mut_async.

Scheme bctC_mut_async := Induction for bctC Sort Prop
  with eptC_mut_async := Induction for eptC Sort Prop.
Combined Scheme LJFC_mutind_async from bctC_mut_async, eptC_mut_async.