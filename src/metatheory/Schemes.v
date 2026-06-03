From LJF Require Import LJF_Rules LJF4_Rules LJFO_Rules.

Scheme ufcL_mut := Induction for ufcL Sort Prop
  with lfcL_mut := Induction for lfcL Sort Prop
  with rfcL_mut := Induction for rfcL Sort Prop.

Combined Scheme LJF_mutind_all from ufcL_mut, lfcL_mut, rfcL_mut.

Scheme bct4_mut := Induction for bct4 Sort Prop
  with ept4_mut := Induction for ept4 Sort Prop
  with lfc4_mut := Induction for lfc4 Sort Prop
  with rfc4_mut := Induction for rfc4 Sort Prop.

Combined Scheme LJF4_mutind_all from bct4_mut, ept4_mut, lfc4_mut, rfc4_mut.

Scheme bctO_mut := Induction for bctO Sort Prop
  with eptO_mut := Induction for eptO Sort Prop
  with lfcO_mut := Induction for lfcO Sort Prop
  with rfcO_mut := Induction for rfcO Sort Prop.

Combined Scheme LJFO_mutind_all from bctO_mut, eptO_mut, lfcO_mut, rfcO_mut.

Scheme bct4_mut_async := Induction for bct4 Sort Prop
  with ept4_mut_async := Induction for ept4 Sort Prop.
Combined Scheme LJF4_mutind_async from bct4_mut_async, ept4_mut_async.

Scheme bctO_mut_async := Induction for bctO Sort Prop
  with eptO_mut_async := Induction for eptO Sort Prop.
Combined Scheme LJFO_mutind_async from bctO_mut_async, eptO_mut_async.