From LJF Require Import LJF_Rules LJF4_Rules LJFO_Rules LJFPS_Rules LJFn_Rules LJFh_Rules.

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

Scheme bct_mut := Induction for bct Sort Prop
  with ept_mut := Induction for ept Sort Prop
  with lfc_mut := Induction for lfc Sort Prop
  with rfc_mut := Induction for rfc Sort Prop.
Combined Scheme LJFPS_mutind_all from bct_mut, ept_mut, lfc_mut, rfc_mut.

Scheme bct4_mut_async := Induction for bct4 Sort Prop
  with ept4_mut_async := Induction for ept4 Sort Prop.
Combined Scheme LJF4_mutind_async from bct4_mut_async, ept4_mut_async.

Scheme bctO_mut_async := Induction for bctO Sort Prop
  with eptO_mut_async := Induction for eptO Sort Prop.
Combined Scheme LJFO_mutind_async from bctO_mut_async, eptO_mut_async.

Scheme bct_mut_async := Induction for bct Sort Prop
  with ept_mut_async := Induction for ept Sort Prop.
Combined Scheme LJFPS_mutind_async from bct_mut_async, ept_mut_async.

Scheme ept_bracketable_mut := Induction for ept Sort Prop
  with lfc_bracketable_mut := Induction for lfc Sort Prop.
Combined Scheme LJFPS_bracketable_mutind from 
  ept_bracketable_mut, lfc_bracketable_mut.

Scheme bctn_mut := Induction for bctn Sort Prop
  with eptn_mut := Induction for eptn Sort Prop
  with lfcn_mut := Induction for lfcn Sort Prop
  with rfcn_mut := Induction for rfcn Sort Prop.
Combined Scheme LJFn_mutind_all from bctn_mut, eptn_mut, lfcn_mut, rfcn_mut.

Scheme bcth_mut := Induction for bcth Sort Prop
  with epth_mut := Induction for epth Sort Prop
  with lfch_mut := Induction for lfch Sort Prop
  with rfch_mut := Induction for rfch Sort Prop.
Combined Scheme LJFh_mutind_all from bcth_mut, epth_mut, lfch_mut, rfch_mut.