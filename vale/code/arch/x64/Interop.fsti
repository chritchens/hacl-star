module Interop
module List = FStar.List.Tot.Base
module HS = FStar.Monotonic.HyperStack
module HH = FStar.Monotonic.HyperHeap
module B = LowStar.Buffer
module MB = LowStar.Monotonic.Buffer
module M = LowStar.Modifies

open Opaque_s
open X64.Machine_s
open X64.Bytes_Semantics_s
open X64.Bytes_Semantics

let op_String_Access = Map.sel
let op_String_Assignment = Map.upd

inline_for_extraction
noeq
type b8 =
  | Buffer: #rrel:MB.srel UInt8.t -> #rel:MB.srel UInt8.t -> b:MB.mbuffer UInt8.t rrel rel -> b8

let sub l i = l - i

let rec loc_locs_disjoint_rec (l:b8) (ls:list b8) : Type0 =
  match ls with
  | [] -> True
  | h::t -> M.loc_disjoint (M.loc_buffer l.b) (M.loc_buffer h.b) /\ loc_locs_disjoint_rec l t

let rec locs_disjoint_rec (ls:list b8) : Type0 =
  match ls with
  | [] -> True
  | h::t -> loc_locs_disjoint_rec h t /\ locs_disjoint_rec t

unfold
let bufs_disjoint (ls:list b8) : Type0 =
  norm [iota; zeta; delta; delta_only [`%loc_locs_disjoint_rec;
                                       `%locs_disjoint_rec]] (locs_disjoint_rec ls)

unfold
let buf_disjoint_from (b:b8) (ls:list b8) : Type0 =
  norm [iota; zeta; delta; delta_only [`%loc_locs_disjoint_rec;
                                       `%locs_disjoint_rec]] (loc_locs_disjoint_rec b ls)

unfold
let disjoint (#a #b:Type0)
  (#ra1 #ra2: MB.srel a)
  (#rb1 #rb2: MB.srel b)
  (ptr1: MB.mbuffer a ra1 ra2)
  (ptr2:MB.mbuffer b rb1 rb2)
=
  M.loc_disjoint (M.loc_buffer ptr1) (M.loc_buffer ptr2)

unfold
let disjoint_or_eq (#a #b:Type0)
  (#ra1 #ra2: MB.srel a)
  (#rb1 #rb2: MB.srel b)
  (ptr1: MB.mbuffer a ra1 ra2)
  (ptr2:MB.mbuffer b rb1 rb2)
=
  disjoint ptr1 ptr2 \/ ptr1 === ptr2

unfold 
let b8_disjoint_or_eq (ptr1 ptr2:b8) =
  disjoint ptr1.b ptr2.b \/ ptr1 == ptr2
