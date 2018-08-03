module EverCrypt.Hash.Test

open FStar.HyperStack.ST
open FStar.Integers
open FStar.Seq
open EverCrypt.Helpers
open EverCrypt.Hash

module ST = FStar.HyperStack.ST
module B = LowStar.Buffer
module M = LowStar.Modifies

/// As a sanity check, we program & verify the whole hash algorithm
/// from its low-level incremental API.  We could compare their
/// extracted code & performance, and similarly provide a shared
/// reference implementation of update_multi.

#reset-options "--z3rlimit 300"
let compute a len text tag =
  push_frame();
  let s = create a in
  assert_norm(v len <= maxLength (Ghost.hide a));
  let ll = len % blockLen a in
  let lb = len - ll in
  let blocks = B.sub text 0ul lb in
  let last = B.offset text lb in
  let h1 = ST.get() in
  init s;
  let h10 = ST.get() in
  update_multi (Ghost.hide (Seq.empty #UInt8.t)) s blocks lb;
  let h11 = ST.get() in

  //18-07-10 improve style on ghosts and lists?
  FStar.Seq.(lemma_eq_intro (append (empty #UInt8.t) (B.as_seq h10 blocks)) (B.as_seq h10 blocks));

  update_last (Ghost.hide (B.as_seq h11 blocks)) s last len;
  finish s tag;
  let h2 = ST.get() in
  pop_frame();
  ( let vblocks = B.as_seq h1 blocks in
    let vlast = B.as_seq h1 last in
    let vsuffix = suffix (Ghost.hide a) (v len) in
    Seq.lemma_eq_intro (B.as_seq h1 text) (vblocks @| vlast);
    lemma_hash2 (acc0 #(Ghost.hide a)) vblocks (vlast @| vsuffix);
    Seq.append_assoc vblocks vlast vsuffix )

(*
val compute:
  a: alg13 ->
  len: UInt32.t ->
  text: uint8_pl (v len) ->
  tag: uint8_pl (tagLength a){ disjoint text tag } -> Stack unit
  (requires fun h0 ->
    live h0 text /\ live h0 tag)
  (ensures fun h0 () h1 ->
    live h1 text /\ live h1 tag /\
    modifies_1 tag h0 h1 /\
    v len <= maxLength a /\ (* required for subtyping the RHS below *)
    as_seq h1 tag = spec a (as_seq h0 text))
let compute a len test tag =
  match a with
  | SHA256 -> hash a len test tag
  | SHA384 -> hash a len test tag
  | SHA512 -> hash a len test tag
*)

val test:
  a: alg13 ->
  len: UInt32.t ->
  text: uint8_pl (v len) -> ST unit
  (requires fun h0 -> B.live h0 text)
  (ensures fun h0 _ h1 -> True //TODO adapt modifies_0 h0 h1
  )

let test a len data =
  push_frame();
  let tag0 = B.alloca 0uy (tagLen a) in
  let tag1 = B.alloca 0uy (tagLen a) in
  assert_norm(pow2 32 <= maxLength (Ghost.hide a));
  EverCrypt.Hash.hash a tag0 data len;
  compute a len data tag1;
  pop_frame()