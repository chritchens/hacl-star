module Hacl.EC.Curve25519.Bignum.Fscalar.Lemmas

open FStar.Mul
open FStar.ST
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer
open FStar.Math.Lib
open FStar.Math.Lemmas

open Hacl.UInt64

open Hacl.EC.Curve25519.Parameters
open Hacl.EC.Curve25519.Bigint
open Hacl.EC.Curve25519.Bignum.Lemmas.Utils

module U32 = FStar.UInt32
module H64 = Hacl.UInt64
module H128 = Hacl.UInt128

#reset-options "--initial_fuel 0 --max_fuel 0"

let willNotOverflow (h:heap) (a:bigint) (s:s64) : GTot Type0 =
  live h a /\ v (get h a 0) * v s < pow2 128 /\ v (get h a 1) * v s < pow2 128
  /\ v (get h a 2) * v s < pow2 128 /\ v (get h a 3) * v s < pow2 128 /\ v (get h a 4) * v s < pow2 128


let isScalarMult h0 h1 (res:bigint_wide) (a:bigint) (s:s64) : GTot Type0 =
  live h0 a /\ live h1 res
  /\ H128.v (get h1 res 0) = v (get h0 a 0) * v s
  /\ H128.v (get h1 res 1) = v (get h0 a 1) * v s
  /\ H128.v (get h1 res 2) = v (get h0 a 2) * v s
  /\ H128.v (get h1 res 3) = v (get h0 a 3) * v s
  /\ H128.v (get h1 res 4) = v (get h0 a 4) * v s


let bound115 h (b:bigint_wide) : GTot Type0 =
  let open Hacl.UInt128 in
  live h b
  /\ v (get h b 0) < pow2 115
  /\ v (get h b 1) < pow2 115
  /\ v (get h b 2) < pow2 115
  /\ v (get h b 3) < pow2 115
  /\ v (get h b 4) < pow2 115


(*
#reset-options

(* Lemma *)
val scalar_multiplication_lemma_aux: h0:heap -> h1:heap -> a:bigint{live h0 a} -> 
  b:bigint_wide{live h1 b} -> s:int -> len:pos{ (len <= length a)  /\ (len <= length b) } ->
  Lemma
    (requires ( (eval h0 a (len-1) * s = eval_wide h1 b (len-1))
		/\ (v (get h0 a (len-1)) * s = Hacl.UInt128.v (get h1 b (len-1)))))
    (ensures ( eval h0 a len * s = eval_wide h1 b len ))
let scalar_multiplication_lemma_aux h0 h1 a b s len =
//  admit();
  Math.Axioms.paren_mul_left (pow2 (bitweight (templ) (len-1))) (v (get h0 a (len-1))) s;
  Math.Axioms.distributivity_add_left ((pow2 (bitweight (templ) (len-1))) * (v (get h0 a (len-1)))) (eval h0 a (len-1)) s

#reset-options

(* Lemma *)
val scalar_multiplication_lemma: h0:heap -> h1:heap -> a:bigint{live h0 a} -> 
  b:bigint_wide{live h1 b} -> s:int -> len:nat{len <= length a /\ len <= length b} ->
  Lemma
    (requires (forall (i:nat). i < len ==> v (get h0 a i) * s = Hacl.UInt128.v (get h1 b i)))
    (ensures (eval h0 a len * s = eval_wide h1 b len))
let rec scalar_multiplication_lemma h0 h1 a b s len =
//  admit();
  match len with
  | 0 -> 
    assert(eval h0 a len = 0); ()
    (* FscalarLemmas.lemma_1 s *)
  | _ -> 
    (* FscalarLemmas.lemma_3 len; *)
    scalar_multiplication_lemma h0 h1 a b s (len-1); 
    scalar_multiplication_lemma_aux h0 h1 a b s len

val scalar_multiplication_tr_1: res:bigint_wide -> a:bigint{disjoint res a} -> s:s64 -> 
  ctr:u32{w ctr<norm_length} -> STL unit
     (requires (fun h -> 
       (live h res) /\ (live h a) /\ (length a >= norm_length) /\ (length res >= norm_length)
       /\ (forall (i:nat). (i >= w ctr /\ i < norm_length) ==> v (get h a i) * v s < pow2 platform_wide)))
     (ensures (fun h0 u h1 -> 
       (live h0 res) /\ (live h1 res) /\ (live h0 a) /\ (live h1 a)
       /\ (length res >= norm_length) /\ (length res = length res)
       /\ (modifies_1 res h0 h1) /\ (length a >= norm_length)
       /\ (forall (i:nat). (i >= w ctr+1 /\ i < norm_length) ==> v (get h0 a i) * v s < pow2 platform_wide) 
       /\ (forall (i:nat). (i < length res /\ i <> w ctr) ==> (get h1 res i == get h0 res i))
       /\ (Hacl.UInt128.v (get h1 res (w ctr)) = v (get h0 a (w ctr)) * v s)
     ))
let rec scalar_multiplication_tr_1 res a s ctr =
    let ai = index a ctr in
    let z = Hacl.UInt128.mul_wide ai s in
    upd res ctr z

val scalar_multiplication_tr_2:
  h0:heap -> h1:heap -> h2:heap -> res:bigint_wide -> a:bigint{disjoint res a} -> s:s64 -> ctr:nat{ctr<norm_length} -> 
  Lemma
     (requires (
       (live h1 res) /\ (live h2 res) /\ (live h1 a) /\ (live h2 a) /\ live h0 a /\ live h0 res
       /\ modifies_1 res h0 h1
       /\ (modifies_1 res h1 h2) /\ (length a >= norm_length)
       /\ (forall (i:nat). {:pattern (get h1 a i)} (i >= ctr+1 /\ i < norm_length) ==> v (get h1 a i) * v s < pow2 platform_wide)
       /\ (length res >= norm_length) /\ (length res = length res)
       /\ length res = length res
       /\ (forall (i:nat). {:pattern (get h1 res i)} (i < length res /\ i <> ctr) ==> get h1 res i == get h0 res i)
       /\ vv (get h1 res ctr) = v (get h0 a ctr) * v s
       /\ (forall (i:nat{(i>= ctr+1 /\ i < norm_length)}). {:pattern (get h2 res i)} vv (get h2 res i) = v (get h1 a i) * v s)
       /\ (forall (i:nat{(i < length res /\ (i < ctr+1 \/ i >= norm_length))}). {:pattern (get h2 res i)}
	   (get h2 res i == get h1 res i))
       /\ (Seq.equal (sel h1 (a)) (sel h2 (a))) ))
     (ensures (
       (live h0 res) /\ (live h2 res) /\ (live h0 a) /\ (live h2 a)
       /\ (modifies_1 res h0 h2) /\ (length a >= norm_length)
       /\ (forall (i:nat). (i >= ctr /\ i < norm_length) ==> v (get h0 a i) * v s < pow2 platform_wide)
       /\ (length res >= norm_length) /\ (length res = length res)
       /\ (forall (i:nat{(i>= ctr /\ i < norm_length)}). vv (get h2 res i) = v (get h0 a i) * v s)
       /\ (forall (i:nat{(i < length res /\ (i < ctr \/ i >= norm_length))}). 
	   (get h2 res i == get h0 res i))
       /\ (Seq.equal (sel h0 (a)) (sel h2 (a)))
     ))
let scalar_multiplication_tr_2 h0 h1 h2 res a s ctr =
  (* no_upd_lemma h0 h1 a (only res); *)
  (* no_upd_lemma h1 h2 a (only res); *)
  ()

(* Code *)
(* Tail recursive version of the scalar multiplication *)
val scalar_multiplication_tr: res:bigint_wide -> a:bigint{disjoint res a} -> s:s64 -> ctr:u32{w ctr<=norm_length} -> STL unit
     (requires (fun h -> 
       (live h res) /\ (live h a) /\ (length a >= norm_length) /\ (length res >= norm_length)
       /\ (forall (i:nat). (i >= w ctr /\ i < norm_length) ==> v (get h a i) * v s < pow2 platform_wide)))
     (ensures (fun h0 u h1 -> 
       (live h0 res) /\ (live h1 res) /\ (live h0 a) /\ (live h1 a)
       /\ (modifies_1 res h0 h1) /\ (length a >= norm_length)
       /\ (forall (i:nat). (i >= w ctr /\ i < norm_length) ==> v (get h0 a i) * v s < pow2 platform_wide)
       /\ (length res >= norm_length) /\ (length res = length res)
       /\ (forall (i:nat{(i>= w ctr /\ i < norm_length)}). vv (get h1 res i) = v (get h0 a i) * v s)
       /\ (forall (i:nat{(i < length res /\ (i < w ctr \/ i >= norm_length))}). 
	   (get h1 res i == get h0 res i))
       /\ (Seq.equal (sel h0 (a)) (sel h1 (a)))  ))
let rec scalar_multiplication_tr res a s ctr =
  //admit();
  let h0 = ST.get() in
  if U32.eq ctr nlength then ()
  else begin
     let i = ctr in
     (* FscalarLemmas.lemma_4 norm_length ctr;  *)
     scalar_multiplication_tr_1 res a s ctr; 
     let h1 = ST.get() in 
     (* no_upd_lemma h0 h1 a (only res); *)
     scalar_multiplication_tr res a s (ctr+|1ul); 
     let h2 = ST.get() in
     scalar_multiplication_tr_2 h0 h1 h2 res a s (w ctr)
  end

(* Lemma *)   	 
val theorem_scalar_multiplication: h0:heap -> h1:heap -> a:bigint{live h0 a} -> s:s64 -> 
  len:nat{len <= length a} -> b:bigint_wide{live h1 b /\ len <= length b} -> Lemma
    (requires (forall (i:nat). i < len ==> vv (get h1 b i) = v (get h0 a i) * v s))
    (ensures ((eval_wide h1 b len) = (eval h0 a len) * v s))
let theorem_scalar_multiplication h0 h1 a s len b = 
  scalar_multiplication_lemma h0 h1 a b (v s) len; ()

#reset-options

val auxiliary_lemma_2: ha:heap -> a:bigint{norm ha a} -> s:s64 -> i:nat{ i < norm_length} -> Lemma
    (requires (True))
    (ensures (v (get ha a i) * v s < pow2 (platform_wide)))
let auxiliary_lemma_2 ha a s i =
  (* UInt.mul_lemma #(templ i) (v (get ha a i)) #platform_size (v s); *)
  Curve.Parameters.parameters_lemma_0 ();
  (* Math.Lib.pow2_increases_2 platform_wide (templ i + platform_size) *)
  ()
  
val auxiliary_lemma_0: ha:heap -> a:bigint{norm ha a} -> s:s64 -> Lemma
  (forall (i:nat). i < norm_length ==> v (get ha a i) * v s < pow2 platform_wide)
let auxiliary_lemma_0 ha a s = ()

val auxiliary_lemma_1: h0:heap -> h1:heap -> b:bigint{norm h0 b} -> #t:Type -> b':buffer t ->
  Lemma (requires (live h1 b /\ modifies_1 b' h0 h1 /\ disjoint b b'))
	(ensures (norm h1 b))
let auxiliary_lemma_1 h0 h1 b #t b' = ()

val scalar': res:bigint_wide -> a:bigint{disjoint res a} -> s:s64 -> STL unit
     (requires (fun h -> norm h a /\ live h res))
     (ensures (fun h0 u h1 -> live h0 res /\ live h1 res /\ norm h0 a /\ norm h1 a
       /\ modifies_1 res h0 h1
       /\ eval_wide h1 res norm_length = eval h0 a norm_length * v s ))
let scalar' res a s =
  let h0 = ST.get() in  
  auxiliary_lemma_0 h0 a s; 
  scalar_multiplication_tr res a s 0ul; 
  let h1 = ST.get() in
  (* no_upd_lemma h0 h1 a (only res); *)
  auxiliary_lemma_1 h0 h1 a (res); 
  theorem_scalar_multiplication h0 h1 a s norm_length res; 
  ()

	       
