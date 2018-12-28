module Interop

module List = FStar.List.Tot.Base
module HS = FStar.Monotonic.HyperStack
module HH = FStar.Monotonic.HyperHeap
module B = LowStar.Buffer
module M = LowStar.Modifies

open Opaque_s
open X64.Machine_s
open X64.Bytes_Semantics_s
open X64.Bytes_Semantics

#reset-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1"

(* Write a buffer in the vale memory *)

let rec write_vale_mem (contents:Seq.seq UInt8.t) (length:nat{length = FStar.Seq.Base.length contents}) addr (i:nat{i <= length}) 
      (curr_heap:heap{forall j. {:pattern (Seq.index contents j)} 
	0 <= j /\ j < i ==> curr_heap.[addr+j] == UInt8.v (Seq.index contents j)}) : Tot heap (decreases %[sub length i]) =
    if i >= length then curr_heap
    else (
      let heap = curr_heap.[addr + i] <- UInt8.v (FStar.Seq.index contents i) in
      write_vale_mem contents length addr (i+1) heap
    )      

let rec frame_write_vale_mem (contents:Seq.seq UInt8.t) (length:nat{length = FStar.Seq.Base.length contents}) addr (i:nat{i <= length}) 
      (curr_heap:heap{forall j. {:pattern (Seq.index contents j)} 0 <= j /\ j < i ==> curr_heap.[addr + j] == UInt8.v (Seq.index contents j)}) : Lemma
      (requires True)
      (ensures (let new_heap = write_vale_mem contents length addr i curr_heap in
      forall j. j < addr \/ j >= addr + length ==> curr_heap.[j] == new_heap.[j]))
      (decreases %[sub length i])=
      if i >= length then ()
      else begin
	let heap = curr_heap.[addr + i] <- UInt8.v (FStar.Seq.index contents i) in
	frame_write_vale_mem contents length addr (i+1) heap
      end
      
let rec load_store_write_vale_mem 
  (contents:Seq.seq UInt8.t) 
  (length:nat{length = FStar.Seq.Base.length contents}) 
  addr 
  (i:nat{i <= length}) 
  (curr_heap:heap{forall j. {:pattern (Seq.index contents j)} 0 <= j /\ j < i ==> 
    curr_heap.[addr + j] == UInt8.v (Seq.index contents j)}) : Lemma
      (requires True)
      (ensures (let new_heap = write_vale_mem contents length addr i curr_heap in
      forall j. 0 <= j /\ j < length ==> UInt8.v (Seq.index contents j) == new_heap.[addr + j]))
      (decreases %[sub length i])=
      if i >= length then ()
      else begin
	let heap = curr_heap.[addr + i] <- UInt8.v (FStar.Seq.index contents i) in
	load_store_write_vale_mem contents length addr (i+1) heap
      end

let rec domain_write_vale_mem 
  (contents:Seq.seq UInt8.t) 
  (length:nat{length = FStar.Seq.Base.length contents}) 
  addr 
  (i:nat{i <= length}) 
  (curr_heap:heap{forall j. {:pattern (Seq.index contents j)} 0 <= j /\ j < i ==> 
    curr_heap.[addr + j] == UInt8.v (Seq.index contents j)}) : Lemma
      (requires True)
      (ensures (let new_heap = write_vale_mem contents length addr i curr_heap in
      forall j. Set.mem j (Map.domain new_heap) /\ not (Set.mem j (Map.domain curr_heap)) ==> 
        addr <= j /\ j < addr + length))
      (decreases %[sub length i])=
   if i >= length then ()
   else begin
     let heap = curr_heap.[addr + i] <- UInt8.v (FStar.Seq.index contents i) in
     domain_write_vale_mem contents length addr (i+1) heap
    end

let rec domain2_write_vale_mem 
  (contents:Seq.seq UInt8.t) 
  (length:nat{length = FStar.Seq.Base.length contents}) 
  addr 
  (i:nat{i <= length}) 
  (curr_heap:heap{forall j. {:pattern (Seq.index contents j)} 0 <= j /\ j < i ==> 
    curr_heap.[addr + j] == UInt8.v (Seq.index contents j)}) : Lemma
      (requires forall j. addr <= j /\ j < addr + i ==> Set.mem j (Map.domain curr_heap))
      (ensures (let new_heap = write_vale_mem contents length addr i curr_heap in
	forall j. addr <= j /\ j < addr + length ==> Set.mem j (Map.domain new_heap)))
      (decreases %[sub length i])=
   if i >= length then ()
   else begin
     let heap = curr_heap.[addr + i] <- UInt8.v (FStar.Seq.index contents i) in
     domain2_write_vale_mem contents length addr (i+1) heap
    end

let rec monotone_domain_write_vale_mem 
  (contents:Seq.seq UInt8.t) 
  (length:nat{length = FStar.Seq.Base.length contents}) 
  addr 
  (i:nat{i <= length}) 
  (curr_heap:heap{forall j. {:pattern (Seq.index contents j)} 0 <= j /\ j < i ==> 
    curr_heap.[addr + j] == UInt8.v (Seq.index contents j)}) : Lemma
      (requires True)
      (ensures (let new_heap = write_vale_mem contents length addr i curr_heap in
      forall j. Set.mem j (Map.domain curr_heap) ==> Set.mem j (Map.domain new_heap)))
      (decreases %[sub length i])=
   if i >= length then ()
   else begin
     let heap = curr_heap.[addr + i] <- UInt8.v (FStar.Seq.index contents i) in
     monotone_domain_write_vale_mem contents length addr (i+1) heap
    end

#set-options "--z3rlimit 40"

let correct_down_p_cancel mem (addrs:addr_map) heap (p:b8) : Lemma
  (forall p'. p == p' ==>       
      (let length = B.length p in
      let contents = B.as_seq mem p in
      let addr = addrs p in
      let new_heap = write_vale_mem contents length addr 0 heap in
      correct_down_p mem addrs new_heap p')) = 
  let rec aux (p':b8) : Lemma 
    (p == p'  ==> (let length = B.length p in
      let contents = B.as_seq mem p in
      let addr = addrs p in
      let new_heap = write_vale_mem contents length addr 0 heap in
      correct_down_p mem addrs new_heap p')) =
        let length = B.length p in
        let contents = B.as_seq mem p in
        let addr = addrs p in
        let new_heap = write_vale_mem contents length addr 0 heap in
	load_store_write_vale_mem contents length addr 0 heap
  in
  Classical.forall_intro aux
      
let correct_down_p_frame mem (addrs:addr_map) (heap:heap) (p:b8) : Lemma
  (forall p'. disjoint p p' /\ correct_down_p mem addrs heap p' ==>       
      (let length = B.length p in
      let contents = B.as_seq mem p in
      let addr = addrs p in
      let new_heap = write_vale_mem contents length addr 0 heap in
      correct_down_p mem addrs new_heap p')) = 
  let rec aux (p':b8) : Lemma 
    (disjoint p p' /\ correct_down_p mem addrs heap p' ==> (let length = B.length p in
      let contents = B.as_seq mem p in
      let addr = addrs p in
      let new_heap = write_vale_mem contents length addr 0 heap in
      correct_down_p mem addrs new_heap p')) =
        let length = B.length p in
        let contents = B.as_seq mem p in
        let addr = addrs p in
        let new_heap = write_vale_mem contents length addr 0 heap in
	frame_write_vale_mem contents length addr 0 heap
  in
  Classical.forall_intro aux



private let add_buffer_domain (b:b8) (addrs:addr_map) (accu:Set.set int) : GTot (s:Set.set int{
  forall x. Set.mem x s <==> (Set.mem x accu \/ (x >= addrs b /\ x < addrs b + B.length b))}) =
  let rec aux (j:nat{j <= B.length b}) (acc:Set.set int{forall x. Set.mem x acc <==>
    Set.mem x accu \/ (x >= addrs b /\ x < addrs b + j)}) :
    GTot (s:Set.set int{forall x. Set.mem x s <==>
    Set.mem x accu \/ (x >= addrs b /\ x < addrs b + B.length b)}) 
    (decreases %[B.length b - j]) = 
    if j >= B.length b then acc else begin
      let s = Set.union acc (Set.singleton (addrs b + j)) in
      aux (j+1) s
    end in
  aux 0 accu
  

private let rec addrs_set_aux (ptrs:list b8)
			      (ps2: list b8)
			      (ps:list b8{forall b. List.memP b ptrs <==> List.memP b ps \/ List.memP b ps2})
			      (addrs:addr_map)
			      (accu:Set.set int{forall (x:int). not (Set.mem x accu) <==>
			        (forall (b:b8{List.memP b ps}). x < addrs b \/ x >= addrs b + B.length b)}) :
			 GTot (s:Set.set int{forall (x:int). not (Set.mem x s) <==>
			        (forall (b:b8{List.memP b ptrs}). x < addrs b \/ x >= addrs b + B.length b)}) =
  match ps2 with
  | [] -> accu
  | a::q -> 
    let s = add_buffer_domain a addrs accu in
    let aux (x:int) : Lemma
      (requires True)
      (ensures not (Set.mem x s) <==> 
      (forall (b:b8{List.memP b (a::ps)}). 
	x < addrs b \/ x >= addrs b + B.length b)) = ()
    in
    Classical.forall_intro aux;
    addrs_set_aux ptrs q (a::ps) addrs s

let addrs_set ptrs addrs = addrs_set_aux ptrs ptrs [] addrs Set.empty

let addrs_set_lemma ptrs1 ptrs2 addrs =
  let s1 = addrs_set_aux ptrs1 ptrs1 [] addrs Set.empty in
  let s2 = addrs_set_aux ptrs2 ptrs2 [] addrs Set.empty in
  assert (Set.equal s1 s2)

let addrs_set_concat ptrs a addrs = 
  let s1 = addrs_set ptrs addrs in
  let s2 = addrs_set [a] addrs in
  assert (Set.equal (addrs_set (a::ptrs) addrs) (Set.union s1 s2));
  ()

let addrs_set_mem ptrs a addrs i = ()

let write_buffer_vale (a:b8) (heap:heap) (mem:HS.mem) (addrs:addr_map) =
  let length = B.length a in
  let contents = B.as_seq mem a in
  let addr = addrs a in
  write_vale_mem contents length addr 0 heap

let domain_write_buffer (a:b8) (heap:heap) (mem:HS.mem) (addrs:addr_map) : Lemma
  (let new_heap = write_buffer_vale a heap mem addrs in
   Set.equal (Set.union (Map.domain heap) (addrs_set [a] addrs)) (Map.domain new_heap)) =
   let new_heap = write_buffer_vale a heap mem addrs in
   let s1 = Map.domain heap in
   let s2 = addrs_set [a] addrs in
   let s3 = Map.domain new_heap in
   let length = B.length a in
   let contents = B.as_seq mem a in
   let addr = addrs a in   
   domain_write_vale_mem contents length addr 0 heap;
   domain2_write_vale_mem contents length addr 0 heap;
   monotone_domain_write_vale_mem contents length addr 0 heap;
   ()

let rec down_mem_aux (ptrs:list b8{list_disjoint_or_eq ptrs})
  (addrs:addr_map)
  (mem:HS.mem)
  (ps:list b8)
  (accu:list b8{forall p. List.memP p ptrs <==> List.memP p ps \/ List.memP p accu})
  (h:heap{correct_down mem addrs accu h}) : 
  GTot (heap:heap{correct_down mem addrs ptrs heap}) =
  match ps with
    | [] -> addrs_set_lemma accu ptrs addrs; h
    | a::q ->
      let new_heap = write_buffer_vale a h mem addrs in
      let length = B.length a in
      let contents = B.as_seq mem a in
      let addr = addrs a in      
      load_store_write_vale_mem contents length addr 0 h;
      correct_down_p_cancel mem addrs h a;
      correct_down_p_frame mem addrs h a;
      assert (forall p. List.memP p accu ==> disjoint_or_eq p a);
      domain_write_buffer a h mem addrs;
      addrs_set_concat accu a addrs;
      down_mem_aux ptrs addrs mem q (a::accu) new_heap

let down_mem mem addrs ptrs =
  (* Dummy heap *)
  let heap = FStar.Map.const 0 in
  let heap = Map.restrict Set.empty heap in
  down_mem_aux ptrs addrs mem ptrs [] heap

private
let rec frame_down_mem_aux (ptrs:list b8{list_disjoint_or_eq ptrs})
  (addrs:addr_map)
  (mem:HS.mem)
  (ps:list b8)
  (accu:list b8{forall p. List.memP p ptrs <==> List.memP p ps \/ List.memP p accu})
  (h:heap{correct_down mem addrs accu h}) : Lemma
  (let heap = down_mem_aux ptrs addrs mem ps accu h in
   forall i. (forall (b:b8{List.memP b ptrs}). 
      let base = addrs b in
      i < base \/ i >= base + B.length b) ==>
      h.[i] == heap.[i]) =
  match ps with
  | [] -> ()
  | a::q ->
    let new_heap = write_buffer_vale a h mem addrs in
    let length = B.length a in
    let contents = B.as_seq mem a in
    let addr = addrs a in     
    load_store_write_vale_mem contents length addr 0 h;
    correct_down_p_cancel mem addrs h a;
    correct_down_p_frame mem addrs h a;
    assert (forall p. List.memP p accu ==> disjoint_or_eq p a);
    domain_write_buffer a h mem addrs;
    addrs_set_concat accu a addrs;
    let new_heap' = down_mem_aux ptrs addrs mem q (a::accu) new_heap in
    frame_down_mem_aux ptrs addrs mem q (a::accu) new_heap;
    frame_write_vale_mem contents length addr 0 h;
    assert_norm (down_mem_aux ptrs addrs mem (a::q) accu h ==
                 new_heap') //NS: 11/30, unfolding a recursive function via smt
                            //requires non-trivial proofs of typing;
                            //do it via normalization instead
 
let same_unspecified_down mem1 mem2 addrs ptrs =
  let heap = Map.const 0 in
  let heap = Map.restrict Set.empty heap in 
  let heapf1 = down_mem_aux ptrs addrs mem1 ptrs [] heap in
  let heapf2 = down_mem_aux ptrs addrs mem2 ptrs [] heap in
  frame_down_mem_aux ptrs addrs mem1 ptrs [] heap;
  frame_down_mem_aux ptrs addrs mem2 ptrs [] heap;
  ()

let get_seq_heap_as_seq (heap1 heap2:heap) (addrs:addr_map) (mem:HS.mem) (b:b8) : Lemma
  (requires correct_down_p mem addrs heap1 b /\
    (forall x. x >= addrs b /\ x < addrs b + B.length b ==> heap1.[x] == heap2.[x]))
  (ensures B.as_seq mem b == get_seq_heap heap2 addrs b) =
  assert (Seq.equal (B.as_seq mem b) (get_seq_heap heap2 addrs b))

let rec up_mem_aux (heap:heap)
               (addrs:addr_map)
               (ptrs:list b8{list_disjoint_or_eq ptrs})
               (ps:list b8)
               (accu:list b8{forall p. List.memP p ptrs <==> List.memP p ps \/ List.memP p accu}) 
               (m:HS.mem{list_live m ptrs /\ 
                 Set.equal (addrs_set ptrs addrs) (Map.domain heap) /\ 
                 (forall p. List.memP p accu ==> correct_down_p m addrs heap p)})
  : GTot (m':HS.mem{correct_down m' addrs ptrs heap /\ list_live m' ptrs}) =
    match ps with
    | [] -> m
    | a::q ->
      let s = get_seq_heap heap addrs a in
      B.g_upd_seq_as_seq a s m;
      let m' = B.g_upd_seq a s m in
      up_mem_aux heap addrs ptrs q (a::accu) m'

let up_mem heap addrs ptrs mem = up_mem_aux heap addrs ptrs ptrs [] mem

let rec down_up_identity_aux
    (heap:heap)
    (addrs:addr_map)
    (ptrs:list b8{list_disjoint_or_eq ptrs})
    (ps:list b8)
    (accu:list b8{forall p. List.memP p ptrs <==> List.memP p ps \/ List.memP p accu})    
    (m:HS.mem{list_live m ptrs /\ correct_down m addrs ptrs heap})
  : Lemma (m == up_mem_aux heap addrs ptrs ps accu m) =
  match ps with
  | [] -> ()
  | a::q ->
      let s = get_seq_heap heap addrs a in
      let m' = B.g_upd_seq a s m in
      B.lemma_g_upd_with_same_seq a m;
      assert (Seq.equal s (B.as_seq m a));
      (* The previous assertion and lemma ensure that m == m' *)
      B.g_upd_seq_as_seq a s m;
      down_up_identity_aux heap addrs ptrs q (a::accu) m'

let down_up_identity mem addrs ptrs =
  let heap = down_mem mem addrs ptrs in
  down_up_identity_aux heap addrs ptrs ptrs [] mem

let correct_down_p_same_sel (b:b8) (mem:HS.mem) (addrs:addr_map) (heap1 heap2:heap) (x:int) : Lemma
  (requires (x >= addrs b /\ x < addrs b + B.length b 
    /\ correct_down_p mem addrs heap1 b /\ correct_down_p mem addrs heap2 b))
  (ensures Map.sel heap1 x == Map.sel heap2 x) = 
    let i = x - addrs b in
    assert (heap1.[x] == heap1.[addrs b + i]);
    assert (heap2.[x] == heap2.[addrs b + i])

let rec up_down_identity_aux
  (ptrs:list b8{list_disjoint_or_eq ptrs})
  (addrs:addr_map)
  (mem:HS.mem)
  (init_heap:heap{correct_down mem addrs ptrs init_heap})
  : Lemma 
      (let heap = down_mem mem addrs ptrs in 
      forall x. Map.contains heap x ==> Map.sel heap x == Map.sel init_heap x) =
    let heap = down_mem mem addrs ptrs in
    let aux (x:int) : Lemma 
      (requires Map.contains heap x)
      (ensures Map.sel heap x == Map.sel init_heap x) =
      Classical.forall_intro 
        (Classical.move_requires (fun b -> correct_down_p_same_sel b mem addrs heap init_heap x))
    in Classical.forall_intro (Classical.move_requires aux)

#reset-options "--z3rlimit 50 --max_fuel 1 --max_ifuel 1 --initial_fuel 1 --initial_ifuel 1"
let up_down_identity mem addrs ptrs heap = 
  let initial_heap = down_mem mem addrs ptrs in
  let new_heap = down_mem (up_mem heap addrs ptrs mem) addrs ptrs in
  same_unspecified_down mem (up_mem heap addrs ptrs mem) addrs ptrs;
  up_down_identity_aux ptrs addrs (up_mem heap addrs ptrs mem) heap;
  assert (forall k. Map.contains heap k ==> Map.sel heap k == Map.sel new_heap k);
  assert (forall k. (~ (Map.contains heap k)) ==> Map.sel heap k == Map.sel new_heap k);
  assert (Map.equal heap new_heap)

#set-options "--max_fuel 1 --max_ifuel 1"

let g_upd_tot_correct_down_invariant
  (ptrs:list b8{list_disjoint_or_eq ptrs})
  (addrs:addr_map)
  (heap1:heap)
  (heap2:heap)
  (b:b8{List.memP b ptrs})
  (mem:HS.mem{list_live mem ptrs})
  : Lemma
  (requires forall p. (p =!= b /\ List.memP p ptrs) ==> correct_down_p mem addrs heap1 p)
  (ensures (
    let m' = B.g_upd_seq b (get_seq_heap heap2 addrs b) mem in
    forall p. (p =!= b /\ List.memP p ptrs) ==> correct_down_p m' addrs heap1 p)
  ) = 
    B.g_upd_seq_as_seq b (get_seq_heap heap2 addrs b) mem

let g_upd_tot_correct_down
  (mem:HS.mem)
  (addrs:addr_map)
  (heap:heap)
  (b:b8{B.live mem b}) :
  Lemma (correct_down_p (B.g_upd_seq b (get_seq_heap heap addrs b) mem) addrs heap b) =
  B.g_upd_seq_as_seq b (get_seq_heap heap addrs b) mem

#reset-options "--z3rlimit 50 --max_fuel 1 --max_ifuel 1 --initial_fuel 1 --initial_ifuel 1"
let rec update_buffer_up_mem_aux
  (ptrs:list b8{list_disjoint_or_eq ptrs})
  (addrs:addr_map)
  (mem:HS.mem{list_live mem ptrs})
  (b:b8{List.memP b ptrs})
  (heap1:heap{Set.equal (Map.domain heap1) (addrs_set ptrs addrs)})
  (heap2:heap{Set.equal (Map.domain heap1) (Map.domain heap2)})
  (ps:list b8)
  (accu:list b8{forall p. List.memP p ptrs <==> List.memP p ps \/ List.memP p accu}) : Lemma
  (requires (forall x. x < addrs b \/ x >= addrs b + B.length b ==> heap1.[x] == heap2.[x]) /\
    (List.memP b accu ==> B.as_seq mem b == get_seq_heap heap2 addrs b) /\  
    (forall p. List.memP p accu ==> correct_down_p mem addrs heap2 p) /\
    (forall p. (p =!= b /\ List.memP p ptrs) ==> correct_down_p mem addrs heap1 p)    )
  (ensures 
  (List.memP b accu ==> up_mem_aux heap2 addrs ptrs ps accu mem == mem) /\
  (~(List.memP b accu) ==> up_mem_aux heap2 addrs ptrs ps accu mem ==
    B.g_upd_seq b (get_seq_heap heap2 addrs b) mem))
  (decreases ps)
  
  = match ps with
   | [] -> ()
   | a::q ->
     let s = get_seq_heap heap2 addrs a in       
     B.g_upd_seq_as_seq a s mem;         
     let m' = B.g_upd_seq a s mem in
     if StrongExcludedMiddle.strong_excluded_middle (a == b) then (
       if StrongExcludedMiddle.strong_excluded_middle (List.memP b accu) then (
         B.lemma_g_upd_with_same_seq a mem;       
         update_buffer_up_mem_aux ptrs addrs m' b heap1 heap2 q (a::accu)
       ) else (
         g_upd_tot_correct_down_invariant ptrs addrs heap1 heap2 b mem;
         g_upd_tot_correct_down mem addrs heap2 b;
         update_buffer_up_mem_aux ptrs addrs m' b heap1 heap2 q (a::accu)
       )
     ) else (
       assert (B.disjoint a b);
       get_seq_heap_as_seq heap1 heap2 addrs mem a;
       B.lemma_g_upd_with_same_seq a mem;       
       update_buffer_up_mem_aux ptrs addrs m' b heap1 heap2 q (a::accu)
     )

let update_buffer_up_mem ptrs addrs mem b heap1 heap2 =
  update_buffer_up_mem_aux ptrs addrs mem b heap1 heap2 ptrs []
