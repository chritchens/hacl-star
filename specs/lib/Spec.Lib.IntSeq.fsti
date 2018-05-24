module Spec.Lib.IntSeq

open Spec.Lib.IntTypes


///
/// Definition of sequences
///

val seq: a:Type0 -> t:Type0

val length: #a:Type0 -> seq a -> size_nat

//val lseq: a:Type0 -> len:size_nat -> Type0

let lseq (a:Type0) (len:size_nat) = s:seq a{length s == len}

type intseq (t:m_inttype) (len:size_nat) = lseq (uint_t t) len

///
/// Definition of byte-based sequences
///

type bytes = seq uint8

type lbytes (len:size_nat) = lseq uint8 len

///
/// Conversions operations
///

val to_lseq: #a:Type0 -> s:seq a -> lseq a (length s)

val to_lbytes: b:bytes -> lbytes (length b)

val to_seq: #a:Type0 -> #len:size_nat -> s:lseq a len -> o:seq a {length o == len}

val to_bytes: #len:size_nat -> b:lbytes len -> o:bytes{length o == len}


///
/// Operations on sequences
///

val index: #a:Type -> #len:size_nat -> s:lseq a len -> n:size_nat{n < len} -> a

val upd: #a:Type -> #len:size_nat -> s:lseq a len -> n:size_nat{n < len /\ len > 0} -> x:a -> Pure (lseq a len)
    (requires True)
    (ensures (fun o -> index o n == x /\
      (forall (i:size_nat). {:pattern (index s i)} (i < len /\ i <> n) ==> index o i == index s i)))

///
/// Allocation functions for sequences
///

val create: #a:Type -> len:size_nat -> init:a -> s:lseq a len{
    forall (i:size_nat). {:pattern (index s i)} i < len ==> index s i == init}

val createL: #a:Type -> l:list a{List.Tot.length l <= maxint U32} -> lseq a (List.Tot.length l)

//val copy: #a:Type -> #len:size_nat -> lseq a len -> lseq a len

val sub: #a:Type -> #len:size_nat -> lseq a len -> start:size_nat -> n:size_nat{start + n <= len} -> lseq a n

let slice (#a:Type) (#len:size_nat) (i:lseq a len) (start:size_nat)
	  (fin:size_nat{start <= fin /\ fin <= len}) =
	  sub #a #len i start (fin - start)

val update_sub: #a:Type -> #len:size_nat -> i:lseq a len -> start:size_nat -> n:size_nat{start + n <= len} -> x:lseq a n -> o:lseq a len{sub o start n == x}

let update_slice (#a:Type) (#len:size_nat) (i:lseq a len) (start:size_nat) (fin:size_nat{start <= fin /\ fin <= len}) (upd:lseq a (fin - start)) = 
		 update_sub #a #len i start (fin-start) upd


let op_String_Access #a #len = index #a #len
let op_String_Assignment #a #len = upd #a #len


val repeat_range: #a:Type -> min:size_nat -> max:size_nat{min <= max} -> (i:size_nat{i >= min /\ i < max}  -> a -> Tot a) -> a -> Tot (a)

(* BB: I think, this might not be necessary *)
val repeat_range_ghost: #a:Type -> min:size_nat -> max:size_nat{min <= max} -> (i:size_nat{i >= min /\ i < max}  -> a -> GTot a) -> a -> GTot (a)

val repeati: #a:Type -> n:size_nat -> (i:size_nat{i < n}  -> a -> Tot a) -> a -> Tot (a)

(* BB: I think, this might not be necessary *)
val repeati_ghost: #a:Type -> n:size_nat -> (i:size_nat{i < n}  -> a -> GTot a) -> a -> GTot a

val repeat: #a:Type -> n:size_nat -> (a -> Tot a) -> a -> Tot (a)

unfold type repeatable (#a:Type) (#n:size_nat) (pred:(i:size_nat{i <= n} -> a -> Tot Type)) = i:size_nat{i < n} -> x:a -> Pure a (requires (pred i x)) (ensures (fun r -> pred (i+1) r))

val repeat_range_inductive: #a:Type -> min:size_nat -> max:size_nat{min <= max} -> pred:(i:size_nat{i <= max} -> a -> Tot Type) -> f:repeatable #a #max pred -> x0:a{pred min x0} -> Tot (res:a{pred max res})

val repeati_inductive: #a:Type -> n:size_nat -> pred:(i:size_nat{i <= n} -> a -> Tot Type) -> f:repeatable #a #n pred -> x0:a{pred 0 x0} -> Tot (res:a{pred n res})

val fold_left_range: #a:Type -> #b:Type -> #len:size_nat -> min:size_nat -> max:size_nat{min <= max /\ max <= len} -> (i:size_nat{i >= min /\ i < max} -> a -> b -> Tot b) -> lseq a len -> b -> Tot (b)

val fold_lefti: #a:Type -> #b:Type -> #len:size_nat -> (i:size_nat{i < len} -> a -> b -> Tot b) -> lseq a len -> b -> Tot (b)

val fold_left: #a:Type -> #b:Type -> #len:size_nat -> (a -> b -> Tot b) -> lseq a len -> b -> Tot (b)

val map: #a:Type -> #b:Type -> #len:size_nat -> (a -> Tot b) -> lseq a len -> lseq b len

//val mapi: #a:Type -> #b:Type -> #len:size_nat -> (i:size_nat{i < len} -> a -> Tot b) -> lseq a len -> lseq b len

val for_all: #a:Type -> #len:size_nat -> (a -> Tot bool) -> lseq a len -> bool


val ghost_map: #a:Type -> #b:Type -> #len:size_nat -> (a -> GTot b) -> lseq a len -> GTot (lseq b len)

val map2: #a:Type -> #b:Type -> #c:Type -> #len:size_nat -> (a -> b -> Tot c) -> lseq a len -> lseq b len -> lseq c len

val for_all2: #a:Type -> #b:Type -> #len:size_nat -> (a -> b -> Tot bool) -> lseq a len -> lseq b len -> bool

///
/// Conversions between natural numbers and sequences
///

val nat_from_intseq_be: #t:m_inttype -> #len:size_nat -> b:intseq t len -> Tot (n:nat{n < pow2 (len `op_Multiply` bits t)})

val nat_from_intseq_le: #t:m_inttype -> #len:size_nat -> b:intseq t len -> Tot (n:nat{n < pow2 (len `op_Multiply` bits t)})

val nat_from_bytes_be: #len:size_nat -> b:lbytes len -> Tot (n:nat{n < pow2 (len `op_Multiply` 8)})

val nat_from_bytes_le: #len:size_nat -> b:lbytes len -> Tot (n:nat{n < pow2 (len `op_Multiply` 8)})

val nat_to_bytes_be: len:size_nat -> n:nat{n < pow2 (8 `op_Multiply` len)} ->  Tot (b:lbytes len {n == nat_from_intseq_be #U8 #len b})

val nat_to_bytes_le: len:size_nat -> n:nat{n < pow2 (8 `op_Multiply` len)} ->  Tot (b:lbytes len {n == nat_from_intseq_le #U8 #len b})

val uint_to_bytes_le: #t:m_inttype -> u:uint_t t -> lbytes (numbytes t)

val uint_to_bytes_be: #t:m_inttype -> u:uint_t t -> lbytes (numbytes t)

val uint_from_bytes_le: #t:m_inttype -> lbytes (numbytes t) -> u:uint_t t

val uint_from_bytes_be: #t:m_inttype -> lbytes (numbytes t) -> u:uint_t t

val uints_to_bytes_le: #t:m_inttype -> #len:size_nat{len `op_Multiply` numbytes t <= max_size_t} -> intseq t len -> lbytes (len `op_Multiply` numbytes t)

val uints_to_bytes_be: #t:m_inttype -> #len:size_nat{len `op_Multiply` numbytes t <= max_size_t} -> intseq t len -> lbytes (len `op_Multiply` numbytes t)

val uints_from_bytes_le: #t:m_inttype -> #len:size_nat{len `op_Multiply` numbytes t <= max_size_t} -> lbytes (len `op_Multiply` numbytes t) -> intseq t len

val uints_from_bytes_be: #t:m_inttype -> #len:size_nat{len `op_Multiply` numbytes t <= max_size_t} -> lbytes (len `op_Multiply` numbytes t) -> intseq t len


///
/// Unsafe functions
/// !!! The following function is primarily meant for testing, do not rely on it in code. !!!
///

val as_list: #a:Type -> #len:size_nat -> lseq a len -> l:list a{List.Tot.length l = len}


///
/// Experimental functions
///

val concat: #a:Type -> #len1:size_nat -> #len2:size_nat{len1 + len2 <= maxint SIZE} -> lseq a len1 -> lseq a len2 -> lseq a (len1 + len2)
let (@|) #a #len1 #len2 s1 s2 = concat #a #len1 #len2 s1 s2

open FStar.Mul
val map_blocks: #a:Type0 ->
		blocksize:size_nat{blocksize > 0} ->
		nblocks:size_nat{nblocks * blocksize <= maxint SIZE} ->
		f:(i:size_nat{i + 1 <= nblocks} -> lseq a blocksize -> lseq a blocksize) ->
		inp: lseq a (nblocks * blocksize) ->
		out:  lseq a (nblocks * blocksize) 
val reduce_blocks: #a:Type0 -> #b:Type0 ->
		blocksize:size_nat{blocksize > 0} ->
		nblocks:size_nat{nblocks * blocksize <= maxint SIZE} ->
		f:(i:size_nat{i + 1 <= nblocks} -> lseq a blocksize -> b -> b) ->
		inp: lseq a (nblocks * blocksize) ->
		init: b ->
		out:  b

