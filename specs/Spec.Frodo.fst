module Spec.Frodo

open FStar.Mul
open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence
open Lib.RawIntTypes
open FStar.Math.Lemmas

open Spec.PQ.Lib
open Spec.Keccak

assume val zqmatrix_eq:
  #q:size_pos -> #n1:size_pos -> #n2:size_pos ->
  a:zqmatrix_t q n1 n2 -> b:zqmatrix_t q n1 n2 -> Tot bool

assume val lbytes_eq:
  #len:size_nat -> a:lbytes len -> b:lbytes len -> Tot bool

val cshake128_frodo:
  input_len:size_nat -> input:lbytes input_len ->
  cstm:uint16 -> output_len:size_nat -> Tot (lbytes output_len)
let cshake128_frodo input_len input cstm output_len =
  let s = create 25 (u64 0) in
  let s = s.[0] <- (u64 0x10010001a801) |. (shift_left (to_u64 cstm) (u32 48)) in
  let s = state_permute s in
  let s = absorb s 168 input_len input (u8 0x04) in
  squeeze s 168 output_len

val cshake256_frodo:
  input_len:size_nat -> input:lbytes input_len ->
  cstm:uint16 -> output_len:size_nat -> Tot (lbytes output_len)
let cshake256_frodo input_len input cstm output_len =
  let s = create 25 (u64 0) in
  let s = s.[0] <- (u64 0x100100018801) |. (shift_left (to_u64 cstm) (u32 48)) in
  let s = state_permute s in
  let s = absorb s 136 input_len input (u8 0x04) in
  squeeze s 136 output_len

//FrodoKEM-640
let params_n:size_pos = 640
let params_logq:size_pos = 15
let params_extracted_bits:size_pos = 2
let crypto_bytes:size_pos = 16
let cshake_frodo = cshake128_frodo
let cdf_table_len:size_pos = 12
let cdf_table : lseq size_nat cdf_table_len =
  let cdf_table0: list size_nat = [4727; 13584; 20864; 26113; 29434; 31278; 32176; 32560; 32704; 32751; 32764; 32767] in
  assert_norm (List.Tot.length cdf_table0 = cdf_table_len);
  createL cdf_table0

let bytes_seed_a:size_pos = 16
let params_nbar:size_pos = 8
let params_q:size_pos = pow2 params_logq
let bytes_mu:size_pos = (params_extracted_bits * params_nbar * params_nbar) / 8
let crypto_publickeybytes:size_pos  = bytes_seed_a + (params_logq * params_n * params_nbar) / 8
let crypto_secretkeybytes:size_pos  = crypto_bytes + crypto_publickeybytes
let crypto_ciphertextbytes:size_pos = ((params_nbar * params_n + params_nbar * params_nbar) * params_logq) / 8 + crypto_bytes

val ec:k:size_nat{k < pow2 params_extracted_bits} -> Tot (r:size_nat{r < pow2 params_logq})
let ec k = k * pow2 (params_logq - params_extracted_bits)

val dc:c:size_nat{c < pow2 params_logq} -> Tot (r:size_nat{r < pow2 params_extracted_bits})
let dc c = ((c + pow2 (params_logq - params_extracted_bits - 1)) / pow2 (params_logq - params_extracted_bits)) % pow2 params_extracted_bits

val lemma_dc_ec:
  k:size_nat{k < pow2 params_extracted_bits} -> Lemma (dc (ec k) == k)
  #reset-options "--z3rlimit 50 --max_fuel 0"
let lemma_dc_ec k =
  let c = ec k in
  assert (c == k * pow2 (params_logq - params_extracted_bits));
  assert (dc c == ((c + pow2 (params_logq - params_extracted_bits - 1)) / pow2 (params_logq - params_extracted_bits)) % pow2 params_extracted_bits);
  assert (dc c == ((k * pow2 (params_logq - params_extracted_bits) + pow2 (params_logq - params_extracted_bits - 1)) / pow2 (params_logq - params_extracted_bits)) % pow2 params_extracted_bits);
  pow2_plus 1 (params_logq - params_extracted_bits - 1);
  //assert (pow2 (params_logq - params_extracted_bits) = pow2 1 * pow2 (params_logq - params_extracted_bits - 1));
  distributivity_add_left (k * pow2 1) 1 (pow2 (params_logq - params_extracted_bits - 1));
  //assert (dc c == (((k * pow2 1 + 1) * pow2 (params_logq - params_extracted_bits - 1)) / (pow2 1 * pow2 (params_logq - params_extracted_bits - 1))) % pow2 params_extracted_bits);
  division_multiplication_lemma ((k * pow2 1 + 1) * pow2 (params_logq - params_extracted_bits - 1))  (pow2 (params_logq - params_extracted_bits - 1)) (pow2 1);
  //assert (dc c == (((k * pow2 1 + 1) * pow2 (params_logq - params_extracted_bits - 1)) /  pow2 (params_logq - params_extracted_bits - 1) / pow2 1) % pow2 params_extracted_bits);
  multiple_division_lemma (k * pow2 1 + 1) (pow2 (params_logq - params_extracted_bits - 1));
  //assert (dc c == ((k * pow2 1 + 1) / pow2 1) % pow2 params_extracted_bits);
  division_addition_lemma 1 (pow2 1) k;
  //assert (dc c == (k + 1 / pow2 1) % pow2 params_extracted_bits);
  small_division_lemma_1 1 (pow2 1);
  small_modulo_lemma_1 k (pow2 params_extracted_bits)

assume val frodo_key_encode:
  b:size_nat{(params_nbar * params_nbar * b) / 8 < max_size_t} ->
  a:lbytes ((params_nbar * params_nbar * b) / 8) ->
  Tot (zqmatrix_t params_q params_nbar params_nbar)
//let frodo_key_encode b a = admit()

assume val frodo_key_decode:
  b:size_nat{(params_nbar * params_nbar * b) / 8 < max_size_t} ->
  a:zqmatrix_t params_q params_nbar params_nbar ->
  Tot (lbytes ((params_nbar * params_nbar * b) / 8))
//let frodo_key_decode b a = admit()

assume val frodo_pack:
  n1:size_pos -> n2:size_pos ->
  a:zqmatrix_t params_q n1 n2 ->
  d:size_nat{(d * n1 * n2) / 8 < max_size_t} -> Tot (lbytes ((d * n1 * n2) / 8))
//let frodo_pack n1 n2 a d =

assume val frodo_unpack:
  n1:size_pos -> n2:size_pos ->
  d:size_nat{(d * n1 * n2) / 8 < max_size_t} -> b:lbytes ((d * n1 * n2) / 8) ->
  Tot (zqmatrix_t params_q n1 n2)
//let frodo_unpack n1 n2 d b = admit()

val frodo_sample: r:uint16 -> Tot (zqelem_t params_q)
#reset-options "--z3rlimit 50 --max_fuel 1"
let frodo_sample r =
  let t = r >>. u32 1 in
  let e = 0 in
  let r0 = r &. u16 1 in

  let e = repeati (cdf_table_len - 1)
  (fun z e ->
    let e = if (uint_to_nat t > cdf_table.[z]) then e + 1 else e in e
  ) e in
  assume (e < cdf_table_len);
  let e = (FStar.Math.Lib.powx (-1) (uint_to_nat r0)) * e in
  assume (-cdf_table_len < e /\ e < cdf_table_len);
  zqelem (e + params_q)

val frodo_sample_matrix:
  n1:size_pos -> n2:size_pos{2 * n1 * n2 < max_size_t} ->
  seedLen:size_nat -> seed:lbytes seedLen ->
  ctr:uint16 -> Tot (zqmatrix_t params_q n1 n2)
let frodo_sample_matrix n1 n2 seedLen seed ctr =
  let r = cshake_frodo seedLen seed ctr (2 * n1 * n2) in
  let res = zqmatrix_create params_q n1 n2 in
  repeati n1
  (fun i res ->
    repeati n2
    (fun j res ->
      assume (2 * (n2 * i + j) + 2 <= 2 * n1 * n2);
      let res_ij = sub r (2 * (n2 * i + j)) 2 in
      set res i j (frodo_sample (uint_from_bytes_le #U16 res_ij))
    ) res
  ) res

val frodo_sample_matrix_tr:
  n1:size_pos -> n2:size_pos{2 * n1 * n2 < max_size_t} ->
  seedLen:size_nat -> seed:lbytes seedLen ->
  ctr:uint16 -> Tot (zqmatrix_t params_q n1 n2)
let frodo_sample_matrix_tr n1 n2 seedLen seed ctr =
  let r = cshake_frodo seedLen seed ctr (2 * n1 * n2) in
  let res = zqmatrix_create params_q n1 n2 in
  repeati n1
  (fun i res ->
    repeati n2
    (fun j res ->
      assume (2 * (n1 * j + i) + 2 <= 2 * n1 * n2);
      let res_ij = sub r (2 * (n1 * j + i)) 2 in
      set res i j (frodo_sample (uint_from_bytes_le #U16 res_ij))
    ) res
  ) res

val frodo_gen_matrix_cshake:
  n:size_pos{2 * n < max_size_t /\ 256 + n < maxint U16} -> seedLen:size_nat -> seed:lbytes seedLen ->
  Tot (zqmatrix_t params_q n n)
let frodo_gen_matrix_cshake n seedLen seed =
  let res = zqmatrix_create params_q n n in
  repeati n
  (fun i res ->
    let res_i = cshake128_frodo seedLen seed (u16 (256 + i)) (2 * n) in
    repeati n
    (fun j res ->
      let res_ij = uint_from_bytes_le #U16 (sub res_i (j * 2) 2) in
      set res i j (zqelem #params_q (uint_to_nat res_ij))
    ) res
  ) res

let frodo_gen_matrix = frodo_gen_matrix_cshake

val crypto_kem_keypair:
  coins:lbytes (2 * crypto_bytes + bytes_seed_a) ->
  Tot (tuple2 (lbytes crypto_publickeybytes) (tuple2 (lbytes crypto_secretkeybytes) (zqmatrix_t params_q params_n params_nbar)))
let crypto_kem_keypair coins =
  let s = sub coins 0 crypto_bytes in
  let seed_e = sub coins crypto_bytes crypto_bytes in
  let seed_a = sub coins (2 * crypto_bytes) bytes_seed_a in

  let a_matrix = frodo_gen_matrix params_n bytes_seed_a seed_a in
  let s_matrix = frodo_sample_matrix_tr params_n params_nbar crypto_bytes seed_e (u16 1) in
  let e_matrix = frodo_sample_matrix params_n params_nbar crypto_bytes seed_e (u16 2) in
  let b_matrix = zqmatrix_add (zqmatrix_mul a_matrix s_matrix) e_matrix in
  let b = frodo_pack params_n params_nbar b_matrix params_logq in

  let pk = concat seed_a b in
  let sk = concat s pk in
  (pk,  (sk, s_matrix))

val crypto_kem_enc:
  coins:lbytes bytes_mu -> pk:lbytes crypto_publickeybytes ->
  Tot (tuple2 (lbytes crypto_ciphertextbytes) (lbytes crypto_bytes))
let crypto_kem_enc coins pk =
  let seed_a = sub pk 0 bytes_seed_a in
  let b = sub pk bytes_seed_a (crypto_publickeybytes - bytes_seed_a) in

  let g = cshake_frodo (crypto_publickeybytes + bytes_mu) (concat pk coins) (u16 3) (3 * crypto_bytes) in
  let seed_e = sub g 0 crypto_bytes in
  let k = sub g crypto_bytes crypto_bytes in
  let d = sub g (2*crypto_bytes) crypto_bytes in

  let sp_matrix = frodo_sample_matrix params_nbar params_n crypto_bytes seed_e (u16 4) in
  let ep_matrix = frodo_sample_matrix params_nbar params_n crypto_bytes seed_e (u16 5) in
  let a_matrix = frodo_gen_matrix params_n bytes_seed_a seed_a in
  let bp_matrix = zqmatrix_add (zqmatrix_mul sp_matrix a_matrix) ep_matrix in
  let c1 = frodo_pack params_nbar params_n bp_matrix params_logq in

  let epp_matrix = frodo_sample_matrix params_nbar params_nbar crypto_bytes seed_e (u16 6) in
  let b_matrix = frodo_unpack params_n params_nbar params_logq b in
  let v_matrix = zqmatrix_add (zqmatrix_mul sp_matrix b_matrix) epp_matrix in

  let mu_encode = frodo_key_encode params_extracted_bits coins in
  let c_matrix = zqmatrix_add v_matrix mu_encode in
  let c2 = frodo_pack params_nbar params_nbar c_matrix params_logq in

  let ss_init = concat c1 (concat c2 (concat k d)) in
  let ss_init_len = (params_logq * params_nbar * params_n) / 8 + (params_logq * params_nbar * params_nbar) / 8 + 2 * crypto_bytes in
  let ss = cshake_frodo ss_init_len ss_init (u16 7) crypto_bytes in
  let ct = concat c1 (concat c2 d) in
  (ct, ss)

val crypto_kem_dec:
  ct:lbytes crypto_ciphertextbytes ->
  sk:tuple2 (lbytes crypto_secretkeybytes) (zqmatrix_t params_q params_n params_nbar) ->
  Tot (lbytes crypto_bytes)
let crypto_kem_dec ct sk =
  let c1Len = (params_logq * params_nbar * params_n) / 8 in
  let c2Len = (params_logq * params_nbar * params_nbar) / 8 in
  let c1 = sub ct 0 c1Len in
  let c2 = sub ct c1Len c2Len in
  let d = sub ct (c1Len+c2Len) crypto_bytes in

  let sk1, s_matrix = sk in
  let s = sub sk1 0 crypto_bytes in
  let pk = sub sk1 crypto_bytes crypto_publickeybytes in
  let seed_a = sub pk 0 bytes_seed_a in
  let b = sub pk bytes_seed_a (crypto_publickeybytes - bytes_seed_a) in

  let bp_matrix = frodo_unpack params_nbar params_n params_logq c1 in
  let c_matrix = frodo_unpack params_nbar params_nbar params_logq c2 in
  let m_matrix = zqmatrix_sub c_matrix (zqmatrix_mul bp_matrix s_matrix) in
  let mu_decode = frodo_key_decode params_extracted_bits m_matrix in

  let g = cshake_frodo (crypto_publickeybytes + (params_nbar * params_nbar * params_extracted_bits) / 8) (concat pk mu_decode)  (u16 3) (3 * crypto_bytes) in
  let seed_ep = sub g 0 crypto_bytes in
  let kp = sub g crypto_bytes crypto_bytes in
  let dp = sub g (2*crypto_bytes) crypto_bytes in

  let sp_matrix = frodo_sample_matrix params_nbar params_n crypto_bytes seed_ep (u16 4) in
  let ep_matrix = frodo_sample_matrix params_nbar params_n crypto_bytes seed_ep (u16 5) in
  let a_matrix = frodo_gen_matrix params_n bytes_seed_a seed_a in
  let bpp_matrix = zqmatrix_add (zqmatrix_mul sp_matrix a_matrix) ep_matrix in

  let epp_matrix = frodo_sample_matrix params_nbar params_nbar crypto_bytes seed_ep (u16 6) in
  let b_matrix = frodo_unpack params_n params_nbar params_logq b in
  let v_matrix = zqmatrix_add (zqmatrix_mul sp_matrix b_matrix) epp_matrix in

  let mu_encode = frodo_key_encode params_extracted_bits mu_decode in
  let cp_matrix = zqmatrix_add v_matrix mu_encode in

  let ss_init = concat c1 c2 in
  let ss_init_len = (params_logq * params_nbar * params_n) / 8 + (params_logq * params_nbar * params_nbar) / 8 + 2 * crypto_bytes in
  let ss_init1:lbytes ss_init_len = concat ss_init (concat kp d) in
  let ss_init2:lbytes ss_init_len = concat ss_init (concat s d) in
  let bcond = (lbytes_eq #crypto_bytes d dp) && (zqmatrix_eq #params_q #params_nbar #params_n bp_matrix bpp_matrix) && (zqmatrix_eq #params_q #params_nbar #params_nbar c_matrix cp_matrix) in
  let ss_init = if (bcond) then ss_init1 else ss_init2 in
  let ss = cshake_frodo ss_init_len ss_init (u16 7) crypto_bytes in
  ss