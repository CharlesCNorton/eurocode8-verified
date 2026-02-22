
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



(** val pred : int -> int **)

let pred = fun n -> Stdlib.max 0 (n-1)

module Coq__1 = struct
 (** val add : int -> int -> int **)

 let rec add = (+)
end
include Coq__1

(** val mul : int -> int -> int **)

let rec mul = ( * )

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Nat =
 struct
  (** val add : int -> int -> int **)

  let rec add n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun p -> Stdlib.Int.succ (add p m))
      n

  (** val mul : int -> int -> int **)

  let rec mul n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun p -> add m (mul p m))
      n

  (** val pow : int -> int -> int **)

  let rec pow n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Stdlib.Int.succ 0)
      (fun m0 -> mul n (pow n m0))
      m
 end

module Pos =
 struct
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q1 -> XO (add_carry p q1)
       | XO q1 -> XI (add p q1)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q1 -> XI (add p q1)
       | XO q1 -> XO (add p q1)
       | XH -> XI p)
    | XH -> (match y with
             | XI q1 -> XO (succ q1)
             | XO q1 -> XI q1
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q1 -> XI (add_carry p q1)
       | XO q1 -> XO (add_carry p q1)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q1 -> XO (add_carry p q1)
       | XO q1 -> XI (add p q1)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q1 -> XI (succ q1)
       | XO q1 -> XO (succ q1)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q1 -> double_mask (sub_mask p q1)
       | XO q1 -> succ_double_mask (sub_mask p q1)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q1 -> succ_double_mask (sub_mask_carry p q1)
       | XO q1 -> double_mask (sub_mask p q1)
       | XH -> IsPos (pred_double p))
    | XH -> (match y with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q1 -> succ_double_mask (sub_mask_carry p q1)
       | XO q1 -> double_mask (sub_mask p q1)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q1 -> double_mask (sub_mask_carry p q1)
       | XO q1 -> succ_double_mask (sub_mask_carry p q1)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val sub : positive -> positive -> positive **)

  let sub x y =
    match sub_mask x y with
    | IsPos z0 -> z0
    | _ -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val size_nat : positive -> int **)

  let rec size_nat = function
  | XI p0 -> Stdlib.Int.succ (size_nat p0)
  | XO p0 -> Stdlib.Int.succ (size_nat p0)
  | XH -> Stdlib.Int.succ 0

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q1 -> compare_cont r p q1
       | XO q1 -> compare_cont Gt p q1
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q1 -> compare_cont Lt p q1
       | XO q1 -> compare_cont r p q1
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val ggcdn :
      int -> positive -> positive -> positive * (positive * positive) **)

  let rec ggcdn n a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> (XH, (a, b)))
      (fun n0 ->
      match a with
      | XI a' ->
        (match b with
         | XI b' ->
           (match compare a' b' with
            | Eq -> (a, (XH, XH))
            | Lt ->
              let (g, p) = ggcdn n0 (sub b' a') a in
              let (ba, aa) = p in (g, (aa, (add aa (XO ba))))
            | Gt ->
              let (g, p) = ggcdn n0 (sub a' b') b in
              let (ab, bb) = p in (g, ((add bb (XO ab)), bb)))
         | XO b0 ->
           let (g, p) = ggcdn n0 a b0 in
           let (aa, bb) = p in (g, (aa, (XO bb)))
         | XH -> (XH, (a, XH)))
      | XO a0 ->
        (match b with
         | XI _ ->
           let (g, p) = ggcdn n0 a0 b in
           let (aa, bb) = p in (g, ((XO aa), bb))
         | XO b0 -> let (g, p) = ggcdn n0 a0 b0 in ((XO g), p)
         | XH -> (XH, (a, XH)))
      | XH -> (XH, (XH, b)))
      n

  (** val ggcd : positive -> positive -> positive * (positive * positive) **)

  let ggcd a b =
    ggcdn (Coq__1.add (size_nat a) (size_nat b)) a b

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> int **)

  let to_nat x =
    iter_op Coq__1.add x (Stdlib.Int.succ 0)

  (** val of_nat : int -> positive **)

  let rec of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> XH)
      (fun x ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> XH)
        (fun _ -> succ (of_nat x))
        x)
      n

  (** val of_succ_nat : int -> positive **)

  let rec of_succ_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> XH)
      (fun x -> succ (of_succ_nat x))
      n
 end

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Coq_Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Coq_Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q1 -> double (pos_sub p q1)
       | XO q1 -> succ_double (pos_sub p q1)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q1 -> pred_double (pos_sub p q1)
       | XO q1 -> double (pos_sub p q1)
       | XH -> Zpos (Coq_Pos.pred_double p))
    | XH ->
      (match y with
       | XI q1 -> Zneg (XO q1)
       | XO q1 -> Zneg (Coq_Pos.pred_double q1)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Coq_Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Coq_Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val sub : z -> z -> z **)

  let sub m n =
    add m (opp n)

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Coq_Pos.mul x' y')
       | Zneg y' -> Zneg (Coq_Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Coq_Pos.mul x' y')
       | Zneg y' -> Zpos (Coq_Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Coq_Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Coq_Pos.compare x' y')
       | _ -> Lt)

  (** val sgn : z -> z **)

  let sgn = function
  | Z0 -> Z0
  | Zpos _ -> Zpos XH
  | Zneg _ -> Zneg XH

  (** val max : z -> z -> z **)

  let max n m =
    match compare n m with
    | Lt -> m
    | _ -> n

  (** val min : z -> z -> z **)

  let min n m =
    match compare n m with
    | Gt -> m
    | _ -> n

  (** val abs : z -> z **)

  let abs = function
  | Zneg p -> Zpos p
  | x -> x

  (** val to_nat : z -> int **)

  let to_nat = function
  | Zpos p -> Coq_Pos.to_nat p
  | _ -> 0

  (** val of_nat : int -> z **)

  let of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Z0)
      (fun n0 -> Zpos (Coq_Pos.of_succ_nat n0))
      n

  (** val to_pos : z -> positive **)

  let to_pos = function
  | Zpos p -> p
  | _ -> XH

  (** val ggcd : z -> z -> z * (z * z) **)

  let ggcd a b =
    match a with
    | Z0 -> ((abs b), (Z0, (sgn b)))
    | Zpos a0 ->
      (match b with
       | Z0 -> ((abs a), ((sgn a), Z0))
       | Zpos b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zpos aa), (Zpos bb)))
       | Zneg b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zpos aa), (Zneg bb))))
    | Zneg a0 ->
      (match b with
       | Z0 -> ((abs a), ((sgn a), Z0))
       | Zpos b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zneg aa), (Zpos bb)))
       | Zneg b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zneg aa), (Zneg bb))))
 end

(** val z_lt_dec : z -> z -> bool **)

let z_lt_dec x y =
  match Z.compare x y with
  | Lt -> true
  | _ -> false

(** val z_lt_ge_dec : z -> z -> bool **)

let z_lt_ge_dec =
  z_lt_dec

(** val z_lt_le_dec : z -> z -> bool **)

let z_lt_le_dec =
  z_lt_ge_dec

(** val pow_pos : ('a1 -> 'a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

let rec pow_pos rmul x = function
| XI i0 -> let p = pow_pos rmul x i0 in rmul x (rmul p p)
| XO i0 -> let p = pow_pos rmul x i0 in rmul p p
| XH -> x

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

type q = { qnum : z; qden : positive }

(** val qplus : q -> q -> q **)

let qplus x y =
  { qnum = (Z.add (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden)));
    qden = (Coq_Pos.mul x.qden y.qden) }

(** val qmult : q -> q -> q **)

let qmult x y =
  { qnum = (Z.mul x.qnum y.qnum); qden = (Coq_Pos.mul x.qden y.qden) }

(** val qopp : q -> q **)

let qopp x =
  { qnum = (Z.opp x.qnum); qden = x.qden }

(** val qminus : q -> q -> q **)

let qminus x y =
  qplus x (qopp y)

(** val qinv : q -> q **)

let qinv x =
  match x.qnum with
  | Z0 -> { qnum = Z0; qden = XH }
  | Zpos p -> { qnum = (Zpos x.qden); qden = p }
  | Zneg p -> { qnum = (Zneg x.qden); qden = p }

(** val qlt_le_dec : q -> q -> bool **)

let qlt_le_dec x y =
  z_lt_le_dec (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden))

(** val qarchimedean : q -> positive **)

let qarchimedean q1 =
  let { qnum = qnum0; qden = _ } = q1 in
  (match qnum0 with
   | Zpos p -> Coq_Pos.add p XH
   | _ -> XH)

(** val qpower_positive : q -> positive -> q **)

let qpower_positive =
  pow_pos qmult

(** val qpower : q -> z -> q **)

let qpower q1 = function
| Z0 -> { qnum = (Zpos XH); qden = XH }
| Zpos p -> qpower_positive q1 p
| Zneg p -> qinv (qpower_positive q1 p)

(** val qabs : q -> q **)

let qabs x =
  let { qnum = n; qden = d } = x in { qnum = (Z.abs n); qden = d }

(** val pos_log2floor_plus1 : positive -> positive **)

let rec pos_log2floor_plus1 = function
| XI p' -> Coq_Pos.succ (pos_log2floor_plus1 p')
| XO p' -> Coq_Pos.succ (pos_log2floor_plus1 p')
| XH -> XH

(** val qbound_lt_ZExp2 : q -> z **)

let qbound_lt_ZExp2 q1 =
  match q1.qnum with
  | Z0 -> Zneg (XO (XO (XO (XI (XO (XI (XI (XI (XI XH)))))))))
  | Zpos p ->
    Z.pos_sub (Coq_Pos.succ (pos_log2floor_plus1 p))
      (pos_log2floor_plus1 q1.qden)
  | Zneg _ -> Z0

type cReal = { seq : (z -> q); scale : z }

(** val sig_forall_dec : (int -> bool) -> int option **)

let sig_forall_dec _ =
  None

(** val lowerCutBelow : (q -> bool) -> q **)

let lowerCutBelow f =
  let s =
    sig_forall_dec (fun n ->
      let b = f (qopp { qnum = (Z.of_nat n); qden = XH }) in
      if b then false else true)
  in
  (match s with
   | Some s0 -> qopp { qnum = (Z.of_nat s0); qden = XH }
   | None -> assert false (* absurd case *))

(** val lowerCutAbove : (q -> bool) -> q **)

let lowerCutAbove f =
  let s =
    sig_forall_dec (fun n ->
      let b = f { qnum = (Z.of_nat n); qden = XH } in
      if b then true else false)
  in
  (match s with
   | Some s0 -> { qnum = (Z.of_nat s0); qden = XH }
   | None -> assert false (* absurd case *))

type dReal = (q -> bool)

(** val dRealQlim_rec : (q -> bool) -> int -> int -> q **)

let rec dRealQlim_rec f n p =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> assert false (* absurd case *))
    (fun n0 ->
    let b =
      f
        (qplus (lowerCutBelow f) { qnum = (Z.of_nat n0); qden =
          (Coq_Pos.of_nat (Stdlib.Int.succ n)) })
    in
    if b
    then qplus (lowerCutBelow f) { qnum = (Z.of_nat n0); qden =
           (Coq_Pos.of_nat (Stdlib.Int.succ n)) }
    else dRealQlim_rec f n n0)
    p

(** val dRealAbstr : cReal -> dReal **)

let dRealAbstr x =
  let h = fun q1 n ->
    let s =
      qlt_le_dec
        (qplus q1
          (qpower { qnum = (Zpos (XO XH)); qden = XH } (Z.opp (Z.of_nat n))))
        (x.seq (Z.opp (Z.of_nat n)))
    in
    if s then false else true
  in
  (fun q1 -> match sig_forall_dec (h q1) with
             | Some _ -> true
             | None -> false)

(** val dRealQlim : dReal -> int -> q **)

let dRealQlim x n =
  let s = lowerCutAbove x in
  let s0 = qarchimedean (qminus s (lowerCutBelow x)) in
  dRealQlim_rec x n (mul (Stdlib.Int.succ n) (Coq_Pos.to_nat s0))

(** val dRealQlimExp2 : dReal -> int -> q **)

let dRealQlimExp2 x n =
  dRealQlim x (pred (Nat.pow (Stdlib.Int.succ (Stdlib.Int.succ 0)) n))

(** val cReal_of_DReal_seq : dReal -> z -> q **)

let cReal_of_DReal_seq x n =
  dRealQlimExp2 x (Z.to_nat (Z.opp n))

(** val cReal_of_DReal_scale : dReal -> z **)

let cReal_of_DReal_scale x =
  qbound_lt_ZExp2
    (qplus (qabs (cReal_of_DReal_seq x (Zneg XH))) { qnum = (Zpos (XO XH));
      qden = XH })

(** val dRealRepr : dReal -> cReal **)

let dRealRepr x =
  { seq = (cReal_of_DReal_seq x); scale = (cReal_of_DReal_scale x) }

module type RbaseSymbolsSig =
 sig
  type coq_R

  val coq_Rabst : cReal -> coq_R

  val coq_Rrepr : coq_R -> cReal

  val coq_R0 : coq_R

  val coq_R1 : coq_R

  val coq_Rplus : coq_R -> coq_R -> coq_R

  val coq_Rmult : coq_R -> coq_R -> coq_R

  val coq_Ropp : coq_R -> coq_R
 end

module RbaseSymbolsImpl =
 struct
  (** val coq_Rabst : cReal -> dReal **)

  let coq_Rabst =
    dRealAbstr

  (** val coq_Rrepr : dReal -> cReal **)

  let coq_Rrepr =
    dRealRepr

  (** val coq_Rquot1 : __ **)

  let coq_Rquot1 =
    __

  (** val coq_Rquot2 : __ **)

  let coq_Rquot2 =
    __

  type coq_Rlt = __

  (** val coq_R0_def : __ **)

  let coq_R0_def =
    __

  (** val coq_R1_def : __ **)

  let coq_R1_def =
    __

  (** val coq_Rplus_def : __ **)

  let coq_Rplus_def =
    __

  (** val coq_Rmult_def : __ **)

  let coq_Rmult_def =
    __

  (** val coq_Ropp_def : __ **)

  let coq_Ropp_def =
    __

  (** val coq_Rlt_def : __ **)

  let coq_Rlt_def =
    __
 end

(** val iPR_2 : positive -> float **)

let rec iPR_2 = function
| XI p0 -> ( *. ) (( +. ) 1.0 1.0) (( +. ) 1.0 (iPR_2 p0))
| XO p0 -> ( *. ) (( +. ) 1.0 1.0) (iPR_2 p0)
| XH -> ( +. ) 1.0 1.0

(** val iPR : positive -> float **)

let iPR = function
| XI p0 -> ( +. ) 1.0 (iPR_2 p0)
| XO p0 -> iPR_2 p0
| XH -> 1.0

(** val iZR : z -> float **)

let iZR = function
| Z0 -> 0.0
| Zpos n -> iPR n
| Zneg n -> (fun x -> ~-. x) (iPR n)

module type RinvSig =
 sig
  val coq_Rinv : float -> float
 end

module RinvImpl =
 struct
  (** val coq_Rinv_def : __ **)

  let coq_Rinv_def =
    __
 end



type ground_type =
| GroundA
| GroundB
| GroundC
| GroundD
| GroundE

type spectrum_type =
| Type1
| Type2

type importance_class =
| ClassI
| ClassII
| ClassIII
| ClassIV

(** val gamma_I : importance_class -> float **)

let gamma_I = function
| ClassI ->
  (fun a b -> a /. b) (iZR (Zpos (XO (XO XH)))) (iZR (Zpos (XI (XO XH))))
| ClassII -> iZR (Zpos XH)
| ClassIII ->
  (fun a b -> a /. b) (iZR (Zpos (XO (XI XH)))) (iZR (Zpos (XI (XO XH))))
| ClassIV ->
  (fun a b -> a /. b) (iZR (Zpos (XI (XI XH)))) (iZR (Zpos (XI (XO XH))))

type spectrum_params = { sp_S : float; sp_TB : float; sp_TC : float;
                         sp_TD : float }

(** val spectrum_lookup : spectrum_type -> ground_type -> spectrum_params **)

let spectrum_lookup st gt =
  match st with
  | Type1 ->
    (match gt with
     | GroundA ->
       { sp_S = (iZR (Zpos XH)); sp_TB =
         ((fun a b -> a /. b) (iZR (Zpos (XI XH)))
           (iZR (Zpos (XO (XO (XI (XO XH))))))); sp_TC =
         ((fun a b -> a /. b) (iZR (Zpos (XO XH))) (iZR (Zpos (XI (XO XH)))));
         sp_TD = (iZR (Zpos (XO XH))) }
     | GroundB ->
       { sp_S =
         ((fun a b -> a /. b) (iZR (Zpos (XO (XI XH))))
           (iZR (Zpos (XI (XO XH))))); sp_TB =
         ((fun a b -> a /. b) (iZR (Zpos (XI XH)))
           (iZR (Zpos (XO (XO (XI (XO XH))))))); sp_TC =
         ((fun a b -> a /. b) (iZR (Zpos XH)) (iZR (Zpos (XO XH)))); sp_TD =
         (iZR (Zpos (XO XH))) }
     | GroundC ->
       { sp_S =
         ((fun a b -> a /. b) (iZR (Zpos (XI (XI (XI (XO XH))))))
           (iZR (Zpos (XO (XO (XI (XO XH))))))); sp_TB =
         ((fun a b -> a /. b) (iZR (Zpos XH)) (iZR (Zpos (XI (XO XH)))));
         sp_TC =
         ((fun a b -> a /. b) (iZR (Zpos (XI XH))) (iZR (Zpos (XI (XO XH)))));
         sp_TD = (iZR (Zpos (XO XH))) }
     | GroundD ->
       { sp_S =
         ((fun a b -> a /. b) (iZR (Zpos (XI (XI (XO (XI XH))))))
           (iZR (Zpos (XO (XO (XI (XO XH))))))); sp_TB =
         ((fun a b -> a /. b) (iZR (Zpos XH)) (iZR (Zpos (XI (XO XH)))));
         sp_TC =
         ((fun a b -> a /. b) (iZR (Zpos (XO (XO XH))))
           (iZR (Zpos (XI (XO XH))))); sp_TD = (iZR (Zpos (XO XH))) }
     | GroundE ->
       { sp_S =
         ((fun a b -> a /. b) (iZR (Zpos (XI (XI XH))))
           (iZR (Zpos (XI (XO XH))))); sp_TB =
         ((fun a b -> a /. b) (iZR (Zpos (XI XH)))
           (iZR (Zpos (XO (XO (XI (XO XH))))))); sp_TC =
         ((fun a b -> a /. b) (iZR (Zpos XH)) (iZR (Zpos (XO XH)))); sp_TD =
         (iZR (Zpos (XO XH))) })
  | Type2 ->
    (match gt with
     | GroundA ->
       { sp_S = (iZR (Zpos XH)); sp_TB =
         ((fun a b -> a /. b) (iZR (Zpos XH))
           (iZR (Zpos (XO (XO (XI (XO XH))))))); sp_TC =
         ((fun a b -> a /. b) (iZR (Zpos XH)) (iZR (Zpos (XO (XO XH)))));
         sp_TD =
         ((fun a b -> a /. b) (iZR (Zpos (XO (XI XH))))
           (iZR (Zpos (XI (XO XH))))) }
     | GroundB ->
       { sp_S =
         ((fun a b -> a /. b) (iZR (Zpos (XI (XI (XO (XI XH))))))
           (iZR (Zpos (XO (XO (XI (XO XH))))))); sp_TB =
         ((fun a b -> a /. b) (iZR (Zpos XH))
           (iZR (Zpos (XO (XO (XI (XO XH))))))); sp_TC =
         ((fun a b -> a /. b) (iZR (Zpos XH)) (iZR (Zpos (XO (XO XH)))));
         sp_TD =
         ((fun a b -> a /. b) (iZR (Zpos (XO (XI XH))))
           (iZR (Zpos (XI (XO XH))))) }
     | GroundC ->
       { sp_S =
         ((fun a b -> a /. b) (iZR (Zpos (XI XH))) (iZR (Zpos (XO XH))));
         sp_TB =
         ((fun a b -> a /. b) (iZR (Zpos XH)) (iZR (Zpos (XO (XI (XO XH))))));
         sp_TC =
         ((fun a b -> a /. b) (iZR (Zpos XH)) (iZR (Zpos (XO (XO XH)))));
         sp_TD =
         ((fun a b -> a /. b) (iZR (Zpos (XO (XI XH))))
           (iZR (Zpos (XI (XO XH))))) }
     | GroundD ->
       { sp_S =
         ((fun a b -> a /. b) (iZR (Zpos (XI (XO (XO XH)))))
           (iZR (Zpos (XI (XO XH))))); sp_TB =
         ((fun a b -> a /. b) (iZR (Zpos XH)) (iZR (Zpos (XO (XI (XO XH))))));
         sp_TC =
         ((fun a b -> a /. b) (iZR (Zpos (XI XH)))
           (iZR (Zpos (XO (XI (XO XH)))))); sp_TD =
         ((fun a b -> a /. b) (iZR (Zpos (XO (XI XH))))
           (iZR (Zpos (XI (XO XH))))) }
     | GroundE ->
       { sp_S =
         ((fun a b -> a /. b) (iZR (Zpos (XO (XO (XO XH)))))
           (iZR (Zpos (XI (XO XH))))); sp_TB =
         ((fun a b -> a /. b) (iZR (Zpos XH))
           (iZR (Zpos (XO (XO (XI (XO XH))))))); sp_TC =
         ((fun a b -> a /. b) (iZR (Zpos XH)) (iZR (Zpos (XO (XO XH)))));
         sp_TD =
         ((fun a b -> a /. b) (iZR (Zpos (XO (XI XH))))
           (iZR (Zpos (XI (XO XH))))) })

(** val se : spectrum_params -> float -> float -> float -> float **)

let se p ag eta t =
  if (fun a b -> if a <= b then true else false) t p.sp_TB
  then ( *. ) (( *. ) ag p.sp_S)
         (( +. ) (iZR (Zpos XH))
           (( *. ) ((fun a b -> a /. b) t p.sp_TB)
             (( -. )
               (( *. ) eta
                 ((fun a b -> a /. b) (iZR (Zpos (XI (XO XH))))
                   (iZR (Zpos (XO XH))))) (iZR (Zpos XH)))))
  else if (fun a b -> if a <= b then true else false) t p.sp_TC
       then ( *. ) (( *. ) (( *. ) ag p.sp_S) eta)
              ((fun a b -> a /. b) (iZR (Zpos (XI (XO XH))))
                (iZR (Zpos (XO XH))))
       else if (fun a b -> if a <= b then true else false) t p.sp_TD
            then ( *. )
                   (( *. ) (( *. ) (( *. ) ag p.sp_S) eta)
                     ((fun a b -> a /. b) (iZR (Zpos (XI (XO XH))))
                       (iZR (Zpos (XO XH))))) ((fun a b -> a /. b) p.sp_TC t)
            else ( *. )
                   (( *. ) (( *. ) (( *. ) ag p.sp_S) eta)
                     ((fun a b -> a /. b) (iZR (Zpos (XI (XO XH))))
                       (iZR (Zpos (XO XH)))))
                   ((fun a b -> a /. b) (( *. ) p.sp_TC p.sp_TD) (( *. ) t t))

type ductility_class =
| DCL
| DCM
| DCH

type structural_system =
| FrameSystem
| DualFrameEquiv
| DualWallEquiv
| DuctileWallSystem
| InvertedPendulum
| TorsionallyFlexible

(** val q0 : ductility_class -> structural_system -> float -> float **)

let q0 dc ss au_a1 =
  match dc with
  | DCL -> (fun a b -> a /. b) (iZR (Zpos (XI XH))) (iZR (Zpos (XO XH)))
  | DCM ->
    (match ss with
     | FrameSystem -> ( *. ) (iZR (Zpos (XI XH))) au_a1
     | DualFrameEquiv -> ( *. ) (iZR (Zpos (XI XH))) au_a1
     | InvertedPendulum ->
       (fun a b -> a /. b) (iZR (Zpos (XI XH))) (iZR (Zpos (XO XH)))
     | TorsionallyFlexible -> iZR (Zpos (XO XH))
     | _ -> iZR (Zpos (XI XH)))
  | DCH ->
    (match ss with
     | FrameSystem ->
       ( *. )
         ((fun a b -> a /. b) (iZR (Zpos (XI (XO (XO XH)))))
           (iZR (Zpos (XO XH)))) au_a1
     | DualFrameEquiv ->
       ( *. )
         ((fun a b -> a /. b) (iZR (Zpos (XI (XO (XO XH)))))
           (iZR (Zpos (XO XH)))) au_a1
     | InvertedPendulum -> iZR (Zpos (XO XH))
     | TorsionallyFlexible -> iZR (Zpos (XI XH))
     | _ -> ( *. ) (iZR (Zpos (XO (XO XH)))) au_a1)

(** val beta : float **)

let beta =
  (fun a b -> a /. b) (iZR (Zpos XH)) (iZR (Zpos (XI (XO XH))))

(** val sd : spectrum_params -> float -> float -> float -> float -> float **)

let sd p ag eta q1 t =
  (fun a b -> if a >= b then a else b)
    ((fun a b -> a /. b) (se p ag eta t) q1) (( *. ) beta ag)

(** val lambda : float -> spectrum_params -> int -> float **)

let lambda t1 p n_storeys =
  if (fun a b -> if a <= b then true else false) t1
       (( *. ) (iZR (Zpos (XO XH))) p.sp_TC)
  then if (<=) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
            n_storeys
       then (fun a b -> a /. b) (iZR (Zpos (XI (XO (XO (XO XH))))))
              (iZR (Zpos (XO (XO (XI (XO XH))))))
       else iZR (Zpos XH)
  else iZR (Zpos XH)

(** val fb : float -> float -> float -> float **)

let fb sd_T1 m lam =
  ( *. ) (( *. ) sd_T1 m) lam

type storey = { st_z : float; st_m : float }

(** val sum_zm : storey list -> float **)

let rec sum_zm = function
| [] -> iZR Z0
| s :: rest -> ( +. ) (( *. ) s.st_z s.st_m) (sum_zm rest)

(** val fi : float -> storey -> float -> float **)

let fi fb0 s szm =
  (fun a b -> a /. b) (( *. ) fb0 (( *. ) s.st_z s.st_m)) szm

(** val storey_forces : float -> storey list -> float list **)

let storey_forces fb0 storeys =
  let szm = sum_zm storeys in map (fun s -> fi fb0 s szm) storeys

(** val sum_Fi_eq_Fb : __ **)

let sum_Fi_eq_Fb =
  __

type ns_category =
| NS_Brittle
| NS_Ductile
| NS_None

(** val drift_limit : ns_category -> float **)

let drift_limit = function
| NS_Brittle ->
  (fun a b -> a /. b) (iZR (Zpos XH))
    (iZR (Zpos (XO (XO (XO (XI (XO (XO (XI XH)))))))))
| NS_Ductile ->
  (fun a b -> a /. b) (iZR (Zpos (XI (XI (XI XH)))))
    (iZR (Zpos (XO (XO (XO (XO (XI (XO (XI (XI (XI (XI XH))))))))))))
| NS_None ->
  (fun a b -> a /. b) (iZR (Zpos XH))
    (iZR (Zpos (XO (XO (XI (XO (XO (XI XH))))))))

(** val nu : float **)

let nu =
  (fun a b -> a /. b) (iZR (Zpos XH)) (iZR (Zpos (XO XH)))

(** val drift_ok_dec : ns_category -> float -> float -> bool **)

let drift_ok_dec cat dr h =
  (fun a b -> if a <= b then true else false) (( *. ) dr nu)
    (( *. ) (drift_limit cat) h)

type pdelta_regime =
| PD_Negligible
| PD_Approximate
| PD_Detailed
| PD_Inadmissible

(** val classify_pdelta : float -> pdelta_regime **)

let classify_pdelta th =
  if (fun a b -> if a <= b then true else false) th
       ((fun a b -> a /. b) (iZR (Zpos XH)) (iZR (Zpos (XO (XI (XO XH))))))
  then PD_Negligible
  else if (fun a b -> if a <= b then true else false) th
            ((fun a b -> a /. b) (iZR (Zpos XH)) (iZR (Zpos (XI (XO XH)))))
       then PD_Approximate
       else if (fun a b -> if a <= b then true else false) th
                 ((fun a b -> a /. b) (iZR (Zpos (XI XH)))
                   (iZR (Zpos (XO (XI (XO XH))))))
            then PD_Detailed
            else PD_Inadmissible

(** val pdelta_amplification : float -> float **)

let pdelta_amplification th =
  (fun a b -> a /. b) (iZR (Zpos XH)) (( -. ) (iZR (Zpos XH)) th)

type building = { bld_storeys : storey list; bld_masses : float list;
                  bld_stiffnesses : float list; bld_T1 : float;
                  bld_n_storeys : int; bld_e0x : float; bld_e0y : float;
                  bld_rx : float; bld_ry : float; bld_ls : float }

type seismic_params = { spar_sp : spectrum_params; spar_ag : float;
                        spar_eta : float; spar_q : float;
                        spar_ns_cat : ns_category }

type storey_data = { sd_dr : float; sd_h : float; sd_theta : float }

(** val plan_regular_dec :
    float -> float -> float -> float -> float -> bool **)

let plan_regular_dec e0x e0y rx ry ls =
  let s =
    (fun a b -> if a <= b then true else false) e0x
      (( *. )
        ((fun a b -> a /. b) (iZR (Zpos (XI XH)))
          (iZR (Zpos (XO (XI (XO XH)))))) rx)
  in
  if s
  then let s0 =
         (fun a b -> if a <= b then true else false) e0y
           (( *. )
             ((fun a b -> a /. b) (iZR (Zpos (XI XH)))
               (iZR (Zpos (XO (XI (XO XH)))))) ry)
       in
       if s0
       then let s1 =
              (fun a b -> if a >= b then if a = b then true else true else false)
                rx ls
            in
            if s1
            then (fun a b -> if a >= b then if a = b then true else true else false)
                   ry ls
            else false
       else false
  else false

(** val all_drifts_ok_dec : ns_category -> storey_data list -> bool **)

let rec all_drifts_ok_dec cat = function
| [] -> true
| y :: l ->
  let s = drift_ok_dec cat y.sd_dr y.sd_h in
  if s then all_drifts_ok_dec cat l else false

(** val all_pdelta_ok_dec : storey_data list -> bool **)

let rec all_pdelta_ok_dec = function
| [] -> true
| y :: l0 ->
  let s =
    (fun a b -> if a <= b then true else false) y.sd_theta
      ((fun a b -> a /. b) (iZR (Zpos (XI XH)))
        (iZR (Zpos (XO (XI (XO XH))))))
  in
  if s then all_pdelta_ok_dec l0 else false

(** val mass_ratio_ok_dec : float -> float -> bool **)

let mass_ratio_ok_dec m1 m2 =
  let s =
    (fun a b -> if a <= b then true else false) m2
      (( *. ) ((fun a b -> a /. b) (iZR (Zpos (XI XH))) (iZR (Zpos (XO XH))))
        m1)
  in
  if s
  then (fun a b -> if a <= b then true else false) m1
         (( *. )
           ((fun a b -> a /. b) (iZR (Zpos (XI XH))) (iZR (Zpos (XO XH)))) m2)
  else false

(** val stiffness_continuity_dec : float -> float -> bool **)

let stiffness_continuity_dec k1 k2 =
  (fun a b -> if a >= b then if a = b then true else true else false) k1
    (( *. )
      ((fun a b -> a /. b) (iZR (Zpos (XI (XI XH))))
        (iZR (Zpos (XO (XI (XO XH)))))) k2)

(** val all_adjacent_dec : ('a1 -> 'a1 -> bool) -> 'a1 list -> bool **)

let rec all_adjacent_dec p_dec = function
| [] -> true
| y :: l0 ->
  (match l0 with
   | [] -> true
   | a :: _ ->
     let s = p_dec y a in if s then all_adjacent_dec p_dec l0 else false)

(** val elevation_regular_dec : float list -> float list -> bool **)

let elevation_regular_dec masses stiffnesses =
  let s = all_adjacent_dec mass_ratio_ok_dec masses in
  if s then all_adjacent_dec stiffness_continuity_dec stiffnesses else false

(** val ec8_compliant_dec :
    building -> seismic_params -> storey_data list -> bool **)

let ec8_compliant_dec b sp sds =
  let s = plan_regular_dec b.bld_e0x b.bld_e0y b.bld_rx b.bld_ry b.bld_ls in
  if s
  then let s0 = elevation_regular_dec b.bld_masses b.bld_stiffnesses in
       if s0
       then let s1 =
              (fun a b -> if a <= b then true else false) b.bld_T1
                (( *. ) (iZR (Zpos (XO (XO XH)))) sp.spar_sp.sp_TC)
            in
            if s1
            then let s2 = all_drifts_ok_dec sp.spar_ns_cat sds in
                 if s2 then all_pdelta_ok_dec sds else false
            else false
       else false
  else false
