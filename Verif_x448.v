(* Verification of the C Implementation of Curve448. *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import x448.
Require Import stdpp.list.
Require Import ZArith.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(* The gf structure defined. *)
Definition t_gf := Tstruct __257 noattr.

(* A function to split an integer into its representation*)
Local Open Scope Z. 
Definition split_to_list (N : Z) : list Z :=
    [    N mod 2^32;
        (N/(2^32)) mod 2^32;
        (N/(2^(32*2))) mod 2^32;
        (N/(2^(32*3))) mod 2^32;
        (N/(2^(32*4))) mod 2^32;
        (N/(2^(32*5))) mod 2^32;
        (N/(2^(32*6))) mod 2^32;
        (N/(2^(32*7))) mod 2^32;
        (N/(2^(32*8))) mod 2^32;
        (N/(2^(32*9))) mod 2^32;
        (N/(2^(32*10))) mod 2^32;
        (N/(2^(32*11))) mod 2^32;
        (N/(2^(32*12))) mod 2^32;
        (N/(2^(32*13))) mod 2^32;
        (N/(2^(32*14))) mod 2^32;
        (N/(2^(32*15))) mod 2^32
    ].

(* Some listrep functions to represent our lists. *)
Definition listrepVal (s : share) (x : val) (contents : list val) : mpred :=
    EX x0 : list val, EX limb : val,
    data_at s t_gf x0 x  *  
        data_at Tsh (tarray tuint 16) contents limb.

Arguments listrepVal s x contents : simpl never.

(* Lemma listrepVal_local_prop: forall s x contents, listrepVal s x contents |--
        !! (is_pointer_or_null x  /\ (x=nullval <-> contents=nil)). *)

Definition listrepZ (s : share) (x : val) (contents : list Z) : mpred :=
    EX x0 : list val, EX limb : val,
    data_at s (t_gf (*the gf contains limb*)) x0 x  *  
        data_at Tsh (tarray tuint 16) ((map Vint (map Int.repr contents))) limb.

Arguments listrepZ s x contents : simpl never.

(* Function Specifications *)

(* SECTION : gf_cpy *)
Definition gf_cpy_spec : ident * funspec := 
DECLARE _gf_cpy
WITH
        x: val,                 (* nombre (pointer) del arreglo gf *)
        shx : share,
        (* x0 : list val,          contenidos de la lista x de tipo __257 *)
        (* limbx : val,             nombre del arreglo LIMB *)
        (* shlx : share, *)
        contents_x : list val,   (* contenido de LIMB *)
        y: val,
        shy : share,
        (* y0 : list val, *)
        (* limby: val, *)
        (* shly: share,  *)
        contents_y : list Z,
        gv : globals
    PRE [ tptr t_gf, tptr t_gf ]
        PROP   (writable_share shx;
                readable_share shy;
                Zlength contents_x = 16;
                Zlength contents_y = 16)
        PARAMS (x ; y) GLOBALS (gv)
        SEP    (field_at shx t_gf contents_x; listrepZ shy y contents_y)
    POST [ tvoid ]
        PROP   ()
        RETURN ()
        SEP    (listrepZ shx x contents_y; listrepZ shy y contents_y).

(* Define the invariant for the loop. *)
Definition gf_cpy_INV shx shy x y contents_x contents_y := 
    EX i : Z,
        PROP  (writable_share shx;
               readable_share shy;
               Zlength contents_x = 16;
               Zlength contents_y = 16;
               i >= 0)
        LOCAL (temp _x x; temp _y y)
        SEP   (listrepVal shx x ((list.take (Z.to_nat i) (map Vint (map Int.repr contents_y)))
                ++ list.drop (Z.to_nat i) contents_x);
               listrepZ shy y contents_y).

Definition Gprog : funspecs := [ gf_cpy_spec ].

Lemma body_gf_cpy : semax_body Vprog Gprog f_gf_cpy gf_cpy_spec.
Proof.
    start_function.
    forward.
    forward_for_simple_bound 16 (gf_cpy_INV shx shy x y contents_x contents_y).
    entailer!.
    unfold listrepVal.
    Intros x0 limbx.
    Exists x0 limbx.
    entailer!.
    Intros.
    unfold listrepVal.
    unfold listrepZ.

    Intros x0 limbx.
    Intros y0 limby.
    forward.
    Check tc_val.

    entailer.
    

    autorewrite with sublist in *|-.

    simplify_value_fits in H9.
    simplify_value_fits in H9.
    destruct H9.

    entailer!.
    Search is_int I32 _ .
    remember (Znth i y0) as M.
    try apply is_int_I32_Vint.
    Check M.
    lia.
    autorewrite with sublist in *|-.
 
    simplify_value_fits in H15.
    simplify_value_fits in H15.
    destruct H15.
    induction i; simpl; try auto.

    
    
    unfold nth; try auto; simpl.   

    Check value_fits. 

(* gf_mul *)
(* gf_isqrt *)
(* gf_inv *)
(* gf_reduce *)
(* gf_add *)
(* gf_sub *)
(* cond_swap *)
(* gf_mlw *)
(* gf_canon *)
(* gf_deser *)
(* gf_ser *)

(* x448 *)
(* x448_base *)

(** Putting all the funspecs together: *)

    (* Definition Gprog : funspecs :=
            ltac:(with_library prog [
                    (newstack_spec; push_spec; pop_spec)
    ]). *)

(* Proofs of Function Bodies *)

(* gf_cpy *)
(* gf_mul *)
(* gf_isqrt *)
(* gf_inv *)
(* gf_reduce *)
(* gf_add *)
(* gf_sub *)
(* cond_swap *)
(* gf_mlw *)
(* gf_canon *)
(* gf_deser *)
(* gf_ser *)

(* x448 *)
(* x448_base *)
