Require Import VST.floyd.proofauto.
Require Import x448.
Require Import stdpp.list.
Require Import ZArith.
Require Import compcert.lib.Coqlib.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition t_gf := Tstruct __257 noattr.

(** We will define a separation-logic predicate, [listrep N p],
 to describe the concept that the address [p] in memory is a
 list that represents the number N \in GF(prime) in 16 limbs. *)

Local Open Scope Z.

(* Function to split a [large] integer into a list representation *
 * of size number of limbs (16 in this case).                     *)
Definition int_to_list (N : Z) : list Z := 
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

About data_at.

Fixpoint list_to_int' (l  : list Z) (n : Z) : Z := 
    match l with 
    | nil => 0
    | h :: t => (h * (Z.pow 2 (32 * (n)))) + (list_to_int' t (n+1))
    end. 

Definition list_to_int (l : list Z) := list_to_int' l 0.

(* Definition gf_cpy_spec : ident * funspec :=
    DECLARE _gf_cpy
    WITH 
        x: val,
        shx : share,
        contents_x : list val,
        y: val,
        shy : share,
        contents_y : list int,
        gv : globals
    PRE [ tptr t_gf, tptr t_gf ]
        PROP   (writable_share shx;
                readable_share shy;
                Zlength contents_x = 16;
                Zlength contents_y = 16)
        PARAMS (x ; y) GLOBALS (gv)
        SEP    (field_at shx t_gf (DOT _limb) contents_x x;
                field_at shy t_gf (DOT _limb) (map Vint contents_y) y)
    POST [ tvoid ]
        PROP   ()
        RETURN ()
        SEP    (field_at shx t_gf (DOT _limb) (map Vint contents_y) x;
                field_at shy t_gf (DOT _limb) (map Vint contents_y) y). *)


Definition gf_cpy_spec : ident * funspec :=
    DECLARE _gf_cpy
    WITH 
        x: val,
        shx : share,
        contents_x : list val,
        y: val,
        shy : share,
        contents_y : list Z,
        gv : globals
    PRE [ tptr t_gf, tptr t_gf ]
        PROP   (writable_share shx;
                readable_share shy;
                Zlength contents_x = 16;
                Zlength contents_y = 16)
        PARAMS (x ; y) GLOBALS (gv)
        SEP    (field_at shx t_gf (DOT _limb) contents_x x;
                field_at shy t_gf (DOT _limb) (map Vint (map Int.repr contents_y)) y)
    POST [ tvoid ]
        PROP   ()
        RETURN ()
        SEP    (field_at shx t_gf (DOT _limb) (map Vint (map Int.repr contents_y)) x;
                field_at shy t_gf (DOT _limb) (map Vint (map Int.repr contents_y)) y).




Definition gf_cpy_Inv shx shy x y contents_x contents_y := 
    (EX i : Z,
        (PROP   (writable_share shx;
                readable_share shy;
                Zlength contents_x = 16;
                Zlength contents_y = 16;
                i >= 0)
        LOCAL   (temp _x x; temp _y y)
        SEP     (field_at shx t_gf (DOT _limb) (
                    (list.take (Z.to_nat i) (map Vint (map Int.repr contents_y))) 
                    ++ (list.drop (Z.to_nat i) contents_x)) x;
                field_at shy t_gf (DOT _limb) (map Vint (map Int.repr contents_y)) y)))%assert.


Definition Gprog : funspecs := ltac:(with_library prog [ gf_cpy_spec ]).

Lemma body_gf_cpy : semax_body Vprog Gprog f_gf_cpy gf_cpy_spec.
Proof.
    start_function.
    forward.
    forward_for_simple_bound 16 (gf_cpy_Inv shx shy x y contents_x contents_y).
    - entailer!.
    - try repeat forward.
        entailer!.
        replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)).
Admitted.
(* Qed. *)





