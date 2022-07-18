Require Import VST.floyd.proofauto.
Require Import x448.
Require Import stdpp.list.
Require Import ZArith.
Require Import Coq.Program.Equality.
Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition t_gf := Tstruct __257 noattr.

(* Un comentario *)

(** We will define a separation-logic predicate, [listrep N p],
 to describe the concept that the address [p] in memory is a
 list that represents the number N \in GF(prime) in 16 limbs. *)

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

Compute split_to_list 20461022933861958966015542640853531714416036282372.

Definition gf_cpy_spec : ident * funspec :=
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
                field_at shy t_gf (DOT _limb) (map Vint contents_y) y).



Definition gf_cpy_Inv shx shy x y contents_x contents_y := 
    (EX i : Z,
        (PROP   (writable_share shx;
                readable_share shy;
                Zlength contents_x = 16;
                Zlength contents_y = 16;
                i >= 0)
        LOCAL   (temp _x x; temp _y y)
        SEP     (field_at shx t_gf (DOT _limb) ((list.take (Z.to_nat i) (map Vint contents_y)) 
                    ++ (list.drop (Z.to_nat i) contents_x)) x;
                field_at shy t_gf (DOT _limb) (map Vint contents_y) y)))%assert.


Definition Gprog : funspecs := [ gf_cpy_spec ].

Lemma body_gf_cpy : semax_body Vprog Gprog f_gf_cpy gf_cpy_spec.
Proof.
    start_function.
    forward.
    forward_for_simple_bound 16 (gf_cpy_Inv shx shy x y contents_x contents_y).
    - entailer!.
    - try repeat forward.
        entailer!.
        replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)).
        Check upd_Znth_app_step_Zlength.
        assert
        hint.
Qed.



Definition gf_cpy_spec : ident * funspec :=
    DECLARE _gf_mul
    WITH 
        c: val, shc : share, contents_c : list val,
        a: val, sha : share, contents_a : list int,
        b: val, shb : share, contents_b : list int,
        gv : globals
    PRE [ tptr t_gf, tptr t_gf, tptr t_gf ]
        PROP   (writable_share shc;
                readable_share sha;
                readable_share shb;
                Zlength contents_a = 16;
                Zlength contents_b = 16;
                Zlength contents_c = 16)
        PARAMS (c ; a ; b) GLOBALS (gv)
        SEP    (field_at shc t_gf (DOT _limb) contents_c c;
                field_at sha t_gf (DOT _limb) (map Vint contents_a) a;
                field_at shb t_gf (DOT _limb) (map Vint contents_b) b)
    POST [ tvoid ]
        PROP   ()
        RETURN ()
        SEP    (field_at shx t_gf (DOT _limb) (map Vint contents_y) x;
                field_at shy t_gf (DOT _limb) (map Vint contents_y) y).
