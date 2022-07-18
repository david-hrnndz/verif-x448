Require Import VST.floyd.proofauto.
Require Import x448.
Require Import stdpp.list.
Require Import ZArith.
Require Import compcert.lib.Coqlib.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition t_gf := Tstruct __257 noattr.

Local Open Scope Z.

Definition gf_mul_spec : ident * funspec :=
    DECLARE _gf_mul
    WITH 
        c: val, shc : share, contents_c : list val,
        a: val, sha : share, contents_a : list Z,
        b: val, shb : share, contents_b : list Z,
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
                field_at sha t_gf (DOT _limb) (map Vint (map Int.repr contents_a)) a;
                field_at shb t_gf (DOT _limb) (map Vint (map Int.repr contents_b)) b)
    POST [ tvoid ]
        PROP   ()
        RETURN ()
        SEP    (field_at shc t_gf (DOT _limb) (map Vint 
                (map Int.repr (int_to_list ((list_to_int contents_a) * (list_to_int contents_b))))) c;
                field_at sha t_gf (DOT _limb) (map Vint (map Int.repr contents_a)) a;
                field_at shb t_gf (DOT _limb) (map Vint (map Int.repr contents_b)) b).

Definition Gprog : funspecs := ltac:(with_library prog [ gf_mul_spec; gf_cpy_spec ]).

Lemma body_gf_cpy : semax_body Vprog Gprog2 f_gf_mul gf_mul_spec.
Proof.
    start_function.
Admitted.