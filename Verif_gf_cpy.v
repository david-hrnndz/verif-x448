Require Import VST.floyd.proofauto.
Require Import VST.floyd.list_solver.
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


(* Compute list.take 2 [1;2;3;4;5] = sublist.sublist 0 0 [1;2;3;4;5].
Compute list.drop 2 [1;2;3;4;5] = sublist.sublist 2 (Zlength [1;2;3;4;5]) [1;2;3;4;5]. *)

Definition gf_cpy_Inv shx shy x y contents_x contents_y := 
    (EX i : Z,
        (PROP   (writable_share shx;
                readable_share shy;
                Zlength contents_x = 16;
                Zlength contents_y = 16;
                i >= 0)
        LOCAL   (temp _x x; temp _y y)
        SEP     (field_at shx t_gf (DOT _limb) (
                    (sublist.sublist 0 i (map Vint (map Int.repr contents_y))) 
                    ++ (sublist.sublist i (Zlength contents_x) contents_x)) x;
                field_at shy t_gf (DOT _limb) (map Vint (map Int.repr contents_y)) y)))%assert.


Definition Gprog : funspecs := ltac:(with_library prog [ gf_cpy_spec ]).


(* Lemma L1 (i : Z) (l : list val) :
0 <= i < Zlength l ->
upd_Znth i (take (Z.to_nat i) l) (Znth i l) =  take (Z.to_nat (i + 1)) l.
Proof. Admitted.

Lemma L2 (i : Z) (l1 l2 : list val) :
0 <= i < Zlength l1 ->
0 <= i < Zlength l2 ->
upd_Znth i (take (Z.to_nat i) l1 ++ drop (Z.to_nat i) l2) (Znth i l1) 
    =  take (Z.to_nat (i + 1)) l1 ++
       drop (Z.to_nat (i + 1)) l2.
Proof.
    intros.
    rewrite upd_Znth_unfold.
    simpl.
    assert (sublist.sublist 0 i (take (Z.to_nat i) l1 ++ drop (Z.to_nat i) l2) = take (Z.to_nat i) l1).
    admit.
    rewrite H1.
    replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
    apply take_S_r. *)

Lemma L1 (i : Z) (l1 l2 : list val) : 
0 <= i < Zlength l1 ->
sublist.sublist 0 i (sublist.sublist 0 i l1 ++ l2) = sublist.sublist 0 i l1.
Proof. 
    intros;
    list_solve.
    Qed.

Lemma L1' (i : Z) (l1 l2 : list val) : 
0 <= i < Zlength l1 ->
Zlength l1 = Zlength l2 ->
sublist.sublist (i + 1) (Zlength l2) (sublist.sublist 0 i l1 ++
    sublist.sublist i (Zlength l2) l2) = sublist.sublist (i + 1) (Zlength l2) l2.
Proof.
    intros;
    list_solve.
    Qed.  

Lemma L2 (i : Z) (l : list Z) : 
0 <= i < Zlength l ->
(sublist.sublist 0 i (map Vint (map Int.repr l))) ++
[Vint (Int.repr (Znth i l))] = sublist.sublist 0 (i+1) (map Vint (map Int.repr l)).
Proof. 
    intros;
    list_solve.
    Qed.

Lemma L3 (i : Z) (l1 l2 : list val) :
0 <= i < Zlength l1 ->
Zlength l1 = Zlength l2 ->
Zlength (sublist.sublist 0 i l1 ++ sublist.sublist i (Zlength l2) l2) = Zlength l2.
Proof. 
    intros.
    rewrite Zlength_app.
    list_simplify.
    Qed.

Lemma body_gf_cpy : semax_body Vprog Gprog f_gf_cpy gf_cpy_spec.
Proof.
    start_function.
    forward.
    forward_for_simple_bound 16 (gf_cpy_Inv shx shy x y contents_x contents_y).
    -   entailer!.
    assert (sublist.sublist 0 0 (map Vint (map Int.repr contents_y)) = [])by list_solve.
    rewrite H5; simpl.      
    assert ((sublist.sublist 0 (Zlength contents_x) contents_x) = contents_x) by list_solve.
    rewrite H6.    
    cancel.
    - try repeat forward.
        entailer!.
        rewrite upd_Znth_unfold.
        rewrite L1.
        rewrite app_assoc.
        rewrite L2.
        rewrite L3.
        rewrite L1'.
        cancel.
        try repeat rewrite Zlength_map.
        by rewrite H0.
        try repeat rewrite Zlength_map.
        by rewrite H0.
        try repeat rewrite Zlength_map; by rewrite H0.
        try repeat rewrite Zlength_map; by rewrite H0.
        by rewrite H0.
        try repeat rewrite Zlength_map; by rewrite H0.
        

        About sublist.sublist.

        list_simplify.

    - entailer!.
        rewrite <- H0.
        assert (Zlength contents_y = Zlength (map Vint (map Int.repr contents_y))) by list_simplify.
        rewrite H6 at 1.
        assert (sublist.sublist 0 (Zlength (map Vint (map Int.repr contents_y)))
        (map Vint (map Int.repr contents_y)) = (map Vint (map Int.repr contents_y))) by list_solve.
        rewrite H7.
        rewrite H, H0.
        assert (sublist.sublist 16 16 contents_x = []) by list_solve.
        rewrite H8.
        rewrite app_nil_r.
        cancel.
        Qed.





