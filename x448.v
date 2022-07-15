From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.9".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "macos".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "x448.c".
  Definition normalized := true.
End Info.

Definition _EDWARDS_D : ident := $"EDWARDS_D".
Definition _ONE : ident := $"ONE".
Definition _P : ident := $"P".
Definition _X448_BASE_POINT : ident := $"X448_BASE_POINT".
Definition _ZERO : ident := $"ZERO".
Definition __257 : ident := $"_257".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_read16_reversed : ident := $"__builtin_read16_reversed".
Definition ___builtin_read32_reversed : ident := $"__builtin_read32_reversed".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___builtin_write16_reversed : ident := $"__builtin_write16_reversed".
Definition ___builtin_write32_reversed : ident := $"__builtin_write32_reversed".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition _a : ident := $"a".
Definition _aa : ident := $"aa".
Definition _accum : ident := $"accum".
Definition _addback : ident := $"addback".
Definition _b : ident := $"b".
Definition _base : ident := $"base".
Definition _bits : ident := $"bits".
Definition _buf : ident := $"buf".
Definition _c : ident := $"c".
Definition _carry : ident := $"carry".
Definition _cond_swap : ident := $"cond_swap".
Definition _gf_add : ident := $"gf_add".
Definition _gf_canon : ident := $"gf_canon".
Definition _gf_cpy : ident := $"gf_cpy".
Definition _gf_deser : ident := $"gf_deser".
Definition _gf_inv : ident := $"gf_inv".
Definition _gf_isqrt : ident := $"gf_isqrt".
Definition _gf_mlw : ident := $"gf_mlw".
Definition _gf_mul : ident := $"gf_mul".
Definition _gf_reduce : ident := $"gf_reduce".
Definition _gf_ser : ident := $"gf_ser".
Definition _gf_sub : ident := $"gf_sub".
Definition _i : ident := $"i".
Definition _i__1 : ident := $"i__1".
Definition _j : ident := $"j".
Definition _j__1 : ident := $"j__1".
Definition _j__2 : ident := $"j__2".
Definition _k : ident := $"k".
Definition _k_t : ident := $"k_t".
Definition _limb : ident := $"limb".
Definition _main : ident := $"main".
Definition _nz : ident := $"nz".
Definition _out : ident := $"out".
Definition _s : ident := $"s".
Definition _sb : ident := $"sb".
Definition _scalar : ident := $"scalar".
Definition _ser : ident := $"ser".
Definition _swap : ident := $"swap".
Definition _t : ident := $"t".
Definition _t1 : ident := $"t1".
Definition _t2 : ident := $"t2".
Definition _w : ident := $"w".
Definition _ww : ident := $"ww".
Definition _ww__1 : ident := $"ww__1".
Definition _x : ident := $"x".
Definition _x1 : ident := $"x1".
Definition _x2 : ident := $"x2".
Definition _x3 : ident := $"x3".
Definition _x448 : ident := $"x448".
Definition _x448_base : ident := $"x448_base".
Definition _y : ident := $"y".
Definition _z : ident := $"z".
Definition _z2 : ident := $"z2".
Definition _z3 : ident := $"z3".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'14 : ident := 141%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition v_X448_BASE_POINT := {|
  gvar_info := (tarray tuchar 56);
  gvar_init := (Init_int8 (Int.repr 5) :: Init_space 55 :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_ZERO := {|
  gvar_info := (tarray (Tstruct __257 noattr) 1);
  gvar_init := (Init_int32 (Int.repr 0) :: Init_space 60 :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_ONE := {|
  gvar_info := (tarray (Tstruct __257 noattr) 1);
  gvar_init := (Init_int32 (Int.repr 1) :: Init_space 60 :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_P := {|
  gvar_info := (tarray (Tstruct __257 noattr) 1);
  gvar_init := (Init_int32 (Int.repr 268435455) ::
                Init_int32 (Int.repr 268435455) ::
                Init_int32 (Int.repr 268435455) ::
                Init_int32 (Int.repr 268435455) ::
                Init_int32 (Int.repr 268435455) ::
                Init_int32 (Int.repr 268435455) ::
                Init_int32 (Int.repr 268435455) ::
                Init_int32 (Int.repr 268435455) ::
                Init_int32 (Int.repr 268435454) ::
                Init_int32 (Int.repr 268435455) ::
                Init_int32 (Int.repr 268435455) ::
                Init_int32 (Int.repr 268435455) ::
                Init_int32 (Int.repr 268435455) ::
                Init_int32 (Int.repr 268435455) ::
                Init_int32 (Int.repr 268435455) ::
                Init_int32 (Int.repr 268435455) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_EDWARDS_D := {|
  gvar_info := tint;
  gvar_init := (Init_int32 (Int.repr (-39081)) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_gf_cpy := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr (Tstruct __257 noattr))) ::
                (_y, (tptr (Tstruct __257 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                       (Ebinop Odiv (Econst_int (Int.repr 448) tint)
                         (Ebinop Odiv
                           (Ebinop Omul (Econst_int (Int.repr 32) tint)
                             (Econst_int (Int.repr 7) tint) tint)
                           (Econst_int (Int.repr 8) tint) tint) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _t'1
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar _y (tptr (Tstruct __257 noattr)))
                    (Tstruct __257 noattr)) _limb (tarray tuint 16))
                (Etempvar _i tuint) (tptr tuint)) tuint))
          (Sassign
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar _x (tptr (Tstruct __257 noattr)))
                    (Tstruct __257 noattr)) _limb (tarray tuint 16))
                (Etempvar _i tuint) (tptr tuint)) tuint)
            (Etempvar _t'1 tuint))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
          tuint)))))
|}.

Definition f_gf_mul := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_c, (tptr (Tstruct __257 noattr))) ::
                (_a, (tptr (Tstruct __257 noattr))) ::
                (_b, (tptr (Tstruct __257 noattr))) :: nil);
  fn_vars := ((_aa, (tarray (Tstruct __257 noattr) 1)) ::
              (_accum, (tarray tulong 16)) :: nil);
  fn_temps := ((_i, tuint) :: (_j, tuint) :: (_j__1, tuint) ::
               (_j__2, tuint) :: (_t'14, tuint) :: (_t'13, tuint) ::
               (_t'12, tulong) :: (_t'11, tuint) :: (_t'10, tuint) ::
               (_t'9, tulong) :: (_t'8, tulong) :: (_t'7, tulong) ::
               (_t'6, tulong) :: (_t'5, tulong) :: (_t'4, tulong) ::
               (_t'3, tulong) :: (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _gf_cpy (Tfunction
                    (Tcons (tptr (Tstruct __257 noattr))
                      (Tcons (tptr (Tstruct __257 noattr)) Tnil)) tvoid
                    cc_default))
    ((Evar _aa (tarray (Tstruct __257 noattr) 1)) ::
     (Etempvar _a (tptr (Tstruct __257 noattr))) :: nil))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd (Evar _accum (tarray tulong 16))
          (Econst_int (Int.repr 0) tint) (tptr tulong)) tulong)
      (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Evar _accum (tarray tulong 16))
            (Econst_int (Int.repr 1) tint) (tptr tulong)) tulong)
        (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd (Evar _accum (tarray tulong 16))
              (Econst_int (Int.repr 2) tint) (tptr tulong)) tulong)
          (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd (Evar _accum (tarray tulong 16))
                (Econst_int (Int.repr 3) tint) (tptr tulong)) tulong)
            (Econst_int (Int.repr 0) tint))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Evar _accum (tarray tulong 16))
                  (Econst_int (Int.repr 4) tint) (tptr tulong)) tulong)
              (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Sassign
                (Ederef
                  (Ebinop Oadd (Evar _accum (tarray tulong 16))
                    (Econst_int (Int.repr 5) tint) (tptr tulong)) tulong)
                (Econst_int (Int.repr 0) tint))
              (Ssequence
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Evar _accum (tarray tulong 16))
                      (Econst_int (Int.repr 6) tint) (tptr tulong)) tulong)
                  (Econst_int (Int.repr 0) tint))
                (Ssequence
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Evar _accum (tarray tulong 16))
                        (Econst_int (Int.repr 7) tint) (tptr tulong)) tulong)
                    (Econst_int (Int.repr 0) tint))
                  (Ssequence
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Evar _accum (tarray tulong 16))
                          (Econst_int (Int.repr 8) tint) (tptr tulong))
                        tulong) (Econst_int (Int.repr 0) tint))
                    (Ssequence
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Evar _accum (tarray tulong 16))
                            (Econst_int (Int.repr 9) tint) (tptr tulong))
                          tulong) (Econst_int (Int.repr 0) tint))
                      (Ssequence
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Evar _accum (tarray tulong 16))
                              (Econst_int (Int.repr 10) tint) (tptr tulong))
                            tulong) (Econst_int (Int.repr 0) tint))
                        (Ssequence
                          (Sassign
                            (Ederef
                              (Ebinop Oadd (Evar _accum (tarray tulong 16))
                                (Econst_int (Int.repr 11) tint)
                                (tptr tulong)) tulong)
                            (Econst_int (Int.repr 0) tint))
                          (Ssequence
                            (Sassign
                              (Ederef
                                (Ebinop Oadd (Evar _accum (tarray tulong 16))
                                  (Econst_int (Int.repr 12) tint)
                                  (tptr tulong)) tulong)
                              (Econst_int (Int.repr 0) tint))
                            (Ssequence
                              (Sassign
                                (Ederef
                                  (Ebinop Oadd
                                    (Evar _accum (tarray tulong 16))
                                    (Econst_int (Int.repr 13) tint)
                                    (tptr tulong)) tulong)
                                (Econst_int (Int.repr 0) tint))
                              (Ssequence
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd
                                      (Evar _accum (tarray tulong 16))
                                      (Econst_int (Int.repr 14) tint)
                                      (tptr tulong)) tulong)
                                  (Econst_int (Int.repr 0) tint))
                                (Ssequence
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Evar _accum (tarray tulong 16))
                                        (Econst_int (Int.repr 15) tint)
                                        (tptr tulong)) tulong)
                                    (Econst_int (Int.repr 0) tint))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _i
                                        (Econst_int (Int.repr 0) tint))
                                      (Ssequence
                                        (Sset _i
                                          (Econst_int (Int.repr 0) tint))
                                        (Sloop
                                          (Ssequence
                                            (Sifthenelse (Ebinop Olt
                                                           (Etempvar _i tuint)
                                                           (Ebinop Odiv
                                                             (Econst_int (Int.repr 448) tint)
                                                             (Ebinop Odiv
                                                               (Ebinop Omul
                                                                 (Econst_int (Int.repr 32) tint)
                                                                 (Econst_int (Int.repr 7) tint)
                                                                 tint)
                                                               (Econst_int (Int.repr 8) tint)
                                                               tint) tint)
                                                           tint)
                                              Sskip
                                              Sbreak)
                                            (Ssequence
                                              (Ssequence
                                                (Sset _j
                                                  (Econst_int (Int.repr 0) tint))
                                                (Ssequence
                                                  (Sset _j
                                                    (Econst_int (Int.repr 0) tint))
                                                  (Sloop
                                                    (Ssequence
                                                      (Sifthenelse (Ebinop Olt
                                                                    (Etempvar _j tuint)
                                                                    (Ebinop Odiv
                                                                    (Econst_int (Int.repr 448) tint)
                                                                    (Ebinop Odiv
                                                                    (Ebinop Omul
                                                                    (Econst_int (Int.repr 32) tint)
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    tint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tint)
                                                                    tint)
                                                                    tint)
                                                        Sskip
                                                        Sbreak)
                                                      (Ssequence
                                                        (Sset _t'12
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _accum (tarray tulong 16))
                                                              (Ebinop Omod
                                                                (Ebinop Oadd
                                                                  (Etempvar _i tuint)
                                                                  (Etempvar _j tuint)
                                                                  tuint)
                                                                (Ebinop Odiv
                                                                  (Econst_int (Int.repr 448) tint)
                                                                  (Ebinop Odiv
                                                                    (Ebinop Omul
                                                                    (Econst_int (Int.repr 32) tint)
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    tint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tint)
                                                                  tint)
                                                                tuint)
                                                              (tptr tulong))
                                                            tulong))
                                                        (Ssequence
                                                          (Sset _t'13
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _b (tptr (Tstruct __257 noattr)))
                                                                    (Tstruct __257 noattr))
                                                                  _limb
                                                                  (tarray tuint 16))
                                                                (Etempvar _i tuint)
                                                                (tptr tuint))
                                                              tuint))
                                                          (Ssequence
                                                            (Sset _t'14
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Efield
                                                                    (Ederef
                                                                    (Evar _aa (tarray (Tstruct __257 noattr) 1))
                                                                    (Tstruct __257 noattr))
                                                                    _limb
                                                                    (tarray tuint 16))
                                                                  (Etempvar _j tuint)
                                                                  (tptr tuint))
                                                                tuint))
                                                            (Sassign
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _accum (tarray tulong 16))
                                                                  (Ebinop Omod
                                                                    (Ebinop Oadd
                                                                    (Etempvar _i tuint)
                                                                    (Etempvar _j tuint)
                                                                    tuint)
                                                                    (Ebinop Odiv
                                                                    (Econst_int (Int.repr 448) tint)
                                                                    (Ebinop Odiv
                                                                    (Ebinop Omul
                                                                    (Econst_int (Int.repr 32) tint)
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    tint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tint)
                                                                    tint)
                                                                    tuint)
                                                                  (tptr tulong))
                                                                tulong)
                                                              (Ebinop Oadd
                                                                (Etempvar _t'12 tulong)
                                                                (Ebinop Omul
                                                                  (Ecast
                                                                    (Etempvar _t'13 tuint)
                                                                    tulong)
                                                                  (Etempvar _t'14 tuint)
                                                                  tulong)
                                                                tulong))))))
                                                    (Sset _j
                                                      (Ebinop Oadd
                                                        (Etempvar _j tuint)
                                                        (Econst_int (Int.repr 1) tint)
                                                        tuint)))))
                                              (Ssequence
                                                (Sset _t'10
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Efield
                                                        (Ederef
                                                          (Evar _aa (tarray (Tstruct __257 noattr) 1))
                                                          (Tstruct __257 noattr))
                                                        _limb
                                                        (tarray tuint 16))
                                                      (Ebinop Oxor
                                                        (Ebinop Osub
                                                          (Ebinop Osub
                                                            (Ebinop Odiv
                                                              (Econst_int (Int.repr 448) tint)
                                                              (Ebinop Odiv
                                                                (Ebinop Omul
                                                                  (Econst_int (Int.repr 32) tint)
                                                                  (Econst_int (Int.repr 7) tint)
                                                                  tint)
                                                                (Econst_int (Int.repr 8) tint)
                                                                tint) tint)
                                                            (Econst_int (Int.repr 1) tint)
                                                            tint)
                                                          (Etempvar _i tuint)
                                                          tuint)
                                                        (Ebinop Odiv
                                                          (Ebinop Odiv
                                                            (Econst_int (Int.repr 448) tint)
                                                            (Ebinop Odiv
                                                              (Ebinop Omul
                                                                (Econst_int (Int.repr 32) tint)
                                                                (Econst_int (Int.repr 7) tint)
                                                                tint)
                                                              (Econst_int (Int.repr 8) tint)
                                                              tint) tint)
                                                          (Econst_int (Int.repr 2) tint)
                                                          tint) tuint)
                                                      (tptr tuint)) tuint))
                                                (Ssequence
                                                  (Sset _t'11
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Efield
                                                          (Ederef
                                                            (Evar _aa (tarray (Tstruct __257 noattr) 1))
                                                            (Tstruct __257 noattr))
                                                          _limb
                                                          (tarray tuint 16))
                                                        (Ebinop Osub
                                                          (Ebinop Osub
                                                            (Ebinop Odiv
                                                              (Econst_int (Int.repr 448) tint)
                                                              (Ebinop Odiv
                                                                (Ebinop Omul
                                                                  (Econst_int (Int.repr 32) tint)
                                                                  (Econst_int (Int.repr 7) tint)
                                                                  tint)
                                                                (Econst_int (Int.repr 8) tint)
                                                                tint) tint)
                                                            (Econst_int (Int.repr 1) tint)
                                                            tint)
                                                          (Etempvar _i tuint)
                                                          tuint)
                                                        (tptr tuint)) tuint))
                                                  (Sassign
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Efield
                                                          (Ederef
                                                            (Evar _aa (tarray (Tstruct __257 noattr) 1))
                                                            (Tstruct __257 noattr))
                                                          _limb
                                                          (tarray tuint 16))
                                                        (Ebinop Oxor
                                                          (Ebinop Osub
                                                            (Ebinop Osub
                                                              (Ebinop Odiv
                                                                (Econst_int (Int.repr 448) tint)
                                                                (Ebinop Odiv
                                                                  (Ebinop Omul
                                                                    (Econst_int (Int.repr 32) tint)
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    tint)
                                                                  (Econst_int (Int.repr 8) tint)
                                                                  tint) tint)
                                                              (Econst_int (Int.repr 1) tint)
                                                              tint)
                                                            (Etempvar _i tuint)
                                                            tuint)
                                                          (Ebinop Odiv
                                                            (Ebinop Odiv
                                                              (Econst_int (Int.repr 448) tint)
                                                              (Ebinop Odiv
                                                                (Ebinop Omul
                                                                  (Econst_int (Int.repr 32) tint)
                                                                  (Econst_int (Int.repr 7) tint)
                                                                  tint)
                                                                (Econst_int (Int.repr 8) tint)
                                                                tint) tint)
                                                            (Econst_int (Int.repr 2) tint)
                                                            tint) tuint)
                                                        (tptr tuint)) tuint)
                                                    (Ebinop Oadd
                                                      (Etempvar _t'10 tuint)
                                                      (Etempvar _t'11 tuint)
                                                      tuint))))))
                                          (Sset _i
                                            (Ebinop Oadd (Etempvar _i tuint)
                                              (Econst_int (Int.repr 1) tint)
                                              tuint)))))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'8
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _accum (tarray tulong 16))
                                              (Ebinop Osub
                                                (Ebinop Odiv
                                                  (Econst_int (Int.repr 448) tint)
                                                  (Ebinop Odiv
                                                    (Ebinop Omul
                                                      (Econst_int (Int.repr 32) tint)
                                                      (Econst_int (Int.repr 7) tint)
                                                      tint)
                                                    (Econst_int (Int.repr 8) tint)
                                                    tint) tint)
                                                (Econst_int (Int.repr 1) tint)
                                                tint) (tptr tulong)) tulong))
                                        (Ssequence
                                          (Sset _t'9
                                            (Ederef
                                              (Ebinop Oadd
                                                (Evar _accum (tarray tulong 16))
                                                (Ebinop Osub
                                                  (Ebinop Odiv
                                                    (Econst_int (Int.repr 448) tint)
                                                    (Ebinop Odiv
                                                      (Ebinop Omul
                                                        (Econst_int (Int.repr 32) tint)
                                                        (Econst_int (Int.repr 7) tint)
                                                        tint)
                                                      (Econst_int (Int.repr 8) tint)
                                                      tint) tint)
                                                  (Econst_int (Int.repr 2) tint)
                                                  tint) (tptr tulong))
                                              tulong))
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Evar _accum (tarray tulong 16))
                                                (Ebinop Osub
                                                  (Ebinop Odiv
                                                    (Econst_int (Int.repr 448) tint)
                                                    (Ebinop Odiv
                                                      (Ebinop Omul
                                                        (Econst_int (Int.repr 32) tint)
                                                        (Econst_int (Int.repr 7) tint)
                                                        tint)
                                                      (Econst_int (Int.repr 8) tint)
                                                      tint) tint)
                                                  (Econst_int (Int.repr 1) tint)
                                                  tint) (tptr tulong))
                                              tulong)
                                            (Ebinop Oadd
                                              (Etempvar _t'8 tulong)
                                              (Ebinop Oshr
                                                (Etempvar _t'9 tulong)
                                                (Ebinop Odiv
                                                  (Ebinop Omul
                                                    (Econst_int (Int.repr 32) tint)
                                                    (Econst_int (Int.repr 7) tint)
                                                    tint)
                                                  (Econst_int (Int.repr 8) tint)
                                                  tint) tulong) tulong))))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'7
                                            (Ederef
                                              (Ebinop Oadd
                                                (Evar _accum (tarray tulong 16))
                                                (Ebinop Osub
                                                  (Ebinop Odiv
                                                    (Econst_int (Int.repr 448) tint)
                                                    (Ebinop Odiv
                                                      (Ebinop Omul
                                                        (Econst_int (Int.repr 32) tint)
                                                        (Econst_int (Int.repr 7) tint)
                                                        tint)
                                                      (Econst_int (Int.repr 8) tint)
                                                      tint) tint)
                                                  (Econst_int (Int.repr 2) tint)
                                                  tint) (tptr tulong))
                                              tulong))
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Evar _accum (tarray tulong 16))
                                                (Ebinop Osub
                                                  (Ebinop Odiv
                                                    (Econst_int (Int.repr 448) tint)
                                                    (Ebinop Odiv
                                                      (Ebinop Omul
                                                        (Econst_int (Int.repr 32) tint)
                                                        (Econst_int (Int.repr 7) tint)
                                                        tint)
                                                      (Econst_int (Int.repr 8) tint)
                                                      tint) tint)
                                                  (Econst_int (Int.repr 2) tint)
                                                  tint) (tptr tulong))
                                              tulong)
                                            (Ebinop Oand
                                              (Etempvar _t'7 tulong)
                                              (Ebinop Osub
                                                (Ebinop Oshl
                                                  (Ecast
                                                    (Econst_int (Int.repr 1) tint)
                                                    tuint)
                                                  (Ebinop Odiv
                                                    (Ebinop Omul
                                                      (Econst_int (Int.repr 32) tint)
                                                      (Econst_int (Int.repr 7) tint)
                                                      tint)
                                                    (Econst_int (Int.repr 8) tint)
                                                    tint) tuint)
                                                (Econst_int (Int.repr 1) tint)
                                                tuint) tulong)))
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'5
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Evar _accum (tarray tulong 16))
                                                  (Ebinop Odiv
                                                    (Ebinop Odiv
                                                      (Econst_int (Int.repr 448) tint)
                                                      (Ebinop Odiv
                                                        (Ebinop Omul
                                                          (Econst_int (Int.repr 32) tint)
                                                          (Econst_int (Int.repr 7) tint)
                                                          tint)
                                                        (Econst_int (Int.repr 8) tint)
                                                        tint) tint)
                                                    (Econst_int (Int.repr 2) tint)
                                                    tint) (tptr tulong))
                                                tulong))
                                            (Ssequence
                                              (Sset _t'6
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Evar _accum (tarray tulong 16))
                                                    (Ebinop Osub
                                                      (Ebinop Odiv
                                                        (Econst_int (Int.repr 448) tint)
                                                        (Ebinop Odiv
                                                          (Ebinop Omul
                                                            (Econst_int (Int.repr 32) tint)
                                                            (Econst_int (Int.repr 7) tint)
                                                            tint)
                                                          (Econst_int (Int.repr 8) tint)
                                                          tint) tint)
                                                      (Econst_int (Int.repr 1) tint)
                                                      tint) (tptr tulong))
                                                  tulong))
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Evar _accum (tarray tulong 16))
                                                    (Ebinop Odiv
                                                      (Ebinop Odiv
                                                        (Econst_int (Int.repr 448) tint)
                                                        (Ebinop Odiv
                                                          (Ebinop Omul
                                                            (Econst_int (Int.repr 32) tint)
                                                            (Econst_int (Int.repr 7) tint)
                                                            tint)
                                                          (Econst_int (Int.repr 8) tint)
                                                          tint) tint)
                                                      (Econst_int (Int.repr 2) tint)
                                                      tint) (tptr tulong))
                                                  tulong)
                                                (Ebinop Oadd
                                                  (Etempvar _t'5 tulong)
                                                  (Ebinop Oshr
                                                    (Etempvar _t'6 tulong)
                                                    (Ebinop Odiv
                                                      (Ebinop Omul
                                                        (Econst_int (Int.repr 32) tint)
                                                        (Econst_int (Int.repr 7) tint)
                                                        tint)
                                                      (Econst_int (Int.repr 8) tint)
                                                      tint) tulong) tulong))))
                                          (Ssequence
                                            (Ssequence
                                              (Sset _j__1
                                                (Econst_int (Int.repr 0) tint))
                                              (Ssequence
                                                (Sset _j__1
                                                  (Econst_int (Int.repr 0) tint))
                                                (Sloop
                                                  (Ssequence
                                                    (Sifthenelse (Ebinop Olt
                                                                   (Etempvar _j__1 tuint)
                                                                   (Ebinop Odiv
                                                                    (Econst_int (Int.repr 448) tint)
                                                                    (Ebinop Odiv
                                                                    (Ebinop Omul
                                                                    (Econst_int (Int.repr 32) tint)
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    tint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tint)
                                                                    tint)
                                                                   tint)
                                                      Sskip
                                                      Sbreak)
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'3
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _accum (tarray tulong 16))
                                                              (Etempvar _j__1 tuint)
                                                              (tptr tulong))
                                                            tulong))
                                                        (Ssequence
                                                          (Sset _t'4
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _accum (tarray tulong 16))
                                                                (Ebinop Omod
                                                                  (Ebinop Osub
                                                                    (Etempvar _j__1 tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tuint)
                                                                  (Ebinop Odiv
                                                                    (Econst_int (Int.repr 448) tint)
                                                                    (Ebinop Odiv
                                                                    (Ebinop Omul
                                                                    (Econst_int (Int.repr 32) tint)
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    tint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tint)
                                                                    tint)
                                                                  tuint)
                                                                (tptr tulong))
                                                              tulong))
                                                          (Sassign
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _accum (tarray tulong 16))
                                                                (Etempvar _j__1 tuint)
                                                                (tptr tulong))
                                                              tulong)
                                                            (Ebinop Oadd
                                                              (Etempvar _t'3 tulong)
                                                              (Ebinop Oshr
                                                                (Etempvar _t'4 tulong)
                                                                (Ebinop Odiv
                                                                  (Ebinop Omul
                                                                    (Econst_int (Int.repr 32) tint)
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    tint)
                                                                  (Econst_int (Int.repr 8) tint)
                                                                  tint)
                                                                tulong)
                                                              tulong))))
                                                      (Ssequence
                                                        (Sset _t'2
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _accum (tarray tulong 16))
                                                              (Ebinop Omod
                                                                (Ebinop Osub
                                                                  (Etempvar _j__1 tuint)
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  tuint)
                                                                (Ebinop Odiv
                                                                  (Econst_int (Int.repr 448) tint)
                                                                  (Ebinop Odiv
                                                                    (Ebinop Omul
                                                                    (Econst_int (Int.repr 32) tint)
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    tint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tint)
                                                                  tint)
                                                                tuint)
                                                              (tptr tulong))
                                                            tulong))
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _accum (tarray tulong 16))
                                                              (Ebinop Omod
                                                                (Ebinop Osub
                                                                  (Etempvar _j__1 tuint)
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  tuint)
                                                                (Ebinop Odiv
                                                                  (Econst_int (Int.repr 448) tint)
                                                                  (Ebinop Odiv
                                                                    (Ebinop Omul
                                                                    (Econst_int (Int.repr 32) tint)
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    tint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tint)
                                                                  tint)
                                                                tuint)
                                                              (tptr tulong))
                                                            tulong)
                                                          (Ebinop Oand
                                                            (Etempvar _t'2 tulong)
                                                            (Ebinop Osub
                                                              (Ebinop Oshl
                                                                (Ecast
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  tuint)
                                                                (Ebinop Odiv
                                                                  (Ebinop Omul
                                                                    (Econst_int (Int.repr 32) tint)
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    tint)
                                                                  (Econst_int (Int.repr 8) tint)
                                                                  tint)
                                                                tuint)
                                                              (Econst_int (Int.repr 1) tint)
                                                              tuint) tulong)))))
                                                  (Sset _j__1
                                                    (Ebinop Oadd
                                                      (Etempvar _j__1 tuint)
                                                      (Econst_int (Int.repr 1) tint)
                                                      tuint)))))
                                            (Ssequence
                                              (Sset _j__2
                                                (Econst_int (Int.repr 0) tint))
                                              (Ssequence
                                                (Sset _j__2
                                                  (Econst_int (Int.repr 0) tint))
                                                (Sloop
                                                  (Ssequence
                                                    (Sifthenelse (Ebinop Olt
                                                                   (Etempvar _j__2 tuint)
                                                                   (Ebinop Odiv
                                                                    (Econst_int (Int.repr 448) tint)
                                                                    (Ebinop Odiv
                                                                    (Ebinop Omul
                                                                    (Econst_int (Int.repr 32) tint)
                                                                    (Econst_int (Int.repr 7) tint)
                                                                    tint)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tint)
                                                                    tint)
                                                                   tint)
                                                      Sskip
                                                      Sbreak)
                                                    (Ssequence
                                                      (Sset _t'1
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _accum (tarray tulong 16))
                                                            (Etempvar _j__2 tuint)
                                                            (tptr tulong))
                                                          tulong))
                                                      (Sassign
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _c (tptr (Tstruct __257 noattr)))
                                                                (Tstruct __257 noattr))
                                                              _limb
                                                              (tarray tuint 16))
                                                            (Etempvar _j__2 tuint)
                                                            (tptr tuint))
                                                          tuint)
                                                        (Etempvar _t'1 tulong))))
                                                  (Sset _j__2
                                                    (Ebinop Oadd
                                                      (Etempvar _j__2 tuint)
                                                      (Econst_int (Int.repr 1) tint)
                                                      tuint)))))))))))))))))))))))))))
|}.

Definition f_gf_isqrt := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_y, (tptr (Tstruct __257 noattr))) ::
                (_x, (tptr (Tstruct __257 noattr))) :: nil);
  fn_vars := ((_a, (tarray (Tstruct __257 noattr) 1)) ::
              (_b, (tarray (Tstruct __257 noattr) 1)) ::
              (_c, (tarray (Tstruct __257 noattr) 1)) :: nil);
  fn_temps := ((_i, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _gf_mul (Tfunction
                    (Tcons (tptr (Tstruct __257 noattr))
                      (Tcons (tptr (Tstruct __257 noattr))
                        (Tcons (tptr (Tstruct __257 noattr)) Tnil))) tvoid
                    cc_default))
    ((Evar _c (tarray (Tstruct __257 noattr) 1)) ::
     (Etempvar _x (tptr (Tstruct __257 noattr))) ::
     (Etempvar _x (tptr (Tstruct __257 noattr))) :: nil))
  (Ssequence
    (Scall None
      (Evar _gf_mul (Tfunction
                      (Tcons (tptr (Tstruct __257 noattr))
                        (Tcons (tptr (Tstruct __257 noattr))
                          (Tcons (tptr (Tstruct __257 noattr)) Tnil))) tvoid
                      cc_default))
      ((Evar _b (tarray (Tstruct __257 noattr) 1)) ::
       (Etempvar _x (tptr (Tstruct __257 noattr))) ::
       (Evar _c (tarray (Tstruct __257 noattr) 1)) :: nil))
    (Ssequence
      (Scall None
        (Evar _gf_cpy (Tfunction
                        (Tcons (tptr (Tstruct __257 noattr))
                          (Tcons (tptr (Tstruct __257 noattr)) Tnil)) tvoid
                        cc_default))
        ((Evar _c (tarray (Tstruct __257 noattr) 1)) ::
         (Evar _b (tarray (Tstruct __257 noattr) 1)) :: nil))
      (Ssequence
        (Ssequence
          (Sset _i (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                             (Econst_int (Int.repr 1) tint) tint)
                Sskip
                Sbreak)
              (Scall None
                (Evar _gf_mul (Tfunction
                                (Tcons (tptr (Tstruct __257 noattr))
                                  (Tcons (tptr (Tstruct __257 noattr))
                                    (Tcons (tptr (Tstruct __257 noattr))
                                      Tnil))) tvoid cc_default))
                ((Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                 (Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                 (Evar _c (tarray (Tstruct __257 noattr) 1)) :: nil)))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))
        (Ssequence
          (Scall None
            (Evar _gf_mul (Tfunction
                            (Tcons (tptr (Tstruct __257 noattr))
                              (Tcons (tptr (Tstruct __257 noattr))
                                (Tcons (tptr (Tstruct __257 noattr)) Tnil)))
                            tvoid cc_default))
            ((Evar _b (tarray (Tstruct __257 noattr) 1)) ::
             (Etempvar _x (tptr (Tstruct __257 noattr))) ::
             (Evar _c (tarray (Tstruct __257 noattr) 1)) :: nil))
          (Ssequence
            (Scall None
              (Evar _gf_cpy (Tfunction
                              (Tcons (tptr (Tstruct __257 noattr))
                                (Tcons (tptr (Tstruct __257 noattr)) Tnil))
                              tvoid cc_default))
              ((Evar _c (tarray (Tstruct __257 noattr) 1)) ::
               (Evar _b (tarray (Tstruct __257 noattr) 1)) :: nil))
            (Ssequence
              (Ssequence
                (Sset _i (Econst_int (Int.repr 0) tint))
                (Sloop
                  (Ssequence
                    (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                   (Econst_int (Int.repr 3) tint) tint)
                      Sskip
                      Sbreak)
                    (Scall None
                      (Evar _gf_mul (Tfunction
                                      (Tcons (tptr (Tstruct __257 noattr))
                                        (Tcons (tptr (Tstruct __257 noattr))
                                          (Tcons
                                            (tptr (Tstruct __257 noattr))
                                            Tnil))) tvoid cc_default))
                      ((Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                       (Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                       (Evar _c (tarray (Tstruct __257 noattr) 1)) :: nil)))
                  (Sset _i
                    (Ebinop Oadd (Etempvar _i tint)
                      (Econst_int (Int.repr 1) tint) tint))))
              (Ssequence
                (Scall None
                  (Evar _gf_mul (Tfunction
                                  (Tcons (tptr (Tstruct __257 noattr))
                                    (Tcons (tptr (Tstruct __257 noattr))
                                      (Tcons (tptr (Tstruct __257 noattr))
                                        Tnil))) tvoid cc_default))
                  ((Evar _a (tarray (Tstruct __257 noattr) 1)) ::
                   (Evar _b (tarray (Tstruct __257 noattr) 1)) ::
                   (Evar _c (tarray (Tstruct __257 noattr) 1)) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _gf_cpy (Tfunction
                                    (Tcons (tptr (Tstruct __257 noattr))
                                      (Tcons (tptr (Tstruct __257 noattr))
                                        Tnil)) tvoid cc_default))
                    ((Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                     (Evar _a (tarray (Tstruct __257 noattr) 1)) :: nil))
                  (Ssequence
                    (Ssequence
                      (Sset _i (Econst_int (Int.repr 0) tint))
                      (Sloop
                        (Ssequence
                          (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                         (Econst_int (Int.repr 3) tint) tint)
                            Sskip
                            Sbreak)
                          (Scall None
                            (Evar _gf_mul (Tfunction
                                            (Tcons
                                              (tptr (Tstruct __257 noattr))
                                              (Tcons
                                                (tptr (Tstruct __257 noattr))
                                                (Tcons
                                                  (tptr (Tstruct __257 noattr))
                                                  Tnil))) tvoid cc_default))
                            ((Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                             (Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                             (Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                             nil)))
                        (Sset _i
                          (Ebinop Oadd (Etempvar _i tint)
                            (Econst_int (Int.repr 1) tint) tint))))
                    (Ssequence
                      (Scall None
                        (Evar _gf_mul (Tfunction
                                        (Tcons (tptr (Tstruct __257 noattr))
                                          (Tcons
                                            (tptr (Tstruct __257 noattr))
                                            (Tcons
                                              (tptr (Tstruct __257 noattr))
                                              Tnil))) tvoid cc_default))
                        ((Evar _a (tarray (Tstruct __257 noattr) 1)) ::
                         (Evar _b (tarray (Tstruct __257 noattr) 1)) ::
                         (Evar _c (tarray (Tstruct __257 noattr) 1)) :: nil))
                      (Ssequence
                        (Scall None
                          (Evar _gf_cpy (Tfunction
                                          (Tcons
                                            (tptr (Tstruct __257 noattr))
                                            (Tcons
                                              (tptr (Tstruct __257 noattr))
                                              Tnil)) tvoid cc_default))
                          ((Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                           (Evar _a (tarray (Tstruct __257 noattr) 1)) ::
                           nil))
                        (Ssequence
                          (Ssequence
                            (Sset _i (Econst_int (Int.repr 0) tint))
                            (Sloop
                              (Ssequence
                                (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                                               (Econst_int (Int.repr 9) tint)
                                               tint)
                                  Sskip
                                  Sbreak)
                                (Scall None
                                  (Evar _gf_mul (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct __257 noattr))
                                                    (Tcons
                                                      (tptr (Tstruct __257 noattr))
                                                      (Tcons
                                                        (tptr (Tstruct __257 noattr))
                                                        Tnil))) tvoid
                                                  cc_default))
                                  ((Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                   (Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                   (Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                   nil)))
                              (Sset _i
                                (Ebinop Oadd (Etempvar _i tint)
                                  (Econst_int (Int.repr 1) tint) tint))))
                          (Ssequence
                            (Scall None
                              (Evar _gf_mul (Tfunction
                                              (Tcons
                                                (tptr (Tstruct __257 noattr))
                                                (Tcons
                                                  (tptr (Tstruct __257 noattr))
                                                  (Tcons
                                                    (tptr (Tstruct __257 noattr))
                                                    Tnil))) tvoid cc_default))
                              ((Evar _b (tarray (Tstruct __257 noattr) 1)) ::
                               (Evar _a (tarray (Tstruct __257 noattr) 1)) ::
                               (Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                               nil))
                            (Ssequence
                              (Scall None
                                (Evar _gf_cpy (Tfunction
                                                (Tcons
                                                  (tptr (Tstruct __257 noattr))
                                                  (Tcons
                                                    (tptr (Tstruct __257 noattr))
                                                    Tnil)) tvoid cc_default))
                                ((Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                 (Evar _b (tarray (Tstruct __257 noattr) 1)) ::
                                 nil))
                              (Ssequence
                                (Ssequence
                                  (Sset _i (Econst_int (Int.repr 0) tint))
                                  (Sloop
                                    (Ssequence
                                      (Sifthenelse (Ebinop Olt
                                                     (Etempvar _i tint)
                                                     (Econst_int (Int.repr 1) tint)
                                                     tint)
                                        Sskip
                                        Sbreak)
                                      (Scall None
                                        (Evar _gf_mul (Tfunction
                                                        (Tcons
                                                          (tptr (Tstruct __257 noattr))
                                                          (Tcons
                                                            (tptr (Tstruct __257 noattr))
                                                            (Tcons
                                                              (tptr (Tstruct __257 noattr))
                                                              Tnil))) tvoid
                                                        cc_default))
                                        ((Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                         (Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                         (Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                         nil)))
                                    (Sset _i
                                      (Ebinop Oadd (Etempvar _i tint)
                                        (Econst_int (Int.repr 1) tint) tint))))
                                (Ssequence
                                  (Scall None
                                    (Evar _gf_mul (Tfunction
                                                    (Tcons
                                                      (tptr (Tstruct __257 noattr))
                                                      (Tcons
                                                        (tptr (Tstruct __257 noattr))
                                                        (Tcons
                                                          (tptr (Tstruct __257 noattr))
                                                          Tnil))) tvoid
                                                    cc_default))
                                    ((Evar _a (tarray (Tstruct __257 noattr) 1)) ::
                                     (Etempvar _x (tptr (Tstruct __257 noattr))) ::
                                     (Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                     nil))
                                  (Ssequence
                                    (Scall None
                                      (Evar _gf_cpy (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct __257 noattr))
                                                        (Tcons
                                                          (tptr (Tstruct __257 noattr))
                                                          Tnil)) tvoid
                                                      cc_default))
                                      ((Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                       (Evar _a (tarray (Tstruct __257 noattr) 1)) ::
                                       nil))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _i
                                          (Econst_int (Int.repr 0) tint))
                                        (Sloop
                                          (Ssequence
                                            (Sifthenelse (Ebinop Olt
                                                           (Etempvar _i tint)
                                                           (Econst_int (Int.repr 18) tint)
                                                           tint)
                                              Sskip
                                              Sbreak)
                                            (Scall None
                                              (Evar _gf_mul (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct __257 noattr))
                                                                (Tcons
                                                                  (tptr (Tstruct __257 noattr))
                                                                  (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    Tnil)))
                                                              tvoid
                                                              cc_default))
                                              ((Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                               (Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                               (Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                               nil)))
                                          (Sset _i
                                            (Ebinop Oadd (Etempvar _i tint)
                                              (Econst_int (Int.repr 1) tint)
                                              tint))))
                                      (Ssequence
                                        (Scall None
                                          (Evar _gf_mul (Tfunction
                                                          (Tcons
                                                            (tptr (Tstruct __257 noattr))
                                                            (Tcons
                                                              (tptr (Tstruct __257 noattr))
                                                              (Tcons
                                                                (tptr (Tstruct __257 noattr))
                                                                Tnil))) tvoid
                                                          cc_default))
                                          ((Evar _a (tarray (Tstruct __257 noattr) 1)) ::
                                           (Evar _b (tarray (Tstruct __257 noattr) 1)) ::
                                           (Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                           nil))
                                        (Ssequence
                                          (Scall None
                                            (Evar _gf_cpy (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct __257 noattr))
                                                              (Tcons
                                                                (tptr (Tstruct __257 noattr))
                                                                Tnil)) tvoid
                                                            cc_default))
                                            ((Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                             (Evar _a (tarray (Tstruct __257 noattr) 1)) ::
                                             nil))
                                          (Ssequence
                                            (Ssequence
                                              (Sset _i
                                                (Econst_int (Int.repr 0) tint))
                                              (Sloop
                                                (Ssequence
                                                  (Sifthenelse (Ebinop Olt
                                                                 (Etempvar _i tint)
                                                                 (Econst_int (Int.repr 37) tint)
                                                                 tint)
                                                    Sskip
                                                    Sbreak)
                                                  (Scall None
                                                    (Evar _gf_mul (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                    ((Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                                     (Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                                     (Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                                     nil)))
                                                (Sset _i
                                                  (Ebinop Oadd
                                                    (Etempvar _i tint)
                                                    (Econst_int (Int.repr 1) tint)
                                                    tint))))
                                            (Ssequence
                                              (Scall None
                                                (Evar _gf_mul (Tfunction
                                                                (Tcons
                                                                  (tptr (Tstruct __257 noattr))
                                                                  (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    Tnil)))
                                                                tvoid
                                                                cc_default))
                                                ((Evar _b (tarray (Tstruct __257 noattr) 1)) ::
                                                 (Evar _a (tarray (Tstruct __257 noattr) 1)) ::
                                                 (Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                                 nil))
                                              (Ssequence
                                                (Scall None
                                                  (Evar _gf_cpy (Tfunction
                                                                  (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    Tnil))
                                                                  tvoid
                                                                  cc_default))
                                                  ((Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                                   (Evar _b (tarray (Tstruct __257 noattr) 1)) ::
                                                   nil))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _i
                                                      (Econst_int (Int.repr 0) tint))
                                                    (Sloop
                                                      (Ssequence
                                                        (Sifthenelse 
                                                          (Ebinop Olt
                                                            (Etempvar _i tint)
                                                            (Econst_int (Int.repr 37) tint)
                                                            tint)
                                                          Sskip
                                                          Sbreak)
                                                        (Scall None
                                                          (Evar _gf_mul 
                                                          (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct __257 noattr))
                                                              (Tcons
                                                                (tptr (Tstruct __257 noattr))
                                                                (Tcons
                                                                  (tptr (Tstruct __257 noattr))
                                                                  Tnil)))
                                                            tvoid cc_default))
                                                          ((Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                                           (Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                                           (Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                                           nil)))
                                                      (Sset _i
                                                        (Ebinop Oadd
                                                          (Etempvar _i tint)
                                                          (Econst_int (Int.repr 1) tint)
                                                          tint))))
                                                  (Ssequence
                                                    (Scall None
                                                      (Evar _gf_mul (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                      ((Evar _b (tarray (Tstruct __257 noattr) 1)) ::
                                                       (Evar _a (tarray (Tstruct __257 noattr) 1)) ::
                                                       (Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                                       nil))
                                                    (Ssequence
                                                      (Scall None
                                                        (Evar _gf_cpy 
                                                        (Tfunction
                                                          (Tcons
                                                            (tptr (Tstruct __257 noattr))
                                                            (Tcons
                                                              (tptr (Tstruct __257 noattr))
                                                              Tnil)) tvoid
                                                          cc_default))
                                                        ((Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                                         (Evar _b (tarray (Tstruct __257 noattr) 1)) ::
                                                         nil))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Sset _i
                                                            (Econst_int (Int.repr 0) tint))
                                                          (Sloop
                                                            (Ssequence
                                                              (Sifthenelse 
                                                                (Ebinop Olt
                                                                  (Etempvar _i tint)
                                                                  (Econst_int (Int.repr 111) tint)
                                                                  tint)
                                                                Sskip
                                                                Sbreak)
                                                              (Scall None
                                                                (Evar _gf_mul 
                                                                (Tfunction
                                                                  (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    Tnil)))
                                                                  tvoid
                                                                  cc_default))
                                                                ((Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                                                 (Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                                                 (Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                                                 nil)))
                                                            (Sset _i
                                                              (Ebinop Oadd
                                                                (Etempvar _i tint)
                                                                (Econst_int (Int.repr 1) tint)
                                                                tint))))
                                                        (Ssequence
                                                          (Scall None
                                                            (Evar _gf_mul 
                                                            (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct __257 noattr))
                                                                (Tcons
                                                                  (tptr (Tstruct __257 noattr))
                                                                  (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    Tnil)))
                                                              tvoid
                                                              cc_default))
                                                            ((Evar _a (tarray (Tstruct __257 noattr) 1)) ::
                                                             (Evar _b (tarray (Tstruct __257 noattr) 1)) ::
                                                             (Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                                             nil))
                                                          (Ssequence
                                                            (Scall None
                                                              (Evar _gf_cpy 
                                                              (Tfunction
                                                                (Tcons
                                                                  (tptr (Tstruct __257 noattr))
                                                                  (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    Tnil))
                                                                tvoid
                                                                cc_default))
                                                              ((Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                                               (Evar _a (tarray (Tstruct __257 noattr) 1)) ::
                                                               nil))
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sset _i
                                                                  (Econst_int (Int.repr 0) tint))
                                                                (Sloop
                                                                  (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _i tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Scall None
                                                                    (Evar _gf_mul 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                                                    (Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                                                    (Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                                                    nil)))
                                                                  (Sset _i
                                                                    (Ebinop Oadd
                                                                    (Etempvar _i tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint))))
                                                              (Ssequence
                                                                (Scall None
                                                                  (Evar _gf_mul 
                                                                  (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                  ((Evar _b (tarray (Tstruct __257 noattr) 1)) ::
                                                                   (Etempvar _x (tptr (Tstruct __257 noattr))) ::
                                                                   (Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                                                   nil))
                                                                (Ssequence
                                                                  (Scall None
                                                                    (Evar _gf_cpy 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                                                    (Evar _b (tarray (Tstruct __257 noattr) 1)) ::
                                                                    nil))
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Sset _i
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _i tint)
                                                                    (Econst_int (Int.repr 223) tint)
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Scall None
                                                                    (Evar _gf_mul 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                                                    (Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                                                    (Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                                                    nil)))
                                                                    (Sset _i
                                                                    (Ebinop Oadd
                                                                    (Etempvar _i tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint))))
                                                                    (Scall None
                                                                    (Evar _gf_mul 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _y (tptr (Tstruct __257 noattr))) ::
                                                                    (Evar _a (tarray (Tstruct __257 noattr) 1)) ::
                                                                    (Evar _c (tarray (Tstruct __257 noattr) 1)) ::
                                                                    nil))))))))))))))))))))))))))))))))))))
|}.

Definition f_gf_inv := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_y, (tptr (Tstruct __257 noattr))) ::
                (_x, (tptr (Tstruct __257 noattr))) :: nil);
  fn_vars := ((_z, (tarray (Tstruct __257 noattr) 1)) ::
              (_w, (tarray (Tstruct __257 noattr) 1)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _gf_mul (Tfunction
                    (Tcons (tptr (Tstruct __257 noattr))
                      (Tcons (tptr (Tstruct __257 noattr))
                        (Tcons (tptr (Tstruct __257 noattr)) Tnil))) tvoid
                    cc_default))
    ((Evar _z (tarray (Tstruct __257 noattr) 1)) ::
     (Etempvar _x (tptr (Tstruct __257 noattr))) ::
     (Etempvar _x (tptr (Tstruct __257 noattr))) :: nil))
  (Ssequence
    (Scall None
      (Evar _gf_isqrt (Tfunction
                        (Tcons (tptr (Tstruct __257 noattr))
                          (Tcons (tptr (Tstruct __257 noattr)) Tnil)) tvoid
                        cc_default))
      ((Evar _w (tarray (Tstruct __257 noattr) 1)) ::
       (Evar _z (tarray (Tstruct __257 noattr) 1)) :: nil))
    (Ssequence
      (Scall None
        (Evar _gf_mul (Tfunction
                        (Tcons (tptr (Tstruct __257 noattr))
                          (Tcons (tptr (Tstruct __257 noattr))
                            (Tcons (tptr (Tstruct __257 noattr)) Tnil)))
                        tvoid cc_default))
        ((Evar _z (tarray (Tstruct __257 noattr) 1)) ::
         (Evar _w (tarray (Tstruct __257 noattr) 1)) ::
         (Evar _w (tarray (Tstruct __257 noattr) 1)) :: nil))
      (Ssequence
        (Scall None
          (Evar _gf_mul (Tfunction
                          (Tcons (tptr (Tstruct __257 noattr))
                            (Tcons (tptr (Tstruct __257 noattr))
                              (Tcons (tptr (Tstruct __257 noattr)) Tnil)))
                          tvoid cc_default))
          ((Evar _w (tarray (Tstruct __257 noattr) 1)) ::
           (Etempvar _x (tptr (Tstruct __257 noattr))) ::
           (Evar _z (tarray (Tstruct __257 noattr) 1)) :: nil))
        (Scall None
          (Evar _gf_cpy (Tfunction
                          (Tcons (tptr (Tstruct __257 noattr))
                            (Tcons (tptr (Tstruct __257 noattr)) Tnil)) tvoid
                          cc_default))
          ((Etempvar _y (tptr (Tstruct __257 noattr))) ::
           (Evar _w (tarray (Tstruct __257 noattr) 1)) :: nil))))))
|}.

Definition f_gf_reduce := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr (Tstruct __257 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_j, tuint) :: (_t'5, tuint) :: (_t'4, tuint) ::
               (_t'3, tuint) :: (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'4
      (Ederef
        (Ebinop Oadd
          (Efield
            (Ederef (Etempvar _x (tptr (Tstruct __257 noattr)))
              (Tstruct __257 noattr)) _limb (tarray tuint 16))
          (Ebinop Odiv
            (Ebinop Odiv (Econst_int (Int.repr 448) tint)
              (Ebinop Odiv
                (Ebinop Omul (Econst_int (Int.repr 32) tint)
                  (Econst_int (Int.repr 7) tint) tint)
                (Econst_int (Int.repr 8) tint) tint) tint)
            (Econst_int (Int.repr 2) tint) tint) (tptr tuint)) tuint))
    (Ssequence
      (Sset _t'5
        (Ederef
          (Ebinop Oadd
            (Efield
              (Ederef (Etempvar _x (tptr (Tstruct __257 noattr)))
                (Tstruct __257 noattr)) _limb (tarray tuint 16))
            (Ebinop Osub
              (Ebinop Odiv (Econst_int (Int.repr 448) tint)
                (Ebinop Odiv
                  (Ebinop Omul (Econst_int (Int.repr 32) tint)
                    (Econst_int (Int.repr 7) tint) tint)
                  (Econst_int (Int.repr 8) tint) tint) tint)
              (Econst_int (Int.repr 1) tint) tint) (tptr tuint)) tuint))
      (Sassign
        (Ederef
          (Ebinop Oadd
            (Efield
              (Ederef (Etempvar _x (tptr (Tstruct __257 noattr)))
                (Tstruct __257 noattr)) _limb (tarray tuint 16))
            (Ebinop Odiv
              (Ebinop Odiv (Econst_int (Int.repr 448) tint)
                (Ebinop Odiv
                  (Ebinop Omul (Econst_int (Int.repr 32) tint)
                    (Econst_int (Int.repr 7) tint) tint)
                  (Econst_int (Int.repr 8) tint) tint) tint)
              (Econst_int (Int.repr 2) tint) tint) (tptr tuint)) tuint)
        (Ebinop Oadd (Etempvar _t'4 tuint)
          (Ebinop Oshr (Etempvar _t'5 tuint)
            (Ebinop Odiv
              (Ebinop Omul (Econst_int (Int.repr 32) tint)
                (Econst_int (Int.repr 7) tint) tint)
              (Econst_int (Int.repr 8) tint) tint) tuint) tuint))))
  (Ssequence
    (Sset _j (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sset _j (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _j tuint)
                         (Ebinop Odiv (Econst_int (Int.repr 448) tint)
                           (Ebinop Odiv
                             (Ebinop Omul (Econst_int (Int.repr 32) tint)
                               (Econst_int (Int.repr 7) tint) tint)
                             (Econst_int (Int.repr 8) tint) tint) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Ssequence
              (Sset _t'2
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef (Etempvar _x (tptr (Tstruct __257 noattr)))
                        (Tstruct __257 noattr)) _limb (tarray tuint 16))
                    (Etempvar _j tuint) (tptr tuint)) tuint))
              (Ssequence
                (Sset _t'3
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef (Etempvar _x (tptr (Tstruct __257 noattr)))
                          (Tstruct __257 noattr)) _limb (tarray tuint 16))
                      (Ebinop Omod
                        (Ebinop Osub (Etempvar _j tuint)
                          (Econst_int (Int.repr 1) tint) tuint)
                        (Ebinop Odiv (Econst_int (Int.repr 448) tint)
                          (Ebinop Odiv
                            (Ebinop Omul (Econst_int (Int.repr 32) tint)
                              (Econst_int (Int.repr 7) tint) tint)
                            (Econst_int (Int.repr 8) tint) tint) tint) tuint)
                      (tptr tuint)) tuint))
                (Sassign
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef (Etempvar _x (tptr (Tstruct __257 noattr)))
                          (Tstruct __257 noattr)) _limb (tarray tuint 16))
                      (Etempvar _j tuint) (tptr tuint)) tuint)
                  (Ebinop Oadd (Etempvar _t'2 tuint)
                    (Ebinop Oshr (Etempvar _t'3 tuint)
                      (Ebinop Odiv
                        (Ebinop Omul (Econst_int (Int.repr 32) tint)
                          (Econst_int (Int.repr 7) tint) tint)
                        (Econst_int (Int.repr 8) tint) tint) tuint) tuint))))
            (Ssequence
              (Sset _t'1
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef (Etempvar _x (tptr (Tstruct __257 noattr)))
                        (Tstruct __257 noattr)) _limb (tarray tuint 16))
                    (Ebinop Omod
                      (Ebinop Osub (Etempvar _j tuint)
                        (Econst_int (Int.repr 1) tint) tuint)
                      (Ebinop Odiv (Econst_int (Int.repr 448) tint)
                        (Ebinop Odiv
                          (Ebinop Omul (Econst_int (Int.repr 32) tint)
                            (Econst_int (Int.repr 7) tint) tint)
                          (Econst_int (Int.repr 8) tint) tint) tint) tuint)
                    (tptr tuint)) tuint))
              (Sassign
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef (Etempvar _x (tptr (Tstruct __257 noattr)))
                        (Tstruct __257 noattr)) _limb (tarray tuint 16))
                    (Ebinop Omod
                      (Ebinop Osub (Etempvar _j tuint)
                        (Econst_int (Int.repr 1) tint) tuint)
                      (Ebinop Odiv (Econst_int (Int.repr 448) tint)
                        (Ebinop Odiv
                          (Ebinop Omul (Econst_int (Int.repr 32) tint)
                            (Econst_int (Int.repr 7) tint) tint)
                          (Econst_int (Int.repr 8) tint) tint) tint) tuint)
                    (tptr tuint)) tuint)
                (Ebinop Oand (Etempvar _t'1 tuint)
                  (Ebinop Osub
                    (Ebinop Oshl (Ecast (Econst_int (Int.repr 1) tint) tuint)
                      (Ebinop Odiv
                        (Ebinop Omul (Econst_int (Int.repr 32) tint)
                          (Econst_int (Int.repr 7) tint) tint)
                        (Econst_int (Int.repr 8) tint) tint) tuint)
                    (Econst_int (Int.repr 1) tint) tuint) tuint)))))
        (Sset _j
          (Ebinop Oadd (Etempvar _j tuint) (Econst_int (Int.repr 1) tint)
            tuint))))))
|}.

Definition f_gf_add := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr (Tstruct __257 noattr))) ::
                (_y, (tptr (Tstruct __257 noattr))) ::
                (_z, (tptr (Tstruct __257 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                         (Ebinop Odiv (Econst_int (Int.repr 448) tint)
                           (Ebinop Odiv
                             (Ebinop Omul (Econst_int (Int.repr 32) tint)
                               (Econst_int (Int.repr 7) tint) tint)
                             (Econst_int (Int.repr 8) tint) tint) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sset _t'1
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef (Etempvar _y (tptr (Tstruct __257 noattr)))
                      (Tstruct __257 noattr)) _limb (tarray tuint 16))
                  (Etempvar _i tuint) (tptr tuint)) tuint))
            (Ssequence
              (Sset _t'2
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef (Etempvar _z (tptr (Tstruct __257 noattr)))
                        (Tstruct __257 noattr)) _limb (tarray tuint 16))
                    (Etempvar _i tuint) (tptr tuint)) tuint))
              (Sassign
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef (Etempvar _x (tptr (Tstruct __257 noattr)))
                        (Tstruct __257 noattr)) _limb (tarray tuint 16))
                    (Etempvar _i tuint) (tptr tuint)) tuint)
                (Ebinop Oadd (Etempvar _t'1 tuint) (Etempvar _t'2 tuint)
                  tuint)))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
            tuint)))))
  (Scall None
    (Evar _gf_reduce (Tfunction (Tcons (tptr (Tstruct __257 noattr)) Tnil)
                       tvoid cc_default))
    ((Etempvar _x (tptr (Tstruct __257 noattr))) :: nil)))
|}.

Definition f_gf_sub := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr (Tstruct __257 noattr))) ::
                (_y, (tptr (Tstruct __257 noattr))) ::
                (_z, (tptr (Tstruct __257 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_t'3, tuint) :: (_t'2, tuint) ::
               (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                         (Ebinop Odiv (Econst_int (Int.repr 448) tint)
                           (Ebinop Odiv
                             (Ebinop Omul (Econst_int (Int.repr 32) tint)
                               (Econst_int (Int.repr 7) tint) tint)
                             (Econst_int (Int.repr 8) tint) tint) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sset _t'1
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef (Etempvar _y (tptr (Tstruct __257 noattr)))
                      (Tstruct __257 noattr)) _limb (tarray tuint 16))
                  (Etempvar _i tuint) (tptr tuint)) tuint))
            (Ssequence
              (Sset _t'2
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef (Etempvar _z (tptr (Tstruct __257 noattr)))
                        (Tstruct __257 noattr)) _limb (tarray tuint 16))
                    (Etempvar _i tuint) (tptr tuint)) tuint))
              (Ssequence
                (Sset _t'3
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef (Evar _P (tarray (Tstruct __257 noattr) 1))
                          (Tstruct __257 noattr)) _limb (tarray tuint 16))
                      (Etempvar _i tuint) (tptr tuint)) tuint))
                (Sassign
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef (Etempvar _x (tptr (Tstruct __257 noattr)))
                          (Tstruct __257 noattr)) _limb (tarray tuint 16))
                      (Etempvar _i tuint) (tptr tuint)) tuint)
                  (Ebinop Oadd
                    (Ebinop Osub (Etempvar _t'1 tuint) (Etempvar _t'2 tuint)
                      tuint)
                    (Ebinop Omul (Econst_int (Int.repr 2) tint)
                      (Etempvar _t'3 tuint) tuint) tuint))))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
            tuint)))))
  (Scall None
    (Evar _gf_reduce (Tfunction (Tcons (tptr (Tstruct __257 noattr)) Tnil)
                       tvoid cc_default))
    ((Etempvar _x (tptr (Tstruct __257 noattr))) :: nil)))
|}.

Definition f_cond_swap := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr (Tstruct __257 noattr))) ::
                (_y, (tptr (Tstruct __257 noattr))) :: (_swap, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_s, tuint) :: (_t'4, tuint) ::
               (_t'3, tuint) :: (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                       (Ebinop Odiv (Econst_int (Int.repr 448) tint)
                         (Ebinop Odiv
                           (Ebinop Omul (Econst_int (Int.repr 32) tint)
                             (Econst_int (Int.repr 7) tint) tint)
                           (Econst_int (Int.repr 8) tint) tint) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Ssequence
            (Sset _t'3
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef (Etempvar _x (tptr (Tstruct __257 noattr)))
                      (Tstruct __257 noattr)) _limb (tarray tuint 16))
                  (Etempvar _i tuint) (tptr tuint)) tuint))
            (Ssequence
              (Sset _t'4
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef (Etempvar _y (tptr (Tstruct __257 noattr)))
                        (Tstruct __257 noattr)) _limb (tarray tuint 16))
                    (Etempvar _i tuint) (tptr tuint)) tuint))
              (Sset _s
                (Ebinop Oand
                  (Ebinop Oxor (Etempvar _t'3 tuint) (Etempvar _t'4 tuint)
                    tuint) (Etempvar _swap tuint) tuint))))
          (Ssequence
            (Ssequence
              (Sset _t'2
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef (Etempvar _x (tptr (Tstruct __257 noattr)))
                        (Tstruct __257 noattr)) _limb (tarray tuint 16))
                    (Etempvar _i tuint) (tptr tuint)) tuint))
              (Sassign
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef (Etempvar _x (tptr (Tstruct __257 noattr)))
                        (Tstruct __257 noattr)) _limb (tarray tuint 16))
                    (Etempvar _i tuint) (tptr tuint)) tuint)
                (Ebinop Oxor (Etempvar _t'2 tuint) (Etempvar _s tuint) tuint)))
            (Ssequence
              (Sset _t'1
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef (Etempvar _y (tptr (Tstruct __257 noattr)))
                        (Tstruct __257 noattr)) _limb (tarray tuint 16))
                    (Etempvar _i tuint) (tptr tuint)) tuint))
              (Sassign
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef (Etempvar _y (tptr (Tstruct __257 noattr)))
                        (Tstruct __257 noattr)) _limb (tarray tuint 16))
                    (Etempvar _i tuint) (tptr tuint)) tuint)
                (Ebinop Oxor (Etempvar _t'1 tuint) (Etempvar _s tuint) tuint))))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
          tuint)))))
|}.

Definition f_gf_mlw := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr (Tstruct __257 noattr))) ::
                (_b, (tptr (Tstruct __257 noattr))) :: (_w, tint) :: nil);
  fn_vars := ((_ww, (tarray (Tstruct __257 noattr) 1)) ::
              (_ww__1, (tarray (Tstruct __257 noattr) 1)) :: nil);
  fn_temps := nil;
  fn_body :=
(Sifthenelse (Ebinop Ogt (Etempvar _w tint) (Econst_int (Int.repr 0) tint)
               tint)
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd
          (Efield
            (Ederef
              (Ebinop Oadd (Evar _ww (tarray (Tstruct __257 noattr) 1))
                (Econst_int (Int.repr 0) tint) (tptr (Tstruct __257 noattr)))
              (Tstruct __257 noattr)) _limb (tarray tuint 16))
          (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint)
      (Etempvar _w tint))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd
            (Efield
              (Ederef
                (Ebinop Oadd (Evar _ww (tarray (Tstruct __257 noattr) 1))
                  (Econst_int (Int.repr 0) tint)
                  (tptr (Tstruct __257 noattr))) (Tstruct __257 noattr))
              _limb (tarray tuint 16)) (Econst_int (Int.repr 1) tint)
            (tptr tuint)) tuint) (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef
                  (Ebinop Oadd (Evar _ww (tarray (Tstruct __257 noattr) 1))
                    (Econst_int (Int.repr 0) tint)
                    (tptr (Tstruct __257 noattr))) (Tstruct __257 noattr))
                _limb (tarray tuint 16)) (Econst_int (Int.repr 2) tint)
              (tptr tuint)) tuint) (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef
                    (Ebinop Oadd (Evar _ww (tarray (Tstruct __257 noattr) 1))
                      (Econst_int (Int.repr 0) tint)
                      (tptr (Tstruct __257 noattr))) (Tstruct __257 noattr))
                  _limb (tarray tuint 16)) (Econst_int (Int.repr 3) tint)
                (tptr tuint)) tuint) (Econst_int (Int.repr 0) tint))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef
                      (Ebinop Oadd
                        (Evar _ww (tarray (Tstruct __257 noattr) 1))
                        (Econst_int (Int.repr 0) tint)
                        (tptr (Tstruct __257 noattr)))
                      (Tstruct __257 noattr)) _limb (tarray tuint 16))
                  (Econst_int (Int.repr 4) tint) (tptr tuint)) tuint)
              (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Sassign
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Evar _ww (tarray (Tstruct __257 noattr) 1))
                          (Econst_int (Int.repr 0) tint)
                          (tptr (Tstruct __257 noattr)))
                        (Tstruct __257 noattr)) _limb (tarray tuint 16))
                    (Econst_int (Int.repr 5) tint) (tptr tuint)) tuint)
                (Econst_int (Int.repr 0) tint))
              (Ssequence
                (Sassign
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Ebinop Oadd
                            (Evar _ww (tarray (Tstruct __257 noattr) 1))
                            (Econst_int (Int.repr 0) tint)
                            (tptr (Tstruct __257 noattr)))
                          (Tstruct __257 noattr)) _limb (tarray tuint 16))
                      (Econst_int (Int.repr 6) tint) (tptr tuint)) tuint)
                  (Econst_int (Int.repr 0) tint))
                (Ssequence
                  (Sassign
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Ebinop Oadd
                              (Evar _ww (tarray (Tstruct __257 noattr) 1))
                              (Econst_int (Int.repr 0) tint)
                              (tptr (Tstruct __257 noattr)))
                            (Tstruct __257 noattr)) _limb (tarray tuint 16))
                        (Econst_int (Int.repr 7) tint) (tptr tuint)) tuint)
                    (Econst_int (Int.repr 0) tint))
                  (Ssequence
                    (Sassign
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Ebinop Oadd
                                (Evar _ww (tarray (Tstruct __257 noattr) 1))
                                (Econst_int (Int.repr 0) tint)
                                (tptr (Tstruct __257 noattr)))
                              (Tstruct __257 noattr)) _limb
                            (tarray tuint 16)) (Econst_int (Int.repr 8) tint)
                          (tptr tuint)) tuint)
                      (Econst_int (Int.repr 0) tint))
                    (Ssequence
                      (Sassign
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Ebinop Oadd
                                  (Evar _ww (tarray (Tstruct __257 noattr) 1))
                                  (Econst_int (Int.repr 0) tint)
                                  (tptr (Tstruct __257 noattr)))
                                (Tstruct __257 noattr)) _limb
                              (tarray tuint 16))
                            (Econst_int (Int.repr 9) tint) (tptr tuint))
                          tuint) (Econst_int (Int.repr 0) tint))
                      (Ssequence
                        (Sassign
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Ederef
                                  (Ebinop Oadd
                                    (Evar _ww (tarray (Tstruct __257 noattr) 1))
                                    (Econst_int (Int.repr 0) tint)
                                    (tptr (Tstruct __257 noattr)))
                                  (Tstruct __257 noattr)) _limb
                                (tarray tuint 16))
                              (Econst_int (Int.repr 10) tint) (tptr tuint))
                            tuint) (Econst_int (Int.repr 0) tint))
                        (Ssequence
                          (Sassign
                            (Ederef
                              (Ebinop Oadd
                                (Efield
                                  (Ederef
                                    (Ebinop Oadd
                                      (Evar _ww (tarray (Tstruct __257 noattr) 1))
                                      (Econst_int (Int.repr 0) tint)
                                      (tptr (Tstruct __257 noattr)))
                                    (Tstruct __257 noattr)) _limb
                                  (tarray tuint 16))
                                (Econst_int (Int.repr 11) tint) (tptr tuint))
                              tuint) (Econst_int (Int.repr 0) tint))
                          (Ssequence
                            (Sassign
                              (Ederef
                                (Ebinop Oadd
                                  (Efield
                                    (Ederef
                                      (Ebinop Oadd
                                        (Evar _ww (tarray (Tstruct __257 noattr) 1))
                                        (Econst_int (Int.repr 0) tint)
                                        (tptr (Tstruct __257 noattr)))
                                      (Tstruct __257 noattr)) _limb
                                    (tarray tuint 16))
                                  (Econst_int (Int.repr 12) tint)
                                  (tptr tuint)) tuint)
                              (Econst_int (Int.repr 0) tint))
                            (Ssequence
                              (Sassign
                                (Ederef
                                  (Ebinop Oadd
                                    (Efield
                                      (Ederef
                                        (Ebinop Oadd
                                          (Evar _ww (tarray (Tstruct __257 noattr) 1))
                                          (Econst_int (Int.repr 0) tint)
                                          (tptr (Tstruct __257 noattr)))
                                        (Tstruct __257 noattr)) _limb
                                      (tarray tuint 16))
                                    (Econst_int (Int.repr 13) tint)
                                    (tptr tuint)) tuint)
                                (Econst_int (Int.repr 0) tint))
                              (Ssequence
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd
                                      (Efield
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar _ww (tarray (Tstruct __257 noattr) 1))
                                            (Econst_int (Int.repr 0) tint)
                                            (tptr (Tstruct __257 noattr)))
                                          (Tstruct __257 noattr)) _limb
                                        (tarray tuint 16))
                                      (Econst_int (Int.repr 14) tint)
                                      (tptr tuint)) tuint)
                                  (Econst_int (Int.repr 0) tint))
                                (Ssequence
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Efield
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _ww (tarray (Tstruct __257 noattr) 1))
                                              (Econst_int (Int.repr 0) tint)
                                              (tptr (Tstruct __257 noattr)))
                                            (Tstruct __257 noattr)) _limb
                                          (tarray tuint 16))
                                        (Econst_int (Int.repr 15) tint)
                                        (tptr tuint)) tuint)
                                    (Econst_int (Int.repr 0) tint))
                                  (Scall None
                                    (Evar _gf_mul (Tfunction
                                                    (Tcons
                                                      (tptr (Tstruct __257 noattr))
                                                      (Tcons
                                                        (tptr (Tstruct __257 noattr))
                                                        (Tcons
                                                          (tptr (Tstruct __257 noattr))
                                                          Tnil))) tvoid
                                                    cc_default))
                                    ((Etempvar _a (tptr (Tstruct __257 noattr))) ::
                                     (Etempvar _b (tptr (Tstruct __257 noattr))) ::
                                     (Evar _ww (tarray (Tstruct __257 noattr) 1)) ::
                                     nil))))))))))))))))))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd
          (Efield
            (Ederef
              (Ebinop Oadd (Evar _ww__1 (tarray (Tstruct __257 noattr) 1))
                (Econst_int (Int.repr 0) tint) (tptr (Tstruct __257 noattr)))
              (Tstruct __257 noattr)) _limb (tarray tuint 16))
          (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint)
      (Eunop Oneg (Etempvar _w tint) tint))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd
            (Efield
              (Ederef
                (Ebinop Oadd (Evar _ww__1 (tarray (Tstruct __257 noattr) 1))
                  (Econst_int (Int.repr 0) tint)
                  (tptr (Tstruct __257 noattr))) (Tstruct __257 noattr))
              _limb (tarray tuint 16)) (Econst_int (Int.repr 1) tint)
            (tptr tuint)) tuint) (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef
                  (Ebinop Oadd
                    (Evar _ww__1 (tarray (Tstruct __257 noattr) 1))
                    (Econst_int (Int.repr 0) tint)
                    (tptr (Tstruct __257 noattr))) (Tstruct __257 noattr))
                _limb (tarray tuint 16)) (Econst_int (Int.repr 2) tint)
              (tptr tuint)) tuint) (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef
                    (Ebinop Oadd
                      (Evar _ww__1 (tarray (Tstruct __257 noattr) 1))
                      (Econst_int (Int.repr 0) tint)
                      (tptr (Tstruct __257 noattr))) (Tstruct __257 noattr))
                  _limb (tarray tuint 16)) (Econst_int (Int.repr 3) tint)
                (tptr tuint)) tuint) (Econst_int (Int.repr 0) tint))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef
                      (Ebinop Oadd
                        (Evar _ww__1 (tarray (Tstruct __257 noattr) 1))
                        (Econst_int (Int.repr 0) tint)
                        (tptr (Tstruct __257 noattr)))
                      (Tstruct __257 noattr)) _limb (tarray tuint 16))
                  (Econst_int (Int.repr 4) tint) (tptr tuint)) tuint)
              (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Sassign
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef
                        (Ebinop Oadd
                          (Evar _ww__1 (tarray (Tstruct __257 noattr) 1))
                          (Econst_int (Int.repr 0) tint)
                          (tptr (Tstruct __257 noattr)))
                        (Tstruct __257 noattr)) _limb (tarray tuint 16))
                    (Econst_int (Int.repr 5) tint) (tptr tuint)) tuint)
                (Econst_int (Int.repr 0) tint))
              (Ssequence
                (Sassign
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Ebinop Oadd
                            (Evar _ww__1 (tarray (Tstruct __257 noattr) 1))
                            (Econst_int (Int.repr 0) tint)
                            (tptr (Tstruct __257 noattr)))
                          (Tstruct __257 noattr)) _limb (tarray tuint 16))
                      (Econst_int (Int.repr 6) tint) (tptr tuint)) tuint)
                  (Econst_int (Int.repr 0) tint))
                (Ssequence
                  (Sassign
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Ebinop Oadd
                              (Evar _ww__1 (tarray (Tstruct __257 noattr) 1))
                              (Econst_int (Int.repr 0) tint)
                              (tptr (Tstruct __257 noattr)))
                            (Tstruct __257 noattr)) _limb (tarray tuint 16))
                        (Econst_int (Int.repr 7) tint) (tptr tuint)) tuint)
                    (Econst_int (Int.repr 0) tint))
                  (Ssequence
                    (Sassign
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Ebinop Oadd
                                (Evar _ww__1 (tarray (Tstruct __257 noattr) 1))
                                (Econst_int (Int.repr 0) tint)
                                (tptr (Tstruct __257 noattr)))
                              (Tstruct __257 noattr)) _limb
                            (tarray tuint 16)) (Econst_int (Int.repr 8) tint)
                          (tptr tuint)) tuint)
                      (Econst_int (Int.repr 0) tint))
                    (Ssequence
                      (Sassign
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Ebinop Oadd
                                  (Evar _ww__1 (tarray (Tstruct __257 noattr) 1))
                                  (Econst_int (Int.repr 0) tint)
                                  (tptr (Tstruct __257 noattr)))
                                (Tstruct __257 noattr)) _limb
                              (tarray tuint 16))
                            (Econst_int (Int.repr 9) tint) (tptr tuint))
                          tuint) (Econst_int (Int.repr 0) tint))
                      (Ssequence
                        (Sassign
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Ederef
                                  (Ebinop Oadd
                                    (Evar _ww__1 (tarray (Tstruct __257 noattr) 1))
                                    (Econst_int (Int.repr 0) tint)
                                    (tptr (Tstruct __257 noattr)))
                                  (Tstruct __257 noattr)) _limb
                                (tarray tuint 16))
                              (Econst_int (Int.repr 10) tint) (tptr tuint))
                            tuint) (Econst_int (Int.repr 0) tint))
                        (Ssequence
                          (Sassign
                            (Ederef
                              (Ebinop Oadd
                                (Efield
                                  (Ederef
                                    (Ebinop Oadd
                                      (Evar _ww__1 (tarray (Tstruct __257 noattr) 1))
                                      (Econst_int (Int.repr 0) tint)
                                      (tptr (Tstruct __257 noattr)))
                                    (Tstruct __257 noattr)) _limb
                                  (tarray tuint 16))
                                (Econst_int (Int.repr 11) tint) (tptr tuint))
                              tuint) (Econst_int (Int.repr 0) tint))
                          (Ssequence
                            (Sassign
                              (Ederef
                                (Ebinop Oadd
                                  (Efield
                                    (Ederef
                                      (Ebinop Oadd
                                        (Evar _ww__1 (tarray (Tstruct __257 noattr) 1))
                                        (Econst_int (Int.repr 0) tint)
                                        (tptr (Tstruct __257 noattr)))
                                      (Tstruct __257 noattr)) _limb
                                    (tarray tuint 16))
                                  (Econst_int (Int.repr 12) tint)
                                  (tptr tuint)) tuint)
                              (Econst_int (Int.repr 0) tint))
                            (Ssequence
                              (Sassign
                                (Ederef
                                  (Ebinop Oadd
                                    (Efield
                                      (Ederef
                                        (Ebinop Oadd
                                          (Evar _ww__1 (tarray (Tstruct __257 noattr) 1))
                                          (Econst_int (Int.repr 0) tint)
                                          (tptr (Tstruct __257 noattr)))
                                        (Tstruct __257 noattr)) _limb
                                      (tarray tuint 16))
                                    (Econst_int (Int.repr 13) tint)
                                    (tptr tuint)) tuint)
                                (Econst_int (Int.repr 0) tint))
                              (Ssequence
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd
                                      (Efield
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar _ww__1 (tarray (Tstruct __257 noattr) 1))
                                            (Econst_int (Int.repr 0) tint)
                                            (tptr (Tstruct __257 noattr)))
                                          (Tstruct __257 noattr)) _limb
                                        (tarray tuint 16))
                                      (Econst_int (Int.repr 14) tint)
                                      (tptr tuint)) tuint)
                                  (Econst_int (Int.repr 0) tint))
                                (Ssequence
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Efield
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _ww__1 (tarray (Tstruct __257 noattr) 1))
                                              (Econst_int (Int.repr 0) tint)
                                              (tptr (Tstruct __257 noattr)))
                                            (Tstruct __257 noattr)) _limb
                                          (tarray tuint 16))
                                        (Econst_int (Int.repr 15) tint)
                                        (tptr tuint)) tuint)
                                    (Econst_int (Int.repr 0) tint))
                                  (Ssequence
                                    (Scall None
                                      (Evar _gf_mul (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct __257 noattr))
                                                        (Tcons
                                                          (tptr (Tstruct __257 noattr))
                                                          (Tcons
                                                            (tptr (Tstruct __257 noattr))
                                                            Tnil))) tvoid
                                                      cc_default))
                                      ((Etempvar _a (tptr (Tstruct __257 noattr))) ::
                                       (Etempvar _b (tptr (Tstruct __257 noattr))) ::
                                       (Evar _ww__1 (tarray (Tstruct __257 noattr) 1)) ::
                                       nil))
                                    (Scall None
                                      (Evar _gf_sub (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct __257 noattr))
                                                        (Tcons
                                                          (tptr (Tstruct __257 noattr))
                                                          (Tcons
                                                            (tptr (Tstruct __257 noattr))
                                                            Tnil))) tvoid
                                                      cc_default))
                                      ((Etempvar _a (tptr (Tstruct __257 noattr))) ::
                                       (Evar _ZERO (tarray (Tstruct __257 noattr) 1)) ::
                                       (Etempvar _a (tptr (Tstruct __257 noattr))) ::
                                       nil))))))))))))))))))))
|}.

Definition f_gf_canon := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr (Tstruct __257 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_carry, tlong) :: (_i, tuint) :: (_addback, tuint) ::
               (_i__1, tuint) :: (_t'4, tuint) :: (_t'3, tuint) ::
               (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _gf_reduce (Tfunction (Tcons (tptr (Tstruct __257 noattr)) Tnil)
                       tvoid cc_default))
    ((Etempvar _a (tptr (Tstruct __257 noattr))) :: nil))
  (Ssequence
    (Sset _carry (Ecast (Econst_int (Int.repr 0) tint) tlong))
    (Ssequence
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Sset _i (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                             (Ebinop Odiv (Econst_int (Int.repr 448) tint)
                               (Ebinop Odiv
                                 (Ebinop Omul (Econst_int (Int.repr 32) tint)
                                   (Econst_int (Int.repr 7) tint) tint)
                                 (Econst_int (Int.repr 8) tint) tint) tint)
                             tint)
                Sskip
                Sbreak)
              (Ssequence
                (Ssequence
                  (Sset _t'3
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef (Etempvar _a (tptr (Tstruct __257 noattr)))
                            (Tstruct __257 noattr)) _limb (tarray tuint 16))
                        (Etempvar _i tuint) (tptr tuint)) tuint))
                  (Ssequence
                    (Sset _t'4
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Evar _P (tarray (Tstruct __257 noattr) 1))
                              (Tstruct __257 noattr)) _limb
                            (tarray tuint 16)) (Etempvar _i tuint)
                          (tptr tuint)) tuint))
                    (Sset _carry
                      (Ebinop Osub
                        (Ebinop Oadd (Etempvar _carry tlong)
                          (Etempvar _t'3 tuint) tlong) (Etempvar _t'4 tuint)
                        tlong))))
                (Ssequence
                  (Sassign
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef (Etempvar _a (tptr (Tstruct __257 noattr)))
                            (Tstruct __257 noattr)) _limb (tarray tuint 16))
                        (Etempvar _i tuint) (tptr tuint)) tuint)
                    (Ebinop Oand (Etempvar _carry tlong)
                      (Ebinop Osub
                        (Ebinop Oshl
                          (Ecast (Econst_int (Int.repr 1) tint) tuint)
                          (Ebinop Odiv
                            (Ebinop Omul (Econst_int (Int.repr 32) tint)
                              (Econst_int (Int.repr 7) tint) tint)
                            (Econst_int (Int.repr 8) tint) tint) tuint)
                        (Econst_int (Int.repr 1) tint) tuint) tlong))
                  (Sset _carry
                    (Ebinop Oshr (Etempvar _carry tlong)
                      (Ebinop Odiv
                        (Ebinop Omul (Econst_int (Int.repr 32) tint)
                          (Econst_int (Int.repr 7) tint) tint)
                        (Econst_int (Int.repr 8) tint) tint) tlong)))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
                tuint)))))
      (Ssequence
        (Sset _addback (Ecast (Etempvar _carry tlong) tuint))
        (Ssequence
          (Sset _carry (Ecast (Econst_int (Int.repr 0) tint) tlong))
          (Ssequence
            (Sset _i__1 (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Sset _i__1 (Econst_int (Int.repr 0) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _i__1 tuint)
                                 (Ebinop Odiv
                                   (Econst_int (Int.repr 448) tint)
                                   (Ebinop Odiv
                                     (Ebinop Omul
                                       (Econst_int (Int.repr 32) tint)
                                       (Econst_int (Int.repr 7) tint) tint)
                                     (Econst_int (Int.repr 8) tint) tint)
                                   tint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Ssequence
                      (Sset _t'1
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _a (tptr (Tstruct __257 noattr)))
                                (Tstruct __257 noattr)) _limb
                              (tarray tuint 16)) (Etempvar _i__1 tuint)
                            (tptr tuint)) tuint))
                      (Ssequence
                        (Sset _t'2
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Ederef
                                  (Evar _P (tarray (Tstruct __257 noattr) 1))
                                  (Tstruct __257 noattr)) _limb
                                (tarray tuint 16)) (Etempvar _i__1 tuint)
                              (tptr tuint)) tuint))
                        (Sset _carry
                          (Ebinop Oadd
                            (Ebinop Oadd (Etempvar _carry tlong)
                              (Etempvar _t'1 tuint) tlong)
                            (Ebinop Oand (Etempvar _t'2 tuint)
                              (Etempvar _addback tuint) tuint) tlong))))
                    (Ssequence
                      (Sassign
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _a (tptr (Tstruct __257 noattr)))
                                (Tstruct __257 noattr)) _limb
                              (tarray tuint 16)) (Etempvar _i__1 tuint)
                            (tptr tuint)) tuint)
                        (Ebinop Oand (Etempvar _carry tlong)
                          (Ebinop Osub
                            (Ebinop Oshl
                              (Ecast (Econst_int (Int.repr 1) tint) tuint)
                              (Ebinop Odiv
                                (Ebinop Omul (Econst_int (Int.repr 32) tint)
                                  (Econst_int (Int.repr 7) tint) tint)
                                (Econst_int (Int.repr 8) tint) tint) tuint)
                            (Econst_int (Int.repr 1) tint) tuint) tlong))
                      (Sset _carry
                        (Ebinop Oshr (Etempvar _carry tlong)
                          (Ebinop Odiv
                            (Ebinop Omul (Econst_int (Int.repr 32) tint)
                              (Econst_int (Int.repr 7) tint) tint)
                            (Econst_int (Int.repr 8) tint) tint) tlong)))))
                (Sset _i__1
                  (Ebinop Oadd (Etempvar _i__1 tuint)
                    (Econst_int (Int.repr 1) tint) tuint))))))))))
|}.

Definition f_gf_deser := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct __257 noattr))) ::
                (_ser, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_k, tuint) :: (_bits, tuint) ::
               (_buf, tulong) :: (_accum, tlong) :: (_i__1, tuint) ::
               (_t'3, tuint) :: (_t'2, tint) :: (_t'1, tint) ::
               (_t'6, tuchar) :: (_t'5, tuint) :: (_t'4, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _k (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sset _bits (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sset _buf (Ecast (Econst_int (Int.repr 0) tint) tulong))
      (Ssequence
        (Ssequence
          (Sset _i (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                             (Ebinop Odiv (Econst_int (Int.repr 448) tint)
                               (Econst_int (Int.repr 8) tint) tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Ssequence
                  (Sset _t'6
                    (Ederef
                      (Ebinop Oadd (Etempvar _ser (tptr tuchar))
                        (Etempvar _i tuint) (tptr tuchar)) tuchar))
                  (Sset _buf
                    (Ebinop Oor (Etempvar _buf tulong)
                      (Ebinop Oshl (Ecast (Etempvar _t'6 tuchar) tulong)
                        (Etempvar _bits tuint) tulong) tulong)))
                (Ssequence
                  (Sset _bits
                    (Ebinop Oadd (Etempvar _bits tuint)
                      (Econst_int (Int.repr 8) tint) tuint))
                  (Sloop
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Sifthenelse (Ebinop Oge (Etempvar _bits tuint)
                                         (Ebinop Odiv
                                           (Ebinop Omul
                                             (Econst_int (Int.repr 32) tint)
                                             (Econst_int (Int.repr 7) tint)
                                             tint)
                                           (Econst_int (Int.repr 8) tint)
                                           tint) tint)
                            (Sset _t'1 (Econst_int (Int.repr 1) tint))
                            (Sset _t'1
                              (Ecast
                                (Ebinop Oeq (Etempvar _i tuint)
                                  (Ebinop Osub
                                    (Ebinop Odiv
                                      (Econst_int (Int.repr 448) tint)
                                      (Econst_int (Int.repr 8) tint) tint)
                                    (Econst_int (Int.repr 1) tint) tint)
                                  tint) tbool)))
                          (Sifthenelse (Etempvar _t'1 tint)
                            (Sset _t'2
                              (Ecast
                                (Ebinop Olt (Etempvar _k tuint)
                                  (Ebinop Odiv
                                    (Econst_int (Int.repr 448) tint)
                                    (Ebinop Odiv
                                      (Ebinop Omul
                                        (Econst_int (Int.repr 32) tint)
                                        (Econst_int (Int.repr 7) tint) tint)
                                      (Econst_int (Int.repr 8) tint) tint)
                                    tint) tint) tbool))
                            (Sset _t'2 (Econst_int (Int.repr 0) tint))))
                        (Sifthenelse (Etempvar _t'2 tint) Sskip Sbreak))
                      (Ssequence
                        (Ssequence
                          (Sset _t'3 (Etempvar _k tuint))
                          (Sset _k
                            (Ebinop Oadd (Etempvar _t'3 tuint)
                              (Econst_int (Int.repr 1) tint) tuint)))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Ederef
                                  (Etempvar _s (tptr (Tstruct __257 noattr)))
                                  (Tstruct __257 noattr)) _limb
                                (tarray tuint 16)) (Etempvar _t'3 tuint)
                              (tptr tuint)) tuint)
                          (Ebinop Oand (Etempvar _buf tulong)
                            (Ebinop Osub
                              (Ebinop Oshl
                                (Ecast (Econst_int (Int.repr 1) tint) tuint)
                                (Ebinop Odiv
                                  (Ebinop Omul
                                    (Econst_int (Int.repr 32) tint)
                                    (Econst_int (Int.repr 7) tint) tint)
                                  (Econst_int (Int.repr 8) tint) tint) tuint)
                              (Econst_int (Int.repr 1) tint) tuint) tulong))))
                    (Ssequence
                      (Sset _bits
                        (Ebinop Osub (Etempvar _bits tuint)
                          (Ebinop Odiv
                            (Ebinop Omul (Econst_int (Int.repr 32) tint)
                              (Econst_int (Int.repr 7) tint) tint)
                            (Econst_int (Int.repr 8) tint) tint) tuint))
                      (Sset _buf
                        (Ebinop Oshr (Etempvar _buf tulong)
                          (Ebinop Odiv
                            (Ebinop Omul (Econst_int (Int.repr 32) tint)
                              (Econst_int (Int.repr 7) tint) tint)
                            (Econst_int (Int.repr 8) tint) tint) tulong)))))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
                tuint))))
        (Ssequence
          (Sset _accum (Ecast (Econst_int (Int.repr 0) tint) tlong))
          (Ssequence
            (Ssequence
              (Sset _i__1 (Econst_int (Int.repr 0) tint))
              (Ssequence
                (Sset _i__1 (Econst_int (Int.repr 0) tint))
                (Sloop
                  (Ssequence
                    (Sifthenelse (Ebinop Olt (Etempvar _i__1 tuint)
                                   (Ebinop Odiv
                                     (Econst_int (Int.repr 448) tint)
                                     (Ebinop Odiv
                                       (Ebinop Omul
                                         (Econst_int (Int.repr 32) tint)
                                         (Econst_int (Int.repr 7) tint) tint)
                                       (Econst_int (Int.repr 8) tint) tint)
                                     tint) tint)
                      Sskip
                      Sbreak)
                    (Ssequence
                      (Sset _t'4
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _s (tptr (Tstruct __257 noattr)))
                                (Tstruct __257 noattr)) _limb
                              (tarray tuint 16)) (Etempvar _i__1 tuint)
                            (tptr tuint)) tuint))
                      (Ssequence
                        (Sset _t'5
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Ederef
                                  (Evar _P (tarray (Tstruct __257 noattr) 1))
                                  (Tstruct __257 noattr)) _limb
                                (tarray tuint 16)) (Etempvar _i__1 tuint)
                              (tptr tuint)) tuint))
                        (Sset _accum
                          (Ebinop Oshr
                            (Ebinop Osub
                              (Ebinop Oadd (Etempvar _accum tlong)
                                (Etempvar _t'4 tuint) tlong)
                              (Etempvar _t'5 tuint) tlong)
                            (Econst_int (Int.repr 32) tint) tlong)))))
                  (Sset _i__1
                    (Ebinop Oadd (Etempvar _i__1 tuint)
                      (Econst_int (Int.repr 1) tint) tuint)))))
            (Sreturn (Some (Etempvar _accum tlong)))))))))
|}.

Definition f_gf_ser := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ser, (tptr tuchar)) ::
                (_a, (tptr (Tstruct __257 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_k, tint) :: (_bits, tint) :: (_buf, tulong) ::
               (_i, tuint) :: (_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) ::
               (_t'4, tuint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _gf_canon (Tfunction (Tcons (tptr (Tstruct __257 noattr)) Tnil)
                      tvoid cc_default))
    ((Etempvar _a (tptr (Tstruct __257 noattr))) :: nil))
  (Ssequence
    (Sset _k (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sset _bits (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sset _buf (Ecast (Econst_int (Int.repr 0) tint) tulong))
        (Ssequence
          (Sset _i (Econst_int (Int.repr 0) tint))
          (Ssequence
            (Sset _i (Econst_int (Int.repr 0) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                               (Ebinop Odiv (Econst_int (Int.repr 448) tint)
                                 (Ebinop Odiv
                                   (Ebinop Omul
                                     (Econst_int (Int.repr 32) tint)
                                     (Econst_int (Int.repr 7) tint) tint)
                                   (Econst_int (Int.repr 8) tint) tint) tint)
                               tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Ssequence
                    (Sset _t'4
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _a (tptr (Tstruct __257 noattr)))
                              (Tstruct __257 noattr)) _limb
                            (tarray tuint 16)) (Etempvar _i tuint)
                          (tptr tuint)) tuint))
                    (Sset _buf
                      (Ebinop Oor (Etempvar _buf tulong)
                        (Ebinop Oshl (Ecast (Etempvar _t'4 tuint) tulong)
                          (Etempvar _bits tint) tulong) tulong)))
                  (Ssequence
                    (Sset _bits
                      (Ebinop Oadd (Etempvar _bits tint)
                        (Ebinop Odiv
                          (Ebinop Omul (Econst_int (Int.repr 32) tint)
                            (Econst_int (Int.repr 7) tint) tint)
                          (Econst_int (Int.repr 8) tint) tint) tint))
                    (Sloop
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Sifthenelse (Ebinop Oge (Etempvar _bits tint)
                                           (Econst_int (Int.repr 8) tint)
                                           tint)
                              (Sset _t'1 (Econst_int (Int.repr 1) tint))
                              (Sset _t'1
                                (Ecast
                                  (Ebinop Oeq (Etempvar _i tuint)
                                    (Ebinop Osub
                                      (Ebinop Odiv
                                        (Econst_int (Int.repr 448) tint)
                                        (Ebinop Odiv
                                          (Ebinop Omul
                                            (Econst_int (Int.repr 32) tint)
                                            (Econst_int (Int.repr 7) tint)
                                            tint)
                                          (Econst_int (Int.repr 8) tint)
                                          tint) tint)
                                      (Econst_int (Int.repr 1) tint) tint)
                                    tint) tbool)))
                            (Sifthenelse (Etempvar _t'1 tint)
                              (Sset _t'2
                                (Ecast
                                  (Ebinop Olt (Etempvar _k tint)
                                    (Ebinop Odiv
                                      (Econst_int (Int.repr 448) tint)
                                      (Econst_int (Int.repr 8) tint) tint)
                                    tint) tbool))
                              (Sset _t'2 (Econst_int (Int.repr 0) tint))))
                          (Sifthenelse (Etempvar _t'2 tint) Sskip Sbreak))
                        (Ssequence
                          (Ssequence
                            (Sset _t'3 (Etempvar _k tint))
                            (Sset _k
                              (Ebinop Oadd (Etempvar _t'3 tint)
                                (Econst_int (Int.repr 1) tint) tint)))
                          (Sassign
                            (Ederef
                              (Ebinop Oadd (Etempvar _ser (tptr tuchar))
                                (Etempvar _t'3 tint) (tptr tuchar)) tuchar)
                            (Etempvar _buf tulong))))
                      (Ssequence
                        (Sset _bits
                          (Ebinop Osub (Etempvar _bits tint)
                            (Econst_int (Int.repr 8) tint) tint))
                        (Sset _buf
                          (Ebinop Oshr (Etempvar _buf tulong)
                            (Econst_int (Int.repr 8) tint) tulong)))))))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tuint)
                  (Econst_int (Int.repr 1) tint) tuint)))))))))
|}.

Definition f_x448 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr tuchar)) :: (_scalar, (tptr tuchar)) ::
                (_base, (tptr tuchar)) :: nil);
  fn_vars := ((_x1, (tarray (Tstruct __257 noattr) 1)) ::
              (_x2, (tarray (Tstruct __257 noattr) 1)) ::
              (_z2, (tarray (Tstruct __257 noattr) 1)) ::
              (_x3, (tarray (Tstruct __257 noattr) 1)) ::
              (_z3, (tarray (Tstruct __257 noattr) 1)) ::
              (_t1, (tarray (Tstruct __257 noattr) 1)) ::
              (_t2, (tarray (Tstruct __257 noattr) 1)) :: nil);
  fn_temps := ((_t, tint) :: (_swap, tuint) :: (_sb, tuchar) ::
               (_k_t, tuint) :: (_nz, tint) :: (_t'3, tuchar) ::
               (_t'2, tint) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _gf_deser (Tfunction
                      (Tcons (tptr (Tstruct __257 noattr))
                        (Tcons (tptr tuchar) Tnil)) tuint cc_default))
    ((Evar _x1 (tarray (Tstruct __257 noattr) 1)) ::
     (Etempvar _base (tptr tuchar)) :: nil))
  (Ssequence
    (Scall None
      (Evar _gf_cpy (Tfunction
                      (Tcons (tptr (Tstruct __257 noattr))
                        (Tcons (tptr (Tstruct __257 noattr)) Tnil)) tvoid
                      cc_default))
      ((Evar _x2 (tarray (Tstruct __257 noattr) 1)) ::
       (Evar _ONE (tarray (Tstruct __257 noattr) 1)) :: nil))
    (Ssequence
      (Scall None
        (Evar _gf_cpy (Tfunction
                        (Tcons (tptr (Tstruct __257 noattr))
                          (Tcons (tptr (Tstruct __257 noattr)) Tnil)) tvoid
                        cc_default))
        ((Evar _z2 (tarray (Tstruct __257 noattr) 1)) ::
         (Evar _ZERO (tarray (Tstruct __257 noattr) 1)) :: nil))
      (Ssequence
        (Scall None
          (Evar _gf_cpy (Tfunction
                          (Tcons (tptr (Tstruct __257 noattr))
                            (Tcons (tptr (Tstruct __257 noattr)) Tnil)) tvoid
                          cc_default))
          ((Evar _x3 (tarray (Tstruct __257 noattr) 1)) ::
           (Evar _x1 (tarray (Tstruct __257 noattr) 1)) :: nil))
        (Ssequence
          (Scall None
            (Evar _gf_cpy (Tfunction
                            (Tcons (tptr (Tstruct __257 noattr))
                              (Tcons (tptr (Tstruct __257 noattr)) Tnil))
                            tvoid cc_default))
            ((Evar _z3 (tarray (Tstruct __257 noattr) 1)) ::
             (Evar _ONE (tarray (Tstruct __257 noattr) 1)) :: nil))
          (Ssequence
            (Sset _swap (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Ssequence
                (Sset _t
                  (Ebinop Osub (Econst_int (Int.repr 448) tint)
                    (Econst_int (Int.repr 1) tint) tint))
                (Sloop
                  (Ssequence
                    (Sifthenelse (Ebinop Oge (Etempvar _t tint)
                                   (Econst_int (Int.repr 0) tint) tint)
                      Sskip
                      Sbreak)
                    (Ssequence
                      (Ssequence
                        (Sset _t'3
                          (Ederef
                            (Ebinop Oadd (Etempvar _scalar (tptr tuchar))
                              (Ebinop Odiv (Etempvar _t tint)
                                (Econst_int (Int.repr 8) tint) tint)
                              (tptr tuchar)) tuchar))
                        (Sset _sb (Ecast (Etempvar _t'3 tuchar) tuchar)))
                      (Ssequence
                        (Sifthenelse (Ebinop Oeq
                                       (Ebinop Odiv (Etempvar _t tint)
                                         (Econst_int (Int.repr 8) tint) tint)
                                       (Econst_int (Int.repr 0) tint) tint)
                          (Sset _sb
                            (Ecast
                              (Ebinop Oand (Etempvar _sb tuchar)
                                (Econst_int (Int.repr 252) tint) tint)
                              tuchar))
                          (Sifthenelse (Ebinop Oeq
                                         (Ebinop Odiv (Etempvar _t tint)
                                           (Econst_int (Int.repr 8) tint)
                                           tint)
                                         (Ebinop Osub
                                           (Ebinop Odiv
                                             (Econst_int (Int.repr 448) tint)
                                             (Econst_int (Int.repr 8) tint)
                                             tint)
                                           (Econst_int (Int.repr 1) tint)
                                           tint) tint)
                            (Sset _sb
                              (Ecast
                                (Ebinop Oor (Etempvar _sb tuchar)
                                  (Econst_int (Int.repr 128) tint) tint)
                                tuchar))
                            Sskip))
                        (Ssequence
                          (Sset _k_t
                            (Ebinop Oand
                              (Ebinop Oshr (Etempvar _sb tuchar)
                                (Ebinop Omod (Etempvar _t tint)
                                  (Econst_int (Int.repr 8) tint) tint) tint)
                              (Econst_int (Int.repr 1) tint) tint))
                          (Ssequence
                            (Sset _k_t
                              (Eunop Oneg (Etempvar _k_t tuint) tuint))
                            (Ssequence
                              (Sset _swap
                                (Ebinop Oxor (Etempvar _swap tuint)
                                  (Etempvar _k_t tuint) tuint))
                              (Ssequence
                                (Scall None
                                  (Evar _cond_swap (Tfunction
                                                     (Tcons
                                                       (tptr (Tstruct __257 noattr))
                                                       (Tcons
                                                         (tptr (Tstruct __257 noattr))
                                                         (Tcons tuint Tnil)))
                                                     tvoid cc_default))
                                  ((Evar _x2 (tarray (Tstruct __257 noattr) 1)) ::
                                   (Evar _x3 (tarray (Tstruct __257 noattr) 1)) ::
                                   (Etempvar _swap tuint) :: nil))
                                (Ssequence
                                  (Scall None
                                    (Evar _cond_swap (Tfunction
                                                       (Tcons
                                                         (tptr (Tstruct __257 noattr))
                                                         (Tcons
                                                           (tptr (Tstruct __257 noattr))
                                                           (Tcons tuint Tnil)))
                                                       tvoid cc_default))
                                    ((Evar _z2 (tarray (Tstruct __257 noattr) 1)) ::
                                     (Evar _z3 (tarray (Tstruct __257 noattr) 1)) ::
                                     (Etempvar _swap tuint) :: nil))
                                  (Ssequence
                                    (Sset _swap (Etempvar _k_t tuint))
                                    (Ssequence
                                      (Scall None
                                        (Evar _gf_add (Tfunction
                                                        (Tcons
                                                          (tptr (Tstruct __257 noattr))
                                                          (Tcons
                                                            (tptr (Tstruct __257 noattr))
                                                            (Tcons
                                                              (tptr (Tstruct __257 noattr))
                                                              Tnil))) tvoid
                                                        cc_default))
                                        ((Evar _t1 (tarray (Tstruct __257 noattr) 1)) ::
                                         (Evar _x2 (tarray (Tstruct __257 noattr) 1)) ::
                                         (Evar _z2 (tarray (Tstruct __257 noattr) 1)) ::
                                         nil))
                                      (Ssequence
                                        (Scall None
                                          (Evar _gf_sub (Tfunction
                                                          (Tcons
                                                            (tptr (Tstruct __257 noattr))
                                                            (Tcons
                                                              (tptr (Tstruct __257 noattr))
                                                              (Tcons
                                                                (tptr (Tstruct __257 noattr))
                                                                Tnil))) tvoid
                                                          cc_default))
                                          ((Evar _t2 (tarray (Tstruct __257 noattr) 1)) ::
                                           (Evar _x2 (tarray (Tstruct __257 noattr) 1)) ::
                                           (Evar _z2 (tarray (Tstruct __257 noattr) 1)) ::
                                           nil))
                                        (Ssequence
                                          (Scall None
                                            (Evar _gf_sub (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct __257 noattr))
                                                              (Tcons
                                                                (tptr (Tstruct __257 noattr))
                                                                (Tcons
                                                                  (tptr (Tstruct __257 noattr))
                                                                  Tnil)))
                                                            tvoid cc_default))
                                            ((Evar _z2 (tarray (Tstruct __257 noattr) 1)) ::
                                             (Evar _x3 (tarray (Tstruct __257 noattr) 1)) ::
                                             (Evar _z3 (tarray (Tstruct __257 noattr) 1)) ::
                                             nil))
                                          (Ssequence
                                            (Scall None
                                              (Evar _gf_mul (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct __257 noattr))
                                                                (Tcons
                                                                  (tptr (Tstruct __257 noattr))
                                                                  (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    Tnil)))
                                                              tvoid
                                                              cc_default))
                                              ((Evar _x2 (tarray (Tstruct __257 noattr) 1)) ::
                                               (Evar _t1 (tarray (Tstruct __257 noattr) 1)) ::
                                               (Evar _z2 (tarray (Tstruct __257 noattr) 1)) ::
                                               nil))
                                            (Ssequence
                                              (Scall None
                                                (Evar _gf_add (Tfunction
                                                                (Tcons
                                                                  (tptr (Tstruct __257 noattr))
                                                                  (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    Tnil)))
                                                                tvoid
                                                                cc_default))
                                                ((Evar _z2 (tarray (Tstruct __257 noattr) 1)) ::
                                                 (Evar _z3 (tarray (Tstruct __257 noattr) 1)) ::
                                                 (Evar _x3 (tarray (Tstruct __257 noattr) 1)) ::
                                                 nil))
                                              (Ssequence
                                                (Scall None
                                                  (Evar _gf_mul (Tfunction
                                                                  (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    Tnil)))
                                                                  tvoid
                                                                  cc_default))
                                                  ((Evar _x3 (tarray (Tstruct __257 noattr) 1)) ::
                                                   (Evar _t2 (tarray (Tstruct __257 noattr) 1)) ::
                                                   (Evar _z2 (tarray (Tstruct __257 noattr) 1)) ::
                                                   nil))
                                                (Ssequence
                                                  (Scall None
                                                    (Evar _gf_sub (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                    ((Evar _z3 (tarray (Tstruct __257 noattr) 1)) ::
                                                     (Evar _x2 (tarray (Tstruct __257 noattr) 1)) ::
                                                     (Evar _x3 (tarray (Tstruct __257 noattr) 1)) ::
                                                     nil))
                                                  (Ssequence
                                                    (Scall None
                                                      (Evar _gf_mul (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                      ((Evar _z2 (tarray (Tstruct __257 noattr) 1)) ::
                                                       (Evar _z3 (tarray (Tstruct __257 noattr) 1)) ::
                                                       (Evar _z3 (tarray (Tstruct __257 noattr) 1)) ::
                                                       nil))
                                                    (Ssequence
                                                      (Scall None
                                                        (Evar _gf_mul 
                                                        (Tfunction
                                                          (Tcons
                                                            (tptr (Tstruct __257 noattr))
                                                            (Tcons
                                                              (tptr (Tstruct __257 noattr))
                                                              (Tcons
                                                                (tptr (Tstruct __257 noattr))
                                                                Tnil))) tvoid
                                                          cc_default))
                                                        ((Evar _z3 (tarray (Tstruct __257 noattr) 1)) ::
                                                         (Evar _x1 (tarray (Tstruct __257 noattr) 1)) ::
                                                         (Evar _z2 (tarray (Tstruct __257 noattr) 1)) ::
                                                         nil))
                                                      (Ssequence
                                                        (Scall None
                                                          (Evar _gf_add 
                                                          (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct __257 noattr))
                                                              (Tcons
                                                                (tptr (Tstruct __257 noattr))
                                                                (Tcons
                                                                  (tptr (Tstruct __257 noattr))
                                                                  Tnil)))
                                                            tvoid cc_default))
                                                          ((Evar _z2 (tarray (Tstruct __257 noattr) 1)) ::
                                                           (Evar _x2 (tarray (Tstruct __257 noattr) 1)) ::
                                                           (Evar _x3 (tarray (Tstruct __257 noattr) 1)) ::
                                                           nil))
                                                        (Ssequence
                                                          (Scall None
                                                            (Evar _gf_mul 
                                                            (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct __257 noattr))
                                                                (Tcons
                                                                  (tptr (Tstruct __257 noattr))
                                                                  (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    Tnil)))
                                                              tvoid
                                                              cc_default))
                                                            ((Evar _x3 (tarray (Tstruct __257 noattr) 1)) ::
                                                             (Evar _z2 (tarray (Tstruct __257 noattr) 1)) ::
                                                             (Evar _z2 (tarray (Tstruct __257 noattr) 1)) ::
                                                             nil))
                                                          (Ssequence
                                                            (Scall None
                                                              (Evar _gf_mul 
                                                              (Tfunction
                                                                (Tcons
                                                                  (tptr (Tstruct __257 noattr))
                                                                  (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    Tnil)))
                                                                tvoid
                                                                cc_default))
                                                              ((Evar _z2 (tarray (Tstruct __257 noattr) 1)) ::
                                                               (Evar _t1 (tarray (Tstruct __257 noattr) 1)) ::
                                                               (Evar _t1 (tarray (Tstruct __257 noattr) 1)) ::
                                                               nil))
                                                            (Ssequence
                                                              (Scall None
                                                                (Evar _gf_mul 
                                                                (Tfunction
                                                                  (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    Tnil)))
                                                                  tvoid
                                                                  cc_default))
                                                                ((Evar _t1 (tarray (Tstruct __257 noattr) 1)) ::
                                                                 (Evar _t2 (tarray (Tstruct __257 noattr) 1)) ::
                                                                 (Evar _t2 (tarray (Tstruct __257 noattr) 1)) ::
                                                                 nil))
                                                              (Ssequence
                                                                (Scall None
                                                                  (Evar _gf_mul 
                                                                  (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                  ((Evar _x2 (tarray (Tstruct __257 noattr) 1)) ::
                                                                   (Evar _z2 (tarray (Tstruct __257 noattr) 1)) ::
                                                                   (Evar _t1 (tarray (Tstruct __257 noattr) 1)) ::
                                                                   nil))
                                                                (Ssequence
                                                                  (Scall None
                                                                    (Evar _gf_sub 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _t2 (tarray (Tstruct __257 noattr) 1)) ::
                                                                    (Evar _z2 (tarray (Tstruct __257 noattr) 1)) ::
                                                                    (Evar _t1 (tarray (Tstruct __257 noattr) 1)) ::
                                                                    nil))
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'2
                                                                    (Evar _EDWARDS_D tint))
                                                                    (Scall None
                                                                    (Evar _gf_mlw 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    (Tcons
                                                                    tint
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _t1 (tarray (Tstruct __257 noattr) 1)) ::
                                                                    (Evar _t2 (tarray (Tstruct __257 noattr) 1)) ::
                                                                    (Eunop Oneg
                                                                    (Etempvar _t'2 tint)
                                                                    tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _gf_add 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _t1 (tarray (Tstruct __257 noattr) 1)) ::
                                                                    (Evar _t1 (tarray (Tstruct __257 noattr) 1)) ::
                                                                    (Evar _z2 (tarray (Tstruct __257 noattr) 1)) ::
                                                                    nil))
                                                                    (Scall None
                                                                    (Evar _gf_mul 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct __257 noattr))
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _z2 (tarray (Tstruct __257 noattr) 1)) ::
                                                                    (Evar _t2 (tarray (Tstruct __257 noattr) 1)) ::
                                                                    (Evar _t1 (tarray (Tstruct __257 noattr) 1)) ::
                                                                    nil))))))))))))))))))))))))))))
                  (Sset _t
                    (Ebinop Osub (Etempvar _t tint)
                      (Econst_int (Int.repr 1) tint) tint))))
              (Ssequence
                (Scall None
                  (Evar _cond_swap (Tfunction
                                     (Tcons (tptr (Tstruct __257 noattr))
                                       (Tcons (tptr (Tstruct __257 noattr))
                                         (Tcons tuint Tnil))) tvoid
                                     cc_default))
                  ((Evar _x2 (tarray (Tstruct __257 noattr) 1)) ::
                   (Evar _x3 (tarray (Tstruct __257 noattr) 1)) ::
                   (Etempvar _swap tuint) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _cond_swap (Tfunction
                                       (Tcons (tptr (Tstruct __257 noattr))
                                         (Tcons (tptr (Tstruct __257 noattr))
                                           (Tcons tuint Tnil))) tvoid
                                       cc_default))
                    ((Evar _z2 (tarray (Tstruct __257 noattr) 1)) ::
                     (Evar _z3 (tarray (Tstruct __257 noattr) 1)) ::
                     (Etempvar _swap tuint) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _gf_inv (Tfunction
                                      (Tcons (tptr (Tstruct __257 noattr))
                                        (Tcons (tptr (Tstruct __257 noattr))
                                          Tnil)) tvoid cc_default))
                      ((Evar _z2 (tarray (Tstruct __257 noattr) 1)) ::
                       (Evar _z2 (tarray (Tstruct __257 noattr) 1)) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar _gf_mul (Tfunction
                                        (Tcons (tptr (Tstruct __257 noattr))
                                          (Tcons
                                            (tptr (Tstruct __257 noattr))
                                            (Tcons
                                              (tptr (Tstruct __257 noattr))
                                              Tnil))) tvoid cc_default))
                        ((Evar _x1 (tarray (Tstruct __257 noattr) 1)) ::
                         (Evar _x2 (tarray (Tstruct __257 noattr) 1)) ::
                         (Evar _z2 (tarray (Tstruct __257 noattr) 1)) :: nil))
                      (Ssequence
                        (Scall None
                          (Evar _gf_ser (Tfunction
                                          (Tcons (tptr tuchar)
                                            (Tcons
                                              (tptr (Tstruct __257 noattr))
                                              Tnil)) tvoid cc_default))
                          ((Etempvar _out (tptr tuchar)) ::
                           (Evar _x1 (tarray (Tstruct __257 noattr) 1)) ::
                           nil))
                        (Ssequence
                          (Sset _nz (Econst_int (Int.repr 0) tint))
                          (Ssequence
                            (Ssequence
                              (Sset _t (Econst_int (Int.repr 0) tint))
                              (Sloop
                                (Ssequence
                                  (Sifthenelse (Ebinop Olt (Etempvar _t tint)
                                                 (Ebinop Odiv
                                                   (Econst_int (Int.repr 448) tint)
                                                   (Econst_int (Int.repr 8) tint)
                                                   tint) tint)
                                    Sskip
                                    Sbreak)
                                  (Ssequence
                                    (Sset _t'1
                                      (Ederef
                                        (Ebinop Oadd
                                          (Etempvar _out (tptr tuchar))
                                          (Etempvar _t tint) (tptr tuchar))
                                        tuchar))
                                    (Sset _nz
                                      (Ebinop Oor (Etempvar _nz tint)
                                        (Etempvar _t'1 tuchar) tint))))
                                (Sset _t
                                  (Ebinop Oadd (Etempvar _t tint)
                                    (Econst_int (Int.repr 1) tint) tint))))
                            (Ssequence
                              (Sset _nz
                                (Ebinop Oshr
                                  (Ebinop Osub (Etempvar _nz tint)
                                    (Econst_int (Int.repr 1) tint) tint)
                                  (Econst_int (Int.repr 8) tint) tint))
                              (Sreturn (Some (Etempvar _nz tint))))))))))))))))))
|}.

Definition f_x448_base := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr tuchar)) :: (_scalar, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _x448 (Tfunction
                  (Tcons (tptr tuchar)
                    (Tcons (tptr tuchar) (Tcons (tptr tuchar) Tnil))) tint
                  cc_default))
    ((Etempvar _out (tptr tuchar)) :: (Etempvar _scalar (tptr tuchar)) ::
     (Evar _X448_BASE_POINT (tarray tuchar 56)) :: nil))
  (Sreturn (Some (Etempvar _t'1 tint))))
|}.

Definition composites : list composite_definition :=
(Composite __257 Struct ((_limb, (tarray tuint 16)) :: nil) noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Tsingle :: nil) AST.Tsingle cc_default))
     (Tcons tfloat Tnil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tulong (Tcons tulong Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons (tptr tvoid) (Tcons tulong Tnil))
     (tptr tvoid) cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tint Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tlong :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_X448_BASE_POINT, Gvar v_X448_BASE_POINT) :: (_ZERO, Gvar v_ZERO) ::
 (_ONE, Gvar v_ONE) :: (_P, Gvar v_P) :: (_EDWARDS_D, Gvar v_EDWARDS_D) ::
 (_gf_cpy, Gfun(Internal f_gf_cpy)) :: (_gf_mul, Gfun(Internal f_gf_mul)) ::
 (_gf_isqrt, Gfun(Internal f_gf_isqrt)) ::
 (_gf_inv, Gfun(Internal f_gf_inv)) ::
 (_gf_reduce, Gfun(Internal f_gf_reduce)) ::
 (_gf_add, Gfun(Internal f_gf_add)) :: (_gf_sub, Gfun(Internal f_gf_sub)) ::
 (_cond_swap, Gfun(Internal f_cond_swap)) ::
 (_gf_mlw, Gfun(Internal f_gf_mlw)) ::
 (_gf_canon, Gfun(Internal f_gf_canon)) ::
 (_gf_deser, Gfun(Internal f_gf_deser)) ::
 (_gf_ser, Gfun(Internal f_gf_ser)) :: (_x448, Gfun(Internal f_x448)) ::
 (_x448_base, Gfun(Internal f_x448_base)) :: nil).

Definition public_idents : list ident :=
(_x448_base :: _x448 :: _X448_BASE_POINT :: ___builtin_debug ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___compcert_i64_umulh :: ___compcert_i64_smulh :: ___compcert_i64_sar ::
 ___compcert_i64_shr :: ___compcert_i64_shl :: ___compcert_i64_umod ::
 ___compcert_i64_smod :: ___compcert_i64_udiv :: ___compcert_i64_sdiv ::
 ___compcert_i64_utof :: ___compcert_i64_stof :: ___compcert_i64_utod ::
 ___compcert_i64_stod :: ___compcert_i64_dtou :: ___compcert_i64_dtos ::
 ___builtin_expect :: ___builtin_unreachable :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


