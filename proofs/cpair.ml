let c_pair_DEF = define `c_pair x y = ((x+y)*(x+y+1)) DIV 2 + x`;;

let c_pair_LEMMA = prove
 (`a + b < c + d ==> c_pair a b < c_pair c d`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC (ARITH_RULE `x < c_pair 0 (a+b+1) /\ c_pair 0 (a+b+1) <= c_pair 0 (c+d) /\ c_pair 0 (c+d) <= y ==> x < y`) THEN
  REWRITE_TAC [c_pair_DEF; ADD_0] THEN REPEAT CONJ_TAC THEN TRY (MATCH_MP_TAC DIV_MONO THEN MATCH_MP_TAC LE_MULT2) THEN ASM_ARITH_TAC);;

let c_pair_INJ = prove
 (`c_pair a b = c_pair c d ==> a = c /\ b = d`,
  ASM_CASES_TAC `a + b = c + d` THENL
   [ASM_REWRITE_TAC[c_pair_DEF;ADD_ASSOC;EQ_ADD_LCANCEL] THEN ASM_METIS_TAC[EQ_ADD_LCANCEL];
    ASM_METIS_TAC[LT_REFL; LT_CASES; c_pair_LEMMA]]);;

let c_pair_SURJ = prove
 (`!x. ?a b. c_pair a b = x`,
 MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
  [REPEAT (EXISTS_TAC `0`) THEN REWRITE_TAC[c_pair_DEF;ADD_CLAUSES;MULT_CLAUSES;DIV_0];
   GEN_TAC THEN DISCH_THEN(DESTRUCT_TAC "@a. @b. op") THEN DESTRUCT_TAC "beq0 | @pb. bp1" (SPEC `b:num` (cases "num")) THENL
    [EXISTS_TAC `0` THEN EXISTS_TAC `a+1`; EXISTS_TAC `a+1` THEN EXISTS_TAC `pb:num`] THEN
    REMOVE_THEN "op" MP_TAC THEN ASM_REWRITE_TAC [c_pair_DEF] THEN ASM_ARITH_TAC]);;

let c_pair_CAR_CDR = new_specification ["c_car"; "c_cdr"] (REWRITE_RULE [SKOLEM_THM] c_pair_SURJ) ;;

