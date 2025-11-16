(* hol-light usage notes

   still underusing directed conversions, implicational and target rewriting,
   custom tactics, simpsets, user parsers/printers

   parsing: , ; brackets are special

   study drule/impconv more *)

(* subst a large term into the body of an abs is slow since it needs to be checked for bound variables; possibly exponential nested alpha, def linear *)
(* comparing pointer identical terms is fast; at worst linear if no alpha convert *)
(* assumption lists are linear *)
(* substitution always linear in template, except when alpha converting *)
(* once_depth: try root, try children once if failed *)
(* depth: exhaust children then root *)
(* redepth: recurse, try root once, repeat *)
(* top_depth: exhaust, recurse, alternate trying root once and recursing *)
(* top_sweep: exhaust then recurse *)
(* definition sizes irrelevant, definitions list not used by core; too many (hundreds) of constants will slow down parsing *)

(* known variants and proof consequences (2025-11-02)

   andrew-j-wade/compiler-optimizations: 8097701
     f2aee peephole two dispatchroots?, TODO
     01815 combining semi-states, handled(nonuniqueness)
     80977 initialization phase uses a BB machine, handled(cruft)
   andrew-j-wade/master: 92375ea
     cf386 alignment in transfer, handled(noop removal)
     b371d no dedicated entry, handled(init-phase)
     5d676 alignment changes, handled(noop removal)
   andrew-j-wade/DET-typo-fix: 807332b
     80733 cherry-picked
   andrew-j-wade/patch-2: 8ce2367 (on CatsAreFluffy/master)
     8ce23 rearranges cases for consistency, logic only, TODO
   CatsAreFluffy/master: 74a0e04
     printing changes
     distingish size from alignment, handled(noop removal)
     many loader things and handling scripts, irrelevant
     temporary and expression changes, handled
     added decz primitive, handled
     various logic
     misc logic changes, handleable, TODO

   ajwade/turing_machine_explorer/master: d3a9e07
     very different, proof seems to be adaptable
     inc and regselect logic are the same, dec has the same recursive structure
     but a different base case leading to different return values
     dispatch tree is variable height but that was allowed for
     single dispatch root, simpler in that way than advanced fixed-height TMs
     control flow leading to dispatch root is completely different using break
     and continue operators but fits naturally into the subroutine model

     particular difficulty is the handling of the -1 register, in particular
     the moving left edge of the register file and the fact that every register
     operation is dispatched twice. we can probably make it work by
     complicating the description of interface states

     boot is more annoying than difficult, 2133492, 61009974 step eval process,
     may need to leverage structure, most of boot1 is collatzy 2-cycles, boot2
     is pseudo-dispatch
   *)

(* preliminaries - function and list handling *)

override_interface("::",`CONS:A->A list->A list`);;
parse_as_infix("::",(13,"right"));;
override_interface("++",`APPEND:A list->A list->A list`);;
parse_as_infix("++",(13,"right"));;
unspaced_binops := "::" :: !unspaced_binops;;

let NUM_OF_INT_2 = prove(`&0 <= x ==> ?z. x:int = &z`, REWRITE_TAC[EXISTS_THM;NUM_OF_INT;num_of_int] THEN MESON_TAC[]);;

let ITERF_DEF = define`ITERF 0 f (x:A) = x /\ ITERF (SUC n) f x = f (ITERF n f x)`;;
let ITERF_ADD = prove(`!m n f (x:A). ITERF (m + n) f x = ITERF m f (ITERF n f x)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES;ITERF_DEF]);;

let TAKE_DEF = define`TAKE 0 (l:A list) = [] /\
  TAKE (SUC i) l = HD l :: TAKE i (TL l)`;;
let DROP_DEF = define`DROP 0 (l:A list) = l /\
  DROP (SUC i) l = DROP i (TL l:A list)`;;

let LENGTH_TAKE = prove(`!i l. LENGTH (TAKE i l:A list) = i`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[TAKE_DEF;LENGTH]);;
let LENGTH_DROP = prove(
 `!i (l:A list). i <= LENGTH l ==> LENGTH (DROP i l) = LENGTH l - i`,
  INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[DROP_DEF; LENGTH; SUB_0; TL; LE_SUC; SUB_SUC; LE; NOT_SUC]);;

let EL_TAKE = prove(`!i j l. i < j ==> EL i (TAKE j l) = (EL i l:A)`,
  REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC[TAKE_DEF; EL; HD; TL; LT_SUC; LT]);;
let EL_DROP = prove(`!j l. EL i (DROP j l) = EL (i + j) (l:A list)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[DROP_DEF;ADD_CLAUSES;EL]);;

let TAKE_DROP = prove(
 `!i (l:A list). i <= LENGTH l ==> TAKE i l ++ DROP i l = l`,
  INDUCT_TAC THEN LIST_INDUCT_TAC THEN ASM_SIMP_TAC[TAKE_DEF; DROP_DEF; APPEND;
    LENGTH; LE_SUC; LE; NOT_SUC; HD; TL]);;

let TAKE_APPEND_EQ = prove(`!a b. TAKE (LENGTH (a:A list)) (a ++ b) = a`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH; TAKE_DEF; APPEND; HD; TL]);;

let DROP_APPEND_GE = prove(
 `!x a b. LENGTH a <= x ==> DROP x (a:A list ++ b) = DROP (x - LENGTH a) b`,
  INDUCT_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[DROP_DEF; APPEND; LENGTH;
    SUB; LE_SUC; SUB_PRESUC; TL] THEN REWRITE_TAC[LE; NOT_SUC]);;

let list_2INDUCT = prove(
 `!(P:A list -> bool). P [] /\ (!a0. P [a0]) /\ (!a0 a1 l.
        P (a1::l) /\ P l ==> P (a0::a1::l)) ==> !l. P l`,
  INTRO_TAC "!P; i0 i1 i2; !l" THEN WF_INDUCT_TAC `LENGTH (l:A list)` THEN
  POP_ASSUM MP_TAC THEN
  STRUCT_CASES_TAC (SPEC_ALL list_CASES) THEN ASM_REWRITE_TAC[] THEN
  STRUCT_CASES_TAC (SPEC `t:A list` list_CASES) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN USE_THEN "i2" MATCH_MP_TAC THEN CONJ_TAC THEN
  POP_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[LENGTH] THEN ARITH_TAC);;

(* preliminaries - fast maps

   hol-light's built in definition by cases is far, far too slow to handle our
   transition table

   maps are typed as functions, but have a recursive representation that allows
   logarithmic time evaluation without alpha conversion. the base concept is
   similar to sptree from HOL4, but simplified for our use case

   imprecise = few guarantees on value outside provided alist. a precise mode
   is possible but requires ~twice the term nodes

   todo: actual definition primitive, maybe a conv-generator *)

let nmap_node_DEF = define`NMAP_NODE l r = \i. (if ODD i then r else l) (i DIV 2):A` ;;
let nmap_leaf_DEF = define`NMAP_LEAF v f = \i. if i = 0 then v else f:A` ;;

let nmap_CLAUSES = prove(
  `NMAP_NODE l r (NUMERAL i) = (NMAP_NODE l r i):A /\ NMAP_NODE l r _0 = l _0 /\ NMAP_NODE l r (BIT0 i) = l i /\ NMAP_NODE l r (BIT1 i) = r i /\
   NMAP_LEAF v f _0 = v /\ NMAP_LEAF v f (NUMERAL i) = (NMAP_LEAF v f i):A /\ NMAP_LEAF v f (BIT0 i) = NMAP_LEAF v f i /\ NMAP_LEAF v f (BIT1 i) = f`,
  REWRITE_TAC[NUMERAL;BIT0;BIT1] THEN SUBST1_TAC (SYM (SPEC `_0` NUMERAL)) THEN
  REWRITE_TAC[nmap_node_DEF;nmap_leaf_DEF;DIV_0;ODD;ODD_ADD;NOT_SUC;ARITH_RULE `(i+i)DIV 2=i/\SUC(i+i)DIV 2=i/\(i+i=0 <=> i=0)`]);;

let UNBIT01 = prove(`~ODD (BIT0 i) /\ BIT0 i DIV 2 = i /\ ODD (BIT1 i) /\ BIT1 i DIV 2 = i`,
  CONV_TAC(SUBS_CONV [SPEC `i:num` BIT0; SPEC `i:num` BIT1]) THEN REWRITE_TAC[ODD;ODD_ADD] THEN ARITH_TAC);;

let nmap_FORALL = prove(
 `((\m. !i. P (m i:A)) (NMAP_NODE x y) <=> (\m. !i. P (m i)) x /\ (\m. !i. P (m i)) y) /\ ((\m. !i. P (m i)) (NMAP_LEAF a b) <=> P a /\ P b)`,
  (CONJ_TAC THEN EQ_TAC THEN SIMP_TAC[nmap_node_DEF;nmap_leaf_DEF;COND_RAND;COND_RATOR;COND_ID] THEN REPEAT STRIP_TAC) THENL
    (List.map (fun t -> POP_ASSUM (MP_TAC o SPEC t)) [`BIT0 i`;`BIT1 i`;`0`;`1`]) THEN REWRITE_TAC[UNBIT01;ARITH_EQ]);;

let mk_nmap_imprecise def =
  let leaf = mk_const("NMAP_LEAF",[type_of def,aty]) in
  let node = mk_const("NMAP_NODE",[type_of def,aty]) in
  let rec mk_nmap pairs = match pairs with
      [] -> mk_binop leaf def def
    | [0,tm1] -> mk_binop leaf tm1 def
    | [_,tm1] -> mk_binop leaf def tm1
    | [0,tm1;_,tm2] -> mk_binop leaf tm1 tm2
    | [_,tm1;0,tm2] -> mk_binop leaf tm2 tm1
    | _ -> let submap m = (mk_nmap Option.(List.filter_map (fun (i,tm) -> if i mod 2 == m then some (i/2, tm) else none) pairs)) in
            mk_binop node (submap 0) (submap 1)
    in mk_nmap ;;

let bmap_DEF = define`BMAP f t c = if c then t else f:A` ;;
let bmap_CLAUSES = prove(`BMAP f t F = f:A /\ BMAP f t T = t`, REWRITE_TAC[bmap_DEF]) ;;
let bmap_EXPAND = prove(`c = BMAP f t <=> c F = f /\ c T = (t:A)`,
  REWRITE_TAC[FUN_EQ_THM; bmap_DEF; FORALL_BOOL_THM; CONJ_SYM]);;
let bmap_FORALL = prove(`(\m. !b. P (m b:A)) (BMAP f t) <=> P f /\ P t`, REWRITE_TAC[bmap_DEF;COND_RAND;FORALL_BOOL_THM;CONJ_SYM]);;

let mk_bmap f t = mk_binop (mk_const("BMAP",[type_of f,aty])) f t ;;

(* definition of a general TM

   we do everything concretely, but want to be able to present an existential
   theorem later "there is an <X> state TM that does <Y>"

   head positions are implicit, we limit to a single tape and 2 symbols, states
   are num indexed (to avoid type variables in the sequel), the transition
   table takes the current state and symbol and produces the new state,
   movement direction, and new symbol.

   being halted is considered an update and associated with state 0 for
   totality reasons, valid TMs will not leave state 0. similarly, the initial
   state is always 1 *)

let gtm_valid_DEF = define`gtm_valid (tt:num->bool->num#bool#bool) st <=> ~(st = 0) /\ !b. FST(tt 0 b) = 0 /\ !i. i <= st ==> FST (tt i b) <= st` ;;
let tape_shift_DEF = define`shift i (tp:int->bool) = \j. tp (i+j)`;;
let tape_write_DEF = define`write v (tp:int->bool) = \i. if i = &0 then v else tp i`;;
let initial_DEF = define`initial = 1,\(i:int).F`;;
let halted_DEF = define`halted = 0,\(i:int).F`;;
let gtm_step_DEF = define`gtm_step tt (st:num,t) = let ns,m,w = tt st (t (&0)) in if ns=0 then halted else ns,shift (if m then &1 else -- &1) (write w t)` ;;

(* loading and parsing .tm files emitted by nqlaconic

   state_info is a list of (name,when symbol 0,when symbol 1) with behaviors
   represented as transition table values. name_to_state is also important and
   will drive most proving *)

let tm_lines = strings_of_file "../machines/2017-zf-sorear-748/zf2.tm" ;;
let fix_state_name name = match name with
  | "transfer(_Gnextproof,_scratch_1,_scratch_2)[01]" -> "reg_incr.2"
  | nn -> nn ;;
let tm_states_tok = map (map fix_state_name) (map (String.split_on_char ' ') ("HALT = 0 L HALT 0 L HALT" :: tm_lines)) ;;
let state_of_name n = index n (map hd tm_states_tok) ;;
let name_of_state s = hd (el s tm_states_tok) ;;
let toks_to_state_info [name;_;w0;m0;ns0;w1;m1;ns1] =
 (name,(state_of_name ns0,m0="R",w0="1"),(state_of_name ns1,m1="R",w1="1")) ;;
let state_info = map toks_to_state_info tm_states_tok ;;

let mk_bool = let T = `T` and F = `F` in fun b -> if b then T else F ;;

(* construct and prove validity of loaded transition table *)

let transition_table_DEF =
  let triple (ns,m,w) = mk_pair(mk_small_numeral ns, mk_pair(mk_bool m, mk_bool w)) in
  let table = mk_nmap_imprecise `BMAP (0,F,F) (0,F,F)` (List.mapi (fun i (_,t0,t1) -> i, mk_bmap (triple t0) (triple t1)) state_info) in
  new_basic_definition (mk_eq(`transition_table:num->bool->num#bool#bool`, table)) ;;

let transition_table_LIMIT = CONV_RULE (SIMP_CONV[]) ((PURE_REWRITE_CONV [transition_table_DEF;nmap_FORALL;bmap_FORALL;FST] THENC SIMP_CONV[ARITH_LE;ARITH_LT;EQ_CLAUSES])
  `(\m. !i. (\n. !b. FST (n b) <= 748) (m i)) transition_table`);;

let transition_table_VALID = prove(`gtm_valid transition_table 748`, REWRITE_TAC[gtm_valid_DEF;transition_table_LIMIT;FORALL_BOOL_THM;transition_table_DEF;nmap_CLAUSES;bmap_CLAUSES;ARITH_EQ]);;

    (* 200 times faster than REWRITE_CONV on a ground term *)
let transition_table_CONV = GEN_REWRITE_CONV DEPTH_CONV [transition_table_DEF;nmap_CLAUSES;bmap_CLAUSES];;

(* tape handling

   for the register and dispatch logic, we represent the tape at the bit level,
   since updates do not pass through intermediate states that are meaningful at
   higher levels. we also support "cruft" in ignored portions of the tape,
   because ajwade's machines use an unclean initialization process.

   the initialization process itself does not have to be modeled since it
   halts, but we need a calculation-friendly tape representation

   this whole thing is incredibly circuitous for something that could have been
   a definition. the two-sided zipper is almost certainly the interface we want
   downstream, although the lists could be replaced with colists (wrapper
   around num->bool) if the appropriate utilities existed (mostly, a version of
   APPEND :A list -> (num -> A) -> num -> A). we could adopt the two-sided
   zipper as a definition, or a symmetric zipper, or perhaps introduce colists
   as an intermediate stage *)

prioritize_int();;
let list_tape_DEF = define `list_tape l tp = \i. &0 <= tp+i /\ tp+i < &(LENGTH l) /\ EL (num_of_int (tp+i)) l`;;

let list_tape_SHIFT = prove(`shift j (list_tape l tp) = list_tape l (tp+j)`, SIMP_TAC[tape_shift_DEF;list_tape_DEF;INT_ADD_ASSOC]);;

let list_tape_RAPPEND = prove(
 `list_tape (APPEND l [F]) tp = list_tape l tp`,
  REWRITE_TAC[list_tape_DEF] THEN ABS_TAC THEN ASM_CASES_TAC `&0 <= tp+i` THEN ASM_SIMP_TAC[] THEN
  POP_ASSUM (DESTRUCT_TAC "@j. eq" o MATCH_MP NUM_OF_INT_2) THEN POP_ASSUM SUBST1_TAC THEN
  EQ_TAC THEN SIMP_TAC[NUM_OF_INT_OF_NUM;INT_OF_NUM_LT;LENGTH_APPEND;LENGTH;EL_APPEND;ADD_CLAUSES;LT] THEN
  INTRO_TAC "(lt|eq) el" THEN USE_THEN "el" (UNDISCH_TAC o concl) THEN ASM_SIMP_TAC[SUB_REFL;LT_REFL;EL;HD]);;

let list_tape_LAPPEND = prove(
 `list_tape (APPEND [F] l) (tp + &1) = list_tape l tp`,
  SIMP_TAC[list_tape_DEF; LENGTH; APPEND; INT_ADD_AC] THEN ABS_TAC THEN
  SIMP_TAC[INT_ADD_ASSOC] THEN ASM_CASES_TAC `&0 <= i + tp` THENL [
   POP_ASSUM (DESTRUCT_TAC "@j. eq" o MATCH_MP NUM_OF_INT_2) THEN ASM_SIMP_TAC[
     INT_OF_NUM_CLAUSES; GSYM ADD1; LT_SUC; NUM_OF_INT_OF_NUM; EL; TL; LE_0];
     ASM_CASES_TAC `i + tp = -- &1` THENL[
       ASM_SIMP_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN
       SIMP_TAC[EL; NUM_OF_INT_OF_NUM; HD]; ASM_ARITH_TAC]]);;

let list_tape_WRITE = prove(
 `tp < LENGTH l ==> write b (list_tape l (&tp)) =
      list_tape (TAKE tp l ++ b :: DROP (SUC tp) l) (&tp)`,
 SIMP_TAC[tape_write_DEF; list_tape_DEF] THEN DISCH_TAC THEN ABS_TAC THEN
 ASM_CASES_TAC `&0 <= &tp + i` THENL [
   POP_ASSUM (DESTRUCT_TAC "@j. eq" o MATCH_MP NUM_OF_INT_2) THEN
   SUBGOAL_TAC "i" `i = &0 <=> (j:num) = tp` [ASM_ARITH_TAC] THEN
   SUBGOAL_TAC "as" `tp + SUC (LENGTH l - SUC tp) = LENGTH (l:bool list)` [ASM_ARITH_TAC] THEN
   ASM_SIMP_TAC[LENGTH_APPEND; LENGTH; LENGTH_DROP; LE_SUC_LT; EL_APPEND;
     LENGTH_TAKE; INT_OF_NUM_CLAUSES; NUM_OF_INT_OF_NUM; LE_0] THEN
   STRUCT_CASES_TAC (SPECL [`j:num`;`tp:num`] LT_CASES) THEN
   ASM_SIMP_TAC[LT_IMP_NE; EL_TAKE; EL_DROP; SUB_REFL; LT_REFL; EL; HD; EL_CONS;
     SUB_EQ_0; LE_REFL; GSYM NOT_LT] THEN
   SUBGOAL_TAC  "tp < j ==> j" `j - tp - 1 + SUC tp = j /\ ~(j < tp)` [ASM_ARITH_TAC] THEN
   ASM_REWRITE_TAC[];
   COND_CASES_TAC THEN ASM_ARITH_TAC]);;

let lzip_tape = define`lzip_tape ls rs =
        list_tape (REVERSE ls ++ rs) (&(LENGTH ls) - &1)`;;
let rzip_tape = define`rzip_tape ls rs =
        list_tape (REVERSE ls ++ rs) (&(LENGTH ls))`;;
let zip_shift = prove(
 `shift (-- &1) (lzip_tape (l :: ls) rs) = lzip_tape ls (l :: rs) /\
  shift    (&1) (rzip_tape ls (r :: rs)) = rzip_tape (r :: ls) rs /\
  shift (-- &1) (rzip_tape ls rs) = lzip_tape ls rs /\
  shift    (&1) (lzip_tape ls rs) = rzip_tape ls rs`,
  SIMP_TAC[lzip_tape; rzip_tape; list_tape_SHIFT; REVERSE; GSYM APPEND_ASSOC;
    LENGTH; APPEND] THEN REPEAT CONJ_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let zip_write = prove(
 `write b (lzip_tape (l::ls) rs) = lzip_tape (b::ls) rs /\
  write b (rzip_tape ls (r::rs)) = rzip_tape ls (b::rs)`,
  SIMP_TAC[lzip_tape; rzip_tape] THEN
  IMP_REWRITE_TAC[INT_OF_NUM_SUB; list_tape_WRITE] THEN
  SIMP_TAC[LENGTH; ADD1; LE_ADD; LE_ADDR; LENGTH_APPEND; ADD_SUB; REVERSE;
  GSYM APPEND_ASSOC; GSYM ADD_ASSOC; LT_ADD; APPEND] THEN
  CONJ_TAC THEN TARGET_REWRITE_TAC [GSYM LENGTH_REVERSE] TAKE_APPEND_EQ THEN
  IMP_REWRITE_TAC[DROP_APPEND_GE; TAKE_APPEND_EQ] THEN
  SIMP_TAC[LENGTH_REVERSE; LE_ADDR; LE_ADD; ADD_SUB2; LT_ADD] THEN
  SIMP_TAC[ONE; DROP_DEF; TL; ADD_CLAUSES; LT_0]);;

let zip_extend = prove(
  `lzip_tape [] rs = lzip_tape [F] rs /\ rzip_tape ls [] = rzip_tape ls [F]`,
  SIMP_TAC[lzip_tape;rzip_tape;REVERSE;LENGTH;APPEND;SYM ONE;
    list_tape_RAPPEND;APPEND_NIL] THEN
  MP_TAC(SPECL[`rs:bool list`;`--(&1)`] (GEN_ALL list_tape_LAPPEND)) THEN
  CONV_TAC INT_REDUCE_CONV THEN SIMP_TAC[APPEND]);;

let zip_extend' = prove(
  `rzip_tape ls rs = rzip_tape ls (rs ++ [F])`,
  SIMP_TAC[rzip_tape;list_tape_RAPPEND;APPEND_ASSOC]);;

let zip_read = prove(
  `lzip_tape (CONS l ls) rs (&0) = l /\ rzip_tape ls (CONS r rs) (&0) = r`,
  REWRITE_TAC[lzip_tape; rzip_tape; list_tape_DEF; LENGTH; LENGTH_APPEND;
    REVERSE; GSYM APPEND_ASSOC; APPEND; ADD1; INT_ADD_RID;
    GSYM INT_OF_NUM_CLAUSES; ARITH_RULE `(x+y)-y=x`] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; NUM_OF_INT_OF_NUM; LE_0; ADD;
    LENGTH_REVERSE; EL_APPEND; LT_REFL; SUB_REFL; EL; HD; ADD_AC;
    ARITH_RULE `x < x + y + 1`]);;

let zip_init = prove(`initial = 1,rzip_tape [] []`,
  REWRITE_TAC[initial_DEF; PAIR_EQ; FUN_EQ_THM; rzip_tape; list_tape_DEF;
   LENGTH; REVERSE; APPEND] THEN ARITH_TAC);;

prioritize_num();;

(* semantics

   we start with a small-step semantics on "worldstates" (turing state, tape
   pairs). this is not quite standard because it is irreflexive; this will
   facilitate proofs of nontermination later, and can be used for a rough lower
   bound on execution time, but no attempt is made to measure execution time
   precisely

   big step would make proofs easier since HOL's native equational reasoning
   applies, but it appears unable to prove any useful property of
   nonterminating programs. maybe if we had a beep state and coinductive
   semantics? try to achieve the same end with a "transitive simplification"
   tactic

   extend to a small-step semantics on "classes" (sets of worldstates); this
   roughly matches Hoare triples but always terminates and the operations
   performed are implicit in the states

   reflexive small-step may be an option if we bounce between two disjoint sets
   to prove non-termination, could also be expressed by having progressing and
   non-progressing relations, a fourth option would be to extend the
   completeness proof to prove that a register increases without bound while a
   turing machine that halts will do so after finitely many writes *)

let _ = parse_as_infix("-->_w",(12,"right"));;
let tm_evolves = define`w1 -->_w w2 <=>
   ?n. ITERF (SUC n) (gtm_step transition_table) w1 = w2`;;

let tm_evolves_TRANS = prove(`w1 -->_w w2 /\ w2 -->_w w3 ==> w1 -->_w w3`,
  REWRITE_TAC[tm_evolves] THEN INTRO_TAC "(@n1. im1) (@n2. im2)" THEN
  EXISTS_TAC `n2 + SUC n1` THEN ASM_REWRITE_TAC[GSYM ADD; ITERF_ADD]);;

let tm_evolves_BASE = prove(
 `gtm_step transition_table w1 = w2 ==> w1 -->_w w2`,
 DISCH_TAC THEN REWRITE_TAC[tm_evolves] THEN EXISTS_TAC `0` THEN
 ASM_REWRITE_TAC[ITERF_DEF]);;

  (* st, b must be literals *)
let BEHAVIOR =
  let cv = REWRITE_CONV[gtm_step_DEF;zip_read] THENC
    transition_table_CONV THENC let_CONV THENC NUM_REDUCE_CONV THENC
    REWRITE_CONV[zip_write; zip_shift] in
  let tm = `gtm_step transition_table (st,lzip_tape (b :: ls) rs),
            gtm_step transition_table (st,rzip_tape ls (b :: rs))` in
  fun st b ->
    let tm' = (vsubst [st,`st:num`;b,`b:bool`] tm) in
    CONJ (MATCH_MP tm_evolves_BASE (cv (lhand tm')))
         (MATCH_MP tm_evolves_BASE (cv (rand tm'))) ;;

let HALTED_STICKY1 = EQT_ELIM ((REWRITE_CONV[halted_DEF; gtm_step_DEF] THENC
    transition_table_CONV THENC LAND_CONV let_CONV THENC
    REWRITE_CONV[]) `gtm_step transition_table halted = halted`);;
let HALTED_STICKY = MATCH_MP tm_evolves_BASE HALTED_STICKY1;;

(* naming TM states

   we don't want to name every state, partly for performance but mostly because
   the names are only useful in hand-written proofs. the various dispatch tree
   states will remain nameless, known only by their behavior

   it remains to be seen how we handle variance between tm versions. there are
   only two basic versions of the register machine but some of them have
   optimizations, dec_check, dec_restore, dec_scan_done are half states, !ENTRY
   is unneeded, etc, as well as yucky issues with name collapsing

   todo: generalize bmap-based definition mechanism
   todo: custom parse for tm states *)

let nmap_EXPAND limit th =
  let rec iter i = if i >= limit then [] else
    CONV_RULE (GEN_REWRITE_CONV TOP_SWEEP_CONV [nmap_CLAUSES])
      (AP_THM th (mk_small_numeral i))::iter (i+1) in
  end_itlist CONJ (iter 0) ;;

let NAMED_STATES =
  let nn = mk_small_numeral o state_of_name in
  let defs1 tmn stn _ = new_basic_definition(
    mk_eq(mk_var(tmn,`:num`),nn stn)) in
  let defs2 tmn s0 s1 _ = new_basic_definition(
    mk_eq(mk_var(tmn,`:bool->num`),mk_bmap (nn s0) (nn s1))) in
  let defs4 tmn s0 s1 s2 s3 _ = new_basic_definition(
    mk_eq(mk_var(tmn,`:bool->bool->num`),
      mk_bmap (mk_bmap (nn s0) (nn s1)) (mk_bmap (nn s2) (nn s3)))) in
  let defsn tmn sp _ =
    let rec states n =
      try let s = nn (sp ^ string_of_int n) in (n,s)::states (n+1)
      with Failure _ -> [] in
    let stn = states 0 in
    nmap_EXPAND (length stn) (new_basic_definition(
            mk_eq(mk_var(tmn,`:num->num`),mk_nmap_imprecise `0` stn))) in
  let clauses = [
    defs1 "dec_init" "dec.init"; defs1 "dec_check" "dec.check";
    defs1 "dec_restore" "dec.restore"; defs1 "dec_scan_done" "dec.scan_done";
    defs2 "dec_scan" "dec.scan_0" "dec.scan_1";
    defs2 "dec_shift" "dec.shift_0" "dec.shift_1";
    defs2 "inc_shift" "inc.shift_0" "inc.shift_1";
    defs4 "return" "return.0" "return.1" "return2.0" "return2.1";
    defs2 "nextstate" "dispatch.0.carry" "nextstate_2";
    defs1 "dispatchroot" "main()[]";
    defs1 "init_f1" "init.f1"; defs1 "init_f2" "init.f2";
    defs2 "init_scan" "init.scan_0" "init.scan_1";
    defs1 "reg_incr_last" "reg_incr.-1"; defs1 "reg_decr_last" "reg_decr.-1";
    defsn "reg_incr" "reg_incr."; defsn "reg_decr" "reg_decr."] in
  let conjs = end_itlist CONJ (mapfilter (fun c -> c ()) clauses) in
  CONV_RULE (REWRITE_CONV [bmap_EXPAND; CONJ_ACI]) conjs ;;

let NAMED_BEHAVIOR =
  CONV_RULE (REWRITE_CONV [GSYM NAMED_STATES]) (end_itlist CONJ
    (map (fun e -> CONJ (BEHAVIOR (rhs e) `F`) (BEHAVIOR (rhs e) `T`))
         (conjuncts (concl NAMED_STATES))));;

let GMATCH_MP' f v = let vars,_ = strip_forall (concl v) in
  GENL vars (MATCH_MP f (SPEC_ALL v)) ;;
let EVOLVE_TO_IMP = MATCH_MP (TAUT `((a /\ b) ==> c) ==> a ==> (b ==> c = T)`) tm_evolves_TRANS;;
let NAMED_BEHAVIOR_IMP =
   CONJ NAMED_BEHAVIOR (end_itlist CONJ (map (MATCH_MP EVOLVE_TO_IMP)
     (CONJUNCTS (CONV_RULE (REWRITE_CONV [CONJ_ACI]) NAMED_BEHAVIOR))));;

(* register operations

   start by proving single steps, use induction to build the inner loops, then
   inductively construct the behavior of primitive register operations at the
   dispatch/register interface boundary

   initial attempts to prove this used a "pseudo big step" approach where all
   states were proven to evolve to the nextstate interface; this made use of
   implicational rewriting but had poor modularity and required heavy use of
   REVERSE; current approach does two-sided recursion to avoid reverses *)

let REG = define`REG n xs = APPEND (REPLICATE (SUC n) T) (F :: xs)`;;
let REGFILE = define `REGFILE ns = ITLIST REG ns []`;;
let OPSEG = define`OPSEG ns cruft = F :: F :: REGFILE ns ++ cruft`;;
let (REGLIKE, REGLIKE_IND, REGLIKE_CASES) = new_inductive_definition
 `REGLIKE F [] /\
  (!x b bs. REGLIKE b bs /\ (b \/ x) ==> REGLIKE x (b :: bs))`;;

let REGFILE_CLAUSES = prove(
 `REGFILE [] = [] /\ REGFILE (n::ns) = REPLICATE (SUC n) T ++ F :: REGFILE ns`,
  REWRITE_TAC[REGFILE; ITLIST; REG]);;

let IS_REGLIKE = prove(
 `!ns. REGLIKE F (REGFILE ns)`,
 REWRITE_TAC[REGFILE] THEN LIST_INDUCT_TAC THEN
 IMP_REWRITE_TAC[ITLIST; REG; REPLICATE; APPEND; REGLIKE] THEN
 SPEC_TAC(`h:num`,`h:num`) THEN INDUCT_TAC THEN
 (ASM IMP_REWRITE_TAC)[REPLICATE; APPEND; REGLIKE]);;

let IS_REGLIKE_PARTIAL = prove(
 `!n. REGLIKE T (REPLICATE n T ++ F::REGFILE ns)`,
 INDUCT_TAC THEN IMP_REWRITE_TAC[REPLICATE; APPEND; REGLIKE; IS_REGLIKE]);;

let IS_REGLIKE_T = prove(
 `REGLIKE T (REGFILE (n::ns))`,
 IMP_REWRITE_TAC[REGFILE_CLAUSES; REPLICATE; APPEND; REGLIKE;
   IS_REGLIKE_PARTIAL]);;

let (WITH_ASSUMS:tactic->tactic) = fun tt (asl,w) ->
   (REPEAT (POP_ASSUM MP_TAC) THEN tt THEN
     REPLICATE_TAC (length asl) DISCH_TAC) (asl,w) ;;
let CRUFT_EX_THM = prove(
 `!cruft. ?crs cbs. cruft ++ [F; F] = REGFILE crs ++ F::cbs`,
  MATCH_MP_TAC list_2INDUCT THEN REPEAT STRIP_TAC THENL [
    EXISTS_TAC `[]:num list` THEN EXISTS_TAC `[F]`;
    BOOL_CASES_TAC `a0:bool` THENL [
      EXISTS_TAC `[0]` THEN EXISTS_TAC `[]:bool list`;
      EXISTS_TAC `[]:num list` THEN EXISTS_TAC `[F;F]`];
    WITH_ASSUMS (BOOL_CASES_TAC `a0:bool`) THENL [
      WITH_ASSUMS (BOOL_CASES_TAC `a1:bool`) THENL [
        WITH_ASSUMS (STRUCT_CASES_TAC (ISPEC `crs:num list` list_CASES)) THENL [
          WITH_ASSUMS (SIMP_TAC [REGFILE_CLAUSES; injectivity "list"; APPEND]);
          EXISTS_TAC `SUC h::t` THEN EXISTS_TAC `cbs:bool list`];
        EXISTS_TAC `0::crs'` THEN EXISTS_TAC `cbs':bool list`];
      EXISTS_TAC `[]:num list` THEN EXISTS_TAC `a1::cruft ++ [F; F]`]] THEN

  RULE_ASSUM_TAC SYM THEN
  REPEAT (POP_ASSUM MP_TAC) THEN SIMP_TAC[APPEND; REGFILE_CLAUSES; REPLICATE]);;
let CRUFT_PARSE = new_specification ["JREGS"; "JBITS"]
  (CONV_RULE (REWRITE_CONV [SKOLEM_THM]) CRUFT_EX_THM);;

let ALL_BOOL_CASES_TAC g = MAP_EVERY BOOL_CASES_TAC
  (filter (fun v -> type_of v = bool_ty) (frees (snd g))) g;;

let REGFILE_SUC = prove(`REGFILE (SUC n::ns) = T::REGFILE (n::ns)`,
  REWRITE_TAC[REGFILE; ITLIST; REG; REPLICATE; APPEND]);;

let incr_IND = prove(
 `!bs. REGLIKE T bs ==> !left.
   inc_shift T,rzip_tape left (bs ++ F::cruft) -->_w
   return F T,lzip_tape left (T::bs ++ cruft)`,
  SPEC_TAC(`T`,`s:bool`) THEN MATCH_MP_TAC REGLIKE_IND THEN CONJ_TAC THEN
  REPEAT GEN_TAC THEN ALL_BOOL_CASES_TAC THEN REWRITE_TAC[] THEN
  TRY (DISCH_THEN (ASSUME_TAC o GMATCH_MP' EVOLVE_TO_IMP)) THEN
  (ASM IMP_REWRITE_TAC)[APPEND; NAMED_BEHAVIOR_IMP]);;

let incr_THM = prove(
`inc_shift T,rzip_tape (F::left) (REGFILE ((n::ns) ++ crs) ++ F::cruft) -->_w
 return F F,lzip_tape left (F::REGFILE ((SUC n::ns) ++ crs) ++ cruft)`,
  IMP_REWRITE_TAC[REGFILE_SUC; APPEND; NAMED_BEHAVIOR;
   GMATCH_MP' EVOLVE_TO_IMP ((CONV_RULE (REWRITE_CONV [IS_REGLIKE_T])
   (SPECL[`(REGFILE (n::ns))`] incr_IND)))]);;

let decr_IND = prove(
 `!x bs. REGLIKE x bs ==> !left.
   dec_scan x,rzip_tape (x::left) (bs ++ F::cruft) -->_w
   dec_shift x,lzip_tape left (bs ++ F::F::cruft)`,
  MATCH_MP_TAC REGLIKE_IND THEN CONJ_TAC THEN
  REPEAT GEN_TAC THEN ALL_BOOL_CASES_TAC THEN REWRITE_TAC[] THEN
  TRY (DISCH_THEN (ASSUME_TAC o GMATCH_MP' EVOLVE_TO_IMP)) THEN
  (ASM IMP_REWRITE_TAC)[APPEND; NAMED_BEHAVIOR_IMP]);;

let decr_THM_0 = prove(
 `dec_init,rzip_tape (F::left) (REGFILE ((0::ns) ++ crs) ++ F::cruft) -->_w
  return F F,lzip_tape left (F::REGFILE ((0::ns) ++ crs) ++ F::cruft)`,
  IMP_REWRITE_TAC[REGFILE_CLAUSES; REPLICATE; APPEND; NAMED_BEHAVIOR_IMP]);;

let decr_THM_SUC = prove(
 `dec_init,rzip_tape (F::left) (REGFILE ((SUC n::ns) ++ crs) ++ F::cruft) -->_w
  return T F,lzip_tape left (F::(REGFILE ((n::ns) ++ crs)) ++ F::F::cruft)`,
  IMP_REWRITE_TAC[REGFILE_CLAUSES; APPEND; REPLICATE; NAMED_BEHAVIOR_IMP;
   GMATCH_MP' EVOLVE_TO_IMP ((CONV_RULE (REWRITE_CONV [IS_REGLIKE_PARTIAL])
   (SPECL[`T`;`REPLICATE n T ++ F::REGFILE ns`] decr_IND)))]);;

let init_IND = prove(
 `!x bs. REGLIKE x bs ==> !left.
   init_scan x,rzip_tape (x::left) (bs ++ F :: cruft) -->_w
   return F x,lzip_tape left (x::bs ++ T :: cruft)`,
  MATCH_MP_TAC REGLIKE_IND THEN CONJ_TAC THEN
  REPEAT GEN_TAC THEN ALL_BOOL_CASES_TAC THEN REWRITE_TAC[] THEN
  TRY (DISCH_THEN (ASSUME_TAC o GMATCH_MP' EVOLVE_TO_IMP)) THEN
  (ASM IMP_REWRITE_TAC)[APPEND; NAMED_BEHAVIOR_IMP]);;

let init_THM = prove(
 `init_scan F,rzip_tape (F::left) (REGFILE ((r::rs) ++ crs) ++ F::cruft) -->_w
  return F F,lzip_tape left (F::REGFILE ((r::rs) ++ crs) ++ T::cruft)`,
  MP_TAC (SPECL [`F`; `REGFILE ((r::rs) ++ crs)`] init_IND) THEN
  SIMP_TAC[IS_REGLIKE]);;

let EVOLVES_TO_IMPS_TAC = RULE_ASSUM_TAC
  (fun a -> try GEN_ALL (GMATCH_MP' EVOLVE_TO_IMP a) with Failure _ -> a) ;;
let regselect_THM = prove(
 `(!left. instate,rzip_tape (F::left) (REGFILE (rs ++ crs) ++ F :: cruft) -->_w
     return skip F,lzip_tape left (F::REGFILE (rs' ++ crs) ++ cruft')) ==>
  (!l r. selstate,rzip_tape l (F::r) -->_w instate,rzip_tape (F::l) r) ==>
  (!l r. selstate,rzip_tape l (T::r) -->_w selstate,rzip_tape (T::l) r) ==>
  selstate,rzip_tape (F::left) (REGFILE ((r::rs) ++ crs) ++ F::cruft) -->_w
    return skip F,lzip_tape left (F::REGFILE ((r::rs') ++ crs) ++ cruft')`,

 REWRITE_TAC[REGFILE_CLAUSES; APPEND; REPLICATE; GSYM APPEND_ASSOC] THEN
 REPEAT STRIP_TAC THEN EVOLVES_TO_IMPS_TAC THEN (ASM IMP_REWRITE_TAC)[] THEN
 TRANS_TAC (GEN_ALL tm_evolves_TRANS) `return skip T,lzip_tape (F::left)
     (T::REPLICATE r T ++ F::REGFILE (rs' ++ crs) ++ cruft')` THEN
 CONJ_TAC THENL [
   SPEC_TAC (`F::left`,`left':bool list`) THEN
   SPEC_TAC(`r:num`,`r:num`) THEN INDUCT_TAC; ALL_TAC] THEN

 WITH_ASSUMS (BOOL_CASES_TAC `skip:bool`) THEN EVOLVES_TO_IMPS_TAC THEN
 (ASM IMP_REWRITE_TAC)[REPLICATE; APPEND; NAMED_BEHAVIOR_IMP]);;

let REGFILE_APPEND = prove(
  `!rs1. REGFILE (rs1 ++ rs2) = REGFILE rs1 ++ REGFILE rs2`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[REGFILE_CLAUSES; APPEND; GSYM APPEND_ASSOC]);;

let regentry_THM = prove(
 `(!left crb crs.
     instate,rzip_tape (F::left) (REGFILE (rs ++ crs) ++ F::crb) -->_w
     return skip F,lzip_tape left (F::REGFILE (rs' ++ crs) ++ E crb)) ==>
  (!l r. sel1state,rzip_tape l (F::r) -->_w sel2state,rzip_tape (F::l) r) ==>
  (!l r. sel2state,rzip_tape l (F::r) -->_w instate,rzip_tape (F::l) r) ==>
  sel1state,rzip_tape left (OPSEG rs cruft) -->_w
  nextstate skip,lzip_tape left (OPSEG rs'
    (REGFILE (JREGS cruft) ++ E (JBITS cruft)))`,
 REWRITE_TAC[OPSEG] THEN
 REPEAT STRIP_TAC THEN REPLICATE_TAC 2 (ONCE_REWRITE_TAC [zip_extend']) THEN
 ASM_REWRITE_TAC[APPEND; GSYM APPEND_ASSOC; CRUFT_PARSE] THEN
 REWRITE_TAC[APPEND_ASSOC; GSYM REGFILE_APPEND] THEN
 EVOLVES_TO_IMPS_TAC THEN (ASM IMP_REWRITE_TAC)[] THEN
 BOOL_CASES_TAC `skip:bool` THEN REWRITE_TAC[NAMED_BEHAVIOR]);;

let num_regs =
  let rec iter i = if can state_of_name ("reg_incr."^string_of_int i) then
            iter (i+1) else i in
  iter 0;;

let mk_selected_thm state base =
  CONV_RULE (REWRITE_CONV[NAMED_BEHAVIOR]) (INST [state,`selstate:num`]
    (MATCH_MP regselect_THM (INST [genvar `:num`,`r:num`]
    (GEN `left:bool list` base))));;

let all_regs = map (fun i -> mk_var("r"^(string_of_int i),`:num`))
    (0 -- (num_regs-1));;
let mk_entry_thm st1 st2 sel =
  let th = CONV_RULE (REWRITE_CONV[NAMED_BEHAVIOR])
    (INST [st1,`sel1state:num`;st2,`sel2state:num`] (MATCH_MP regentry_THM
      (GENL [`left:bool list`;`cruft:bool list`;`crs:num list`] sel))) in
  let cregs,ctail = splitlist dest_cons (find_term is_cons (concl th)) in
  let rec substs i = if i == length cregs then
    [mk_list(List.drop i all_regs,`:num`),ctail] else
    match variables (el i cregs) with
      v::_ -> (el i all_regs,v)::substs (i+1) | [] -> substs (i+1) in
  INST (substs 0) th;;

let OPER_INIT_THM = mk_entry_thm `init_f1` `init_f2` init_THM;;
let (OPER_INCR_THMS, OPER_DECR_0_THMS, OPER_DECR_SUC_THMS) =
  let rec states sf i =
    if can state_of_name ("reg_incr." ^ (string_of_int i)) then
      mk_comb(sf,mk_small_numeral i)::states sf (i+1) else [] in
  let rec wrapify thm sts = match sts with
    | st0::((st1::_) as sts') -> mk_entry_thm st1 st0 thm::
        wrapify (mk_selected_thm st0 thm) sts'
    | _ -> [] in
  wrapify incr_THM (`reg_incr_last`::states `reg_incr` 0),
  wrapify decr_THM_0 (`reg_decr_last`::states `reg_decr` 0),
  wrapify decr_THM_SUC (`reg_decr_last`::states `reg_decr` 0);;

(* load and parse .subs file *)



(* dispatch basics

   dispatch and operations are two systems with clearly separated halves of the
   tape, subsets of the state set, and only a handful of crossing states (2
   dispatch, 2*nreg+1 operations)

   (we may also consider an "initialization segment" which is just executed and
   sets up the registers, although the 2017 machine runs reg_init
   continuously...)

   jumps and halting do not use data and happen entirely within the dispatch
   segment. since jumps can go in and out of several subroutines, ignoring them
   at higher levels is problematic, but we cannot identify them with either an
   entry or exit state. instead, higher levels use dispatch-root states, which
   are reliably hit before every operation or jump

   here we prove that from the dispatch-root we can reach an operation state if
   there is one, or go to another dispatch-root if there was a jump, and that
   operation returns can reach the dispatch root. it is mostly just expanding
   definitions, the tricky part is parameterizing subroutines so that they can
   be handled in any context *)

(* dispatch - spine *)

let memo_fix fn =
  let tbl = Hashtbl.create 500 in
  let rec fn' v = match Hashtbl.find_opt tbl v with
    Some r -> r | None -> let r = fn fn' v in Hashtbl.add tbl v r; r in
  fn' ;;

let INC_PC = define
  `INC_PC [] = [] /\
   INC_PC (F::sfx) = T::sfx /\
   INC_PC (T::sfx) = F::INC_PC sfx`;;

 (* machine dependent *)
let DISPSTATE = define`DISPSTATE left pc right = 1,lzip_tape left (REVERSE pc ++ right)`;;

let DISPSTATE_CONS = prove(
 `DISPSTATE left pc (b::right) = DISPSTATE left (b::pc) right`,
 REWRITE_TAC[DISPSTATE; REVERSE; GSYM APPEND_ASSOC; APPEND]);;

 (* todo: smarter STRUCT_CASES_TAC *)
let SPINE_C = prove(
 `!disp stnc stc n.
  (!pc right. LENGTH pc = n ==> stnc,lzip_tape (pc ++ left) right -->_w DISPSTATE left pc right) ==>
  (!pc right. LENGTH pc = n ==> stc,lzip_tape (pc ++ left) right -->_w DISPSTATE left (INC_PC pc) right) ==>
  (!ls rs. disp,lzip_tape (F::ls) rs -->_w stnc,lzip_tape ls (T::rs)) ==>
  (!ls rs. disp,lzip_tape (T::ls) rs -->_w stc,lzip_tape ls (F::rs)) ==>
  (!pc right. LENGTH pc = SUC n ==> disp,lzip_tape (pc ++ left) right -->_w DISPSTATE left (INC_PC pc) right)`,
  REPLICATE_TAC 9 STRIP_TAC THEN
  STRUCT_CASES_TAC (ISPEC `pc:bool list` list_CASES) THEN
  REWRITE_TAC[LENGTH; APPEND; NOT_SUC; SUC_INJ] THEN
  BOOL_CASES_TAC `h:bool` THEN EVOLVES_TO_IMPS_TAC THEN
  ASM IMP_REWRITE_TAC[INC_PC; SYM DISPSTATE_CONS]);;

let SPINE_NC = prove(
 `!disp stnc n.
  (!pc right. LENGTH pc = n ==> stnc,lzip_tape (pc ++ left) right -->_w DISPSTATE left pc right) ==>
  (!ls rs. disp,lzip_tape (F::ls) rs -->_w stnc,lzip_tape ls (F::rs)) ==>
  (!ls rs. disp,lzip_tape (T::ls) rs -->_w stnc,lzip_tape ls (T::rs)) ==>
  (!pc right. LENGTH pc = SUC n ==> disp,lzip_tape (pc ++ left) right -->_w DISPSTATE left pc right)`,
  REPLICATE_TAC 8 STRIP_TAC THEN
  STRUCT_CASES_TAC (ISPEC `pc:bool list` list_CASES) THEN
  REWRITE_TAC[LENGTH; APPEND; NOT_SUC; SUC_INJ] THEN
  BOOL_CASES_TAC `h:bool` THEN EVOLVES_TO_IMPS_TAC THEN
  ASM IMP_REWRITE_TAC[SYM DISPSTATE_CONS]);;

let SPINE_C2 = prove(
 `!disp stc n.
  (!pc right. LENGTH pc = n ==> stc,lzip_tape (pc ++ left) right -->_w DISPSTATE left (INC_PC pc) right) ==>
  (!ls rs. disp,lzip_tape (F::ls) rs -->_w stc,lzip_tape ls (F::rs)) ==>
  (!ls rs. disp,lzip_tape (T::ls) rs -->_w stc,lzip_tape ls (T::rs)) ==>
  (!pc right. LENGTH pc = SUC n ==> disp,lzip_tape (pc ++ left) right -->_w DISPSTATE left (INC_PC (INC_PC pc)) right)`,
  REPLICATE_TAC 8 STRIP_TAC THEN
  STRUCT_CASES_TAC (ISPEC `pc:bool list` list_CASES) THEN
  REWRITE_TAC[LENGTH; APPEND; NOT_SUC; SUC_INJ] THEN
  BOOL_CASES_TAC `h:bool` THEN EVOLVES_TO_IMPS_TAC THEN
  ASM IMP_REWRITE_TAC[INC_PC; SYM DISPSTATE_CONS]);;

let SPINE_C0 = prove(
 `!disp.
  (!ls rs. disp,lzip_tape (F::ls) rs -->_w 1,lzip_tape ls (T::rs)) ==>
  (!ls rs. disp,lzip_tape (T::ls) rs -->_w 1,lzip_tape ls (F::rs)) ==>
  (!pc right. LENGTH pc = SUC 0 ==> disp,lzip_tape (pc ++ left) right -->_w DISPSTATE left (INC_PC pc) right)`,
  REPLICATE_TAC 5 STRIP_TAC THEN
  STRUCT_CASES_TAC (ISPEC `pc:bool list` list_CASES) THEN
  SIMP_TAC[LENGTH; APPEND; NOT_SUC; SUC_INJ; LENGTH_EQ_NIL] THEN
  BOOL_CASES_TAC `h:bool` THEN
  ASM REWRITE_TAC[INC_PC; DISPSTATE; REVERSE; GSYM APPEND_ASSOC; APPEND]);;

let SPINE_NC0 = prove(
 `!disp.
  (!ls rs. disp,lzip_tape (F::ls) rs -->_w 1,lzip_tape ls (F::rs)) ==>
  (!ls rs. disp,lzip_tape (T::ls) rs -->_w 1,lzip_tape ls (T::rs)) ==>
  (!pc right. LENGTH pc = SUC 0 ==> disp,lzip_tape (pc ++ left) right -->_w DISPSTATE left pc right)`,
  REPLICATE_TAC 5 STRIP_TAC THEN
  STRUCT_CASES_TAC (ISPEC `pc:bool list` list_CASES) THEN
  SIMP_TAC[LENGTH; APPEND; NOT_SUC; SUC_INJ; LENGTH_EQ_NIL] THEN
  BOOL_CASES_TAC `h:bool` THEN
  ASM REWRITE_TAC[DISPSTATE; REVERSE; GSYM APPEND_ASSOC; APPEND]);;

let SPINE = memo_fix (fun SPINE' id ->
  let nid = mk_small_numeral id in
  let disch = CONV_RULE (REWRITE_CONV [ARITH_SUC; BEHAVIOR nid `F`; BEHAVIOR nid `T`]) in
  let name,(ns0,m0,w0),(ns1,m1,w1) = el id state_info in
  if w0 = true then
    if ns0 = 1 then 1,true,disch (SPEC nid SPINE_C0) else
    let len,_,thmnc = SPINE' ns0 in
    let _,_,thmc = SPINE' ns1 in
    len+1,true,MP (MP (disch (SPECL [nid; mk_small_numeral ns0; mk_small_numeral ns1; mk_small_numeral len] SPINE_C)) thmnc) thmc
  else
    if ns0 = 1 then 1,false,disch (SPEC nid SPINE_NC0) else
    let len,c,thmnc = SPINE' ns0 in
    if c then
      len+1,false,MP (disch (SPECL [nid; mk_small_numeral ns0; mk_small_numeral len] SPINE_C2)) thmnc
    else
      len+1,false,MP (disch (SPECL [nid; mk_small_numeral ns0; mk_small_numeral len] SPINE_NC)) thmnc) ;;

(* dispatch - jump and noop *)

let write_ID = prove(`write (t (&0)) t = t`,
 REWRITE_TAC [FUN_EQ_THM; tape_write_DEF] THEN MESON_TAC[]);;

 (* 10-20x faster than BEHAVIOR *)
let TT_CLAUSE =
  let z = `0` in
  let cv1 = CONV_RULE (GEN_REWRITE_CONV TOP_SWEEP_CONV [nmap_CLAUSES]) in
  let cv2 = CONV_RULE (GEN_REWRITE_CONV TOP_SWEEP_CONV [bmap_CLAUSES]) in
  fun id ->
    let precl = cv1 (AP_THM transition_table_DEF (mk_small_numeral id)) in
    fun b ->
      let cl1 = cv2 (AP_THM precl (mk_bool b)) in
      CONJ cl1 (NUM_EQ_CONV (mk_eq(lhand (rand (concl cl1)),z)));;
let TT_CLAUSES id = let cls = TT_CLAUSE id in CONJ (cls false) (cls true);;

let IGN_TURN_THM = prove(
 `(transition_table st F = nst,d,F /\ (nst = 0) = F) /\
  (transition_table st T = nst,d,T /\ (nst = 0) = F) ==>
  st,t -->_w nst,shift (if d then (&1) else --(&1)) t`,
 MATCH_MP_TAC (TAUT `(p/\q==>r==>s)==>(q/\r)/\(p/\r)==>s`) THEN
 REWRITE_TAC [SYM FORALL_BOOL_THM] THEN
 STRIP_TAC THEN STRIP_TAC THEN MATCH_MP_TAC tm_evolves_BASE THEN
 ASM_REWRITE_TAC[gtm_step_DEF; LET_DEF; LET_END_DEF; write_ID]);;

let TT_BEHAVE_L = prove(
 `transition_table st b = nst,F,w /\ (nst = 0) = F ==>
  (!l r. st,lzip_tape (b::l) r -->_w nst,lzip_tape l (w::r)) /\
  (!l r. st,rzip_tape l (b::r) -->_w nst,lzip_tape l (w::r))`,
 REPEAT STRIP_TAC THEN MATCH_MP_TAC tm_evolves_BASE THEN
 ASM_REWRITE_TAC[gtm_step_DEF; LET_DEF; LET_END_DEF; zip_read; zip_write;
 zip_shift]);;

let TT_BEHAVE_R = prove(
 `transition_table st b = nst,T,w /\ (nst = 0) = F ==>
  (!l r. st,lzip_tape (b::l) r -->_w nst,rzip_tape (w::l) r) /\
  (!l r. st,rzip_tape l (b::r) -->_w nst,rzip_tape (w::l) r)`,
 REPEAT STRIP_TAC THEN MATCH_MP_TAC tm_evolves_BASE THEN
 ASM_REWRITE_TAC[gtm_step_DEF; LET_DEF; LET_END_DEF; zip_read; zip_write;
 zip_shift]);;

let TT_BEHAVE_H = prove(
 `transition_table st b = 0,m,w /\ (0 = 0) = T ==>
  (!l r. st,lzip_tape (b::l) r -->_w halted) /\
  (!l r. st,rzip_tape l (b::r) -->_w halted)`,
 REPEAT STRIP_TAC THEN MATCH_MP_TAC tm_evolves_BASE THEN
 ASM_REWRITE_TAC[gtm_step_DEF; LET_DEF; LET_END_DEF; zip_read]);;

let JUMP_BIT_THM = prove(
 `transition_table st b = nst,F,b' /\ (nst = 0) = F ==>
  (!right. LENGTH pc = n ==> nst,lzip_tape (pc ++ left) right -->_w
    DISPSTATE left pc' right) ==>
  !right. LENGTH (b::pc) = SUC n ==> st,lzip_tape ((b::pc) ++ left) right -->_w
    DISPSTATE left (b'::pc') right`,
  DISCH_THEN (MP_TAC o MATCH_MP TT_BEHAVE_L) THEN STRIP_TAC THEN
  EVOLVES_TO_IMPS_TAC THEN ASM IMP_REWRITE_TAC[LENGTH; SUC_INJ; APPEND;
    SYM DISPSTATE_CONS]);;

let JUMP_TURN_THM = prove(
 `(transition_table st F = nst,F,F /\ (nst = 0) = F) /\
  (transition_table st T = nst,F,T /\ (nst = 0) = F) ==>
  (!right. LENGTH pc = n ==> nst,lzip_tape (pc ++ left) right -->_w
    DISPSTATE left pc' right) ==>
  !right. LENGTH pc = n ==> st,rzip_tape (pc ++ left) right -->_w
    DISPSTATE left pc' right`,
  DISCH_THEN (MP_TAC o GEN_ALL o MATCH_MP IGN_TURN_THM) THEN STRIP_TAC THEN
  EVOLVES_TO_IMPS_TAC THEN ASM IMP_REWRITE_TAC[zip_shift]);;

let JUMP = memo_fix (fun JUMP (kvars,id) ->
  let name,(ns0,m0,w0),(ns1,m1,w1) = el id state_info in
  if String.starts_with ~prefix:"dispatch." name then
    let _,_,thm = SPINE id in snd(SPEC_VAR thm)
  else if w1 && not w0 && not m0 && not m1 && ns0 = ns1 then
    MATCH_MP (MATCH_MP JUMP_TURN_THM (TT_CLAUSES id)) (JUMP (kvars,ns0))
  else
    match kvars with
     kv::kvs -> MATCH_MP (MATCH_MP JUMP_BIT_THM (TT_CLAUSE id kv))
       (JUMP (kvs,if kv then ns1 else ns0)));;

(* dispatch - building the tree

   the DISPATCH predicate depends on the existence of a dispatch-root state, so
   in machine variants where it does not exist a weaker predicate must be used.
   DISPATCH_WEAK is believed to survive *)

let DISPATCH = define`DISPATCH st len sfx <=> LENGTH sfx = len /\
  !left right pfx. DISPSTATE left (pfx ++ sfx) right -->_w
    st,rzip_tape (sfx ++ left) (REVERSE pfx ++ right)`;;

 (* or perhaps dispatch.16 *)
let main_state = state_of_name "main()[]";;

let DISPATCH_LEN = prove(`DISPATCH st len sfx ==> LENGTH sfx = len`,
  SIMP_TAC[DISPATCH]);;
let DISPATCH_EV = prove(`DISPATCH st len sfx /\ 2 <= len ==>
    DISPSTATE left (pfx ++ sfx) right -->_w
      st,rzip_tape (sfx ++ left) (REVERSE pfx ++ right)`,
  SIMP_TAC[DISPATCH]);;

let DISPATCH_ROOT = prove(`DISPATCH 448 0 []`, (*hack*)
  SIMP_TAC[DISPATCH; LENGTH; APPEND; APPEND_NIL; DISPSTATE] THEN
  REPEAT GEN_TAC THEN ACCEPT_TAC (CONV_RULE (REWRITE_CONV [zip_shift])
    (INST[`lzip_tape left (REVERSE pfx ++ right)`,`t:int -> bool`]
      (MATCH_MP IGN_TURN_THM (TT_CLAUSES 1)))));;

let DISPATCH_BIT = prove(
 `transition_table st b = nst,T,b /\ (nst = 0) = F ==>
  DISPATCH st len sfx ==> DISPATCH nst (SUC len) (b::sfx)`,
  DISCH_THEN (ASSUME_TAC o GEN_ALL o MATCH_MP TT_BEHAVE_R) THEN
  SIMP_TAC[DISPATCH; LENGTH; APPEND] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM (MP_TAC o SPECL [`left:bool list`; `right:bool list`;
    `pfx ++ [b:bool]`]) THEN
  SIMP_TAC[GSYM APPEND_ASSOC; APPEND; REVERSE_APPEND; REVERSE] THEN
  DISCH_THEN (MP_TAC o GEN_ALL o MATCH_MP EVOLVE_TO_IMP) THEN
  IMP_REWRITE_TAC[] THEN ASM_SIMP_TAC[]);;

let DISPATCH_HALT = prove(
 `transition_table st b = 0,m,w /\ (0 = 0) = T ==>
  DISPATCH st len sfx ==> DISPSTATE left (b::sfx) right -->_w halted`,
  DISCH_THEN (ASSUME_TAC o GEN_ALL o MATCH_MP TT_BEHAVE_H) THEN
  SIMP_TAC[DISPATCH] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM (MP_TAC o SPECL [`left:bool list`; `right:bool list`;
    `[b:bool]`]) THEN
  SIMP_TAC[GSYM APPEND_ASSOC; APPEND; REVERSE] THEN
  DISCH_THEN (MP_TAC o GEN_ALL o MATCH_MP EVOLVE_TO_IMP) THEN
  IMP_REWRITE_TAC[] THEN ASM_SIMP_TAC[]);;

let WRAPAROUND = prove(`DISPATCH st 0 sfx ==> INC_PC sfx = sfx`,
  SIMP_TAC[DISPATCH; LENGTH_EQ_NIL; INC_PC]);;

(* sub representation *)

type line = Lop of thm list | Lsub of thm ;;

let pc_bits, _, _ = SPINE (state_of_name "dispatch.0.carry");; (*hack*)

let LINE_OF_OPER =
  let lewit = EQT_ELIM (NUM_LE_CONV (mk_comb(`(<=) 2`,
    mk_small_numeral pc_bits))) in
  let disp0 = CONV_RULE (REWRITE_CONV [REVERSE; APPEND])
    (INST [`[]:bool list`,`pfx:bool list`] DISPATCH_EV) in
  let right = `right:bool list` and left = `left:bool list` in
  let app = `(++):bool list->bool list->bool list` in
  let subline asm basethm =
    let pcterm = rand (concl asm) in
    let lenth = MATCH_MP DISPATCH_LEN asm in
    let _,_,thm3 = SPINE (dest_small_numeral (lhand (rand (concl basethm)))) in
    let step1 = INST[rand (rand (lhand (concl basethm))),right]
      (MATCH_MP disp0 (CONJ asm lewit)) in
    let step2 = INST[mk_comb (mk_comb(app, pcterm),left),left] basethm in
    let step3 = INST[rand (rand (rand (concl basethm))),right]
      (CONV_RULE (PURE_REWRITE_CONV [INC_PC])
        (SPEC_ALL (MATCH_MP thm3 lenth))) in
    MATCH_MP tm_evolves_TRANS (CONJ step1
      (MATCH_MP tm_evolves_TRANS (CONJ step2 step3))) in
  let basethms = map (CONV_RULE (REWRITE_CONV [NAMED_STATES]))
    (OPER_INIT_THM :: (OPER_INCR_THMS @ OPER_DECR_0_THMS @
      OPER_DECR_SUC_THMS)) in
  fun asm ->
    let opst = rand (rator (rator (concl asm))) in
    let len = dest_small_numeral (lhand (concl asm)) in
    if len <> pc_bits then failwith "LINE_OF_OPER short" else
    let bases = filter (fun t -> lhand (lhand (concl t)) = opst) basethms in
    if bases = [] then failwith "LINE_OF_OPER nomatch" else
    Lop (map (subline asm) bases) ;;

let dest_bool b =
  if b = mk_bool true then true else
  if b = mk_bool false then false else
  failwith "dest_bool" ;;

 (* optimize? support left-edge jumps? *)
let LINE_OF_JUMP asm =
  let kbits,_ = splitlist dest_cons (rand (concl asm)) in
  let pclen = dest_small_numeral (lhand (concl asm)) in
  let extrapc = mk_list(replicate (mk_bool false) (pc_bits - pclen),bool_ty) in
  let wit = EQT_ELIM (NUM_LE_CONV (mk_comb(`(<=) 2`,lhand(concl asm)))) in
  let state = dest_small_numeral (lhand (rator (concl asm))) in
  let dth = MATCH_MP DISPATCH_EV (CONJ asm wit) in
  let jthr = CONV_RULE (PURE_REWRITE_CONV [ARITH_SUC])
    (SPEC_ALL (JUMP (map dest_bool kbits,state))) in
  let jth = INST [`REVERSE pfx ++ right:bool list`,`right:bool list`]
     (MATCH_MP jthr (MATCH_MP DISPATCH_LEN asm)) in
  let djth = INST [extrapc,`pfx:bool list`]
    (MATCH_MP tm_evolves_TRANS (CONJ dth jth)) in
  Lop [CONV_RULE (PURE_REWRITE_CONV [REVERSE; APPEND;
    INC_PC; DISPSTATE_CONS]) djth] ;;

let LINES_OF_EDGE nodefn asm bit =
  let st = dest_small_numeral (lhand (rator (concl asm))) in
  let cl = TT_CLAUSE st bit in
  if dest_bool (rand (rand (concl cl))) then
    [Lop [MATCH_MP (MATCH_MP DISPATCH_HALT cl) asm]]
  else
    nodefn (CONV_RULE (PURE_REWRITE_CONV [ARITH_SUC])
      (MATCH_MP (MATCH_MP DISPATCH_BIT cl) asm)) ;;

let LINES_OF_NODE nodefn asm =
  try [LINE_OF_OPER asm] with Failure _ ->
  let st = dest_small_numeral (lhand (rator (concl asm))) in
  let name = name_of_state st in
  if String.ends_with ~suffix:"[]" name &&
      hd (hyp asm) <> concl asm then
    [Lsub asm]
  else if String.contains name '[' || name = "reg_incr.2" then (*hack*)
    LINES_OF_EDGE nodefn asm false @ LINES_OF_EDGE nodefn asm true
  else
    [LINE_OF_JUMP asm];;

let apply_wraparound asm =
  let wr = MATCH_MP WRAPAROUND asm in
  let apply = CONV_RULE (PURE_REWRITE_CONV [wr]) in
  function Lsub _ as l -> l | Lop tt -> Lop (map apply tt);;

let LINES_OF_SUB =
  let subtree = memo_fix LINES_OF_NODE in
  fun (st,len) ->
    let asm = ASSUME (list_mk_comb(`DISPATCH`,[mk_small_numeral(st);
      mk_small_numeral(len); mk_var("pc",`:bool list`)])) in
    let ll = subtree asm in
    if len = 0 then map (apply_wraparound asm) ll else ll;;

let callee_of_line l = match l with
    Lsub th -> (dest_small_numeral (lhand (rator (concl th))),
     dest_small_numeral (lhand (concl th)))
  | _ -> failwith "callee_of_line";;

let all_callees_of_sub fn = memo_fix (fun r addr ->
  insert addr (unions (map r (mapfilter callee_of_line (fn addr)))));;

let complexity fn =
  let subs = all_callees_of_sub fn (main_state,0) in
  let lines = flat (map fn subs) in
  let thms = flat (map (function Lop ts -> ts | Lsub t -> [t]) lines) in
  (length subs, length lines, length thms) ;;

(* initialization *)

let comp_tm_step = memo_fix (fun _ (st,b,dir) ->
  let cl = TT_CLAUSE st b in
  let bf = if dest_bool (rand (rand (concl cl))) then
    TT_BEHAVE_H else if dest_bool (lhand (rand (rand (lhand (concl cl))))) then
      TT_BEHAVE_R else TT_BEHAVE_L in
  let bfc = MATCH_MP bf cl in
  let bp = SPEC_ALL (if dir then CONJUNCT2 bfc else CONJUNCT1 bfc) in
  EQ_MP (AP_THM (AP_TERM `-->_w` (SYM (ASSUME
    (mk_eq(`i:num#(int -> bool)`,lhand (concl bp)))))) (rand (concl bp))) bp,
  MATCH_MP tm_evolves_TRANS
    (CONJ (ASSUME (mk_comb(`(-->_w) i`,lhand (concl bp)))) bp));;

let extend_tm_step dir =
  let cr = CONV_RULE (REWRITE_CONV [zip_extend]) o ASSUME in
  if dir then
    cr (`i = st:num,rzip_tape l []`), cr (`i -->_w st,rzip_tape l []`)
  else
    cr (`i = st:num,lzip_tape [] r`), cr (`i -->_w st,lzip_tape [] r`);;

let apply_tm_step (eq,tr) i thm =
  let rule = if is_eq (concl thm) then eq else tr in
  PROVE_HYP thm (INST i rule);;

let COMP_TM_ITERATE =
  let lv = `l:bool list` and rv = `r:bool list` in
  let iv = `i:num#(int -> bool)` and stv = `st:num` in
  fun thm ->
    let sttm,btm,dir,ltm,rtm,ex = match rand (concl thm) with
        Comb(Comb(_,sttm),Comb(Comb(Const("rzip_tape",_),ltm),
          Comb(Comb(_,btm),rtm))) -> sttm,btm,true,ltm,rtm,false
      | Comb(Comb(_,sttm),Comb(Comb(Const("lzip_tape",_),Comb(Comb(_,btm),
          ltm)),rtm)) -> sttm,btm,false,ltm,rtm,false
      | Comb(Comb(_,sttm),Comb(Comb(Const("rzip_tape",_),ltm),nil)) ->
          sttm,mk_bool false,true,ltm,nil,true
      | Comb(Comb(_,sttm),Comb(Comb(Const("lzip_tape",_),nil),rtm)) ->
          sttm,mk_bool false,false,nil,rtm,true
      | _ -> failwith "not a ground tape" in
    let thm' = if ex then apply_tm_step (extend_tm_step dir)
      [lhand (concl thm),iv;ltm,lv;rtm,rv;sttm,stv] thm else thm in
    apply_tm_step (comp_tm_step (dest_small_numeral sttm,dest_bool btm,dir))
      [lhand (concl thm),iv;ltm,lv;rtm,rv] thm' ;;

 (* 1120 states at ~80 us/step *)
let INIT_REACHED =
  let state_eq = REWRITE_CONV [DISPSTATE; OPSEG; REGFILE_CLAUSES; REVERSE;
    APPEND; REPLICATE; zip_extend]
    `DISPSTATE [] [F;F;F;F;T;F;F;F;F;F;F;F;F;F;F;F;F]
      (OPSEG [0;0;0;0;0;0;0;0;0;0;0;0] [T;F;T;F;T;F;T])` in (*hack*)
  let rec srch = fun i thm -> if rand (concl thm) = rand (concl state_eq) then
    CONV_RULE (RAND_CONV (K (SYM state_eq))) thm else
    if i > 10000 then failwith "too long" else
    srch (i+1) (COMP_TM_ITERATE thm) in
  srch 0 zip_init ;;

(* class abstraction *)

parse_as_infix("-->_c",(12,"right"));;
let TMEVC_DEF = define`c1 -->_c c2 <=>
   !a. a IN c1 ==> ?b. b IN c2 /\ a -->_w b`;;
let REGSTATE = define`RS pc regs = {DISPSTATE l pc (OPSEG regs c) | c,l | T}`;;

let TMEVC_TRANS = prove(`c1 -->_c c2 /\ c2 -->_c c3 ==> c1 -->_c c3`,
  MESON_TAC[TMEVC_DEF; tm_evolves_TRANS]);;
let TMEVC_LIFT1 = prove(
 `(!l c. DISPSTATE l pc (OPSEG rs c) -->_w
   DISPSTATE l pc' (OPSEG rs' (J c))) ==> RS pc rs -->_c RS pc' rs'`,
 REWRITE_TAC[REGSTATE; TMEVC_DEF; IN_ELIM_THM] THEN MESON_TAC[]);;
let TMEVC_LIFTI = prove(
 `initial -->_w DISPSTATE l pc (OPSEG rs c) ==> {initial} -->_c RS pc rs`,
 REWRITE_TAC[REGSTATE; TMEVC_DEF; IN_ELIM_THM; IN_SING] THEN MESON_TAC[]);;
let INITIAL_RS = MATCH_MP TMEVC_LIFTI INIT_REACHED;;
let TMEVC_LIFT2 = prove(
 `(!l rr. DISPSTATE l pc rr -->_w DISPSTATE l pc' rr) ==>
  RS pc rs -->_c RS pc' rs`,
 REWRITE_TAC[REGSTATE; TMEVC_DEF; IN_ELIM_THM] THEN MESON_TAC[]);;
let TMEVC_LIFT3 = prove(
 `(!l rr. DISPSTATE l pc rr -->_w halted) ==> RS pc rs -->_c {halted}`,
 REWRITE_TAC[REGSTATE; TMEVC_DEF; IN_ELIM_THM; IN_SING] THEN MESON_TAC[]);;

let LINES_OF_SUB_C =
  let abs_tm t = if is_const (rand (concl t)) then
    MATCH_MP TMEVC_LIFT3 (GENL [`left:bool list`;`right:bool list`] t) else
    if is_var (rand (rand (concl t))) then
      MATCH_MP TMEVC_LIFT2 (GENL [`left:bool list`;`right:bool list`] t) else
      MATCH_MP TMEVC_LIFT1 (GENL [`left:bool list`;`cruft:bool list`] t) in
  let abs_line l = match l with Lsub t -> Lsub t | Lop ts ->
    Lop (map abs_tm ts) in
memo_fix (fun _ addr -> map abs_line (LINES_OF_SUB addr));;

(* cantor pairs *)

let CPAIR_INDUCT = prove(
 `P 0 0 /\ (!x y. P x (SUC y) ==> P (SUC x) y) /\
  (!x. P x 0 ==> P 0 (SUC x)) ==> !x y. P x y`,
  REPEAT STRIP_TAC THEN WF_INDUCT_TAC `x + y` THEN POP_ASSUM MP_TAC THEN
  SPEC_TAC(`y:num`,`y:num`) THEN SPEC_TAC(`x:num`,`x:num`) THEN
  REPEAT INDUCT_TAC THEN
  (ASM IMP_REWRITE_TAC[ARITH_RULE `SUC x + y = x + SUC y`]) THEN
  ASM_SIMP_TAC[ADD_CLAUSES; LT]);;

parse_as_infix("<>",(14,"right"));;
let CPAIR_DEF = define`x <> y = ((x + y) * ((x + y) + 1)) DIV 2 + x`;;
let CPAIR_REC = prove(
 `0 <> 0 = 0 /\ SUC x <> y = SUC (x <> SUC y) /\ 0 <> SUC y = SUC (y <> 0)`,
  REWRITE_TAC[CPAIR_DEF] THEN ARITH_TAC);;

let CUNPAIR_DEF = new_recursive_definition num_RECURSION
  `CUNPAIR 0 = 0,0 /\ CUNPAIR (SUC p) = (match SND (CUNPAIR p) with
     0 -> 0,SUC (FST (CUNPAIR p)) | SUC y -> SUC (FST (CUNPAIR p)),y)`;;
let CFST_DEF = define`CFST p = FST (CUNPAIR p)`;;
let CSND_DEF = define`CSND p = SND (CUNPAIR p)`;;
let CFSTSND = prove(
 `CFST 0 = 0 /\ CSND 0 = 0 /\
  CFST (SUC p) = (match CSND p with 0 -> 0 | SUC y -> SUC (CFST p)) /\
  CSND (SUC p) = (match CSND p with 0 -> SUC (CFST p) | SUC y -> y)`,
 REWRITE_TAC[CFST_DEF; CSND_DEF; CUNPAIR_DEF] THEN
 STRUCT_CASES_TAC (SPEC `SND (CUNPAIR p)` num_CASES) THEN
 REWRITE_TAC[]);;

let CFSTSNDP = prove(`!x y. CFST (x <> y) = x /\ CSND (x <> y) = y`,
  MATCH_MP_TAC CPAIR_INDUCT THEN SIMP_TAC[CPAIR_REC; CFSTSND]);;
let CPAIR = prove(`!p. CFST p <> CSND p = p`,
  INDUCT_TAC THEN SIMP_TAC[CPAIR_REC; CFSTSND] THEN POP_ASSUM MP_TAC THEN
  STRUCT_CASES_TAC (SPEC `CSND p` num_CASES) THEN SIMP_TAC[CPAIR_REC]);;

let CPAIR_INDUCT2 = prove(`!P. (!x y. P (x <> y)) ==> !p. P p`,
  REPEAT STRIP_TAC THEN POP_ASSUM (MP_TAC o SPECL[`CFST p`; `CSND p`]) THEN
  SIMP_TAC[CPAIR]);;

(* simplification

   simplifycf simplifies control flow by combining adjacent edges: operations
   which do not perform case analysis (jumps, increments, noops, initialization
   steps, more after inlining) are combined with their predecessors, and
   unreachable lines are removed. this also performs a consistency check that
   we have a line for all reachable pc values

   decrloop recognizes simple decrement loops and translates them into zeroing,
   addition, etc as simple operations *)

let c_halted_tm = `{halted}`;;
let rec pad_pc nbits tm = if nbits = 0 then tm else
  mk_cons (mk_bool false) (pad_pc (nbits-1) tm);;
let rec inc_pc tm =
  if is_cons tm then
    let btm,bstm = dest_cons tm in
    if dest_bool btm then mk_cons (mk_bool false) (inc_pc bstm) else
    mk_cons (mk_bool true) bstm
  else
    mk_comb(`INC_PC`,tm);;

let addr_of_line = function
    Lsub t -> pad_pc (pc_bits - dest_small_numeral (lhand (concl t)))
      (rand (concl t))
  | Lop (t::_) -> lhand (lhand (concl t))
  | _ -> failwith "addr_of_line";;

let addrs_after_line = function
    Lsub t -> [pad_pc (pc_bits - dest_small_numeral (lhand (concl t)))
      (inc_pc (rand (concl t)))]
  | Lop tt -> map lhand (filter (fun t -> t <> c_halted_tm)
      (map (rand o concl) tt));;

let thms_of_line = function Lsub t -> [t] | Lop tt -> tt;;
let thms_of_sub = flat o map thms_of_line;;
let pcl_of_sub = dest_small_numeral o lhand o
  hd o hyp o hd o thms_of_line o hd;;

let curried_tmevc = MATCH_MP (TAUT `(p/\q==>r)==>q==>p==>r`) TMEVC_TRANS;;

let ADD00 = ARITH_RULE `0 + x = x /\ x + 0 = x`;;
let simplifycf lines =
  let lassoc = map (fun l -> addr_of_line l,l) lines in
  let pcl = pcl_of_sub lines in
  let first_addr = if pcl = 0 then (*hack*)
    funpow 16 inc_pc (pad_pc (pc_bits - pcl) `pc:bool list`) else
    pad_pc (pc_bits - pcl) `pc:bool list` in
  let last_addr = pad_pc (pc_bits - pcl) `INC_PC pc` in
  let rec chain t1 t2 = (*minor hack*)
    let t1r = rand (rand (concl t1)) and t2l = rand (lhand (concl t2)) in
    if is_var t1r && not (is_var t2l) then chain (INST [t2l,t1r] t1) t2 else
    CONV_RULE (REWRITE_CONV [ADD00; ARITH_SUC; CFSTSNDP])
      (MATCH_MP (MATCH_MP curried_tmevc t2) t1) in
  let rec simpcl t = if rand (concl t) = c_halted_tm then t else
    let nexta = lhand (rand (concl t)) in
    match List.assoc_opt nexta lassoc with
      Some (Lop [tn]) -> simpcl (chain t tn) | _ -> t in
  let simpline = function Lsub t -> Lsub t | Lop tt -> Lop (map simpcl tt) in
  let rec visit lblack agrey = match agrey with [] -> lblack | ag::ags ->
    if List.mem_assoc ag lblack || ag = last_addr then visit lblack ags else
    let gl' = simpline (assoc ag lassoc) in
    visit ((ag,gl')::lblack) (addrs_after_line gl' @ ags) in
  rev (map snd (visit [] [first_addr])) ;;

let EVOLVEC_TO_IMP = MATCH_MP (TAUT `(p/\q==>r)==>p==>q==>r=T`) TMEVC_TRANS;;

let TMEVC_INDUCT = prove(
 `!D E. (!j. D 0 j -->_c E j) /\ (!i j. D (SUC i) j -->_c D i (SUC j)) ==>
  !i. D i 0 -->_c E (i + 0)`,
  REPLICATE_TAC 4 STRIP_TAC THEN SPEC_TAC(`0`,`j:num`) THEN
  SPEC_TAC(`i:num`,`i:num`) THEN
  POP_ASSUM (ASSUME_TAC o GEN_ALL o MATCH_MP EVOLVEC_TO_IMP o SPEC_ALL) THEN
  INDUCT_TAC THEN ASM IMP_REWRITE_TAC[ADD] THEN
  ASM_SIMP_TAC[ARITH_RULE `SUC (i+j) = i + SUC j`]);;

let decrloop thm0 thmsuc =
  let rec find_indvar ll = let l,ll' = dest_cons ll in
    if is_comb l && rator l = `SUC` then rand l else find_indvar ll' in
  let indvar = find_indvar (rand (lhand (concl thmsuc))) in
  let tmpvar = `i:num` in
  let suc_map = zip (dest_list (rand (lhand (concl thmsuc))))
    (dest_list (rand (rand (concl thmsuc)))) in
  let suc_map' = filter (fun p -> is_var (fst p) && snd p <> fst p) suc_map in
  let substsm (r,rupd) =
    if rupd = mk_comb(`SUC`,r) then mk_binop `(+)` indvar r,r else
    failwith "decrloop unknown rule" in
  let sublist = map substsm suc_map' in
  let d = mk_abs(tmpvar,mk_abs(indvar,subst ((tmpvar,`0`)::sublist)
    (lhand (concl thm0)))) in
  let e = mk_abs(indvar,subst sublist (rand (concl thm0))) in
  CONV_RULE (REWRITE_CONV[ADD_CLAUSES]) (SPEC indvar
    (CONV_RULE (REWRITE_CONV [thm0; thmsuc; ADD])
      (SPECL [d;e] TMEVC_INDUCT)));;

let decrloop_sub ls =
  let decrloop_line l = match l with
      Lop [t0;ts] when lhand (lhand (concl ts)) = lhand (rand (concl ts)) ->
        Lop [decrloop t0 ts]
    | _ -> l in
  map decrloop_line ls;;

let inline_sub r ls =
  let inline_line l = match l with
      Lsub t -> (match r (callee_of_line l) with
          [Lop [lop]] -> Lop [CONV_RULE (REWRITE_CONV [INC_PC])
            (PROVE_HYP t (INST [rand (concl t),`pc:bool list`] lop))]
        | _ -> l)
    | _ -> l in
  map inline_line ls;;

let rec force_inline r ls =
  let rec
    inline_line l = match l with
      Lop _ -> [l]
    | Lsub t -> map (adjust_line t) (force_inline r (r (callee_of_line l))) and
    adjust_cl t cl = CONV_RULE (REWRITE_CONV [INC_PC])
      (PROVE_HYP t (INST [rand (concl t),`pc:bool list`] cl)) and
    adjust_line t l = match l with
      Lop tt -> Lop (map (adjust_cl t) tt)
    | _ -> fail() in
  flat (map inline_line ls);;

let unshuffle_vars thmlist =
  let regfiles = map dest_list (flat (map (fun t ->
    [rand (lhand (concl t)); rand (rand (concl t))]) thmlist)) in
  let xpos = itlist (fun t xp -> map (fun (x,y) -> x::y) (zip t xp)) regfiles
    (replicate [] num_regs) in
  let blank = replicate `v:num` num_regs in
  let reg_to_skel = zip blank all_regs in
  let skels = zip (map (map (vsubst reg_to_skel)) xpos) all_regs in
  let blank_skel = replicate `v:num` (length regfiles) in
  let oregs = map snd (sort (<) (filter (fun (sk,r) ->
    sk <> blank_skel) skels)) in

  let indices = map (fun r -> index r all_regs) oregs in
  let ren = map (fun i -> mk_var("v"^(string_of_int i),`:num`))
    (1 -- length oregs) in
  let ren_map = zip ren oregs in
  let abs = list_mk_abs (ren, vsubst ren_map (mk_flist all_regs)) in
  let cnv t =
    let parts = dest_list t in
    SYM (BETAS_CONV (list_mk_comb(abs,
      (map (fun ix -> el ix parts) indices)))) in
  let gen t =
    GENL (intersect (frees (concl t)) oregs) t in
  map (gen o CONV_RULE (ONCE_DEPTH_CONV cnv)) thmlist;;

let EVOLVESC_TO_IMPS_TAC = RULE_ASSUM_TAC
  (fun a -> try GEN_ALL (GMATCH_MP' EVOLVEC_TO_IMP a) with Failure _ -> a) ;;

let EVOLVESC_TO_IMPS_TAC' = RULE_ASSUM_TAC
  (fun a -> try CONJ a (GEN_ALL (GMATCH_MP' EVOLVEC_TO_IMP a))
    with Failure _ -> a) ;;

let pair_sub_THM = prove(
 `(!y x z. RS A (J x y z) -->_c RS B (J 0 (x + y) (x + z))) ==>
  (!x y. RS B (J x y 0) -->_c RS C (J x 0 y)) ==>
  (!y z x. RS B (J x y (SUC z)) -->_c
    RS B (J 0 ((z + x) + SUC y) (z + x))) ==>
  RS A (J x y z) -->_c RS C (J 0 0 ((x <> z) + y))`,

  REWRITE_TAC[ADD_CLAUSES; CPAIR_DEF] THEN INTRO_TAC "a; b0; bs" THEN
  REMOVE_THEN "b0" MP_TAC THEN EVOLVESC_TO_IMPS_TAC THEN
  ASM IMP_REWRITE_TAC[] THEN STRIP_TAC THEN SPEC_TAC(`y:num`, `y:num`) THEN
  SPEC_TAC(`x + z`, `w:num`) THEN INDUCT_TAC THEN
  ASM IMP_REWRITE_TAC[MULT; ADD; DIV_0] THEN
  ASM_REWRITE_TAC[ARITH_RULE `
    w + 0 = w /\ SUC ((w + 0) + x + y) = x + y + SUC w /\
    ((w * SUC (w + 1) + SUC (w + 1)) DIV 2 + x) + y =
      ((w * (w + 1)) DIV 2 + x) + (y + SUC w)`]);;

let (EDIT_TAC:term -> tactic ->tactic) = fun tm t (asl,w) ->
  (SUBGOAL_THEN (mk_eq(w,tm)) SUBST1_TAC THENL [t; ALL_TAC]) (asl,w);;

let unpair_sub_THM = prove(
 `(!y x z. RS A (J x y z) -->_c RS B (J 0 0 (x + z))) ==>
  (!x y. RS B (J x y 0) -->_c RS D (J x y 0)) ==>
  (!x y z. RS B (J x y (SUC z)) -->_c RS C (J x (SUC y) z)) ==>
  (!y z. RS C (J 0 y z) -->_c RS B (J y 0 z)) ==>
  (!x y z. RS C (J (SUC x) y z) -->_c RS B (J x y z)) ==>
  RS A (J x y z) -->_c RS D (J (CSND (x + z)) (CFST (x + z)) 0)`,

  STRIP_TAC THEN EVOLVESC_TO_IMPS_TAC THEN ASM IMP_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN

  EDIT_TAC `RS B (J (CSND 0) (CFST 0) (x+z)) -->_c
    RS D (J (CSND (0+x+z)) (CFST (0+x+z)) (1-1))`
    (REWRITE_TAC[CFSTSND; ADD00; SUB_REFL]) THEN
  SPEC_TAC(`0`,`u:num`) THEN SPEC_TAC(`x+z`,`w:num`) THEN
  REWRITE_TAC[SUB_REFL] THEN INDUCT_TAC THEN

  ASM_REWRITE_TAC[ADD00] THEN

  GEN_TAC THEN POP_ASSUM (MP_TAC o SPEC `SUC u`) THEN
  EVOLVESC_TO_IMPS_TAC THEN ASM IMP_REWRITE_TAC[ADD_CLAUSES] THEN

  CONV_TAC (LAND_CONV (LAND_CONV (REWRITE_CONV [CFSTSND]))) THEN
  STRUCT_CASES_TAC (SPEC `CSND u` num_CASES) THEN ASM IMP_REWRITE_TAC[]);;

let renormalize_vars t =
  let t' = BETA_RULE t in
  let varl = dest_list (rand (lhand (concl t'))) in
  INST (zip all_regs varl) t';;

let recognize_pairing ll = try match ll with
    [Lop [l1]; Lop [l2;l3]] -> [Lop [
      renormalize_vars (rev_itlist (C MATCH_MP)
        (unshuffle_vars [l1; l2; l3]) pair_sub_THM)]]
  | [Lop [l1]; Lop [l2;l3]; Lop [l4;l5]] -> [Lop [
      renormalize_vars (rev_itlist (C MATCH_MP)
        (unshuffle_vars [l1; l2; l3; l4; l5]) unpair_sub_THM)]]
  | _ -> ll
  with _ -> ll;;

let dest_dec_op = function
  Lop [t0; tsuc] -> el (index `0`
    (dest_list (rand (lhand (concl t0))))) all_regs, t0, tsuc
| _ -> failwith "dest_dec_op";;

let TRICOND_THM = prove(
 `(!v w. RS A (S 0       w) -->_c RS C (S 0 w) /\
         RS A (S (SUC v) w) -->_c RS B (S v w) /\
         RS B (S v       0) -->_c RS G (W v 0) /\
         RS B (S v (SUC w)) -->_c RS A (S v w) /\
         RS C (S v       0) -->_c RS E (V v 0) /\
         RS C (S v (SUC w)) -->_c RS D (U v w)) ==>
  (v < w ==> RS A (S v w) -->_c RS D (U 0 (w - v - 1))) /\
  (v = w ==> RS A (S v w) -->_c RS E (V 0 0)) /\
  (w < v ==> RS A (S v w) -->_c RS G (W (v - w - 1) 0))`,

  REWRITE_TAC[GSYM AND_FORALL_THM] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN EVOLVESC_TO_IMPS_TAC' THEN
  SPEC_TAC(`w:num`,`w:num`) THEN SPEC_TAC(`v:num`,`v:num`) THEN
  INDUCT_TAC THEN INDUCT_TAC THEN
  ASM_SIMP_TAC[NOT_SUC; SUC_INJ; LT_0; SUB_0; SUC_SUB1; LT_SUC;
    SUB_SUC; LT] THEN ASM IMP_REWRITE_TAC[]);;

let ltgtjoin = MATCH_MP (TAUT `(A \/ B \/ C) ==>
  (A ==> P) /\ (B ==> P) ==> ~C ==> P`) (SPEC_ALL LT_CASES);;
let tricond_line al lassoc =
  let air,a0,asuc = dest_dec_op al in
  let bir,b0,bsuc = dest_dec_op (assoc (lhand (rand (concl asuc))) lassoc) in
  let cir,c0,csuc = dest_dec_op (assoc (lhand (rand (concl a0))) lassoc) in
  if bir <> cir || air = bir then failwith "inconsistent regs" else
  let bundle = GENL[air; bir](end_itlist CONJ [a0;asuc;b0;bsuc;c0;csuc]) in
  let [l;e;g] = CONJUNCTS (CONV_RULE (REWRITE_CONV [ADD00])
    (MATCH_MP TRICOND_THM bundle)) in
  Lop (map (renormalize_vars o UNDISCH)
    (try[MATCH_MP ltgtjoin (CONJ l g); e] with Failure _ -> [l;e;g]));;

let tricond ls =
  let lassoc = map (fun l -> addr_of_line l,l) ls in
  map (fun l -> try tricond_line l lassoc with Failure _ -> l) ls ;;

let LINES_OF_SUB_SIMP = memo_fix (fun r addr ->
  LINES_OF_SUB_C addr |> inline_sub r |> simplifycf |> decrloop_sub |>
  tricond |> simplifycf |> recognize_pairing);;

(* abstract interpretation *)

let curry_eq_tmevc =
  EQT_ELIM (SIMP_CONV[] `y -->_c z ==> x = y ==> x -->_c z`);;
let cond_eq_tmevc =
  EQT_ELIM (SIMP_CONV[] `(h ==> y -->_c z) ==> x = y ==> h ==> x -->_c z`);;
let cond_curried_tmevc =
  MATCH_MP (TAUT `(p/\q==>r)==>(h==>q)==>p==>(h==>r)`) TMEVC_TRANS;;

let abstract_interpret lines rwths hyths =
  let lassoc = map (fun l -> addr_of_line l,l) lines in
  let impcon = `-->_c` in
  let try_clause t cl =
    let cl' = match subtract (hyp cl) (hyp t) with
      (h::hs) -> DISCH h cl | [] -> cl in
    let rule = if is_eq (concl t) then
      if is_imp (concl cl') then cond_eq_tmevc else curry_eq_tmevc else
      if is_imp (concl cl') then cond_curried_tmevc else curried_tmevc in
    let cv = RAND_CONV (REWRITE_CONV rwths) in
    let cv' = if is_imp (concl cl') then
      BINOP2_CONV (REWRITE_CONV hyths) cv THENC REWRITE_CONV[] else cv in
    let rw = CONV_RULE cv' (MATCH_MP (MATCH_MP rule cl') t) in
    if rator (rator (concl rw)) = impcon then rw else fail() in
  let rec try_clauses t = function
    cl1::rest -> (try try_clause t cl1
      with Failure _ -> try_clauses t rest)
  | _ -> fail() in
  let step t =
    let nexta = lhand (rand (concl t)) in
    let l2 = assoc nexta lassoc in
    let clauses = match l2 with Lop tt -> tt | _ -> failwith "sub" in
    try_clauses t clauses in
  step;;

(** logic state setup and evolution rules
    this should be the only part with deep knowledge of zf2.nql compilation *)

let entry_pc_tm = `[F;F;F;F;T;F;F;F;F;F;F;F;F;F;F;F;F]`;;

let unsub_thm = PROVE_HYP DISPATCH_ROOT o
  INST [`[]:bool list`,`pc:bool list`];;
let unsub_line = function Lsub t -> Lsub (unsub_thm t)
                        | Lop tt -> Lop (map unsub_thm tt);;

let CFSTSND0 = prove(`CFST 0 = 0 /\ CSND 0 = 0`, REWRITE_TAC[CFSTSND]);;

let NOT1_CHECK = prove(`(x = 0 \/ x = SUC (SUC (PRE (PRE x))) <=>
  ~(x = (0 <> 0) <> 1)) /\ (x = SUC 0 <=> x = (0 <> 0) <> 1)`,
  REWRITE_TAC[CPAIR_DEF] THEN ARITH_TAC);;
let TRY_COMBINE =
  let OR_SIMP = TAUT `p \/ q /\ ~p <=> p \/ q` in
  let OR_MIDDLE = TAUT `~p /\ ~q \/ p \/ q` in
  let OR_MIDDLE2 = TAUT `~p /\ ~q /\ r \/ (p \/ q) /\ r <=> r` in
  let combine_t = TAUT `(p ==> r) ==> (q ==> r) ==> (p \/ q) ==> r` in
  let undisch_t0 = TAUT `p ==> T ==> p` in
  let undisch_t2 = TAUT `(p ==> q ==> r) ==> (q /\ p) ==> r` in
  let rec DISCH_CONJ thm = match hyp thm with [] -> MATCH_MP undisch_t0 thm |
    h::_ -> MATCH_MP undisch_t2 (DISCH_CONJ (DISCH h thm)) in
  fun rws thm1 thm2 ->
    if not (aconv (concl thm1) (concl thm2)) then [thm1; thm2] else
    let rws' = rws @ [GSYM LEFT_OR_DISTRIB; GSYM RIGHT_OR_DISTRIB; NOT1_CHECK;
      EXCLUDED_MIDDLE; CONJ_ACI; OR_SIMP; OR_MIDDLE; OR_MIDDLE2] in
    [PROVE_HYP TRUTH (UNDISCH (CONV_RULE (LAND_CONV (REWRITE_CONV rws'))
      (MATCH_MP (MATCH_MP combine_t (DISCH_CONJ thm1)) (DISCH_CONJ thm2))))];;

let COMBINE rws thm1 thm2 = match TRY_COMBINE rws thm1 thm2
  with [t] -> t | _ -> failwith("COMBINE");;

let CPAIR_EQ = prove(`!x y a b. x <> y = a <> b <=> x = a /\ y = b`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN STRIP_TAC THEN
  CONV_TAC (ONCE_DEPTH_CONV (SUBS_CONV (CONJUNCTS
   (GSYM (SPECL [`x:num`;`y:num`] CFSTSNDP))))) THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[CFSTSNDP]);;

let LSTATE = define
 `LS pl np ws = UNIONS {RS [F;F;F;F;T;F;F;F;F;F;F;F;F;F;F;F;F]
    [pl; 0; 0; np; ot2; oaxc; op1; op2; op3; CSND ws; CFST ws; 0] |
    ot2,oaxc,op1,op2,op3 | T}`;;

let TMEVC_ABS = prove(
 `(!a. a IN A ==> (?b. b IN B /\ a -->_c b)) ==> UNIONS A -->_c UNIONS B`,
  REWRITE_TAC[TMEVC_DEF; FORALL_IN_UNIONS; EXISTS_IN_UNIONS] THEN
  MESON_TAC[]);;

let TMEVC_ABSR1 = prove(
 `(!a. a IN A ==> (?b. b IN B /\ A -->_c b)) ==> A -->_c UNIONS B`,
  REWRITE_TAC[TMEVC_DEF; EXISTS_IN_UNIONS] THEN MESON_TAC[]);;

let TMEVC_ABSL = prove(`UNIONS A -->_c B <=> !a. a IN A ==> a -->_c B`,
  REWRITE_TAC[TMEVC_DEF; FORALL_IN_UNIONS] THEN MESON_TAC[]);;
let TMEVC_UNL = prove(`A UNION B -->_c C <=> A -->_c C /\ B -->_c C`,
  REWRITE_TAC[TMEVC_DEF; IN_UNION] THEN MESON_TAC[]);;

let LSTATE_LIFT = prove(
 `(!ot2 oaxc op1 op2 op3. RS [F;F;F;F;T;F;F;F;F;F;F;F;F;F;F;F;F]
       [pl; 0; 0; np; ot2; oaxc; op1; op2; op3; ws; tw; 0] -->_c
     RS[F;F;F;F;T;F;F;F;F;F;F;F;F;F;F;F;F]
       [pl'; 0; 0; np'; ot2'; oaxc'; op1'; op2'; op3'; ws'; tw'; 0]) ==>
  LS pl np (tw <> ws) -->_c LS pl' np' (tw' <> ws')`,
  REWRITE_TAC[LSTATE] THEN DISCH_TAC THEN MATCH_MP_TAC TMEVC_ABS THEN
  REWRITE_TAC[IN_ELIM_THM; CFSTSNDP] THEN ASM_MESON_TAC[]);;

let LSTATE_INIT = prove(`{initial} -->_c LS 0 0 (0 <> 0)`,
  MP_TAC INITIAL_RS THEN REWRITE_TAC[LSTATE; TMEVC_DEF; IN_UNIONS;
    IN_SING; IN_ELIM_THM; CFSTSNDP] THEN MESON_TAC[]);;

let LSTATE_LIFTH = prove(
 `(!ot2 oaxc op1 op2 op3. RS [F;F;F;F;T;F;F;F;F;F;F;F;F;F;F;F;F]
       [pl; 0; 0; np; ot2; oaxc; op1; op2; op3; ws; tw; 0] -->_c {halted}) ==>
  LS pl np (tw <> ws) -->_c {halted}`,
  REWRITE_TAC[LSTATE; TMEVC_ABSL] THEN DISCH_TAC THEN
  REWRITE_TAC[IN_ELIM_THM; CFSTSNDP] THEN ASM_MESON_TAC[]);;

let LSTATE_LOOP_THMS =
  print_string "This step may take over a minute\n";
  let lines = force_inline LINES_OF_SUB_SIMP (LINES_OF_SUB_SIMP (448,0)) |>
    map unsub_line in
  let dlines = filter (fun l -> addr_of_line l <> entry_pc_tm) lines in
  let do_ai_first a1 a2 t = repeat(abstract_interpret lines
    (ADD00 :: CFSTSNDP :: CFSTSND0 :: a1) a2) t in
  let do_ai a1 a2 t = repeat(abstract_interpret dlines
    (ADD00 :: CFSTSNDP :: CFSTSND0 :: a1) a2) t in
  let base_init_t = REFL `RS [F;F;F;F;T;F;F;F;F;F;F;F;F;F;F;F;F]
    [pl; 0; 0; np; ot2; oaxc; op1; op2; op3; ws1 <> ws; tw; 0]` in
  let do_axc t =
    if not(vfree_in `axc:num` (concl t)) then [t] else
    let sucify n = funpow n (fun tm -> mk_comb(`SUC`,tm)) in
    map (fun axc -> INST[sucify axc `0`,`axc:num`] t) (0 -- 17) @
    [INST[sucify 18 `axcp:num`,`axc:num`] t] in
  let do_mp t =
    let [_; _; _; _; _; _; p1; p2; p3; _; _; _] =
      dest_list (rand (rand (concl t))) in
    let cond = mk_eq(mk_binop `<>` (mk_binop `<>` p3 p1) `2`, p2) in
    TRY_COMBINE [] (do_ai [] [ASSUME cond] t)
      (do_ai [] [ASSUME (mk_neg cond)] t) in
  let do_b6a t =
    let [_; _; _; _; _; _; p1; p2; p3; _; _; _] =
      dest_list (rand (rand (concl t))) in
    let p1p3 = mk_eq(p1,p3) and p2p3 = mk_eq(p2,p3) in
    TRY_COMBINE [] (do_ai [] [ASSUME (mk_conj(mk_neg(p1p3),mk_neg(p2p3)))] t)
      (COMBINE [] (do_ai [] [ASSUME(p1p3)] t)
        (do_ai [] [ASSUME(mk_conj(mk_neg(p1p3),p2p3))] t)) in
  let do_check t =
    let rlist = rand (rand (concl t)) in
    let [_; _; _; _; _; _; _; _; _; _; tw; _] = dest_list rlist in
    if tw = `0` then [t] else
    let twcase v =
      let cv eq = funpow 4 RAND_CONV (LAND_CONV (ONCE_REWRITE_CONV [eq])) in
      do_ai [] [NOT1_CHECK] (CONV_RULE (cv(ASSUME(mk_eq(tw,v)))) t) in
    let nonhalt = COMBINE [CPAIR_EQ; ARITH_EQ] (twcase `0`)
      (twcase (vsubst [tw,`q:num`] `SUC (SUC (PRE (PRE q)))`)) in
    if is_var tw then [nonhalt; twcase `SUC 0`] else [nonhalt] in
  let to_ls thm =
    try DISCH_ALL (MATCH_MP LSTATE_LIFT (GENL [`ot2:num`; `oaxc:num`;
          `op1:num`; `op2:num`;`op3:num`] thm))
    with Failure _ ->
    try DISCH_ALL (MATCH_MP LSTATE_LIFTH (GENL [`ot2:num`; `oaxc:num`;
          `op1:num`; `op2:num`;`op3:num`] thm))
    with Failure _ -> thm in
  [INST[`SUC (axc <> p1 <> p2 <> p3 <> pl)`,`pl:num`] base_init_t;
  INST[`SUC (axc <> p1 <> p2 <> p3 <> pl)`,`np:num`;`0`,`pl:num`] base_init_t;
  INST[`0`,`np:num`;`0`,`pl:num`] base_init_t] |>
  map (do_ai_first [ARITH_SUC] []) |> map do_axc |> flat |>
  map (do_ai [] []) |> map do_mp |> flat |> map do_b6a |> flat |>
  map do_check |> flat |> map to_ls |>
  map (CONV_RULE (REWRITE_CONV [ADD1; ADD_AC] THENC NUM_REDUCE_CONV));;

(* wffs, wff encoding, axioms and provability *)

let wff_INDUCT, wff_RECURSION = define_type "wff = =: num num | @: num num |
  ==>: wff wff | ~: wff | !: num wff | ATOM num";;
parse_as_infix("=:",(22,"right"));;
parse_as_infix("@:",(22,"right"));;
parse_as_infix("/\:",(21,"right"));;
parse_as_infix("==>:",(16,"right"));;
parse_as_infix("<=>:",(13,"right"));;

let ENCODE_WFF = define
 `encode_wff (x =: y) = (x <> y) <> 0 /\
  encode_wff (x @: y) = (x <> y) <> 1 /\
  encode_wff (p ==>: q) = (encode_wff p <> encode_wff q) <> 2 /\
  encode_wff (~: p) = encode_wff p <> 3 /\
  encode_wff (!: x p) = (x <> encode_wff p) <> 4 /\
  encode_wff (ATOM n) = CFST n <> (5 + CSND n)`;;

let AXIOMS = end_itlist CONJ (map (define o parse_term) [
  `?: x p = ~: (!: x (~: p)):`;
  `p /\: q = ~: (p ==>: ~: q):`;
  `p <=>: q = (p ==>: q) /\: (q ==>: p):`;

  `axB1 ph ps ch = (ph ==>: ps) ==>: (ps ==>: ch) ==>: ph ==>: ch:`;
  `axB2 ph = (~: ph ==>: ph) ==>: ph:`;
  `axB3 ph ps = ph ==>: ~: ph ==>: ps:`;
  `axB4 x ph ps = !: x (ph ==>: ps) ==>: !: x ph ==>: !: x ps:`;
  `axB6a x y z = (x =: y ==>: !: z (x =: y)) /\:
    (x @: y ==>: !: z (x @: y)):`;
  `axB6b x y ph = !: x (!: y ph) ==>: !: y (!: x ph):`;
  `axB6c x ph = ?: x (!: x ph) ==>: ph:`;
  `axB7 x y = ?: x (x =: y):`;
  `axB8a x y z = x =: y ==>: x =: z ==>: y =: z:`;
  `axB8b x y z = x =: y ==>: x @: z ==>: y @: z:`;
  `axB8c x y z = x =: y ==>: z @: x ==>: z @: y:`;
  `axEXT = !: 2 (2 @: 0 <=>: 2 @: 1) ==>: 0 =: 1:`;
  `axREP ph = !: 3 (?: 1 (!: 2 (!: 1 ph ==>: 2 =: 1))) ==>:
     ?: 1 (!: 2 (2 @: 1 <=>: ?: 3 (3 @: 0 /\: !: 1 ph))):`;
  `axPOW = ?: 1 (!: 2 (!: 3 (3 @: 2 ==>: 3 @: 0) ==>: 2 @: 1)):`;
  `axUNI = ?: 1 (!: 2 (?: 3 (2 @: 3 /\: 3 @: 0) ==>: 2 @: 1)):`;
  `axINF = ?: 1 ((0 @: 1) /\: !: 0 (0 @: 1 ==>:
    ?: 2 ((2 @: 1) /\: !: 1 (1 @: 2 <=>: 1 =: 0)))):`]);;

let provable, provable_INDUCT, provable_CASES = new_inductive_definition
 `(!ph ps. provable (ph ==>: ps) /\ provable ph ==> provable ps) /\
  (!x ph. provable ph ==> provable (!: x ph)) /\

  (!ph ps ch. provable (axB1 ph ps ch)) /\
  (!ph. provable (axB2 ph)) /\ (!ph ps. provable (axB3 ph ps)) /\

  (!x ph ps. provable (axB4 x ph ps)) /\
  (!x y z. ~(x = z) /\ ~(y = z) ==> provable (axB6a x y z)) /\
  (!x y ph. provable (axB6b x y ph)) /\ (!x ph. provable (axB6c x ph)) /\
  (!x y. provable (axB7 x y)) /\ (!x y z. provable (axB8a x y z)) /\
  (!x y z. provable (axB8b x y z)) /\ (!x y z. provable (axB8c x y z)) /\

  provable axEXT /\ (!ph. provable (axREP ph)) /\ provable axPOW /\
  provable axUNI /\ provable axINF`;;

let encode_wffstack = define
 `encode_wffstack [] = 0 /\
  encode_wffstack (w::ws) = encode_wff w <> encode_wffstack ws`;;

let cconcl = concl o UNDISCH_ALL;;

let PUSH0 = prove(`0 <> encode_wffstack l = encode_wffstack (0 =: 0 :: l)`,
  REWRITE_TAC[encode_wffstack; ENCODE_WFF; CPAIR_REC]);;

let encode_wff_11 = prove(`!ph ps. encode_wff ph = encode_wff ps <=> ph = ps`,
  MATCH_MP_TAC wff_INDUCT THEN REPEAT STRIP_TAC THEN
  SPEC_TAC(`ps:wff`,`ps:wff`) THEN MATCH_MP_TAC wff_INDUCT THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ENCODE_WFF; CPAIR_EQ;
    injectivity "wff"; distinctness "wff"; EQ_ADD_LCANCEL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN TRY ARITH_TAC THEN
  SPEC_TAC(`a:num`,`a:num`) THEN MATCH_MP_TAC CPAIR_INDUCT2 THEN
  REPEAT STRIP_TAC THEN
  SPEC_TAC(`a':num`,`a':num`) THEN MATCH_MP_TAC CPAIR_INDUCT2 THEN
  REPEAT STRIP_TAC THEN SIMP_TAC[CFSTSNDP; CPAIR_EQ]);;

let wffeq1 = prove(`encode_wff pp = 1 <=> pp = 0 @: 0`,
  REWRITE_TAC[SYM((REWRITE_CONV [CPAIR_DEF; ENCODE_WFF] THENC
    NUM_REDUCE_CONV) `encode_wff (0 @: 0)`); encode_wff_11]);;

let WSTATE_LOOP_THMS =
  let rec prune_ws t =
    let rec tail tm = if is_binop `<>` (rand tm) then tail (rand tm) else tm in
    let st = rand (cconcl t) in
    let ttail = if st <> `{halted}` then tail (rand st) else
      tail (rand (lhand (cconcl t))) in
    if not (is_var (lhand ttail)) then t else
    if mem (lhand ttail) (freesl (hyp (UNDISCH_ALL t))) then t else
    prune_ws (DISCH_ALL (SPEC_ALL (MATCH_MP CPAIR_INDUCT2
      (GENL [lhand ttail;rand ttail] (UNDISCH_ALL t))))) in
  let decode t =
    let sps = lhand (rator (lhand (cconcl t))) in
    let sps = if sps = `0` then lhand (lhand (cconcl t)) else sps in
    let ax = try dest_small_numeral (lhand (lhand sps)) with Failure _ -> 18 in
    let t = if ax = 15 || ax = 1 || ax >= 3 && ax <= 5 then INST[`encode_wff pp1`,`p1:num`] t else t in
    let t = if ax = 3 || ax = 5 || ax = 6 || ax = 9 then INST[`encode_wff pp2`,`p2:num`] t else t in
    let t = if ax = 3 || ax = 6 || ax = 8 then INST[`encode_wff pp3`,`p3:num`] t else t in
    let wind,wstk = splitlist (dest_binop `<>`) (rand (lhand (cconcl t))) in
    let w2e v = mk_comb(`encode_wff`,mk_var(name_of v,`:wff`)),v in
    INST ((`encode_wffstack wstk`,wstk) :: map w2e wind) t in
  LSTATE_LOOP_THMS |> map prune_ws |> map decode |>
  map (CONV_RULE (REWRITE_CONV[GSYM ENCODE_WFF; GSYM AXIOMS;
    SYM (CONJUNCT2 encode_wffstack); PUSH0; encode_wff_11; wffeq1]));;

(* propositional completeness *)

let [axMPa; axGEN; axB1; axB2; axB3; axB4; axB6a; axB6b; axB6c; axB7; axB8a;
  axB8b; axB8c; axEXT; axREP; axPOW; axUNI; axINF] = CONJUNCTS provable;;
let axMP = MATCH_MP (TAUT `(p/\q==>r)==>p==>q==>r`) (SPEC_ALL axMPa);;

let UNIFY_MP maj min =
  let smaj = SPEC_ALL maj and smin = SPEC_ALL min in
  let avoiding tref t =
    let renable = subtract (frees (concl t)) (freesl (hyp t)) in
    let renamed = variants (thm_frees tref) renable in
    INST (zip renamed renable) t in
  let rmaj = avoiding smin smaj in
  let rmin = avoiding rmaj smin in
  let majb,majt = strip_forall (lhand (concl rmaj)) in
  let rbmap = zip majb (variants
    (union (thm_frees rmaj) (thm_frees rmin)) majb) in
  let rmajb = map (subst rbmap) majb in
  let rmajt = subst rbmap majt in
  let (_,tmin,tyin) = term_type_unify rmajt (concl rmin) ([],[],[]) in
  let imag = INST tmin (INST_TYPE tyin rmaj) in
  let imin = INST tmin (INST_TYPE tyin rmin) in
  let gimin = GENL (map (vsubst tmin o inst tyin) rmajb) imin in
  MP imag gimin ;;

let DRULE ps =
  let rec apply p stk = if is_imp (concl (SPEC_ALL p)) then
    let lh = lhand (concl (SPEC_ALL p)) in
    if is_comb lh && rator lh = `provable` then
    apply (UNIFY_MP p (hd stk)) (tl stk) else
    apply (UNIFY_MP p (ASSUME `p:bool`)) stk else p::stk in
  match (itlist apply (map (CONV_RULE (REWRITE_CONV [AXIOMS])) ps) [])
    with [t] -> DISCH_ALL t | _ -> failwith "bad stack" ;;

let wASM t = ASSUME (mk_comb(`provable`,t));;
let wLUK1 = DRULE [axMP; axMP; axB1; wASM `c ==>: b`; wASM `b ==>: a`];;
let wLUK2 = DRULE [wLUK1; wLUK1; axB1; axMP; axB1; axB3; axB1];;
let wLUK3 = DRULE [wLUK1; axB3; wLUK2];;
let wLUK4 = DRULE [wLUK1; axMP; axB1; axMP; axMP; wLUK3; axB2; axB2; axB2];;
let wKCOM = DRULE [wLUK1; wLUK3; wLUK4];;
let wWCOM = DRULE [wLUK1; axB1; axMP; wLUK4; axMP; axB1; axMP; axB1;
  wLUK1; wKCOM; wLUK1; wLUK2; wLUK4];;
let wCCOM = DRULE [wLUK1; axB1; axMP; axB1; wLUK1; wLUK1; wKCOM; axB1; wWCOM];;
let wBCOM = DRULE [axMP; wCCOM; axB1];;
let wSCOM = DRULE [wLUK1; wCCOM; wLUK1; wBCOM; axMP; wBCOM; wWCOM];;
let wCON4 = DRULE [wLUK1; wLUK2; wLUK4];;
let wNNTR = DRULE [axMP; wWCOM; wLUK1; axMP; wCCOM; axB3; wCON4];;
let wCON2 = DRULE [wLUK1; axMP; axB1; wNNTR; wCON4];;
let wID   = DRULE [wLUK1; axB3; axB2];;
let wNNOT = DRULE [axMP; wCON2; wID];;
let wCON3 = DRULE [wLUK1; axMP; wBCOM; wNNOT; wCON4];;
let wCON1 = DRULE [wLUK1; axMP; axB1; wNNTR; wCON3];;
let wCASE = DRULE [axMP; axB2; wLUK1; axMP; wCON3; wASM`w:wff`; wASM`w:wff`];;

let wTAUT =
  let lift0 = UNIFY_MP axMP wKCOM in
  let lift1 = UNIFY_MP axMP wBCOM in
  let lift2 = DRULE [axMP; axMP; wBCOM; wSCOM; axMP; wBCOM; wASM `w:wff`] in
  let liftK = DRULE [axMP; axMP; wBCOM; wKCOM; wASM `w:wff`] in
  let baseIM1 = DRULE [axMP; wCCOM; axB3] in
  let baseIM3 = DRULE [wLUK1; axMP; wCCOM; wID; wCON1] in
  fun fm ->
  let exp = PURE_REWRITE_CONV [AXIOMS] (mk_comb(`provable`,fm)) in
  let expfm = rand (rhs (concl exp)) in
  let rec atoms subtm =
    try let x,y = dest_binop `==>: ` subtm in union (atoms x) (atoms y)
    with Failure _ -> if is_comb subtm && rator subtm = `~: `
      then atoms (rand subtm) else [subtm] in
  let allat = atoms expfm in
  let rec prove subtm (atv,im1,im2,im3,n1,_) as cx =
    if is_binop `==>: ` subtm then
      let nl,pl = prove (lhand subtm) cx in
      let nr,pr = prove (rand subtm) cx in
      if nl then false,UNIFY_MP (UNIFY_MP axMP im1) pl else
      if not nr then false,UNIFY_MP (UNIFY_MP axMP im2) pr else
      true,UNIFY_MP (UNIFY_MP axMP (UNIFY_MP (UNIFY_MP axMP im3) pl)) pr else
    if is_comb subtm && rator subtm = `~: ` then
      let n,p = prove (rand subtm) cx in
      if n then false,p else true,UNIFY_MP (UNIFY_MP axMP n1) p else
    rev_assoc subtm atv in
  let rec analyze atoms (atv,im1,im2,im3,n1,k) as cx = match atoms with
      [] -> let n,prf = prove expfm cx in
            if n then failwith "not a tautology" else prf
    | (a::ats) ->
      let im1' = UNIFY_MP lift1 im1 in let im2' = UNIFY_MP lift1 im2 in
      let im3' = UNIFY_MP lift2 im3 in let n1' = UNIFY_MP lift1 n1 in
      let atv' = map (fun (n,t),a -> (n,UNIFY_MP lift0 t),a) atv in
      let k' = UNIFY_MP liftK k in
      let ptrue = analyze ats (((false,k),a)::atv',im1',im2',im3',n1',k') in
      let pfals = analyze ats (((true,k),a)::atv',im1',im2',im3',n1',k') in
      UNIFY_MP (UNIFY_MP wCASE pfals) ptrue in
  let gprf = analyze allat ([],baseIM1,wKCOM,baseIM3,wNNOT,wID) in
  let cprf = UNIFY_MP (DISCH_ALL (ASSUME (rhs (concl exp)))) gprf in
  EQ_MP (SYM exp) (INST (zip allat (atoms (rand (concl cprf)))) cprf) ;;

(* predicate "completeness" *)

let wEXIM = DRULE [wLUK1; axMP; axB4; axGEN; wCON1; wLUK1; axB4; wCON1];;
let wSIMPL = wTAUT `p /\: q ==>: p`;;
let wSIMPR = wTAUT `p /\: q ==>: q`;;

let rec axB6 tm =
  if is_binop `=: ` tm then
  DRULE[axMP; wSIMPL; axB6a] else
  if is_binop `@: ` tm then
  DRULE[axMP; wSIMPR; axB6a] else
  if is_binop `==>: ` tm then
  DRULE[axMP; axMP; axMP; axMP;
    wTAUT `(!: z (~: x) ==>: !: z (x ==>: y)) ==>:
      (!: z y ==>: !: z (x ==>: y)) ==>: (~: x ==>: !: z (~: x)) ==>:
      (y ==>: !: z y) ==>: (x ==>: y) ==>: !: z (x ==>: y)`;
    axMP; axB4; axGEN; axMP; wCCOM; axB3;
    axMP; axB4; axGEN; wKCOM;
    axB6 (mk_comb(`~: `,lhand tm)); axB6 (rand tm)] else
  if is_binop `!: ` tm then
  DRULE[wLUK1; axMP; axB4; axGEN; axB6 (rand tm); axB6b] else
  if is_comb tm && rator tm = `~: ` then
  DRULE[axMP; wCON3; wLUK1; axMP; wEXIM; axGEN; axB6 (rand tm); axB6c] else
  failwith "defined / p-atom / non-ground in axB6" ;;

let axB6e tm = DRULE[axMP; wCON3; axB6 (mk_comb(`~: `,tm))];;
let wEQRF = UNIFY_MP (DRULE[axMP; axMP; wCON3; axB6 `~: (y =: y)`; axMP;
  axMP; wEXIM; axGEN; axMP; wWCOM; axB8a; axB7])
  (ARITH_RULE `~(x = SUC x) /\ ~(x = SUC x)`);;
let wEQSM = DRULE[axMP; axMP; wCCOM; axB8a; wEQRF];;
let wB8a2 = DRULE[axMP; axMP; wBCOM; axMP; wBCOM; wEQSM; axMP; axMP; wBCOM;
  axMP; axMP; wCCOM; wBCOM; wEQSM; axB8a];;

let wGENE = DRULE[axMP; axMP; wEXIM; axGEN; axMP; wKCOM; wASM `w:wff`; axB7];;
let wMTO = DRULE[axMP; axMP; wCON1; wASM `w:wff`; wASM `w:wff`];;

let wNUL1 = DRULE[axGEN; wGENE; axGEN; axMP; axMP; wCCOM; axB3; axB7];;
let wNUL2 = DRULE[axMP; wTAUT `~: ps ==>: (ph <=>: ps) ==>: ~: ph`;
  wMTO; axMP; wEXIM; axGEN; wSIMPR; wMTO; axB6e `!: 1 (~: (1 =: 1))`; axB7]
let wNUL = MATCH_MP (DRULE[axMP; axMP; wEXIM; axGEN; axMP; axB4; axGEN;
  wNUL2; axMP; axREP; wNUL1]) (ARITH_RULE `~(1 = 3) /\ ~(1 = 3)`);;

let wB321 = wTAUT `(c==>:a)==>:(b==>:d)==>:(a==>:b)==>:(c==>:d)`;;
let wSYLK = wTAUT `(a==>:b==>:c)==>:(a==>:c==>:d)==>:a==>:b==>:d`;;
let wIDK = wTAUT `a==>:b==>:b`;;
let rec wINST v tm =
  if is_binop `!: ` tm then
  DRULE[wLUK1; axB6 `x =: y`; axMP; axB4; axGEN; wINST v (rand tm)] else
  if is_binop `==>: ` tm then
  DRULE[axMP; axMP; wB321; wINST v (lhand tm); wINST v (rand tm)] else
  if is_binop `=: ` tm then
  DRULE[axMP; axMP; wSYLK; if lhand tm = v then axB8a else wIDK;
    if rand tm = v then wB8a2 else wIDK] else
  if is_binop `@: ` tm then
  DRULE[axMP; axMP; wSYLK; if lhand tm = v then axB8b else wIDK;
    if rand tm = v then axB8c else wIDK] else
  if is_comb tm && rator tm = `~: ` then
  DRULE[wLUK1; wLUK1; wEQSM; wINST v (rand tm); wCON1] else
  failwith "p-atom or non-ground in wINST";;

let wSPEC v tm = DRULE[wLUK1; axMP; axB4; axGEN; axMP; wCCOM; wINST v tm;
  wLUK1; axMP; axMP; wCCOM; wEXIM; axB7; axB6e tm];;
let wCBVA v w tm = DRULE[wLUK1; axB6 (mk_comb(mk_comb(`!: `,w),tm));
  axMP; axB4; axGEN; wSPEC v tm];;
let wNOT1A = MATCH_MP (DRULE[axMP; axMP; wEXIM; axGEN;
  wSPEC `2` `~: (2 @: 1)`; wNUL]) (ARITH_RULE `~(1 = 2) /\ ~(1 = 2)`);;
let wNOT1 = MATCH_MP (MATCH_MP (DRULE[wMTO; wCBVA `1` `0` `1 @: 1`; wMTO;
  axMP; axB4; axGEN; wNNOT; wNOT1A]) (ARITH_RULE `~(1 = 0)`))
  (ARITH_RULE `~(0 = 1)`);;
let wEXP1 = DRULE[axMP; axMP; axB3; axGEN; wASM `0 @: 0`; wNOT1];;

(* machine soundness *)

let NOWFFSTATE = define`NWS pl np = {halted | provable (0 @: 0)} UNION
  UNIONS {LS pl np (encode_wffstack ws) | ws | ALL provable ws}`;;

let NWS_ABSNH_R = prove(
 `(pred ==> A -->_c LS pl np (encode_wffstack ws)) ==>
  pred /\ ALL provable ws ==> A -->_c NWS pl np`,
  BOOL_CASES_TAC `pred:bool` THEN SIMP_TAC[] THEN
  REWRITE_TAC[TMEVC_DEF; NOWFFSTATE; IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let NWS_ABSH_R = prove(
 `(pred ==> A -->_c {halted}) ==>
  pred /\ provable (0 @: 0) ==> A -->_c NWS pl np`,
  BOOL_CASES_TAC `pred:bool` THEN SIMP_TAC[] THEN REWRITE_TAC[TMEVC_DEF;
    NOWFFSTATE; IN_UNION; IN_UNIONS; IN_ELIM_THM; IN_SING] THEN
  MESON_TAC[]);;

let ASC_THM = TAUT `(p ==> r) /\ (q ==> r) ==> (p \/ q) ==> r`;;
let rec ADJ_SAME_CONCL ts = match ts with (t1::t2::trest) ->
    let t12 = try Some (UNIFY_MP ASC_THM (CONJ t1 t2))
    with Failure _ -> None in
    (match t12 with Some tt -> ADJ_SAME_CONCL (tt::trest)
                  | None -> t1::ADJ_SAME_CONCL (t2::trest))
  | _ -> ts ;;

(* how exactly does this work? *)
let ss_with_and = ss_of_congs [TAUT `(p <=> p') ==> (p' ==> (q <=> q')) ==> (p /\ q <=> p' /\ q')`] (basic_ss []);;

let NWSB6A = prove(
 `(~(p1 = p3) /\ ~(p2 = p3)) /\ provable (axB6a p1 p2 p3) /\ ALL provable wstk
   \/ (p1 = p3 \/ p2 = p3) /\ ALL provable wstk <=> ALL provable wstk`,
  CONV_TAC (SIMPLIFY_CONV ss_with_and[GSYM DE_MORGAN_THM; provable]) THEN
  BOOL_CASES_TAC `p1:num = p3 \/ p2 = p3` THEN SIMP_TAC[]);;

let NWSMP = prove(
 `(((tw ==>: pp1 = ws1 /\ ~(pp1 = 0 @: 0)) /\ provable pp1 /\
  ALL provable wstk \/ (tw ==>: pp1 = ws1 /\ pp1 = 0 @: 0) /\
  provable (0 @: 0)) \/ ~(tw ==>: pp1 = ws1) /\ ALL provable wstk ==> R)
  ==> ALL provable (tw::ws1::wstk) ==> R`,
  ASM_CASES_TAC `tw ==>: pp1 = ws1` THEN ASM_SIMP_TAC[ALL] THEN
  POP_ASSUM (SUBST1_TAC o SYM) THEN ASM_CASES_TAC `pp1 = 0 @: 0` THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN ASM IMP_REWRITE_TAC[] THEN
  BOOL_CASES_TAC `ALL provable wstk` THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  SIMP_TAC[] THEN MATCH_ACCEPT_TAC (CONJUNCT1 provable));;

let NWSGEN = prove(`(provable (!: p1 tw) /\ ALL provable wstk ==> R) ==>
  ALL provable (tw::wstk) ==> R`,
  DISCH_TAC THEN ASM IMP_REWRITE_TAC[ALL] THEN
  IMP_REWRITE_TAC[el 1 (CONJUNCTS provable)]);;

let CPAIR_LE = prove(`!x y. x <= x <> y /\ y <= x <> y`,
  MATCH_MP_TAC CPAIR_INDUCT THEN SIMP_TAC[CPAIR_REC; LE_SUC; LE_0] THEN
  ARITH_TAC);;
let CFSTSND_LE = prove(`!p. CFST p <= p /\ CSND p <= p`,
  MATCH_MP_TAC CPAIR_INDUCT2 THEN REWRITE_TAC[CFSTSNDP; CPAIR_LE]);;

let CFST_LT = prove(`CFST p < p <=> ~(p = 0)`,
  STRUCT_CASES_TAC (SPEC `p:num` num_CASES) THEN
  REWRITE_TAC[CFSTSND0; NOT_SUC; LT_REFL] THEN
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
  CONV_TAC (ONCE_REWRITE_CONV[CFSTSND]) THENL [
    REWRITE_TAC[CFSTSND; LT_0];
    STRUCT_CASES_TAC (SPEC `CSND (SUC n)` num_CASES) THEN
    ASM_REWRITE_TAC[LT_SUC; LT_0]]);;

let CFST2_LT = prove(`(CFST (CFST p) < p <=> ~(p = 0)) /\
    (CSND (CFST p) < p <=> ~(p = 0))`,
  ASM_CASES_TAC `p = 0` THEN ASM_SIMP_TAC[CFSTSND0; LT_REFL] THEN CONJ_TAC THEN
  TRANS_TAC LET_TRANS `CFST p` THEN ASM_SIMP_TAC[CFSTSND_LE; CFST_LT]);;

let DECODE_WFF =
  let rf = pure_prove_recursive_function_exists
   `?decode_wff. !i. decode_wff i =
      if CSND i = 0 then CFST (CFST i) =: CSND (CFST i) else
      if CSND i = 1 then CFST (CFST i) @: CSND (CFST i) else
      if CSND i = 2 then decode_wff (CFST (CFST i)) ==>:
        decode_wff (CSND (CFST i)) else
      if CSND i = 3 then ~: (decode_wff (CFST i)) else
      if CSND i = 4 then !: (CFST (CFST i)) (decode_wff (CSND (CFST i)))
      else ATOM (CFST i <> CSND i - 5)` in
  new_specification ["decode_wff"] (PROVE_HYP (prove(hd(hyp rf),
    EXISTS_TAC `<` THEN SIMP_TAC[CFST_LT; CFST2_LT; WF_num] THEN
    REPEAT CONJ_TAC THEN GEN_TAC THEN ASM_CASES_TAC `i = 0` THEN
    ASM_SIMP_TAC[CFSTSND0])) rf);;

let ENCODE_DECODE_WFF = prove(`!i. encode_wff (decode_wff i) = i`,
  MATCH_MP_TAC num_WF THEN REPEAT STRIP_TAC THEN
  CONV_TAC (ONCE_REWRITE_CONV[DECODE_WFF]) THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[ENCODE_WFF] THEN
  TRY (POP_ASSUM (SUBST1_TAC o SYM)) THEN
  TRY (ASM IMP_REWRITE_TAC[CPAIR; CFST_LT; CFST2_LT]) THEN
  TRY (STRIP_TAC THEN POP_ASSUM SUBST_ALL_TAC THEN
    REPEAT (POP_ASSUM MP_TAC) THEN REWRITE_TAC[CFSTSND0]) THEN
  IMP_REWRITE_TAC[CFSTSNDP; CPAIR; ARITH_RULE `5 <= x ==> 5 + x - 5 = x`] THEN
  ASM_ARITH_TAC);;

let WFFRESTACK = prove(
 `!ws. ?w ws'. encode_wffstack ws = encode_wffstack (w::ws') /\
    ALL provable ws = ALL provable (w::ws')`,
  LIST_INDUCT_TAC THENL [
    EXISTS_TAC `0 =: 0` THEN EXISTS_TAC `[]:wff list`;
    EXISTS_TAC `h:wff` THEN EXISTS_TAC `t:wff list`] THEN
  REWRITE_TAC[encode_wffstack; ALL; wEQRF; ENCODE_WFF; CPAIR_REC]);;

 (* ugly, but until we have more examples of {halted} handling *)
let NWS_ABS_L = prove(
 `(!x y ws. ALL provable (x::y::ws) ==>
    LS pl np (encode_wffstack (x::y::ws)) -->_c NWS pl' np') ==>
  NWS pl np -->_c NWS pl' np'`,
  STRIP_TAC THEN REWRITE_TAC[NOWFFSTATE; TMEVC_UNL] THEN
  CONJ_TAC THENL [
    REWRITE_TAC[TMEVC_DEF; IN_ELIM_THM] THEN CONV_TAC FORALL_UNWIND_CONV THEN
    STRIP_TAC THEN EXISTS_TAC `halted` THEN
    ASM_SIMP_TAC[IN_UNION; IN_ELIM_THM; HALTED_STICKY];

    REWRITE_TAC[TMEVC_ABSL; GSYM NOWFFSTATE; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    STRIP_ASSUME_TAC (SPEC `ws:wff list` WFFRESTACK) THEN
    STRIP_ASSUME_TAC (SPEC `ws':wff list` WFFRESTACK) THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`w:wff`;`w':wff`;`ws'':wff list`]) THEN
    REPEAT (POP_ASSUM MP_TAC) THEN SIMP_TAC[ALL; encode_wffstack]]);;

let IMPORT = TAUT `(p ==> q ==> r) ==> (p /\ q) ==> r`;; (* IMP_CONJ IMP_IMP *)
let TRY_MATCH_MP maj min = try MATCH_MP maj min with Failure _ -> min ;;
let TRY_UNIFY_MP maj min = try UNIFY_MP maj min with Failure _ -> min ;;
let ALL_AXCODES_CONV =
  let thm = ARITH_RULE `x = x - (n+1) + (n+1) \/ x = n <=> x = x - n + n` in
  fun tm ->
    let l,r = dest_binop `\/` tm in
    CONV_RULE NUM_REDUCE_CONV
      (INST[lhs r,`x:num`;rhs r,`n:num`] thm);;

let [NWSTATE_LOOP_0; NWSTATE_LOOP_NEXT; NWSTATE_LOOP_CONT] =
  WSTATE_LOOP_THMS
  |> map (TRY_MATCH_MP IMPORT)
  |> map (fun t -> if is_imp (concl t) then t else DISCH `T` t)
  |> map (TRY_UNIFY_MP NWS_ABSNH_R)
  |> map (TRY_UNIFY_MP NWS_ABSH_R)
  |> ADJ_SAME_CONCL
  |> map (CONV_RULE (REWRITE_CONV [provable; ALL; wEQRF; NWSB6A]))
  |> map (TRY_UNIFY_MP NWSMP)
  |> map (TRY_UNIFY_MP NWSGEN)
  |> map (TRY_UNIFY_MP NWS_ABS_L)
  |> map (INST[`decode_wff p1`,`pp1:wff`;`decode_wff p2`,`pp2:wff`;
               `decode_wff p3`,`pp3:wff`;`axc - 18`,`axcp:num`])
  |> map (CONV_RULE (REWRITE_CONV [ENCODE_DECODE_WFF]))
  |> map (fun t -> try DISCH_ALL (CONV_RULE (REWRITE_CONV
       [SYM(AP_TERM `<>` (ASSUME(mk_eq(`axc:num`, lhand
         (find_term (is_binop `<>`) (concl t))))))]) t)
       with Failure _ -> t)
  |> map (CONV_RULE (DEPTH_CONV ALL_AXCODES_CONV)) o ADJ_SAME_CONCL o rev
  |> map (CONV_RULE (REWRITE_CONV [SUB; ADD_CLAUSES]))
  ;;

 (* todo UNIFY_MP_EQ *)
 (* TMEVC operations based on subsets? *)
let NWSTATE_INIT = prove(`{initial} -->_c NWS 0 0`,
  MATCH_MP_TAC (INST [`T`,`pred:bool`;`[]:wff list`,`ws:wff list`]
    (CONV_RULE (REWRITE_CONV[IMP_IMP]) NWS_ABSNH_R)) THEN
  MP_TAC INITIAL_RS THEN SIMP_TAC[ALL; encode_wffstack] THEN
  REWRITE_TAC[TMEVC_DEF; LSTATE; CFSTSND0; EXISTS_IN_UNIONS; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let CPAIR_IND4 = prove(
 `!P. (!ax p1 p2 p3 np. P (ax <> p1 <> p2 <> p3 <> np)) ==> !p. P p`,
  STRIP_TAC THEN STRIP_TAC THEN REPLICATE_TAC 4
   (MATCH_MP_TAC CPAIR_INDUCT2 THEN GEN_TAC) THEN ASM_REWRITE_TAC[]);;

let NWSTATE_EACH_PROOF = prove(`NWS 0 n -->_c NWS 0 (n + 1)`,
  STRUCT_CASES_TAC (SPEC `n:num` num_CASES) THENL [
    REWRITE_TAC[ARITH; NWSTATE_LOOP_0]; ALL_TAC] THEN
  REWRITE_TAC[ADD1; ADD_AC] THEN CONV_TAC NUM_REDUCE_CONV THEN
  SPEC_TAC(`n':num`,`n':num`) THEN MATCH_MP_TAC CPAIR_IND4 THEN
  REPLICATE_TAC 4 GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[NWSTATE_LOOP_NEXT] THEN
  IMP_REWRITE_TAC[MATCH_MP EVOLVEC_TO_IMP NWSTATE_LOOP_NEXT] THEN
  SUBGOAL_THEN `!np pl. NWS (SUC pl) np -->_c NWS 0 np` MATCH_ACCEPT_TAC THEN

  GEN_TAC THEN REWRITE_TAC[ADD1] THEN MATCH_MP_TAC num_WF THEN
  MATCH_MP_TAC CPAIR_IND4 THEN REPLICATE_TAC 4 GEN_TAC THEN INDUCT_TAC THEN
  DISCH_TAC THEN ASM IMP_REWRITE_TAC[NWSTATE_LOOP_CONT;
    MATCH_MP EVOLVEC_TO_IMP NWSTATE_LOOP_CONT; ADD1] THEN

  SUBGOAL_THEN `!x y z. x < z ==> (x < y <> z) = T` ASSUME_TAC THENL [
    REPEAT STRIP_TAC THEN SIMP_TAC[] THEN TRANS_TAC LTE_TRANS `z:num` THEN
    ASM_SIMP_TAC[CPAIR_LE]; ASM IMP_REWRITE_TAC[LT_ADD] THEN ARITH_TAC]);;

let NWSTATE_ALL_PROOFS = prove(`!n. {initial} -->_c NWS 0 n`,
  INDUCT_TAC THEN EVOLVESC_TO_IMPS_TAC' THEN
  TRY (ASM IMP_REWRITE_TAC[]) THEN
  REWRITE_TAC[ADD1; NWSTATE_EACH_PROOF; NWSTATE_INIT]);;

 (* ugly *)
let TMEVC_HALT = prove(
  `{x} -->_c S /\ S -->_c S /\ x -->_w halted ==> halted IN S`,
  REWRITE_TAC[tm_evolves; RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  GEN_TAC THEN SPEC_TAC (`x:num#(int->bool)`,`x:num#(int->bool)`) THEN
  SPEC_TAC(`n:num`,`n:num`) THEN MATCH_MP_TAC num_WF THEN
  REWRITE_TAC[TMEVC_DEF; tm_evolves; RIGHT_AND_EXISTS_THM; IN_SING] THEN
  CONV_TAC (DEPTH_CONV (CHANGED_CONV FORALL_UNWIND_CONV)) THEN
  CONV_TAC (DEPTH_CONV (CHANGED_CONV UNWIND_CONV)) THEN
  REPEAT STRIP_TAC THEN
  DISJ_CASES_TAC (ARITH_RULE `SUC n <= SUC n' \/ n' < n`) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[LE_EXISTS; LT_EXISTS] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN STRIP_TAC THEN POP_ASSUM SUBST_ALL_TAC THEN
  WITH_ASSUMS (REWRITE_TAC [ITERF_ADD; ARITH_RULE `SUC(m+n)=m+SUC n`]) THENL [
    POP_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `ITERF d (gtm_step transition_table)
       halted = halted` SUBST_ALL_TAC THEN
    ASM_REWRITE_TAC[] THEN SPEC_TAC(`d:num`,`d:num`) THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC[ITERF_DEF; HALTED_STICKY1];

    FIRST_X_ASSUM (MP_TAC o SPEC `d:num`) THEN ASM_SIMP_TAC[] THEN
    ANTS_TAC THENL [ARITH_TAC; DISCH_THEN (MP_TAC o SPEC
      `ITERF (SUC n') (gtm_step transition_table) x`)] THEN
    ASM_MESON_TAC[]]);;

let RSTATE_NOT_HALT = prove(`~(halted IN RS pc regs)`,
  REWRITE_TAC[REGSTATE; IN_ELIM_THM; DISPSTATE; halted_DEF; PAIR_EQ] THEN
  ARITH_TAC);;

let MACHINE_SOUND = prove(`initial -->_w halted ==> provable (0 @: 0)`,
  DISCH_TAC THEN MP_TAC (SPECL [`initial`; `UNIONS {NWS 0 i|T}`]
    (GEN_ALL TMEVC_HALT)) THEN ASM_REWRITE_TAC[] THEN ANTS_TAC THEN
  TRY CONJ_TAC THENL [
    MATCH_MP_TAC TMEVC_ABSR1 THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MESON_TAC[NWSTATE_INIT];

    MATCH_MP_TAC TMEVC_ABS THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MESON_TAC[NWSTATE_EACH_PROOF];

    REPEAT (CONV_TAC (DEPTH_CONV (CHANGED_CONV UNWIND_CONV)) THEN
      REWRITE_TAC[IN_UNIONS; IN_UNION; IN_ELIM_THM; NOWFFSTATE; LSTATE;
        RSTATE_NOT_HALT; GSYM LEFT_EXISTS_AND_THM])]);;

(* machine completeness *)

let pick_encoding (_,w) =
  let wff = find_term (fun tm -> type_of tm = `:wff` && not (is_var tm)) w in
  let typ,_ = strip_comb wff in
  let thm = find (fun c -> can (find_term (fun t -> t = typ)) c &&
    lhand (rator (lhand c)) <> `0`) (map cconcl WSTATE_LOOP_THMS) in
  let base = instantiate (term_type_unify (lhand (rand (rand (rand thm)))) wff
    ([],[],[])) (lhand (rator (lhand thm))) in
  let base = if typ = `!: ` then mk_comb(`f:num->num`,base) else base in
  EXISTS_TAC(mk_abs(`pl:num`,base));;

let PROOFS_EXIST = prove(
 `!w. provable w ==> ?f.
    (!pl np ws. LS (f pl) np (encode_wffstack ws) -->_c {halted}) \/
    ~(w = 0 @: 0) /\ (!pl np ws. LS (f pl) np (encode_wffstack ws) -->_c
       LS pl np (encode_wffstack (w::ws)))`,
  MATCH_MP_TAC provable_INDUCT THEN REPEAT STRIP_TAC THEN
  TRY (EXISTS_TAC `f:num->num` THEN ASM_SIMP_TAC[] THEN NO_TAC) THEN
  TRY (EXISTS_TAC `f':num->num` THEN ASM_SIMP_TAC[] THEN NO_TAC) THEN
  TRY (W pick_encoding) THEN ASM_SIMP_TAC WSTATE_LOOP_THMS THEN
  REWRITE_TAC[AXIOMS; distinctness "wff"] THEN TRY (EXISTS_TAC
    `\pl. f (f' ((1 <> encode_wff ps <> 0 <> 0 <> pl) + 1):num):num`) THEN
  EVOLVESC_TO_IMPS_TAC' THEN ASM IMP_REWRITE_TAC WSTATE_LOOP_THMS THEN
  REWRITE_TAC [EXCLUDED_MIDDLE]);;

let MACHINE_COMPLETE = prove(`provable (0 @: 0) ==> {initial} -->_c {halted}`,
  DISCH_TAC THEN MP_TAC (SPEC `0 @: 0` PROOFS_EXIST) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC (SPEC `(0 <> 0 <> 0 <> 0 <> (f 0)) + 1` NWSTATE_ALL_PROOFS) THEN
  DISCH_TAC THEN EVOLVESC_TO_IMPS_TAC' THEN ASM IMP_REWRITE_TAC[] THEN
  REWRITE_TAC[NOWFFSTATE; TMEVC_UNL; TMEVC_ABSL] THEN CONJ_TAC THENL [
    REWRITE_TAC[TMEVC_DEF; IN_SING; IN_ELIM_THM] THEN MESON_TAC[HALTED_STICKY];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    POP_ASSUM SUBST_ALL_TAC THEN
    IMP_REWRITE_TAC(mapfilter (MATCH_MP EVOLVEC_TO_IMP) WSTATE_LOOP_THMS) THEN
    ASM_REWRITE_TAC[]]);;

let MACHINE_CORRECT = prove(`initial -->_w halted <=> !w. provable w`,
  MESON_TAC[wEXP1; MACHINE_SOUND; MACHINE_COMPLETE; TMEVC_DEF; IN_SING]);;
(*

unset_verbose_symbols();;
set_margin 200;;
Printexc.record_backtrace true;;

install_user_printer("regname",fun f tm ->
  let nm,ty = dest_var tm in let n::ns = explode nm in
  if n <> "r" || ty <> `:num` then failwith "" else
  let nns = int_of_string (implode ns) in
  let alias = el nns ["rpl";"rs1";"rs2";"rnp";"rt2";"raxc";"rp1";"rp2";"rp3";
    "rws";"rtw";"rs3"] in
  pp_print_string f alias);;

install_user_printer("pc",fun f tm ->
  let bs,fin = splitlist dest_cons tm in
  if not (bs <> [] && fin = `pc:bool list` ||
      length bs = pc_bits && fin = `[]:bool list`) then fail() else
  let s = implode (rev (map (fun b -> if dest_bool b then "1" else "0") bs)) in
  pp_print_string f ("#"^s^"(pc)"));;

*)
