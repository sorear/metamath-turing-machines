let _ = prioritize_int();;
let _ = set_verbose_symbols(false);;

(* hol-light usage notes

   still underusing directed conversions, implicational and target rewriting,
   custom tactics, simpsets, user parsers/printers *)

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

(*
let my_rev_conv =
   let lem1 = SYM (REWRITE_CONV [APPEND_NIL] `APPEND (REVERSE (xs:A list)) []`) in
   let lem2 = REWRITE_CONV [REVERSE;APPEND;GSYM APPEND_ASSOC] `APPEND (REVERSE (CONS (x:A) xs)) ys` in
   let lem3 = REWRITE_CONV [REVERSE;APPEND] `APPEND (REVERSE []) (ys:A list)` in
   fun rterm ->
      let lsterm = rand rterm in
      let Tyapp (_, ty::_) = type_of lsterm in
      let [lem1i; lem2i; lem3i] = map (INST_TYPE [ty,aty]) [lem1; lem2; lem3] in
      let [vxs; vx; vys] = frees (concl lem2i) in
      let rec iter eq lhs rhs = match lhs with
         | Const ("NIL",_) -> TRANS eq (INST [rhs,vys] lem3i)
         | Comb (Comb (_,l) as cons_l,rest) -> iter (TRANS eq (INST [l,vx;rest,vxs;rhs,vys] lem2i)) rest (mk_comb(cons_l,rhs))
      in iter (INST [lsterm,vxs] lem1i) lsterm (mk_const("NIL",[ty,aty])) ;;
my_rev_conv `REVERSE [1;2;3;4;5;6]`;;
*)

(* preliminaries - function and list handling *)

let NUM_OF_INT_2 = prove(`&0 <= x ==> ?z. x:int = &z`, REWRITE_TAC[EXISTS_THM;NUM_OF_INT;num_of_int] THEN MESON_TAC[]);;

let ITERF_DEF = define`ITERF 0 f (x:A) = x /\ ITERF (SUC n) f x = f (ITERF n f x)`;;
let ITERF_ADD = prove(`!m n f (x:A). ITERF (m + n) f x = ITERF m f (ITERF n f x)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES;ITERF_DEF]);;

let TAKE_DEF = define`TAKE 0 l = [] /\ TAKE (SUC i) l = (CONS (HD l:A) (TAKE i (TL l)))`;;
let DROP_DEF = define`DROP 0 l = l /\ DROP (SUC i) l = DROP i (TL l:A list)`;;

let LENGTH_TAKE = prove(`!i l. LENGTH (TAKE i l:A list) = i`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[TAKE_DEF;LENGTH]);;
let LENGTH_DROP = prove(`!i (l:A list). i <= LENGTH l ==> LENGTH (DROP i l) = LENGTH l - i`,
  INDUCT_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[DROP_DEF;LENGTH;SUB_0;TL;LE_SUC;SUB_SUC;LE;NOT_SUC]);;

let EL_TAKE = prove(`!i j l. i < j ==> EL i (TAKE j l) = (EL i l:A)`,
  REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC[TAKE_DEF; EL; HD; TL; LT_SUC; LT]);;
let EL_DROP = prove(`!j l. EL i (DROP j l) = EL (i + j) (l:A list)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[DROP_DEF;ADD_CLAUSES;EL]);;

let TAKE_DROP = prove(`!i l. i <= LENGTH l ==> APPEND (TAKE i l) (DROP i l) = l`,
  INDUCT_TAC THEN LIST_INDUCT_TAC THEN ASM_SIMP_TAC[TAKE_DEF;DROP_DEF;APPEND;LENGTH;LE_SUC;LE;NOT_SUC;HD;TL]);;

let TAKE_APPEND_EQ = prove(`!a b. TAKE (LENGTH (a:A list)) (APPEND a b) = a`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH; TAKE_DEF; APPEND; HD; TL]);;

let DROP_APPEND_GE = prove(
 `!x a b. LENGTH a <= x ==> DROP x (APPEND (a:A list) b) = DROP (x - LENGTH a) b`,
  INDUCT_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[DROP_DEF; APPEND; LENGTH;
    SUB; LE_SUC; SUB_PRESUC; TL] THEN REWRITE_TAC[LE; NOT_SUC]);;

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
  `NMAP_NODE l r (NUMERAL i) = (NMAP_NODE l r i):'a /\ NMAP_NODE l r _0 = l _0 /\ NMAP_NODE l r (BIT0 i) = l i /\ NMAP_NODE l r (BIT1 i) = r i /\
   NMAP_LEAF v f _0 = v /\ NMAP_LEAF v f (NUMERAL i) = (NMAP_LEAF v f i):'a /\ NMAP_LEAF v f (BIT0 i) = NMAP_LEAF v f i /\ NMAP_LEAF v f (BIT1 i) = f`,
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
let halted_DEF = define`halted = 0,\(i:int).F`;;
let gtm_step_DEF = define`gtm_step tt (st:num,t) = let ns,m,w = tt st (t (&0)) in if ns=0 then halted else ns,shift (if m then &1 else -- &1) (write w t)` ;;

(* loading and parsing .tm files emitted by nqlaconic

   state_info is a list of (name,when symbol 0,when symbol 1) with behaviors
   represented as transition table values. name_to_state is also important and
   will drive most proving *)

let nqlroot = "..";;
let tm_lines = In_channel.with_open_text (nqlroot ^ "/machines/2017-zf-sorear-748/zf2.tm") In_channel.input_lines ;;
let tm_states_tok = List.map (String.split_on_char ' ') ("HALT = 0 L HALT 0 L HALT" :: tm_lines) ;;
let state_of_name n = Option.get (List.find_index (fun tp -> n = (List.hd tp)) tm_states_tok) ;;
let name_of_state s = List.hd (List.nth tm_states_tok s) ;;
let next_info toks i = state_of_name (List.nth toks i) ;;
let toks_to_state_info [name;_;w0;m0;ns0;w1;m1;ns1] = (name,(state_of_name ns0,m0="R",w0="1"),(state_of_name ns1,m1="R",w1="1")) ;;
let state_info = List.map toks_to_state_info tm_states_tok ;;

let mk_bool b = if b then `T` else `F` ;;

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
      list_tape (APPEND (TAKE tp l) (CONS b (DROP (SUC tp) l))) (&tp)`,
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
        list_tape (APPEND (REVERSE ls) rs) (&(LENGTH ls) - &1)`;;
let rzip_tape = define`rzip_tape ls rs =
        list_tape (APPEND (REVERSE ls) rs) (&(LENGTH ls))`;;
let zip_shift = prove(
 `shift (-- &1) (lzip_tape (CONS l ls) rs) = lzip_tape ls (CONS l rs) /\
  shift    (&1) (rzip_tape ls (CONS r rs)) = rzip_tape (CONS r ls) rs /\
  shift (-- &1) (rzip_tape ls rs) = lzip_tape ls rs /\
  shift    (&1) (lzip_tape ls rs) = rzip_tape ls rs`,
  SIMP_TAC[lzip_tape; rzip_tape; list_tape_SHIFT; REVERSE; GSYM APPEND_ASSOC;
    LENGTH; APPEND] THEN REPEAT CONJ_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let zip_write = prove(
 `write b (lzip_tape (CONS l ls) rs) = lzip_tape (CONS b ls) rs /\
  write b (rzip_tape ls (CONS r rs)) = rzip_tape ls (CONS b rs)`,
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

let zip_read = prove(
  `lzip_tape (CONS l ls) rs (&0) = l /\ rzip_tape ls (CONS r rs) (&0) = r`,
  REWRITE_TAC[lzip_tape; rzip_tape; list_tape_DEF; LENGTH; LENGTH_APPEND;
    REVERSE; GSYM APPEND_ASSOC; APPEND; ADD1; INT_ADD_RID;
    GSYM INT_OF_NUM_CLAUSES; ARITH_RULE `(x+y)-y=x`] THEN
  REWRITE_TAC[INT_OF_NUM_CLAUSES; NUM_OF_INT_OF_NUM; LE_0; ADD;
    LENGTH_REVERSE; EL_APPEND; LT_REFL; SUB_REFL; EL; HD; ADD_AC;
    ARITH_RULE `x < x + y + 1`]);;

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

let defn_for_state tm name = new_basic_definition(mk_eq(tm,
  mk_small_numeral(state_of_name name)));;
let defn_state_pair tm name0 name1 = new_basic_definition(mk_eq(tm,
  mk_bmap (mk_small_numeral (state_of_name name0))
          (mk_small_numeral (state_of_name name1))));;
let defn_state_q tm n0 n1 n2 n3 = new_basic_definition(mk_eq(tm,
  mk_bmap (mk_bmap (mk_small_numeral (state_of_name n0))
                   (mk_small_numeral (state_of_name n1)))
          (mk_bmap (mk_small_numeral (state_of_name n2))
                   (mk_small_numeral (state_of_name n3)))));;
let dec_init_S = defn_for_state `dec_init:num` "dec.init";;
let dec_check_S = defn_for_state `dec_check:num` "dec.check";;
let dec_restore_S = defn_for_state `dec_restore:num` "dec.restore";;
let dec_scan_S = defn_state_pair `dec_scan:bool->num` "dec.scan_0" "dec.scan_1";;
let dec_scan_done_S = defn_for_state `dec_scan_done:num` "dec.scan_done";;
let dec_shift_S = defn_state_pair `dec_shift:bool->num` "dec.shift_0" "dec.shift_1";;
let inc_shift_S = defn_state_pair `inc_shift:bool->num` "inc.shift_0" "inc.shift_1";;
let return_S = defn_state_q `return:bool->bool->num`
    "return.0" "return.1" "return2.0" "return2.1";; 
let dispatchroot_S = defn_for_state `dispatchroot:num` "main()[]";;
let dispatch_S = defn_state_pair `dispatch:bool->num` "dispatch.0.carry" "nextstate_2";;

(* register operations

   start by proving single steps, use induction to build the inner loops, then
   inductively construct the behavior of primitive register operations at the
   dispatch/register interface boundary *)

let REG = define`REG n xs = APPEND (REPLICATE (SUC n) T) (CONS F xs)`;;
let REGFILE = define`REGFILE ns xs = ITLIST REG ns xs`;;
let OPSEG = define`OPSEG ns cruft = CONS F (CONS F (ITLIST REG ns cruft))`;;
let DEC_CRUFT = define`DEC_CRUFT n (creg,cbit) =
        if n = 0 then creg,cbit else creg,CONS F cbit`;;
let (REGLIKE, REGLIKE_IND, REGLIKE_CASES) = new_inductive_definition
 `REGLIKE F [F] /\
  (!bs. REGLIKE F bs ==> REGLIKE T (CONS F bs)) /\
  (!b bs. REGLIKE T bs ==> REGLIKE b (CONS T bs))`;;

(* TODO automate *)
let return_LEMMA = prove(
`return skip F,lzip_tape (CONS F ls) rs -->_w dispatch skip,lzip_tape ls (CONS F rs) /\
 return skip F,lzip_tape (CONS T ls) rs -->_w return skip T,lzip_tape ls (CONS T rs) /\
 return skip T,lzip_tape (CONS F ls) rs -->_w return skip F,lzip_tape ls (CONS F rs) /\
 return skip T,lzip_tape (CONS T ls) rs -->_w return skip T,lzip_tape ls (CONS T rs)`,
  BOOL_CASES_TAC `skip:bool` THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC tm_evolves_BASE THEN
  REWRITE_TAC[dispatch_S; return_S; gtm_step_DEF; zip_write; zip_read; bmap_CLAUSES] THEN
  CONV_TAC transition_table_CONV THEN SIMP_TAC[LET_DEF;ARITH;LET_END_DEF; zip_shift]);;

let return_THM = prove(
`!b rf. REGLIKE b rf ==> !left right. (return skip b, lzip_tape (APPEND rf left) right) -->_w
 (dispatch skip, lzip_tape left (APPEND (REVERSE rf) right))`,
 MATCH_MP_TAC REGLIKE_IND THEN
 REPEAT STRIP_TAC THEN REWRITE_TAC[APPEND; REVERSE; GSYM APPEND_ASSOC] THENL [
   ALL_TAC;
   TRANS_TAC (GEN_ALL tm_evolves_TRANS) `return skip F,lzip_tape (APPEND bs left) (CONS F right)`;
   TRANS_TAC (GEN_ALL tm_evolves_TRANS) `return skip T,lzip_tape (APPEND bs left) (CONS T right)`] THEN
 TRY (BOOL_CASES_TAC `b:bool`) THEN ASM_REWRITE_TAC[return_LEMMA]);;

(*
`!P. (!l b. (P F l ==> P T (CONS F l)) /\ (P T l ==> P b (CONS T l)))
 ==> P T (CONS F (REGFILE ns rest)) /\ !s. P s (REGFILE ns rest)`
`!ns. REGLIKE incz rf ==> (return skip incz, lzip_tape (APPEND (REVERSE rf left) right) -->_w (nextstate skip, lzip_tape left (APPEND rf right))`

(* dec Z return.1 left-before 0 before reg *)
(* dec NZ return.0 left-after 0 before reg *)
(* inc return.0 left-after 0 after last reg *)
(* init return.1 left-before 0 after last reg *)


`(return skip T, lzip_tape (REGFILE (REVERSE nsl) (CONS F left)) (REGFILE nsr cruft)) -->_w
 (nextstate skip, lzip_tape left (OPSEG (APPEND nsl nsr) cruft))`

`!ns. (reg_decr 2, rzip_tape left (OPSEG (CONS n0 (CONS n1 ns)) cruft)) -->_w
      (nextstate (~(n1 = 0)), lzip_tape left
        (OPSEG (CONS n0 (CONS (PRE n1) ns)) (DEC_CRUFT n1 cruft)))`
`?cruft'. (reg_incr 2, rzip_tape left (OPSEG (CONS n0 (CONS n1 ns)) cruft)) -->_w
      (nextstate F, lzip_tape left
        (OPSEG (CONS n0 (CONS (SUC n1) ns)) cruft'))`

`{ dispatchroot, rzip_tape lcruft (APPEND (REVERSE pc) (OPSEG ns rcruft)) | T }`
*)

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

(* .subs semantics
   
   combines the judgements from "dispatch basics" and "operations" and wraps it
   all in existential quantifiers so that you don't need to study cruft
   evolution *)
