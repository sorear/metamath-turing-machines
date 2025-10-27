(* preliminaries - function theory *)

let ITERF_DEF = define`ITERF 0 f (x:A) = x /\ ITERF (SUC n) f x = f (ITERF n f x)`;;
let ITERF_ADD = prove(`!m n f (x:A). ITERF (m + n) f x = ITERF m f (ITERF n f x)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES;ITERF_DEF]);;

(* preliminaries - fast maps

   hol-light's built in definition by cases is far, far too slow to handle our
   transition table

   maps are typed as functions, but have a recursive representation that allows
   logarithmic time evaluation without alpha conversion. the base concept is
   similar to sptree from HOL4, but simplified for our use case
   
   imprecise = few guarantees on value outside provided alist. a precise mode
   is possible but requires ~twice the term nodes *)

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

let nqlroot = Sys.getenv "NQLROOT";;
let tm_lines = In_channel.with_open_text (nqlroot ^ "/machines/2017-zf-sorear-748/zf2.tm") In_channel.input_lines ;;
let tm_states_tok = List.map (String.split_on_char ' ') ("HALT = 0 L HALT 0 L HALT" :: tm_lines) ;;
let state_of_name n = Option.get (List.find_index (fun tp -> n = (List.hd tp)) tm_states_tok) ;;
let name_of_state s = List.hd (List.nth tm_states_tok s) ;;
let next_info toks i = state_of_name (List.nth toks i) ;;
let toks_to_state_info [name;_;w0;m0;ns0;w1;m1;ns1] = (name,(state_of_name ns0,m0="R",w0="1"),(state_of_name ns1,m1="R",w1="1")) ;;
let state_info = List.map toks_to_state_info tm_states_tok ;;

let mk_bool b = if b then `T` else `F` ;;

(* subst a large term into the body of an abs is slow since it needs to be checked for bound variables; possibly exponential nested alpha, def linear *)
(* comparing rigorously identical terms is fast *)
(* assumption lists are linear *)
(* substitution always linear in template, except when alpha converting *)
(* once_depth: try root, try children once if failed *)
(* depth: exhaust children then root *)
(* redepth: recurse, try root once, repeat *)
(* top_depth: exhaust, recurse, alternate trying root once and recursing *)
(* top_sweep: exhaust then recurse *)

(* construct and prove validity of loaded transition table *)

let transition_table_DEF =
  let triple (ns,m,w) = mk_pair(mk_small_numeral ns, mk_pair(mk_bool m, mk_bool w)) in
  let table = mk_nmap_imprecise `BMAP (0,F,F) (0,F,F)` (List.mapi (fun i (_,t0,t1) -> i, mk_bmap (triple t0) (triple t1)) state_info) in
  new_basic_definition (mk_eq(`transition_table:num->bool->num#bool#bool`, table)) ;;

let transition_table_LIMIT = CONV_RULE (SIMP_CONV[]) ((PURE_REWRITE_CONV [transition_table_DEF;nmap_FORALL;bmap_FORALL;FST] THENC SIMP_CONV[ARITH_LE;ARITH_LT;EQ_CLAUSES])
  `(\m. !i. (\n. !b. FST (n b) <= 748) (m i)) transition_table`);;

let transition_table_VALID = prove(`gtm_valid transition_table 748`, REWRITE_TAC[gtm_valid_DEF;transition_table_LIMIT;FORALL_BOOL_THM;transition_table_DEF;nmap_CLAUSES;bmap_CLAUSES;ARITH_EQ]);;

    (* to convert ground terms, may become optimized *)
let transition_table_CONV = REWRITE_CONV[transition_table_DEF;nmap_CLAUSES;bmap_CLAUSES];;

(* tape handling

   for the register and dispatch logic, we represent the tape at the bit level,
   since updates do not pass through intermediate states that are meaningful at
   higher levels. we also support "cruft" in ignored portions of the tape,
   because ajwade's machines use an unclean initialization process.

   the initialization process itself does not have to be modeled since it
   halts, but we need a calculation-friendly tape representation *)

let list_tape_DEF = define `list_tape l tp = \i. &0 <= tp+i /\ tp+i < &(LENGTH l) /\ EL (num_of_int (tp+i)) l`;;
let bilist_tape_DEF = define `bilist_tape ll sy rl = \i. if i = &0 then sy else let l = if i < &0 then ll else rl in let ii = num_of_int (abs i - 1) in ii < LENGTH l /\ EL ii l`;;

let list_tape_SHIFT = prove(`shift j (list_tape l tp) = list_tape l (tp+j)`, SIMP_TAC[tape_shift_DEF;list_tape_DEF;INT_ADD_ASSOC]);;

let NUM_OF_INT_2 = prove(`&0 <= x ==> ?z. x:int = &z`, REWRITE_TAC[EXISTS_THM;NUM_OF_INT;num_of_int] THEN MESON_TAC[]);;

let list_tape_RAPPEND = prove(
 `list_tape (APPEND l [F]) tp = list_tape l tp`,
  REWRITE_TAC[list_tape_DEF] THEN ABS_TAC THEN ASM_CASES_TAC `&0 <= tp+i` THEN ASM_SIMP_TAC[] THEN
  POP_ASSUM (DESTRUCT_TAC "@j. eq" o MATCH_MP NUM_OF_INT_2) THEN POP_ASSUM SUBST1_TAC THEN
  EQ_TAC THEN SIMP_TAC[NUM_OF_INT_OF_NUM;INT_OF_NUM_LT;LENGTH_APPEND;LENGTH;EL_APPEND;ADD_CLAUSES;LT] THEN
  INTRO_TAC "(lt|eq) el" THEN USE_THEN "el" (UNDISCH_TAC o concl) THEN ASM_SIMP_TAC[SUB_REFL;LT_REFL;EL;HD]);;

let list_tape_LAPPEND = prove(
 `list_tape (APPEND [F] l) (tp + &1) = list_tape l tp`,
   SIMP_TAC[list_tape_DEF;APPEND;LENGTH;EL_CONS;INT_ADD_AC] THEN ABS_TAC THEN ASM_CASES_TAC `i + tp + &1 = &0` THENL[
     MP_TAC(SPEC `&0` NUM_OF_INT) THEN ASM_SIMP_TAC[INT_LE_REFL;INT_OF_NUM_EQ] THEN ASM_ARITH_TAC;
     ASM_REWRITE_TAC[INT_LE_LT;INT_ADD_ASSOC;GSYM INT_LE_DISCRETE;ADD1;GSYM INT_OF_NUM_ADD;INT_LT_RADD] THEN
     REWRITE_TAC[GSYM INT_ADD_ASSOC;GSYM INT_LE_LT] THEN
     SIMP_TAC[TAUT `(p/\q)=(p/\r)<=>(p==>q=r)`;NUM_OF_INT;INT_ADD_ASSOC] THEN FIRST_X_ASSUM (DESTRUCT_TAC "nz") THEN
     INTRO_TAC "num" THEN USE_THEN "nz" (UNDISCH_TAC o concl) THEN REWRITE_TAC[INT_ADD_ASSOC] THEN
     USE_THEN "num" (SUBST1_TAC o SYM) THEN REWRITE_TAC[INT_OF_NUM_CLAUSES] THEN
     REWRITE_TAC[NUM_OF_INT_OF_NUM;GSYM ADD1;NOT_SUC] THEN REWRITE_TAC[ADD1;ADD_SUB]]);;




let bilist_tape_READ = prove(`bilist_tape ll sy rl (&0) = sy`, REWRITE_TAC[bilist_tape_DEF]);;
let bilist_tape_WRITE = prove(`write sy' (bilist_tape_2 ll sy rl) = (bilist_tape_2 ll sy' rl)`, SIMP_TAC[bilist_tape_DEF;tape_write_DEF]);;
