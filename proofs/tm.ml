(* bare minimum "generic" TM theory to allow proving existentials *)

let ITERF_DEF = define`ITERF 0 f (x:A) = x /\ ITERF (SUC n) f x = f (ITERF n f x)`;;
let ITERF_ADD = prove(`!m n f (x:A). ITERF (m + n) f x = ITERF m f (ITERF n f x)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES;ITERF_DEF]);;

let gtm_valid_DEF = define`gtm_valid (tt:num->bool->num#bool#bool) st <=> ~(st = 0) /\ !b. FST(tt 0 b) = 0 /\ !i. i <= st ==> FST (tt i b) <= st` ;;
let tape_shift_DEF = define`shift i (tp:int->bool) = \j. tp (i+j)`;;
let tape_write_DEF = define`write v (tp:int->bool) = \i. if i = &0 then v else tp i`;;
let halted_DEF = define`halted = 0,\(i:int).F`;;
let gtm_step_DEF = define`gtm_step tt (st:num,t) = let ns,m,w = tt st (t (&0)) in if ns=0 then halted else ns,shift (if m then &1 else -- &1) (write w t)` ;;

let nqlroot = Sys.getenv "NQLROOT";;
let tm_lines = In_channel.with_open_text (nqlroot ^ "/machines/2017-zf-sorear-748/zf2.tm") In_channel.input_lines ;;
let tm_states_tok = List.map (String.split_on_char ' ') ("HALT = 0 L HALT 0 L HALT" :: tm_lines) ;;
let state_of_name n = Option.get (List.find_index (fun tp -> n = (List.hd tp)) tm_states_tok) ;;
let name_of_state s = List.hd (List.nth tm_states_tok s) ;;
let next_info toks i = state_of_name (List.nth toks i) ;;
let toks_to_state_info [name;_;w0;m0;ns0;w1;m1;ns1] = (name,(state_of_name ns0,m0="R",w0="1"),(state_of_name ns1,m1="R",w1="1")) ;;
let state_info = List.map toks_to_state_info tm_states_tok ;;

let mk_bool b = if b then `T` else `F` ;;

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

(* subst a large term into the body of an abs is slow since it needs to be checked for bound variables; possibly exponential nested alpha, def linear *)
(* comparing rigorously identical terms is fast *)
(* assumption lists are linear *)
(* substitution always linear in template, except when alpha converting *)
(* once_depth: try root, try children once if failed *)
(* depth: exhaust children then root *)
(* redepth: recurse, try root once, repeat *)
(* top_depth: exhaust, recurse, alternate trying root once and recursing *)
(* top_sweep: exhaust then recurse *)


(* too slow - 20+ min

let triple_def (s,b) (ns,m,w) = mk_eq(mk_binop(mk_var("transition_map",`num -> bool -> num#bool#bool`), mk_small_numeral s, mk_bool b), mk_pair(mk_small_numeral ns, mk_pair(mk_bool m, mk_bool w))) in
list_mk_conj (List.concat_map (fun (_,t0,t1) -> [triple_def t0; triple_def t1]))a

let transition_map_DEF =
  let triple_def (s,b) (ns,m,w) = mk_eq(mk_binop (mk_var("transition_map",`:num -> bool -> num#bool#bool`)) (mk_small_numeral s) (mk_bool b), mk_pair(mk_small_numeral ns, mk_pair(mk_bool m, mk_bool w))) in
  state_info |> List.mapi (fun i (_,t0,t1) -> [triple_def (i,false) t0; triple_def (i,true) t1]) |> List.concat |> list_mk_conj |> define;;

*)

let transition_table_DEF =
  let triple (ns,m,w) = mk_pair(mk_small_numeral ns, mk_pair(mk_bool m, mk_bool w)) in
  let table = mk_nmap_imprecise `BMAP (0,F,F) (0,F,F)` (List.mapi (fun i (_,t0,t1) -> i, mk_bmap (triple t0) (triple t1)) state_info) in
  new_basic_definition (mk_eq(`transition_table:num->bool->num#bool#bool`, table)) ;;

let transition_table_LIMIT = CONV_RULE (SIMP_CONV[]) ((PURE_REWRITE_CONV [transition_table_DEF;nmap_FORALL;bmap_FORALL;FST] THENC SIMP_CONV[ARITH_LE;ARITH_LT;EQ_CLAUSES])
  `(\m. !i. (\n. !b. FST (n b) <= 748) (m i)) transition_table`);;

let transition_table_VALID = prove(`gtm_valid transition_table 748`, REWRITE_TAC[gtm_valid_DEF;transition_table_LIMIT;FORALL_BOOL_THM;transition_table_DEF;nmap_CLAUSES;bmap_CLAUSES;ARITH_EQ]);;
