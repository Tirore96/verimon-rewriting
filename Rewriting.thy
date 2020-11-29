  theory Rewriting
    imports "MFODL_Monitor_Optimized.Formula" "MFODL_Monitor_Optimized.Regex"
begin


(*
Question: Is the set of range restricted variables defined in the Formula module?

definition propagate_cond where
  "propagate_cond f1 f2 =
      (let rr1, b1 = rr f1;
           rr2, b2 = rr f2; 
           fv2 = Formula.fv f2 
      in  (rr1 \<inter> (fv2 \<setminus> rr2)) \<supset> \<emptyset> )"
*)

thm Let_def
lemma sat_1:
  "Formula.sat \<sigma> V v i (Formula.And a (Formula.Or b g)) =
   Formula.sat \<sigma> V v i (Formula.Or (Formula.And a b) (Formula.And a g))"
  by auto

lemma sat_rewrite_5: "Formula.sat \<sigma> V v i (Formula.And a (Formula.Neg b))  = 
                      Formula.sat \<sigma> V v i (Formula.And a (Formula.Neg (Formula.And a b)))"
  by auto

primrec shiftTI :: "nat \<Rightarrow> Formula.trm \<Rightarrow> Formula.trm" where
  "shiftTI k (Formula.Const c) = Formula.Const c"
| "shiftTI k (Formula.Var i) = (if k \<le> i then Formula.Var (i+1) 
                                         else Formula.Var i)"
| "shiftTI k (Formula.Plus t u) = Formula.Plus (shiftTI k t) (shiftTI k u)"
| "shiftTI k (Formula.Minus t u) = Formula.Minus (shiftTI k t) (shiftTI k u)"
| "shiftTI k (Formula.UMinus t)  = Formula.UMinus (shiftTI k t)"
| "shiftTI k (Formula.Mult t u) = Formula.Mult (shiftTI k t) (shiftTI k u)"
| "shiftTI k (Formula.Div t u) = Formula.Div (shiftTI k t) (shiftTI k u)"
| "shiftTI k (Formula.Mod t u) = Formula.Mod (shiftTI k t) (shiftTI k u)"
| "shiftTI k (Formula.F2i t) = Formula.F2i (shiftTI k t)"
| "shiftTI k (Formula.I2f t) = Formula.I2f (shiftTI k t)"


abbreviation "shiftT \<equiv> shiftTI 0"

(* Rules taken from Formula that I take inspiration from
lemma fvi_trm_plus: "x \<in> fvi_trm (b + c) t \<longleftrightarrow> x + c \<in> fvi_trm b t"
  by (induction t) auto

lemma fvi_trm_iff_fv_trm: "x \<in> fvi_trm b t \<longleftrightarrow> x + b \<in> fv_trm t"
  using fvi_trm_plus[where b=0 and c=b] by simp_all
*)

lemma shift_fv_in_t: "x  \<in> Formula.fvi_trm b t \<longleftrightarrow> 
                        x+1 \<in> Formula.fvi_trm b (shiftTI b t)" by (induction t;auto)


    

primrec shiftI :: "nat \<Rightarrow> Formula.formula \<Rightarrow> Formula.formula" where
  "shiftI k (Formula.Pred r ts) = Formula.Pred r (map (shiftTI k) ts)"
| "shiftI k (Formula.Exists a) = Formula.Exists (shiftI (Suc k) a)"
| "shiftI k (Formula.Let nm n a b) = Formula.Let nm n (shiftI k a) (shiftI k b)"
| "shiftI k (Formula.Eq t1 t2) = Formula.Eq (shiftTI k t1) (shiftTI k t2)"
| "shiftI k (Formula.Less t1 t2) =  Formula.Less (shiftTI k t1) (shiftTI k t2)"
| "shiftI k (Formula.LessEq t1 t2) = Formula.LessEq (shiftTI k t1) (shiftTI k t2)"
| "shiftI k (Formula.Neg a) = Formula.Neg (shiftI k a)"
| "shiftI k (Formula.Or a b) = Formula.Or (shiftI k a) (shiftI k b)"
| "shiftI k (Formula.And a b) = Formula.And (shiftI k a) (shiftI k b)"
| "shiftI k (Formula.Ands as) = Formula.Ands (map (shiftI k) as)"  
| "shiftI k (Formula.Agg y op b t a) = Formula.Agg (if y < k then y else y + 1)
                                            op b (shiftTI (k + b) t) (shiftI (k + b) a)"
| "shiftI k (Formula.Prev \<I> a) = Formula.Prev \<I> (shiftI k a)"
| "shiftI k (Formula.Next \<I> a) = Formula.Next \<I> (shiftI k a)"
| "shiftI k (Formula.Since a1 \<I> a2) = Formula.Since (shiftI k a1) \<I> (shiftI k a2)"
| "shiftI k (Formula.Until a1 \<I> a2) = Formula.Until (shiftI k a1) \<I> (shiftI k a2)"
| "shiftI k (Formula.MatchF \<I> r) = Formula.MatchF \<I> (Regex.map_regex (shiftI k) r)"
| "shiftI k (Formula.MatchP \<I> r) = Formula.MatchP \<I> (Regex.map_regex (shiftI k) r)"


abbreviation shift where "shift \<equiv> shiftI 0"
(*Sequence of lemmas I think is needed to finally show sat_rewrite_4 *)
lemma shift_fv_in_f: "x \<in> (Formula.fvi b \<phi>) \<longleftrightarrow> (x+1) \<in> (Formula.fvi b (shiftI b \<phi>))" 
  using shift_fv_in_t proof(induction \<phi> rule: fvi.induct)
  case (16 b I r)
  then show ?case by (induct r;auto)
next
  case (17 b I r)
  then show ?case by (induct r;auto)
qed auto


lemma shift_valuation_conservation: "length xs = b \<Longrightarrow>
                                 Formula.eval_trm (xs @ v) t = 
                                 Formula.eval_trm (xs @ z # v) (shiftTI b t)"
(is "?L \<Longrightarrow> ?R")
proof(induct t)
    case (Var x)
    then show ?case
      proof(cases "b\<le>x")
        case True
        assume ?L
        then show ?thesis using nth_append[where ?xs=xs] by simp
    next
      case False
      then show ?thesis using nth_append[where ?xs=xs] by (simp add: Var.prems)
    qed
qed simp_all

  (*
  have sub_val: "\<And>b' xs' x' v' k'. b' = length xs' \<Longrightarrow> b'+ k' = x' \<Longrightarrow> (xs' @ v')!x' = v'!k'" by auto
  then have ?thesis by auto
*)

lemma shift_preserve_sat_aux: "\<And>v. length xs = b \<Longrightarrow>
  Formula.sat \<sigma> V (xs @ v) i \<phi> = Formula.sat \<sigma> V (xs @ z # v) i (shiftI b \<phi>)"
using shift_valuation_conservation proof(induct \<phi> rule: Formula.sat.induct)
  case (1 \<sigma> V v i r ts)
  then show ?case by (auto split: option.splits)
next
case (2 \<sigma> V v i p b \<phi> \<psi>)
then show ?case sorry
next
  case (3 \<sigma> V v i t1 t2)
  then show ?case sorry
next
  case (4 \<sigma> V v i t1 t2)
  then show ?case sorry
next
  case (5 \<sigma> V v i t1 t2)
then show ?case sorry
next
case (10 \<sigma> V v i \<phi>)
  then show ?case sorry
next
  case (11 \<sigma> V v i y \<omega> b f \<phi>)
  then show ?case sorry
next
  case (12 \<sigma> V v i I \<phi>)
  then show ?case sorry
next
  case (13 \<sigma> V v i I \<phi>)
  then show ?case sorry
next
  case (14 \<sigma> V v i \<phi> I \<psi>)
  then show ?case sorry
next
  case (15 \<sigma> V v i \<phi> I \<psi>)
  then show ?case sorry
next
  case (16 \<sigma> V v i I r)
  then show ?case sorry
next
  case (17 \<sigma> V v i I r)
  then show ?case sorry
qed simp_all





lemma shift_preserve_sat:
  "Formula.sat \<sigma> V v i \<phi> = Formula.sat \<sigma> V (z # v) i (shift \<phi>)"
  using shift_preserve_sat_aux[of "[]"] by simp

(*"\<alpha> \<and> \<exists>x. \<beta> = \<exists>x. (shift \<alpha>) \<and> \<beta>" *)
lemma shift_conj_in_exists: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Exists \<beta>)) = 
                    Formula.sat \<sigma> V v i (Formula.Exists (Formula.And (shift \<alpha>) \<beta> ))"
  using shift_preserve_sat by auto

lemma sat_rewrite_4: "Formula.sat \<sigma> V v i (rewrite_4 \<phi>) = Formula.sat \<sigma> V v i \<phi>" sorry





(*
Lemmas that could be interesting in the future

lemma fv_rewrite[simp]: "fv (rewrite \<phi>) = fv \<phi>"

lemma "safe_formula \<phi> \<Longrightarrow> safe_formula (rewrite \<phi>)" 
*)

end
