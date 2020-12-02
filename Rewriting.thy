  theory Rewriting
    imports "MFODL_Monitor_Optimized.Formula" "MFODL_Monitor_Optimized.Regex"
begin


(*
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

fun shiftTI :: "nat \<Rightarrow> Formula.trm \<Rightarrow> Formula.trm" where
 "shiftTI k (Formula.Var i) = (if i < k then Formula.Var i 
                                               else Formula.Var (i + 1))"
| "shiftTI k (Formula.Plus t u) = Formula.Plus (shiftTI k t) (shiftTI k u)"
| "shiftTI k (Formula.Minus t u) = Formula.Minus (shiftTI k t) (shiftTI k u)"
| "shiftTI k (Formula.UMinus t) = Formula.UMinus (shiftTI k t)"
| "shiftTI k (Formula.Mult t u) = Formula.Mult (shiftTI k t) (shiftTI k u)"
| "shiftTI k (Formula.Div t u) = Formula.Div (shiftTI k t) (shiftTI k u)"
| "shiftTI k (Formula.Mod t u) = Formula.Mod (shiftTI k t) (shiftTI k u)"
| "shiftTI k (Formula.F2i t) = Formula.F2i (shiftTI k t)"
| "shiftTI k (Formula.I2f t) = Formula.I2f (shiftTI k t)"
| "shiftTI k (Formula.Const n) = (Formula.Const n)"

(*abbreviation "shiftT \<equiv> shiftTI 0"*)
lemma eval_trm_shiftTI: "length xs = b \<Longrightarrow>
  Formula.eval_trm (xs @ z # v) (shiftTI b t) = Formula.eval_trm (xs @ v) t"
  by (induct b t rule: shiftTI.induct) (auto simp: nth_append split: trm.splits)

(* Rules taken from Formula that I take inspiration from
lemma fvi_trm_plus: "x \<in> fvi_trm (b + c) t \<longleftrightarrow> x + c \<in> fvi_trm b t"
  by (induction t) auto

lemma fvi_trm_iff_fv_trm: "x \<in> fvi_trm b t \<longleftrightarrow> x + b \<in> fv_trm t"
  using fvi_trm_plus[where b=0 and c=b] by simp_all
*)

lemma shift_fv_in_t: "x+1 \<in> Formula.fvi_trm b (shiftTI b t) \<longleftrightarrow> x  \<in> Formula.fvi_trm b t" 
   by (induction t;auto)


    

primrec shiftI :: "nat \<Rightarrow> Formula.formula \<Rightarrow> Formula.formula" where
  "shiftI k (Formula.Pred r ts) = Formula.Pred r (map (shiftTI k) ts)"
| "shiftI k (Formula.Exists a) = Formula.Exists (shiftI (Suc k) a)"
| "shiftI k (Formula.Let nm n a b) = Formula.Let nm n a (shiftI k b)" (*fix error a is not shifted*)
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
lemma shift_fv_in_f: "(x+1) \<in> (Formula.fvi b (shiftI b \<phi>)) \<longleftrightarrow> x \<in> (Formula.fvi b \<phi>)" 
using shift_fv_in_t proof (induction b \<phi> rule: fvi.induct)
  case (16 b I r)
  then show ?case by (induct r;auto)
next
  case (17 b I r)
  then show ?case by (induct r;auto)
qed (auto)

lemma shift_fv_notin_t: "x+1 \<notin> Formula.fvi_trm b (shiftTI b t) \<longleftrightarrow> x  \<notin> Formula.fvi_trm b t" 
  by (induction t;auto)

lemma shift_fv_notin_f: "(x+1) \<notin> (Formula.fvi b (shiftI b \<phi>)) \<longleftrightarrow> x \<notin> (Formula.fvi b \<phi>)" 
using shift_fv_notin_t proof (induction b \<phi> rule: fvi.induct)
  case (16 b I r)
  then show ?case by (induct r;auto)
next
  case (17 b I r)
  then show ?case by (induct r;auto)
qed (auto)

lemma fv_trm_shift_fv_empty: "Formula.fv_trm t = {} \<Longrightarrow>  Formula.fv_trm (shiftTI (Suc b) t) = Formula.fv_trm (shiftTI b t) "
  by (induction t;auto)


lemma fvi_trm_empty_shift_id: "Formula.fvi_trm b t = {} \<Longrightarrow> b \<le> b' \<Longrightarrow> shiftTI b' t = t"
  by (induction t;auto split:if_splits)

(*lemma map_idI: "(\<And>x. x \<in> set xs \<Longrightarrow> f x = x) \<Longrightarrow> map f xs = xs"
by (induct xs, auto)*)

(*prove this more general lemma, to later show nfv_shift_fv_empty*)
lemma fvi_empty_shift_id: "Formula.fvi b \<phi> = {} \<Longrightarrow> b \<le> b' \<Longrightarrow> shiftI b' \<phi> = \<phi>"
proof(induction \<phi> arbitrary: b b')
  case (Pred r ts)
  then show ?case using fvi_trm_empty_shift_id[where b="b" and b'="b'"] by (auto simp: map_idI) (*same as below*)
next
  case ands: (Ands xs)
  then show ?case using ands.IH[where b="b" and b'="b'"] by (auto simp: map_idI) (*must instansiate b and b' for map_idI to kick in*)
next
  case (Exists \<phi>)
  then show ?case  by (auto simp: fvi_trm_empty_shift_id)
next
  case (MatchF I r)
  then show ?case by (induction r;auto)
next
  case (MatchP I r)
  then show ?case by (induction r;auto)
qed (auto simp: fvi_trm_empty_shift_id split:if_splits)

lemma nfv_shift_fv_empty: "Formula.fv \<phi> = {} \<Longrightarrow>  Formula.nfv (shiftI (Suc b) \<phi>) = Formula.nfv (shiftI b \<phi>)"
proof-
  assume L: "Formula.fv \<phi> = {}"
  then have LHS:"shiftI (Suc b) \<phi> = \<phi>" using fvi_empty_shift_id[where b=0 and b'="Suc b"] by auto
  from L have RHS: "shiftI b \<phi> = \<phi>" using fvi_empty_shift_id[where b=0 and b'="b"] by auto
  from LHS and RHS show ?thesis by auto
qed


lemma sat_shift_fv_empty: "Formula.fv \<phi> = {} \<Longrightarrow> Formula.sat \<sigma> V v i (shiftI (Suc b) \<phi>) =
                                                 Formula.sat \<sigma> V v i (shiftI b \<phi>)" 
proof-
  assume L: "Formula.fv \<phi> = {}"
  then have LHS:"shiftI (Suc b) \<phi> = \<phi>" using fvi_empty_shift_id[where b=0 and b'="Suc b"] by auto
  from L have RHS: "shiftI b \<phi> = \<phi>" using fvi_empty_shift_id[where b=0 and b'="b"] by auto
  from LHS and RHS show ?thesis by auto
qed


lemma nfv_shift_high_b: "Formula.fv \<phi> \<noteq> {} \<Longrightarrow> Formula.nfv \<phi> \<le> b \<Longrightarrow>  Formula.nfv (shiftI (Suc b) \<phi>) = Formula.nfv (shiftI b \<phi>) " sorry

lemma nfv_shift_suc_b: "Formula.fv \<phi> \<noteq> {} \<Longrightarrow> Formula.nfv \<phi> = Suc b \<Longrightarrow>  Formula.nfv (shiftI (Suc b) \<phi>) + 1 = Formula.nfv (shiftI b \<phi>) " sorry

lemma nfv_shift_high_nfv: "Formula.fv \<phi> \<noteq> {} \<Longrightarrow> Formula.nfv \<phi> > Suc b \<Longrightarrow>  Formula.nfv (shiftI (Suc b) \<phi>) = Formula.nfv (shiftI b \<phi>) " sorry


lemma shift_inter_t: "length xs = b \<Longrightarrow> length ys = k \<Longrightarrow> 
                 Formula.eval_trm (xs @ ys @ z # v) (shiftTI (b + k) t) =
                 Formula.eval_trm (xs @ z # ys @ v) (shiftTI b t)" by (induction t;auto simp: nth_append)

lemma shift_inter_f: "length xs = b \<Longrightarrow> length ys = k \<Longrightarrow>
                 Formula.sat \<sigma> V (xs @ ys @ z # v) i (shiftI (b + k) \<phi>) =
                 Formula.sat \<sigma> V (xs @ z # ys @ v) i (shiftI b \<phi>)"
  using shift_inter_t proof(induction \<phi> )
case (Pred r ts)
  then have map_lemma: "map (Formula.eval_trm (xs @ ys @ z # v) \<circ> shiftTI (b + k)) ts =
                        map (Formula.eval_trm (xs @ z # ys @ v) \<circ> shiftTI b) ts" by (simp add: shift_inter_t)
  show ?case by (auto simp: map_lemma split: option.splits) 
next
  case let_case: (Let p b' \<phi> \<psi>)
  then show ?case 
  proof (cases "Formula.fv \<phi> = {}")
    case c: True
    then show ?thesis using let_case.IH(2)[OF let_case.prems(1)] sorry (* by (auto simp: nfv_shift_fv_empty sat_shift_fv_empty) *)
  next
    case False
    then consider (1) " Formula.nfv \<phi> \<le>  b" | (2) "Formula.nfv \<phi> = Suc b" | (3) "Formula.nfv \<phi> > Suc b"
      by linarith
    then show ?thesis 
    proof (cases)
      case 1
      then show ?thesis sorry
    next
      case 2
      then show ?thesis sorry
    next
      case 3
      then show ?thesis sorry 
    qed
  qed
next
  case (Exists \<phi>)
  then show ?case sorry
next
  case (Agg x1 x2 x3 x4 \<phi>)
  then show ?case sorry
next
  case (Prev x1 \<phi>)
  then show ?case sorry
next
  case (Next x1 \<phi>)
  then show ?case sorry
next
  case (Since \<phi>1 x2 \<phi>2)
  then show ?case sorry
next
  case (Until \<phi>1 x2 \<phi>2)
  then show ?case sorry
next
  case (MatchF x1 x2)
  then show ?case sorry
next
  case (MatchP x1 x2)
  then show ?case sorry
qed simp_all


lemma first_shift: "Formula.sat \<sigma> V (z # xs @ v) i (shiftI 0 \<phi>) = Formula.sat \<sigma> V (xs @ v) i \<phi>"
using eval_trm_shiftTI[of "[]"] proof(induction \<phi> arbitrary: V xs) (*arbitrary because of Let*)
  case (Pred r ts)
  then have map_lemma: "map (Formula.eval_trm (z # xs @ v) \<circ> shiftTI 0) ts
                        = map (Formula.eval_trm (xs @ v)) ts " by auto
  then show ?case by (auto split:option.splits simp: map_lemma)
next
  case ex: (Exists \<phi>)
  from ex show ?case using shift_inter_f[where xs="[]" and ys="[_]"] and ex.IH[where xs="_#xs"] by auto
next
  case (Agg x1 x2 x3 x4 \<phi>)
  then show ?case sorry
next
  case (Prev x1 \<phi>)
then show ?case sorry
next
  case (Next x1 \<phi>)
  then show ?case sorry
next
  case (Since \<phi>1 x2 \<phi>2)
  then show ?case sorry
next
case (Until \<phi>1 x2 \<phi>2)
  then show ?case sorry
next
  case (MatchF I r)
  then show ?case sorry
next
  case (MatchP x1 x2)
  then show ?case sorry
qed auto

(*
  case (Pred r ts)
  then have map_lemma: "map (Formula.eval_trm (xs @ z # v) \<circ> shiftTI b) ts =
                        map (Formula.eval_trm (z # xs @ v) \<circ> shiftTI 0) ts" by (simp add: shift_inter_t)
  show ?case by (auto simp: map_lemma split: option.splits)
next
  case c_top: (Let p b' \<phi> \<psi>)
  then consider (1) "(Formula.nfv \<phi>) \<noteq> 0 \<and>  b \<ge> Formula.nfv \<phi>"
               |(2) "(Formula.nfv \<phi>) = 0 \<and>  b \<ge> Formula.nfv \<phi>"
               |(3) "(Formula.nfv \<phi>) \<noteq> 0 \<and>  b < Formula.nfv \<phi>"
               |(4) "(Formula.nfv \<phi>) = 0 \<and>  b < Formula.nfv \<phi>" by linarith
  then show "?case"
  proof cases
    case 1
    then show ?thesis using shift_nfv_inc[OF a] sorry
  next
    case 2
    then have L: "(Formula.nfv \<phi>) = 0 \<or> b < Formula.nfv \<phi> " by auto
    from 2 have L2: "\<And>v. (\<exists>zs. length zs = b' \<and>
                     Formula.sat \<sigma> V (zs @ v) i (shiftI b \<phi>)) \<longleftrightarrow>  
                          (\<exists>zs. length zs = b' \<and> Formula.sat \<sigma> V (zs @ v) i (shiftI 0 \<phi>)) " sorry
    from 2 show ?thesis using shift_nfv_eq[OF L] sorry
  next
    case 3
    then show ?thesis sorry
  next 
    case 4
    then have L: "Formula.nfv \<phi> = 0 \<or> b < Formula.nfv \<phi>" by auto
    from 4 and c_top show ?thesis using shift_nfv_eq[OF L] 
          and shift_exists[where b'="b'" and \<sigma>="\<sigma>" and V="V" and b="b" and \<phi>="\<phi>"] 
      by (auto simp add: shift_nfv_0 )
  qed 
*)

lemma sat_shift: " length xs = b \<Longrightarrow> Formula.sat \<sigma> V (xs @ z # v) i (shiftI b \<phi>) = Formula.sat \<sigma> V (xs@v) i \<phi>"
proof -
  assume L: "length xs = b"
  then have B0:"Formula.sat \<sigma> V (xs @ z # v) i (shiftI b \<phi>) = Formula.sat \<sigma> V (z # xs @ v) i (shiftI 0 \<phi>)" 
    using shift_inter_f[where b=0 and k="b"] by auto
  have "Formula.sat \<sigma> V (z # xs @ v) i (shiftI 0 \<phi>) = Formula.sat \<sigma> V (xs @ v) i \<phi>" sorry
  oops

(*

using eval_trm_shiftTI proof(induction \<phi> arbitrary: v)
  case (Pred r ts)

  then have map_lemma: "map (Formula.eval_trm (xs @ z # v) \<circ> shiftTI b) ts = 
                        map (Formula.eval_trm (xs @ v)) ts" by auto
  show ?case by (auto simp: map_lemma split:option.splits)
next
  case (Let p b \<phi> \<psi>)
  have same_nfv: "Formula.nfv (Rewriting.shiftI 0 \<phi>) = Formula.nfv \<phi>" sorry
  then show ?case sorry      
next
  case (Exists \<phi>)
  then show ?case sorry (* use shift_inter later here*)
next
  case (Agg x1 x2 x3 x4 \<phi>)
  then show ?case sorry
next
  case (Prev I \<phi>)
  then show ?case sorry
next
  case (Next x1 \<phi>)
  then show ?case sorry
next
  case (Since \<phi>1 x2 \<phi>2)
  then show ?case sorry
next
  case (Until \<phi>1 x2 \<phi>2)
  then show ?case sorry
next
  case (MatchF x1 x2)
  then show ?case sorry
next
  case (MatchP x1 x2)
  then show ?case sorry
qed simp_all*)
  

(*"\<alpha> \<and> \<exists>x. \<beta> = \<exists>x. (shift \<alpha>) \<and> \<beta>" *)
lemma sat_rewrite_4: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Exists \<beta>)) = 
                    Formula.sat \<sigma> V v i (Formula.Exists (Formula.And (shift \<alpha>) \<beta> ))"
using shift_inter_f[where b=0 and k=0]  sorry


(*
lemma shift_preserve_sat_aux: "length xs = b \<Longrightarrow>
  Formula.sat \<sigma> V ( xs @ k # v) i (shiftI b \<phi>) = Formula.sat \<sigma> V (xs @ v) i \<phi>"
proof (induction \<phi> arbitrary: xs k v b)
  case (Pred r ts)
  then have map_eval_trm: "map (Formula.eval_trm (xs @ k # v) \<circ> (shiftTI b)) ts =
    map (Formula.eval_trm (xs @ v)) ts"
    using eval_trm_shiftTI
    by simp
  show ?case
    by (auto simp: map_eval_trm split: option.splits)
next
  case c: (Exists \<phi>) 
    assume a0: "xs=xs'@[x']" 
    assume a1: "b = length xs"
    assume "Formula.sat \<sigma> V (z #xs @ k # v) i (shiftI (Suc b) \<phi>)"
    then obtain z where Z: "Formula.sat \<sigma> V (z # xs @ k # v) i
                            (shiftI  (Suc b) \<phi>)" by auto
    from a0 and a1 and Z have LE: "Formula.sat \<sigma> V (z # xs' @ k # x' # v) i (shiftI b \<phi>)" 
      using shift_lower_f[where xs="z#xs'"] by (auto;simp)
    from c and Z and LE have "\<exists>z. Formula.sat \<sigma> V (z # xs @ v) i \<phi>" 
      by (metis Cons_eq_appendI length_Cons)
*)

(*
Lemmas that could be interesting in the future

lemma fv_rewrite[simp]: "fv (rewrite \<phi>) = fv \<phi>"

lemma "safe_formula \<phi> \<Longrightarrow> safe_formula (rewrite \<phi>)" 
*)

end
