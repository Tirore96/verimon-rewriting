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

lemma sat_1:
  "Formula.sat \<sigma> V v i (Formula.And a (Formula.Or b g)) =
   Formula.sat \<sigma> V v i (Formula.Or (Formula.And a b) (Formula.And a g))"
  by auto

lemma sat_rewrite_5: "Formula.sat \<sigma> V v i (Formula.And a (Formula.Neg b))  = 
                      Formula.sat \<sigma> V v i (Formula.And a (Formula.Neg (Formula.And a b)))"
  by auto

(*------------setup for proving set_rewrite_4----------------------------*)

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

lemma eval_trm_shiftTI: "length xs = b \<Longrightarrow>
  Formula.eval_trm (xs @ z # v) (shiftTI b t) = Formula.eval_trm (xs @ v) t"
  by (induct b t rule: shiftTI.induct) (auto simp: nth_append split: trm.splits)

lemma shift_fv_in_t: "x+1 \<in> Formula.fvi_trm b (shiftTI b t) \<longleftrightarrow> x  \<in> Formula.fvi_trm b t" 
   by (induction t;auto)

primrec shiftI :: "nat \<Rightarrow> Formula.formula \<Rightarrow> Formula.formula" where
  "shiftI k (Formula.Pred r ts) = Formula.Pred r (map (shiftTI k) ts)"
| "shiftI k (Formula.Exists a) = Formula.Exists (shiftI (Suc k) a)"
| "shiftI k (Formula.Let nm n a b) = Formula.Let nm n a (shiftI k b)" (*fixed error, a is not shifted*)
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

lemma shift_fv_in_f: "(x+1) \<in> (Formula.fvi b (shiftI b \<phi>)) \<longleftrightarrow> x \<in> (Formula.fvi b \<phi>)"
using shift_fv_in_t proof (induction b \<phi> rule: fvi.induct)
  case (16 b I r)
  then show ?case by (induct r;auto)
next
  case (17 b I r)
  then show ?case by (induct r;auto)
qed (auto)
(*
lemma shift_inter_t: "length xs = b \<Longrightarrow> length ys = k \<Longrightarrow> 
                 Formula.eval_trm (xs @ ys @ z # v) (shiftTI (b + k) t) =
                 Formula.eval_trm (xs @ z # ys @ v) (shiftTI b t)" by (induction t;auto simp: nth_append)

lemma shift_inter_f: "length xs = b \<Longrightarrow> length ys = k \<Longrightarrow>
                 Formula.sat \<sigma> V (xs @ ys @ z # v) i (shiftI (b + k) \<phi>) =
                 Formula.sat \<sigma> V (xs @ z # ys @ v) i (shiftI b \<phi>)"
proof(induction \<phi> arbitrary: V xs b i) (*needed arb V for let, i for Prev*)
case (Pred r ts)
  then have map_lemma: "map (Formula.eval_trm (xs @ ys @ z # v) \<circ> shiftTI (b + k)) ts =
                        map (Formula.eval_trm (xs @ z # ys @ v) \<circ> shiftTI b) ts" by (simp add: shift_inter_t)
  show ?case by (auto simp: map_lemma split: option.splits) 
next
  case exists: (Exists \<phi>)
  then show ?case using exists.IH[where xs= "_ # xs" and b="Suc b"] by (auto)
next
  case agg: (Agg x1 x2 x3 x4 \<phi>)
  then show ?case using agg.IH sorry (*MEETING*)
next
  case prev: (Prev I \<phi>)
  then show ?case by (auto split:nat.splits)
next
  case (MatchF I r)
  then show ?case 
  proof (induction r)
  case (Times r1 r2)
  then show ?case sorry (*MEETING*)
  next
  case (Star r)
  then show ?case sorry
  qed auto
next
  case (MatchP I r)
  then show ?case 
  proof (induction r)
  case (Times r1 r2)
  then show ?case sorry
  next
  case (Star r)
  then show ?case sorry
  qed auto
qed (auto simp: shift_inter_t)


lemma first_shift: "Formula.sat \<sigma> V (z # xs @ v) i (shiftI 0 \<phi>) = Formula.sat \<sigma> V (xs @ v) i \<phi>"
using eval_trm_shiftTI[of "[]"] proof(induction \<phi> arbitrary: V xs i) (*arbitrary because of Let*)
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
then show ?case by (auto split:nat.splits)
next
  case (MatchF I r)
  then show ?case 
  proof(induction r)
    case (Times r1 r2)
    then show ?case sorry
  next
    case (Star r)
    then show ?case sorry
  qed auto
next
  case (MatchP I r)
  then show ?case
  proof(induction r)
    case (Times r1 r2)
    then show ?case sorry
  next
    case (Star r)
    then show ?case sorry
  qed auto
qed auto
*)
(*lemma sat_shift: " length xs = b \<Longrightarrow> Formula.sat \<sigma> V (xs @ z # v) i (shiftI b \<phi>) = Formula.sat \<sigma> V (xs@v) i \<phi>"
proof -
  assume L: "length xs = b"
  then have B0:"Formula.sat \<sigma> V (xs @ z # v) i (shiftI b \<phi>) = Formula.sat \<sigma> V (z # xs @ v) i (shiftI 0 \<phi>)" 
    using shift_inter_f[where b=0 and k="b"] by auto
  have S:"Formula.sat \<sigma> V (z # xs @ v) i (shiftI 0 \<phi>) = Formula.sat \<sigma> V (xs @ v) i \<phi>" by (auto simp: first_shift)
  from L show ?thesis by (auto simp: B0 S)
qed*)


lemma match_map_regex: "(\<And>k a. a \<in> Regex.atms r \<Longrightarrow> sat k (f a) \<longleftrightarrow> sat' k a) \<Longrightarrow>
  Regex.match sat (regex.map_regex f r) = Regex.match sat' r"
  by (induction r) simp_all

lemma sat_shift: "length xs = b \<Longrightarrow> Formula.sat \<sigma> V (xs @ z # v) i (shiftI b \<phi>) = Formula.sat \<sigma> V (xs@v) i \<phi>"
proof(induction \<phi> arbitrary: V i xs b)
  case pred: (Pred r ts)
  then have map_lemma: "map (Formula.eval_trm (xs @ z # v) \<circ> shiftTI (length xs)) ts
             = map (Formula.eval_trm (xs @ v)) ts" by (auto simp:eval_trm_shiftTI) 
  from pred show ?case by (auto split:option.splits simp:map_lemma)
  case ex: (Exists \<phi>)
  then show ?case using ex.IH[where xs= "_ # xs" and b="Suc b"] by (auto)
next
  case (Agg x1 x2 x3 x4 \<phi>)
  have rw11: "Formula.sat \<sigma> V (zs @ xs @ z # v) i (shiftI (b + x3) \<phi>) \<longleftrightarrow>
    Formula.sat \<sigma> V (zs @ xs @ v) i \<phi>" if "length zs = x3" for zs
    using Agg(1)[of "zs @ xs"] Agg(2) that
    by simp
  have rw12:
    "Formula.eval_trm (zs @ xs @ z # v) (shiftTI (b + x3) x4) =
    Formula.eval_trm (zs @ xs @ v) x4" if "length zs = x3" for zs
    using eval_trm_shiftTI[of "zs @ xs"] Agg(2) that
    by simp
  have rw1: "\<And>x. {zs. length zs = x3 \<and>
      Formula.sat \<sigma> V (zs @ xs @ z # v) i (shiftI (b + x3) \<phi>) \<and>
      Formula.eval_trm (zs @ xs @ z # v) (shiftTI (b + x3) x4) = x} =
    {zs. length zs = x3 \<and>
      Formula.sat \<sigma> V (zs @ xs @ v) i \<phi> \<and> Formula.eval_trm (zs @ xs @ v) x4 = x}"
    using rw11 rw12 by auto
  have rw2: "fv (shiftI (b + x3) \<phi>) \<subseteq> {0..<x3} \<longleftrightarrow> fv \<phi> \<subseteq> {0..<x3}"
    using (*fvi_iff_fv*) shift_fv_in_f
    sorry
  show ?case
    using Agg(2)
    by (auto simp add: rw1 rw2 nth_append)
next
  case (Prev x1 \<phi>)
  then show ?case by (auto split:nat.splits)
next
  case (MatchF I r)
  have rw: "Regex.match (Formula.sat \<sigma> V (xs @ z # v)) (regex.map_regex (shiftI b) r) =
    Regex.match (Formula.sat \<sigma> V (xs @ v)) r"
    apply (rule match_map_regex)
    using MatchF
    by auto
  show ?case
    using MatchF
    by (simp add: rw)
next
  case (MatchP I r)
  have rw: "\<And>j. Regex.match (Formula.sat \<sigma> V (xs @ z # v)) (regex.map_regex (shiftI b) r) =
    Regex.match (Formula.sat \<sigma> V (xs @ v)) r"
    apply (rule match_map_regex)
    using MatchP
    by auto
  show ?case
    by (simp add: rw)
qed (auto simp: eval_trm_shiftTI)



(*"\<alpha> \<and> \<exists>x. \<beta> = \<exists>x. (shift \<alpha>) \<and> \<beta>" *)
lemma sat_rewrite_4: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Exists \<beta>)) = 
                    Formula.sat \<sigma> V v i (Formula.Exists (Formula.And (shift \<alpha>) \<beta> ))"
using sat_shift[of "[]"] by auto




end
