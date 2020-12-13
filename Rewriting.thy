  theory Rewriting
    imports "MFODL_Monitor_Optimized.Formula" "MFODL_Monitor_Optimized.Regex" "MFODL_Monitor_Optimized.Trace"
begin

(*Section 2 of Normalization*)
lemma sat_2_1: "(\<forall>x. Formula.sat \<sigma> V (x#v) i \<alpha>) = Formula.sat \<sigma> V v i (Formula.Neg (Formula.Exists (Formula.Neg \<alpha>)))" by simp
lemma sat_2_2: "(Formula.sat \<sigma> V v i \<alpha> \<longrightarrow> Formula.sat \<sigma> V v i \<beta>) = (Formula.sat \<sigma> V v i (Formula.Or (Formula.Neg \<alpha>) \<beta>))" by simp
lemma sat_2_3: "(Formula.sat \<sigma> V v i \<alpha> \<longleftrightarrow> Formula.sat \<sigma> V v i \<beta>) = 
                (Formula.sat \<sigma> V v i (Formula.And (Formula.Or (Formula.Neg \<alpha>) \<beta>)(Formula.Or (Formula.Neg \<beta>) \<alpha>)))" by auto

(*------------setup and lemmas about shifting valuation list----------------------------*)

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


lemma no_shift_t:  "b' \<le> x3 \<Longrightarrow> Formula.fvi_trm b' (shiftTI (b + x3) t) \<subseteq> {0..<x3-b'} \<longleftrightarrow> Formula.fvi_trm b' t \<subseteq> {0..<x3-b'}"
  by (induction t; auto)

lemma no_shift:  "b' \<le> x3 \<Longrightarrow> Formula.fvi b' (shiftI (b + x3) \<phi>) \<subseteq> {0..<x3-b'} \<longleftrightarrow> Formula.fvi b' \<phi> \<subseteq> {0..<x3-b'}" (*MEETING: Do we want if on the top-lemma level?*)
proof(induction \<phi> arbitrary: b' x3)
  case (Ands x)
  then show ?case
    by fastforce (*MEETING: why do I have to instansiate b'? A: To obtain a faster proof by auto *)
next
  case (Pred r ts)
  thm no_shift_t[OF Pred(1)]
  then have helper: "((\<Union>a\<in>set ts. Formula.fvi_trm b' (shiftTI (b + x3) a)) \<subseteq> {0..<x3 - b'}) = 
                     (\<Union> (Formula.fvi_trm b' ` set ts) \<subseteq> {0..<x3 - b'})" using no_shift_t[OF Pred(1)] by (auto;simp)
  from Pred helper show ?case by auto
next
  case (Exists \<phi>)
  from Exists(2) have suc_lemma: "Suc b' \<le> Suc x3" by simp
  from Exists(1)[OF suc_lemma] show ?case by simp
next
  case (Agg xy op bb t \<phi>)
  from Agg(2) have plusbb: "b' + bb \<le> x3+bb" by simp
  from Agg(1)[OF plusbb] have helper1: "(Formula.fvi (b' + bb) (shiftI (b + (x3 + bb)) \<phi>)) \<subseteq> {0..<x3 - b'} =
                 ((Formula.fvi (b' + bb) \<phi>)  \<subseteq> {0..<x3 - b'})" by simp


  from no_shift_t[OF plusbb] have helper2: "(Formula.fvi_trm (b' + bb) (shiftTI (b + (x3 + bb)) t) \<subseteq> {0..<x3 - b'}) =
                                            (Formula.fvi_trm (b' + bb) t \<subseteq> {0..<x3 - b'}) " by simp
 
  from plusbb have helper3: "((if b' \<le> (if xy < b + x3 then xy else xy + 1) then {(if xy < b + x3 then xy else xy + 1) - b'} else {}) \<subseteq> {0..<x3 - b'}) =
                 ((if b' \<le> xy then {xy - b'} else {}) \<subseteq> {0..<x3 - b'})" by auto

  have helper: "(Formula.fvi (b' + bb) (shiftI (b + (x3 + bb)) \<phi>) \<union> 
                Formula.fvi_trm (b' + bb) (shiftTI (b + (x3 + bb)) t) \<union>
                (if b' \<le> (if xy < b + x3 then xy else xy + 1) then {(if xy < b + x3 then xy else xy + 1) - b'} else {}) \<subseteq> {0..<x3 - b'}) =
                (Formula.fvi (b' + bb) \<phi> \<union> 
                Formula.fvi_trm (b' + bb) t \<union> 
                (if b' \<le> xy then {xy - b'} else {}) \<subseteq> {0..<x3 - b'})" by (simp add: helper1 helper2 helper3)
  have assoc: "b + x3 + bb = b + (x3 + bb)" by simp
  show ?case by (simp only: shiftI.simps fvi.simps helper assoc) (*'simp only' because we aim for the helper-lemma as the last goal*)
next
  case (MatchF I r)
  then show ?case by (induction r;auto)
next
  case (MatchP I r)
  then show ?case by (induction r;auto)
qed (auto simp: no_shift_t)

lemma match_map_regex: "(\<And>k a. a \<in> Regex.atms r \<Longrightarrow> sat k (f a) \<longleftrightarrow> sat' k a) \<Longrightarrow>
  Regex.match sat (regex.map_regex f r) = Regex.match sat' r"
  by (induction r) simp_all

lemma sat_shift: "length xs = b \<Longrightarrow> Formula.sat \<sigma> V (xs @ z # v) i (shiftI b \<phi>) = Formula.sat \<sigma> V (xs@v) i \<phi>"
proof(induction \<phi> arbitrary: V i xs b)
  case pred: (Pred r ts)
  then have map_lemma: "map (Formula.eval_trm (xs @ z # v) \<circ> shiftTI (length xs)) ts
             = map (Formula.eval_trm (xs @ v)) ts" by (auto simp:eval_trm_shiftTI) 
  from pred show ?case by (auto split:option.splits simp:map_lemma)
  case (Exists \<phi>)
  then show ?case using Exists.IH[where xs= "_ # xs" and b="Suc b"] by (auto)
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
  have rw2: "fv (shiftI (b + x3) \<phi>) \<subseteq> {0..<x3} \<longleftrightarrow> fv \<phi> \<subseteq> {0..<x3}" using no_shift[where b'=0] by (auto)
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

(*Section 3 of Normalization chapter p. 79*)
lemma sat_3_a: "Formula.sat \<sigma> V v i (Formula.Neg (Formula.Neg \<alpha>)) = Formula.sat \<sigma> V v i \<alpha>" by auto
lemma sat_3_b: "Formula.sat \<sigma> V v i (Formula.Exists (shiftI 0 \<alpha>)) = Formula.sat \<sigma> V v i \<alpha>" using sat_shift[of "[]"] by auto (*Uses lemma proved in previous section*)
lemma sat_3_c1: "Formula.sat \<sigma> V v i (Formula.Neg(Formula.Or \<alpha> \<beta>)) = Formula.sat \<sigma> V v i (Formula.And (Formula.Neg \<alpha>) (Formula.Neg \<beta>)) " by auto
lemma sat_3_c2: "Formula.sat \<sigma> V v i (Formula.Neg(Formula.And \<alpha> \<beta>)) = Formula.sat \<sigma> V v i (Formula.Or (Formula.Neg \<alpha>) (Formula.Neg \<beta>)) " by auto

lemma sat_3_d: "Formula.sat \<sigma> V v i (Formula.Neg (Formula.Next I \<alpha>)) =
  Formula.sat \<sigma> V v i (Formula.Or (Formula.Neg (Formula.Next I Formula.TT))
                                  (Formula.Next I (Formula.Neg \<alpha>)))"  (*MEETING: So we are bloating up the formula because we want
                                                                        to push a negation closer to \<alpha>?*)
  by auto

(*Abbreviations corresponding to syntactic sugar presented in the phd-thesis*)
abbreviation diamond_b where "diamond_b I \<alpha> \<equiv> Formula.Since Formula.TT I \<alpha>"  
abbreviation square_b where "square_b I \<alpha> \<equiv> Formula.Neg (diamond_b I (Formula.Neg \<alpha>))"  
abbreviation diamond_w where "diamond_w I \<alpha> \<equiv> Formula.Until Formula.TT I \<alpha>"
abbreviation square_w where "square_w I \<alpha> \<equiv> Formula.Neg (diamond_w I (Formula.Neg \<alpha>))"
abbreviation excl_zero where "excl_zero I \<equiv> \<not> (mem 0 I)"

lemma sat_3_e1: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Neg (diamond_w I \<alpha>)) = Formula.sat \<sigma> V v i (square_w I (Formula.Neg \<alpha>))" 
  by simp

lemma sat_3_e2: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Neg (square_w I \<alpha>)) = Formula.sat \<sigma> V v i (diamond_w I (Formula.Neg \<alpha>))" 
  by auto

lemma sat_3_e3: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Neg (diamond_b I \<alpha>)) = Formula.sat \<sigma> V v i (square_b I (Formula.Neg \<alpha>))" 
  by auto

lemma sat_3_e4: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Neg (square_b I \<alpha>)) = Formula.sat \<sigma> V v i (diamond_b I (Formula.Neg \<alpha>))" 
  by auto

lemma sat_3_f1: "Formula.sat \<sigma> V v i (Formula.Neg (diamond_w I \<alpha>)) = Formula.sat \<sigma> V v i (square_w I (Formula.Neg \<alpha>))"
(*  using sat_3 ...
    apply (auto simp del: Formula.sat.simps) *)
  by simp

lemma sat_3_f2: "Formula.sat \<sigma> V v i (Formula.Neg (square_w I \<alpha>)) = Formula.sat \<sigma> V v i (diamond_w I (Formula.Neg \<alpha>))" 
  by auto

lemma sat_3_f3: "Formula.sat \<sigma> V v i (Formula.Neg (diamond_b I \<alpha>)) = Formula.sat \<sigma> V v i (square_b I (Formula.Neg \<alpha>))" 
  by auto

lemma sat_3_f4: "Formula.sat \<sigma> V v i (Formula.Neg (square_b I \<alpha>)) = Formula.sat \<sigma> V v i (diamond_b I (Formula.Neg \<alpha>))" 
  by auto

abbreviation release where "release \<beta> I \<gamma> \<equiv> Formula.Neg (Formula.Until (Formula.Neg \<beta>) I (Formula.Neg \<gamma>) )"
abbreviation trigger where "trigger \<beta> I \<gamma> \<equiv> Formula.Neg (Formula.Since (Formula.Neg \<beta>) I (Formula.Neg \<gamma>) )"

lemma sat_3_g1: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Neg (Formula.Since \<beta> I \<gamma>)) = 
                                 Formula.sat \<sigma> V v i (trigger (Formula.Neg \<beta>) I (Formula.Neg \<gamma>))" by simp

lemma sat_3_g2: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Neg (Formula.Until \<beta> I \<gamma>)) = 
                                 Formula.sat \<sigma> V v i (release (Formula.Neg \<beta>) I (Formula.Neg \<gamma>))" by simp

lemma sat_3_h1: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Neg (trigger \<beta> I \<gamma>)) = 
                                 Formula.sat \<sigma> V v i (Formula.Since (Formula.Neg \<beta>) I (Formula.Neg \<gamma>))" by auto

lemma sat_3_h2: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Neg (release \<beta> I \<gamma>)) = 
                                 Formula.sat \<sigma> V v i (Formula.Until (Formula.Neg \<beta>) I (Formula.Neg \<gamma>))" by auto

lemma sat_3_i1: "Formula.sat \<sigma> V v i (Formula.Neg (Formula.Since \<beta> I \<gamma>)) = 
                 Formula.sat \<sigma> V v i (trigger (Formula.Neg \<beta>) I (Formula.Neg \<gamma>))" by auto

lemma sat_3_i2: "Formula.sat \<sigma> V v i (Formula.Neg (Formula.Until \<beta> I \<gamma>)) = 
                 Formula.sat \<sigma> V v i (release (Formula.Neg \<beta>) I (Formula.Neg \<gamma>))" by force

lemma sat_3_j1: "Formula.sat \<sigma> V v i (Formula.Neg (trigger \<beta> I \<gamma>)) = 
                 Formula.sat \<sigma> V v i (Formula.Since (Formula.Neg \<beta>) I (Formula.Neg \<gamma>))" by auto

lemma sat_3_j2: "Formula.sat \<sigma> V v i (Formula.Neg (release \<beta> I \<gamma>)) = 
                 Formula.sat \<sigma> V v i (Formula.Until (Formula.Neg \<beta>) I (Formula.Neg \<gamma>))" by auto

(*
definition propagate_cond where
  "propagate_cond f1 f2 =
      (let rr1, b1 = rr f1;
           rr2, b2 = rr f2; 
           fv2 = Formula.fv f2 
      in  (rr1 \<inter> (fv2 \<setminus> rr2)) \<supset> \<emptyset> )"
*)

lemma sat_rewrite_1:
  "Formula.sat \<sigma> V v i (Formula.And a (Formula.Or b g)) =
   Formula.sat \<sigma> V v i (Formula.Or (Formula.And a b) (Formula.And a g))"
  by auto

lemma sat_rewrite_4: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Exists \<beta>)) = 
                    Formula.sat \<sigma> V v i (Formula.Exists (Formula.And (shift \<alpha>) \<beta> ))"
  using sat_shift[of "[]"] by auto

lemma sat_rewrite_5: "Formula.sat \<sigma> V v i (Formula.And a (Formula.Neg b))  =
                      Formula.sat \<sigma> V v i (Formula.And a (Formula.Neg (Formula.And a b)))"
  by auto

lemma sat_rewrite_6: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Since (Formula.And \<alpha> \<gamma>) I \<beta> ) =
                                      Formula.sat \<sigma> V v i (Formula.Since (Formula.And \<alpha> \<gamma>) I (Formula.And (diamond_w I \<alpha>) \<beta>))" by fastforce

lemma sat_rewrite_7: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Until (Formula.And \<alpha> \<gamma>) I \<beta> ) =
                                      Formula.sat \<sigma> V v i (Formula.Until (Formula.And \<alpha> \<gamma>) I (Formula.And (diamond_b I \<alpha>) \<beta>))" by fastforce


lemma sat_rewrite_12: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Since \<gamma> I \<beta>)) =
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Since \<gamma> I (Formula.And (diamond_w I \<alpha>)\<beta>)))" by auto

lemma sat_rewrite_13: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Until \<gamma> I \<beta>)) =
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Until \<gamma> I (Formula.And (diamond_b I \<alpha>)\<beta>)))" by auto

lemma sat_rewrite_14: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.And \<alpha> (diamond_b I \<beta>)) = 
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (diamond_b I (Formula.And (diamond_w I \<alpha> ) \<beta>)))" by auto

lemma sat_rewrite_15: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.And \<alpha> (diamond_w I \<beta>)) = 
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (diamond_w I (Formula.And (diamond_b I \<alpha> ) \<beta>)))" by auto

lemma sat_rewrite_16: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.And \<alpha> (square_b I \<beta>)) = 
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (square_b I (Formula.And (diamond_w I \<alpha> ) \<beta>)))" by auto

lemma sat_rewrite_17: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.And \<alpha> (square_w I \<beta>)) = 
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (square_w I (Formula.And (diamond_b I \<alpha> ) \<beta>)))" by auto

lemma sat_rewrite_18: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (diamond_b I \<beta>)) = 
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (diamond_b I (Formula.And (diamond_w I \<alpha> ) \<beta>)))" by auto

lemma sat_rewrite_19: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (diamond_w I \<beta>)) = 
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (diamond_w I (Formula.And (diamond_b I \<alpha> ) \<beta>)))" by auto

lemma sat_rewrite_20: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (square_b I \<beta>)) = 
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (square_b I (Formula.And (diamond_w I \<alpha> ) \<beta>)))" by auto

lemma sat_rewrite_21: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (square_w I \<beta>)) = 
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (square_w I (Formula.And (diamond_b I \<alpha> ) \<beta>)))" by auto

lemma sat_rewrite_22: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Prev I \<beta>)) = 
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Prev I (Formula.And (Formula.Next I \<alpha>) \<beta>)))"  by (auto split: nat.splits)

lemma sat_rewrite_23: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Next I \<beta>)) = 
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Next I (Formula.And (Formula.Prev I \<alpha>) \<beta>)))" by auto

(*non-trivial*)

(*abbreviation past_window where "past_window I \<alpha> \<equiv> Formula.Since \<alpha> I Formula.TT"
abbreviation future_window where "future_window I \<alpha> \<equiv> Formula.Until \<alpha> I Formula.TT"*)


lift_definition init_int :: "\<I> \<Rightarrow> \<I>" is "\<lambda>(_,n). (0, n)" using zero_enat_def by auto

lemma left_init_int[simp]: "left (init_int I) = 0"  by (transfer; auto)+
lemma right_init_int[simp]: "right (init_int I) = right I"  by (transfer; auto)+

lemma interval_imp: "mem i I \<Longrightarrow> mem i (init_int I)" by simp


lemma nat_less_than_range: "\<And>i j:: nat. k \<in> {i..j} \<and> k' \<in>{i..j} \<Longrightarrow> (k-k') \<le> (j-i)" 
proof -
  fix i j :: nat assume A:"k \<in> {i..j} \<and> k' \<in>{i..j}"
  show "(k-k') \<le> (j-i)"
  proof(cases "i\<le>j")
  case True
  then show ?thesis using A diff_le_mono2 by auto
next
  case False
  then show ?thesis using A by auto
qed
qed

lemma mem_of_init: "mem j I \<Longrightarrow>  \<forall>k\<le>j. mem k (init_int I)" 
proof(induction j)
  case 0
  then show ?case by simp
next
  case (Suc j)
  then show ?case by (simp add: order_subst2)
qed

lemma nat_less_mem_of_init: "\<And>i j:: nat. k \<in> {i..j} \<and> k' \<in>{i..j} \<Longrightarrow> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<Longrightarrow>  mem (\<tau> \<sigma> k - \<tau> \<sigma> k') (init_int I)" 
proof -
  fix i j :: nat assume A:"k \<in> {i..j} \<and> k' \<in>{i..j}" "mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I"
  then have "(\<tau> \<sigma> k - \<tau> \<sigma> k') \<le> (\<tau> \<sigma> j - \<tau> \<sigma> i)" using nat_less_than_range by auto
  then show " mem (\<tau> \<sigma> k - \<tau> \<sigma> k') (init_int I)" using A(2) mem_of_init by blast
qed
 



lemma sat_rewrite_8: "Formula.sat \<sigma> V v i (Formula.Since \<beta> I (Formula.And \<alpha> \<gamma>) ) =
                      Formula.sat \<sigma> V v i (Formula.Since (Formula.And (diamond_b (init_int I) \<alpha>) \<beta>) I (Formula.And \<alpha> \<gamma>))"
(is "?L = ?R")
proof(rule iffI)
  assume L:?L
  then obtain j where j:"j\<le>i" "mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I" "Formula.sat \<sigma> V v j \<alpha>" "Formula.sat \<sigma> V v j \<gamma>" "(\<forall>k\<in>{j<..i}. Formula.sat \<sigma> V v k \<beta>)" by auto

  have "\<forall>k\<in>{j<..i}. j\<le>k" by simp
  moreover have "\<forall>k\<in>{j<..i}. mem (\<tau> \<sigma> k - \<tau> \<sigma> j) (init_int I)" using nat_less_mem_of_init[OF _ j(2)] by auto
  moreover have "\<forall>k\<in>{j<..i}. Formula.sat \<sigma> V v j \<alpha>" using j(3) by auto
  ultimately have "\<forall>k\<in>{j<..i}. \<exists>j\<le>k. mem (\<tau> \<sigma> k - \<tau> \<sigma> j) (init_int I) \<and> Formula.sat \<sigma> V v j \<alpha>" by fast

  then show ?R using L j by auto
qed auto

lemma sat_rewrite_9: "Formula.sat \<sigma> V v i (Formula.Until \<beta> I (Formula.And \<alpha> \<gamma>)) =
                                      Formula.sat \<sigma> V v i (Formula.Until (Formula.And (diamond_w (init_int I) \<alpha>) \<beta>) I (Formula.And \<alpha> \<gamma>))" 
(is "?L = ?R")
proof(rule iffI)
  assume L:?L
  then obtain j where j: "j\<ge>i" "mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I" "Formula.sat \<sigma> V v j \<alpha>"  "Formula.sat \<sigma> V v j \<gamma>" "(\<forall>k\<in>{i..<j}. Formula.sat \<sigma> V v k \<beta>)" by auto

  have "\<forall>k\<in>{i..<j}. j\<ge>k" by auto
  moreover have "\<forall>k\<in>{i..<j}. mem (\<tau> \<sigma> j - \<tau> \<sigma> k) (init_int I)" using nat_less_mem_of_init[OF _ j(2)] by auto
  moreover have "\<forall>k\<in>{i..<j}. Formula.sat \<sigma> V v j \<alpha>" using j(3) by auto
  ultimately have "\<forall>k\<in>{i..<j}. \<exists>j\<ge>k. mem (\<tau> \<sigma> j - \<tau> \<sigma> k) (init_int I) \<and> Formula.sat \<sigma> V v j \<alpha>" by fast

  then show ?R using L j by auto
qed auto

lemma sat_rewrite_11: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Until \<beta> I \<gamma>)) =
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Until (Formula.And (diamond_b (init_int I) \<alpha>) \<beta>) I \<gamma>))" 
(is "?L = ?R")
proof(rule iffI)
  assume L:?L
  then obtain j where j: "j\<ge>i" "mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I" "Formula.sat \<sigma> V v j \<gamma>" "(\<forall>k\<in>{i..<j}.  Formula.sat \<sigma> V v i \<alpha> \<and> Formula.sat \<sigma> V v k \<beta>)" by auto
  then have "\<forall>k\<in>{i..<j}. mem (\<tau> \<sigma> k - \<tau> \<sigma> i) (init_int I)" using nat_less_mem_of_init[OF _ j(2)] by fastforce
  then show ?R using L j by fastforce
qed auto


lemma sat_rewrite_10: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Since \<beta> I \<gamma>)) =
                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Since (Formula.And (diamond_w (init_int I) \<alpha>) \<beta>) I \<gamma>))"
(is "?L = ?R")
proof(rule iffI)
  assume L:?L
  then obtain j where j: "j\<le>i" "mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I" "Formula.sat \<sigma> V v j \<gamma>" "(\<forall>k\<in>{j<..i}. Formula.sat \<sigma> V v i \<alpha> \<and> Formula.sat \<sigma> V v k \<beta>)" by auto
  then have "\<forall>k\<in>{j<..i}. mem (\<tau> \<sigma> i - \<tau> \<sigma> k) (init_int I)" using nat_less_mem_of_init[OF _ j(2)] by fastforce
  then show ?R using L j by fastforce
qed auto

lemma sat_rewrite_2: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (release \<beta> I \<gamma>)) =
                                      Formula.sat \<sigma> V v i (Formula.And \<alpha> (release (Formula.And \<beta> (diamond_b (init_int I) \<alpha>)) I (Formula.And \<gamma> (diamond_b I \<alpha>))))" sorry

lemma sat_rewrite_3: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.And \<alpha> (trigger \<beta> I \<gamma>)) =
                                      Formula.sat \<sigma> V v i (Formula.And \<alpha> (trigger (Formula.And \<beta> (diamond_w I \<alpha>)) I (Formula.And \<gamma> (diamond_w I \<alpha>))))" sorry




(*lemma \<tau>_mono2: "j \<le> k \<and> k \<le> j' \<and> j' \<le> i \<Longrightarrow> \<tau> \<sigma> j' - \<tau> \<sigma> k \<le> \<tau> \<sigma> i - \<tau> \<sigma> j"
    by (force dest: \<tau>_mono[of _ _ \<sigma>])*)


end