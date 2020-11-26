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

fun rewrite_1 where
  "rewrite_1 (Formula.And a (Formula.Or b g)) =
     (let a' = rewrite_1 a;
          b' = rewrite_1 b;
          g' = rewrite_1 g
     in Formula.Or (Formula.And a' b') (Formula.And a' g'))"
| "rewrite_1 x = x"

lemma sat_rewrite_1: "Formula.sat \<sigma> V v i (rewrite_1 \<phi>) =
                      Formula.sat \<sigma> V v i \<phi>"

proof (induction \<phi> rule: rewrite_1.induct)
  case (1 a b g)
  then show ?case
    by (auto simp add: Let_def)
qed simp_all



fun rewrite_5 where
  "rewrite_5 (Formula.And a (Formula.Neg b)) =
     (let a' = rewrite_5 a;
          b' = rewrite_5 b
     in (Formula.And a' (Formula.Neg (Formula.And a' b'))))"
| "rewrite_5 x = x"

lemma sat_rewrite_5: "Formula.sat \<sigma> V v i (rewrite_5 \<phi>) =
                      Formula.sat \<sigma> V v i \<phi>"

proof (induction \<phi> rule: rewrite_5.induct)
  case (1 a b)
  then show ?case
    by (auto simp add: Let_def)
qed simp_all

definition shiftTI :: "nat \<Rightarrow> Formula.trm \<Rightarrow> Formula.trm" where
 "shiftTI k t = (case t of (Formula.Var i) \<Rightarrow> (if i < k then Formula.Var i 
                                               else Formula.Var (i + 1))
                           | _ \<Rightarrow> t)"
abbreviation "shiftT \<equiv> shiftTI 0"

(* Rules taken from Formula that I take inspiration from
lemma fvi_trm_plus: "x \<in> fvi_trm (b + c) t \<longleftrightarrow> x + c \<in> fvi_trm b t"
  by (induction t) auto

lemma fvi_trm_iff_fv_trm: "x \<in> fvi_trm b t \<longleftrightarrow> x + b \<in> fv_trm t"
  using fvi_trm_plus[where b=0 and c=b] by simp_all
*)


lemma shift_fv_in_term: "x + b  \<in> (Formula.fvi_trm b t) \<longleftrightarrow> 
                        (x+b+1) \<in> (Formula.fvi_trm b (shiftTI b t))" 
proof(induction t)
  case (Var i)
  then show ?case unfolding shiftTI_def by (cases "b\<le>i"; auto) 
next 
  case (Const c)
  then show ?case unfolding Formula.fvi_trm_def oops

primrec shiftRexI  where
  "shiftRexI sh (Regex.Skip n) = Regex.Skip n"
| "shiftRexI sh (Regex.Test a) = Regex.Test (sh a)"
| "shiftRexI sh (Regex.Plus a b) = Regex.Plus (shiftRexI sh a) (shiftRexI sh b)"
| "shiftRexI sh (Regex.Times a b) = Regex.Times (shiftRexI sh a) (shiftRexI sh b)"
| "shiftRexI sh (Regex.Star a) = Regex.Star (shiftRexI sh a)"
         

lemma shiftRexI_cong[fundef_cong]:
  "r = r' \<Longrightarrow> (\<And>a. a \<in> Regex.atms r \<Longrightarrow> sh a = sh' a) \<Longrightarrow> shiftRexI sh r = shiftRexI sh' r'"
  by (induct r arbitrary: r') auto

fun shiftI :: "nat \<Rightarrow> Formula.formula \<Rightarrow> Formula.formula" where
  "shiftI k (Formula.Pred r ts) = Formula.Pred r (map (shiftTI k) ts)"
| "shiftI k (Formula.Exists a) = Formula.Exists (shiftI (k + 1) a)"
| "shiftI k (Formula.Let nm n a b) = Formula.Let nm n (shiftI k a) (shiftI k b)"
| "shiftI k (Formula.Eq t1 t2) = Formula.Eq (shiftTI k t1) (shiftTI k t2)"
| "shiftI k (Formula.Less t1 t2) =  Formula.Less (shiftTI k t1) (shiftTI k t2)"
| "shiftI k (Formula.LessEq t1 t2) = Formula.LessEq (shiftTI k t1) (shiftTI k t2)"
| "shiftI k (Formula.Neg a) = Formula.Neg (shiftI k a)"
| "shiftI k (Formula.Or a b) = Formula.Or (shiftI k a) (shiftI k b)"
| "shiftI k (Formula.And a b) = Formula.And (shiftI k a) (shiftI k b)"
| "shiftI k (Formula.Ands as) = Formula.Ands (map (shiftI k) as)"  
| "shiftI k (Formula.Agg n op n2 t a) = Formula.Agg n op n2 (shiftTI k t) (shiftI k a)"
| "shiftI k (Formula.Prev \<I> a) = Formula.Prev \<I> (shiftI k a)"
| "shiftI k (Formula.Next \<I> a) = Formula.Next \<I> (shiftI k a)"
| "shiftI k (Formula.Since a1 \<I> a2) = Formula.Since (shiftI k a1) \<I> (shiftI k a2)"
| "shiftI k (Formula.Until a1 \<I> a2) = Formula.Until (shiftI k a1) \<I> (shiftI k a2)"
| "shiftI k (Formula.MatchF \<I> r) = Formula.MatchF \<I> (shiftRexI (shiftI k) r)"
| "shiftI k (Formula.MatchP \<I> r) = Formula.MatchP \<I> (shiftRexI (shiftI k) r)"
  
abbreviation shift where "shift \<equiv> shiftI 0"

fun rewrite_4 where
  "rewrite_4 (Formula.And a (Formula.Exists b)) =
     (let a' = rewrite_4 a;
          b' = rewrite_4 b
     in (Formula.And a' (Formula.Exists (Formula.And (shift a') b'))))"
| "rewrite_4 x = x"

(*Sequence of lemmas I think is needed to finally show sat_rewrite_4 *)
lemma shift_inc_fv: "x + b \<in> (fvi b \<phi>) \<longleftrightarrow> (x+b+1) \<in> (fv (shift \<phi>))" sorry

lemma shift_preserve_sat: "Formula.sat \<sigma> V v i \<phi> = Formula.sat \<sigma> V (z#v) i (shift \<phi>)" sorry

lemma shift_in_exists: " Formula.sat \<sigma> V v i \<phi> = Formula.sat \<sigma> V v i (Formula.Exists (shift \<phi>))" sorry

(*"\<alpha> \<and> \<exists>x. \<beta> = \<exists>x. (shift \<alpha>) \<and> \<beta>" *)
lemma shift_conj_in_exists: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Exists \<beta>)) = 
                    Formula.sat \<sigma> V v i (Formula.Exists (Formula.And (shift \<alpha>) \<beta> ))" sorry
                  
lemma sat_rewrite_4: "Formula.sat \<sigma> V v i (rewrite_4 \<phi>) = Formula.sat \<sigma> V v i \<phi>" sorry





(*
Lemmas that could be interesting in the future

lemma fv_rewrite[simp]: "fv (rewrite \<phi>) = fv \<phi>"

lemma "safe_formula \<phi> \<Longrightarrow> safe_formula (rewrite \<phi>)" 
*)

end
