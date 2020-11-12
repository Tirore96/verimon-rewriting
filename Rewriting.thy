theory Rewriting
  imports "MFODL_Monitor_Optimized.Formula"
begin

fun rewrite where
  "rewrite (Formula.And f (Formula.Or g h)) =
     (let f' = rewrite f;
          g' = rewrite g;
          h' = rewrite h
     in Formula.Or (Formula.And f' g') (Formula.And f' h'))"
(*| "rewrite (Formula.Exists \<phi>) = (if 0 \<in> fv \<phi> then Formula.Exists (rewrite \<phi>) else rewrite \<phi>)"*)
| "rewrite x = x"

thm rewrite.induct

lemma sat_rewrite: "Formula.sat \<sigma> V v i (rewrite \<phi>) = Formula.sat \<sigma> V v i \<phi>"
proof (induct \<phi> arbitrary: v rule: rewrite.induct)
  case (1 f g h)
  then show ?case
    by (auto simp add: Let_def)
(*next
  case (2 \<phi>)
  then show ?case
    apply auto
    sorry*)
qed simp_all

lemma fv_rewrite[simp]: "fv (rewrite \<phi>) = fv \<phi>"
proof (induct \<phi> rule: rewrite.induct)
  case (1 f g h)
  then show ?case
    by (auto simp add: Let_def)
qed simp_all

lemma "safe_formula \<phi> \<Longrightarrow> safe_formula (rewrite \<phi>)"
proof (induct \<phi> rule: rewrite.induct)
  case (1 f g h)
  then show ?case
    by (auto simp: safe_assignment_def Let_def)
qed simp_all

end
