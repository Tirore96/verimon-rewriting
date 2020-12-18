  theory Rewriting
    imports "MFODL_Monitor_Optimized.Formula" "MFODL_Monitor_Optimized.Regex" "MFODL_Monitor_Optimized.Trace"
begin



(*
definition propagate_cond where
  "propagate_cond f1 f2 =
      (let rr1, b1 = rr f1;
           rr2, b2 = rr f2; 
           fv2 = Formula.fv f2 
      in  (rr1 \<inter> (fv2 \<setminus> rr2)) \<supset> \<emptyset> )"
*)

(*fun tvars :: "Formula.trm \<Rightarrow> nat set" where
  "tvars (Var x) = (if b \<le> x then {x} else {})"
| "tvars (Const _) = {}"
| "tvars (Plus x y) = tvars b x \<union> tvars b y"
| "tvars (Minus x y) = tvars b x \<union> tvars b y"
| "tvars (UMinus x) = tvars b x"
| "tvars (Mult x y) = tvars b x \<union> tvars b y"
| "tvars (Div x y) = tvars b x \<union> tvars b y"
| "tvars (Mod x y) = tvars b x \<union> tvars b y"
| "tvars (F2i x) = tvars b x"
| "tvars (I2f x) = tvars b x"*)


primrec rr_regex where
  "rr_regex rr (Regex.Skip n) = {}"
| "rr_regex rr (Regex.Test \<phi>) = rr \<phi>"
| "rr_regex rr (Regex.Plus r s) = rr_regex rr r \<union> rr_regex rr s"
| "rr_regex rr (Regex.Times r s) = rr_regex rr r \<union> rr_regex rr s"
| "rr_regex rr (Regex.Star r) = rr_regex rr r"


fun rr :: "nat \<Rightarrow> Formula.formula \<Rightarrow> nat set" where
  "rr b (Formula.Pred r ts) = (\<Union>t\<in>set ts. Formula.fvi_trm b t)"
| "rr b (Formula.Let p _ \<phi> \<psi>) = rr b \<psi>"
| "rr  b(Formula.Eq t1 t2) = (case (t1,t2) of
                             (Formula.Var x,Formula.Const _) \<Rightarrow> {x-b}
                            |(Formula.Const _,Formula.Var x) \<Rightarrow> {x-b}
                            | _ \<Rightarrow> {})"

| "rr b (Formula.Less t1 t2) = (case (t1,t2) of
                                              (Formula.Var x,Formula.Const _) \<Rightarrow> {x-b}
                                             |_ \<Rightarrow> {})"
| "rr b (Formula.LessEq t1 t2) = (case (t1,t2) of
                                              (Formula.Var x,Formula.Const _) \<Rightarrow> {x-b}
                                             |_ \<Rightarrow> {})"
| "rr b (Formula.Or \<phi> \<psi>) = rr b \<phi> \<inter> rr b \<psi>"
| "rr b (Formula.And \<phi> \<psi>) = rr b \<phi> \<union> rr b \<psi>"
| "rr b (Formula.Ands \<phi>s) = (let xs = map (rr b) \<phi>s in \<Union>x\<in>set xs. x)"
| "rr b (Formula.Exists \<phi>) = (if (0 \<in> rr 0 \<phi>) then rr (Suc b) \<phi>
                                            else {})"
| "rr b (Formula.Agg y \<omega> b' f \<phi>) = {}" (*How?*)
| "rr b (Formula.Prev I \<phi>) = rr b \<phi>"
| "rr b (Formula.Next I \<phi>) = rr b \<phi>"
| "rr b (Formula.Since \<phi> I \<psi>) = rr b \<psi>"
| "rr b (Formula.Until \<phi> I \<psi>) = rr b \<psi>"
(*| "rr b (Formula.MatchF I r) = rr_regex (rr b) r"
| "rr b (Formula.MatchP I r) = rr_regex (rr b) r"   Termination issues*)
| "rr b (Formula.Neg \<beta>) = (case \<beta> of
                            Formula.Until (Formula.Neg \<beta>) I (Formula.Neg \<gamma>) \<Rightarrow> rr b \<gamma>
                           |Formula.Since (Formula.Neg \<beta>) I (Formula.Neg \<gamma>) \<Rightarrow> rr b \<gamma> )"  (*release and trigger cases*)
| "rr b (formula.MatchF I r) = {}"
| "rr b (formula.MatchP I r) = {}"

definition "prop_cond f1 f2 =
       (let rr1 = rr 0 f1;
           rr2 = rr 0 f2; 
           fv2 = Formula.fv f2 
       in  (rr1 \<inter> (fv2-rr2)) \<noteq> {})"


(*let rec rr = function
  | Pred p -> (Predicate.pvars p, true)

  | Equal (t1, t2) ->
    (match t1, t2 with
     | Var x, Cst c -> ([x], true)
     | Cst c, Var x -> ([x], true)
     | _ -> ([], true) )
  | Less (t1, t2) ->
    (match t1, t2 with
     | Var x, Var y when x=y -> ([x], true)
     | Var x, Cst c -> ([x], true)
     | _ -> ([], true))
  | LessEq (t1, t2) ->
    (match t1, t2 with
     | Var x, Cst c -> ([x], true)
     | _ -> ([], true))

  | Neg (Equal (t1, t2)) ->
    (match t1, t2 with
     | Var x, Var y when x=y -> ([x], true)
     | _ -> ([], true))
  | Neg (Less (t1, t2)) ->
    (match t1, t2 with
     | Cst c, Var x -> ([x], true)
     | _ -> ([], true))
  | Neg (LessEq (t1, t2)) ->
    (match t1, t2 with
     | Var x, Var y when x=y -> ([x], true)
     | Cst c, Var x -> ([x], true)
     | _ -> ([], true))

  | Neg f ->
    let _, b = rr f in
    ([], b)

  | And (f1, Equal (Var x, Var y)) ->
    let (rr1, b) = rr f1 in
    if List.mem x rr1 then
      (Misc.union rr1 [y], b)
    else if List.mem y rr1 then
      (Misc.union rr1 [x], b)
    else
      (rr1, b)

  | And (f1, Less (Var x, Var y)) ->
    let (rr1, b) = rr f1 in
    if List.mem y rr1  || x = y then
      (Misc.union rr1 [x], b)
    else
      (rr1, b)

  | And (f1, Neg (Less (Var x, Var y))) ->
    let (rr1, b) = rr f1 in
    if List.mem x rr1 then
      (Misc.union rr1 [y], b)
    else
      (rr1, b)

  | And (f1, (LessEq (t1, t2)))
  | And (f1, Neg (LessEq (t1, t2))) ->
    let (rr1, b) = rr f1 in
    if b then
      let vars1 = Predicate.tvars t1 in
      let vars2 = Predicate.tvars t2 in
      (rr1, (Misc.subset vars1 rr1) &&
            (Misc.subset vars2 rr1))
    else
      (rr1, b)
  (* failwith "[Rewriting.rr] not yet" *)

  | And (f1, f2) ->
    let (rr1, b1) = rr f1 in
    let (rr2, b2) = rr f2 in
    (Misc.union rr1 rr2, b1 && b2)

  | Or (f1, f2) ->
    let (rr1, b1) = rr f1 in
    let (rr2, b2) = rr f2 in
    (List.filter (fun v -> List.mem v rr1) rr2, b1 && b2)

  | Exists (vl, f) ->
    let (rrf, b) = rr f in
    let rec aux crt_rrf crt_b = function
      | [] -> crt_rrf, crt_b
      | v :: rest ->
        if List.mem v crt_rrf then
          let new_rrf = List.filter (fun x -> x<>v) crt_rrf in
          aux new_rrf crt_b rest
        else
          crt_rrf, false
    in
    aux rrf b vl
  (* if List.mem v rrf then *)
  (*   (List.filter (fun x -> x<>v) rrf, b) *)
  (* else *)
  (*   (rrf, false) *)

  | Aggreg (ytyp, y, op, x, glist, f) ->
    let rrf, b = rr f in
    let frr = List.filter (fun z -> List.mem z glist) rrf in
    y :: frr, b

  | Prev (intv, f) -> rr f
  | Next (intv, f) -> rr f
  | Eventually (intv, f) -> rr f
  | Once (intv, f) -> rr f

  | Since (intv, f1, f2)
  | Until (intv, f1, f2) ->
    let _, b1 = rr f1 in
    let rr2, b2 = rr f2 in
    (rr2, b1 && b2)
  | Frex (_,r) -> rr_re true r 
  | Prex (_,r) -> rr_re false r 
  | Let (_,_,f) -> rr f
  | _ -> failwith "[Rewriting.rr] internal error"
  and rr_re future = function 
  | Wild -> ([],true)
  | Test f -> rr f
  | Concat (r1,r2) -> let (rr1,b1) = rr_re future r1 in
                      let (rr2,b2) = rr_re future r2 in
                      (rr2, b1 && b2)
  | Plus (r1, r2) ->  let (rr1,b1) = rr_re future r1 in
                      let (rr2,b2) = rr_re future r2 in
                      (List.filter (fun v -> List.mem v rr1) rr2, b1 && b2)
  | Star r -> rr_re future r*)


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
abbreviation FF where "FF \<equiv> Formula.Exists (Formula.Neg (Formula.Eq (Formula.Var 0) (Formula.Var 0)))"
abbreviation TT where "TT \<equiv> Formula.Neg FF"
lemma FF_simp: "FF = Formula.FF" by (simp add: Formula.FF_def)
lemma TT_simp: "TT = Formula.TT" by (simp add: Formula.TT_def FF_simp)

abbreviation diamond_b where "diamond_b I \<alpha> \<equiv> Formula.Since TT I \<alpha>"  
abbreviation square_b where "square_b I \<alpha> \<equiv> Formula.Neg (diamond_b I (Formula.Neg \<alpha>))"  
abbreviation diamond_w where "diamond_w I \<alpha> \<equiv> Formula.Until TT I \<alpha>"
abbreviation square_w where "square_w I \<alpha> \<equiv> Formula.Neg (diamond_w I (Formula.Neg \<alpha>))"
abbreviation excl_zero where "excl_zero I \<equiv> \<not> (mem 0 I)"

(*Maybe interesting lemma for intution*)
lemma strict_until: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Until \<phi> I \<psi>) = 
                                    (\<exists>j>i. mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and> Formula.sat \<sigma> V v j \<psi> \<and> (\<forall>k \<in> {i..< j}. Formula.sat \<sigma> V v k \<phi>))"  using le_eq_less_or_eq by auto

(*duplications of sat_3_f*  not needed*)
(*
lemma sat_3_e1: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Neg (diamond_w I \<alpha>)) = Formula.sat \<sigma> V v i (square_w I (Formula.Neg \<alpha>))" 
  by simp

lemma sat_3_e2: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Neg (square_w I \<alpha>)) = Formula.sat \<sigma> V v i (diamond_w I (Formula.Neg \<alpha>))" 
  by auto

lemma sat_3_e3: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Neg (diamond_b I \<alpha>)) = Formula.sat \<sigma> V v i (square_b I (Formula.Neg \<alpha>))" 
  by auto

lemma sat_3_e4: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Neg (square_b I \<alpha>)) = Formula.sat \<sigma> V v i (diamond_b I (Formula.Neg \<alpha>))" 
  by auto*)

lemma sat_3_f1: "Formula.sat \<sigma> V v i (Formula.Neg (diamond_w I \<alpha>)) = Formula.sat \<sigma> V v i (square_w I (Formula.Neg \<alpha>))"
  by simp

lemma sat_3_f2: "Formula.sat \<sigma> V v i (Formula.Neg (square_w I \<alpha>)) = Formula.sat \<sigma> V v i (diamond_w I (Formula.Neg \<alpha>))" 
  by auto

lemma sat_3_f3: "Formula.sat \<sigma> V v i (Formula.Neg (diamond_b I \<alpha>)) = Formula.sat \<sigma> V v i (square_b I (Formula.Neg \<alpha>))" 
  by auto

lemma sat_3_f4: "Formula.sat \<sigma> V v i (Formula.Neg (square_b I \<alpha>)) = Formula.sat \<sigma> V v i (diamond_b I (Formula.Neg \<alpha>))" 
  by auto

abbreviation (input) release where "release \<beta> I \<gamma> \<equiv> Formula.Neg (Formula.Until (Formula.Neg \<beta>) I (Formula.Neg \<gamma>) )"
abbreviation trigger where "trigger \<beta> I \<gamma> \<equiv> Formula.Neg (Formula.Since (Formula.Neg \<beta>) I (Formula.Neg \<gamma>) )"

abbreviation release2 where "release2 \<beta> I \<gamma> \<equiv> Formula.And (Formula.Neg (Formula.Until (Formula.Neg \<beta>) I (Formula.Neg \<gamma>) ))
                                                          (diamond_w I Formula.TT)"


lemma sat_release2: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (release2 \<beta> I \<gamma>) \<Longrightarrow>
                     (\<exists>j>i. mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and> ( Formula.sat \<sigma> V v j \<gamma> \<or> (\<exists>k\<in>{i..<j}. Formula.sat \<sigma> V v k \<beta>)))" by fastforce

(*Duplication again*)
(*
lemma sat_3_g1: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Neg (Formula.Since \<beta> I \<gamma>)) = 
                                 Formula.sat \<sigma> V v i (trigger (Formula.Neg \<beta>) I (Formula.Neg \<gamma>))" by simp

lemma sat_3_g2: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Neg (Formula.Until \<beta> I \<gamma>)) = 
                                 Formula.sat \<sigma> V v i (release (Formula.Neg \<beta>) I (Formula.Neg \<gamma>))" by simp

lemma sat_3_h1: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Neg (trigger \<beta> I \<gamma>)) = 
                                 Formula.sat \<sigma> V v i (Formula.Since (Formula.Neg \<beta>) I (Formula.Neg \<gamma>))" by auto

lemma sat_3_h2: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Neg (release \<beta> I \<gamma>)) = 
                                 Formula.sat \<sigma> V v i (Formula.Until (Formula.Neg \<beta>) I (Formula.Neg \<gamma>))" by auto*)

lemma sat_3_i1: "Formula.sat \<sigma> V v i (Formula.Neg (Formula.Since \<beta> I \<gamma>)) = 
                 Formula.sat \<sigma> V v i (trigger (Formula.Neg \<beta>) I (Formula.Neg \<gamma>))" by auto

lemma sat_3_i2: "Formula.sat \<sigma> V v i (Formula.Neg (Formula.Until \<beta> I \<gamma>)) = 
                 Formula.sat \<sigma> V v i (release (Formula.Neg \<beta>) I (Formula.Neg \<gamma>))" by force

lemma sat_3_j1: "Formula.sat \<sigma> V v i (Formula.Neg (trigger \<beta> I \<gamma>)) = 
                 Formula.sat \<sigma> V v i (Formula.Since (Formula.Neg \<beta>) I (Formula.Neg \<gamma>))" by auto

lemma sat_3_j2: "Formula.sat \<sigma> V v i (Formula.Neg (release \<beta> I \<gamma>)) = 
                 Formula.sat \<sigma> V v i (Formula.Until (Formula.Neg \<beta>) I (Formula.Neg \<gamma>))" by auto


(*Reasoning about intervals including 0*)
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

(*Main lemma used multiple times*)
lemma nat_less_mem_of_init: "\<And>i j:: nat. k \<in> {i..j} \<and> k' \<in>{i..j} \<Longrightarrow> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<Longrightarrow>  mem (\<tau> \<sigma> k - \<tau> \<sigma> k') (init_int I)" 
proof -
  fix i j :: nat assume A:"k \<in> {i..j} \<and> k' \<in>{i..j}" "mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I"
  then have "(\<tau> \<sigma> k - \<tau> \<sigma> k') \<le> (\<tau> \<sigma> j - \<tau> \<sigma> i)" using nat_less_than_range by auto
  then show " mem (\<tau> \<sigma> k - \<tau> \<sigma> k') (init_int I)" using A(2) mem_of_init by blast
qed


(*Equivalences*)

(*excl_zero I assumption needed to ensure alpha is satisfiable in some range*)
lemma equiv_1: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Until \<alpha> I \<beta>) = Formula.sat \<sigma> V v i (Formula.Until \<alpha> I (Formula.And (diamond_b I \<alpha>) \<beta>))" by fastforce

lemma equiv_2: "Formula.sat \<sigma> V v i (Formula.Until \<alpha> I \<beta>) = Formula.sat \<sigma> V v i (Formula.Until (Formula.And \<alpha> (diamond_w (init_int I) \<beta>) ) I \<beta>)" 
(is "?L = ?R")
proof(rule iffI)
  assume ass:?L
  then obtain j where j: "j\<ge>i" "mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I" "Formula.sat \<sigma> V v j \<beta>" "(\<forall>k\<in>{i..<j}. Formula.sat \<sigma> V v k \<alpha>)" by auto
  then have "\<forall>k\<in>{i..<j}.j\<ge>k " by auto
  moreover have "\<forall>k\<in>{i..<j}. mem (\<tau> \<sigma> j - \<tau> \<sigma> k) (init_int I)" using nat_less_mem_of_init[OF _ j(2)] by auto
  moreover have "\<forall>k\<in>{i..<j}. Formula.sat \<sigma> V v j \<beta>" using j(3) by auto
  ultimately have "\<forall>k\<in>{i..<j}. (\<exists>j\<ge>k. mem (\<tau> \<sigma> j - \<tau> \<sigma> k) (init_int I) \<and> Formula.sat \<sigma> V v j \<beta>)" by fast
  then show ?R using j by auto
qed auto

lemma equiv_3: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Since \<alpha> I \<beta>) = Formula.sat \<sigma> V v i (Formula.Since \<alpha> I (Formula.And (diamond_w I \<alpha>) \<beta>))" by fastforce

lemma equiv_4: " Formula.sat \<sigma> V v i (Formula.Since \<alpha> I \<beta>)  = Formula.sat \<sigma> V v i (Formula.Since (Formula.And \<alpha> (diamond_b (init_int I) \<beta>) ) I \<beta>)" 
(is "?L = ?R")
proof(rule iffI)
  assume ass:?L
  then obtain j where j: "j\<le>i" "mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I" "Formula.sat \<sigma> V v j \<beta>" "(\<forall>k\<in>{j<..i}. Formula.sat \<sigma> V v k \<alpha>)" by auto
  then have "\<forall>k\<in>{j<..i}.j\<le>k " by auto
  moreover have "\<forall>k\<in>{j<..i}. mem (\<tau> \<sigma> k - \<tau> \<sigma> j) (init_int I)" using nat_less_mem_of_init[OF _ j(2)] by auto
  moreover have "\<forall>k\<in>{j<..i}. Formula.sat \<sigma> V v j \<beta>" using j(3) by auto
  ultimately have "\<forall>k\<in>{j<..i}. (\<exists>j\<le>k. mem (\<tau> \<sigma> k - \<tau> \<sigma> j) (init_int I) \<and> Formula.sat \<sigma> V v j \<beta>)" by fast
  then show ?R using j by auto
qed auto
(*rules 5-8 is covered by next sections rewrite rules 10-13*)


lemma   sat_rewrite_1:
  "Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Or \<beta> \<gamma>)) =
   Formula.sat \<sigma> V v i (Formula.Or (Formula.And \<alpha> \<beta>) (Formula.And \<alpha> \<gamma>))"
  by auto

lemma sat_rewrite_4: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Exists \<beta>)) = 
                    Formula.sat \<sigma> V v i (Formula.Exists (Formula.And (shift \<alpha>) \<beta> ))"
  using sat_shift[of "[]"] by auto

lemma sat_rewrite_5: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Neg \<beta>))  =
                      Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Neg (Formula.And \<alpha> \<beta>)))"
  by auto

lemma sat_rewrite_6: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Since (Formula.And \<alpha> \<gamma>) I \<beta> ) =
                                      Formula.sat \<sigma> V v i (Formula.Since (Formula.And \<alpha> \<gamma>) I (Formula.And (diamond_w I \<alpha>) \<beta>))" by fastforce
  
lemma sat_rewrite_7: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Until (Formula.And \<alpha> \<gamma>) I \<beta> ) =
                                      Formula.sat \<sigma> V v i (Formula.Until (Formula.And \<alpha> \<gamma>) I (Formula.And (diamond_b I \<alpha>) \<beta>))" by fastforce


lemma sat_rewrite_12: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Since \<gamma> I \<beta>)) =
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Since \<gamma> I (Formula.And (diamond_w I \<alpha>)\<beta>)))" by auto

lemma sat_rewrite_13: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Until \<gamma> I \<beta>)) =
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Until \<gamma> I (Formula.And (diamond_b I \<alpha>)\<beta>)))" by auto


(*Duplications *)
(*lemma sat_rewrite_14: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.And \<alpha> (diamond_b I \<beta>)) = 
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (diamond_b I (Formula.And (diamond_w I \<alpha> ) \<beta>)))" by auto

lemma sat_rewrite_15: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.And \<alpha> (diamond_w I \<beta>)) = 
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (diamond_w I (Formula.And (diamond_b I \<alpha> ) \<beta>)))" by auto

lemma sat_rewrite_16: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.And \<alpha> (square_b I \<beta>)) = 
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (square_b I (Formula.And (diamond_w I \<alpha> ) \<beta>)))" by auto

lemma sat_rewrite_17: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.And \<alpha> (square_w I \<beta>)) = 
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (square_w I (Formula.And (diamond_b I \<alpha> ) \<beta>)))" by auto*)

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

(*Non-trivial rewrites gathered together*)

lemma sat_rewrite_2: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (release \<beta> I \<gamma>)) =
                                      Formula.sat \<sigma> V v i (Formula.And \<alpha> (release (Formula.And \<beta> (diamond_b (init_int I) \<alpha>)) I (Formula.And \<gamma> (diamond_b I \<alpha>))))" 
(is "?L = ?R" )
proof(rule iffI)
  assume ass: "?L"
  then have split_A: "Formula.sat \<sigma> V v i \<alpha>" 
                   "(\<And>j. j\<ge>i \<Longrightarrow> \<not> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<or> Formula.sat \<sigma> V v j \<gamma> \<or> (\<exists>k\<in>{i..<j}. Formula.sat \<sigma> V v k \<beta>))"
    by auto

  then have "(\<And>j. j\<ge>i \<Longrightarrow> \<not> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<or>
               (Formula.sat \<sigma> V v j \<gamma> \<and> (\<exists>ja\<le>j. mem (\<tau> \<sigma> j - \<tau> \<sigma> ja) I)) \<or>
              (\<exists>k\<in>{i..<j}.
                  (Formula.sat \<sigma> V v k \<beta> \<and> (\<exists>j\<le>k. mem (\<tau> \<sigma> k - \<tau> \<sigma> j) (init_int I) \<and> Formula.sat \<sigma> V v j \<alpha> ))))" 
  proof -
  fix j assume le:"j\<ge>i" 
  then have " \<not> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<or> Formula.sat \<sigma> V v j \<gamma> \<or> (\<exists>k\<in>{i..<j}. Formula.sat \<sigma> V v k \<beta>)" using ass by auto
  then consider (a) "\<not> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I" | 
                (b) "(Formula.sat \<sigma> V v j \<gamma>) \<and>  mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I" | 
                (c) "(\<exists>k\<in>{i..<j}. Formula.sat \<sigma> V v k \<beta>)"  "mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I" by auto
  then show "(\<not> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<or>
               (Formula.sat \<sigma> V v j \<gamma> \<and> (\<exists>ja\<le>j. mem (\<tau> \<sigma> j - \<tau> \<sigma> ja) I)) \<or>
              (\<exists>k\<in>{i..<j}.
                  (Formula.sat \<sigma> V v k \<beta> \<and> (\<exists>j\<le>k. mem (\<tau> \<sigma> k - \<tau> \<sigma> j) (init_int I) \<and> Formula.sat \<sigma> V v j \<alpha> ))))" 
  proof(cases)
    case a
    then show ?thesis by auto
  next
    case b
    then show ?thesis using le by auto
  next
    case c
    then show ?thesis using split_A(1) nat_less_mem_of_init[OF _ c(2)] by auto
  qed
qed
  then show ?R using split_A(1)  by auto
qed auto

lemma sat_rewrite_3: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (trigger \<beta> I \<gamma>)) =
                                      Formula.sat \<sigma> V v i (Formula.And \<alpha> (trigger (Formula.And \<beta> (diamond_w (init_int I) \<alpha>)) I (Formula.And \<gamma> (diamond_w I \<alpha>))))" 
(is "?L = ?R" )
proof(rule iffI)
  assume ass: "?L"
  then have split_A: "Formula.sat \<sigma> V v i \<alpha>" 
                     "(\<And>j. i\<ge>j \<Longrightarrow> \<not> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<or> Formula.sat \<sigma> V v j \<gamma> \<or> (\<exists>k\<in>{j<..i}. Formula.sat \<sigma> V v k \<beta>))" by auto
  then have "(\<And>j. i\<ge>j \<Longrightarrow> \<not>mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<or>
              (Formula.sat \<sigma> V v j \<gamma> \<and> (\<exists>ja\<ge>j. mem (\<tau> \<sigma> ja - \<tau> \<sigma> j) I)) \<or>
              (\<exists>k\<in>{j<..i}. (Formula.sat \<sigma> V v k \<beta> \<and> (\<exists>j\<ge>k. mem (\<tau> \<sigma> j - \<tau> \<sigma> k) (init_int I) \<and> Formula.sat \<sigma> V v j \<alpha>))))" 
  proof -
    fix j assume le:"i\<ge>j" 
    then have " \<not> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<or> Formula.sat \<sigma> V v j \<gamma> \<or> (\<exists>k\<in>{j<..i}. Formula.sat \<sigma> V v k \<beta>)" using ass by auto
    then consider (a) "\<not> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I " |
                  (b) "Formula.sat \<sigma> V v j \<gamma> \<and> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I" | 
                  (c) "(\<exists>k\<in>{j<..i}. Formula.sat \<sigma> V v k \<beta>)" "mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I" by auto
    then show "\<not>mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<or>
              (Formula.sat \<sigma> V v j \<gamma> \<and> (\<exists>ja\<ge>j. mem (\<tau> \<sigma> ja - \<tau> \<sigma> j) I)) \<or>
              (\<exists>k\<in>{j<..i}. (Formula.sat \<sigma> V v k \<beta> \<and> (\<exists>j\<ge>k. mem (\<tau> \<sigma> j - \<tau> \<sigma> k) (init_int I) \<and> Formula.sat \<sigma> V v j \<alpha>)))" 
  proof(cases)
    case a
    then show ?thesis by blast
  next
    case b
    then show ?thesis using le by auto
  next
    case c
    then show ?thesis using split_A(1) nat_less_mem_of_init[OF _ c(2)] by auto
  qed
qed
then show ?R using split_A(1) by auto
qed auto


lemma sat_rewrite_8: "Formula.sat \<sigma> V v i (Formula.Since \<beta> I (Formula.And \<alpha> \<gamma>) ) =
                      Formula.sat \<sigma> V v i (Formula.Since (Formula.And (diamond_b (init_int I) \<alpha>) \<beta>) I (Formula.And \<alpha> \<gamma>))" 
(is "?L = ?R")
proof(rule iffI)
  assume L:?L
  show ?R using iffD1[OF equiv_4 L] by fastforce 
qed auto

lemma sat_rewrite_9: "Formula.sat \<sigma> V v i (Formula.Until \<beta> I (Formula.And \<alpha> \<gamma>)) =
                                      Formula.sat \<sigma> V v i (Formula.Until (Formula.And (diamond_w (init_int I) \<alpha>) \<beta>) I (Formula.And \<alpha> \<gamma>))" 
(is "?L = ?R")
proof(rule iffI)
  assume L:?L
  show ?R using iffD1[OF equiv_2 L] by fastforce 
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


lemma sat_rewrite_11: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Until \<beta> I \<gamma>)) =
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Until (Formula.And (diamond_b (init_int I) \<alpha>) \<beta>) I \<gamma>))" 
(is "?L = ?R")
proof(rule iffI)
  assume L:?L
  then obtain j where j: "j\<ge>i" "mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I" "Formula.sat \<sigma> V v j \<gamma>" "(\<forall>k\<in>{i..<j}.  Formula.sat \<sigma> V v i \<alpha> \<and> Formula.sat \<sigma> V v k \<beta>)" by auto
  then have "\<forall>k\<in>{i..<j}. mem (\<tau> \<sigma> k - \<tau> \<sigma> i) (init_int I)" using nat_less_mem_of_init[OF _ j(2)] by fastforce
  then show ?R using L j by fastforce
qed auto

(*
datatype "constant" = SINCE | UNTIL \<I> | NEG

datatype 'c "term" = App 'c "'c term list"

datatype ('c, 'x) "pattern" = Var 'x | PApp 'c "('c, 'x) pattern list"

fun matches where
  "matches [] [] \<sigma> = Some \<sigma>"
| "matches (Var x # ps) (t # ts) \<sigma> =
     (case \<sigma> x of
       None \<Rightarrow> matches ps ts ((\<sigma>(x \<mapsto> t)))
     | Some u \<Rightarrow> if t = u then matches ps ts \<sigma> else None)"
| "matches (PApp c ps # ps') (App d ts # ts') \<sigma> = (if c = d \<and> length ps = length ts then 
     matches (ps @ ps') (ts @ ts') \<sigma> else None)"
| "matches _ _ \<sigma> = None"

fun instantiate where
  "instantiate \<sigma> (Var x) = the (\<sigma> x)"
| "instantiate \<sigma> (PApp c ps) = App c (map (instantiate \<sigma>) ps)"

fun rewrite1 :: "(('c, 'x) pattern \<times> ('c, 'x) pattern) list \<Rightarrow> 'c term \<Rightarrow> 'c term" where
  "rewrite1 [] t = t"
| "rewrite1 ((p, u) # rs) t =
   (case matches [p] [t] Map.empty of
     Some \<sigma> \<Rightarrow> instantiate \<sigma> u
   | None \<Rightarrow> rewrite1 rs t)"

fun rewrite :: "(('c, 'x) pattern \<times> ('c, 'x) pattern) list \<Rightarrow> 'c term \<Rightarrow> 'c term" where
  "rewrite rs (App c ts) = rewrite1 rs (App c (map (rewrite rs) ts))"

fun embed where
  "embed (Formula.Until \<phi> I \<psi>) = App (UNTIL I) [embed \<phi>, embed \<psi>]"
*)


(*lemma eval_cong[cong]: "\<And>P::(Formula.trm \<Rightarrow> Formula.trm). (Formula.eval_trm v t = Formula.eval_trm v t') \<Longrightarrow> Formula.eval_trm v (P t) =  Formula.eval_trm v (P t')" sorry
lemma sat_cong[cong]: "(Formula.sat \<sigma> V v i \<alpha> = Formula.sat \<sigma> V v i \<beta>) \<Longrightarrow> Formula.sat \<sigma> V v i (P \<alpha>) = Formula.sat \<sigma> V v i (P \<beta>)" sorry*)

(*future lemma, set of range restricted variables is same or less after rewrite*)

(*
fun rewrite1 :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewrite1 (Formula.And \<alpha> (Formula.Or \<beta> \<gamma>)) = (let \<alpha>' = rewrite1 \<alpha>;
                                                    \<beta>' = rewrite1 \<beta>;
                                                    \<gamma>' = rewrite1 \<gamma>
                                                 in if prop_cond \<alpha>' \<beta>' 
                                                    then Formula.Or (Formula.And \<alpha>' \<beta>') (Formula.And \<alpha>' \<gamma>')
                                                    else Formula.And \<alpha>' (Formula.Or \<beta>' \<gamma>'))"  (*Maybe also a disjunction with prop_cond a' g'*)
| "rewrite1 f = f"

thm sat.simps

lemma rewrite1_sat: "Formula.sat \<sigma> V v i (rewrite1 \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> rule:rewrite1.induct)
  case (1 \<alpha> \<beta> \<gamma>)
  then show ?case  by (simp del:sat.simps add:Let_def sat_rewrite_1;auto)
qed auto


fun rewrite2:: "Formula.formula \<Rightarrow> Formula.formula" where
"rewrite2 (Formula.And \<alpha> (release \<beta> I \<gamma>)) =(let \<alpha>' = rewrite2 \<alpha>;
                                                 \<beta>' = rewrite2 \<beta>;
                                                 \<gamma>' = rewrite2 \<gamma>
                                                in if prop_cond \<alpha>' \<beta>' 
                                                 then Formula.And \<alpha>' (release (Formula.And \<beta>' (diamond_b (init_int I) \<alpha>')) I (Formula.And \<gamma>' (diamond_b I \<alpha>'))) 
                                                 else Formula.And \<alpha>' (release \<beta>' I \<gamma>'))"
| "rewrite2 f = f"

thm conj_cong
thm sat.simps(15)
lemma rewrite2_sat: "Formula.sat \<sigma> V v i (rewrite2 \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> arbitrary: i rule:rewrite2.induct)
  case (1 \<alpha> \<beta> I \<gamma>)
  then show ?case by (simp only:rewrite2.simps Let_def sat_rewrite_2[symmetric] split:if_splits;simp)
qed auto

fun rewrite3 :: "Formula.formula \<Rightarrow> Formula.formula" where
 "rewrite3 (Formula.And \<alpha> (trigger \<beta> I \<gamma>)) =(let \<alpha>' = rewrite3 \<alpha>;
                                                 \<beta>' = rewrite3 \<beta>;
                                                 \<gamma>' = rewrite3 \<gamma>
                                                in if prop_cond \<alpha>' \<beta>'  
                                                 then Formula.And \<alpha>' (trigger (Formula.And \<beta>' (diamond_w (init_int I) \<alpha>')) I (Formula.And \<gamma>' (diamond_w I \<alpha>')))  
                                                 else Formula.And \<alpha>' (trigger \<beta>' I \<gamma>'))"
| "rewrite3 f = f"

lemma rewrite3_sat: "Formula.sat \<sigma> V v i (rewrite3 \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> arbitrary: i rule:rewrite3.induct)
  case (1 \<alpha> \<beta> I \<gamma>)
  then show ?case by (simp only:rewrite3.simps Let_def sat_rewrite_3[symmetric] split:if_splits;simp)
qed auto

fun rewrite4 :: "Formula.formula \<Rightarrow> Formula.formula" where
 "rewrite4 (Formula.And \<alpha> (Formula.Exists \<beta>)) =(let \<alpha>' = rewrite4 \<alpha>;
                                                    \<beta>' = rewrite4 \<beta>
                                                in if prop_cond \<alpha>' \<beta>'  
                                                 then Formula.Exists (Formula.And (shift \<alpha>') \<beta>')  
                                                 else Formula.And \<alpha>' (Formula.Exists \<beta>'))"
| "rewrite4 f = f"

thm sat.simps(10)
lemma rewrite4_sat: "Formula.sat \<sigma> V v i (rewrite4 f) = Formula.sat \<sigma> V v i f" 
proof(induction f arbitrary: i v rule:rewrite4.induct)
  case (1 \<alpha> \<beta>)  
  then show ?case by(simp only: rewrite4.simps shiftI.simps sat_rewrite_4[symmetric] Let_def split:if_splits;simp) 
qed auto

fun rewrite5 :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewrite5 (Formula.And \<alpha> (Formula.Neg \<beta>)) =(let \<alpha>' = rewrite5 \<alpha>;
                                                 \<beta>' = rewrite5 \<beta>
                                                in if prop_cond \<alpha>' \<beta>'  
                                                 then Formula.And \<alpha>' (Formula.Neg (Formula.And \<alpha>' \<beta>'))  
                                                 else Formula.And \<alpha>' (Formula.Neg \<beta>'))"
| "rewrite5 f = f"


lemma rewrite5_sat: "Formula.sat \<sigma> V v i (rewrite5 \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> rule:rewrite5.induct)
  case (1 \<alpha> \<beta>)
  then show ?case by (simp add: Let_def sat_rewrite_5;auto)
qed auto

fun rewrite6 :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewrite6 (Formula.Since (Formula.And \<alpha> \<gamma>) I \<beta> ) =(let \<alpha>' = rewrite6 \<alpha>;
                                                        \<beta>' = rewrite6 \<beta>;
                                                        \<gamma>' = rewrite6 \<gamma>
                                                in if prop_cond \<alpha>' \<beta>' \<and> excl_zero I 
                                                 then Formula.Since (Formula.And \<alpha>' \<gamma>') I (Formula.And (diamond_w I \<alpha>') \<beta>')  
                                                 else Formula.Since (Formula.And \<alpha>' \<gamma>') I \<beta>' )"
| "rewrite6 f = f"

lemma rewrite6_sat: "Formula.sat \<sigma> V v i (rewrite6 \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> arbitrary: i rule:rewrite6.induct)
  case (1 \<alpha> \<gamma> I \<beta>)
  then show ?case  
  proof(cases "excl_zero I")
    thm sat_rewrite_6[symmetric]
    case True
    then show ?thesis using 1 by (simp only:rewrite6.simps Let_def sat_rewrite_6[OF True,symmetric] split:if_splits;simp)
  next
    case False
    then show ?thesis using 1 by simp
  qed
qed auto

fun rewrite7 :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewrite7 (Formula.Until (Formula.And \<alpha> \<gamma>) I \<beta> ) =(let \<alpha>' = rewrite7 \<alpha>;
                                                        \<beta>' = rewrite7 \<beta>;
                                                        \<gamma>' = rewrite7 \<gamma>
                                                in if prop_cond \<alpha>' \<beta>' \<and> excl_zero I 
                                                 then Formula.Until (Formula.And \<alpha>' \<gamma>') I (Formula.And (diamond_b I \<alpha>') \<beta>')
                                                 else Formula.Until (Formula.And \<alpha>' \<gamma>') I \<beta>')"
| "rewrite7 f = f"

lemma rewrite7_sat: "Formula.sat \<sigma> V v i (rewrite7 \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> arbitrary: i rule:rewrite7.induct)
  case (1 \<alpha> \<gamma> I \<beta>)
  then show ?case
  proof(cases "excl_zero I")
    case True
    then show ?thesis using 1 by (simp only:rewrite7.simps Let_def sat_rewrite_7[OF True,symmetric] split:if_splits;simp)
  next
    case False
    then show ?thesis using 1 by simp
  qed
qed auto

fun rewrite8 :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewrite8 (Formula.Since \<beta> I (Formula.And \<alpha> \<gamma>)) =(let \<alpha>' = rewrite8 \<alpha>;
                                                        \<beta>' = rewrite8 \<beta>;
                                                        \<gamma>' = rewrite8 \<gamma>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.Since (Formula.And (diamond_b (init_int I) \<alpha>') \<beta>') I (Formula.And \<alpha>' \<gamma>')
                                                 else Formula.Since \<beta>' I (Formula.And \<alpha>' \<gamma>') )"

| "rewrite8 f = f"

lemma rewrite8_sat: "Formula.sat \<sigma> V v i (rewrite8 \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> arbitrary: i rule:rewrite8.induct)
  case (1 \<beta> I \<alpha> \<gamma>)
  then show ?case by (simp only:rewrite8.simps Let_def sat_rewrite_8[symmetric] split:if_splits;simp)
qed auto

fun rewrite9 :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewrite9 (Formula.Until \<beta> I (Formula.And \<alpha> \<gamma>)) =(let \<alpha>' = rewrite9 \<alpha>;
                                                        \<beta>' = rewrite9 \<beta>;
                                                        \<gamma>' = rewrite9 \<gamma>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.Until (Formula.And (diamond_w (init_int I) \<alpha>') \<beta>') I (Formula.And \<alpha>' \<gamma>')
                                                 else Formula.Until \<beta>' I (Formula.And \<alpha>' \<gamma>') )"

| "rewrite9 f = f"

lemma rewrite9_sat: "Formula.sat \<sigma> V v i (rewrite9 \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> arbitrary: i rule:rewrite9.induct)
  case (1 \<beta> I \<alpha> \<gamma>)
  then show ?case by (simp only:rewrite9.simps Let_def sat_rewrite_9[symmetric] split:if_splits;simp)
qed auto


fun rewrite10 :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewrite10 (Formula.And \<alpha> (Formula.Since \<beta> I \<gamma>)) =(let \<alpha>' = rewrite10 \<alpha>;
                                                        \<beta>' = rewrite10 \<beta>;
                                                        \<gamma>' = rewrite10 \<gamma>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (Formula.Since (Formula.And (diamond_w (init_int I) \<alpha>') \<beta>') I \<gamma>')
                                                 else Formula.And \<alpha>' (Formula.Since \<beta>' I \<gamma>'))"

| "rewrite10 f = f"

lemma rewrite10_sat: "Formula.sat \<sigma> V v i (rewrite10 \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> arbitrary: i rule:rewrite10.induct)
  case (1 \<alpha> \<beta> I \<gamma>)
  then show ?case by (simp only:rewrite10.simps Let_def sat_rewrite_10[symmetric] split:if_splits;simp)
qed auto

fun rewrite11 :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewrite11 (Formula.And \<alpha> (Formula.Until \<beta> I \<gamma>)) =(let \<alpha>' = rewrite11 \<alpha>;
                                                        \<beta>' = rewrite11 \<beta>;
                                                        \<gamma>' = rewrite11 \<gamma>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (Formula.Until (Formula.And (diamond_b (init_int I) \<alpha>') \<beta>') I \<gamma>')
                                                 else Formula.And \<alpha>' (Formula.Until \<beta>' I \<gamma>'))"

| "rewrite11 f = f"

lemma rewrite11_sat: "Formula.sat \<sigma> V v i (rewrite11 \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> arbitrary: i rule:rewrite11.induct)
  case (1 \<beta> I \<alpha> \<gamma>)
  then show ?case by (simp only:rewrite11.simps Let_def sat_rewrite_11[symmetric] split:if_splits;simp)
qed auto

fun rewrite12 :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewrite12 (Formula.And \<alpha> (Formula.Since \<gamma> I \<beta>)) =(let \<alpha>' = rewrite12 \<alpha>;
                                                        \<beta>' = rewrite12 \<beta>;
                                                        \<gamma>' = rewrite12 \<gamma>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (Formula.Since \<gamma>' I (Formula.And (diamond_w I \<alpha>') \<beta>'))
                                                 else Formula.And \<alpha>' (Formula.Since \<gamma>' I \<beta>'))"

| "rewrite12 f = f"

lemma rewrite12_sat: "Formula.sat \<sigma> V v i (rewrite12 \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> arbitrary: i rule:rewrite12.induct)
  case (1)
  then show ?case by (simp only:rewrite12.simps Let_def sat_rewrite_12[symmetric] split:if_splits;simp)
qed auto

fun rewrite13 :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewrite13 (Formula.And \<alpha> (Formula.Until \<gamma> I \<beta>)) =(let \<alpha>' = rewrite13 \<alpha>;
                                                        \<beta>' = rewrite13 \<beta>;
                                                        \<gamma>' = rewrite13 \<gamma>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (Formula.Until \<gamma>' I (Formula.And (diamond_b I \<alpha>') \<beta>'))
                                                 else Formula.And \<alpha>' (Formula.Until \<gamma>' I \<beta>'))"

| "rewrite13 f = f"

lemma rewrite13_sat: "Formula.sat \<sigma> V v i (rewrite13 \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> arbitrary: i rule:rewrite13.induct)
  case (1)
  then show ?case by (simp only:rewrite13.simps Let_def sat_rewrite_13[symmetric] split:if_splits;simp)
qed auto

(*Introduced abbreviations of TT and FF to allow diamond_b abbreviation in pattern*)
function(sequential) rewrite18 :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewrite18 (Formula.And \<alpha> (diamond_b I \<beta>)) =(let \<alpha>' = rewrite18 \<alpha>;
                                     \<beta>' = rewrite18 \<beta>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (diamond_b I (Formula.And (diamond_w I \<alpha>') \<beta>'))
                                                 else Formula.And \<alpha>' (diamond_b I \<beta>'))"

| "rewrite18 f = f"
  by (pat_completeness) auto
termination by lexicographic_order

lemma rewrite18_sat: "Formula.sat \<sigma> V v i (rewrite18 \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> arbitrary: i rule:rewrite18.induct)
  case (1)
  then show ?case by (simp only:rewrite18.simps Let_def sat_rewrite_18[symmetric] split:if_splits;simp)
qed auto

function(sequential) rewrite19 :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewrite19 (Formula.And \<alpha> (diamond_w I \<beta>)) =(let \<alpha>' = rewrite19 \<alpha>;
                                                   \<beta>' = rewrite19 \<beta>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (diamond_w I (Formula.And (diamond_b I \<alpha>') \<beta>'))
                                                 else Formula.And \<alpha>' (diamond_w I \<beta>'))"

| "rewrite19 f = f"
by (pat_completeness) auto

termination by lexicographic_order

lemma rewrite19_sat: "Formula.sat \<sigma> V v i (rewrite19 \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> arbitrary: i rule:rewrite19.induct)
  case (1)
  then show ?case by (simp only:rewrite19.simps Let_def sat_rewrite_19[symmetric] split:if_splits;simp)
qed auto

function(sequential) rewrite20 :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewrite20 (Formula.And \<alpha> (square_b I \<beta>)) =(let \<alpha>' = rewrite20 \<alpha>;
                                                   \<beta>' = rewrite20 \<beta>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (square_b I (Formula.And (diamond_w I \<alpha>' ) \<beta>'))
                                                 else Formula.And \<alpha>' (square_b I \<beta>'))"

| "rewrite20 f = f"
 by (pat_completeness) auto
termination by lexicographic_order

lemma rewrite20_sat: "Formula.sat \<sigma> V v i (rewrite20 \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> arbitrary: i rule:rewrite20.induct)
  case (1)
  then show ?case by (simp only:rewrite20.simps Let_def sat_rewrite_20[symmetric] split:if_splits;simp)
qed auto


function(sequential) rewrite21 :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewrite21 (Formula.And \<alpha> (square_w I \<beta>)) =(let \<alpha>' = rewrite21 \<alpha>;
                                                   \<beta>' = rewrite21 \<beta>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (square_w I (Formula.And (diamond_b I \<alpha>') \<beta>'))
                                                 else Formula.And \<alpha>' (square_w I \<beta>'))"

| "rewrite21 f = f"
 by (pat_completeness) auto
termination by lexicographic_order

lemma rewrite21_sat: "Formula.sat \<sigma> V v i (rewrite21 \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> arbitrary: i rule:rewrite21.induct)
  case (1)
  then show ?case by (simp only:rewrite21.simps Let_def sat_rewrite_21[symmetric] split:if_splits;simp)
qed auto


function(sequential) rewrite22 :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewrite22 (Formula.And \<alpha> (Formula.Prev I \<beta>)) =(let \<alpha>' = rewrite22 \<alpha>;
                                                      \<beta>' = rewrite22 \<beta>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (Formula.Prev I (Formula.And (Formula.Next I \<alpha>') \<beta>'))
                                                 else Formula.And \<alpha>' (Formula.Prev I \<beta>'))"

| "rewrite22 f = f"
 by (pat_completeness) auto

termination by lexicographic_order

lemma rewrite22_sat: "Formula.sat \<sigma> V v i (rewrite22 \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> arbitrary: i rule:rewrite22.induct)
  case (1)
  then show ?case by (simp only:rewrite22.simps Let_def sat_rewrite_22[symmetric] split:if_splits ;simp split:nat.splits)
qed auto

function(sequential) rewrite23 :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewrite23 (Formula.And \<alpha> (Formula.Next I \<beta>)) =(let \<alpha>' = rewrite23 \<alpha>;
                                                   \<beta>' = rewrite23 \<beta>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (Formula.Next I (Formula.And (Formula.Prev I \<alpha>') \<beta>'))
                                                 else Formula.And \<alpha>' (Formula.Next I \<beta>'))"

| "rewrite23 f = f"
 by (pat_completeness) auto
termination by lexicographic_order

lemma rewrite23_sat: "Formula.sat \<sigma> V v i (rewrite23 \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> arbitrary: i rule:rewrite23.induct)
  case (1)
  then show ?case by (simp only:rewrite23.simps Let_def sat_rewrite_23[symmetric] split:if_splits;simp)
qed auto
*)

term "case xs of [] \<Rightarrow> 0 | x # xs \<Rightarrow> 1"
term "case_list 0 (\<lambda>x xs. 1) xs"

fun rewrite :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewrite f = (case f of
     Formula.And \<alpha> (Formula.Or \<beta> \<gamma>) \<Rightarrow>
       (if prop_cond \<alpha> \<beta>
       then Formula.Or (rewrite (Formula.And \<alpha> \<beta>)) (rewrite (Formula.And \<alpha> \<gamma>))
       else let \<alpha>' = rewrite \<alpha>; \<beta>' = rewrite \<beta>;  \<gamma>' = rewrite \<gamma> in Formula.And \<alpha>' (Formula.Or \<beta>' \<gamma>'))
   | _ \<Rightarrow> f)"

lemma rewrite_sat: "Formula.sat \<sigma> V v i (rewrite \<alpha>) = Formula.sat \<sigma> V v i \<alpha>"
  apply (induct \<alpha> rule: rewrite.induct)
  apply (subst rewrite.simps)
(*
  apply (simp only: simp_thms formula.inject split_paired_All split formula.splits if_splits)
  find_theorems "(_ \<and> _ \<longleftrightarrow> _) = _"
  apply (intro allI impI conjI)
*)
(*
  using [[simp_trace_new mode=full]]
  using [[simproc del: let_simp]]
*)
  apply (simp del: rewrite.simps sat.simps add: sat_rewrite_1 
    split: formula.splits if_splits)
  apply (intro allI impI conjI)
  apply simp_all
  done


function(sequential) rewrite :: "Formula.formula \<Rightarrow> Formula.formula" where
(*1*)  "rewrite (Formula.And \<alpha> (Formula.Or \<beta> \<gamma>)) = (let \<alpha>' = rewrite \<alpha>;
                                                    \<beta>' = rewrite \<beta>;
                                                    \<gamma>' = rewrite \<gamma>
                                                 in if prop_cond \<alpha>' \<beta>' 
                                                    then Formula.Or (Formula.And \<alpha>' \<beta>') (Formula.And \<alpha>' \<gamma>')
                                                    else Formula.And \<alpha>' (Formula.Or \<beta>' \<gamma>'))"  (*Maybe also a disjunction with prop_cond a' g'*)  
(*4*)| "rewrite (Formula.And \<alpha> (Formula.Exists \<beta>)) =(let \<alpha>' = rewrite \<alpha>;
                                                    \<beta>' = rewrite \<beta>
                                                in if prop_cond \<alpha>' \<beta>'  
                                                 then Formula.Exists (Formula.And (shift \<alpha>') \<beta>')  
                                                 else Formula.And \<alpha>' (Formula.Exists \<beta>'))"
(*(*21*)| "rewrite (Formula.And \<alpha> (square_w I \<beta>)) =(let \<alpha>' = rewrite \<alpha>;
                                                   \<beta>' = rewrite \<beta>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (square_w I (Formula.And (diamond_b I \<alpha>') \<beta>'))
                                                 else Formula.And \<alpha>' (square_w I \<beta>'))"
(*2*)| "rewrite (Formula.And \<alpha> (release \<beta> I \<gamma>)) =(let \<alpha>' = rewrite \<alpha>;
                                                 \<beta>' = rewrite \<beta>;
                                                 \<gamma>' = rewrite \<gamma>
                                                in if prop_cond \<alpha>' \<beta>' 
                                                 then Formula.And \<alpha>' (release (Formula.And \<beta>' (diamond_b (init_int I) \<alpha>')) I (Formula.And \<gamma>' (diamond_b I \<alpha>'))) 
                                                 else Formula.And \<alpha>' (release \<beta>' I \<gamma>'))"
(*20*)| "rewrite (Formula.And \<alpha> (square_b I \<beta>)) =(let \<alpha>' = rewrite \<alpha>;
                                                   \<beta>' = rewrite \<beta>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (square_b I (Formula.And (diamond_w I \<alpha>' ) \<beta>'))
                                                 else Formula.And \<alpha>' (square_b I \<beta>'))"
(*3*)| "rewrite (Formula.And \<alpha> (trigger \<beta> I \<gamma>)) =(let \<alpha>' = rewrite \<alpha>;
                                                 \<beta>' = rewrite \<beta>;
                                                 \<gamma>' = rewrite \<gamma>
                                                in if prop_cond \<alpha>' \<beta>'  
                                                 then Formula.And \<alpha>' (trigger (Formula.And \<beta>' (diamond_w (init_int I) \<alpha>')) I (Formula.And \<gamma>' (diamond_w I \<alpha>')))  
                                                 else Formula.And \<alpha>' (trigger \<beta>' I \<gamma>'))"*)
(*5*)| "rewrite (Formula.And \<alpha> (Formula.Neg \<beta>)) =(let \<alpha>' = rewrite \<alpha> 
                                                  in (case \<beta> of
                                                    Formula.Until (Formula.Neg \<beta>'') I (Formula.Neg \<gamma>'') \<Rightarrow>
                                                           (let \<beta>' = rewrite \<beta>'';
                                                                \<gamma>' = rewrite \<gamma>''
                                                            in if prop_cond \<alpha>' \<beta>' 
                                                                  then Formula.And \<alpha>' (release (Formula.And \<beta>' (diamond_b (init_int I) \<alpha>')) 
                                                                                                I 
                                                                                               (Formula.And \<gamma>' (diamond_b I \<alpha>'))) 
                                                                  else Formula.And \<alpha>' (release \<beta>' I \<gamma>'))
                                                    | _ \<Rightarrow> let \<beta>' = rewrite \<beta>
                                                           in if prop_cond \<alpha>' \<beta>'  
                                                                then Formula.And \<alpha>' (Formula.Neg (Formula.And \<alpha>' \<beta>'))  
                                                                else Formula.And \<alpha>' (Formula.Neg \<beta>')))"


(*6*)| "rewrite (Formula.Since (Formula.And \<alpha> \<gamma>) I \<beta> ) =(let \<alpha>' = rewrite \<alpha>;
                                                        \<beta>' = rewrite \<beta>;
                                                        \<gamma>' = rewrite \<gamma>
                                                in if prop_cond \<alpha>' \<beta>' \<and> excl_zero I 
                                                 then Formula.Since (Formula.And \<alpha>' \<gamma>') I (Formula.And (diamond_w I \<alpha>') \<beta>')  
                                                 else Formula.Since (Formula.And \<alpha>' \<gamma>') I \<beta>' )"
(*7*)| "rewrite (Formula.Until (Formula.And \<alpha> \<gamma>) I \<beta> ) =(let \<alpha>' = rewrite \<alpha>;
                                                        \<beta>' = rewrite \<beta>;
                                                        \<gamma>' = rewrite \<gamma>
                                                in if prop_cond \<alpha>' \<beta>' \<and> excl_zero I 
                                                 then Formula.Until (Formula.And \<alpha>' \<gamma>') I (Formula.And (diamond_b I \<alpha>') \<beta>')
                                                 else Formula.Until (Formula.And \<alpha>' \<gamma>') I \<beta>')"
(*8*)(*| "rewrite (Formula.Since \<beta> I (Formula.And \<alpha> \<gamma>)) =(let \<alpha>' = rewrite \<alpha>;
                                                        \<beta>' = rewrite \<beta>;
                                                        \<gamma>' = rewrite \<gamma>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.Since (Formula.And (diamond_b (init_int I) \<alpha>') \<beta>') I (Formula.And \<alpha>' \<gamma>')
                                                 else Formula.Since \<beta>' I (Formula.And \<alpha>' \<gamma>') )"
(*9*)| "rewrite (Formula.Until \<beta> I (Formula.And \<alpha> \<gamma>)) =(let \<alpha>' = rewrite \<alpha>;
                                                        \<beta>' = rewrite \<beta>;
                                                        \<gamma>' = rewrite \<gamma>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.Until (Formula.And (diamond_w (init_int I) \<alpha>') \<beta>') I (Formula.And \<alpha>' \<gamma>')
                                                 else Formula.Until \<beta>' I (Formula.And \<alpha>' \<gamma>') )" *)
(*10*)| "rewrite (Formula.And \<alpha> (Formula.Since \<beta> I \<gamma>)) =(let \<alpha>' = rewrite \<alpha>;
                                                        \<beta>' = rewrite \<beta>;
                                                        \<gamma>' = rewrite \<gamma>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (Formula.Since (Formula.And (diamond_w (init_int I) \<alpha>') \<beta>') I \<gamma>')
                                                 else Formula.And \<alpha>' (Formula.Since \<beta>' I \<gamma>'))"
(*11*)| "rewrite (Formula.And \<alpha> (Formula.Until \<beta> I \<gamma>)) =(let \<alpha>' = rewrite \<alpha>;
                                                        \<beta>' = rewrite \<beta>;
                                                        \<gamma>' = rewrite \<gamma>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (Formula.Until (Formula.And (diamond_b (init_int I) \<alpha>') \<beta>') I \<gamma>')
                                                 else Formula.And \<alpha>' (Formula.Until \<beta>' I \<gamma>'))" 
(*12*)(*| "rewrite (Formula.And \<alpha> (Formula.Since \<gamma> I \<beta>)) =(let \<alpha>' = rewrite \<alpha>;
                                                        \<beta>' = rewrite \<beta>;
                                                        \<gamma>' = rewrite \<gamma>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (Formula.Since \<gamma>' I (Formula.And (diamond_w I \<alpha>') \<beta>'))
                                                 else Formula.And \<alpha>' (Formula.Since \<gamma>' I \<beta>'))"
(*13*)| "rewrite (Formula.And \<alpha> (Formula.Until \<gamma> I \<beta>)) =(let \<alpha>' = rewrite \<alpha>;
                                                        \<beta>' = rewrite \<beta>;
                                                        \<gamma>' = rewrite \<gamma>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (Formula.Until \<gamma>' I (Formula.And (diamond_b I \<alpha>') \<beta>'))
                                                 else Formula.And \<alpha>' (Formula.Until \<gamma>' I \<beta>'))"*)
(*18*)(*| "rewrite (Formula.And \<alpha> (diamond_b I \<beta>)) =(let \<alpha>' = rewrite \<alpha>;
                                     \<beta>' = rewrite \<beta>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (diamond_b I (Formula.And (diamond_w I \<alpha>') \<beta>'))
                                                 else Formula.And \<alpha>' (diamond_b I \<beta>'))"*)   (*INSERT AGAIN*)
(*19*)(*| "rewrite (Formula.And \<alpha> (diamond_w I \<beta>)) =(let \<alpha>' = rewrite \<alpha>;
                                                   \<beta>' = rewrite \<beta>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (diamond_w I (Formula.And (diamond_b I \<alpha>') \<beta>'))
                                                 else Formula.And \<alpha>' (diamond_w I \<beta>'))"  *) (*INSERT AGAIN*)

(*22*)| "rewrite (Formula.And \<alpha> (Formula.Prev I \<beta>)) =(let \<alpha>' = rewrite \<alpha>;
                                                      \<beta>' = rewrite \<beta>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (Formula.Prev I (Formula.And (Formula.Next I \<alpha>') \<beta>'))
                                                 else Formula.And \<alpha>' (Formula.Prev I \<beta>'))"
(*23*)| "rewrite (Formula.And \<alpha> (Formula.Next I \<beta>)) =(let \<alpha>' = rewrite \<alpha>;
                                                   \<beta>' = rewrite \<beta>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (Formula.Next I (Formula.And (Formula.Prev I \<alpha>') \<beta>'))
                                                 else Formula.And \<alpha>' (Formula.Next I \<beta>'))"
| "rewrite f = f "
  by pat_completeness auto
termination by lexicographic_order


(*fun_cases my_elim: "rewrite \<alpha>"*)

thm formula.splits

lemma rewrite_sat: "Formula.sat \<sigma> V v i (rewrite \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> arbitrary: v i rule:rewrite.induct)
  case (1 \<alpha> \<beta> \<gamma>) (*1*)
  then show ?case  by (simp del:sat.simps add:Let_def sat_rewrite_1;auto)
next
  case (2 \<alpha> \<beta>)  (*4*)
  then show ?case by(simp only: rewrite.simps shiftI.simps sat_rewrite_4[symmetric] Let_def split:if_splits;simp) 
next
(*
  case (3)
  then show ?case by (simp only:rewrite.simps Let_def sat_rewrite_21[symmetric] split:if_splits;simp)
next
  case (4 \<alpha> \<beta> I \<gamma>) (*2*)
  then show ?case by (simp only:rewrite.simps Let_def sat_rewrite_2[symmetric] split:if_splits;simp)
next
  case (5) (*20*)
  then show ?case by (simp only:rewrite.simps Let_def sat_rewrite_20[symmetric] split:if_splits;simp)
next
  case (6 \<alpha> \<beta> I \<gamma>)
  then show ?case by (simp only:rewrite.simps Let_def sat_rewrite_3[symmetric] split:if_splits;simp)
next
  case (7 \<alpha> \<beta>)
  then show ?case by (simp add: Let_def sat_rewrite_5;auto)
next
  case l:(8 \<alpha> \<gamma> I \<beta>) (*6*)
  then show ?case  
  proof(cases "excl_zero I")
    thm sat_rewrite_6[symmetric]
    case True
    then show ?thesis using l by (simp only:rewrite.simps Let_def sat_rewrite_6[OF True,symmetric] split:if_splits;simp)
  next
    case False
    then show ?thesis using l by simp
  qed
next
  case l:(9 \<alpha> \<gamma> I \<beta>) (*7*)
  then show ?case
  proof(cases "excl_zero I")
    case True
    then show ?thesis using l by (simp only:rewrite.simps Let_def sat_rewrite_7[OF True,symmetric] split:if_splits;simp)
  next
    case False
    then show ?thesis using l by simp
  qed
next
(*next
  case (8 \<beta> I \<alpha> \<gamma>)
  then show ?case by (simp only:rewrite8.simps Let_def sat_rewrite_8[symmetric] split:if_splits;simp)
next
  case (9 \<beta> I \<alpha> \<gamma>)
  then show ?case by (simp only:rewrite9.simps Let_def sat_rewrite_9[symmetric] split:if_splits;simp)*)
next
  case (10 \<alpha> \<beta> I \<gamma>) (*10*)
  then show ?case by (simp only:rewrite.simps Let_def sat_rewrite_10[symmetric] split:if_splits;simp)
next
  case (11 \<beta> I \<alpha> \<gamma>) (*11*)
  then show ?case by (simp only:rewrite.simps Let_def sat_rewrite_11[symmetric] split:if_splits;simp)
(*next
  case (12)
  then show ?case by (simp only:rewrite12.simps Let_def sat_rewrite_12[symmetric] split:if_splits;simp)
next
  case (13)
  then show ?case by (simp only:rewrite13.simps Let_def sat_rewrite_13[symmetric] split:if_splits;simp)
next
  case (18)
  then show ?case by (simp only:rewrite18.simps Let_def sat_rewrite_18[symmetric] split:if_splits;simp)
next
  case (19)
  then show ?case by (simp only:rewrite19.simps Let_def sat_rewrite_19[symmetric] split:if_splits;simp)
next
  case (20)
  then show ?case by (simp only:rewrite20.simps Let_def sat_rewrite_20[symmetric] split:if_splits;simp)
next
  case (21)
  then show ?case by (simp only:rewrite21.simps Let_def sat_rewrite_21[symmetric] split:if_splits;simp)*)
next
  case (12) (*22*)
  then show ?case by (simp only:rewrite.simps Let_def sat_rewrite_22[symmetric] split:if_splits ;simp split:nat.splits)
next
  case (13) (*23*)
  then show ?case by (simp only:rewrite.simps Let_def sat_rewrite_23[symmetric] split:if_splits;simp)
*)
qed auto



(*5*)| "rewrite (Formula.And \<alpha> (Formula.Neg \<beta>)) =(let \<alpha>' = rewrite \<alpha>;
                                                      \<beta>' = rewrite \<beta>
                                                in if prop_cond \<alpha>' \<beta>'  
                                                 then Formula.And \<alpha>' (Formula.Neg (Formula.And \<alpha>' \<beta>'))  
                                                 else Formula.And \<alpha>' (Formula.Neg \<beta>'))"





end
