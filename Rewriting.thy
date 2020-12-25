theory Rewriting                  
    imports "MFODL_Monitor_Optimized.Formula" "MFODL_Monitor_Optimized.Regex" "MFODL_Monitor_Optimized.Trace"
begin

datatype (discs_sels) rformula = RPred Formula.name "Formula.trm list"
  | RLet Formula.name nat rformula rformula
  | REq Formula.trm Formula.trm | RLess Formula.trm Formula.trm | RLessEq Formula.trm Formula.trm
  | RNeg rformula | ROr rformula rformula | RAnd rformula rformula | RAnds "rformula list"
  | RExists rformula
  | RAgg nat Formula.agg_op nat Formula.trm rformula
  | RPrev \<I> rformula | RNext \<I> rformula
  | RSince rformula \<I> rformula | RUntil rformula \<I> rformula
  | RRelease rformula \<I> rformula | RTrigger rformula \<I> rformula
  | RDiamondB \<I> rformula | RSquareB \<I> rformula
  | RDiamondW \<I> rformula | RSquareW \<I> rformula
  | RMatchF \<I> "rformula Regex.regex" | RMatchP \<I> "rformula Regex.regex"

abbreviation TT where "TT \<equiv> Formula.Eq (Formula.Const (EInt (0 :: integer))) (Formula.Const (EInt 0))"
abbreviation FF where "FF \<equiv> Formula.Neg TT"

fun embed :: "Formula.formula \<Rightarrow> rformula" where
  "embed (Formula.Pred r ts) = RPred r ts"
| "embed (Formula.Let p b \<phi> \<psi>) = RLet p b (embed \<phi>) (embed \<psi>)"
| "embed (Formula.Eq t1 t2) = REq t1 t2"
| "embed (Formula.Less t1 t2) = RLess t1 t2"
| "embed (Formula.LessEq t1 t2) = RLessEq t1 t2"

| "embed (Formula.Neg (Formula.Since (Formula.Neg \<phi>) I (Formula.Neg \<psi>))) = (if \<phi> = TT then 
    RSquareB I (embed \<psi>) else RTrigger (embed \<phi>) I (embed  \<psi>))"
| "embed (Formula.Neg (Formula.Until (Formula.Neg \<phi>) I (Formula.Neg \<psi>))) =  (if \<phi> = TT then 
    RSquareW I (embed \<psi>) else RRelease (embed \<phi>) I (embed \<psi>))"
| "embed (Formula.Neg \<phi>) = RNeg (embed \<phi>)"

| "embed (Formula.Or \<phi> \<psi>) = ROr (embed \<phi>) (embed \<psi>)"
| "embed (Formula.And \<phi> \<psi>) = RAnd (embed \<phi>) (embed \<psi>)"
| "embed (Formula.Ands \<phi>s) = RAnds (map embed \<phi>s)"

| "embed (Formula.Exists \<phi>) = RExists (embed \<phi>)"
| "embed (Formula.Agg y \<omega> b' f \<phi>) = RAgg y \<omega> b' f (embed \<phi>)"
| "embed (Formula.Prev I \<phi>) = RPrev I (embed \<phi>)"
| "embed (Formula.Next I \<phi>) = RNext I (embed \<phi>)"

| "embed (Formula.Since \<phi> I \<psi>) = (if \<phi> = TT then RDiamondB I (embed \<psi>)
                                             else RSince (embed \<phi>) I (embed \<psi>))"

| "embed (Formula.Until \<phi> I \<psi>) = (if \<phi> = TT then RDiamondW I (embed \<psi>)
                                             else RUntil (embed \<phi>) I (embed \<psi>))"

| "embed (Formula.MatchF I r) = RMatchF I (regex.map_regex embed r)"
| "embed (Formula.MatchP I r) = RMatchP I (regex.map_regex embed r)"


fun project :: "rformula \<Rightarrow> Formula.formula" where
  "project (RPred r ts)  = Formula.Pred r ts"
| "project (RLet p b \<phi> \<psi>) =  Formula.Let p b (project \<phi>) (project \<psi>)"
| "project (REq t1 t2) =Formula.Eq t1 t2"
| "project (RLess t1 t2) =Formula.Less t1 t2"
| "project (RLessEq t1 t2) =Formula.LessEq t1 t2"

| "project (RSquareB I \<psi>) = Formula.Neg (Formula.Since (Formula.Neg TT) I (Formula.Neg (project \<psi>)))"
| "project (RTrigger \<phi> I \<psi>) = Formula.Neg (Formula.Since (Formula.Neg (project \<phi>)) I (Formula.Neg (project \<psi>)))"

| "project (RSquareW I \<psi>) = Formula.Neg (Formula.Until (Formula.Neg TT) I (Formula.Neg (project \<psi>)))"
| "project (RRelease \<phi> I \<psi>) = Formula.Neg (Formula.Until (Formula.Neg (project \<phi>)) I (Formula.Neg (project \<psi>)))"

| "project (RNeg \<phi>) = Formula.Neg (project \<phi>)"
| "project (ROr \<phi> \<psi>) = Formula.Or (project \<phi>) (project \<psi>)"
| "project (RAnd \<phi> \<psi>) = Formula.And (project \<phi>) (project \<psi>)"
| "project (RAnds \<phi>s) = Formula.Ands (map project \<phi>s)"

| "project (RExists \<phi>) = Formula.Exists (project \<phi>)"
| "project (RAgg y \<omega> b' f \<phi>) = Formula.Agg y \<omega> b' f (project \<phi>)"
| "project (RPrev I \<phi>) = Formula.Prev I (project \<phi>)"
| "project (RNext I \<phi>) = Formula.Next I (project \<phi>)"
| "project (RDiamondB I \<phi>) = Formula.Since TT I (project \<phi>)"
| "project (RSince \<phi> I \<psi>) = Formula.Since (project \<phi>) I (project \<psi>)"

| "project (RDiamondW I \<phi>) = Formula.Until TT I (project \<phi>)"
| "project (RUntil \<phi> I \<psi>) = Formula.Until (project \<phi>) I (project \<psi>)"

| "project (RMatchF I r) = Formula.MatchF I (regex.map_regex project r)"
| "project (RMatchP I r) = Formula.MatchP I (regex.map_regex project r)"

definition rsat where "rsat \<sigma> V v i \<phi> = Formula.sat \<sigma> V v i (project \<phi>)"

(*lemma "rsat \<sigma> V v i (embed \<phi>) = Formula.sat \<sigma> V v i \<phi>"
  apply (induct \<phi> arbitrary: V v i rule: embed.induct)
                      apply (auto simp: rsat_def)*)
  

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

primrec tvars where
 "tvars (Formula.Var v) = [v]"
|"tvars (Formula.Const c) = []"
|"tvars (Formula.F2i t) = tvars t"
|"tvars (Formula.I2f t) = tvars t"
|"tvars (Formula.UMinus t) = tvars t"
|"tvars (Formula.Plus t1 t2) =  (tvars t1)@ (tvars t2)"
|"tvars (Formula.Minus t1 t2) =  (tvars t1)@ (tvars t2)"
|"tvars (Formula.Mult t1 t2) =  (tvars t1)@ (tvars t2)"
|"tvars (Formula.Div t1 t2) =  (tvars t1)@ (tvars t2)"
|"tvars (Formula.Mod t1 t2) =  (tvars t1)@ (tvars t2)"


primrec rr :: "nat \<Rightarrow> rformula \<Rightarrow> nat list" where
  "rr b (RPred r ts) = (concat (map tvars ts))"
| "rr b (RLet p _ \<phi> \<psi>) = rr b \<psi>"
| "rr  b(REq t1 t2) = (case (t1,t2) of
                             (Formula.Var x,Formula.Const _) \<Rightarrow> [x-b]
                            |(Formula.Const _,Formula.Var x) \<Rightarrow> [x-b]
                            | _ \<Rightarrow> [])"

| "rr b (RLess t1 t2) = (case (t1,t2) of
                        (Formula.Var x,Formula.Const _) \<Rightarrow> [x-b]
                        |_ \<Rightarrow> [])"
| "rr b (RLessEq t1 t2) = (case (t1,t2) of
                                              (Formula.Var x,Formula.Const _) \<Rightarrow> [x-b]
                                             |_ \<Rightarrow> [])"
| "rr b (ROr \<phi> \<psi>) =  (rr b \<phi>) @ (rr b \<psi>)"
| "rr b (RAnd \<phi> \<psi>) = (let l = rr b \<psi> in  filter (\<lambda>v. List.member l v) (rr b \<phi>))"
| "rr b (RAnds \<phi>s) = (let xs = map (rr b) \<phi>s in concat xs)"
| "rr b (RExists \<phi>) = (if (List.member (rr 0 \<phi>) 0) then rr (Suc b) \<phi>
                                            else [])"
| "rr b (RAgg y \<omega> b' f \<phi>) = []" (*How?*)
| "rr b (RPrev I \<phi>) = rr b \<phi>"
| "rr b (RNext I \<phi>) = rr b \<phi>"
| "rr b (RSince \<phi> I \<psi>) = rr b \<psi>"
| "rr b (RUntil \<phi> I \<psi>) = rr b \<psi>"
| "rr b (RRelease \<phi> I \<psi>) = rr b \<psi>"
| "rr b (RTrigger \<phi> I \<psi>) = rr b \<psi>"
| "rr b (RMatchF I r) = []"
| "rr b (RMatchP I r) = []"
| "rr b (RNeg \<alpha>) = []"
| "rr b (RDiamondW I \<alpha>) = []"
| "rr b (RDiamondB I \<alpha>) = []"
| "rr b (RSquareW I \<alpha>) = []"
| "rr b (RSquareB I \<alpha>) = []"



primrec fvi_l_trm :: "nat \<Rightarrow> Formula.trm \<Rightarrow> nat list" where
  "fvi_l_trm b (Formula.Var x) = (if b \<le> x then [x - b] else [])"
| "fvi_l_trm b (Formula.Const _) = []"
| "fvi_l_trm b (Formula.Plus x y) = (fvi_l_trm b x) @ (fvi_l_trm b y)"
| "fvi_l_trm b (Formula.Minus x y) = (fvi_l_trm b x) @ (fvi_l_trm b y)"
| "fvi_l_trm b (Formula.UMinus x) = fvi_l_trm b x"
| "fvi_l_trm b (Formula.Mult x y) = (fvi_l_trm b x) @ (fvi_l_trm b y)"
| "fvi_l_trm b (Formula.Div x y) = (fvi_l_trm b x) @ (fvi_l_trm b y)"
| "fvi_l_trm b (Formula.Mod x y) = (fvi_l_trm b x) @ (fvi_l_trm b y)"
| "fvi_l_trm b (Formula.F2i x) = fvi_l_trm b x"
| "fvi_l_trm b (Formula.I2f x) = fvi_l_trm b x"

primrec fv_l_regex where
  "fv_l_regex fvl (Regex.Skip n) = []"
| "fv_l_regex fvl (Regex.Test \<phi>) = fvl \<phi>"
| "fv_l_regex fvl (Regex.Plus r s) = (fv_l_regex fvl r) @ (fv_l_regex fvl s)"
| "fv_l_regex fvl (Regex.Times r s) = (fv_l_regex fvl r) @ (fv_l_regex fvl s)"
| "fv_l_regex fvl (Regex.Star r) = fv_l_regex fvl r"


fun fvi_l :: "nat \<Rightarrow> rformula \<Rightarrow> nat list" where
  "fvi_l b (RPred r ts) = concat (map (fvi_l_trm b) ts)"
| "fvi_l b (RLet p _ \<phi> \<psi>) = fvi_l b \<psi>"
| "fvi_l b (REq t1 t2) = (fvi_l_trm b t1) @ (fvi_l_trm b t2)"
| "fvi_l b (RLess t1 t2) = (fvi_l_trm b t1) @ (fvi_l_trm b t2)"
| "fvi_l b (RLessEq t1 t2) = (fvi_l_trm b t1) @ (fvi_l_trm b t2)"
| "fvi_l b (RNeg \<phi>) = fvi_l b \<phi>"
| "fvi_l b (ROr \<phi> \<psi>) = (fvi_l b \<phi>) @ (fvi_l b \<psi>)"
| "fvi_l b (RAnd \<phi> \<psi>) = (fvi_l b \<phi>) @ (fvi_l b \<psi>)"
| "fvi_l b (RAnds \<phi>s) = concat (map (fvi_l b) \<phi>s)"
| "fvi_l b (RExists \<phi>) = fvi_l (Suc b) \<phi>"

| "fvi_l b (RAgg y \<omega> b' f \<phi>) = (fvi_l (b + b') \<phi>) @ (fvi_l_trm (b + b') f) @ 
                                      (if b \<le> y then [y - b] else [])"
| "fvi_l b (RPrev I \<phi>) = fvi_l b \<phi>"
| "fvi_l b (RNext I \<phi>) = fvi_l b \<phi>"
| "fvi_l b (RSince \<phi> I \<psi>) = (fvi_l b \<phi>) @ (fvi_l b \<psi>)"
| "fvi_l b (RUntil \<phi> I \<psi>) = (fvi_l b \<phi>) @ (fvi_l b \<psi>)"
| "fvi_l b (RMatchF I r) = []"
| "fvi_l b (RMatchP I r) = []"
| "fvi_l b (RRelease \<phi> I \<psi>) = (fvi_l b \<phi>) @ (fvi_l b \<psi>)"
| "fvi_l b (RTrigger \<phi> I \<psi>) = (fvi_l b \<phi>) @ (fvi_l b \<psi>)"
| "fvi_l b (RDiamondB I \<psi>) = fvi_l b \<psi>"
| "fvi_l b (RDiamondW I \<psi>) = fvi_l b \<psi>"
| "fvi_l b (RSquareB I \<psi>) = fvi_l b \<psi>"
| "fvi_l b (RSquareW I \<psi>) = fvi_l b \<psi>"

(*| "fvi_l b (Formula.MatchF I r) = fv_l_regex (fvi_l b) r"
| "fvi_l b (Formula.MatchP I r) = fv_l_regex (fvi_l b) r"*)


definition "unrestricted \<alpha> = (length (fvi_l 0 \<alpha>)) - (length (rr 0 \<alpha>))"

definition prop_cond :: "rformula \<Rightarrow> rformula \<Rightarrow> bool"where
 "prop_cond f1 f2 =
       (let rr1 =  (rr 0) f1;
            rr2 = rr 0 f2; 
            fv2 = fvi_l 0 f2
        in (let dif = (filter (\<lambda>v. \<not>(List.member rr2 v)) fv2) 
            in (length (filter (\<lambda>v. List.member dif v)  rr1)) > 0))"

definition "list_inter a b = filter (\<lambda>v. List.member b v) a"

(*lemma "(set a) \<inter> (set b) \<subseteq> list_inter a b"*)




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

primrec shiftI :: "nat \<Rightarrow> rformula \<Rightarrow> rformula" where
  "shiftI k (RPred r ts) = RPred r (map (shiftTI k) ts)"
| "shiftI k (RExists a) = RExists (shiftI (Suc k) a)"
| "shiftI k (RLet nm n a b) = RLet nm n a (shiftI k b)" (*fixed error, a is not shifted*)
| "shiftI k (REq t1 t2) = REq (shiftTI k t1) (shiftTI k t2)"
| "shiftI k (RLess t1 t2) =  RLess (shiftTI k t1) (shiftTI k t2)"
| "shiftI k (RLessEq t1 t2) = RLessEq (shiftTI k t1) (shiftTI k t2)"
| "shiftI k (RNeg a) = RNeg (shiftI k a)"
| "shiftI k (ROr a b) = ROr (shiftI k a) (shiftI k b)"
| "shiftI k (RAnd a b) = RAnd (shiftI k a) (shiftI k b)"
| "shiftI k (RAnds as) = RAnds (map (shiftI k) as)"  
| "shiftI k (RAgg y op b t a) = RAgg (if y < k then y else y + 1)
                                            op b (shiftTI (k + b) t) (shiftI (k + b) a)"
| "shiftI k (RPrev \<I> a) = RPrev \<I> (shiftI k a)"
| "shiftI k (RNext \<I> a) = RNext \<I> (shiftI k a)"
| "shiftI k (RSince a1 \<I> a2) = RSince (shiftI k a1) \<I> (shiftI k a2)"
| "shiftI k (RUntil a1 \<I> a2) = RUntil (shiftI k a1) \<I> (shiftI k a2)"
| "shiftI k (RMatchF \<I> r) = RMatchF \<I> (Regex.map_regex (shiftI k) r)"
| "shiftI k (RMatchP \<I> r) = RMatchP \<I> (Regex.map_regex (shiftI k) r)"
| "shiftI k (RRelease \<phi> I \<psi>) = RRelease (shiftI k \<phi>) I (shiftI k \<psi>)"
| "shiftI k (RTrigger \<phi> I \<psi>) = RTrigger (shiftI k \<phi>) I (shiftI k \<psi>)"
| "shiftI k (RDiamondB I \<psi>) = RDiamondB I (shiftI k \<psi>)"
| "shiftI k (RDiamondW I \<psi>) = RDiamondW I (shiftI k \<psi>)"
| "shiftI k (RSquareB I \<psi>) = RSquareB I (shiftI k \<psi>)"
| "shiftI k (RSquareW I \<psi>) = RSquareW I (shiftI k \<psi>)"


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
(*lemma FF_simp: "FF = Formula.FF" by (simp add: Formula.FF_def)
lemma TT_simp: "TT = Formula.TT" by (simp add: Formula.TT_def FF_simp)*)

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
(*rules 5-8 is covered by next sections rewriteC rules 10-13*)


lemma   sat_rewriteC_1:
  "Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Or \<beta> \<gamma>)) =
   Formula.sat \<sigma> V v i (Formula.Or (Formula.And \<alpha> \<beta>) (Formula.And \<alpha> \<gamma>))"
  by auto

lemma sat_rewriteC_4: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Exists \<beta>)) = 
                    Formula.sat \<sigma> V v i (Formula.Exists (Formula.And (shift \<alpha>) \<beta> ))"
  using sat_shift[of "[]"] by auto

lemma sat_rewriteC_5: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Neg \<beta>))  =
                      Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Neg (Formula.And \<alpha> \<beta>)))"
  by auto

lemma sat_rewriteC_6: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Since (Formula.And \<alpha> \<gamma>) I \<beta> ) =
                                      Formula.sat \<sigma> V v i (Formula.Since (Formula.And \<alpha> \<gamma>) I (Formula.And (diamond_w I \<alpha>) \<beta>))" by fastforce
  
lemma sat_rewriteC_7: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.Until (Formula.And \<alpha> \<gamma>) I \<beta> ) =
                                      Formula.sat \<sigma> V v i (Formula.Until (Formula.And \<alpha> \<gamma>) I (Formula.And (diamond_b I \<alpha>) \<beta>))" by fastforce


lemma sat_rewriteC_12: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Since \<gamma> I \<beta>)) =
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Since \<gamma> I (Formula.And (diamond_w I \<alpha>)\<beta>)))" by auto

lemma sat_rewriteC_13: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Until \<gamma> I \<beta>)) =
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Until \<gamma> I (Formula.And (diamond_b I \<alpha>)\<beta>)))" by auto


(*Duplications *)
(*lemma sat_rewriteC_14: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.And \<alpha> (diamond_b I \<beta>)) = 
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (diamond_b I (Formula.And (diamond_w I \<alpha> ) \<beta>)))" by auto

lemma sat_rewriteC_15: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.And \<alpha> (diamond_w I \<beta>)) = 
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (diamond_w I (Formula.And (diamond_b I \<alpha> ) \<beta>)))" by auto

lemma sat_rewriteC_16: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.And \<alpha> (square_b I \<beta>)) = 
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (square_b I (Formula.And (diamond_w I \<alpha> ) \<beta>)))" by auto

lemma sat_rewriteC_17: "excl_zero I \<Longrightarrow> Formula.sat \<sigma> V v i (Formula.And \<alpha> (square_w I \<beta>)) = 
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (square_w I (Formula.And (diamond_b I \<alpha> ) \<beta>)))" by auto*)

lemma sat_rewriteC_18: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (diamond_b I \<beta>)) = 
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (diamond_b I (Formula.And (diamond_w I \<alpha> ) \<beta>)))" by auto

lemma sat_rewriteC_19: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (diamond_w I \<beta>)) = 
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (diamond_w I (Formula.And (diamond_b I \<alpha> ) \<beta>)))" by auto

lemma sat_rewriteC_20: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (square_b I \<beta>)) = 
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (square_b I (Formula.And (diamond_w I \<alpha> ) \<beta>)))" by auto

lemma sat_rewriteC_21: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (square_w I \<beta>)) = 
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (square_w I (Formula.And (diamond_b I \<alpha> ) \<beta>)))" by auto

lemma sat_rewriteC_22: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Prev I \<beta>)) = 
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Prev I (Formula.And (Formula.Next I \<alpha>) \<beta>)))"  by (auto split: nat.splits)

lemma sat_rewriteC_23: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Next I \<beta>)) = 
                                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Next I (Formula.And (Formula.Prev I \<alpha>) \<beta>)))" by auto

(*Non-trivial rewriteCs gathered together*)

lemma sat_rewriteC_2: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (release \<beta> I \<gamma>)) =
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

lemma sat_rewriteC_3: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (trigger \<beta> I \<gamma>)) =
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


lemma sat_rewriteC_8: "Formula.sat \<sigma> V v i (Formula.Since \<beta> I (Formula.And \<alpha> \<gamma>) ) =
                      Formula.sat \<sigma> V v i (Formula.Since (Formula.And (diamond_b (init_int I) \<alpha>) \<beta>) I (Formula.And \<alpha> \<gamma>))" 
(is "?L = ?R")
proof(rule iffI)
  assume L:?L
  show ?R using iffD1[OF equiv_4 L] by fastforce 
qed auto

lemma sat_rewriteC_9: "Formula.sat \<sigma> V v i (Formula.Until \<beta> I (Formula.And \<alpha> \<gamma>)) =
                                      Formula.sat \<sigma> V v i (Formula.Until (Formula.And (diamond_w (init_int I) \<alpha>) \<beta>) I (Formula.And \<alpha> \<gamma>))" 
(is "?L = ?R")
proof(rule iffI)
  assume L:?L
  show ?R using iffD1[OF equiv_2 L] by fastforce 
qed auto



lemma sat_rewriteC_10: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Since \<beta> I \<gamma>)) =
                       Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Since (Formula.And (diamond_w (init_int I) \<alpha>) \<beta>) I \<gamma>))"
(is "?L = ?R")
proof(rule iffI)
  assume L:?L
  then obtain j where j: "j\<le>i" "mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I" "Formula.sat \<sigma> V v j \<gamma>" "(\<forall>k\<in>{j<..i}. Formula.sat \<sigma> V v i \<alpha> \<and> Formula.sat \<sigma> V v k \<beta>)" by auto
  then have "\<forall>k\<in>{j<..i}. mem (\<tau> \<sigma> i - \<tau> \<sigma> k) (init_int I)" using nat_less_mem_of_init[OF _ j(2)] by fastforce
  then show ?R using L j by fastforce
qed auto


lemma sat_rewriteC_11: "Formula.sat \<sigma> V v i (Formula.And \<alpha> (Formula.Until \<beta> I \<gamma>)) =
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

fun rewriteC1 :: "(('c, 'x) pattern \<times> ('c, 'x) pattern) list \<Rightarrow> 'c term \<Rightarrow> 'c term" where
  "rewriteC1 [] t = t"
| "rewriteC1 ((p, u) # rs) t =
   (case matches [p] [t] Map.empty of
     Some \<sigma> \<Rightarrow> instantiate \<sigma> u
   | None \<Rightarrow> rewriteC1 rs t)"

fun rewriteC :: "(('c, 'x) pattern \<times> ('c, 'x) pattern) list \<Rightarrow> 'c term \<Rightarrow> 'c term" where
  "rewriteC rs (App c ts) = rewriteC1 rs (App c (map (rewriteC rs) ts))"

fun embed where
  "embed (Formula.Until \<phi> I \<psi>) = App (UNTIL I) [embed \<phi>, embed \<psi>]"
*)


(*lemma eval_cong[cong]: "\<And>P::(Formula.trm \<Rightarrow> Formula.trm). (Formula.eval_trm v t = Formula.eval_trm v t') \<Longrightarrow> Formula.eval_trm v (P t) =  Formula.eval_trm v (P t')" sorry
lemma sat_cong[cong]: "(Formula.sat \<sigma> V v i \<alpha> = Formula.sat \<sigma> V v i \<beta>) \<Longrightarrow> Formula.sat \<sigma> V v i (P \<alpha>) = Formula.sat \<sigma> V v i (P \<beta>)" sorry*)

(*future lemma, set of range restricted variables is same or less after rewriteC*)

(*
fun rewriteC1 :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewriteC1 (Formula.And \<alpha> (Formula.Or \<beta> \<gamma>)) = (let \<alpha>' = rewriteC1 \<alpha>;
                                                    \<beta>' = rewriteC1 \<beta>;
                                                    \<gamma>' = rewriteC1 \<gamma>
                                                 in if prop_cond \<alpha>' \<beta>' 
                                                    then Formula.Or (Formula.And \<alpha>' \<beta>') (Formula.And \<alpha>' \<gamma>')
                                                    else Formula.And \<alpha>' (Formula.Or \<beta>' \<gamma>'))"  (*Maybe also a disjunction with prop_cond a' g'*)
| "rewriteC1 f = f"

thm sat.simps

lemma rewriteC1_sat: "Formula.sat \<sigma> V v i (rewriteC1 \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> rule:rewriteC1.induct)
  case (1 \<alpha> \<beta> \<gamma>)
  then show ?case  by (simp del:sat.simps add:Let_def sat_rewriteC_1;auto)
qed auto


fun rewriteC2:: "Formula.formula \<Rightarrow> Formula.formula" where
"rewriteC2 (Formula.And \<alpha> (release \<beta> I \<gamma>)) =(let \<alpha>' = rewriteC2 \<alpha>;
                                                 \<beta>' = rewriteC2 \<beta>;
                                                 \<gamma>' = rewriteC2 \<gamma>
                                                in if prop_cond \<alpha>' \<beta>' 
                                                 then Formula.And \<alpha>' (release (Formula.And \<beta>' (diamond_b (init_int I) \<alpha>')) I (Formula.And \<gamma>' (diamond_b I \<alpha>'))) 
                                                 else Formula.And \<alpha>' (release \<beta>' I \<gamma>'))"
| "rewriteC2 f = f"

thm conj_cong
thm sat.simps(15)
lemma rewriteC2_sat: "Formula.sat \<sigma> V v i (rewriteC2 \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> arbitrary: i rule:rewriteC2.induct)
  case (1 \<alpha> \<beta> I \<gamma>)
  then show ?case by (simp only:rewriteC2.simps Let_def sat_rewriteC_2[symmetric] split:if_splits;simp)
qed auto

fun rewriteC3 :: "Formula.formula \<Rightarrow> Formula.formula" where
 "rewriteC3 (Formula.And \<alpha> (trigger \<beta> I \<gamma>)) =(let \<alpha>' = rewriteC3 \<alpha>;
                                                 \<beta>' = rewriteC3 \<beta>;
                                                 \<gamma>' = rewriteC3 \<gamma>
                                                in if prop_cond \<alpha>' \<beta>'  
                                                 then Formula.And \<alpha>' (trigger (Formula.And \<beta>' (diamond_w (init_int I) \<alpha>')) I (Formula.And \<gamma>' (diamond_w I \<alpha>')))  
                                                 else Formula.And \<alpha>' (trigger \<beta>' I \<gamma>'))"
| "rewriteC3 f = f"

lemma rewriteC3_sat: "Formula.sat \<sigma> V v i (rewriteC3 \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> arbitrary: i rule:rewriteC3.induct)
  case (1 \<alpha> \<beta> I \<gamma>)
  then show ?case by (simp only:rewriteC3.simps Let_def sat_rewriteC_3[symmetric] split:if_splits;simp)
qed auto

fun rewriteC4 :: "Formula.formula \<Rightarrow> Formula.formula" where
 "rewriteC4 (Formula.And \<alpha> (Formula.Exists \<beta>)) =(let \<alpha>' = rewriteC4 \<alpha>;
                                                    \<beta>' = rewriteC4 \<beta>
                                                in if prop_cond \<alpha>' \<beta>'  
                                                 then Formula.Exists (Formula.And (shift \<alpha>') \<beta>')  
                                                 else Formula.And \<alpha>' (Formula.Exists \<beta>'))"
| "rewriteC4 f = f"

thm sat.simps(10)
lemma rewriteC4_sat: "Formula.sat \<sigma> V v i (rewriteC4 f) = Formula.sat \<sigma> V v i f" 
proof(induction f arbitrary: i v rule:rewriteC4.induct)
  case (1 \<alpha> \<beta>)  
  then show ?case by(simp only: rewriteC4.simps shiftI.simps sat_rewriteC_4[symmetric] Let_def split:if_splits;simp) 
qed auto

fun rewriteC5 :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewriteC5 (Formula.And \<alpha> (Formula.Neg \<beta>)) =(let \<alpha>' = rewriteC5 \<alpha>;
                                                 \<beta>' = rewriteC5 \<beta>
                                                in if prop_cond \<alpha>' \<beta>'  
                                                 then Formula.And \<alpha>' (Formula.Neg (Formula.And \<alpha>' \<beta>'))  
                                                 else Formula.And \<alpha>' (Formula.Neg \<beta>'))"
| "rewriteC5 f = f"


lemma rewriteC5_sat: "Formula.sat \<sigma> V v i (rewriteC5 \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> rule:rewriteC5.induct)
  case (1 \<alpha> \<beta>)
  then show ?case by (simp add: Let_def sat_rewriteC_5;auto)
qed auto

fun rewriteC6 :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewriteC6 (Formula.Since (Formula.And \<alpha> \<gamma>) I \<beta> ) =(let \<alpha>' = rewriteC6 \<alpha>;
                                                        \<beta>' = rewriteC6 \<beta>;
                                                        \<gamma>' = rewriteC6 \<gamma>
                                                in if prop_cond \<alpha>' \<beta>' \<and> excl_zero I 
                                                 then Formula.Since (Formula.And \<alpha>' \<gamma>') I (Formula.And (diamond_w I \<alpha>') \<beta>')  
                                                 else Formula.Since (Formula.And \<alpha>' \<gamma>') I \<beta>' )"
| "rewriteC6 f = f"

lemma rewriteC6_sat: "Formula.sat \<sigma> V v i (rewriteC6 \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> arbitrary: i rule:rewriteC6.induct)
  case (1 \<alpha> \<gamma> I \<beta>)
  then show ?case  
  proof(cases "excl_zero I")
    thm sat_rewriteC_6[symmetric]
    case True
    then show ?thesis using 1 by (simp only:rewriteC6.simps Let_def sat_rewriteC_6[OF True,symmetric] split:if_splits;simp)
  next
    case False
    then show ?thesis using 1 by simp
  qed
qed auto

fun rewriteC7 :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewriteC7 (Formula.Until (Formula.And \<alpha> \<gamma>) I \<beta> ) =(let \<alpha>' = rewriteC7 \<alpha>;
                                                        \<beta>' = rewriteC7 \<beta>;
                                                        \<gamma>' = rewriteC7 \<gamma>
                                                in if prop_cond \<alpha>' \<beta>' \<and> excl_zero I 
                                                 then Formula.Until (Formula.And \<alpha>' \<gamma>') I (Formula.And (diamond_b I \<alpha>') \<beta>')
                                                 else Formula.Until (Formula.And \<alpha>' \<gamma>') I \<beta>')"
| "rewriteC7 f = f"

lemma rewriteC7_sat: "Formula.sat \<sigma> V v i (rewriteC7 \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> arbitrary: i rule:rewriteC7.induct)
  case (1 \<alpha> \<gamma> I \<beta>)
  then show ?case
  proof(cases "excl_zero I")
    case True
    then show ?thesis using 1 by (simp only:rewriteC7.simps Let_def sat_rewriteC_7[OF True,symmetric] split:if_splits;simp)
  next
    case False
    then show ?thesis using 1 by simp
  qed
qed auto

fun rewriteC8 :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewriteC8 (Formula.Since \<beta> I (Formula.And \<alpha> \<gamma>)) =(let \<alpha>' = rewriteC8 \<alpha>;
                                                        \<beta>' = rewriteC8 \<beta>;
                                                        \<gamma>' = rewriteC8 \<gamma>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.Since (Formula.And (diamond_b (init_int I) \<alpha>') \<beta>') I (Formula.And \<alpha>' \<gamma>')
                                                 else Formula.Since \<beta>' I (Formula.And \<alpha>' \<gamma>') )"

| "rewriteC8 f = f"

lemma rewriteC8_sat: "Formula.sat \<sigma> V v i (rewriteC8 \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> arbitrary: i rule:rewriteC8.induct)
  case (1 \<beta> I \<alpha> \<gamma>)
  then show ?case by (simp only:rewriteC8.simps Let_def sat_rewriteC_8[symmetric] split:if_splits;simp)
qed auto

fun rewriteC9 :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewriteC9 (Formula.Until \<beta> I (Formula.And \<alpha> \<gamma>)) =(let \<alpha>' = rewriteC9 \<alpha>;
                                                        \<beta>' = rewriteC9 \<beta>;
                                                        \<gamma>' = rewriteC9 \<gamma>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.Until (Formula.And (diamond_w (init_int I) \<alpha>') \<beta>') I (Formula.And \<alpha>' \<gamma>')
                                                 else Formula.Until \<beta>' I (Formula.And \<alpha>' \<gamma>') )"

| "rewriteC9 f = f"

lemma rewriteC9_sat: "Formula.sat \<sigma> V v i (rewriteC9 \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> arbitrary: i rule:rewriteC9.induct)
  case (1 \<beta> I \<alpha> \<gamma>)
  then show ?case by (simp only:rewriteC9.simps Let_def sat_rewriteC_9[symmetric] split:if_splits;simp)
qed auto


fun rewriteC10 :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewriteC10 (Formula.And \<alpha> (Formula.Since \<beta> I \<gamma>)) =(let \<alpha>' = rewriteC10 \<alpha>;
                                                        \<beta>' = rewriteC10 \<beta>;
                                                        \<gamma>' = rewriteC10 \<gamma>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (Formula.Since (Formula.And (diamond_w (init_int I) \<alpha>') \<beta>') I \<gamma>')
                                                 else Formula.And \<alpha>' (Formula.Since \<beta>' I \<gamma>'))"

| "rewriteC10 f = f"

lemma rewriteC10_sat: "Formula.sat \<sigma> V v i (rewriteC10 \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> arbitrary: i rule:rewriteC10.induct)
  case (1 \<alpha> \<beta> I \<gamma>)
  then show ?case by (simp only:rewriteC10.simps Let_def sat_rewriteC_10[symmetric] split:if_splits;simp)
qed auto

fun rewriteC11 :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewriteC11 (Formula.And \<alpha> (Formula.Until \<beta> I \<gamma>)) =(let \<alpha>' = rewriteC11 \<alpha>;
                                                        \<beta>' = rewriteC11 \<beta>;
                                                        \<gamma>' = rewriteC11 \<gamma>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (Formula.Until (Formula.And (diamond_b (init_int I) \<alpha>') \<beta>') I \<gamma>')
                                                 else Formula.And \<alpha>' (Formula.Until \<beta>' I \<gamma>'))"

| "rewriteC11 f = f"

lemma rewriteC11_sat: "Formula.sat \<sigma> V v i (rewriteC11 \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> arbitrary: i rule:rewriteC11.induct)
  case (1 \<beta> I \<alpha> \<gamma>)
  then show ?case by (simp only:rewriteC11.simps Let_def sat_rewriteC_11[symmetric] split:if_splits;simp)
qed auto

fun rewriteC12 :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewriteC12 (Formula.And \<alpha> (Formula.Since \<gamma> I \<beta>)) =(let \<alpha>' = rewriteC12 \<alpha>;
                                                        \<beta>' = rewriteC12 \<beta>;
                                                        \<gamma>' = rewriteC12 \<gamma>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (Formula.Since \<gamma>' I (Formula.And (diamond_w I \<alpha>') \<beta>'))
                                                 else Formula.And \<alpha>' (Formula.Since \<gamma>' I \<beta>'))"

| "rewriteC12 f = f"

lemma rewriteC12_sat: "Formula.sat \<sigma> V v i (rewriteC12 \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> arbitrary: i rule:rewriteC12.induct)
  case (1)
  then show ?case by (simp only:rewriteC12.simps Let_def sat_rewriteC_12[symmetric] split:if_splits;simp)
qed auto

fun rewriteC13 :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewriteC13 (Formula.And \<alpha> (Formula.Until \<gamma> I \<beta>)) =(let \<alpha>' = rewriteC13 \<alpha>;
                                                        \<beta>' = rewriteC13 \<beta>;
                                                        \<gamma>' = rewriteC13 \<gamma>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (Formula.Until \<gamma>' I (Formula.And (diamond_b I \<alpha>') \<beta>'))
                                                 else Formula.And \<alpha>' (Formula.Until \<gamma>' I \<beta>'))"

| "rewriteC13 f = f"

lemma rewriteC13_sat: "Formula.sat \<sigma> V v i (rewriteC13 \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> arbitrary: i rule:rewriteC13.induct)
  case (1)
  then show ?case by (simp only:rewriteC13.simps Let_def sat_rewriteC_13[symmetric] split:if_splits;simp)
qed auto

(*Introduced abbreviations of TT and FF to allow diamond_b abbreviation in pattern*)
function(sequential) rewriteC18 :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewriteC18 (Formula.And \<alpha> (diamond_b I \<beta>)) =(let \<alpha>' = rewriteC18 \<alpha>;
                                     \<beta>' = rewriteC18 \<beta>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (diamond_b I (Formula.And (diamond_w I \<alpha>') \<beta>'))
                                                 else Formula.And \<alpha>' (diamond_b I \<beta>'))"

| "rewriteC18 f = f"
  by (pat_completeness) auto
termination by lexicographic_order

lemma rewriteC18_sat: "Formula.sat \<sigma> V v i (rewriteC18 \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> arbitrary: i rule:rewriteC18.induct)
  case (1)
  then show ?case by (simp only:rewriteC18.simps Let_def sat_rewriteC_18[symmetric] split:if_splits;simp)
qed auto

function(sequential) rewriteC19 :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewriteC19 (Formula.And \<alpha> (diamond_w I \<beta>)) =(let \<alpha>' = rewriteC19 \<alpha>;
                                                   \<beta>' = rewriteC19 \<beta>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (diamond_w I (Formula.And (diamond_b I \<alpha>') \<beta>'))
                                                 else Formula.And \<alpha>' (diamond_w I \<beta>'))"

| "rewriteC19 f = f"
by (pat_completeness) auto

termination by lexicographic_order

lemma rewriteC19_sat: "Formula.sat \<sigma> V v i (rewriteC19 \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> arbitrary: i rule:rewriteC19.induct)
  case (1)
  then show ?case by (simp only:rewriteC19.simps Let_def sat_rewriteC_19[symmetric] split:if_splits;simp)
qed auto

function(sequential) rewriteC20 :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewriteC20 (Formula.And \<alpha> (square_b I \<beta>)) =(let \<alpha>' = rewriteC20 \<alpha>;
                                                   \<beta>' = rewriteC20 \<beta>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (square_b I (Formula.And (diamond_w I \<alpha>' ) \<beta>'))
                                                 else Formula.And \<alpha>' (square_b I \<beta>'))"

| "rewriteC20 f = f"
 by (pat_completeness) auto
termination by lexicographic_order

lemma rewriteC20_sat: "Formula.sat \<sigma> V v i (rewriteC20 \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> arbitrary: i rule:rewriteC20.induct)
  case (1)
  then show ?case by (simp only:rewriteC20.simps Let_def sat_rewriteC_20[symmetric] split:if_splits;simp)
qed auto


function(sequential) rewriteC21 :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewriteC21 (Formula.And \<alpha> (square_w I \<beta>)) =(let \<alpha>' = rewriteC21 \<alpha>;
                                                   \<beta>' = rewriteC21 \<beta>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (square_w I (Formula.And (diamond_b I \<alpha>') \<beta>'))
                                                 else Formula.And \<alpha>' (square_w I \<beta>'))"

| "rewriteC21 f = f"
 by (pat_completeness) auto
termination by lexicographic_order

lemma rewriteC21_sat: "Formula.sat \<sigma> V v i (rewriteC21 \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> arbitrary: i rule:rewriteC21.induct)
  case (1)
  then show ?case by (simp only:rewriteC21.simps Let_def sat_rewriteC_21[symmetric] split:if_splits;simp)
qed auto


function(sequential) rewriteC22 :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewriteC22 (Formula.And \<alpha> (Formula.Prev I \<beta>)) =(let \<alpha>' = rewriteC22 \<alpha>;
                                                      \<beta>' = rewriteC22 \<beta>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (Formula.Prev I (Formula.And (Formula.Next I \<alpha>') \<beta>'))
                                                 else Formula.And \<alpha>' (Formula.Prev I \<beta>'))"

| "rewriteC22 f = f"
 by (pat_completeness) auto

termination by lexicographic_order

lemma rewriteC22_sat: "Formula.sat \<sigma> V v i (rewriteC22 \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> arbitrary: i rule:rewriteC22.induct)
  case (1)
  then show ?case by (simp only:rewriteC22.simps Let_def sat_rewriteC_22[symmetric] split:if_splits ;simp split:nat.splits)
qed auto

function(sequential) rewriteC23 :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewriteC23 (Formula.And \<alpha> (Formula.Next I \<beta>)) =(let \<alpha>' = rewriteC23 \<alpha>;
                                                   \<beta>' = rewriteC23 \<beta>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (Formula.Next I (Formula.And (Formula.Prev I \<alpha>') \<beta>'))
                                                 else Formula.And \<alpha>' (Formula.Next I \<beta>'))"

| "rewriteC23 f = f"
 by (pat_completeness) auto
termination by lexicographic_order

lemma rewriteC23_sat: "Formula.sat \<sigma> V v i (rewriteC23 \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> arbitrary: i rule:rewriteC23.induct)
  case (1)
  then show ?case by (simp only:rewriteC23.simps Let_def sat_rewriteC_23[symmetric] split:if_splits;simp)
qed auto
*)


(*embedded rewriteC rules*)

lemma   sat_rewriteC_1_e:
  "rsat \<sigma> V v i (RAnd \<alpha> (ROr \<beta> \<gamma>)) =
   rsat \<sigma> V v i (ROr (RAnd \<alpha> \<beta>) (RAnd \<alpha> \<gamma>))" sorry

lemma sat_rewriteC_2_e: "rsat \<sigma> V v i (RAnd \<alpha> (RRelease \<beta> I \<gamma>)) =
                                      rsat \<sigma> V v i (RAnd \<alpha> (RRelease (RAnd \<beta> (RDiamondB (init_int I) \<alpha>)) I (RAnd \<gamma> (RDiamondB I \<alpha>))))" sorry

lemma sat_rewriteC_3_e: "rsat \<sigma> V v i (RAnd \<alpha> (RTrigger \<beta> I \<gamma>)) =
                                      rsat \<sigma> V v i (RAnd \<alpha> (RTrigger (RAnd \<beta> (RDiamondW (init_int I) \<alpha>)) I (RAnd \<gamma> (RDiamondW I \<alpha>))))" sorry

lemma sat_rewriteC_4_e: "rsat \<sigma> V v i (RAnd \<alpha> (RExists \<beta>)) = 
                    rsat \<sigma> V v i (RExists (RAnd (shift \<alpha>) \<beta> ))" sorry

lemma sat_rewriteC_5_e: "rsat \<sigma> V v i (RAnd \<alpha> (RNeg \<beta>))  =
                      rsat \<sigma> V v i (RAnd \<alpha> (RNeg (RAnd \<alpha> \<beta>)))" sorry

lemma sat_rewriteC_6_e: "excl_zero I \<Longrightarrow> rsat \<sigma> V v i (RSince (RAnd \<alpha> \<gamma>) I \<beta> ) =
                                      rsat \<sigma> V v i (RSince (RAnd \<alpha> \<gamma>) I (RAnd (RDiamondW I \<alpha>) \<beta>))" sorry

lemma sat_rewriteC_7_e: "excl_zero I \<Longrightarrow> rsat \<sigma> V v i (RUntil (RAnd \<alpha> \<gamma>) I \<beta> ) =
                                        rsat \<sigma> V v i (RUntil (RAnd \<alpha> \<gamma>) I (RAnd (RDiamondB I \<alpha>) \<beta>))" sorry

lemma sat_rewriteC_8_e: "rsat \<sigma> V v i (RSince \<beta> I (RAnd \<alpha> \<gamma>) ) =
                      rsat \<sigma> V v i (RSince (RAnd (RDiamondB (init_int I) \<alpha>) \<beta>) I (RAnd \<alpha> \<gamma>))" sorry

lemma sat_rewriteC_9_e: "rsat \<sigma> V v i (RUntil \<beta> I (RAnd \<alpha> \<gamma>)) =
                                      rsat \<sigma> V v i (RUntil (RAnd (RDiamondW (init_int I) \<alpha>) \<beta>) I (RAnd \<alpha> \<gamma>))" sorry

lemma sat_rewriteC_10_e: "rsat \<sigma> V v i (RAnd \<alpha> (RSince \<beta> I \<gamma>)) =
                       rsat \<sigma> V v i (RAnd \<alpha> (RSince (RAnd (RDiamondW (init_int I) \<alpha>) \<beta>) I \<gamma>))" sorry

lemma sat_rewriteC_11_e: "rsat \<sigma> V v i (RAnd \<alpha> (RUntil \<beta> I \<gamma>)) =
                                       rsat \<sigma> V v i (RAnd \<alpha> (RUntil (RAnd (RDiamondB (init_int I) \<alpha>) \<beta>) I \<gamma>))" sorry
lemma sat_rewriteC_12_e: "rsat \<sigma> V v i (RAnd \<alpha> (RSince \<gamma> I \<beta>)) =
                                       rsat \<sigma> V v i (RAnd \<alpha> (RSince \<gamma> I (RAnd (RDiamondW I \<alpha>)\<beta>)))" sorry

lemma sat_rewriteC_13_e: "rsat \<sigma> V v i (RAnd \<alpha> (RUntil \<gamma> I \<beta>)) =
                                       rsat \<sigma> V v i (RAnd \<alpha> (RUntil \<gamma> I (RAnd (RDiamondB I \<alpha>)\<beta>)))" sorry

lemma sat_rewriteC_18_e: "rsat \<sigma> V v i (RAnd \<alpha> (RDiamondB I \<beta>)) = 
                                       rsat \<sigma> V v i (RAnd \<alpha> (RDiamondB I (RAnd (RDiamondW I \<alpha> ) \<beta>)))" sorry

lemma sat_rewriteC_19_e: "rsat \<sigma> V v i (RAnd \<alpha> (RDiamondW I \<beta>)) = 
                                       rsat \<sigma> V v i (RAnd \<alpha> (RDiamondW I (RAnd (RDiamondB I \<alpha> ) \<beta>)))" sorry

lemma sat_rewriteC_20_e: "rsat \<sigma> V v i (RAnd \<alpha> (RSquareB I \<beta>)) = 
                                       rsat \<sigma> V v i (RAnd \<alpha> (RSquareB I (RAnd (RDiamondW I \<alpha> ) \<beta>)))" sorry

lemma sat_rewriteC_21_e: "rsat \<sigma> V v i (RAnd \<alpha> (RSquareW I \<beta>)) = 
                                       rsat \<sigma> V v i (RAnd \<alpha> (RSquareW I (RAnd (RDiamondB I \<alpha> ) \<beta>)))" sorry

lemma sat_rewriteC_22_e: "rsat \<sigma> V v i (RAnd \<alpha> (RPrev I \<beta>)) = 
                                       rsat \<sigma> V v i (RAnd \<alpha> (RPrev I (RAnd (RNext I \<alpha>) \<beta>)))"  sorry

lemma sat_rewriteC_23_e: "rsat \<sigma> V v i (RAnd \<alpha> (RNext I \<beta>)) = 
                                       rsat \<sigma> V v i (RAnd \<alpha> (RNext I (RAnd (RPrev I \<alpha>) \<beta>)))"sorry

(*6.8.10.12.14.16.18.20 all need non-infinte interval for monitorability. Inlcude in rewriteC function*)

(*Include even more rewriteC rules*)


(*inductive f_con where
id_con: "f_con (\<lambda>f. f)" |
const_con: "f_con (\<lambda>f. g)" |
let_con1: "f_con (\<lambda>f. Formula.Let na n f \<alpha>)"|
let_con2: "f_con (\<lambda>f. Formula.Let na n \<alpha> f)"|
neq_con: "f_con (\<lambda>f. Formula.Neg f)"|
or_con1: "f_con (\<lambda>f. Formula.Or f \<alpha>)"|
or_con2: "f_con (\<lambda>f. Formula.Or \<alpha> f)"|
and_con1: "f_con (\<lambda>f. Formula.And f \<alpha>)"|
and_con2: "f_con (\<lambda>f. Formula.And \<alpha> f)"|
ands_con: "f_con (\<lambda>f. Formula.Ands  (a@[f]@b))"|
exists_con: "f_con (\<lambda>f. Formula.Exists f)"|
agg_con: "f_con (\<lambda>f. Formula.Agg n op n2 t f)"|
prev_con: "f_con (\<lambda>f. Formula.Prev I f)"|
next_con: "f_con (\<lambda>f. Formula.Next I f)"|
since_con1: "f_con (\<lambda>f. Formula.Since f I \<alpha>)"|
since_con2: "f_con (\<lambda>f. Formula.Since \<alpha> I f)"|
until_con1: "f_con (\<lambda>f. Formula.Until f I \<alpha>)"|
until_con2: "f_con (\<lambda>f. Formula.Until \<alpha> I f)"*)

(*inductive f_con where
or_con1: "f_con (\<lambda>f. Formula.Or f \<alpha>)"|
or_con2: "f_con (\<lambda>f. Formula.Or \<alpha> f)"|
and_con1: "f_con (\<lambda>f. Formula.And f \<alpha>)"|
and_con2: "f_con (\<lambda>f. Formula.And \<alpha> f)"*)


  

(*
lemma subst_rsat2: "(rsat \<sigma> V v i \<alpha> = rsat \<sigma> V v i \<alpha>') \<Longrightarrow> 
                    (rsat \<sigma> V v i \<beta> = rsat \<sigma> V v i \<beta>') \<Longrightarrow> rsat \<sigma> V v i (P \<alpha> \<beta>) = rsat \<sigma> V v i (P \<alpha>' \<beta>')" using subst_rsat 
  by (metis remove_neg.simps(1) remove_neg.simps(3) sat.simps(6) subst_sat)

lemma subst_rsat3: "rsat \<sigma> V v i \<alpha> = rsat \<sigma> V v i \<alpha>' \<Longrightarrow> 
                    rsat \<sigma> V v i \<beta> = rsat \<sigma> V v i \<beta>' \<Longrightarrow>     
                    rsat \<sigma> V v i \<gamma> = rsat \<sigma> V v i \<gamma>' \<Longrightarrow> rsat \<sigma> V v i (P \<alpha> \<beta> \<gamma>) = rsat \<sigma> V v i (P \<alpha>' \<beta>' \<gamma>')" using subst_rsat 
  by (metis remove_neg.simps(1) remove_neg.simps(3) sat.simps(6) subst_sat)*)


abbreviation finite_int where "finite_int I \<equiv> (right I) \<noteq> \<infinity>"



primrec my_size :: "rformula \<Rightarrow> nat" where
  "my_size (RPred r ts) = 1"
| "my_size (RLet p _ \<phi> \<psi>) = 1"
| "my_size  (REq t1 t2) = 1"

| "my_size (RLess t1 t2) = 1"
| "my_size (RLessEq t1 t2) = 1"
| "my_size (ROr \<phi> \<psi>) =  1 + (my_size \<phi>) + (my_size \<psi>)"
| "my_size (RAnd \<phi> \<psi>) = 1 + (my_size \<phi>) + (my_size \<psi>)"
| "my_size (RAnds \<phi>s) = 1+ ( fold (+) (map my_size \<phi>s) 0)"

| "my_size (RExists \<phi>) = 1 + my_size \<phi>"
| "my_size (RAgg y \<omega> b' f \<phi>) = 1"
| "my_size (RPrev I \<phi>) = 1+ my_size \<phi>"
| "my_size (RNext I \<phi>) = 1+ my_size \<phi>"
| "my_size (RSince \<phi> I \<psi>) = 1+ (my_size \<phi>) + (my_size \<psi>)"
| "my_size (RUntil \<phi> I \<psi>) =  1+ (my_size \<phi>) + (my_size \<psi>)"
| "my_size (RRelease \<phi> I \<psi>) = 1+ (my_size \<phi>) + (my_size \<psi>)"
| "my_size (RTrigger \<phi> I \<psi>) =  1+ (my_size \<phi>) + (my_size \<psi>)"
| "my_size (RMatchF I r) = 1"
| "my_size (RMatchP I r) = 1"
| "my_size (RNeg \<alpha>) = 1 + my_size \<alpha>"
| "my_size (RDiamondW I \<alpha>) = 1 + my_size \<alpha>"
| "my_size (RDiamondB I \<alpha>) =1 + my_size \<alpha>"
| "my_size (RSquareW I \<alpha>) =1 + my_size \<alpha>"
| "my_size (RSquareB I \<alpha>) = 1 + my_size \<alpha>"

lemma shift_size: "my_size (shift \<alpha>) = my_size \<alpha>" sorry

lemma not_zero: "my_size \<alpha> > 0" by (induction \<alpha>;auto)

datatype tries = First | Second

definition size_tries where
"size_tries t = (case t of First \<Rightarrow> 2 | Second \<Rightarrow> 1)"

function rewrite :: "rformula \<Rightarrow> tries \<Rightarrow> rformula" where
(*1*)  "rewrite f t = (case f of
                        (RAnd \<alpha> (ROr \<beta> \<gamma>)) \<Rightarrow>
       (if prop_cond \<alpha> \<beta> \<and> prop_cond \<alpha> \<gamma>
       then ROr (rewrite (RAnd \<alpha> \<beta>) First) (rewrite (RAnd \<alpha> \<gamma>) First)
       else let \<alpha>' = rewrite \<alpha> First; \<beta>' = rewrite \<beta> First;  \<gamma>' = rewrite \<gamma> First in RAnd \<alpha>' (ROr \<beta>' \<gamma>')))"
|
(*1*)  "rewrite (RAnd \<alpha> (ROr \<beta> \<gamma>)) t =
       (if prop_cond \<alpha> \<beta> \<and> prop_cond \<alpha> \<gamma>
       then ROr (rewrite (RAnd \<alpha> \<beta>) First) (rewrite (RAnd \<alpha> \<gamma>) First)
       else let \<alpha>' = rewrite \<alpha> First; \<beta>' = rewrite \<beta> First;  \<gamma>' = rewrite \<gamma> First in RAnd \<alpha>' (ROr \<beta>' \<gamma>'))" (*added prop_cond gamma because the rewrite shouldn't be position dependent*)
(*(*1_2*)| "rewriteC (ROr \<beta> \<gamma>) \<alpha> =
       (if prop_cond \<alpha> \<beta> \<and> prop_cond \<alpha> \<gamma>
       then ROr (rewrite (RAnd \<alpha> \<beta>)) (rewrite (RAnd \<alpha> \<gamma>))
       else let \<alpha>' = rewrite \<alpha>; \<beta>' = rewrite \<beta>;  \<gamma>' = rewrite \<gamma> in RAnd \<alpha>' (ROr \<beta>' \<gamma>'))"*)
(*(*2*) | "rewrite (RAnd \<alpha> (RRelease \<beta> I \<gamma>)) t =
      (if prop_cond \<alpha> \<beta>
       then RAnd (rewrite \<alpha> First) (RRelease (rewrite (RAnd \<beta> (RDiamondB (init_int I) \<alpha>)) First) I (rewrite (RAnd \<gamma> (RDiamondB I \<alpha>)) First))
       else let \<alpha>' = rewrite \<alpha> First; \<beta>' = rewrite \<beta> First;  \<gamma>' = rewrite \<gamma> First in (RAnd \<alpha>' (RRelease \<beta>' I \<gamma>')))"
(*2_2*) | "rewriteC (RRelease \<beta> I \<gamma>) \<alpha> =
      (if prop_cond \<alpha> \<beta>
       then RAnd (rewrite \<alpha>) (RRelease (rewrite (RAnd \<beta> (RDiamondB (init_int I) \<alpha>))) I (rewrite (RAnd \<gamma> (RDiamondB I \<alpha>))))
       else let \<alpha>' = rewrite \<alpha>; \<beta>' = rewrite \<beta>;  \<gamma>' = rewrite \<gamma> in (RAnd \<alpha>' (RRelease \<beta>' I \<gamma>')))"*)
(*3*) | "rewrite (RAnd \<alpha> (RTrigger \<beta> I \<gamma>)) t =
      (if prop_cond \<alpha> \<beta>
       then RAnd (rewrite \<alpha> First) (RTrigger (rewrite (RAnd \<beta> (RDiamondW (init_int I) \<alpha>)) First) I (rewrite (RAnd \<gamma> (RDiamondW I \<alpha>)) First))
       else let \<alpha>' = rewrite \<alpha> First; \<beta>' = rewrite \<beta> First;  \<gamma>' = rewrite \<gamma> First in (RAnd \<alpha>' (RTrigger \<beta>' I \<gamma>')))"
  (*(*3_2*) | "rewrite (RAnd (RTrigger \<beta> I \<gamma>) \<alpha>) =
      (if prop_cond \<alpha> \<beta>
       then RAnd (rewrite \<alpha>) (RTrigger (rewrite (RAnd \<beta> (RDiamondW (init_int I) \<alpha>))) I (rewrite (RAnd \<gamma> (RDiamondW I \<alpha>))))
       else let \<alpha>' = rewrite \<alpha>; \<beta>' = rewrite \<beta>;  \<gamma>' = rewrite \<gamma> in (RAnd \<alpha>' (RTrigger \<beta>' I \<gamma>')))"*)
(*4*) | "rewrite (RAnd \<alpha> (RExists \<beta>)) t = 
       (if prop_cond \<alpha> \<beta>  
        then RExists (rewrite (RAnd (shift \<alpha>) \<beta>) First)
        else let \<alpha>' = rewrite \<alpha> First; \<beta>' = rewrite \<beta> First in RAnd \<alpha>' (RExists \<beta>'))"
(*(*4_2*) | "rewrite (RAnd (RExists \<beta>) \<alpha>) = 
       (if prop_cond \<alpha> \<beta>  
        then RExists (rewrite (RAnd (shift \<alpha>) \<beta>))
        else let \<alpha>' = rewrite \<alpha>; \<beta>' = rewrite \<beta> in RAnd \<alpha>' (RExists \<beta>'))"*)
(*5*) | "rewrite (RAnd \<alpha> (RNeg \<beta>)) t =
      (if prop_cond \<alpha> \<beta>  
       then RAnd (rewrite \<alpha> First) ((RNeg (rewrite (RAnd \<alpha> \<beta>) First)))  
       else let \<alpha>' = rewrite \<alpha> First; \<beta>' = rewrite \<beta> First in RAnd \<alpha>' (RNeg \<beta>'))"
(*(*5_2*) | "rewrite (RAnd (RNeg \<beta>) \<alpha>) =
      (if prop_cond \<alpha> \<beta>  
       then RAnd (rewrite \<alpha>) ((RNeg (rewrite (RAnd \<alpha> \<beta>))))  
       else let \<alpha>' = rewrite \<alpha>; \<beta>' = rewrite \<beta> in RAnd \<alpha>' (RNeg \<beta>'))"*)
(*10,12*) | "rewrite (RAnd \<alpha> (RSince \<beta> I \<gamma>)) t =
      (if (prop_cond \<alpha> \<beta>) \<and> (finite_int I) then RAnd (rewrite \<alpha> First) (RSince (rewrite (RAnd (RDiamondW (init_int I) \<alpha>) \<beta>) First) I (rewrite \<gamma> First))
       else if (prop_cond \<alpha> \<gamma>) \<and> (finite_int I) then RAnd (rewrite \<alpha> First) (RSince (rewrite \<beta> First) I (rewrite (RAnd (RDiamondW I \<alpha>) \<gamma>) First))
       else let \<alpha>' = rewrite \<alpha> First; \<beta>' = rewrite \<beta> First;  \<gamma>' = rewrite \<gamma> First in RAnd \<alpha>' (RSince \<beta>' I \<gamma>'))"
(*(*10_2,12_2*) | "rewrite (RAnd (RSince \<beta> I \<gamma>) \<alpha>) =
      (if (prop_cond \<alpha> \<beta>) \<and> (finite_int I) then RAnd (rewrite \<alpha>) (RSince (rewrite (RAnd (RDiamondW (init_int I) \<alpha>) \<beta>)) I (rewrite \<gamma>))
       else if (prop_cond \<alpha> \<gamma>) \<and> (finite_int I) then RAnd (rewrite \<alpha>) (RSince (rewrite \<beta>) I (rewrite (RAnd (RDiamondW I \<alpha>) \<gamma>)))
       else let \<alpha>' = rewrite \<alpha>; \<beta>' = rewrite \<beta>;  \<gamma>' = rewrite \<gamma> in RAnd \<alpha>' (RSince \<beta>' I \<gamma>'))"*)
(*11,13*) | "rewrite (RAnd \<alpha> (RUntil \<beta> I \<gamma>)) t =
      (if (prop_cond \<alpha> \<beta>) \<and> (finite_int I) then RAnd (rewrite \<alpha> First) (RUntil (rewrite (RAnd (RDiamondB (init_int I) \<alpha>) \<beta>) First) I (rewrite \<gamma> First))
       else if (prop_cond \<alpha> \<gamma>) \<and> (finite_int I) then RAnd (rewrite \<alpha> First) (RUntil (rewrite \<beta> First) I (rewrite (RAnd (RDiamondB I \<alpha>) \<gamma>) First))
       else let \<alpha>' = rewrite \<alpha> First; \<beta>' = rewrite \<beta> First;  \<gamma>' = rewrite \<gamma> First in RAnd \<alpha>' (RUntil \<beta>' I \<gamma>'))"
(*(*11_2,13_2*) | "rewrite (RAnd (RUntil \<beta> I \<gamma>) \<alpha>) =
      (if (prop_cond \<alpha> \<beta>) \<and> (finite_int I) then RAnd (rewrite \<alpha>) (RUntil (rewrite (RAnd (RDiamondB (init_int I) \<alpha>) \<beta>)) I (rewrite \<gamma>))
       else if (prop_cond \<alpha> \<gamma>) \<and> (finite_int I) then RAnd (rewrite \<alpha>) (RUntil (rewrite \<beta>) I (rewrite (RAnd (RDiamondB I \<alpha>) \<gamma>)))
       else let \<alpha>' = rewrite \<alpha>; \<beta>' = rewrite \<beta>;  \<gamma>' = rewrite \<gamma> in RAnd \<alpha>' (RUntil \<beta>' I \<gamma>'))"*)
(*18*) | "rewrite (RAnd \<alpha> (RDiamondB I \<beta>)) t =
      (if (prop_cond \<alpha> \<beta>) \<and> (finite_int I)
       then RAnd (rewrite \<alpha> First) (RDiamondB I (RAnd (RDiamondW I (rewrite \<alpha> First)) (rewrite \<beta> First)))
       else let \<alpha>' = rewrite \<alpha> First; \<beta>' = rewrite \<beta> First in RAnd \<alpha>' (RDiamondB I \<beta>'))"
(*(*18_2*) | "rewrite (RAnd (RDiamondB I \<beta>) \<alpha>) =
      (if (prop_cond \<alpha> \<beta>) \<and> (finite_int I)
       then RAnd (rewrite \<alpha>) (RDiamondB I (RAnd (RDiamondW I (rewrite \<alpha>)) (rewrite \<beta>)))
       else let \<alpha>' = rewrite \<alpha>; \<beta>' = rewrite \<beta> in RAnd \<alpha>' (RDiamondB I \<beta>'))"*)
(*19*) | "rewrite (RAnd \<alpha> (RDiamondW I \<beta>)) t =
      (if (prop_cond \<alpha> \<beta>)
       then RAnd (rewrite \<alpha> First) (RDiamondW I (RAnd (RDiamondB I (rewrite \<alpha> First)) (rewrite \<beta> First)))
       else let \<alpha>' = rewrite \<alpha> First; \<beta>' = rewrite \<beta> First in RAnd \<alpha>' (RDiamondW I \<beta>'))"
(*(*19_2*) | "rewrite (RAnd (RDiamondW I \<beta>) \<alpha>) =
      (if (prop_cond \<alpha> \<beta>)
       then RAnd (rewrite \<alpha>) (RDiamondW I (RAnd (RDiamondB I (rewrite \<alpha>)) (rewrite \<beta>)))
       else let \<alpha>' = rewrite \<alpha>; \<beta>' = rewrite \<beta> in RAnd \<alpha>' (RDiamondW I \<beta>'))"*)
 (*20*) | "rewrite (RAnd \<alpha> (RSquareB I \<beta>)) t =
      (if (prop_cond \<alpha> \<beta>) \<and> (finite_int I)
       then RAnd (rewrite \<alpha> First) (RSquareB I (RAnd (RDiamondW I (rewrite \<alpha> First)) (rewrite \<beta> First)))
       else let \<alpha>' = rewrite \<alpha> First; \<beta>' = rewrite \<beta> First in RAnd \<alpha>' (RSquareB I \<beta>'))" (*some of these rules don't rewrite the conjunction, of diamond/square, because it doesn't increase rr of the conjunction more than recursing the leaves*)
(*(*20_2*) | "rewrite (RAnd (RSquareB I \<beta>) \<alpha>) =
      (if (prop_cond \<alpha> \<beta>) \<and> (finite_int I)
       then RAnd (rewrite \<alpha>) (RSquareB I (RAnd (RDiamondW I (rewrite \<alpha>)) (rewrite \<beta>)))
       else let \<alpha>' = rewrite \<alpha>; \<beta>' = rewrite \<beta> in RAnd \<alpha>' (RSquareB I \<beta>'))"*)
 (*21*) | "rewrite (RAnd \<alpha> (RSquareW I \<beta>)) t =
      (if (prop_cond \<alpha> \<beta>)
       then RAnd (rewrite \<alpha> First) (RSquareW I (RAnd (RDiamondB I (rewrite \<alpha> First)) (rewrite \<beta> First)))
       else let \<alpha>' = rewrite \<alpha> First; \<beta>' = rewrite \<beta> First in RAnd \<alpha>' (RSquareW I \<beta>'))"
(* (*21_2*) | "rewrite (RAnd (RSquareW I \<beta>) \<alpha>) =
      (if (prop_cond \<alpha> \<beta>)
       then RAnd (rewrite \<alpha>) (RSquareW I (RAnd (RDiamondB I (rewrite \<alpha>)) (rewrite \<beta>)))
       else let \<alpha>' = rewrite \<alpha>; \<beta>' = rewrite \<beta> in RAnd \<alpha>' (RSquareW I \<beta>'))"*)
 (*22*) | "rewrite (RAnd \<alpha> (RPrev I \<beta>)) t =
      (if (prop_cond \<alpha> \<beta>)
       then RAnd (rewrite \<alpha> First) (RPrev I (RAnd (RNext I (rewrite \<alpha> First)) (rewrite \<beta> First)))
       else let \<alpha>' = rewrite \<alpha> First; \<beta>' = rewrite \<beta> First in RAnd \<alpha>' (RPrev I \<beta>'))"
(*(*22_2*) | "rewrite (RAnd (RPrev I \<beta>) \<alpha>) =
      (if (prop_cond \<alpha> \<beta>)
       then RAnd (rewrite \<alpha>) (RPrev I (RAnd (RNext I (rewrite \<alpha>)) (rewrite \<beta>)))
       else let \<alpha>' = rewrite \<alpha>; \<beta>' = rewrite \<beta> in RAnd \<alpha>' (RPrev I \<beta>'))"*)
(*23*) | "rewrite (RAnd \<alpha> (RNext I \<beta>)) t =
      (if (prop_cond \<alpha> \<beta>)
       then RAnd (rewrite \<alpha> First) (RNext I (RAnd (RPrev I (rewrite \<alpha> First)) (rewrite \<beta> First)))
       else let \<alpha>' = rewrite \<alpha> First; \<beta>' = rewrite \<beta> First in (RAnd \<alpha>' (RNext I \<beta>')))"
(*(*23_2*) | "rewrite (RAnd (RNext I \<beta>) \<alpha>) =
      (if (prop_cond \<alpha> \<beta>)
       then RAnd (rewrite \<alpha>) (RNext I (RAnd (RPrev I (rewrite \<alpha>)) (rewrite \<beta>)))
       else let \<alpha>' = rewrite \<alpha>; \<beta>' = rewrite \<beta> in (RAnd \<alpha>' (RNext I \<beta>')))"*)

(*6,8*)| "rewrite (RSince l I r) t = (
             case (l,r) of
              (RAnd \<alpha> \<gamma>,\<beta>) \<Rightarrow> (if (prop_cond \<alpha> \<beta>) \<and> (finite_int I)
                               then RSince (rewrite (RAnd \<alpha> \<gamma>) First) I (rewrite (RAnd (RDiamondW I \<alpha>) \<beta>) First)
                               else let \<alpha>' = rewrite \<alpha> First; \<beta>' = rewrite \<beta> First;  \<gamma>' = rewrite \<gamma> First in RSince (RAnd \<alpha>' \<gamma>') I \<beta>')
             | (\<beta>,RAnd \<alpha> \<gamma>) \<Rightarrow> (if (prop_cond \<alpha> \<beta>)
                                then RSince (rewrite (RAnd (RDiamondB I \<alpha>) \<beta>) First) I (rewrite (RAnd \<alpha> \<gamma>) First)
                                else let \<alpha>' = rewrite \<alpha> First; \<beta>' = rewrite \<beta> First;  \<gamma>' = rewrite \<gamma> First in RSince \<beta>' I (RAnd \<alpha>' \<gamma>'))
             | _ \<Rightarrow> let l' = rewrite l First; r' = rewrite r First in RSince l' I r')"
(*7,9*) | "rewrite (RUntil l I r) t = (
             case (l,r) of
              (RAnd \<alpha> \<gamma>,\<beta>) \<Rightarrow>  (if (prop_cond \<alpha> \<beta>)
                                then RUntil (rewrite (RAnd \<alpha> \<gamma>) First) I (rewrite (RAnd (RDiamondB I \<alpha>) \<beta>) First)
                                else let \<alpha>' = rewrite \<alpha> First; \<beta>' = rewrite \<beta> First;  \<gamma>' = rewrite \<gamma> First in RUntil (RAnd \<alpha>' \<gamma>') I \<beta>')
             | (\<beta>,RAnd \<alpha> \<gamma>) \<Rightarrow> (if (prop_cond \<alpha> \<beta>)
                                then RUntil (rewrite (RAnd (RDiamondW I \<alpha>) \<beta>) First) I (rewrite (RAnd \<alpha> \<gamma>) First)
                                else let \<alpha>' = rewrite \<alpha> First; \<beta>' = rewrite \<beta> First;  \<gamma>' = rewrite \<gamma> First in RUntil \<beta>' I (RAnd \<alpha>' \<gamma>'))
             | _ \<Rightarrow> let l' = rewrite l First; r' = rewrite r First in RSince l' I r')"
| "rewrite (RAnd f1 f2) First = rewrite (RAnd f2 f1) Second"
| "rewrite (RAnd f1 f2) S)cond = RAnd f1 f2"

| "rewrite f t = f"

  by pat_completeness auto
termination 
  apply(relation "measure (\<lambda>f t. (my_size f) + (size_tries t)")
  apply (auto simp add: shift_size not_zero) (*not_zero important because size of constructor then depends on its' number of arguments*)
  done
lemma size_r: "\<And>r::rformula. m r > 0" sorry



  by pat_completeness auto
termination 
  apply(relation "measure my_size")
  apply (auto simp add: shift_size not_zero) (*not_zero important because size of constructor then depends on its' number of arguments*)
  done
lemma size_r: "\<And>r::rformula. m r > 0" sorry

inductive f_conr where
or_con1: "f_conr (\<lambda>r. ROr r \<alpha>)"|
or_con2: "f_conr (\<lambda>r. ROr \<alpha> r)"|
and_con1: "f_conr (\<lambda>r. RAnd r \<alpha>)"|
and_con2: "f_conr (\<lambda>r. RAnd \<alpha> r)"

inductive f_conr2 where
f_conr2_1_t: "f_conr2 (\<lambda>f1 f2. ROr f1 f2)"

inductive f_conr3 where
f_conr3_1_l: "f_conr3 (\<lambda>f1 f2 f3. RAnd f1 (ROr f2 f3))"


(*inductive trans_con where
trans_or1: "trans_con (\<lambda>r. ROr r \<alpha>) (\<lambda>f. Formula.Or f \<beta>)" |
trans_or2: "trans_con (\<lambda>r. ROr \<alpha> r) (\<lambda>f. Formula.Or \<beta> f)" |
trans_and1: "trans_con (\<lambda>r. RAnd r \<alpha>) (\<lambda>f. Formula.And f \<beta>)" |
trans_and2: "trans_con (\<lambda>r. RAnd \<alpha> r) (\<lambda>f. Formula.And f \<beta>)"

lemma trans_con_l: "trans_con P P' \<Longrightarrow> f_conr P \<and> f_con P'" using f_con.simps f_conr.simps trans_con.simps by auto

lemma trans_con_unique: "trans_con P P' \<Longrightarrow> trans_con P P'' \<Longrightarrow> P' = P''" sorry

lemma trans_con_l2: "trans_con P P' \<Longrightarrow> rsat \<sigma> V v i (P \<alpha>) \<Longrightarrow> Formula.sat \<sigma> V v i (P' (project \<alpha>))"
  sorry


lemma subst_sat: "f_con P \<Longrightarrow> Formula.sat \<sigma> V v i \<alpha> = Formula.sat \<sigma> V v i \<beta> \<Longrightarrow> Formula.sat \<sigma> V v i (P \<alpha>) = Formula.sat \<sigma> V v i (P \<beta>)" sorry*)

lemma subst_rsat: "f_conr P \<Longrightarrow> rsat \<sigma> V v i \<alpha> = rsat \<sigma> V v i \<beta> \<Longrightarrow> rsat \<sigma> V v i (P \<alpha>) = rsat \<sigma> V v i (P \<beta>)" 
  using f_conr.simps rsat_def by auto

lemma subst_rsat2: "f_conr2 P \<Longrightarrow> (rsat \<sigma> V v i \<alpha> = rsat \<sigma> V v i \<alpha>') \<Longrightarrow> 
                    (rsat \<sigma> V v i \<beta> = rsat \<sigma> V v i \<beta>') \<Longrightarrow> rsat \<sigma> V v i (P \<alpha> \<beta>) = rsat \<sigma> V v i (P \<alpha>' \<beta>')" using subst_rsat 
  by (simp add: f_conr2.simps rsat_def)

lemma subst_rsat3: "f_conr3 P \<Longrightarrow> rsat \<sigma> V v i \<alpha> = rsat \<sigma> V v i \<alpha>' \<Longrightarrow> 
                    rsat \<sigma> V v i \<beta> = rsat \<sigma> V v i \<beta>' \<Longrightarrow>     
                    rsat \<sigma> V v i \<gamma> = rsat \<sigma> V v i \<gamma>' \<Longrightarrow> rsat \<sigma> V v i (P \<alpha> \<beta> \<gamma>) = rsat \<sigma> V v i (P \<alpha>' \<beta>' \<gamma>')" using subst_rsat 
  by (simp add: f_conr3.simps rsat_def)




lemma rewriteC_sat2: "rsat \<sigma> V v i (rewriteC \<alpha>) = rsat \<sigma> V v i \<alpha>"
proof(induct \<alpha> arbitrary:v rule: rewriteC.induct)
  case (1 \<alpha> \<beta> \<gamma>)
  have con:"f_conr2 (\<lambda>f1 f2. ROr f1 f2)" by (rule f_conr2_1_t) 
  from 1 show ?case 
  proof(cases "prop_cond \<alpha> \<beta>")
    case True
    then show ?thesis 
      apply(subst rewriteC.simps)
    apply(simp only: Let_def simp_thms(7,15,16)  split:if_splits)
    apply(simp only: subst_rsat2[OF con 1(1-2)[OF True]] )
    apply(simp only: sat_rewriteC_1_e[symmetric])
    done
  next
    case False
    have con:"f_conr3 (\<lambda>f1 f2 f3. RAnd f1 (ROr f2 f3))" by (rule f_conr3_1_l)
    from False show ?thesis 
      apply(subst rewriteC.simps)
      apply(simp only: Let_def simp_thms(8,15,16)  split:if_splits)
      apply(simp only: subst_rsat3[OF con 1(3)[OF False] 1(4)[OF False refl] 1(5)[OF False refl refl]] )
      done
  qed
next
case (2 \<alpha> \<beta> I \<gamma>)
  then show ?case sorry
next
  case (3 \<alpha> \<beta> I \<gamma>)
  then show ?case sorry
next
case (4 \<alpha> \<beta>)
then show ?case sorry
next
  case (5 \<alpha> \<beta>)
  then show ?case sorry
next
  case (6 l I r)
  then show ?case sorry
next
  case (7 l I r)
  then show ?case sorry
next
  case (8 \<alpha> \<beta> I \<gamma>)
  then show ?case sorry
next
  case (9 \<alpha> \<beta> I \<gamma>)
  then show ?case sorry
next
  case (10 \<alpha> I \<beta>)
  then show ?case sorry
next
  case (11 \<alpha> I \<beta>)
  then show ?case sorry
next
  case (12 \<alpha> I \<beta>)
  then show ?case sorry
next
  case (13 \<alpha> I \<beta>)
  then show ?case sorry
next
  case (14 \<alpha> I \<beta>)
  then show ?case sorry
next
  case (15 \<alpha> I \<beta>)
  then show ?case sorry
qed auto

lemma rewriteC_sat: "Formula.sat \<sigma> V v i (rewriteC \<alpha>) = Formula.sat \<sigma> V v i \<alpha>"
  apply(induct \<alpha> arbitrary:  v rule: rewriteC.induct)

    apply (subst rewriteC.simps shiftI.simps)
    apply(simp only: Let_def  split: formula.splits if_splits )
    apply(simp only: sat_rewriteC_1 sat_rewriteC_4[symmetric] sat_rewriteC_5[symmetric])
                      apply(auto simp: sat_shift[of "[]" 0, simplified])
  sorry


fun rewriteCo :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewriteCo ( Formula.And \<alpha> (Formula.Or \<beta> \<gamma>)) =
       (if prop_cond \<alpha> \<beta>
       then Formula.Or ((Formula.And \<alpha> \<beta>)) ((Formula.And \<alpha> \<gamma>))
       else let \<alpha>' = rewriteCo \<alpha>; \<beta>' = rewriteCo \<beta>;  \<gamma>' = rewriteCo \<gamma> in Formula.And \<alpha>' (Formula.Or \<beta>' \<gamma>'))"
| "rewriteCo (Formula.And \<alpha> (Formula.Exists \<beta>)) = 
       (if prop_cond \<alpha> \<beta>  
        then Formula.Exists ((Formula.And (shift \<alpha>) \<beta>))
        else let \<alpha>' = rewriteCo \<alpha>; \<beta>' = rewriteCo \<beta> in Formula.And \<alpha>' (Formula.Exists \<beta>'))"
| "rewriteCo (Formula.And \<alpha> (Formula.Neg \<beta>)) =
      (if prop_cond \<alpha> \<beta>  
       then Formula.And \<alpha> ((Formula.Neg ((Formula.And \<alpha> \<beta>))))  
       else let \<alpha>' = rewriteCo \<alpha>; \<beta>' = rewriteCo \<beta> in Formula.And \<alpha>' (Formula.Neg \<beta>'))"
| "rewriteCo f = f"
(*Same functions in Case-expression form*)

(*function rewriteC :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewriteC f = (case f of
     Formula.And \<alpha> (Formula.Or \<beta> \<gamma>) \<Rightarrow>
       (if prop_cond \<alpha> \<beta>
       then Formula.Or (rewriteC (Formula.And \<alpha> \<beta>)) (rewriteC (Formula.And \<alpha> \<gamma>))
       else let \<alpha>' = rewriteC \<alpha>; \<beta>' = rewriteC \<beta>;  \<gamma>' = rewriteC \<gamma> in Formula.And \<alpha>' (Formula.Or \<beta>' \<gamma>'))
     | Formula.And \<alpha> (Formula.Exists \<beta>) \<Rightarrow>
       (if prop_cond \<alpha> \<beta>  
        then Formula.Exists (rewriteC (Formula.And (shift \<alpha>) \<beta>))
        else let \<alpha>' = rewriteC \<alpha>; \<beta>' = rewriteC \<beta> in Formula.And \<alpha>' (Formula.Exists \<beta>'))
     | Formula.And \<alpha> (Formula.Neg \<beta>) \<Rightarrow>
      (if prop_cond \<alpha> \<beta>  
       then Formula.And \<alpha> ((Formula.Neg (rewriteC (Formula.And \<alpha> \<beta>))))  
       else let \<alpha>' = rewriteC \<alpha>; \<beta>' = rewriteC \<beta> in Formula.And \<alpha>' (Formula.Neg \<beta>'))
   | _ \<Rightarrow> f)"
  by pat_completeness auto
termination by (relation "measure size") (auto simp add: shift_size)

function rewriteCo :: "Formula.formula \<Rightarrow> Formula.formula" where
  "rewriteCo f = (case f of
     Formula.And \<alpha> (Formula.Or \<beta> \<gamma>) \<Rightarrow>
       (if prop_cond \<alpha> \<beta>
       then Formula.Or (Formula.And \<alpha> \<beta>) (Formula.And \<alpha> \<gamma>)
       else let \<alpha>' = rewriteCo \<alpha>; \<beta>' = rewriteCo \<beta>;  \<gamma>' = rewriteCo \<gamma> in Formula.And \<alpha>' (Formula.Or \<beta>' \<gamma>'))
     | Formula.And \<alpha> (Formula.Exists \<beta>) \<Rightarrow>
       (if prop_cond \<alpha> \<beta>  
        then Formula.Exists (Formula.And (shift \<alpha>) \<beta>)
        else let \<alpha>' = rewriteCo \<alpha>; \<beta>' = rewriteCo \<beta> in Formula.And \<alpha>' (Formula.Exists \<beta>'))
     | Formula.And \<alpha> (Formula.Neg \<beta>) \<Rightarrow>
      (if prop_cond \<alpha> \<beta>  
       then Formula.And \<alpha> (Formula.Neg (Formula.And \<alpha> \<beta>))  
       else let \<alpha>' = rewriteCo \<alpha>; \<beta>' = rewriteCo \<beta> in Formula.And \<alpha>' (Formula.Neg \<beta>'))
   | _ \<Rightarrow> f)"
  by pat_completeness auto
termination by (relation "measure size") (auto simp add: shift_size)*)


(*
lemma o_to_sat: "Formula.sat \<sigma> V v i (rewriteCo \<alpha>) = Formula.sat \<sigma> V v i \<alpha>"
proof(induct \<alpha> arbitrary: v rule: rewriteCo.induct)
case (1 \<alpha> \<beta> \<gamma>)
  then show ?case 
    apply(subst rewriteCo.simps shiftI.simps)
    apply(simp only: Let_def split:if_splits)
    apply(simp only: sat_rewriteC_1;simp)    
    done
next
  case (2 \<alpha> \<beta>)
  then show ?case 
    apply(subst rewriteCo.simps shiftI.simps)
    apply(simp only: Let_def split:if_splits)
    apply(simp only: sat_rewriteC_4[symmetric];simp)    
    done
next
case (3 \<alpha> \<beta>)
  then show ?case sorry
qed auto


lemma r_to_r: "Formula.sat \<sigma> V v i (rewriteC \<alpha>) = Formula.sat \<sigma> V v i (rewriteCo \<alpha>)" 
  by(induct \<alpha> arbitrary: v rule: rewriteC.induct;auto simp add: o_to_sat)

lemma my_induct: "(\<And>\<alpha> \<beta> \<gamma>. P \<alpha> \<Longrightarrow> P \<beta> \<Longrightarrow> P \<gamma> \<Longrightarrow> P (formula.And \<alpha> (formula.Or \<beta> \<gamma>))) \<Longrightarrow>
(\<And>\<alpha> \<beta>. P \<alpha> \<Longrightarrow> P \<beta> \<Longrightarrow> P (formula.Exists (rewriteC (formula.And (Rewriting.shift \<alpha>) \<beta>)))) \<Longrightarrow>
(\<And>\<alpha> \<beta>. P \<alpha> \<Longrightarrow> P \<beta> \<Longrightarrow> P (formula.And \<alpha> (formula.Neg \<beta>))) \<Longrightarrow> (\<And>\<alpha>. P \<alpha>) \<Longrightarrow> P x" by simp

thm my_induct



lemma rewriteC_sat: "Formula.sat \<sigma> V v i (rewriteC \<alpha>) = Formula.sat \<sigma> V v i \<alpha>"
  apply(simp only: r_to_r)
  apply(induct \<alpha> arbitrary:  v rule: rewriteCo.induct)

    apply (subst rewriteCo.simps shiftI.simps)
    apply(simp only: Let_def  split: formula.splits if_splits )
    apply(simp only: sat_rewriteC_1 sat_rewriteC_4[symmetric] sat_rewriteC_5[symmetric])
  apply(auto)
  sorry
  
definition "rr_num \<alpha> = length (sorted_list_of_set (rr 0 \<alpha>))"  

lemma rr_num_g: "rr_num (rewriteC \<alpha>) > rr_num \<alpha>" sorry


lemma   rr_1:
  "rr_num (Formula.And \<alpha> (Formula.Or \<beta> \<gamma>)) > rr_num (Formula.Or (Formula.And \<alpha> \<beta>) (Formula.And \<alpha> \<gamma>))"
  sorry

lemma rr_4:
  "rr_num (Formula.And \<alpha> (Formula.Exists \<beta>)) >
                     (rr_num (Formula.Exists (Formula.And (shift \<alpha>) \<beta> )))"
  using sat_shift[of "[]"] sorry

lemma rr_5: "rr_num (Formula.And \<alpha> (Formula.Neg \<beta>))  >
                      rr_num (Formula.And \<alpha> (Formula.Neg (Formula.And \<alpha> \<beta>)))"
  sorry*)



(*
  apply (simp only: simp_thms formula.inject split_paired_All split formula.splits if_splits)
  find_theorems "(_ \<and> _ \<longleftrightarrow> _) = _"
  apply (intro allI impI conjI)
*)
(*
  using [[simp_trace_new mode=full]]
  using [[simproc del: let_simp]]
*)
 (* apply (simp del: rewriteC.simps sat.simps add: sat_rewriteC_1 
    split: formula.splits if_splits)
  apply (intro allI impI conjI)
   apply simp_all*)

 
  


function(sequential) rewriteC :: "Formula.formula \<Rightarrow> Formula.formula" where
(*1*)  "rewriteC (Formula.And \<alpha> (Formula.Or \<beta> \<gamma>)) = (let \<alpha>' = rewriteC \<alpha>;
                                                    \<beta>' = rewriteC \<beta>;
                                                    \<gamma>' = rewriteC \<gamma>
                                                 in if prop_cond \<alpha>' \<beta>' 
                                                    then Formula.Or (Formula.And \<alpha>' \<beta>') (Formula.And \<alpha>' \<gamma>')
                                                    else Formula.And \<alpha>' (Formula.Or \<beta>' \<gamma>'))"  (*Maybe also a disjunction with prop_cond a' g'*)  
(*4*)| "rewriteC (Formula.And \<alpha> (Formula.Exists \<beta>)) =(let \<alpha>' = rewriteC \<alpha>;
                                                    \<beta>' = rewriteC \<beta>
                                                in if prop_cond \<alpha>' \<beta>'  
                                                 then Formula.Exists (Formula.And (shift \<alpha>') \<beta>')  
                                                 else Formula.And \<alpha>' (Formula.Exists \<beta>'))"
(*(*21*)| "rewriteC (Formula.And \<alpha> (square_w I \<beta>)) =(let \<alpha>' = rewriteC \<alpha>;
                                                   \<beta>' = rewriteC \<beta>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (square_w I (Formula.And (diamond_b I \<alpha>') \<beta>'))
                                                 else Formula.And \<alpha>' (square_w I \<beta>'))"
(*2*)| "rewriteC (Formula.And \<alpha> (release \<beta> I \<gamma>)) =(let \<alpha>' = rewriteC \<alpha>;
                                                 \<beta>' = rewriteC \<beta>;
                                                 \<gamma>' = rewriteC \<gamma>
                                                in if prop_cond \<alpha>' \<beta>' 
                                                 then Formula.And \<alpha>' (release (Formula.And \<beta>' (diamond_b (init_int I) \<alpha>')) I (Formula.And \<gamma>' (diamond_b I \<alpha>'))) 
                                                 else Formula.And \<alpha>' (release \<beta>' I \<gamma>'))"
(*20*)| "rewriteC (Formula.And \<alpha> (square_b I \<beta>)) =(let \<alpha>' = rewriteC \<alpha>;
                                                   \<beta>' = rewriteC \<beta>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (square_b I (Formula.And (diamond_w I \<alpha>' ) \<beta>'))
                                                 else Formula.And \<alpha>' (square_b I \<beta>'))"
(*3*)| "rewriteC (Formula.And \<alpha> (trigger \<beta> I \<gamma>)) =(let \<alpha>' = rewriteC \<alpha>;
                                                 \<beta>' = rewriteC \<beta>;
                                                 \<gamma>' = rewriteC \<gamma>
                                                in if prop_cond \<alpha>' \<beta>'  
                                                 then Formula.And \<alpha>' (trigger (Formula.And \<beta>' (diamond_w (init_int I) \<alpha>')) I (Formula.And \<gamma>' (diamond_w I \<alpha>')))  
                                                 else Formula.And \<alpha>' (trigger \<beta>' I \<gamma>'))"*)
(*5*)| "rewriteC (Formula.And \<alpha> (Formula.Neg \<beta>)) =(let \<alpha>' = rewriteC \<alpha> 
                                                  in (case \<beta> of
                                                    Formula.Until (Formula.Neg \<beta>'') I (Formula.Neg \<gamma>'') \<Rightarrow>
                                                           (let \<beta>' = rewriteC \<beta>'';
                                                                \<gamma>' = rewriteC \<gamma>''
                                                            in if prop_cond \<alpha>' \<beta>' 
                                                                  then Formula.And \<alpha>' (release (Formula.And \<beta>' (diamond_b (init_int I) \<alpha>')) 
                                                                                                I 
                                                                                               (Formula.And \<gamma>' (diamond_b I \<alpha>'))) 
                                                                  else Formula.And \<alpha>' (release \<beta>' I \<gamma>'))
                                                    | _ \<Rightarrow> let \<beta>' = rewriteC \<beta>
                                                           in if prop_cond \<alpha>' \<beta>'  
                                                                then Formula.And \<alpha>' (Formula.Neg (Formula.And \<alpha>' \<beta>'))  
                                                                else Formula.And \<alpha>' (Formula.Neg \<beta>')))"


(*6*)| "rewriteC (Formula.Since (Formula.And \<alpha> \<gamma>) I \<beta> ) =(let \<alpha>' = rewriteC \<alpha>;
                                                        \<beta>' = rewriteC \<beta>;
                                                        \<gamma>' = rewriteC \<gamma>
                                                in if prop_cond \<alpha>' \<beta>' \<and> excl_zero I 
                                                 then Formula.Since (Formula.And \<alpha>' \<gamma>') I (Formula.And (diamond_w I \<alpha>') \<beta>')  
                                                 else Formula.Since (Formula.And \<alpha>' \<gamma>') I \<beta>' )"
(*7*)| "rewriteC (Formula.Until (Formula.And \<alpha> \<gamma>) I \<beta> ) =(let \<alpha>' = rewriteC \<alpha>;
                                                        \<beta>' = rewriteC \<beta>;
                                                        \<gamma>' = rewriteC \<gamma>
                                                in if prop_cond \<alpha>' \<beta>' \<and> excl_zero I 
                                                 then Formula.Until (Formula.And \<alpha>' \<gamma>') I (Formula.And (diamond_b I \<alpha>') \<beta>')
                                                 else Formula.Until (Formula.And \<alpha>' \<gamma>') I \<beta>')"
(*8*)(*| "rewriteC (Formula.Since \<beta> I (Formula.And \<alpha> \<gamma>)) =(let \<alpha>' = rewriteC \<alpha>;
                                                        \<beta>' = rewriteC \<beta>;
                                                        \<gamma>' = rewriteC \<gamma>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.Since (Formula.And (diamond_b (init_int I) \<alpha>') \<beta>') I (Formula.And \<alpha>' \<gamma>')
                                                 else Formula.Since \<beta>' I (Formula.And \<alpha>' \<gamma>') )"
(*9*)| "rewriteC (Formula.Until \<beta> I (Formula.And \<alpha> \<gamma>)) =(let \<alpha>' = rewriteC \<alpha>;
                                                        \<beta>' = rewriteC \<beta>;
                                                        \<gamma>' = rewriteC \<gamma>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.Until (Formula.And (diamond_w (init_int I) \<alpha>') \<beta>') I (Formula.And \<alpha>' \<gamma>')
                                                 else Formula.Until \<beta>' I (Formula.And \<alpha>' \<gamma>') )" *)
(*10*)| "rewriteC (Formula.And \<alpha> (Formula.Since \<beta> I \<gamma>)) =(let \<alpha>' = rewriteC \<alpha>;
                                                        \<beta>' = rewriteC \<beta>;
                                                        \<gamma>' = rewriteC \<gamma>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (Formula.Since (Formula.And (diamond_w (init_int I) \<alpha>') \<beta>') I \<gamma>')
                                                 else Formula.And \<alpha>' (Formula.Since \<beta>' I \<gamma>'))"
(*11*)| "rewriteC (Formula.And \<alpha> (Formula.Until \<beta> I \<gamma>)) =(let \<alpha>' = rewriteC \<alpha>;
                                                        \<beta>' = rewriteC \<beta>;
                                                        \<gamma>' = rewriteC \<gamma>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (Formula.Until (Formula.And (diamond_b (init_int I) \<alpha>') \<beta>') I \<gamma>')
                                                 else Formula.And \<alpha>' (Formula.Until \<beta>' I \<gamma>'))" 
(*12*)(*| "rewriteC (Formula.And \<alpha> (Formula.Since \<gamma> I \<beta>)) =(let \<alpha>' = rewriteC \<alpha>;
                                                        \<beta>' = rewriteC \<beta>;
                                                        \<gamma>' = rewriteC \<gamma>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (Formula.Since \<gamma>' I (Formula.And (diamond_w I \<alpha>') \<beta>'))
                                                 else Formula.And \<alpha>' (Formula.Since \<gamma>' I \<beta>'))"
(*13*)| "rewriteC (Formula.And \<alpha> (Formula.Until \<gamma> I \<beta>)) =(let \<alpha>' = rewriteC \<alpha>;
                                                        \<beta>' = rewriteC \<beta>;
                                                        \<gamma>' = rewriteC \<gamma>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (Formula.Until \<gamma>' I (Formula.And (diamond_b I \<alpha>') \<beta>'))
                                                 else Formula.And \<alpha>' (Formula.Until \<gamma>' I \<beta>'))"*)
(*18*)(*| "rewriteC (Formula.And \<alpha> (diamond_b I \<beta>)) =(let \<alpha>' = rewriteC \<alpha>;
                                     \<beta>' = rewriteC \<beta>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (diamond_b I (Formula.And (diamond_w I \<alpha>') \<beta>'))
                                                 else Formula.And \<alpha>' (diamond_b I \<beta>'))"*)   (*INSERT AGAIN*)
(*19*)(*| "rewriteC (Formula.And \<alpha> (diamond_w I \<beta>)) =(let \<alpha>' = rewriteC \<alpha>;
                                                   \<beta>' = rewriteC \<beta>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (diamond_w I (Formula.And (diamond_b I \<alpha>') \<beta>'))
                                                 else Formula.And \<alpha>' (diamond_w I \<beta>'))"  *) (*INSERT AGAIN*)

(*22*)| "rewriteC (Formula.And \<alpha> (Formula.Prev I \<beta>)) =(let \<alpha>' = rewriteC \<alpha>;
                                                      \<beta>' = rewriteC \<beta>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (Formula.Prev I (Formula.And (Formula.Next I \<alpha>') \<beta>'))
                                                 else Formula.And \<alpha>' (Formula.Prev I \<beta>'))"
(*23*)| "rewriteC (Formula.And \<alpha> (Formula.Next I \<beta>)) =(let \<alpha>' = rewriteC \<alpha>;
                                                   \<beta>' = rewriteC \<beta>
                                                in if prop_cond \<alpha>' \<beta>'
                                                 then Formula.And \<alpha>' (Formula.Next I (Formula.And (Formula.Prev I \<alpha>') \<beta>'))
                                                 else Formula.And \<alpha>' (Formula.Next I \<beta>'))"
| "rewriteC f = f "
  by pat_completeness auto
termination by lexicographic_order


(*fun_cases my_elim: "rewriteC \<alpha>"*)

thm formula.splits

lemma rewriteC_sat: "Formula.sat \<sigma> V v i (rewriteC \<alpha>) = Formula.sat \<sigma> V v i \<alpha>" 
proof(induction \<alpha> arbitrary: v i rule:rewriteC.induct)
  case (1 \<alpha> \<beta> \<gamma>) (*1*)
  then show ?case  by (simp del:sat.simps add:Let_def sat_rewriteC_1;auto)
next
  case (2 \<alpha> \<beta>)  (*4*)
  then show ?case by(simp only: rewriteC.simps shiftI.simps sat_rewriteC_4[symmetric] Let_def split:if_splits;simp) 
next
(*
  case (3)
  then show ?case by (simp only:rewriteC.simps Let_def sat_rewriteC_21[symmetric] split:if_splits;simp)
next
  case (4 \<alpha> \<beta> I \<gamma>) (*2*)
  then show ?case by (simp only:rewriteC.simps Let_def sat_rewriteC_2[symmetric] split:if_splits;simp)
next
  case (5) (*20*)
  then show ?case by (simp only:rewriteC.simps Let_def sat_rewriteC_20[symmetric] split:if_splits;simp)
next
  case (6 \<alpha> \<beta> I \<gamma>)
  then show ?case by (simp only:rewriteC.simps Let_def sat_rewriteC_3[symmetric] split:if_splits;simp)
next
  case (7 \<alpha> \<beta>)
  then show ?case by (simp add: Let_def sat_rewriteC_5;auto)
next
  case l:(8 \<alpha> \<gamma> I \<beta>) (*6*)
  then show ?case  
  proof(cases "excl_zero I")
    thm sat_rewriteC_6[symmetric]
    case True
    then show ?thesis using l by (simp only:rewriteC.simps Let_def sat_rewriteC_6[OF True,symmetric] split:if_splits;simp)
  next
    case False
    then show ?thesis using l by simp
  qed
next
  case l:(9 \<alpha> \<gamma> I \<beta>) (*7*)
  then show ?case
  proof(cases "excl_zero I")
    case True
    then show ?thesis using l by (simp only:rewriteC.simps Let_def sat_rewriteC_7[OF True,symmetric] split:if_splits;simp)
  next
    case False
    then show ?thesis using l by simp
  qed
next
(*next
  case (8 \<beta> I \<alpha> \<gamma>)
  then show ?case by (simp only:rewriteC8.simps Let_def sat_rewriteC_8[symmetric] split:if_splits;simp)
next
  case (9 \<beta> I \<alpha> \<gamma>)
  then show ?case by (simp only:rewriteC9.simps Let_def sat_rewriteC_9[symmetric] split:if_splits;simp)*)
next
  case (10 \<alpha> \<beta> I \<gamma>) (*10*)
  then show ?case by (simp only:rewriteC.simps Let_def sat_rewriteC_10[symmetric] split:if_splits;simp)
next
  case (11 \<beta> I \<alpha> \<gamma>) (*11*)
  then show ?case by (simp only:rewriteC.simps Let_def sat_rewriteC_11[symmetric] split:if_splits;simp)
(*next
  case (12)
  then show ?case by (simp only:rewriteC12.simps Let_def sat_rewriteC_12[symmetric] split:if_splits;simp)
next
  case (13)
  then show ?case by (simp only:rewriteC13.simps Let_def sat_rewriteC_13[symmetric] split:if_splits;simp)
next
  case (18)
  then show ?case by (simp only:rewriteC18.simps Let_def sat_rewriteC_18[symmetric] split:if_splits;simp)
next
  case (19)
  then show ?case by (simp only:rewriteC19.simps Let_def sat_rewriteC_19[symmetric] split:if_splits;simp)
next
  case (20)
  then show ?case by (simp only:rewriteC20.simps Let_def sat_rewriteC_20[symmetric] split:if_splits;simp)
next
  case (21)
  then show ?case by (simp only:rewriteC21.simps Let_def sat_rewriteC_21[symmetric] split:if_splits;simp)*)
next
  case (12) (*22*)
  then show ?case by (simp only:rewriteC.simps Let_def sat_rewriteC_22[symmetric] split:if_splits ;simp split:nat.splits)
next
  case (13) (*23*)
  then show ?case by (simp only:rewriteC.simps Let_def sat_rewriteC_23[symmetric] split:if_splits;simp)
*)
qed auto



(*5*)| "rewriteC (Formula.And \<alpha> (Formula.Neg \<beta>)) =(let \<alpha>' = rewriteC \<alpha>;
                                                      \<beta>' = rewriteC \<beta>
                                                in if prop_cond \<alpha>' \<beta>'  
                                                 then Formula.And \<alpha>' (Formula.Neg (Formula.And \<alpha>' \<beta>'))  
                                                 else Formula.And \<alpha>' (Formula.Neg \<beta>'))"





end
