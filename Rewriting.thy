theory Rewriting                  
    imports "MFODL_Monitor_Optimized.Formula" "MFODL_Monitor_Optimized.Regex" "MFODL_Monitor_Optimized.Trace"
begin

datatype (discs_sels) tformula = 
    TPred Formula.name "Formula.trm list"
  | TLet Formula.name nat tformula tformula
  | TEq Formula.trm Formula.trm 
  | TLess Formula.trm Formula.trm 
  | TLessEq Formula.trm Formula.trm
  | TNeg tformula 
  | TOr tformula tformula 
  | TAnd tformula tformula 
  | TAnds "tformula list"
  | TExists tformula
  | TAgg nat Formula.agg_op nat Formula.trm tformula
  | TPrev \<I> tformula 
  | TNext \<I> tformula
  | TSince tformula \<I> tformula 
  | TUntil tformula \<I> tformula
  | TDiamondB \<I> tformula 
  | TSquareB \<I> tformula
  | TDiamondW \<I> tformula 
  | TSquareW \<I> tformula
  | TMatchF \<I> "tformula Regex.regex" 
  | TMatchP \<I> "tformula Regex.regex"

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

fun embed1 :: "Formula.formula \<Rightarrow> tformula" where
 "embed1 (Formula.Ands \<phi>s) = TAnds (map embed1 \<phi>s)"
| "embed1 (Formula.MatchF I r) = TMatchF I (regex.map_regex embed1 r)"
| "embed1 (Formula.MatchP I r) = TMatchP I (regex.map_regex embed1 r)"

|  "embed1 (Formula.Pred r ts) = TPred r ts"
| "embed1 (Formula.Let p b \<phi> \<psi>) = TLet p b (embed1 \<phi>) (embed1 \<psi>)"
| "embed1 (Formula.Eq t1 t2) = TEq t1 t2"
| "embed1 (Formula.Less t1 t2) = TLess t1 t2"
| "embed1 (Formula.LessEq t1 t2) = TLessEq t1 t2"

| "embed1 (Formula.Neg (Formula.Since \<phi> I (Formula.Neg \<psi>))) = (if \<phi> = TT then 
    TSquareB I (embed1 \<psi>) else TNeg (TSince (embed1 \<phi>) I (TNeg (embed1 \<psi>))))"
| "embed1 (Formula.Neg (Formula.Until \<phi> I (Formula.Neg \<psi>))) =  (if \<phi> = TT then 
    TSquareW I (embed1 \<psi>) else TNeg (TUntil (embed1 \<phi>) I (TNeg (embed1 \<psi>))))"

| "embed1 (Formula.Neg \<phi>) = TNeg (embed1 \<phi>)"

| "embed1 (Formula.Or \<phi> \<psi>) = TOr (embed1 \<phi>) (embed1 \<psi>)"
| "embed1 (Formula.And \<phi> \<psi>) = TAnd (embed1 \<phi>) (embed1 \<psi>)"

| "embed1 (Formula.Exists \<phi>) = TExists (embed1 \<phi>)"
| "embed1 (Formula.Agg y \<omega> b' f \<phi>) = TAgg y \<omega> b' f (embed1 \<phi>)"
| "embed1 (Formula.Prev I \<phi>) = TPrev I (embed1 \<phi>)"
| "embed1 (Formula.Next I \<phi>) = TNext I (embed1 \<phi>)"

| "embed1 (Formula.Since \<phi> I \<psi>) = (if \<phi> = TT then TDiamondB I (embed1 \<psi>)
                                             else TSince (embed1 \<phi>) I (embed1 \<psi>))"

| "embed1 (Formula.Until \<phi> I \<psi>) = (if \<phi> = TT then TDiamondW I (embed1 \<psi>)
                                             else TUntil (embed1 \<phi>) I (embed1 \<psi>))"


fun embed2 where
  "embed2 (TAnds \<phi>s) = RAnds (map embed2 \<phi>s)"
| "embed2 (TMatchF I r) = RMatchF I (regex.map_regex embed2 r)"
| "embed2 (TMatchP I r) = RMatchP I (regex.map_regex embed2 r)"
| "embed2 (TNeg (TSince (TNeg \<phi>) I (TNeg \<psi>))) =  RTrigger (embed2 \<phi>) I (embed2  \<psi>)"
| "embed2 (TNeg (TUntil (TNeg \<phi>) I (TNeg \<psi>))) =   RRelease (embed2 \<phi>) I (embed2 \<psi>)"
| "embed2 (TPred r ts) = RPred r ts"
| "embed2 (TLet p b \<phi> \<psi>) = RLet p b (embed2 \<phi>) (embed2 \<psi>)"
| "embed2 (TEq t1 t2) = REq t1 t2"
| "embed2 (TLess t1 t2) = RLess t1 t2"
| "embed2 (TLessEq t1 t2) = RLessEq t1 t2"
| "embed2 (TNeg \<phi>) = RNeg (embed2 \<phi>)"

| "embed2 (TOr \<phi> \<psi>) = ROr (embed2 \<phi>) (embed2 \<psi>)"
| "embed2 (TAnd \<phi> \<psi>) = RAnd (embed2 \<phi>) (embed2 \<psi>)"

| "embed2 (TExists \<phi>) = RExists (embed2 \<phi>)"
| "embed2 (TAgg y \<omega> b' f \<phi>) = RAgg y \<omega> b' f (embed2 \<phi>)"
| "embed2 (TPrev I \<phi>) = RPrev I (embed2 \<phi>)"
| "embed2 (TNext I \<phi>) = RNext I (embed2 \<phi>)"

| "embed2 (TSince \<phi> I \<psi>) = RSince (embed2 \<phi>) I (embed2 \<psi>)"

| "embed2 (TUntil \<phi> I \<psi>) =  RUntil (embed2 \<phi>) I (embed2 \<psi>)"

| "embed2 (TDiamondW I a) = RDiamondW I (embed2 a) "
| "embed2 (TDiamondB I a) = RDiamondB I (embed2 a) "
| "embed2 (TSquareW I a) = RSquareW I (embed2 a) "
| "embed2 (TSquareB I a) = RSquareB I (embed2 a) "



fun project2 where
 "project2  (RTrigger \<phi> I \<psi>) =  TNeg (TSince (TNeg (project2 \<phi>)) I (TNeg (project2 \<psi>)))"
| "project2 (RRelease  \<phi> I \<psi>) =  TNeg (TUntil (TNeg (project2 \<phi>)) I (TNeg (project2 \<psi>)))  "
|  "project2 (RPred r ts) = TPred r ts"
| "project2 (RLet p b \<phi> \<psi>) = TLet p b (project2 \<phi>) (project2 \<psi>)"
| "project2 (REq t1 t2) = TEq t1 t2"
| "project2 (RLess t1 t2) = TLess t1 t2"
| "project2 (RLessEq t1 t2) = TLessEq t1 t2"
| "project2 (RNeg \<phi>) = TNeg (project2 \<phi>)"

| "project2 (ROr \<phi> \<psi>) = TOr (project2 \<phi>) (project2 \<psi>)"
| "project2 (RAnd \<phi> \<psi>) = TAnd (project2 \<phi>) (project2 \<psi>)"
| "project2 (RAnds \<phi>s) = TAnds (map project2 \<phi>s)"

| "project2 (RExists \<phi>) = TExists (project2 \<phi>)"
| "project2 (RAgg y \<omega> b' f \<phi>) = TAgg y \<omega> b' f (project2 \<phi>)"
| "project2 (RPrev I \<phi>) = TPrev I (project2 \<phi>)"
| "project2 (RNext I \<phi>) = TNext I (project2 \<phi>)"

| "project2 (RSince \<phi> I \<psi>) = TSince (project2 \<phi>) I (project2 \<psi>)"

| "project2 (RUntil \<phi> I \<psi>) =  TUntil (project2 \<phi>) I (project2 \<psi>)"

| "project2 (RMatchF I r) = TMatchF I (regex.map_regex project2 r)"
| "project2 (RMatchP I r) = TMatchP I (regex.map_regex project2 r)"
| "project2 (RDiamondW I a) = TDiamondW I (project2 a) "
| "project2 (RDiamondB I a) = TDiamondB I (project2 a) "
| "project2 (RSquareW I a) = TSquareW I (project2 a) "
| "project2 (RSquareB I a) = TSquareB I (project2 a) "

fun project1 :: "tformula \<Rightarrow> Formula.formula" where
  "project1 (TPred r ts)  = Formula.Pred r ts"
| "project1 (TLet p b \<phi> \<psi>) =  Formula.Let p b (project1 \<phi>) (project1 \<psi>)"
| "project1 (TEq t1 t2) =Formula.Eq t1 t2"
| "project1 (TLess t1 t2) =Formula.Less t1 t2"
| "project1 (TLessEq t1 t2) =Formula.LessEq t1 t2"

| "project1 (TSquareB I \<psi>) = Formula.Neg (Formula.Since TT I (Formula.Neg (project1 \<psi>)))"

| "project1 (TSquareW I \<psi>) = Formula.Neg (Formula.Until TT I (Formula.Neg (project1 \<psi>)))"

| "project1 (TNeg \<phi>) = Formula.Neg (project1 \<phi>)"
| "project1 (TOr \<phi> \<psi>) = Formula.Or (project1 \<phi>) (project1 \<psi>)"
| "project1 (TAnd \<phi> \<psi>) = Formula.And (project1 \<phi>) (project1 \<psi>)"
| "project1 (TAnds \<phi>s) = Formula.Ands (map project1 \<phi>s)"

| "project1 (TExists \<phi>) = Formula.Exists (project1 \<phi>)"
| "project1 (TAgg y \<omega> b' f \<phi>) = Formula.Agg y \<omega> b' f (project1 \<phi>)"
| "project1 (TPrev I \<phi>) = Formula.Prev I (project1 \<phi>)"
| "project1 (TNext I \<phi>) = Formula.Next I (project1 \<phi>)"
| "project1 (TDiamondB I \<phi>) = Formula.Since TT I (project1 \<phi>)"
| "project1 (TSince \<phi> I \<psi>) = Formula.Since (project1 \<phi>) I (project1 \<psi>)"

| "project1 (TDiamondW I \<phi>) = Formula.Until TT I (project1 \<phi>)"
| "project1 (TUntil \<phi> I \<psi>) = Formula.Until (project1 \<phi>) I (project1 \<psi>)"

| "project1 (TMatchF I r) = Formula.MatchF I (regex.map_regex project1 r)"
| "project1 (TMatchP I r) = Formula.MatchP I (regex.map_regex project1 r)"




lemma project_embed1: "(project1 \<circ> embed1) f = f" 
proof(induction f rule:embed1.induct)
case (1 \<phi>s)
then show ?case sorry
next
  case (2 I r)
  then show ?case by (induction r;auto)
next
  case (3 I r)
  then show ?case by (induction r;auto)
qed auto

definition embed where
 "embed f = embed2 (embed1 f)"

definition project where
 "project f = project1 (project2 f)"


lemma project_embed2: "project2 (embed2 r) = r"
proof(induction r rule:embed2.induct)
  case (1 \<phi>s)
  then show ?case sorry
next
  case (2 I r)
  then show ?case by (induction r;auto)
next
  case (3 I r)
  then show ?case by (induction r;auto)
qed auto


lemma project_embed: "project (embed f) = f"
  using Rewriting.embed_def project_def project_embed1 project_embed2 by auto

definition rsat where "rsat \<sigma> V v i \<phi> = Formula.sat \<sigma> V v i (project \<phi>)"


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


(*primrec rr_regex where
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
       in  (rr1 \<inter> (fv2-rr2)) \<noteq> {})"*)


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


primrec rr :: "nat \<Rightarrow> rformula \<Rightarrow> nat set" where
  "rr b (RPred r ts) = (\<Union>t\<in>set ts. Formula.fvi_trm b t)"
| "rr b (RLet p _ \<phi> \<psi>) = rr b \<psi>"
| "rr  b(REq t1 t2) = (case (t1,t2) of
                             (Formula.Var x,Formula.Const _) \<Rightarrow> {x-b}
                            |(Formula.Const _,Formula.Var x) \<Rightarrow> {x-b}
                            | _ \<Rightarrow> {})"

| "rr b (RLess t1 t2) = (case (t1,t2) of
                        (Formula.Var x,Formula.Const _) \<Rightarrow> {x-b}
                        |_ \<Rightarrow> {})"
| "rr b (RLessEq t1 t2) = (case (t1,t2) of
                                              (Formula.Var x,Formula.Const _) \<Rightarrow> {x-b}
                                             |_ \<Rightarrow> {})"
| "rr b (ROr \<phi> \<psi>) =  (rr b \<phi>) \<inter> (rr b \<psi>)"
| "rr b (RAnd \<phi> \<psi>) = rr b \<psi> \<union> (rr b \<phi>)"
| "rr b (RAnds \<phi>s) = (let xs = map (rr b) \<phi>s in \<Union>x\<in>set xs. x)"
| "rr b (RExists \<phi>) = (if (0 \<in> (rr 0 \<phi>)) then rr (Suc b) \<phi>
                                            else {})"
| "rr b (RAgg y \<omega> b' f \<phi>) = rr b \<phi>" (*How?*)
| "rr b (RPrev I \<phi>) = rr b \<phi>"
| "rr b (RNext I \<phi>) = rr b \<phi>"
| "rr b (RSince \<phi> I \<psi>) = rr b \<psi>"
| "rr b (RUntil \<phi> I \<psi>) = rr b \<psi>"
| "rr b (RRelease \<phi> I \<psi>) = rr b \<psi>"
| "rr b (RTrigger \<phi> I \<psi>) = rr b \<psi>"
| "rr b (RMatchF I r) = {}"
| "rr b (RMatchP I r) = {}"
| "rr b (RNeg \<alpha>) = {}"
| "rr b (RDiamondW I \<alpha>) = {}"
| "rr b (RDiamondB I \<alpha>) = {}"
| "rr b (RSquareW I \<alpha>) = {}"
| "rr b (RSquareB I \<alpha>) = {}"


(*fun fvi_r :: "nat \<Rightarrow> rformula \<Rightarrow> nat set" where
  "fvi_r b (RPred r ts) = (\<Union>t\<in>set ts. Formula.fvi_trm b t)"
| "fvi_r b (RLet p _ \<phi> \<psi>) = fvi_r b \<psi>"
| "fvi_r b (REq t1 t2) = Formula.fvi_trm b t1 \<union> Formula.fvi_trm b t2"
| "fvi_r b (RLess t1 t2) = Formula.fvi_trm b t1 \<union> Formula.fvi_trm b t2"
| "fvi_r b (RLessEq t1 t2) = Formula.fvi_trm b t1 \<union> Formula.fvi_trm b t2"
| "fvi_r b (RNeg \<phi>) = fvi_r b \<phi>"
| "fvi_r b (ROr \<phi> \<psi>) = fvi_r b \<phi> \<union> fvi_r b \<psi>"
| "fvi_r b (RAnd \<phi> \<psi>) = fvi_r b \<phi> \<union> fvi_r b \<psi>"
| "fvi_r b (RAnds \<phi>s) = (let xs = map (fvi_r b) \<phi>s in \<Union>x\<in>set xs. x)"
| "fvi_r b (RExists \<phi>) = fvi_r (Suc b) \<phi>"
| "fvi_r b (RAgg y \<omega> b' f \<phi>) = fvi_r (b + b') \<phi> \<union> Formula.fvi_trm (b + b') f \<union> (if b \<le> y then {y - b} else {})"
| "fvi_r b (RPrev I \<phi>) = fvi_r b \<phi>"
| "fvi_r b (RNext I \<phi>) = fvi_r b \<phi>"
| "fvi_r b (RSince \<phi> I \<psi>) = fvi_r b \<phi> \<union> fvi_r b \<psi>"
| "fvi_r b (RUntil \<phi> I \<psi>) = fvi_r b \<phi> \<union> fvi_r b \<psi>"
| "fvi_r b (RMatchF I r) = Regex.fv_regex (fvi_r b) r"
| "fvi_r b (RMatchP I r) = Regex.fv_regex (fvi_r b) r"
| "fvi_r b (RRelease l I r) = fvi_r b l \<inter> fvi_r b r"
| "fvi_r b (RTrigger l I r) = fvi_r b l \<inter> fvi_r b r"
| "fvi_r b (RDiamondB I r) = fvi_r b r"
| "fvi_r b (RDiamondW I r) = fvi_r b r"
| "fvi_r b (RSquareB I r) = fvi_r b r"
| "fvi_r b (RSquareW I r) = fvi_r b r"*)

(*| "fvi_l b (Formula.MatchF I r) = fv_l_regex (fvi_l b) r"
| "fvi_l b (Formula.MatchP I r) = fv_l_regex (fvi_l b) r"*)

definition fvi_r where
      "fvi_r b r = Formula.fvi b (project r)"


definition prop_cond :: "rformula \<Rightarrow> rformula \<Rightarrow> bool"where
 "prop_cond f1 f2 =
       (let rr1 = rr 0 f1;
            rr2 = rr 0 f2; 
            fv2 = fvi_r 0 f2
        in (rr1 \<inter> (fv2-rr2))\<noteq> {})"

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

(*primrec shiftI_r :: "nat \<Rightarrow> rformula \<Rightarrow> rformula" where
  "shiftI_r k (RPred r ts) = RPred r (map (shiftTI k) ts)"
| "shiftI_r k (RExists a) = RExists (shiftI_r (Suc k) a)"
| "shiftI_r k (RLet nm n a b) = RLet nm n a (shiftI_r k b)" (*fixed error, a is not shifted*)
| "shiftI_r k (REq t1 t2) = REq (shiftTI k t1) (shiftTI k t2)"
| "shiftI_r k (RLess t1 t2) =  RLess (shiftTI k t1) (shiftTI k t2)"
| "shiftI_r k (RLessEq t1 t2) = RLessEq (shiftTI k t1) (shiftTI k t2)"
| "shiftI_r k (RNeg a) = RNeg (shiftI_r k a)"
| "shiftI_r k (ROr a b) = ROr (shiftI_r k a) (shiftI_r k b)"
| "shiftI_r k (RAnd a b) = RAnd (shiftI_r k a) (shiftI_r k b)"
| "shiftI_r k (RAnds as) = RAnds (map (shiftI_r k) as)"  
| "shiftI_r k (RAgg y op b t a) = RAgg (if y < k then y else y + 1)
                                            op b (shiftTI (k + b) t) (shiftI_r (k + b) a)"
| "shiftI_r k (RPrev \<I> a) = RPrev \<I> (shiftI_r k a)"
| "shiftI_r k (RNext \<I> a) = RNext \<I> (shiftI_r k a)"
| "shiftI_r k (RSince a1 \<I> a2) = RSince (shiftI_r k a1) \<I> (shiftI_r k a2)"
| "shiftI_r k (RUntil a1 \<I> a2) = RUntil (shiftI_r k a1) \<I> (shiftI_r k a2)"
| "shiftI_r k (RMatchF \<I> r) = RMatchF \<I> (Regex.map_regex (shiftI_r k) r)"
| "shiftI_r k (RMatchP \<I> r) = RMatchP \<I> (Regex.map_regex (shiftI_r k) r)"
| "shiftI_r k (RRelease \<phi> I \<psi>) = RRelease (shiftI_r k \<phi>) I (shiftI_r k \<psi>)"
| "shiftI_r k (RTrigger \<phi> I \<psi>) = RTrigger (shiftI_r k \<phi>) I (shiftI_r k \<psi>)"
| "shiftI_r k (RDiamondB I \<psi>) = RDiamondB I (shiftI_r k \<psi>)"
| "shiftI_r k (RDiamondW I \<psi>) = RDiamondW I (shiftI_r k \<psi>)"
| "shiftI_r k (RSquareB I \<psi>) = RSquareB I (shiftI_r k \<psi>)"
| "shiftI_r k (RSquareW I \<psi>) = RSquareW I (shiftI_r k \<psi>)"*)



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

definition shiftI_r where
"shiftI_r b r = embed (shiftI b (project r))"



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



(*lemma   sat_rewriteC_1_e:
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
                                       rsat \<sigma> V v i (RAnd \<alpha> (RNext I (RAnd (RPrev I \<alpha>) \<beta>)))"sorry*)

  

abbreviation finite_int where "finite_int I \<equiv> (right I) \<noteq> \<infinity>"


datatype argpos = Same | Swapped

fun size_argpos :: "argpos \<Rightarrow> nat"where
"size_argpos Same = 1"
| "size_argpos Swapped = 0"


primrec my_size_regex where
  "my_size_regex fun (Regex.Skip n) = 0"
| "my_size_regex fun (Regex.Test \<phi>) = fun \<phi>"
| "my_size_regex fun (Regex.Plus r s) = my_size_regex fun r + my_size_regex fun s"
| "my_size_regex fun (Regex.Times r s) = my_size_regex fun r + my_size_regex fun s"
| "my_size_regex fun (Regex.Star r) = my_size_regex fun r"

lemma my_size_regex_cong[fundef_cong]:
  "r = r' \<Longrightarrow> (\<And>z. z \<in> Regex.atms r \<Longrightarrow> fun z = fun' z) \<Longrightarrow> my_size_regex fun r = my_size_regex fun' r'"
  by (induct r arbitrary: r') auto


primrec my_map_regex where
  "my_map_regex fun (Regex.Skip n) = Regex.Skip n"
| "my_map_regex fun (Regex.Test \<phi>) = Regex.Test (fun \<phi>)"
| "my_map_regex fun (Regex.Plus r s) = Regex.Plus (my_map_regex fun r) (my_map_regex fun s)"
| "my_map_regex fun (Regex.Times r s) = Regex.Times (my_map_regex fun r) (my_map_regex fun s)"
| "my_map_regex fun (Regex.Star r) = Regex.Star (my_map_regex fun r)"

lemma my_map_regex_cong[fundef_cong]:
  "r = r'  \<Longrightarrow> (\<And>z. z \<in> Regex.atms r \<Longrightarrow> fun z = fun' z) \<Longrightarrow> my_map_regex fun r = my_map_regex fun' r'"
  sorry


fun my_size_list where
 "my_size_list fun (f#fs) = fun f + my_size_list fun fs" 
| "my_size_list fun [] = 0"

lemma my_size_list_cong[fundef_cong]:
  "fs = fs' \<Longrightarrow> (\<And>z. z \<in> set fs \<Longrightarrow> fun z = fun' z) \<Longrightarrow> my_size_list fun fs = my_size_list fun' fs'" 
  by (induct fs arbitrary: fs') auto

fun my_size :: "rformula \<Rightarrow> nat" where
  "my_size (RPred r ts) = 1"
| "my_size (RLet p _ \<phi> \<psi>) = 1"
| "my_size  (REq t1 t2) = 1"

| "my_size (RLess t1 t2) = 1"
| "my_size (RLessEq t1 t2) = 1"
| "my_size (ROr \<phi> \<psi>) =  1 + (my_size \<phi>) + (my_size \<psi>)"
| "my_size (RAnd \<phi> \<psi>) = 1 + (my_size \<phi>) + (my_size \<psi>)"
| "my_size (RAnds \<phi>s) = 1+ my_size_list my_size \<phi>s"

| "my_size (RExists \<phi>) = 1 + my_size \<phi>"
| "my_size (RAgg y \<omega> b' f \<phi>) = 1 + (my_size \<phi>)"
| "my_size (RPrev I \<phi>) = 1+ my_size \<phi>"
| "my_size (RNext I \<phi>) = 1+ my_size \<phi>"
| "my_size (RSince \<phi> I \<psi>) = 1+ (my_size \<phi>) + (my_size \<psi>)"
| "my_size (RUntil \<phi> I \<psi>) =  1+ (my_size \<phi>) + (my_size \<psi>)"
| "my_size (RRelease \<phi> I \<psi>) = 1+ (my_size \<phi>) + (my_size \<psi>)"
| "my_size (RTrigger \<phi> I \<psi>) =  1+ (my_size \<phi>) + (my_size \<psi>)"
| "my_size (RMatchF I r) = 1 + (my_size_regex my_size r)"
| "my_size (RMatchP I r) = 1 + (my_size_regex my_size r)"
| "my_size (RNeg \<alpha>) = 1 + my_size \<alpha>"
| "my_size (RDiamondW I \<alpha>) = 1 + my_size \<alpha>"
| "my_size (RDiamondB I \<alpha>) =1 + my_size \<alpha>"
| "my_size (RSquareW I \<alpha>) =1 + my_size \<alpha>"
| "my_size (RSquareB I \<alpha>) = 1 + my_size \<alpha>"


lemma shift_size: "my_size (shiftI_r 0 \<alpha>) = my_size \<alpha>" sorry

lemma not_zero: "my_size \<alpha> > 0" by (induction \<alpha>;auto)



lemma rewrite1_conj[fundef_cong]: "(\<And>x. f x = g x) \<Longrightarrow> rewrite1 f \<alpha> = rewrite1 g \<alpha>" by presburger

lemma project_cong[fundef_cong]: "f1 = f2 \<Longrightarrow> project f1 = project f2" by auto  





function(sequential) rewrite where
(*1*)  "rewrite (RAnd \<alpha> (ROr \<beta> \<gamma>)) t =
       (if prop_cond \<alpha> \<beta> \<and> prop_cond \<alpha> \<gamma>
       then ROr (rewrite (RAnd \<alpha> \<beta>) Same) (rewrite (RAnd \<alpha> \<gamma>) Same)
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same;  \<gamma>' = rewrite \<gamma> Same in RAnd \<alpha>' (ROr \<beta>' \<gamma>'))" (*added prop_cond gamma because the rewrite shouldn't be position dependent*)

(*2*) | "rewrite (RAnd \<alpha> (RRelease \<beta> I \<gamma>)) t =
      (if prop_cond \<alpha> \<beta>
       then RAnd (rewrite \<alpha> Same) (RRelease (rewrite (RAnd \<beta> (RDiamondB (init_int I) \<alpha>)) Same) I (rewrite (RAnd \<gamma> (RDiamondB I \<alpha>)) Same))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same;  \<gamma>' = rewrite \<gamma> Same in (RAnd \<alpha>' (RRelease \<beta>' I \<gamma>')))"

(*3*) | "rewrite (RAnd \<alpha> (RTrigger \<beta> I \<gamma>)) t =
      (if prop_cond \<alpha> \<beta>
       then RAnd (rewrite \<alpha> Same) (RTrigger (rewrite (RAnd \<beta> (RDiamondW (init_int I) \<alpha>)) Same) I (rewrite (RAnd \<gamma> (RDiamondW I \<alpha>)) Same))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same;  \<gamma>' = rewrite \<gamma> Same in (RAnd \<alpha>' (RTrigger \<beta>' I \<gamma>')))"

(*4*) | "rewrite (RAnd \<alpha> (RExists \<beta>)) t = 
       (if prop_cond \<alpha> \<beta>  
        then RExists (rewrite (RAnd (shiftI_r 0 \<alpha>) \<beta>) Same)
        else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same in RAnd \<alpha>' (RExists \<beta>'))"

(*5*) | "rewrite (RAnd \<alpha> (RNeg \<beta>)) t =
      (if prop_cond \<alpha> \<beta>  
       then RAnd (rewrite \<alpha> Same) ((RNeg (rewrite (RAnd \<alpha> \<beta>) Same)))  
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same in RAnd \<alpha>' (RNeg \<beta>'))"

(*10,12*) | "rewrite (RAnd \<alpha> (RSince \<beta> I \<gamma>)) t =
      (if (prop_cond \<alpha> \<beta>) \<and> (finite_int I) then RAnd (rewrite \<alpha> Same) (RSince (rewrite (RAnd (RDiamondW (init_int I) \<alpha>) \<beta>) Same) I (rewrite \<gamma> Same))
       else if (prop_cond \<alpha> \<gamma>) \<and> (finite_int I) then RAnd (rewrite \<alpha> Same) (RSince (rewrite \<beta> Same) I (rewrite (RAnd (RDiamondW I \<alpha>) \<gamma>) Same))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same;  \<gamma>' = rewrite \<gamma> Same in RAnd \<alpha>' (RSince \<beta>' I \<gamma>'))"

(*11,13*) | "rewrite (RAnd \<alpha> (RUntil \<beta> I \<gamma>)) t =
      (if (prop_cond \<alpha> \<beta>) \<and> (finite_int I) then RAnd (rewrite \<alpha> Same) (RUntil (rewrite (RAnd (RDiamondB (init_int I) \<alpha>) \<beta>) Same) I (rewrite \<gamma> Same))
       else if (prop_cond \<alpha> \<gamma>) \<and> (finite_int I) then RAnd (rewrite \<alpha> Same) (RUntil (rewrite \<beta> Same) I (rewrite (RAnd (RDiamondB I \<alpha>) \<gamma>) Same))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same;  \<gamma>' = rewrite \<gamma> Same in RAnd \<alpha>' (RUntil \<beta>' I \<gamma>'))"

(*18*) | "rewrite (RAnd \<alpha> (RDiamondB I \<beta>)) t =
      (if (prop_cond \<alpha> \<beta>) \<and> (finite_int I)
       then RAnd (rewrite \<alpha> Same) (RDiamondB I (RAnd (RDiamondW I (rewrite \<alpha> Same)) (rewrite \<beta> Same)))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same in RAnd \<alpha>' (RDiamondB I \<beta>'))"

(*19*) | "rewrite (RAnd \<alpha> (RDiamondW I \<beta>)) t =
      (if (prop_cond \<alpha> \<beta>)
       then RAnd (rewrite \<alpha> Same) (RDiamondW I (RAnd (RDiamondB I (rewrite \<alpha> Same)) (rewrite \<beta> Same)))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same in RAnd \<alpha>' (RDiamondW I \<beta>'))"

 (*20*) | "rewrite (RAnd \<alpha> (RSquareB I \<beta>)) t =
      (if (prop_cond \<alpha> \<beta>) \<and> (finite_int I)
       then RAnd (rewrite \<alpha> Same) (RSquareB I (RAnd (RDiamondW I (rewrite \<alpha> Same)) (rewrite \<beta> Same)))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same in RAnd \<alpha>' (RSquareB I \<beta>'))" (*some of these rules don't rewrite the conjunction, of diamond/square, because it doesn't increase rr of the conjunction more than recursing the leaves*)

 (*21*) | "rewrite (RAnd \<alpha> (RSquareW I \<beta>)) t =
      (if (prop_cond \<alpha> \<beta>)
       then RAnd (rewrite \<alpha> Same) (RSquareW I (RAnd (RDiamondB I (rewrite \<alpha> Same)) (rewrite \<beta> Same)))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same in RAnd \<alpha>' (RSquareW I \<beta>'))"

 (*22*) | "rewrite (RAnd \<alpha> (RPrev I \<beta>)) t =
      (if (prop_cond \<alpha> \<beta>)
       then RAnd (rewrite \<alpha> Same) (RPrev I (RAnd (RNext I (rewrite \<alpha> Same)) (rewrite \<beta> Same)))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same in RAnd \<alpha>' (RPrev I \<beta>'))"

(*23*) | "rewrite (RAnd \<alpha> (RNext I \<beta>)) t =
      (if (prop_cond \<alpha> \<beta>)
       then RAnd (rewrite \<alpha> Same) (RNext I (RAnd (RPrev I (rewrite \<alpha> Same)) (rewrite \<beta> Same)))
       else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same in (RAnd \<alpha>' (RNext I \<beta>')))"


(*6,8*)| "rewrite (RSince (RAnd \<alpha> \<gamma>) I \<beta>) t =  (if (prop_cond \<alpha> \<beta>) \<and> (finite_int I)
                               then RSince (rewrite (RAnd \<alpha> \<gamma>) Same) I (rewrite (RAnd (RDiamondW I \<alpha>) \<beta>) Same)
                               else if (prop_cond \<alpha> \<gamma>) \<and> (finite_int I) then RSince (rewrite (RAnd \<alpha> \<gamma>) Same) I (rewrite (RAnd (RDiamondW I \<gamma>) \<beta>) Same)
                               else let \<alpha>' = rewrite \<alpha> Same ; \<beta>' = rewrite \<beta> Same ;  \<gamma>' = rewrite \<gamma> Same  in RSince (RAnd \<alpha>' \<gamma>') I \<beta>')"


(*7,9*) | "rewrite (RUntil (RAnd \<alpha> \<gamma>) I \<beta>) Same = (if (prop_cond \<alpha> \<beta>)
                                  then RUntil (rewrite (RAnd \<alpha> \<gamma>) Same) I (rewrite (RAnd (RDiamondB I \<alpha>) \<beta>) Same )
                                  else if (prop_cond \<alpha> \<gamma>) then RUntil (rewrite (RAnd \<alpha> \<gamma>) Same) I (rewrite (RAnd (RDiamondB I \<gamma>) \<beta>) Same) 
                                else let \<alpha>' = rewrite \<alpha> Same ; \<beta>' = rewrite \<beta> Same ;  \<gamma>' = rewrite \<gamma> Same  in RUntil (RAnd \<alpha>' \<gamma>') I \<beta>')"
| "rewrite (RUntil (RAnd \<alpha> \<gamma>) I \<beta>) Swapped =(if (prop_cond \<alpha> \<beta>)
                                then RUntil (rewrite (RAnd (RDiamondW I \<alpha>) \<beta>) Same ) I (rewrite (RAnd \<alpha> \<gamma>) Same )
                                else let \<alpha>' = rewrite \<alpha> Same; \<beta>' = rewrite \<beta> Same ;  \<gamma>' = rewrite \<gamma> Same in RUntil \<beta>' I (RAnd \<alpha>' \<gamma>'))"
| "rewrite (RSince l I r) Same = rewrite (RSince r I l) Swapped"
| "rewrite (RUntil l I r) Same = rewrite (RUntil r I l) Swapped"
| "rewrite (RAnd l r) Same = rewrite (RAnd r l) Swapped"

| "rewrite (RSince l I r) Swapped = RSince (rewrite r Same) I (rewrite l Same)" (*swap back before recursing on subformulas*)
| "rewrite (RUntil l I r) Swapped =  RUntil (rewrite r Same) I (rewrite l Same)"
| "rewrite (RAnd l r) Swapped =  RAnd (rewrite r Same) (rewrite l Same)"

| "rewrite (ROr \<phi> \<psi>) t =  ROr (rewrite \<phi> Same) (rewrite \<psi> Same)"

| "rewrite (RExists \<phi>) t = RExists (rewrite \<phi> Same)"
| "rewrite (RAgg y \<omega> b' f \<phi>) t = RAgg y \<omega> b' f (rewrite \<phi> Same)"
| "rewrite (RPrev I \<phi>) t = RPrev I (rewrite \<phi> Same)"
| "rewrite (RNext I \<phi>) t = RNext I (rewrite \<phi> Same)"

| "rewrite (RRelease \<phi> I \<psi>) t = RRelease (rewrite \<phi> Same) I (rewrite \<psi> Same)"
| "rewrite (RTrigger \<phi> I \<psi>) t =  RTrigger (rewrite \<phi> Same) I (rewrite \<psi> Same)"

| "rewrite (RNeg \<alpha>) t = RNeg (rewrite \<alpha> Same)"
| "rewrite (RDiamondW I \<alpha>) t = RDiamondW I (rewrite \<alpha> Same)"
| "rewrite (RDiamondB I \<alpha>) t = RDiamondB I (rewrite \<alpha> Same)"
| "rewrite (RSquareW I \<alpha>) t = RSquareW I (rewrite \<alpha> Same)"
| "rewrite (RSquareB I \<alpha>) t = RSquareB I (rewrite \<alpha> Same)"

(*| "rewrite (RMatchF I r) t = RMatchF I (my_map_regex (\<lambda>f. rewrite f Same) r)"
| "rewrite (RMatchP I r) t = RMatchP I (regex.map_regex (\<lambda>f. rewrite f Same) r)"
| "rewrite (RAnds \<phi>s) t = RAnds (map (\<lambda>r. rewrite r Same) \<phi>s)"*)                                    (*TODO: ADD THESE CASES*)
  
| "rewrite f t =  f "

  by pat_completeness auto
termination
  apply(relation "measures [(\<lambda>(f,t). (my_size f)),(\<lambda>(f,t). size_argpos t)]")
  apply (auto simp add: shift_size not_zero) (*not_zero important because size of constructor then depends on its' number of arguments*)
  done

lemma rewrite_cong[fundef_cong]: "r = r' \<Longrightarrow> t = t' \<Longrightarrow> rewrite r t = rewrite r' t'" by blast
lemma sat_cong[fundef_cong]: "\<sigma> = \<sigma>' \<Longrightarrow> V = V' \<Longrightarrow> v = v' \<Longrightarrow> i = i' \<Longrightarrow> a = a' \<Longrightarrow> Formula.sat \<sigma> V v i a = Formula.sat \<sigma>' V' v' i' a'" by blast

fun fix_r where
 "fix_r (RSince l I R) Swapped = RSince l I R"
| "fix_r (RUntil l I R) Swapped = RSince l I R"
| "fix_r r _ = r "

lemma fix_r_same: "fix_r f Same = f" by simp

lemma rewrite_sat: "rsat \<sigma> V v i (rewrite r t) = rsat \<sigma> V v i (fix_r r t)" sorry

definition "rewrite_f a = project (rewrite (embed a) Same)"

lemma proj_embed: "project (embed a) = a" sorry

lemma final_sat: "Formula.sat \<sigma> V v i (rewrite_f f) = Formula.sat \<sigma> V v i f"
proof -
  have "rsat \<sigma> V v i (rewrite (embed f) Same) = rsat \<sigma> V v i (embed f)" using rewrite_sat by auto
  then show ?thesis by (simp add: rewrite_f_def rsat_def proj_embed)
qed

inductive f_con where
f_con_1_t: "f_con (\<lambda>f1. Formula.Exists f1)"|
f_con_2_t: "f_con (\<lambda>f1. Formula.Neg f1)" |
f_con_3_t: "f_con (\<lambda>f1. Formula.Until TT I f1)"|
f_con_4_t: "f_con (\<lambda>f1. Formula.Since TT I f1)" |
f_con_5_t: "f_con (\<lambda>f1. Formula.Next I f1)"|
f_con_6_t: "f_con (\<lambda>f1. Formula.Prev I f1)"

lemma sub_1: "f_con P \<Longrightarrow> (\<And>i. Formula.sat \<sigma> V v i (project \<alpha>) = Formula.sat \<sigma> V v i (project \<beta>)) \<Longrightarrow> Formula.sat \<sigma> V v i (P (project \<alpha>)) = Formula.sat \<sigma> V v i (P (project \<beta>))" 
proof(induction P rule:f_con.induct)
case f_con_1_t
  then show ?case sorry
next
  case (f_con_6_t I)
  then show ?case by (simp split:nat.splits)
qed simp_all


inductive f_con2 where
f_con2_1_t: "f_con2 (\<lambda>f1 f2. Formula.Or f1 f2)" |
f_con2_2_t: "f_con2 (\<lambda>f1 f2. Formula.And f1 f2)" |
f_con2_3_t: "f_con2 (\<lambda>f1 f2. Formula.Neg (Formula.Until (Formula.Neg f1) I (Formula.Neg f2)))"|
f_con2_4_t: "f_con2 (\<lambda>f1 f2. Formula.Neg (Formula.Since (Formula.Neg f1) I (Formula.Neg f2)))" |
f_con2_5_t: "f_con2 (\<lambda>f1 f2. Formula.Since f1 I f2)"|
f_con2_6_t: "f_con2 (\<lambda>f1 f2. Formula.Until f1 I f2)"

lemma sub_2: "f_con2 P \<Longrightarrow> (\<And>i. Formula.sat \<sigma> V v i (project a1) = Formula.sat \<sigma> V v i (project b1)) \<Longrightarrow>
                           (\<And>i. Formula.sat \<sigma> V v i (project a2) = Formula.sat \<sigma> V v i (project b2)) \<Longrightarrow> 
                                 Formula.sat \<sigma> V v i (P (project a1) (project a2)) = Formula.sat \<sigma> V v i (P (project b1) (project b2))" 
  by(induction P rule:f_con2.induct;auto)



inductive f_conr where
(*f_conr_1_t: "f_conr (\<lambda>f1. RExists f1)"|*)
f_conr_2_t: "f_conr (\<lambda>f1. RNeg f1)" |
f_conr_3_t: "f_conr (\<lambda>f1. RDiamondW I f1)"|
f_conr_4_t: "f_conr (\<lambda>f1. RDiamondB I f1)" |
f_conr_5_t: "f_conr (\<lambda>f1. RNext I f1)"|
f_conr_6_t: "f_conr (\<lambda>f1. RPrev I f1)"

inductive trans where
(*f_conr_1_t: "f_conr (\<lambda>f1. RExists f1)"|*)
trans1: "trans (\<lambda>f1. RNeg f1) (\<lambda>f1. Formula.Neg f1)" |
trans2: "trans (\<lambda>f1. RDiamondW I f1) (\<lambda>f1. Formula.Until TT I f1)"|
trans3: "trans (\<lambda>f1. RDiamondB I f1)  (\<lambda>f1. Formula.Since TT I f1)" |
trans4: "trans (\<lambda>f1. RNext I f1) (\<lambda>f1. Formula.Next I f1)"|
trans5: "trans (\<lambda>f1. RPrev I f1) (\<lambda>f1. Formula.Prev I f1)"


lemma trans1: "trans P P' \<Longrightarrow> f_conr P \<and> f_con P' " 
  using f_con.simps f_conr.simps trans.simps by auto

lemma trans2: "trans P P' \<Longrightarrow> project (P r) = P' (project r)" 
proof(induction P P' rule:trans.induct)
  case trans1
  then show ?case sorry
next
  case (trans2 I)
  then show ?case sorry
next
  case (trans3 I)
  then show ?case sorry
next
  case (trans4 I)
  then show ?case sorry
next
  case (trans5 I)
  then show ?case sorry
qed

lemma trans3: "f_conr P \<Longrightarrow> \<exists>P'. trans P P'" 
  using f_conr.simps trans.trans1 trans.trans2 trans3 trans4 trans5 by force


lemma rsub_1: "f_conr P \<Longrightarrow> (\<And>i. rsat \<sigma> V v i \<alpha> = rsat \<sigma> V v i \<beta>) \<Longrightarrow> rsat \<sigma> V v i (P \<alpha>) = rsat \<sigma> V v i (P \<beta>)" 
proof -
  assume A: "f_conr P" "(\<And>i. rsat \<sigma> V v i \<alpha> = rsat \<sigma> V v i \<beta>)"
  then obtain P2 where P2: "trans P P2" using trans3[OF A(1)] by auto
  moreover have L1: "f_con P2" using trans1[OF P2] by auto
  moreover have L2:"(\<And>i. Formula.sat \<sigma> V v i (project \<alpha>) = Formula.sat \<sigma> V v i (project \<beta>))" using A(2) by (simp add: rsat_def)
  ultimately show ?thesis 
    using Rewriting.trans2 rsat_def sub_1 by presburger
qed




inductive f_conr2 where
f_conr2_1_t: "f_conr2 (\<lambda>f1 f2. ROr f1 f2)" |
f_conr2_2_t: "f_conr2 (\<lambda>f1 f2. RAnd f1 f2)" |
f_conr2_3_t: "f_conr2 (\<lambda>f1 f2. RRelease f1 I f2)"|
f_conr2_4_t: "f_conr2 (\<lambda>f1 f2. RTrigger f1 I f2)" |
f_conr2_5_t: "f_conr2 (\<lambda>f1 f2. RSince f1 I f2)"|
f_conr2_6_t: "f_conr2 (\<lambda>f1 f2. RUntil f1 I f2)"

inductive trans2 where
trans2_1: "trans2 (\<lambda>f1 f2. ROr f1 f2)  (\<lambda>f1 f2. Formula.Or f1 f2)" |
trans2_2: "trans2 (\<lambda>f1 f2. RAnd f1 f2) (\<lambda>f1 f2. Formula.And f1 f2)" |
trans2_3: "trans2 (\<lambda>f1 f2. RRelease f1 I f2) (\<lambda>f1 f2. Formula.Neg (Formula.Until (Formula.Neg f1) I (Formula.Neg f2)))"|
trans2_4: "trans2 (\<lambda>f1 f2. RTrigger f1 I f2) (\<lambda>f1 f2. Formula.Neg (Formula.Since (Formula.Neg f1) I (Formula.Neg f2)))" |
trans2_5: "trans2 (\<lambda>f1 f2. RSince f1 I f2) (\<lambda>f1 f2. Formula.Since f1 I f2)"|
trans2_6: "trans2 (\<lambda>f1 f2. RUntil f1 I f2) (\<lambda>f1 f2. Formula.Until f1 I f2)"

lemma trans2_1: "trans2 P P' \<Longrightarrow> f_conr2 P \<and> f_con2 P' " 
  using f_con2.simps f_conr2.simps trans2.simps by auto

lemma trans2_2: "trans2 P P' \<Longrightarrow> project (P r r2) = P' (project r) (project r2)" 
  sorry (* (induction P P' rule:trans2.induct;simp)*)

lemma trans2_3: "f_conr2 P \<Longrightarrow> \<exists>P'. trans2 P P'" 
  apply(induction P rule:f_conr2.induct)
  using trans2.trans2_1 trans2.trans2_2 trans2.trans2_3 trans2.trans2_4 trans2.trans2_5 trans2.trans2_6 apply blast+
  done


lemma rsub_2: "f_conr2 P \<Longrightarrow> (\<And>i. rsat \<sigma> V v i a1 = rsat \<sigma> V v i b1) \<Longrightarrow> (\<And>i. rsat \<sigma> V v i a2 = rsat \<sigma> V v i b2) \<Longrightarrow> rsat \<sigma> V v i (P a1 a2) = rsat \<sigma> V v i (P b1 b2)" 
proof -
  assume A: "f_conr2 P" "(\<And>i. rsat \<sigma> V v i a1 = rsat \<sigma> V v i b1)" "(\<And>i. rsat \<sigma> V v i a2 = rsat \<sigma> V v i b2)"
  then obtain P2 where P2: "trans2 P P2" using trans2_3[OF A(1)] by auto
  moreover have L1: "f_con2 P2" using trans2_1[OF P2] by auto
  moreover have L2:"(\<And>i. Formula.sat \<sigma> V v i (project a1) = Formula.sat \<sigma> V v i (project b1))" using A(2) by (simp add: rsat_def)
  moreover have L3:"(\<And>i. Formula.sat \<sigma> V v i (project a2) = Formula.sat \<sigma> V v i (project b2))" using A(3) by (simp add: rsat_def)
  ultimately show ?thesis 
    using Rewriting.trans2_2 rsat_def sub_2 by presburger
qed





 
  

(*
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
*)




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





end
