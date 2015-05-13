theory dilists imports Main begin

types
  heap = "nat \<rightharpoonup> nat"
  rname = "string"
  ass = "heap \<Rightarrow> (rname \<rightharpoonup> heap) \<Rightarrow> bool"

constdefs disjoint :: "heap \<Rightarrow> heap \<Rightarrow> bool" (infix "\<bottom>" 70)
 "(h \<bottom> h') \<equiv> ((dom h) \<inter> (dom h') = {})"

constdefs
  Box :: "ass \<Rightarrow> rname \<Rightarrow> ass" ("[_]_" [55,60] 60)
  "([P]a) \<sigma> \<Gamma> \<equiv> (\<sigma>=empty \<and> (case \<Gamma> a of None \<Rightarrow> False | Some \<Gamma>a \<Rightarrow> P \<Gamma>a \<Gamma>))"
  New :: "rname \<Rightarrow> ass \<Rightarrow> ass" ("N _. _" [60,55] 55)
  "(N a. P) \<sigma> \<Gamma> \<equiv> ((a \<notin> dom \<Gamma>) \<and> (\<exists>\<sigma>' \<sigma>''. (\<sigma>' \<bottom> \<sigma>'') 
  \<and> (\<sigma> = \<sigma>'++\<sigma>'') \<and> (\<forall>t \<in> ran \<Gamma>. \<sigma>'' \<bottom> t) \<and> (P \<sigma>' (\<Gamma>++[a \<mapsto> \<sigma>'']))))"
  Star :: "ass \<Rightarrow> ass \<Rightarrow> ass" (infixr "*" 55)
  "(P1 * P2) \<sigma> \<Gamma> \<equiv> (\<exists>\<sigma>' \<sigma>''. (\<sigma> = \<sigma>'++\<sigma>'') \<and> (\<sigma>' \<bottom> \<sigma>'') 
  \<and> (P1 \<sigma>' \<Gamma>) \<and> (P2 \<sigma>' \<Gamma>))"
  Cell :: "nat \<Rightarrow> nat \<Rightarrow> ass" (infix "\<longmapsto>" 60)
  "(e1 \<longmapsto> e2) \<sigma> \<Gamma> \<equiv> (\<sigma> = [e1 \<mapsto> e2])"
  Def :: "nat \<Rightarrow> ass" ("_ \<longmapsto> -" [60] 60)
  "(e1 \<longmapsto> -) \<sigma> \<Gamma> \<equiv> (\<exists>e2. \<sigma> = [e1 \<mapsto> e2])"
  emp :: "ass"
  "emp \<sigma> \<Gamma> \<equiv> (\<sigma>=empty)"


(* Bornat lists *)
inductive 
  blist :: "heap \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool"
where
  blistNil:  "blist empty n [] 0"
| blistCons: "blist \<sigma> n X y \<Longrightarrow> blist (\<sigma> ++ [x + n \<mapsto> y]) n (x # X) x"


(* Naïve Definition of doubly-indexed lists *)  
function
  nlist0 :: "nat \<Rightarrow> ass"
where
  "nlist0 x \<sigma> \<Gamma> = ((x=0 \<and> emp \<sigma> \<Gamma>) \<or> 
               (x\<noteq>0 \<and> (\<exists>y. ((x+0 \<longmapsto> y) * (x+1 \<longmapsto> -) * (nlist0 y)) \<sigma> \<Gamma>)))"
by pat_completeness auto
termination 
apply (relation "measure (\<lambda>(x,\<sigma>::nat\<rightharpoonup>nat,\<Gamma>). sizedom \<sigma>)")
  


primrec
  "nlist1(x) = ((x=0) \<and> emp) \<or>
               ((x\<noteq>0) \<and> (\<exists>y. (x+0 \<longmapsto> -) * ((x+1) \<longmapsto> y) * (nlist1 y)))"
constdefs
  "ndil(r0,r1) \<equiv> nlist0 r0 \<and> nlist1 r1"

(* Clever Definition of doubly-indexed lists *)
primrec
  "list0(x) = (x=0 \<and> emp) \<or> 
              (x\<noteq>0 \<and> \<exists>y. x+0 \<mapsto> y * [x+1 \<mapsto> _]\<beta> * list0(y))"
primrec
  "list1(x) = (x=0 \<and> emp) \<or>
              (x\<noteq>0 \<and> \<exists>y. [x+0 \<mapsto> _]\<alpha> * x+1 \<mapsto> y * list0(y))"
constdefs
  "dil(r0,r1) \<equiv> N \<alpha>. N \<beta>. [list0 r0]\<alpha> * [list1 r1]\<beta>"

theorem
  "\<lbrakk>elems X0 = elems X1; blist \<sigma>\<alpha> 0 X0 r0; blist \<sigma>\<beta> 1 X1 r1; \<sigma>\<alpha> \<bottom> \<sigma>\<beta>\<rbrakk> 
  \<Longrightarrow>  \<sigma>\<alpha>++\<sigma>\<beta>, empty \<Turnstile> dil(r0,r1)" 
sorry




end