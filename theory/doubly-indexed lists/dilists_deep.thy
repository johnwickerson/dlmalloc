theory dilists imports Main begin

types
  heap = "nat \<rightharpoonup> nat"
  rname = "string"

datatype ass =
   Box "ass" "rname" ("[_]_" [55,60] 60)
 | New "rname" "ass" ("N _. _" [60,55] 55)
 | Star "ass" "ass" (infixr "*" 55)
 | Cell "nat" "nat" (infixr "\<longmapsto>" 60)
 | Eq "nat" "nat" (infixr "=" 60)
 | Noteq "nat" "nat" (infix "\<noteq>" 60)
 | emp
 | Disj "ass" "ass" (infixr "\<or>" 60)
 | Conj "ass" "ass" (infixr "\<and>" 60)
 | Exists "nat" "ass" ("\<exists> _. _" [60,55] 55)
 | false
 | true

constdefs disjoint :: "heap \<Rightarrow> heap \<Rightarrow> bool" (infix "\<bottom>" 70)
 "(h \<bottom> h') \<equiv> ((dom h) \<inter> (dom h') = {})"

primrec
  Sat :: "heap \<Rightarrow> (rname \<rightharpoonup> heap) \<Rightarrow> ass \<Rightarrow> bool" ("_,_ \<Turnstile> _" [51,51,51] 51)
where
  Box:  "\<sigma>, \<Gamma> \<Turnstile> [P]a = (\<sigma>=empty \<and> (case \<Gamma> a of None \<Rightarrow> False | Some \<Gamma>a \<Rightarrow> \<Gamma>a, \<Gamma> \<Turnstile> P))"
| New: "\<sigma>, \<Gamma> \<Turnstile> N a. P = ((a \<notin> dom \<Gamma>) \<and> (\<exists>\<sigma>' \<sigma>''. (\<sigma>' \<bottom> \<sigma>'') \<and> (\<sigma> = \<sigma>'++\<sigma>'') \<and> (\<forall>t \<in> ran \<Gamma>. \<sigma>'' \<bottom> t) \<and> (\<sigma>', \<Gamma>++[a \<mapsto> \<sigma>''] \<Turnstile> P)))"
| Star: "\<sigma>, \<Gamma> \<Turnstile> P1 * P2 = (\<exists>\<sigma>' \<sigma>''. (\<sigma> = \<sigma>'++\<sigma>'') \<and> (\<sigma>' \<bottom> \<sigma>'') \<and> (\<sigma>', \<Gamma> \<Turnstile> P1) \<and> (\<sigma>'', \<Gamma> \<Turnstile> P2))"
| Cell: "\<sigma>, \<Gamma> \<Turnstile> e1 \<longmapsto> e2 = (\<sigma> = [e1 \<mapsto> e2])"
| Eq: "(\<sigma>, \<Gamma> \<Turnstile> (e1=e2)) = (e1=e2)"
| Noteq: "(\<sigma>, \<Gamma> \<Turnstile> (e1\<noteq>e2)) = (e1\<noteq>e2)"
| Emp: "\<sigma>, \<Gamma> \<Turnstile> emp = (\<sigma> = empty)"
| Disj: "\<sigma>, \<Gamma> \<Turnstile> P1 \<or> P2 = ((\<sigma>, \<Gamma> \<Turnstile> P1) \<or> (\<sigma>, \<Gamma> \<Turnstile> P2))"
| Conj: "\<sigma>, \<Gamma> \<Turnstile> P1 \<and> P2 = ((\<sigma>, \<Gamma> \<Turnstile> P1) \<and> (\<sigma>, \<Gamma> \<Turnstile> P2))"
| Exists: "(\<sigma>, \<Gamma> \<Turnstile> (\<exists>x. P)) = (\<exists>x::nat. (\<sigma>, \<Gamma> \<Turnstile> P))"
| False: "\<sigma>, \<Gamma> \<Turnstile> false = False"
| True: "\<sigma>, \<Gamma> \<Turnstile> true = True"

(* Bornat lists *)
inductive 
  blist :: "heap \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool"
where
  blistNil:  "blist empty n [] 0"
| blistCons: "blist \<sigma> n X y \<Longrightarrow> blist (\<sigma> ++ [x + n \<mapsto> y]) n (x # X) x"


(* Naïve Definition of doubly-indexed lists *)
fun nlist0 :: "nat \<Rightarrow> ass"
where
  "nlist0(x) = ((x=0) \<and> emp) \<or> 
               ((x\<noteq>0) \<and> (\<exists>y. ((x+0) \<longmapsto> y) * (\<exists>k. (x+1) \<longmapsto> k) * (nlist0 y)))"
primrec
  "nlist1(x) = ((x=0) \<and> emp) \<or>
               ((x\<noteq>0) \<and> (\<exists>y. (\<exists>k. (x+0) \<longmapsto> k) * ((x+1) \<longmapsto> y) * (nlist1 y)))"
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