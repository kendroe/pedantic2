-------------------------------------------------------------------
-- The PEDANTIC (Proof Engine for Deductive Automation using Non-deterministic
-- Traversal of Instruction Code) verification framework
--
-- Developed by Kenneth Roe
-- For more information, check out www.cs.jhu.edu/~roe
-- 
-- traversal.v
--
-- Tree traversal example.
-- 
-------------------------------------------------------------------

import .PEDANTIC2

def P := 0.
def RR := 1.
def I := 2.
def N := 3.
def T := 4.
def Tmp_l := 5.
def Tmp_r := 6.

def initCode : com :=
    I ::= A0;
    T ::= !RR;
    P ::= A0.

def precondition : absState :=
    (absExists (λ (x:Value), (absTree (λ env, env RR) 2 (0::1::list.nil) x))).

def afterAssigns : absState := (absExists (λ rTree, (absExists (λ iTree, (absExists (λ pTree, 
         (absTree (λ env, env RR) 2 [0,1] rTree) **
         (absTree (λ env, env I) 2 [0] iTree) **
         (absTree (λ env, env P) 2 [0] pTree) **
         (absAllU (treeRecords iTree) (λ v,(λ st, inTree (nthval 2 (find v iTree)) rTree))) **
         (absAllU (treeRecords pTree) (λ v,(λ st, inTree (nthval 2 (find v pTree)) rTree))))))))).

open tactic
open monad
open expr
open smt_tactic

--@[simp] theorem dist_conj1 {a : absState} {b:absState} (st : imp_state) {v:ident} {e:ℕ} :
--       (a**b) st =
--       a st ** b st :=
--begin
--    admit
--end

--@[simp] theorem dist_conj2 {a : absState} {b:absState} {v:ident} {e:ℕ} :
--       (λ (st : imp_state), (a**b) (st.fst, override (st.snd) v e))=
--       (absCompose (λ (st : imp_state), a (st.fst, override (st.snd) v e))
--          (λ (st : imp_state), b (st.fst, override (st.snd) v e))) :=
--begin
--    admit
--end

@[simp] theorem dist_exists {t} {a : absState} {v:ident} {e:ℕ} :
       (λ (st : imp_state), 
              (@absExists t (λ (x:t), a) (st.fst, override (st.snd) v e)))=
       @absExists t (λ (x:t), (λ (st : imp_state), a (st.fst, override (st.snd) v e))) :=
begin
    admit
end

theorem initWorks: {{precondition}} initCode {{ afterAssigns }} := begin
    unfold initCode, unfold precondition,
    apply strengthenPost,
    apply compose, apply compose,
    apply assignPropagate, 
    dsimp [aeval, A0,A1,A2,A3,A4,A5,A6], simp,
    simplify_override2, simplify_override_predicate,
    simplify_tree,
end.


