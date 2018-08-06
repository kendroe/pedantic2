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

theorem initWorks: {{precondition}} initCode {{ afterAssigns }} := begin
    unfold initCode, unfold precondition,
    apply strengthenPost,
    apply compose, apply compose,
    apply assignPropagate, evaluate_aeval, simplify_override,
    simplify_override2, simplify_override_predicate,
    simplify_tree, conv
    begin
    end,

    apply assignPropagate,
    evaluate_aeval, apply assignPropagate, evaluate_aeval,

    intros s a, rw [absExists] at a,
end.


