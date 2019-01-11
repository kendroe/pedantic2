-------------------------------------------------------------------
-- The PEDANTIC (Proof Engine for Deductive Automation using Non-deterministic
-- Traversal of Instruction Code) verification framework
--
-- Developed by Kenneth Roe
-- For more information, check out www.cs.jhu.edu/~roe
-- 
-- AbsExecute.v
-- This file contains the basic hoare triple definition and many auxiliary theorems
-- and definitions related to forward propagation.
-- 
-- Some key definitions:
--     absExecute
--     hoare_triple
--     strengthenPost
--     assign
--     basic_assign
--     load_traverse
--     load
--     store
--     new_thm
--     delete_thm
--     if_statement
--     while
-------------------------------------------------------------------

import .impHeap
import .AbsState

open tactic
open monad
open expr
open smt_tactic

-------------------------------------------------------------------

--def In {A:Type} : A → list A → Prop
--| _ list.nil := false
--| a (b :: m) := b = a ∨ In a m

def absExecute (funs : functions)
               (c : com)
               (s : absState)
               (s' : absState)
               (r : list (@absExp ℕ))
               (s'' : absState)
               (exc : ident → ((@absExp ℕ) × absState)) : Prop :=
    ∀ st st' i x,
        realizeState s st →
        ((∃ st', ∃ r, ceval funs st c st' r) ∧
         ((ceval funs st c st' func_result.NoResult → realizeState s' st') ∧
          (ceval funs st c st' (func_result.Return x) →
            ((∀ rx, rx ∈ r → @absEval ℕ (st'.snd) rx = x) ∧ realizeState s'' st')) ∧
          (ceval funs st c st' (func_result.Exception i x) → (@absEval ℕ (st'.snd) ((exc i).fst) = x ∧ realizeState ((exc i).snd) st'))))

def hoare_triple (P : absState) (c : com) (Q : absState) (r : list (@absExp ℕ)) (Qr : absState) (exc : ident → ((@absExp ℕ) × absState)) : Prop :=
    absExecute (λ x y z a b, ff) c P Q r Qr exc.

notation `{{ ` P ` }} ` c ` {{ ` Q ` }}` := (hoare_triple P c Q list.nil absNone (λ (x:ident), ((λ (x:env), 0),absNone))).
notation `{{ ` P ` }} ` c ` {{ ` Q ` return ` rr ` with ` QQ ` }}` := (hoare_triple P c Q rr QQ (λ (x:ident), ((λ (x:env), 0),absNone))).

theorem override_equal : ∀ env v, override env v (env v)=env :=
begin
    intros, unfold override, funext,
    by_cases (v=l),rewrite h,simp,
    simp [h]
end

--theorem fun_ext {t} {u} :
--    ∀ (a:t→u) (b:t→u), a=b → (λ (x:t), a)=(λ (x:t), b) :=
--begin
--    assume a b h, by rw h
--end

theorem double_override : ∀ env v v1 v2, override (override env v v1) v v2=override env v v2 :=
begin
    intros, unfold override,
    have h:(∀ l, (ite (v=l) v2 (ite (v=l) v1 (env l)))=
            ite (v=l) v2 (env l)),
    intros, by_cases (v=l), rewrite h, simp,
    simp [h], simp only [h]
end

theorem nonethm {t} : (none <|> none)=@none t:= rfl.

theorem nonethm2 {t} {x:option t} : (x <|> none)=x:= begin
    cases x;refl
end

theorem assignPropagate: ∀ (P : absState) (v:ℕ) e xx,
    hoare_triple P  (v ::= e)
          (absExists
              (λ vv, ( (λ st, (P  ** (absPredicate (λ ee, aeval ee e=st.snd v)))
                       
                       (override_state v vv st))
           ))) [] absNone xx :=
begin
    unfold override_state,
    
    unfold hoare_triple, intros, unfold absExecute,
    intros, split,

    existsi _, existsi _, apply ceval.Ass,

    unfold realizeState at a, split, intro, cases a_1,
    
    unfold realizeState, unfold absExists,
    existsi (st.snd v), unfold absCompose, existsi _, existsi _,
    simp, split,

    have h:(P ((st.fst, override (st.snd) v (aeval (st.snd) e)).fst,
         override ((st.fst, override (st.snd) v (aeval (st.snd) e)).snd) v (st.snd v))), swap,
    apply h, simp, rw double_override, rw override_equal,
    cases st, simp, apply a,

    swap, apply ((empty_heap, override (st.snd) v (aeval (st.snd) e)).fst,
         override ((st.fst, override (st.snd) v (aeval (st.snd) e)).snd) v (st.snd v)),
    
    simp,split, unfold absPredicate, simp, rewrite double_override,
    rw override_equal, unfold override, simp,

    simp, rw double_override, rw override_equal,
    unfold concreteCompose, simp, split,

    intro, right, unfold empty_heap, unfold inhabited.default,
    unfold empty_heap, unfold inhabited.default,
    unfold compose_heaps, simp only [nonethm2],

    --cases st, have h:(∀ x, compose_heaps st.fst empty_heap x = st.fst x),

    --intro, unfold compose_heaps, generalize el:(st.fst x_1)=qq,
    --cases qq, unfold empty_heap, unfold inhabited.default,
    --apply nonethm,
  
    --unfold empty_heap, unfold inhabited.default,
    --simp only [compose_heaps._match_1],
    --tactic.funext,apply h,

    split, intros, split, intros, cases a_2, cases a_1,
    intros, cases a_1

end

--set_option trace.simp_lemmas true.
--set_option trace.simplify true.

theorem strengthenPost : ∀ (R : absState) (P : absState) (Q : absState) (C : com),
                         {{ P }} C {{ Q }} →
                         (forall st, Q st → R st) →
                         {{ P }} C {{ R }} := begin
    intros, unfold hoare_triple at a, unfold absExecute at a,
    unfold hoare_triple, unfold absExecute,
    intros,
    specialize a st st' i x,
    simp, simp at a,
    have hh:((∃ (st' : imp_state),
       Exists
         (ceval (λ (x : ident) (y : imp_state) (z : list ℕ) (a : imp_state) (b : func_result), false) st C st')) ∧
    ((ceval (λ (x : ident) (y : imp_state) (z : list ℕ) (a : imp_state) (b : func_result), false) st C st'
          func_result.NoResult →
        realizeState Q st') ∧
       (ceval (λ (x : ident) (y : imp_state) (z : list ℕ) (a : imp_state) (b : func_result), false) st C st'
            (func_result.Return x) →
          realizeState absNone st') ∧
         (ceval (λ (x : ident) (y : imp_state) (z : list ℕ) (a : imp_state) (b : func_result), false) st C st'
            (func_result.Exception i x) →
          absEval (st'.snd) (λ (x : env), 0) = x ∧ realizeState absNone st'))),
    apply a, apply a_2,
    cases hh, split, apply hh_left,
    cases hh_right, split, intros, apply a_1, apply hh_right_left,
    apply a_3, cases hh_right_right, split, intros,
    exfalso, unfold realizeState at hh_right_right_left,
    unfold absNone at hh_right_right_left,
    apply hh_right_right_left, apply a_3,
    intros, exfalso,unfold realizeState at hh_right_right_right,
    unfold absNone at hh_right_right_right,
    simp at hh_right_right_right,
    apply hh_right_right_right, apply a_3
end

theorem nilmem {t} (x : t) : x ∈ @list.nil t=false :=
begin
    simp
end

theorem rsfalse { st : imp_state} : realizeState absNone st=false :=
begin
    unfold realizeState, unfold absNone
end

theorem andfalse { a : Prop } : (a ∧ false)=false :=
begin
    simp
end

theorem compose : forall (P:absState) c1 c2 Q R,
    {{ P }} c1 {{ Q }} →
    {{ Q }} c2 {{ R }} →
    {{ P }} (com.Seq c1 c2) {{ R }} := begin
    intros, unfold hoare_triple at a, unfold hoare_triple at a_1,
    unfold absExecute at a, unfold absExecute at a_1,
    unfold hoare_triple, unfold absExecute,
    intros,
    simp at a_1, simp at a,
    simp,
     simp only [rsfalse] at a, simp only [andfalse] at a,
     simp only [rsfalse] at a_1, simp only [andfalse] at a_1,

     have aaa:(∀ (st' : imp_state), (∃ (st' : imp_state),
         Exists
           (ceval (λ (x : ident) (y : imp_state) (z : list ℕ) (a : imp_state) (b : func_result), false) st c1
              st')) ∧
      ((ceval (λ (x : ident) (y : imp_state) (z : list ℕ) (a : imp_state) (b : func_result), false) st c1 st'
            func_result.NoResult →
          realizeState Q st') ∧
         (ceval (λ (x : ident) (y : imp_state) (z : list ℕ) (a : imp_state) (b : func_result), false) st c1 st'
              (func_result.Return x) →
            false) ∧
           (ceval (λ (x : ident) (y : imp_state) (z : list ℕ) (a : imp_state) (b : func_result), false) st c1 st'
              (func_result.Exception i x) →
            false))),
    intros, apply a, apply a_2,
    split,
    have aaa2:(  ∀ (st' : imp_state),
    (∃ (st' : imp_state),
         Exists
           (ceval (λ (x : ident) (y : imp_state) (z : list ℕ) (a : imp_state) (b : func_result), false) st c1
              st')) ∧
      ((ceval (λ (x : ident) (y : imp_state) (z : list ℕ) (a : imp_state) (b : func_result), false) st c1 st'
            func_result.NoResult →
          realizeState Q st') ∧
         (ceval (λ (x : ident) (y : imp_state) (z : list ℕ) (a : imp_state) (b : func_result), false) st c1 st'
              (func_result.Return x) →
            false) ∧
           (ceval (λ (x : ident) (y : imp_state) (z : list ℕ) (a : imp_state) (b : func_result), false) st c1 st'
              (func_result.Exception i x) →
            false))), apply aaa,
        
    specialize aaa st', cases aaa, cases aaa_left, cases aaa_left_h,
    cases aaa_left_h_w,

    have aa1:((∃ (st' : imp_state),
       Exists
         (ceval (λ (x : ident) (y : imp_state) (z : list ℕ) (a : imp_state) (b : func_result), false) aaa_left_w c2
            st')) ∧
    ((ceval (λ (x : ident) (y : imp_state) (z : list ℕ) (a : imp_state) (b : func_result), false) aaa_left_w c2 st'
          func_result.NoResult →
        realizeState R st') ∧
       (ceval (λ (x : ident) (y : imp_state) (z : list ℕ) (a : imp_state) (b : func_result), false) aaa_left_w c2 st'
            (func_result.Return x) →
          false) ∧
         (ceval (λ (x : ident) (y : imp_state) (z : list ℕ) (a : imp_state) (b : func_result), false) aaa_left_w c2
            st'
            (func_result.Exception i x) →
          false))), apply a_1,
    specialize aaa2 aaa_left_w, cases aaa2, cases aaa2_right,
    apply aaa2_right_left, apply aaa_left_h_h,
    cases aa1, cases aa1_left, cases aa1_left_h,

    existsi aa1_left_w, existsi aa1_left_h_w,
    apply ceval.Seq1, apply aaa_left_h_h,
    --specialize a_1 aaa_left_w st' i x,

    apply aa1_left_h_h,

    existsi _, existsi _,
    apply ceval.Seq2, apply aaa_left_h_h, 

    existsi _, existsi _,
    apply ceval.Seq3, apply aaa_left_h_h,

    split,
    intros, 
    cases a_3,
    specialize aaa a_3_st', cases aaa, cases aaa_right,
    specialize a_1 a_3_st' st' i x,

    have hh:(realizeState Q a_3_st' → (ceval (λ (x : ident) (y : imp_state) (z : list ℕ) (a : imp_state) (b : func_result), false) a_3_st' c2 st'
         func_result.NoResult) →
  realizeState R st'),
    intros,
    have hhh:((∃ (st' : imp_state),
       Exists
         (ceval (λ (x : ident) (y : imp_state) (z : list ℕ) (a : imp_state) (b : func_result), false) a_3_st' c2
            st')) ∧
    (ceval (λ (x : ident) (y : imp_state) (z : list ℕ) (a : imp_state) (b : func_result), false) a_3_st' c2 st'
         func_result.NoResult →
       realizeState R st') ∧
      (ceval (λ (x : ident) (y : imp_state) (z : list ℕ) (a : imp_state) (b : func_result), false) a_3_st' c2 st'
           (func_result.Return x) →
         false) ∧
        (ceval (λ (x : ident) (y : imp_state) (z : list ℕ) (a : imp_state) (b : func_result), false) a_3_st' c2 st'
           (func_result.Exception i x) →
         false)), apply a_1, apply a_3,
    cases hhh, cases hhh_right,
    apply hhh_right_left, apply a_4,

    apply hh, apply aaa_right_left, apply a_3_a, apply a_3_a_1,

    split, intros, unfold realizeState, unfold absNone,
    cases a_3,
    specialize aaa a_3_st', cases aaa, cases aaa_right,
    specialize a_1 a_3_st' st' i x,
    have hh:((∃ (st' : imp_state),
       Exists
         (ceval (λ (x : ident) (y : imp_state) (z : list ℕ) (a : imp_state) (b : func_result), false) a_3_st' c2
            st')) ∧
    (ceval (λ (x : ident) (y : imp_state) (z : list ℕ) (a : imp_state) (b : func_result), false) a_3_st' c2 st'
         func_result.NoResult →
       realizeState R st') ∧
      (ceval (λ (x : ident) (y : imp_state) (z : list ℕ) (a : imp_state) (b : func_result), false) a_3_st' c2 st'
           (func_result.Return x) →
         false) ∧
        (ceval (λ (x : ident) (y : imp_state) (z : list ℕ) (a : imp_state) (b : func_result), false) a_3_st' c2 st'
           (func_result.Exception i x) →
         false)), apply a_1, apply aaa_right_left, apply a_3_a,
    cases hh, cases hh_right, cases hh_right_right,

    apply hh_right_right_left, apply a_3_a_1,
    specialize aaa st',
    cases aaa, cases aaa_right, cases aaa_right_right,
    apply aaa_right_right_left, apply a_3_a,


    intros, exfalso,
    cases a_3,
    specialize aaa a_3_st', cases aaa, cases aaa_right,
    specialize a_1 a_3_st' st' i x,
    have hh:((∃ (st' : imp_state),
       Exists
         (ceval (λ (x : ident) (y : imp_state) (z : list ℕ) (a : imp_state) (b : func_result), false) a_3_st' c2
            st')) ∧
    (ceval (λ (x : ident) (y : imp_state) (z : list ℕ) (a : imp_state) (b : func_result), false) a_3_st' c2 st'
         func_result.NoResult →
       realizeState R st') ∧
      (ceval (λ (x : ident) (y : imp_state) (z : list ℕ) (a : imp_state) (b : func_result), false) a_3_st' c2 st'
           (func_result.Return x) →
         false) ∧
        (ceval (λ (x : ident) (y : imp_state) (z : list ℕ) (a : imp_state) (b : func_result), false) a_3_st' c2 st'
           (func_result.Exception i x) →
         false)), apply a_1, apply aaa_right_left, apply a_3_a,
    cases hh, cases hh_right, cases hh_right_right,

    apply hh_right_right_right, apply a_3_a_1,
    specialize aaa st',
    cases aaa, cases aaa_right, cases aaa_right_right,
    apply aaa_right_right_right, apply a_3_a  
end


meta def evaluate_aeval_helper : expr → expr
| `(aeval %%e (aexp.Num %%x)) := x
| `(aeval %%e (aexp.Var %%v)) := e v
| `(aeval %%e (aexp.Plus %%x %%y)) :=
            `((%%(evaluate_aeval_helper `(aeval %%e %%x))) +
              (%%(evaluate_aeval_helper `(aeval %%e %%y))))
| `(aeval %%e (aexp.Minus %%x %%y)) :=
            `((%%(evaluate_aeval_helper `(aeval %%e %%x))) -
              (%%(evaluate_aeval_helper `(aeval %%e %%y))))
| `(aeval %%e (aexp.Mult %%x %%y)) :=
            `((%%(evaluate_aeval_helper `(aeval %%e %%x))) *
              (%%(evaluate_aeval_helper `(aeval %%e %%y))))
| `(aeval %%e (aexp.Eq %%x %%y)) :=
           `((%%(evaluate_aeval_helper `(aeval %%e %%x))) =
             (%%(evaluate_aeval_helper `(aeval %%e %%y))))
| `(aeval %%e (aexp.Le %%x %%y)) :=
           `(%%(evaluate_aeval_helper `(aeval %%e %%x))≤
             %%(evaluate_aeval_helper `(aeval %%e %%y)))
| `(aeval %%e (aexp.Land %%x %%y)) :=
      `(if ((aeval %%e %%x)=0) then 0 else (aeval %%e %%y))
--| `(aeval %%e (aexp.Land %%x %%y)) := `(if (aeval %%e %%x)=0 then 0 else (aeval %%e %%y))
| `(aeval %%e (aexp.Lor %%x %%y)) := `(if (aeval %%e %%x)=0 then (aeval %%e %%y) else (aeval %%e %%x))
| `(aeval %%e (aexp.Lnot %%x)) := `(if (aeval %%e %%x)=0 then 1 else 0)
| `(aeval %%e A0) := `(0)
| `(aeval %%e A1) := `(1)
| `(aeval %%e A2) := `(2)
| `(aeval %%e A3) := `(3)
| `(aeval %%e A4) := `(4)
| `(aeval %%e A5) := `(5)
| `(aeval %%e A6) := `(6)
| (expr.app a b) := expr.app (evaluate_aeval_helper a) (evaluate_aeval_helper b)
| (expr.lam v b t e) := expr.lam v b (evaluate_aeval_helper t) (evaluate_aeval_helper e)
| (expr.pi v b t e) := expr.pi v b (evaluate_aeval_helper t) (evaluate_aeval_helper e)
| x := x

meta def evaluate_aeval : tactic unit :=
do { t ← target,
     tgt ← instantiate_mvars t,
     --trace tgt.to_raw_fmt,
     nt ← some (evaluate_aeval_helper tgt),
     --trace nt.to_raw_fmt,
     change nt }

--theorem xx: 1=(2,2).fst :=
--begin
--    do {
--        xxx ← target,
--        trace xxx.to_raw_fmt,
--        admit
--    }
--end

set_option eqn_compiler.max_steps 9999
set_option timeout 10000

meta def simplify_override_helper : expr → expr
| `(λ st, (absCompose %%l %%r)
          (@prod.mk
           (@prod.fst st)
           (override (@prod.snd st) %%vv %%ee))) :=
  (expr.app (expr.app `(absCompose)
      (expr.lam "st" binder_info.default `(imp_state)
          (expr.app
            l
            (expr.app (expr.app `(@prod.mk heap env)
              (expr.app `(@prod.fst heap env) (expr.var 0)))
              (expr.app (expr.app (expr.app `(@override)
                 (expr.app `(@prod.snd heap env) (expr.var 0))) vv) ee)
              ))))
      (expr.lam "st" binder_info.default `(imp_state)
          (expr.app
            l
            (expr.app (expr.app `(@prod.mk heap env)
              (expr.app `(@prod.fst heap env) (expr.var 0)))
              (expr.app (expr.app (expr.app `(@override)
                 (expr.app `(@prod.snd heap env) (expr.var 0))) vv) ee)
              ))))
| (expr.app a b) := expr.app (simplify_override_helper a) (simplify_override_helper b)
| (expr.lam v b t e) := expr.lam v b (simplify_override_helper t) (simplify_override_helper e)
| (expr.pi v b t e) := expr.pi v b (simplify_override_helper t) (simplify_override_helper e)
| x := x

meta def simplify_override_helperb : expr → expr
| `(λ st, (absExists (λ (v:%%t), %%e))
          (@prod.mk (@prod.fst st) (override (@prod.snd st) %%vv %%ee))) :=
      (expr.app `(@absExists %%t)
                    (expr.lam "v" binder_info.default t
                       (expr.lam "st" binder_info.default `(imp_state)
                         (expr.app
                           (expr.lower_vars (expr.lift_vars e 0 1) 2 1)
                           (expr.app
                             (expr.app
                               `(@prod.mk heap env)
                               (expr.app `(@prod.fst heap env) (expr.var 0)))
                               (expr.app (expr.app (expr.app `(override)
                                  (expr.app
                                    `(@prod.snd heap env)
                                    (expr.var 0)))
                                  vv) ee))
                          )
                       )))
| (expr.app a b) := expr.app (simplify_override_helperb a) (simplify_override_helperb b)
| (expr.lam v b t e) := expr.lam v b (simplify_override_helper t) (simplify_override_helperb e)
| (expr.pi v b t e) := expr.pi v b (simplify_override_helperb t) (simplify_override_helperb e)
| x := x

--meta def q : ℕ → (ℕ → ℕ)
--| _ := (λ (s:ℕ), s) 3.

--theorem test : 1=2 :=
--begin
--    do {
--      a ← some (q 0),
--      trace "abc",
--      --trace (a.to_raw_format),
--      b ← to_expr (``(λ (sss:ℕ), sss)),
--      trace b.to_raw_fmt,
--      admit
--    }
--end

meta def simplify_override_helper' : expr → expr
| (expr.lam st b stt
      (expr.app
        (expr.app
          (expr.app
            `(absCompose)
            l)
          r)
        (expr.app
          (expr.app
            (expr.app (expr.app pm hhh) eee)
            (expr.app
              (expr.app (expr.app pf hhha) eeea)
              (expr.var 0)))
          (expr.app
            (expr.app
              (expr.app
                `(override)
                (expr.app
                  (expr.app (expr.app ps hhhb) eeeb)
                  (expr.var 0)))
                vv)
              ee)))) :=
  (expr.app (expr.app `(absCompose)
      (expr.lam st b stt
          (expr.app
            l
            (expr.app (expr.app (expr.app (expr.app pm hhh) eee)
              (expr.app (expr.app (expr.app pf hhha) eeea) (expr.var 0)))
              (expr.app (expr.app (expr.app `(override)
                 (expr.app (expr.app (expr.app ps hhhb) eeeb)
                 (expr.var 0))) vv) ee)
              ))))
      (expr.lam st b stt
          (expr.app
            r
            (expr.app (expr.app (expr.app (expr.app pm hhh) eee)
              (expr.app (expr.app (expr.app pf hhha) eeea) (expr.var 0)))
              (expr.app (expr.app (expr.app `(override)
                 (expr.app (expr.app (expr.app ps hhhb) eeeb)
                 (expr.var 0))) vv) ee)
              ))))
| (expr.app a b) := expr.app (simplify_override_helper' a) (simplify_override_helper' b)
| (expr.lam v b t e) := expr.lam v b (simplify_override_helper' t) (simplify_override_helper' e)
| (expr.pi v b t e) := expr.pi v b (simplify_override_helper' t) (simplify_override_helper' e)
| x := x

meta def simplify_override_helper2 : expr → expr
| (expr.lam st b stt
    (expr.app (expr.app (expr.app ex ext)
        (expr.lam vvv bb vtt e))
      (expr.app
        (expr.app
          (expr.app (expr.app pm hhh) eee)
          (expr.app (expr.app (expr.app pf hhha) eeea) (expr.var 0)))
        (expr.app (expr.app (expr.app `(override)
          (expr.app
              (expr.app (expr.app ps hhhb) eeeb)
              (expr.var 0)))
          vv)
        ee)))) := (expr.app (expr.app ex ext)
                    (expr.lam vvv bb vtt
                       (expr.lam st b stt
                         (expr.app
                           (expr.lower_vars (expr.lift_vars e 0 1) 2 1)
                           (expr.app
                             (expr.app
                               (expr.app (expr.app pm hhh) eee)
                                 (expr.app (expr.app (expr.app pf hhha) eeea) (expr.var 0)))
                               (expr.app (expr.app (expr.app `(override)
                                  (expr.app
                                    (expr.app (expr.app ps hhhb) eeeb)
                                    (expr.var 0)))
                                  vv) ee))
                          )
                       )))

| (expr.app a b) := expr.app (simplify_override_helper2 a) (simplify_override_helper2 b)
| (expr.lam v b t e) := expr.lam v b (simplify_override_helper2 t) (simplify_override_helper2 e)
| (expr.pi v b t e) := expr.pi v b (simplify_override_helper2 t) (simplify_override_helper2 e)
| x := x

meta def replace_varn_helper : ℕ → expr → expr → expr
| n r (expr.var nn) := if n=nn then r else (expr.var nn)
| n r (expr.app a b) := expr.app (replace_varn_helper n r a) (replace_varn_helper n r b)
| n r (expr.lam v b t e) := expr.lam v b (replace_varn_helper (n+1) r t) (replace_varn_helper (n+1) r e)
| n r (expr.pi v b t e) := expr.pi v b (replace_varn_helper n r t) (replace_varn_helper n r e)
| n r x := x

meta def simplify_tree_helper : expr → expr
| (expr.lam st bb stt 
    (expr.app
      (expr.app
        (expr.app
          (expr.app
            (expr.app
              tree 
              (expr.lam v b t e))
            nn)
          fff)
        fr)
        (expr.app
          (expr.app
            (expr.app (expr.app pm hhh) eee)
            (expr.app (expr.app (expr.app pf hhha) eeea) (expr.var 0)))
            (expr.app (expr.app (expr.app `(override)
              (expr.app
                (expr.app (expr.app ps hhhb) eeeb)
                (expr.var 0)))
            vv)
          ee)))) :=
      (expr.app
        (expr.app
          (expr.app
            (expr.app
              tree 
              (expr.lam v b t
               (replace_varn_helper 0
                 (expr.app (expr.app (expr.app `(override)
                   (expr.var 0))
                   vv)
                 ee)               
                 (expr.lower_vars e 2 1))
              ))
            (expr.lower_vars nn 1 1))
          (expr.lower_vars fff 1 1))
        (expr.lower_vars fr 1 1))
| (expr.app a b) := expr.app (simplify_tree_helper a) (simplify_tree_helper b)
| (expr.lam v b t e) := expr.lam v b (simplify_tree_helper t) (simplify_tree_helper e)
| (expr.pi v b t e) := expr.pi v b (simplify_tree_helper t) (simplify_tree_helper e)
| x := x

meta def beq_exp : expr → expr → bool
| a b := ff

meta def update_state_reference : ℕ → expr → option expr
| n (expr.app (expr.app (expr.app ps hhh) eee) (expr.var (n1))) :=
      if (n+1)=n1 then some (expr.var n) else none
| n (expr.var n1) :=
  if (n+1)=n1 then none else some (expr.var n1)
| n (expr.app a b) := match update_state_reference n a with
                      | none := none
                      | some aa := match update_state_reference n b with
                                   | none := none
                                   | some bb := (expr.app aa bb)
                                   end
                      end
| n (expr.lam v b t e) := match update_state_reference (n+1) t with
                          | none := none
                          | some aa := match update_state_reference (n+1) e with
                                       | none := none
                                       | some bb := (expr.lam v b aa bb)
                                       end
                          end
| n (expr.pi v b t e) := match update_state_reference (n+1) t with
                         | none := none
                         | some aa := match update_state_reference (n+1) e with
                                      | none := none
                                      | some bb := (expr.pi v b aa bb)
                                      end
                         end
| n x := some x

meta def simplify_override_predicate_helper : expr → expr
| (expr.lam st b stt
      (expr.app
        (expr.app predicate (expr.lam eev bb eet prr))
        (expr.app
          (expr.app
            (expr.app (expr.app pm hhh) eee)
            (expr.app (expr.app (expr.app pf hhha) eeea) (expr.var 0)))
          (expr.app (expr.app (expr.app `(override)
            (expr.app
                (expr.app (expr.app ps hhhb) eeeb)
                (expr.var 0)))
            vv)
          ee)))) :=
    match update_state_reference 0 (replace_varn_helper 0
                                  (expr.app (expr.app (expr.app `(override)
                                    (expr.app
                                      (expr.app (expr.app ps hhhb) eeeb)
                                      (expr.var 0)))
                                      vv) ee)
                                    prr) with
    | some r := (expr.app predicate (expr.lam eev bb eet
                  (expr.lower_vars r 2 1)))
    | none := (expr.lam st b stt
      (expr.app
        (expr.app predicate (expr.lam eev bb eet prr))
        (expr.app
          (expr.app
            (expr.app (expr.app pm hhh) eee)
            (expr.app (expr.app (expr.app pf hhha) eeea) (expr.var 0)))
          (expr.app (expr.app (expr.app `(override)
            (expr.app
                (expr.app (expr.app ps hhhb) eeeb)
                (expr.var 0)))
            vv)
          ee))))
    end
                       

| (expr.app a b) := expr.app (simplify_override_predicate_helper a) (simplify_override_predicate_helper b)
| (expr.lam v b t e) := expr.lam v b (simplify_override_predicate_helper t) (simplify_override_predicate_helper e)
| (expr.pi v b t e) := expr.pi v b (simplify_override_predicate_helper t) (simplify_override_predicate_helper e)
| x := x

meta def xxx : expr → expr
| e := `(absCompose absNone absNone (empty_heap,empty_env)).

meta def simplify_override : tactic unit :=
do { t ← target,
     tgt ← instantiate_mvars t,
     trace "input333333",
     trace tgt.to_raw_fmt,
     nt ← some (simplify_override_helper tgt),
     trace "output prelim",
     trace nt.to_raw_fmt,
     trace "testit3",
     qq ← some (xxx tgt),
     trace qq.to_raw_fmt,
     assert `xxx nt,swap,admit
    }
meta def simplify_override2 : tactic unit :=
do { t ← target,
     tgt ← instantiate_mvars t,
     trace "input",
     trace tgt.to_raw_fmt,
     nt ← some (simplify_override_helperb tgt),
     trace "output",
     trace nt.to_raw_fmt,
     trace "testit112",
     assert `xxx nt,swap,admit
    }

meta def simplify_override_predicate : tactic unit :=
do { t ← target,
     tgt ← instantiate_mvars t,
     trace "input1",
     trace tgt.to_raw_fmt,
     nt ← some (simplify_override_predicate_helper tgt),
     trace "output2",
     trace nt.to_raw_fmt,
     trace "testit",
     assert `xxx nt,swap,admit
    }

meta def simplify_tree : tactic unit :=
do { t ← target,
     tgt ← instantiate_mvars t,
     trace "input1",
     trace tgt.to_raw_fmt,
     nt ← some (simplify_tree_helper tgt),
     trace "output2",
     trace nt.to_raw_fmt,
     trace "testit",
     assert `xxx nt,swap,admit
    }


@[simp] theorem dist_conj (a : absState) (b : absState) (f : imp_state → imp_state) (st : imp_state) :
    (absCompose a b) (f st) = (absCompose (λ st, a (f st)) (λ st, b (f st))) st :=
begin
    admit
end

@[simp] theorem dist_exists_lambda (t:Type) (a: imp_state → Prop) (st : imp_state) (f : imp_state → imp_state):
    absExists (λ (v:t), a) (f st)=absExists (λ (v:t), (λ st, a (f st))) st :=
begin
    admit
end

@[simp] theorem dist_absPredicate (f: env → Prop) (v : ident)
    (e : ℕ) (st : imp_state) :
    absPredicate f (override_state v e st)=
    (absPredicate (λ env, f (override env v e)) st)  :=
begin
    admit
end

@[simp] theorem dist_absTree (r : env → ℕ) (s : ℕ) (f : list ℕ)
                             (st : imp_state) (v : ident) (e : ℕ)
                             (vv : Value) :
    (absTree r s f vv) (override_state v e st)=
    (absTree (λ ee, r (override ee v e)) s f vv) st :=
begin
    admit
end

@[simp] theorem dist_absExistsAbsTree (r : env → ℕ) (s : ℕ) (f : list ℕ)
                             (st : imp_state) (v : ident) (e : ℕ) :
    absExists (absTree r s f) (override_state v e st)=
    absExists (absTree (λ ee, r (override ee v e)) s f) st :=
begin
    admit
end