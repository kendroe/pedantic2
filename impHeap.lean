-------------------------------------------------------------------
-- The PEDANTIC2 (Proof Engine for Deductive Automation using Non-deterministic
-- Traversal of Instruction Code) verification framework
--
-- Developed by Kenneth Roe
-- For more information, check out www.cs.jhu.edu/~roe
--
-- impHeap.lean
-- This file contains a model of the concrete state.  It was adapted from the
-- Software Foundations Imp.v model.
--
-------------------------------------------------------------------

def cell := option ℕ
def heap := ℕ → option ℕ
def ident := ℕ

def env := ident → ℕ

def empty_env (x : ℕ) := 0

def empty_heap (h : ℕ) := @none ℕ

def empty_cell := @none ℕ

def imp_state := heap × env

def beq_nat : ℕ → ℕ → bool
| 0 0 := tt
| (x+1) (y+1) := (beq_nat x y)
| (x+1) 0 := ff
| 0 (x+1) := ff

def ble_nat : ℕ → ℕ → bool
| 0 z := tt
| (x+1) (y+1) := (ble_nat x y)
| (x+1) 0 := ff

example : beq_nat 3 3=tt := rfl.

def beq_ident := beq_nat

theorem beq_nat00 : beq_nat 0 0 = tt := rfl.

theorem beq_refl (n : ℕ) : beq_nat n n=tt :=
begin
    induction n, rewrite beq_nat00,

    unfold beq_nat, rewrite n_ih
end


theorem beq_nat_comm (a : ℕ) : ∀ b, beq_nat a b=beq_nat b a := begin
    induction a, intro b, destruct b, intro, rewrite a,
    intro, intro, rewrite a, unfold beq_nat,

    intro b, destruct b, intro, rewrite a, unfold beq_nat,

    intro, intro, rewrite a, unfold beq_nat, rewrite a_ih
end

def override (st : env) (v : ident) (n : ℕ) : env :=
    (λ (l : ident), if beq_nat v l then n else (st l))

theorem override_eq (n : ℕ) (V : ident) (st : env) : (override st V n) V=n :=
begin
    unfold override,
    rewrite beq_refl,
    simp
end

theorem override_neq (n : ℕ) (V1 : ident) (V2 : ident) (st : env) :
    beq_ident V2 V1=ff →
    (override st V2 n) V1=st V1 := begin
    unfold override, unfold beq_ident, intro, rewrite a,
    simp
end

theorem override_shadow (x1 : ℕ) (x2 : ℕ) (k : ident) (f : env) :
   (override (override f k x1) k x2) = (override f k x2) :=
begin
    unfold override, apply funext, intro, destruct (beq_nat k x),
    intro,rewrite a,simp,intro,rewrite a,simp
end

theorem beq_nat_eq (a : ℕ) : ∀ b, beq_nat a b=tt → a=b :=
begin
    induction a,
    intro b,
    destruct b, intro, rewrite a, unfold beq_nat, intro, reflexivity,
    intro, intro, rewrite a, unfold beq_nat, simp,

    intro b, destruct b, intro, rewrite a, unfold beq_nat, simp,
    intro, intro, rewrite a, simp, unfold beq_nat,
    intro, apply a_ih, apply a_1
end

theorem override_same (x1 : ℕ) (k1 : ident) (k2 : ident) (f : env) :
  f k1 = x1 →
  (override f k1 x1) k2 = f k2 :=
begin
    intro, unfold override, destruct (beq_nat k1 k2), intro,
    rewrite a_1, simp, intro, rewrite a_1, simp,
    have ek : k1=k2, apply beq_nat_eq, exact a_1,
    subst k1, rewrite a
end

/---------------------------------------------------------------------------/

inductive aexp : Type
  | ANum : ℕ → aexp
  | AVar : ident → aexp
  | APlus : aexp → aexp → aexp
  | AMinus : aexp → aexp → aexp
  | AMult : aexp → aexp → aexp
  | AEq : aexp → aexp → aexp
  | ALe : aexp → aexp → aexp
  | ALand : aexp → aexp → aexp
  | ALor : aexp → aexp → aexp
  | ALnot : aexp → aexp

-- Shorthand for common nats and nat operators

def A0 := (aexp.ANum 0)
def A1 := (aexp.ANum 1)
def A2 := (aexp.ANum 2)
def A3 := (aexp.ANum 3)
def A4 := (aexp.ANum 4)
def A5 := (aexp.ANum 5)
def A6 := (aexp.ANum 6)

infix `***`:50 := aexp.AMult

infix `-*-`:40 := aexp.AMinus

infix `+++`:40 := aexp.APlus

notation `!`:30 X := aexp.AVar X

infix `===`:60 := aexp.AEq

infix `<<=`:60 := aexp.ALe

definition x := 0
definition y := 1
definition Z := 2

--com is intended to mimic the constructs of a statement block in C or C++.

inductive com : Type
  | CSkip : com
  | CLoad : ident -> aexp -> com
  | CStore : aexp -> aexp -> com
  | CAss : ident -> aexp -> com
  | CNew : ident -> aexp -> com
  | CDelete: aexp -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : aexp -> com -> com -> com
  | CWhile : aexp -> com -> com
  | CCall : ident -> ident -> (list aexp) -> com
  | CReturn : aexp -> com
  | CThrow : ident -> aexp -> com
  | CCatch : ident -> ident -> com -> com -> com.

notation  `SKIP` := com.CSkip.
infix `;` := com.CSeq.
notation l `::=`:60 v `-*->`:60 i := com.CLoad l v i.
notation l `-*->`:60 i `::=`:60 v := com.CStore l i v.
notation l `::=`:60 a := com.CAss l a.
notation `NEW `:60 v `, ` s := com.CNew v s.
notation `DELETE `:60 e `, ` s := com.CDelete e s.
notation `WHILE `:80 b ` DO ` c ` LOOP `:80 := com.CWhile b c.
notation `IF `:80 e1 ` THEN ` e2 ` ELSE `:80 e3 ` FI`:80 := com.CIf e1 e2 e3.
notation `RETURN `:60 e := com.CReturn e.


-- Shorthand for common variable names

inductive decl : Type
  | DGlobalVar : ident -> decl
  | DFunction : ident -> (list ident) -> com -> decl.

def get_var (s : imp_state) (v : ℕ) : ℕ := (s.snd v)
def v_or_z : option ℕ → ℕ
| option.none := 0
| (option.some x) := x

def aeval : env → aexp → ℕ 
  | e (aexp.ANum n) := n
  | e (aexp.AVar ii) := e ii
  | e (aexp.APlus a1 a2) := (aeval e a1)+(aeval e a2)
  | e (aexp.AMinus a1 a2) := (aeval e a1)-(aeval e a2)
  | e (aexp.AMult a1 a2) := (aeval e a1)*(aeval e a2)
  | e (aexp.AEq a1 a2) := if beq_nat (aeval e a1) (aeval e a2) then 1 else 0
  | e (aexp.ALe a1 a2) := if ble_nat (aeval e a1) (aeval e a2) then 1 else 0
  | e (aexp.ALnot a1) := if beq_nat (aeval e a1) 0 then 1 else 0
  | e (aexp.ALand a1 a2) := if beq_nat (aeval e a1) 0 then 0 else aeval e a2
  | e (aexp.ALor a1 a2) := if beq_nat (aeval e a1) 0 then aeval e a2 else (aeval e a1)

def aeval_list : env → (list aexp) → list nat
| s list.nil := list.nil
| s (a::b) := (aeval s a)::(aeval_list s b)

-- Auxilliary functions needed for the evaluation relation

def bind_option {X : Type} {Y : Type} :
option X → (X → option Y)
→ option Y
| none f := none
| (some x) f := f x

--Implicit Arguments bind_option [X Y].


def range : ℕ → ℕ → ℕ → bool
| start 0 n := ff
| start (s+1) t := if beq_nat t (start+s) then tt
                   else range start s t

inductive new_heap_cells : heap -> nat -> nat -> heap -> Prop
| OHDone : ∀ h, ∀ v,
           new_heap_cells h v 0 h
| OHNext : ∀ h h' v c h'' val,
             new_heap_cells h (v+1) c h' →
             h' v = option.none →
             h'' = (λ x, if beq_nat x v then option.some val
                         else h' x) →
             new_heap_cells h v (c+1) h''

inductive clear_heap_cells : heap -> nat -> nat -> heap -> Prop
| CHDone : ∀ h v, clear_heap_cells h v 0 h
| CHNext : ∀ h h' v c val h'',
           clear_heap_cells h (v+1) c h' →
           h' v = option.some val →
           h'' = (λ x, if beq_nat x v then option.none else h' x) →
           clear_heap_cells h v (c+1) h''

inductive func_result : Type
| NoResult : func_result
| Return : nat → func_result
| Exception : ident → nat → func_result

def functions := ident → imp_state → (list ℕ) → imp_state →
                 func_result → Prop.

inductive ceval : functions -> imp_state -> com -> imp_state -> func_result -> Prop
| CESkip : ∀ f (st : imp_state), ceval f st com.CSkip st func_result.NoResult
| CEAss  : ∀ f st a1 l,
           ceval f st (com.CAss l a1) ((st.fst),(override (st.snd) l
                 (aeval st.snd a1)))
                 func_result.NoResult
| CENew : ∀ f (st : imp_state) l loc e count h',
          (not (loc=0)) →
          count = aeval (st.snd) e →
          new_heap_cells (st.fst) loc count h' →
          ceval f st (com.CNew l e) (h',override (st.snd) l loc)
                func_result.NoResult
| CEDelete : ∀ f (st : imp_state) loc count l c h',
          l = aeval st.snd loc →
          c = aeval st.snd count →
          clear_heap_cells (st.fst) l c h' →
          ceval f st (com.CDelete loc count) (h',st.snd)
                func_result.NoResult
| CELoad : ∀ f (st:imp_state) loc l val,
           option.some val = (st.fst) (aeval st.snd loc)  →
           ceval f st (com.CLoad l loc)
                 ((st.fst),(override (st.snd) l val))
                 func_result.NoResult
| CEStore : ∀ f (st : imp_state) loc val l v ov,
      v = aeval st.snd val →
      l = aeval st.snd loc →
      (st.fst) l = option.some ov →
      ceval f st (com.CStore loc val)
            ((λ x, if beq_nat l x then (option.some v) else (st.fst) x),(st.snd)) func_result.NoResult
| CESeq1 : ∀ f c1 c2 st st' st'' r,
      ceval f st c1 st' func_result.NoResult →
      ceval f st' c2 st'' r →
      ceval f st (com.CSeq c1 c2) st'' r
| CESeq2 : ∀ f c1 c2 st st' v,
      ceval f st c1 st' (func_result.Return v) →
      ceval f st (com.CSeq c1 c2) st' (func_result.Return v)
| CESeq3 : ∀ f c1 c2 st st' name val,
      ceval f st c1 st' (func_result.Exception name val) →
      ceval f st (com.CSeq c1 c2) st'
            (func_result.Exception name val)
| CEIfTrue : ∀ f r (st : imp_state) (st':imp_state) b1 c1 c2,
      not(aeval st.snd b1 = 0) ->
      ceval f st c1 st' r ->
      ceval f st (com.CIf b1 c1 c2) st' r
| CEIfFalse : ∀ f r (st : imp_state) (st' : imp_state) b1 c1 c2,
      aeval st.snd b1 = 0 →
      ceval f st c2 st' r →
      ceval f st (com.CIf b1 c1 c2) st' r
| CEWhileEnd : ∀ f b1 (st : imp_state) c1,
      aeval st.snd b1 = 0 →
      ceval f st (com.CWhile b1 c1) st func_result.NoResult
| CEWhileLoop1 : ∀ f (st : imp_state) st' st'' b1 c1 r,
      not(aeval st.snd b1 = 0) →
      ceval f st c1 st' func_result.NoResult →
      ceval f st' (com.CWhile b1 c1) st'' r →
      ceval f st (com.CWhile b1 c1) st'' r
| CEWhileLoop2 : ∀ f (st : imp_state) st' b1 c1 r,
      not(aeval st.snd b1 = 0) →
      ceval f st c1 st' (func_result.Return r) →
      ceval f st (com.CWhile b1 c1) st' (func_result.Return r)
| CEWhileLoop3 : ∀ f (st : imp_state) st' b1 c1 name val,
      not(aeval st.snd b1 = 0) →
      ceval f st c1 st' (func_result.Exception name val) →
      ceval f st (com.CWhile b1 c1) st'
            (func_result.Exception name val)
| CEThrow: ∀ f (st : imp_state) val exp v,
      val = aeval st.snd exp ->
      ceval f st (com.CThrow v exp) st (func_result.Exception v val)
| CECatch1: ∀ f st st' exc var code hand,
      ceval f st code st' func_result.NoResult →
      ceval f st (com.CCatch exc var code hand) st' func_result.NoResult
| CECatch2: ∀ f st st' exc var code hand v,
      ceval f st code st' (func_result.Return v) →
      ceval f st (com.CCatch exc var code hand) st' (func_result.Return v)
| CECatch3: ∀ f st st' exc var code hand v name,
      ceval f st code st' (func_result.Exception name v) →
      name ≠ exc →
      ceval f st (com.CCatch exc var code hand) st'
            (func_result.Exception name v)
| CECatch4: ∀ f st st' exc var code hand v st'' name r,
      ceval f st code st' (func_result.Exception exc v) →
      ceval f ((st'.fst),override (st'.snd) var v) hand st'' r →
      name ≠ exc →
      ceval f st (com.CCatch exc var code hand) st'' r
| CECall1: ∀ vl (st : imp_state) el (f:functions) (st':imp_state) r (fid:ident) var,
      vl = aeval_list st.snd el →
      f fid st vl st' (func_result.Return r) →
      ceval f st (com.CCall var fid el) ((st'.fst),override (st'.snd) var r)
            func_result.NoResult
| CECall2: ∀ vl (st : imp_state) el (f:functions) (st':imp_state) r (fid:ident) var name,
      vl = aeval_list st.snd el →
      f fid st vl st' (func_result.Exception name r) →
      ceval f st (com.CCall var fid el) st' (func_result.Exception name r).























#check override



#check bool.tt

#check id
#check id

#print notation
theorem and_commutative (p q :Prop): p ∧ q → q ∧ p :=
begin
assume hpq : p ∧ q,
have hp : p, from and.left hpq,
have hq : q, from and.right hpq,
show q ∧ p, from and.intro hq hp
end

