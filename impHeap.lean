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

instance : inhabited env := ⟨λ x, 0⟩
instance : inhabited heap := ⟨λ h, none⟩
instance : inhabited cell := ⟨none⟩

def empty_env : env := inhabited.default env
def empty_heap : heap := inhabited.default heap
def empty_cell : cell := inhabited.default cell

def imp_state := heap × env

--def beq_nat : ℕ → ℕ → bool
--| 0 0 := tt
--| (x+1) (y+1) := (beq_nat x y)
--| (x+1) 0 := ff
--| 0 (x+1) := ff

--def ble_nat : ℕ → ℕ → bool
--| 0 z := tt
--| (x+1) (y+1) := (ble_nat x y)
--| (x+1) 0 := ff

--example : beq_nat 3 3=tt := rfl.

--def beq_ident := beq_nat
instance : decidable_eq ident :=
by unfold ident; apply_instance

--theorem beq_nat00 : beq_nat 0 0 = tt := rfl.

--theorem beq_refl (n : ℕ) : beq_nat n n=tt :=
--begin
--    induction n, rewrite beq_nat00,
--
--    unfold beq_nat, rewrite n_ih
--end


--theorem beq_nat_comm (a : ℕ) : ∀ b, beq_nat a b=beq_nat b a := begin
--    induction a, intro b, destruct b, intro, rewrite a,
--    intro, intro, rewrite a, unfold beq_nat,
--
--    intro b, destruct b, intro, rewrite a, unfold beq_nat,
--
--    intro, intro, rewrite a, unfold beq_nat, rewrite a_ih
--end

def override (st : env) (v : ident) (n : ℕ) : env :=
    (λ (l : ident), if v=l then n else (st l))

def override_state (v : ident) (n : ℕ) (st : imp_state) : imp_state :=
    (st.fst,override st.snd v n)

@[simp] theorem override_eq (n : ℕ) (V : ident) (st : env) : (override st V n) V=n :=
begin
    unfold override, simp
end

@[simp] theorem override_neq (n : ℕ) (V1 : ident) (V2 : ident) (st : env) :
    V2 ≠ V1 →
    (override st V2 n) V1=st V1 := begin
    unfold override, intro, simp *
end

theorem override_shadow (x1 : ℕ) (x2 : ℕ) (k : ident) (f : env) :
   (override (override f k x1) k x2) = (override f k x2) :=
begin
    unfold override, funext, by_cases (k=l), simp *,
    simp *
end

--theorem beq_nat_eq (a : ℕ) : ∀ b, beq_nat a b=tt → a=b :=
--begin
--    induction a,
--    intro b,
--    destruct b, intro, rewrite a, unfold beq_nat, intro, reflexivity,
--    intro, intro, rewrite a, unfold beq_nat, simp,
--
--    intro b, destruct b, intro, rewrite a, unfold beq_nat, simp,
--    intro, intro, rewrite a, simp, unfold beq_nat,
--    intro, apply a_ih, apply a_1
--end

theorem override_same (x1 : ℕ) (k1 : ident) (k2 : ident) (f : env) :
  f k1 = x1 →
  (override f k1 x1) k2 = f k2 :=
begin
    intro, unfold override, by_cases (k1=k2),
    simp *, rw ← a, rw h,
    simp *
end

inductive aexp : Type
  | Num : ℕ → aexp
  | Var : ident → aexp
  | Plus : aexp → aexp → aexp
  | Minus : aexp → aexp → aexp
  | Mult : aexp → aexp → aexp
  | Eq : aexp → aexp → aexp
  | Le : aexp → aexp → aexp
  | Land : aexp → aexp → aexp
  | Lor : aexp → aexp → aexp
  | Lnot : aexp → aexp

-- Shorthand for common nats and nat operators

def A0 := (aexp.Num 0)
def A1 := (aexp.Num 1)
def A2 := (aexp.Num 2)
def A3 := (aexp.Num 3)
def A4 := (aexp.Num 4)
def A5 := (aexp.Num 5)
def A6 := (aexp.Num 6)

infix `***`:50 := aexp.Mult

infix `-*-`:40 := aexp.Minus

infix `+++`:40 := aexp.Plus

notation `!`:30 X := aexp.Var X

infix `===`:60 := aexp.Eq

infix `<<=`:60 := aexp.Le

definition x := 0
definition y := 1
definition Z := 2

--com is intended to mimic the constructs of a statement block in C or C++.

inductive com : Type
  | Skip : com
  | Load : ident -> aexp -> com
  | Store : aexp -> aexp -> com
  | Ass : ident -> aexp -> com
  | New : ident -> aexp -> com
  | Delete: aexp -> aexp -> com
  | Seq : com -> com -> com
  | If : aexp -> com -> com -> com
  | While : aexp -> com -> com
  | Call : ident -> ident -> (list aexp) -> com
  | Return : aexp -> com
  | Throw : ident -> aexp -> com
  | Catch : ident -> ident -> com -> com -> com.

notation  `SKIP` := com.Skip.
infix `;` := com.Seq.
notation l `::=`:60 v `-*->`:60 i := com.Load l v i.
notation l `-*->`:60 i `::=`:60 v := com.Store l i v.
notation l `::=`:60 a := com.Ass l a.
notation `NEW `:60 v `, ` s := com.New v s.
notation `DELETE `:60 e `, ` s := com.Delete e s.
notation `WHILE `:80 b ` DO ` c ` LOOP `:80 := com.While b c.
notation `IF `:80 e1 ` THEN ` e2 ` ELSE `:80 e3 ` FI`:80 := com.If e1 e2 e3.
notation `RETURN `:60 e := com.Return e.


-- Shorthand for common variable names

inductive decl : Type
  | DGlobalVar : ident -> decl
  | DFunction : ident -> (list ident) -> com -> decl.

def get_var (s : imp_state) (v : ℕ) : ℕ := (s.snd v)
def v_or_z : option ℕ → ℕ
| option.none := 0
| (option.some x) := x

def aeval : env → aexp → ℕ 
  | e (aexp.Num n) := n
  | e (aexp.Var ii) := e ii
  | e (aexp.Plus a1 a2) := (aeval e a1)+(aeval e a2)
  | e (aexp.Minus a1 a2) := (aeval e a1)-(aeval e a2)
  | e (aexp.Mult a1 a2) := (aeval e a1)*(aeval e a2)
  | e (aexp.Eq a1 a2) := if (aeval e a1)=(aeval e a2) then 1 else 0
  | e (aexp.Le a1 a2) := if (aeval e a1)≤(aeval e a2) then 1 else 0
  | e (aexp.Lnot a1) := if (aeval e a1)=0 then 1 else 0
  | e (aexp.Land a1 a2) := if (aeval e a1)=0 then 0 else aeval e a2
  | e (aexp.Lor a1 a2) := if (aeval e a1)=0 then aeval e a2 else (aeval e a1)

def aeval_list : env → (list aexp) → list nat
| s list.nil := list.nil
| s (a::b) := (aeval s a)::(aeval_list s b)

-- Auxilliary functions needed for the evaluation relation

--def bind_option {X : Type} {Y : Type} :
--option X → (X → option Y)
--→ option Y
--| none f := none
--| (some x) f := f x

--Implicit Arguments bind_option [X Y].


def range : ℕ → ℕ → ℕ → bool
| start 0 n := ff
| start (s+1) t := if t=(start+s) then tt
                   else range start s t

inductive new_heap_cells : heap → nat → nat → heap → Prop
| OHDone : ∀ h, ∀ v,
           new_heap_cells h v 0 h
| OHNext : ∀ h h' v c h'' val,
             new_heap_cells h (v+1) c h' →
             h' v = option.none →
             h'' = (λ x, if x=v then option.some val
                         else h' x) →
             new_heap_cells h v (c+1) h''

inductive clear_heap_cells : heap → nat → nat → heap → Prop
| CHDone : ∀ h v, clear_heap_cells h v 0 h
| CHNext : ∀ h h' v c val h'',
           clear_heap_cells h (v+1) c h' →
           h' v = option.some val →
           h'' = (λ x, if x=v then option.none else h' x) →
           clear_heap_cells h v (c+1) h''

inductive func_result : Type
| NoResult : func_result
| Return : nat → func_result
| Exception : ident → nat → func_result

def functions := ident → imp_state → (list ℕ) → imp_state →
                 func_result → Prop.

inductive ceval : functions -> imp_state -> com -> imp_state -> func_result -> Prop
| Skip : ∀ f (st : imp_state), ceval f st com.Skip st func_result.NoResult
| Ass  : ∀ f st a1 l,
           ceval f st (com.Ass l a1) ((st.fst),(override (st.snd) l
                 (aeval st.snd a1)))
                 func_result.NoResult
| New : ∀ f (st : imp_state) l loc e count h',
          loc ≠ 0 →
          count = aeval (st.snd) e →
          new_heap_cells (st.fst) loc count h' →
          ceval f st (com.New l e) (h',override (st.snd) l loc)
                func_result.NoResult
| Delete : ∀ f (st : imp_state) loc count l c h',
          l = aeval st.snd loc →
          c = aeval st.snd count →
          clear_heap_cells (st.fst) l c h' →
          ceval f st (com.Delete loc count) (h',st.snd)
                func_result.NoResult
| Load : ∀ f (st:imp_state) loc l val,
           option.some val = (st.fst) (aeval st.snd loc)  →
           ceval f st (com.Load l loc)
                 ((st.fst),(override (st.snd) l val))
                 func_result.NoResult
| Store : ∀ f (st : imp_state) loc val l v ov,
      v = aeval st.snd val →
      l = aeval st.snd loc →
      (st.fst) l = option.some ov →
      ceval f st (com.Store loc val)
            ((λ x, if l=x then (option.some v) else (st.fst) x),(st.snd)) func_result.NoResult
| Seq1 : ∀ f c1 c2 st st' st'' r,
      ceval f st c1 st' func_result.NoResult →
      ceval f st' c2 st'' r →
      ceval f st (com.Seq c1 c2) st'' r
| Seq2 : ∀ f c1 c2 st st' v,
      ceval f st c1 st' (func_result.Return v) →
      ceval f st (com.Seq c1 c2) st' (func_result.Return v)
| Seq3 : ∀ f c1 c2 st st' name val,
      ceval f st c1 st' (func_result.Exception name val) →
      ceval f st (com.Seq c1 c2) st'
            (func_result.Exception name val)
| IfTrue : ∀ f r (st : imp_state) (st':imp_state) b1 c1 c2,
      not(aeval st.snd b1 = 0) ->
      ceval f st c1 st' r ->
      ceval f st (com.If b1 c1 c2) st' r
| IfFalse : ∀ f r (st : imp_state) (st' : imp_state) b1 c1 c2,
      aeval st.snd b1 = 0 →
      ceval f st c2 st' r →
      ceval f st (com.If b1 c1 c2) st' r
| WhileEnd : ∀ f b1 (st : imp_state) c1,
      aeval st.snd b1 = 0 →
      ceval f st (com.While b1 c1) st func_result.NoResult
| WhileLoop1 : ∀ f (st : imp_state) st' st'' b1 c1 r,
      not(aeval st.snd b1 = 0) →
      ceval f st c1 st' func_result.NoResult →
      ceval f st' (com.While b1 c1) st'' r →
      ceval f st (com.While b1 c1) st'' r
| WhileLoop2 : ∀ f (st : imp_state) st' b1 c1 r,
      not(aeval st.snd b1 = 0) →
      ceval f st c1 st' (func_result.Return r) →
      ceval f st (com.While b1 c1) st' (func_result.Return r)
| WhileLoop3 : ∀ f (st : imp_state) st' b1 c1 name val,
      not(aeval st.snd b1 = 0) →
      ceval f st c1 st' (func_result.Exception name val) →
      ceval f st (com.While b1 c1) st'
            (func_result.Exception name val)
| Throw: ∀ f (st : imp_state) val exp v,
      val = aeval st.snd exp ->
      ceval f st (com.Throw v exp) st (func_result.Exception v val)
| Catch1: ∀ f st st' exc var code hand,
      ceval f st code st' func_result.NoResult →
      ceval f st (com.Catch exc var code hand) st' func_result.NoResult
| Catch2: ∀ f st st' exc var code hand v,
      ceval f st code st' (func_result.Return v) →
      ceval f st (com.Catch exc var code hand) st' (func_result.Return v)
| Catch3: ∀ f st st' exc var code hand v name,
      ceval f st code st' (func_result.Exception name v) →
      name ≠ exc →
      ceval f st (com.Catch exc var code hand) st'
            (func_result.Exception name v)
| Catch4: ∀ f st st' exc var code hand v st'' name r,
      ceval f st code st' (func_result.Exception exc v) →
      ceval f ((st'.fst),override (st'.snd) var v) hand st'' r →
      name ≠ exc →
      ceval f st (com.Catch exc var code hand) st'' r
| Call1: ∀ vl (st : imp_state) el (f:functions) (st':imp_state) r (fid:ident) var,
      vl = aeval_list st.snd el →
      f fid st vl st' (func_result.Return r) →
      ceval f st (com.Call var fid el) ((st'.fst),override (st'.snd) var r)
            func_result.NoResult
| Call2: ∀ vl (st : imp_state) el (f:functions) (st':imp_state) r (fid:ident) var name,
      vl = aeval_list st.snd el →
      f fid st vl st' (func_result.Exception name r) →
      ceval f st (com.Call var fid el) st' (func_result.Exception name r).


