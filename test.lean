import init.data.option.basic

open tactic
open monad
open expr
open smt_tactic

theorem nonethm {t} : (none <|> none)=@none t:= rfl.

theorem nonethm2 {t} {x:option t} : (x <|> none)=x:= begin
    cases x;refl
end


theorem th : ∀ (a:ℕ) (b:ℕ), a ≠ b → (if a=b then 5 else 3)=3 :=
begin
    intros, simp *
end

def f (x : ℕ) := x+1

theorem fsimp : f 0 = 1 :=
begin
    unfold f
end

theorem fsimp2 {e : ℕ } : (λ x : ℕ, x+(f 0)=1+x)=(λ x : ℕ, 1=1) :=
begin
    rewrite fsimp, simp
end

theorem fsimp3 { x : ℕ } : x=0 → f x = 1 :=
begin
    intro, unfold f, rw a
end

theorem fsimp4 {e : ℕ } : e=0 → (λ x : ℕ, x+(f x)=1+x) e=(λ x : ℕ, 1=1) e :=
begin
    intro, conv
    begin
        to_lhs,
        simp, rw a,
        funext,
        rw fsimp3, skip, reflexivity
    end
end

meta def simplifyProd : expr → expr
| (expr.app
    (expr.app
      (expr.app `(prod.fst) tt1a)
      tt1b)
     (expr.app
        (expr.app
          (expr.app 
            (expr.app `(prod.mk) tt1) tt2) a) b)) := a
--| `((λ x, (%%f) x) (%%z)) := `(%%f (%%z+1))
| (expr.app a b) := expr.app (simplifyProd a) (simplifyProd b)
| (expr.lam v b t e) := expr.lam v b (simplifyProd t) (simplifyProd e)
| (expr.pi v b t e) := expr.pi v b (simplifyProd t) (simplifyProd e)
| x := x

theorem testit (f:ℕ) (s:ℕ) :
    (f,s).fst=f :=
begin
   do {
       t ← target,
       trace "Start",
       trace t.to_raw_fmt,
       tq ← some (simplifyProd t),
       trace tq.to_raw_fmt,
       assert `hhhq tq,tactic.swap,admit
   },
   refl
end

theorem test : 1=2 :=
begin
    suffices hh:(3=4), admit,
end

meta def test : expr → expr
| (expr.lam vn b ttt (expr.app f s)) :=
      (expr.lam vn b ttt 
          (expr.app f (expr.app (expr.app `(nat.add) s) `(1))))
| x := x.

theorem junk { p : Prop } { q : Prop } : (p ∨ false ∨ (q ∧ false))=p :=
begin
    sorry
end

theorem test_split { P : ℕ → Prop } { Q : ℕ → Prop } { R : ℕ → Prop } { S : ℕ → Prop } :
    (∀ x, P x ∧ (Q x ∨ R x)) → (∀ x, Q x → S x) → (∀ x, R x → S x) → (∀ x, P x ∧ S x) :=
begin
    intros h h' h'' x,
    specialize h x,
    specialize h' x,
    specialize h'' x, split, cases h, apply h_left,
    cases h, cases h_right, apply h', apply h_right,
    apply h'', apply h_right
end

inductive Value : Type
| NatValue : ℕ -> Value
| ListValue : list Value -> Value
| NoValue : Value

mutual def rangeSet, rangeSetList
with rangeSet : Value -> option (list nat)
| (Value.ListValue ((Value.NatValue loc)::r)) :=
   match rangeSetList r with
   | option.some ll := option.some (loc::ll)
   | _              := option.none
   end
| (Value.NatValue _) := option.some list.nil
| _                  := option.none
with rangeSetList : list Value → option (list nat)
| (f::r) := match rangeSet f
                     with
                     | some l :=
                         match rangeSetList r with
                         | option.some ll := (some (append l ll))
                         | _ := option.none
                         end
                     | _     := option.none
                     end
| _ := @list.nil ℕ.

def beq_nat : ℕ → ℕ → bool
| 0 0 := tt
| (x+1) (y+1) := (beq_nat x y)
| (x+1) 0 := ff
| 0 (x+1) := ff

def listmem : ℕ → list ℕ → bool
| _ list.nil := ff
| e (list.cons a b) := if beq_nat e a then tt else listmem e b

def Rmember : ℕ → Value → bool
| a v := match (rangeSet v) with
         | option.some l := listmem a l 
         | option.none := ff
         end

theorem Rmember1 { a:ℕ } { v:Value } { l:list ℕ } :
        some l = rangeSet v → listmem a l=Rmember a v:= begin
        intros, unfold Rmember, rewrite ← a_1,
        simp only [Rmember._match_1]
end

theorem rootIsMemberAux (root:ℕ) (r:list Value) :
        Rmember root (Value.ListValue (Value.NatValue root :: r)) = to_bool true :=
begin
    rewrite ← Rmember1, swap,
end

theorem x: ∃ x, x=5 :=
begin existsi _, ..
end

def qq (x : ℕ) := x.

inductive ev : ℕ → Prop
| Base : ev 0
| Inductive : forall x, ev x → ev (x+2).

def evv (x :ℕ → ℕ) (y: ℕ):=
    match x y with
    | 0 := tt
    | 1 := ff
    | _ := tt
    end

theorem test: ∀ x (f: ℕ → ℕ), f x=0 → evv f x :=
begin
    intros, unfold evv, rw a, simp only [evv._match_1], rw a, exact rfl,
end
 
inductive od : ℕ → Prop
| Base : od 1
| Inductive : forall x, od x → od x.

inductive ev2 : ℕ → ℕ → ℕ → Prop
| Base : ∀ (a:ℕ) (b:ℕ) (c:ℕ), ev a → b=qq c → ev2 a (b*2) c.

theorem dd : (λ (x:ℕ), x*2)=(λ (x:ℕ), x+x) := begin
    have h:∀ x, x*2=x+x, intro, admit,
    rw h
end

theorem evod (x:ℕ) (y:ℕ) (z:ℕ): ev2 x y z → od (x+1) :=
begin
    intro, cases a, simp, apply od.Base,

    simp, simp at a,
end

def xeval (a : ℕ) (b : ℕ) := if a=0 then 0 else b.

def beq_nat : ℕ → ℕ → bool
| 0 0 := tt
| (x+1) (y+1) := (beq_nat x y)
| (x+1) 0 := ff
| 0 (x+1) := ff

theorem testdummy : (λ (l : ident), ite ↥(beq_nat v l) v2 (ite ↥(beq_nat v l) v1 (env l))) =
    λ (l : ident), ite ↥(beq_nat v l) v2 (env l)
begin
end

meta def evaluate_xeval_helper : expr → expr
| `(xeval %%x %%y) :=
      (app (app (app `(ite)
                     (app (app `(beq_nat))) x `(0))
                     `(0))
                     y)
| x := x

def andFuns (a : ℕ → Prop) (b : ℕ → Prop) : ℕ → Prop :=
    (λ q, (a q) ∧ (b q)).

def existsFuns (a : ℕ → ℕ → Prop) : ℕ → Prop :=
    (λ n, (∃ (e:ℕ), a e n)).

def test := (λ x, x > 3)
def test2 := (λ x, x < 8)
def test3 := (λ (x y:ℕ), x=y)

#check existsFuns.

--meta def divide_lambda1 : name → binder_info → expr → expr → expr → expr → expr
--| n b e1 `(andFuns %%l %%r) v y :=
--      (app (app `(andFuns) (divide_lambda1 n b e1 l v y))
--                           (divide_lambda1 n b e1 r v y))
--| n b e1 x y v := (app (lam n b e1 (app x y)) v).

--meta def transform_lambda_app1 : expr → option expr
--| (app (lam n b e1 (app x y)) val) := some (divide_lambda1 n b e1 x y val)
--| _ := none.

--meta def split_lambda1 : tactic unit :=
--do { t ← target,
--     nt ← transform_lambda_app1 t,
--     (change nt) }.

meta def divide_lambda : name → binder_info → expr → expr → expr → expr
| n b e1 `(andFuns %%l %%r) y :=
      (app (app `(andFuns) (divide_lambda n b e1 l y))
                           (divide_lambda n b e1 r y))
| n b e1 `(existsFuns (λ (qqq:ℕ), %%ll)) y :=
      (app (const "existsFuns" [])
                 (lam "qqq" binder_info.default e1 (divide_lambda n b e1 (ll.lift_vars 0 1) y)))
--      (existsFuns (λ (qqq:ℕ), %%(divide_lambda n b e1 (ll.lift_vars 0 1) y)))
--| n b e1 (app (app `(existsFuns) (lam qqq bi nt ll))) yy :=
--      (app (const "existsFuns" [])
--                 (lam qqq bi nt (divide_lambda n b e1 (ll.lift_vars 0 1) yy)))
| n b e1 x y := (lam n b e1 (app x y)).

meta def transform_lambda_app : expr → option expr
| (app (lam n b e1 (app x y)) val) := some (app (divide_lambda n b e1 x y) val)
| (app `(id %%(lam n b e1 (app x y))) val) := some (app (divide_lambda n b e1 x y) val)
| _ := none

meta def split_lambda : tactic unit :=
do { t ← target,
     --trace t.to_raw_fmt,
     nt ← transform_lambda_app t,
     --trace nt.to_raw_fmt,
     change nt }

meta def test_dummy : tactic unit :=
do {
     test ← some ``((λ (v:ℕ),v=%%(@var tt 1)) 3),
     trace test.to_raw_fmt,
     admit
   }

theorem dummy : 3=4 :=
begin
    test_dummy
end

theorem test1 (v: ℕ) : id (λ (e:ℕ), (andFuns test test2) (e+1)) v :=
begin
  unfold test, unfold test2,
  split_lambda,
end

theorem test1 (v: ℕ) : (λ (e:ℕ), (andFuns test test2) (e+1)) v :=
begin
    unfold test, unfold test2,
    change (andFuns (λ (e:ℕ), test (e+1)) (λ (e:ℕ), test2 (e+1))) v,
end

theorem capture (v: ℕ) (q : ℕ) : id (λ (e:ℕ), (andFuns (existsFuns (λ x:ℕ, test3 x)) test) (e+q)) v :=
begin
    split_lambda,
    --change
    --    andFuns (existsFuns (λ (y e:ℕ), test3 y (e+q)))
    --            (λ (e:ℕ), test (e + q)) v,
end

example (p q : ℕ → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x :=
begin
  intro h,
  cases h with x px,
  constructor, left, exact px
end

theorem testit: ∀ q, ((λ (f : (ℕ → ℕ)), (λ (x:ℕ), (f x)+(f x)))
                         (λ (x:ℕ), x+1)) q = 2*q+2 :=
begin
sorry
end

theorem testdummy: ∀ a b, a → b :=
begin
    intros, have h:1+1=3 → b, admit, apply h, clear h,
end

theorem assignInExists3 {t:Type} :

 ∀ (s : t → absState) (vv:ℕ) (v:ident),

   ((λ (vv : ℕ) (st:imp_state),
       (@absExists t (λ (x:t), s x)) (st.fst,override st.snd v vv)))
   =
                   (λ (vv : ℕ), (@absExists t (λ (x:t),
                    (λ st, s x (st.fst,override st.snd v vv))))):= sorry.

theorem assignInExists1 {t:Type} :
 ∀ (s : absState) (st2 : imp_state) vv v,
   ((λ (st:imp_state), (@absExists t (λ v, s)) (st.fst,override st.snd v vv))=
                   (@absExists t (λ x, (λ st, s (st.fst,override st.snd v vv))))):= sorry.

theorem stsimp1 : ∀ (v:ident) (vv:ℕ),
    (λ (vv : ℕ) (st : imp_state),
            absExists (λ (x : Value), absTree (λ (env : env), env RR) 2 [0, 1] x)
              (st.fst, override (st.snd) v vv))=
            (λ (vv : ℕ), absExists (λ (x : Value), (λ (st : imp_state), absTree (λ (env : env), env RR) 2 [0, 1] x
              (st.fst, override (st.snd) v vv))) := sorry.

open tactic
open monad
open expr
open smt_tactic

meta def findd : expr → list expr → tactic expr
| e [] := failed
| e (h::hs) :=
    do t ← infer_type h,
    (unify e t >> return h) <|> find e hs.

meta def assumptionn : tactic unit :=
do { ctx ← local_context,
       t ← target,
       h ← findd t ctx,
       exact h }
   <|> fail "assumption tactic failed".

def g (x:ℕ) := (x+2)
def f (x:ℕ) := (x+1)