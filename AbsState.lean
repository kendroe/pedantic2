-------------------------------------------------------------------
-- The PEDANTIC (Proof Engine for Deductive Automation using Non-deterministic
-- Traversal of Instruction Code) verification framework
--
-- Developed by Kenneth Roe
-- For more information, check out www.cs.jhu.edu/~roe
--
-- AbsState.lean
-- This file contains a model of the abstract state template.  The function realizeState relates
-- these abstract states to concrete states.  Key top level
-- definitions:
--    Value
--    absExp
--    absState
--    absEval
--    realizeState
--    supportsFunctionality
--
-------------------------------------------------------------------

 import .impHeap


open tactic
open monad
open expr
open smt_tactic

-------------------------------------------------------------------
--
-- absHeap, the abstract heaps
--
-------------------------------------------------------------------

 def stateProp := imp_state -> Prop

-------------------------------------------------------------------
--
-- This section builds up the definition of composing abstract states.
--
-------------------------------------------------------------------

def compose_heaps (h1 h2 : heap) : heap := λ x, h1 x <|> h2 x 
      
def concreteCompose (s1 : imp_state) (s2 : imp_state) (s : imp_state) : Prop :=
    (s1.snd)=(s2.snd) ∧
    (s.snd)=(s1.snd) ∧
    (∀ v, (s1.fst) v=option.none ∨ (s2.fst) v=option.none) ∧
    compose_heaps (s1.fst) (s2.fst)=(s.fst)
    
theorem composeEnvPropagate1 :
    ∀ s1 s2 s v,
    concreteCompose s1 s2 s →
    s1.snd v = s.snd v :=
begin
    intro, intro, intro, intro, intro,
    unfold concreteCompose at *, destruct a, intros,
    destruct right,intro, intro, rw left_1
end.

theorem composeEnvPropagate2 :
    ∀ s1 s2 s v,
    concreteCompose s1 s2 s →
    s2.snd v = s.snd v :=
begin
    intro, intro, intro, intro, intro,
    unfold concreteCompose at *, destruct a, intros,
    destruct right,intro,intro,
    rewrite left_1, rewrite left
end

--
-- This is the main definition for composing abstract states
--
def composeAbsStates : stateProp → stateProp → stateProp :=
        (λ as1 as2 sr, (∃ h1 h2, 
                           (as1 h1 ∧
                           as2 h2 ∧
                           (∀ v, (h1.fst v=option.none ∨
                                  h2.fst v=option.none)) ∧
                           (h1.fst)=(h2.fst) ∧
                           (sr.fst)=(h1.fst) ∧
                           (∀ x, sr.fst x = compose_heaps (h1.fst) (h2.fst) x))
              )).

-------------------------------------------------------------------
--
-- This section builds up the definition of absState and contains a few
-- functions for returning information about absState objects.
--
-------------------------------------------------------------------

def absVar := ℕ

--def absHeap := (λ h hpred (x : imp_state), (h = x.fst ∧ hpred x.fst ∧
--               (∀ v, x.snd v=0)))

--def bind {ev} := ℕ -> option ev.

-- Value is the type used for the values returned when evaluating an absExp
inductive Value : Type
| NatValue : ℕ -> Value
| ListValue : list Value -> Value
| NoValue : Value

instance : inhabited Value := ⟨Value.NoValue⟩

-- Here is the definition for expressions.
-- It takes three parameters in defining its semantics:
--     ev - the type of the OtherType case in Value
--     eq - an equality function over ev
--     f - a function defining the semantics of AbsFun--this usually includes definitions for
--         many basic operators such as addition
--
--inductive  absExp : Type
--| AbsConstVal : (@Value unit) -> absExp
--| AbsVar : ident -> absExp
--| AbsQVar : absVar -> absExp
--| AbsFun : ident -> list absExp -> absExp.

-- Special functions for managing separation logic

mutual def rangeSet, rangeSetList
with rangeSet : Value -> option (list nat)
| (Value.ListValue ((Value.NatValue loc)::r)) :=
  (loc::(rangeSetList r))
| (Value.NatValue _) := option.some list.nil
| _                  := option.none
with rangeSetList : list Value → (list nat)
| (f::r) := match rangeSet f
                     with
                     | some l := l++(rangeSetList r)
                     | _     := []
                     end
| _ := @list.nil ℕ.

def treeRecords (v:Value) : list ℕ :=
    (rangeSet v).get_or_else []

def inTree : Value → Value → Prop
| (Value.NatValue x) v := x ∈ treeRecords v
| (Value.ListValue (Value.NatValue x :: _)) v := x ∈ treeRecords v
| _ v := false

def rangeNumeric : ℕ → ℕ → list ℕ
| s (e+1) :=
    if beq_nat (e+1) s then list.nil
    else if beq_nat s e then (e::list.nil)
    else e::(rangeNumeric s e)
| s 0 := list.nil

mutual def fullRangeSet, fullRangeSetList
with fullRangeSet : Value -> option (list nat)
| (Value.ListValue ((Value.NatValue loc)::r)) :=
   match fullRangeSetList r with
   | option.some ll := option.some (append (rangeNumeric loc (loc+1+(list.sizeof r))) ll)
   | _              := option.none
   end
| (Value.NatValue _) := option.some list.nil
| _                  := option.none
with fullRangeSetList : list Value → option (list nat)
| (f::r) := match fullRangeSet f
                     with
                     | some l :=
                         match fullRangeSetList r with
                         | option.some ll := (some (append l ll))
                         | _ := option.none
                         end
                     | _     := option.none
                     end
| _ := @list.nil ℕ.

--def listmem : ℕ → list ℕ → bool
--| _ list.nil := ff
--| e (list.cons a b) := if beq_nat e a then tt else listmem e b

def Rmember : ℕ → Value → bool
| a v := match (rangeSet v) with
         | option.some l := a ∈ l 
         | option.none := ff
         end

def Rinclude : ℕ → Value → bool
| a v := match (fullRangeSet v) with
         | option.some l := a ∈ l 
         | option.none := ff
         end


/- mutual def findRecord, findRecordHelper
with findRecord : ℕ → Value → (list Value)
| l (Value.ListValue ((Value.NatValue x)::r)) :=
                 if beq_nat x l then
                     ((Value.NatValue x)::r)
                 else findRecordHelper x r
| _ _ := list.nil
with findRecordHelper : ℕ → (list Value) → (list Value)
| _ list.nil := list.nil
| v (f::r) := match findRecord v f with
              | list.nil := findRecordHelper v r
              | x        := x
              end.   -/

-- place holder
def find (n:ℕ) (v:Value) : Value := v.

-- Some auxiliary definitions useful abstract states
inductive fold_compose : list imp_state → imp_state → Prop
| FCNil : ∀ x, fold_compose list.nil (inhabited.default heap,x)
| FCCons : ∀ f r state rstate,
             fold_compose r rstate →
             concreteCompose rstate f state →
             fold_compose (f::r) state

inductive allFirsts {t1} {t2} : list t1 → list (t1 × t2) → Prop
| AFNil : allFirsts list.nil list.nil
| AFCons : ∀ fx fy r r', allFirsts r r' → allFirsts (fx::r) ((fx,fy)::r')

inductive allSeconds {t1} {t2} : list t1 → list (t2 × t1) → Prop
  | ASNil : allSeconds list.nil list.nil
  | ASCons : ∀ fx fy r r', allSeconds r r' → allSeconds (fy::r) ((fx,fy)::r').

inductive anyHeap : ℕ → ℕ → heap → Prop
    | AnyHeapBase : ∀ start,
                    anyHeap start 0 (λ x, none)
    | AnyHeapNext : ∀ start next heap y,
                    anyHeap (start+1) next heap ->
                    anyHeap start (next+1)
                            (λ x, if beq_nat x start then some y else heap x).

inductive Rcell : ℕ → (list ℕ) → heap → ℕ → Prop
  | RCellBase : forall l ll h,
                Rcell l ll h l
  | RCellNext : forall l ll index (h : heap) n nn,
                index ∈ ll=tt →
                h (n+index)=some nn →
                Rcell l ll h n →
                Rcell l ll h nn.

def combine_heap (h1 : heap) (h2 : heap) (x :ℕ) :=
    match h1 x with
    | none := h2 x
    | some y := some y
    end.

inductive mergeHeaps : (list heap) → heap → Prop
  | MHBase : mergeHeaps list.nil (λ x, none)
  | MHNext : ∀ (f : heap) (r :list heap) (h1 : heap) (h2 : heap) (h : heap),
             mergeHeaps r h2 →
             (∀ (x : ℕ), h1 x=none ∨ h2 x=none) →
             h = (combine_heap h1 h2) →
             mergeHeaps (f::r) h.

inductive heapWithIndexList : (list ℕ) → (list heap) → (list Value) → (list (nat × heap × Value)) → Prop
| HWIBase : heapWithIndexList list.nil list.nil list.nil list.nil
| HWINext : ∀ ir hr ihr br i h b,
            heapWithIndexList ir hr br ihr ->
            heapWithIndexList (i::ir) (h::hr) (b::br) ((i,h,b)::ihr).


def findIndex : ℕ → heap → list (nat × heap × Value) → Value
| n h list.nil :=
             match h n with
             | some x := Value.NatValue x
             | none   := Value.NatValue 0
             end
| n h ((nn,hh,v)::r) := if beq_nat n nn then v else findIndex n h r

def buildList : ℕ → ℕ → heap → list (nat ×  heap ×  Value) → list Value
| i 0 h l := list.nil
| i (s+1) h l := (findIndex i h l)::(buildList (i+1) s h l)

inductive ihmem : ℕ → heap → Value → list (ℕ × heap × Value) → Prop
| IHBase : ∀ (n : ℕ) (h : heap) (v : Value) (hl : list (ℕ × heap × Value)),
            ihmem n h v ((n,h,v)::hl)
| IHNext : ∀ n h v f hl,
             ihmem n h v hl →
             ihmem n h v (f::hl).

--
-- Recursive definition for the TREE construct--used in the definition of basicState
--
-- Parameters:
--    #1 - root of tree
--    #2 - size of each node in the tree
--    #3 - list of offsets to fields for each node
--    #4 - functional representation of the tree
--    #5 - concrete heap (Must be exact heap for the tree)
--
inductive Tree : ℕ → ℕ → (list ℕ) → Value → heap → Prop
| TreeNext : ∀ root size indices heaps ihlist h0 h1 heap values vals,
            size > 0 →
            anyHeap root size h0 →
            heapWithIndexList indices heaps values ihlist →
            not(root=0) →
            (∀ i h v x, ihmem i h v ihlist → some x=h0 (root+x) → Tree x size indices v h) →
            mergeHeaps heaps h1 →
            (∀ l, (h1 l=none ∨ h0 l=none)) →
            heap = combine_heap h1 h0 ->
            vals = buildList root size heap ihlist ->
            Tree root size indices (Value.ListValue ((Value.NatValue root)::vals)) heap
  | TreeBase : forall size index (h : ℕ → option ℕ),
            size > 0 →
            (∀ (v : ℕ), h v=none) →
            Tree 0 size index (Value.ListValue ((Value.NatValue 0)::list.nil)) h

def absTree (r: env → ℕ) (s:ℕ) (f: list ℕ) (v:Value) (st: imp_state) := Tree (r st.snd) s f v st.fst.

-- Path stuff
inductive anyHeapv : ℕ → ℕ → heap → (list Value) → Prop
| AnyHeapvBase : ∀ start, anyHeapv start 0 (λ x, none) list.nil
| AnyHeapvNext : ∀ start next heap y r,
                     anyHeapv (start+1) next heap r →
                     anyHeapv start (next+1) (λ x, if beq_nat x start then some y else heap x)
                                    ((Value.NatValue y)::r).

inductive valueIndexList : (list ℕ) → (list Value) → (list (ℕ × Value)) → Prop
| VIBase : valueIndexList list.nil list.nil list.nil
| VINext : ∀ ir br i b ibr,
           valueIndexList ir br ibr →
           valueIndexList (i::ir) (b::br) ((i,b)::ibr).

inductive imem : ℕ → Value → list (ℕ × Value) → Prop
| IBase : ∀ (n : ℕ) (v : Value) hl,
          imem n v ((n,v)::hl)
| INext : ∀ (n : ℕ) (v : Value) f hl,
          imem n v hl →
          imem n v (f::hl).

inductive updateRec : list (nat × Value) → ℕ → list Value → list Value → Prop
| UBase : ∀ n vl,
          updateRec vl n list.nil list.nil
| UMem : ∀ n v vl or nr x,
         imem n v vl →
         updateRec vl (n+1) or nr →
         updateRec vl n (x::or) (v::nr)
| UDef1 : ∀ n v vl or nr x,
          not(imem n v vl) →
          updateRec vl (n+1) or nr →
          updateRec vl n ((Value.NatValue x)::or) ((Value.NatValue x)::or)
| UDef2 : ∀ n v vl or nr x rr,
          not(imem n v vl) →
          updateRec vl (n+1) or nr →
          updateRec vl n ((Value.ListValue ((Value.NatValue x)::rr))::or) ((Value.NatValue x)::or).

def nth {t} : ℕ → list t → t → t
| 0 (f::r) d := f
| (n+1) (f::r) d := nth n r d
| _ _ d := d.

def nthval: ℕ → Value → Value
| n (Value.ListValue l) := nth x l Value.NoValue
| _ _ := Value.NoValue

inductive Path : ℕ → ℕ → list ℕ → Value → Value → Prop
  | PathNext : ∀ (root : ℕ) (size : ℕ) indices (baseData : Value) rec vals ivals rec2,
            size > 0 →
            not(root=0) →
            --((Value.NatValue root)::rec) = findRecord root baseData →
            valueIndexList indices vals ivals →
            --(∀ i x v r, imem i v ivals →
            --            ((Value.ListValue ((Value.NatValue x)::r))=(nth i rec Value.NoValue) ∧
            --            Path x size indices baseData v))) →
            updateRec ivals 0 rec rec2 →
            Path root size indices baseData (Value.ListValue (Value.NatValue root::rec2))
  | PathBase : ∀ size l h,
            size > 0 →
            Path 0 size l h (Value.ListValue ((Value.NatValue 0)::list.nil)).

--
-- Rmember is a predicate used in AbsPredicate constructs to determine whether a nat
-- is in fact a pointer to the head of any of the nodes in the list or tree represented
-- by an RFun construct.
--
-- Parameters:
--    l - location to test
--    tree - a tree (which is the same form as parameter #4 to tree above
--
-- This definition is used in basicEval for the 'inTree' function
--

theorem Rmember1 { a:ℕ } { v:Value } { l:list ℕ } :
        some l = rangeSet v → a ∈ l=Rmember a v:= begin
        intros, unfold Rmember, rewrite ← a_1,
        simp only [Rmember._match_1], admit
end

theorem rootIsMemberAux (root:ℕ) (r:list Value) :
        Rmember root (Value.ListValue (Value.NatValue root :: r)) = to_bool true :=
begin
    rewrite ← Rmember1, swap, unfold rangeSet,refl,
    unfold listmem, rw beq_refl, simp
end

theorem rootIsMember : forall root size fields heap (v : Value),
    root ≠ 0 ->
    Tree root size fields v heap ->
    Rmember root v=true := begin
    intros, cases a_1,
    rw rootIsMemberAux, simp at a, cases a
end

inductive strip_nat_values : (list Value) -> (list ℕ) -> Prop
| SNVNil : strip_nat_values list.nil list.nil
| SNVCons : forall v a b,
            strip_nat_values a b ->
            strip_nat_values ((Value.NatValue v)::a) (v::b).

-- Separation connectives
def absCompose : (imp_state → Prop) → (imp_state → Prop) → imp_state → Prop
| s1 s2 st := ∃ st1 st2,
              (s1 st1 ∧
               s2 st2 ∧
               concreteCompose st1 st2 st).

infix `**`:5 := absCompose.

def absMagicWand : (imp_state → Prop) → (imp_state → Prop) → imp_state → Prop
| s1 s2 st := ∀ st1 st2,
              s1 st1 →
              s2 st2 →
              concreteCompose st st2 st1.

def absOrCompose : (imp_state → Prop) → (imp_state → Prop) → imp_state → Prop
| s1 s2 st := (s1 st ∨ s2 st)

-- Separation leaves
def absEmpty : imp_state → Prop
| st := ∀ (x : ℕ), st.fst x=none

def absAny : imp_state → Prop
| _ := true.

def absNone : imp_state → Prop
| _ := false.

-- Non-trivial leaves
def absPredicate : (env → Prop) → imp_state → Prop
| p s := p s.snd.

def absStateTree : (env → ℕ) → (env → ℕ)→ (env → list ℕ) → (env → Value)  → imp_state → Prop
| root size fields fvalue st := Tree (root st.snd) (size st.snd) (fields st.snd) (fvalue st.snd) st.fst.

def absStatePath : (env → ℕ) → (env → ℕ)→ (env → list ℕ) → (env → Value)  → (env → Value) → imp_state → Prop
| root size fields fvalue path st := Path (root st.snd) (size st.snd) (fields st.snd) (fvalue st.snd) (path st.snd).

def absStateArray : (env → ℕ) → (env → ℕ)→ (env → list Value) → imp_state → Prop
| root size values st := anyHeapv (root st.snd) (size st.snd) st.fst (values st.snd).

def absCell : (env → ℕ) → (env → ℕ) → imp_state → Prop
| l v h := (h.fst (l h.snd))=some (v h.snd) ∧
            (l h.snd ≠ 0 →
            (∀ (x : ℕ), x ≠ (l h.snd) → h.fst x=none)).

-- Separation updaters
def absUpdateLoc : (env → ℕ) → (env → ℕ) → (imp_state → Prop) → imp_state → Prop
| loc val s str := ∀ st, s st →
                   (st.snd = str.snd ∧
                    str.fst = (λ v, if beq_nat v (loc st.snd) then val st.snd else (st.fst) v)).

def absUpdateState : (imp_state → Prop) → (imp_state → Prop) → (imp_state → Prop) → (imp_state → Prop)
| s m p := absCompose (absMagicWand s m) p.

-- Separation quantifiers
def absAll {t : Type} : (t → imp_state → Prop) → (imp_state → Prop) :=
    (λ (st : t → imp_state → Prop) (i : imp_state), (∀ (q:t), (st q i)))

def absAllU {t : Type} : (list t) → (t → imp_state → Prop) → (imp_state → Prop)
| (f::r) st := absCompose (st f) (absAllU r st)
| list.nil st := absEmpty

def absExists {t : Type} : (t → imp_state → Prop) → (imp_state → Prop) :=
    (λ (st : t → imp_state → Prop) (i : imp_state), (∃ (q:t), (st q i)))

def absExistsU {t : Type} : list t → (t → imp_state → Prop) → (imp_state → Prop)
| (f::r) st := absOrCompose (st f) (absExistsU r st)
| list.nil st := absNone

def absEach {t : Type} : (list t) → (t → imp_state → Prop) → (imp_state → Prop)
| (f::r) st := absCompose (st f) (absEach r st)
| list.nil st := absEmpty.

def absState := imp_state → Prop

def absExp {t} := env → t

def realizeState (st : absState) (s : imp_state) : Prop := st s

def absEval {t} (e : env) (exp : env → t) := exp e

