/-
# Curry Howard Corresponsdence
-/


/-
 ## Empty ==> False
-/
#check Empty

-- inductive Empty: Type

inductive Chaos : Type
--uninhabited type

def from_Empty (e : Empty) : Chaos := nomatch e
#check False

-- inductive False : Prop
--defined as empty data type because it has no proofs
def from_false {P : Prop } (p : False) : P := False.elim p --analog of nomatch in Type to False.elim in  Prop

def from_false_true (p: False ) : False = True := False.elim p --from false anything
--no introduction rule

/-
## Unit ==> True
-/
#check Unit
-- inductive PUnit : Sort  u where
-- | unit : PUnit
#check True
-- inductive True : Prop where
-- | intro : True

#check True.intro
-- no elimination rule

def proof_of_true : True := True.intro

def false_implies_true : False → True := fun x => False.elim x
                           --can also use True.intro
/-
## Prod ==> And
-/
#check Prod

/-
structure Prod (α: Type u) (β : Type v) where
 fst : α
 snd : β
-/
#check And

/-
structure And (a b : Prop) : Prop where
 intro ::
 left : a
 right : b
-/
#check And.intro

inductive birds_chirping : Prop
| yep
| boo

inductive sky_blue : Prop
| yep

#check (And birds_chirping sky_blue)

theorem both_and : And birds_chirping sky_blue := And.intro (birds_chirping.boo) (sky_blue.yep)


/-!
Proof Irrelevance
-/


namespace cs2120f23
inductive Bool : Type
 | true
 | false

 theorem proof_equal : birds_chirping.boo = birds_chirping.yep := by trivial


 -- In Prop all proofs are equivalent
 -- Choice of values in Prop can't influence computations


 /-!
  ## SUM ===> Or

 -/
#check Sum
/-!
-- inductive Sum (α : Type u) (β : Type v) where
 -- | inl (val : α) : Sum α β
  --| inr (val : β) : Sum α β
-/

#check Or
/-!
inductive Or (a b : Prop) : Prop where
  | inl (h : a) : Or a b
  | inr (h : b) : Or a b

-/
theorem one_or_other : Or birds_chirping sky_blue := Or.inl birds_chirping.boo
theorem one_or_other' : Or birds_chirping sky_blue := Or.inr sky_blue.yep

example : Or birds_chirping (0=1) := Or.inl birds_chirping.yep

--two(three?) possible proofs
example : (0=1) ∨ (1=2) := _

theorem or_comm {P Q : Prop} : P ∨ Q → Q ∨ P :=
fun d =>
  match d with
  |Or.inl p => Or.inr p
  | Or.inr q => Or.inl q


/-!
## NO ==> Not
-/
def no ( α : Type ) := α → Empty

#check Not

-- Not P is to defined ot be P → False

example : no Chaos := fun a => nomatch a

inductive Raining : Prop

example : ¬ Raining := fun (r: Raining) => nomatch r
