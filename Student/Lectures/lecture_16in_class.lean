def from_ab_pair_a {α β : Type} : α × β → α
| (a,_) => a
#check @Prod
def from_AB_true_a_true {α β : Prop} : And α β → α
|⟨a, _ ⟩ => a
-- notation for prop instead of prod "\<" and "\>"
def x := (1,2)
/-!


-/


#check Or

#check @And
#eval x.1
#eval x.2
def from_ab_proof_to_a_proof {α β : Prop}: α ∧ β → α
|And.intro (a) (_) => a

def sum_elim {α β γ : Type } : (α ⊕ β) → (α → γ) → (β → γ) → γ
| Sum.inl a, x, _ => x a
| Sum.inr b, _, y => y b

def or_elim { α β γ : Prop} : (α ∨ β ) → (α → γ ) → (β → γ) → γ
| Or.inl a, x, _ => x a
| Or.inr b, _ , y =>y b


theorem and_comm { P Q : Prop } : (P ∧ Q → Q ∧ P) ∧ (Q ∧ P → P ∧ Q) :=
And.intro
  (fun ⟨ P, Q⟩ => ⟨ Q, P⟩ )
  (fun ⟨ Q, P⟩ => ⟨ P, Q⟩ )
