/-!
# Quantifiers

Quantifiers are part of the syntax of predicate logic. They allow one
to assert that every object (∀) of some type has some property, or that
there exists (∃) (there is) at least one object of a given type with a
specified property. The syntax of such propositions is as follows:

- ∀ (x : T), P x --predicate takes a type T . Every single x of type T satisfies predicate P
- ∃ (x : T), P x -- There is at least one x of type T that satisfies predicate P

## Universal Quantification

The first proposition can be read as asserting that every value *x* of
type *T* satisfies predicate *P*. Another way to say this is that for
every *x* there is a proof of the proposition, *P x*. Another way to
say that is that there's a function that when given any *x* returns a
proof of *P x*. Indeed, that's how we prove such a proposition: show
that if given any *x* you can produce and return a proof of *P x*.
-/

example : ∀ (n : N) , True := fun n => True.intro
 example : ∃ (n: Nat), True := ⟨ 3, True.intro ⟩


 
/-
Wow, a proof for a forall propisition is
really just a proof that for any arbitrarily
selcted element of the quantified type
there is proof of the pridcate applied to that object
-/
def zornz'' (n : Nat) : n = 0 ∨ n ≠ 0 :=
match n with
  | 0       => Or.inl rfl   -- proves an equality
  | n' + 1  => Or.inr (fun _ => nomatch n')

def zornz' : (n : Nat) →  n = 0 ∨ n ≠ 0
  | 0       => Or.inl rfl   -- proves an equality
  | n' + 1  => Or.inr (fun _ => nomatch n')

def zornz : ∀ (n : Nat),  n = 0 ∨ n ≠ 0
  | 0       => Or.inl rfl   -- proves an equality
  | n' + 1  => Or.inr (fun _ => nomatch n')


/-!
### ∃ (there exists)
-/

def sl5 : ∃ (s : String), s.length = 5 := ⟨"Hello", rfl ⟩
