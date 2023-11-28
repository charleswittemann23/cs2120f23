/-!
Formalize the following logical arguments. Hint: use the variable command to introduce assumed types and such, as we did in class. Use #check to express the informal propositions that follow in the formal logic of Lean.

1. Every dog likes some cat.

2. If any dog, d, likes any dog, g, and that dog, g, likes any dog, w, then d likes w.

3. If any cat, c, likes any cat, d, then d also likes c.

4. Every cat, c, likes itself.

5. If every cat likes every other cat, and c and d are cats, then c likes d.

Finally, give a formal proof in Lean of the proposition in problem #5.

-/


variable
(Dog : Type) --there exists a dog
(doge: Dog) --doge is a dog
(Cat : Type) -- there exists a cat
(c : Cat) -- c is a cat
(d : Cat)
(Likes1 : Dog → Cat → Prop) -- a proof of a Dog liking a cat
(Likes2 : Dog → Dog → Prop)
(Likes3 : Cat → Cat → Prop)

--1.
#check ∀ (d : Dog), ∃ (c : Cat), Likes1 d c

--2.
#check  ∀ (d : Dog), ∀  (d1: Dog), ∀  (d2 : Dog),
Likes2 d d1 ∧ Likes2 d1 d2 → Likes2 d d2
--3.
#check ∀ (c : Cat), ∃ (c1 : Cat), Likes3 c c1 → Likes3 c1 c
-- 4.
#check ∀ (c : Cat), Likes3 c c
-- 5.
example: (∀ (c1: Cat), ∀ (c2: Cat), Likes3 c1 c2) → ( (c: Cat) →  (d : Cat) → Likes3 c d)
| proofofcats, c, d => proofofcats c d
