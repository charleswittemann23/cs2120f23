/-!
# Homework #3

Near final DRAFT. 

The purpose of this homework is to strengthen your
understanding of function composition and of enumerated
and product data types. 
-/

/-!
## Problem #1

Define a function of the following polymorphic type:
{α β γ : Type} → (β → γ) → (α → β) → (α → γ). Call it
*funkom*. After the implicit type arguments it should
take two function arguments and return a function as
a result. 
-/

def is_even:  (Nat → Bool)
| n%2 == 0
-- Answer below
def funkom {α β γ: Type} : (β → γ ) → (α → β ) → (α → γ)
| f, g => ( fun a => f ( g a ))
#check funkom is_even String.length 

#reduce funkom is_even String.length "String"
/-! 
## Problem #2

Define a function of the following polymorphic type:
{α β : Type} → (a : α) → (b : β) → α × β. Call it mkop.
-/

-- Answer below
def mkop {α β : Type} : (a: α ) → (b: β) → α × β
| a, b => Prod.mk a b 


/-! 
## Problem #3

Define a function of the following polymorphic type:
{α β : Type} → α × β → α. Call it op_left.
-/


-- Answer below
def op_left {α β : Type} : α × β→ α
| a => a.1

#eval op_left (Prod.mk 7 "Hello ")

/-! 
## Problem #4

Define a function of the following polymorphic type:
{α β : Type} → α × β → β. Call it op_right.
-/

-- Answer below
def op_right {α β : Type}: α × β → β
| a => a.2


/-! #5
## Problem #5

Define a data type called *Day*, the values of which
are the names of the seven days of the week: *sunday,
monday, etc. 


Some days are work days and some days are play
days. Define a data type, *kind*, with two values,
*work* and *play*.

Now define a function, *day2kind*, that takes a *day*
as an argument and returns the *kind* of day it is as
a result. Specify *day2kind* so that weekdays (monday
through friday) are *work* days and weekend days are
*play* days.

Next, define a data type, *reward*, with two values,
*money* and *health*.

Now define a function, *kind2reward*, from *kind* to 
*reward* where *reward work* is *money* and *reward play* 
is *health*.

Finally, use your *funkom* function to produce a new
function that takes a day and returns the corresponding
reward. Call it *day2reward*.

Include test cases using #reduce to show that the reward
from each weekday is *money* and the reward from a weekend
day is *health*.
-/
inductive Days : Type
| monday
| tuesday
| wednesday
| thursday
| friday
| saturday
| sunday
inductive kind: Type
| work
| play

open Days 
open kind
def day2kind: Days → kind 
| saturday => play
| sunday => play
| _ => work
inductive rewards : Type
| money
| health
open rewards 
def kind2reward: kind → rewards
| play => health
| work => money
def day2reward := funkom kind2reward day2kind
#reduce day2reward monday
#reduce day2reward saturday

/-!
Problem #6

Consider the outputs of the following #check commands. 
-/

#check Nat × Nat × Nat
#check Nat × (Nat × Nat)
#check (Nat × Nat) × Nat

/-!
Is × left associative or right associative?

Answer here: Right Associative, 
it is right associative because left parenthesis changed the order of the function

Define a function, *triple*, of the following type:
{ α β γ : Type } → α → β → γ → (α × β × γ)  
-/

-- Here:
def triple {α β γ : Type}: (a: α ) → (b: β ) → (c: γ) → α  × β  × γ  
| a, b, c => Prod.mk a (Prod.mk b c) -- (a ,(b,c))
/-!
Define three functions, call them *first*, *second*, 
and *third*, each of which takes any such triple as
an argument and that returns, respectively, it first,
second, and third elements.
-/

-- Here:
def first {α β γ : Type}: (α × β × γ ) → α
| a => a.1

def second {α β γ : Type}: (α × β × γ) → β 
|a => a.2.1
def third {α β γ : Type}: (α × β × γ) → γ 
|a => a.2.2
/-!
Write three test cases using #eval to show that when 
you apply each of these "elimination" functions to a
triple (that you can make up) it returns the correct
element of that triple.  
-/


-- Here:
def triple_ex := triple 7 "Hello" true
#check (triple_ex)
#eval second triple_ex
#eval first triple_ex
#eval third triple_ex
/-!
Use #check to check the type of a term (that you can
make up) of type (Nat × String) × Bool. 
-/




