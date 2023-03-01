import tactic.ext
import data.prod.basic

/- Inductive types and structures -/

-- Examples taken from:
-- Theorem proving in Lean
--   (https://leanprover.github.io/theorem_proving_in_lean/inductive_types.html)
-- Mathematics in Lean
--   (https://leanprover-community.github.io/mathematics_in_lean/06_Abstract_Algebra.html)

/- 

General syntax for an inductive type:

inductive foo : Type
| constructor₁ : ... → foo
| constructor₂ : ... → foo
...
| constructorₙ : ... → foo

-/

inductive weekday : Type
| sunday : weekday
| monday : weekday
| tuesday : weekday
| wednesday : weekday
| thursday : weekday
| friday : weekday
| saturday : weekday

#check weekday.sunday

inductive my_unit : Type
| star : my_unit

universes u v 

inductive my_prod (α : Type u) (β : Type v) : Type (max u v)
| mk : α → β → my_prod

#check my_prod.mk 1 2

inductive my_sum (α : Type u) (β : Type v)
| inl : α → my_sum
| inr : β → my_sum

-- The types of propositional logic

inductive my_false : Prop

inductive my_true : Prop
| intro : my_true

inductive my_and (a b : Prop) : Prop
| intro : a → b → my_and

inductive my_or (a b : Prop) : Prop
| intro_left  : a → my_or
| intro_right : b → my_or

inductive my_Exists {α : Type*} (q : α → Prop) : Prop
| intro : ∀ (a : α), q a → my_Exists

-- The natural numbers

inductive my_nat : Type
| zero : my_nat
| succ : my_nat → my_nat

#print prefix my_nat

#check @my_nat.rec_on
-- my_nat.rec_on :
--  Π {motive : my_nat → P} (n : my_nat),
--    motive my_nat.zero → (Π (ᾰ : my_nat), motive ᾰ → motive ᾰ.succ) → motive n

-- The type of lists

inductive my_list (α : Type*)
| nil {} : my_list
| cons : α → my_list → my_list

section
open my_list

def my_length1 {α : Type*} : my_list α → ℕ
| nil          := 0
| (cons hd tl) := 1 + my_length1 tl

def my_length2 {α : Type*} : my_list α → ℕ :=
begin
  intro ls,
  induction ls with hd tl tl_length,
  case nil :
    { exact 0, },
  case cons : hd tl 
    { exact 1 + tl_length, },
end

def my_length3 {α : Type*} (l : my_list α) : ℕ :=
l.rec_on 0 (λ hd tl length_tl, nat.succ length_tl)

#reduce my_length1 nil
#reduce my_length1 (cons 1 nil)
#reduce my_length1 (cons 3 (cons 2 nil))

#reduce my_length2 nil
#reduce my_length2 (cons 1 nil)
#reduce my_length2 (cons 3 (cons 2 nil))

#reduce my_length3 nil
#reduce my_length3 (cons 1 nil)
#reduce my_length3 (cons 3 (cons 2 nil))

end

-- Structures

-- Structures are internally the same thing as inductive types with a single constructor.
-- They are convenient because they support special features, such as named fields and inheritance.

inductive point' (α : Type u) : Type u
| mk : α → α → point'

structure point (α : Type u) : Type u :=
(x : α) (y : α)

#check point
#check @point.rec_on
#check point.mk
#check point.x
#check point.y

#print prefix point

#check { point . x := 10, y := 20 }  -- point ℕ
#check { point . y := 20, x := 10 }
#check ({x := 10, y := 20} : point nat)
#check (⟨10, 20⟩ : point ℕ)

example : point nat :=
{ y := 20, x := 10 }

namespace point

variable {α : Type u}

def add : point ℕ → point ℕ → point ℕ := 
λ a b, ⟨a.x + b.x, a.y + b.y⟩

end point

#check @point.add

-- Structure inheritance

inductive color
| red | green | blue

structure color_point (α : Type*) extends point α :=
mk :: (c : color)

#print prefix color_point
#check color_point.mk
#check color_point.to_point
#check color_point.c


-- Type classes

class my_semigroup (G : Type u) : Type u :=
(mul : G → G → G)
(mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c))

-- Here `class` is equivalent to `@[class] structure`.

instance nat_semigroup : my_semigroup ℕ :=
⟨λ m n, m * n, nat.mul_assoc⟩

namespace my_semigroup 

#print prefix my_semigroup

#check mul
#check mul_assoc

instance prod_semigroup {G : Type u} {H : Type v} [my_semigroup G] [my_semigroup H] :
  my_semigroup (G × H) :=
⟨λ a b, (mul a.1 b.1, mul a.2 b.2),
begin
  intros a b c,
  ext,
  repeat { exact mul_assoc _ _ _, },
end⟩

end my_semigroup

notation a ` ⋆ ` b := my_semigroup.mul a b

#reduce (1, 2) ⋆ (2, 3)
#reduce (1, 2, 3, 4) ⋆ (4, 3, 5, 1)

class my_monoid (M : Type u) extends my_semigroup M : Type u :=
(one : M)
(one_mul : ∀ a : M, (one ⋆ a) = a)
(mul_one : ∀ a : M, (a ⋆ one) = a)

notation `𝟙` := my_monoid.one

instance prod_monoid {M : Type u} {N : Type v} [my_monoid M] [my_monoid N] :
  my_monoid (M × N) :=
⟨(𝟙, 𝟙), 
  by sorry,
  by sorry⟩

/- Now go to https://leanprover-community.github.io/mathlib-overview.html and have a look at how your
  favourite piece of mathematics is treated. You will most likely need to backtrack through a few
  definitions before you find something concrete.

  Also, you can search here: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Mathlib.20semantic.20search.
-/