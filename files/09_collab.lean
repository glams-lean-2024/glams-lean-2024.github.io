import tuto_lib

set_option pp.beta true
set_option pp.coercions false

/-
This is the final file in the series. Here we use everything covered
in previous files to prove a couple of famous theorems from 
elementary real analysis. Of course they all have more general versions
in mathlib.

As usual, keep in mind the following:

  abs_le {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y

  ge_max_iff (p q r) : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q

  le_max_left p q : p ≤ max p q

  le_max_right p q : q ≤ max p q

as well as a lemma from the previous file:

  le_of_le_add_all : (∀ ε > 0, y ≤ x + ε) →  y ≤ x

Let's start with a variation on a known exercise.
-/

-- 0071
lemma le_lim {x y : ℝ} {u : ℕ → ℝ} (hu : seq_limit u x)
  (ineg : ∃ N, ∀ n ≥ N, y ≤ u n) : y ≤ x :=
begin
  apply le_of_le_add_all,
  intros ε hε,
  cases hu ε hε with N₁ hN₁,
  cases ineg with N₂ hN₂,
  let N := max N₁ N₂,
  specialize hN₁ N (le_max_left _ _),
  calc y ≤ u N   : hN₂ N (le_max_right _ _)
     ... ≤ x + ε : by linarith [(abs_le.mp hN₁).right], 
end

/-
Let's now return to the result proved in the `00_` file of this series, 
and prove again the sequential characterization of upper bounds (with a slighly
different proof).

For this, and other exercises below, we'll need many things that we proved in previous files,
and a couple of extras.

From the 5th file:

  limit_const (x : ℝ) : seq_limit (λ n, x) x


  squeeze (lim_u : seq_limit u l) (lim_w : seq_limit w l)
    (hu : ∀ n, u n ≤ v n) (hw : ∀ n, v n ≤ w n)  : seq_limit v l

From the 8th:

  def upper_bound (A : set ℝ) (x : ℝ) := ∀ a ∈ A, a ≤ x

  def is_sup (A : set ℝ) (x : ℝ) := upper_bound A x ∧ ∀ y, upper_bound A y → x ≤ y

  lt_sup (hx : is_sup A x) : ∀ y, y < x → ∃ a ∈ A, y < a :=

You can also use:

  nat.one_div_pos_of_nat {n : ℕ} : 0 < 1 / (n + 1 : ℝ)

  inv_succ_le_all :  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, 1/(n + 1 : ℝ) ≤ ε

and their easy consequences:

  limit_of_sub_le_inv_succ (h : ∀ n, |u n - x| ≤ 1/(n+1)) : seq_limit u x

  limit_const_add_inv_succ (x : ℝ) : seq_limit (λ n, x + 1/(n+1)) x

  limit_const_sub_inv_succ (x : ℝ) : seq_limit (λ n, x - 1/(n+1)) x

as well as:

  lim_le (hu : seq_limit u x) (ineg : ∀ n, u n ≤ y) : x ≤ y

The structure of the proof is offered. It features a new tactic: 
`choose` which invokes the axiom of choice (observing the tactic state before and
after using it should be enough to understand everything). 
-/

-- 0072
lemma is_sup_iff (A : set ℝ) (x : ℝ) :
(is_sup A x) ↔ (upper_bound A x ∧ ∃ u : ℕ → ℝ, seq_limit u x ∧ ∀ n, u n ∈ A ) :=
begin
  split,
  { intro h,
    use h.left,
    have : ∀ n : ℕ, ∃ a ∈ A, x - 1/(n+1) < a,
    { intros n,
      have : 1/(n+1 : ℝ) > 0,
        exact nat.one_div_pos_of_nat,
      exact lt_sup h (x - 1/(n+1)) (by linarith),
    },
    choose u hu using this,
    use u,
    split,
    { apply squeeze (limit_const_sub_inv_succ x) (limit_const x),
      intro n, exact le_of_lt (hu n).right,
      intro n, exact h.left _ (hu n).left, },
    intro n, exact (hu n).left,
  },
  { rintro ⟨maj, u, limu, u_in⟩, 
    use maj,
    intros y hy,
    apply lim_le limu,
    intro n, 
    exact hy _ (u_in n),
  },
end