/- Modified from https://github.com/PatrickMassot/GlimpseOfLean -/

import Mathlib

set_option warningAsError false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

section

open Lean Parser Tactic

macro (name := ring) "ring" : tactic =>
  `(tactic| first | ring1 | ring_nf)

end

/-! ## Divisibility -/

/-
When working with whole numbers rather than reals, we use a
weaker tactic than `field`, called `ring`, to do rearranging.
-/

example (a b : ℕ) : (a + b) * 2 = 2 * a + b + b := by ring

/-
The `use` tactic lets us prove divisibility by supplying the right multiple
and proving an equation.
-/

example (n : ℕ) : 3 ∣ 6 * n + 3 := by
  use 2 * n + 1
  ring

example (n : ℕ) : n ∣ 2 * n := by
  sorry

example (m n : ℕ) : m ∣ m * n + 7 * m ^ 2 := by
  sorry

/-
The `rcases` tactic lets us turn a hypothesis about divisibility into an equation.
-/

example (n : ℕ) (hn : 4 ∣ n) : 2 ∣ n := by
  rcases hn with ⟨k, hk⟩
  use 2 * k
  rw [hk]
  ring

example (m n : ℕ) (hm : 2 ∣ m) (hn : 3 ∣ n) : 6 ∣ 3 * m + 2 * n := by
  sorry

/-! ## Proof by induction -/

/-
The `induction` tactic lets us do proof by induction: if a fact holds for `0`,
and, if it holds for `k`, then it holds for `k + 1`, then it holds for all
non-negative whole numbers.
-/

example (n : ℕ) : 2 ∣ (3 : ℤ) ^ n - 1 := by
  -- the (3 : ℤ) forces Lean to work with integers to avoid issues with subtraction
  induction n with
  | zero =>
    use 0
    ring
  | succ k hk =>
    rcases hk with ⟨a, ha⟩
    use 3 ^ k + a
    calc
      3 ^ (k + 1) - 1 = 3 ^ k - 1 + 2 * 3 ^ k := by ring
                    _ = 2 * a + 2 * 3 ^ k     := by rw [ha]
                    _ = 2 * (3 ^ k + a)       := by ring

/-
You can write `induction n` and then click the yellow light bulb
to generate the right syntax.
-/

example (n : ℕ) : 3 ∣ (4 : ℤ) ^ n - 1 := by
  sorry

example (n : ℕ) : 7 ∣ (2 : ℤ) ^ (n + 2) + (3 : ℤ) ^ (2 * n + 1) := by
  sorry
