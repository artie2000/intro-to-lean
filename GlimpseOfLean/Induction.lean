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

-- TODO : natural number induction proofs
-- tactics : `induction`, `rw`, `lia` (for normalisation), `intro`?, `exact`?
-- obtain, rcases, use, for divisibility?

example (a b : ℕ) : (a + b) * 2 = 2 * a + b + b := by ring

-- start by doing a simpler divisbility thing to get used to creating / destroying divides

example (n : ℕ) : 3 ∣ 6 * n + 3 := by
  use 2 * n + 1
  ring

example (n : ℕ) (hn : 6 ∣ n) : 3 ∣ n := by
  rcases hn with ⟨k, hk⟩
  use 2 * k
  rw [hk]
  ring

-- now induction

example (n : ℕ) : 3 ∣ (4 : ℤ) ^ n - 1 := by -- note use of Z
  induction n with
  | zero =>
    use 0
    ring
  | succ n ih =>
    rcases ih with ⟨k, hk⟩
    use 4 * k + 1
    calc
      4 ^ (n + 1) - 1 = 4 * (4 ^ n - 1) + 3 := by ring
      _ = 4 * (3 * k) + 3 := by rw [hk]
      _ = 3 * (4 * k + 1) := by ring


example (n : ℕ) : 7 ∣ 2 ^ (n + 2) + 3 ^ (2 * n + 1) := by
  induction n with
  | zero =>
    use 1
    ring
  | succ n ih =>
    rcases ih with ⟨k, hk⟩
    use 2 * k + 3 ^ (2 * n + 1)
    calc
      2 ^ (n + 1 + 2) + 3 ^ (2 * (n + 1) + 1) =
      2 * (2 ^ (n + 2) + 3 ^ (2 * n + 1)) + 7 * 3 ^ (2 * n + 1) := by ring
      _ = 2 * (7 * k) + 7 * 3 ^ (2 * n + 1) := by rw [hk]
      _ = 7 * (2 * k + 3 ^ (2 * n + 1)) := by ring
