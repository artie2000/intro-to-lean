/- Modified from https://github.com/PatrickMassot/GlimpseOfLean -/

import Mathlib

set_option warningAsError false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

section

open Lean Parser Tactic

macro (name := field) "field" : tactic =>
  `(tactic| ((try field_simp); first | done | ring_nf))

alias cos_two_mul := Real.cos_two_mul'

end

open Real hiding cos_two_mul

/- Start here! -/

example (x : ℝ) (hx : cos (x / 2) ≠ 0) :
    sin x = (2 * tan (x / 2)) / (1 + (tan (x / 2)) ^ 2) := by
  rw [tan_eq_sin_div_cos]
  field
  suffices sin x * (sin (x * (1 / 2)) ^ 2 + cos (x * (1 / 2)) ^ 2) =
           2 * sin (x * (1 / 2)) * cos (x * (1 / 2)) by linear_combination this
  rw [← sin_two_mul]
  rw [sin_sq_add_cos_sq]
  field


example (a b c : ℝ) : (a * b) * c = b * (a * c) := by
  field

example (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  sorry


example (a b c d e : ℝ) (h : a = b + c) (h' : b = d - e) : a + e = d + c := by
  rw [h]
  rw [h']
  field

example (a b c d e : ℝ) (h : a = b + c) (h' : b = d - e) : a + e = d + c := by
  rw [h, h']
  field

example (a b c d : ℝ) (h : b = d + d) (h' : a = b + c) : a + b = c + 4 * d := by
  sorry


#check sin_zero
#check cos_zero

example (a b c : ℝ) : sin 0 + cos 0 = 1 := by
  rw [sin_zero]
  rw [cos_zero]
  field

example (a b : ℝ) (h : a = 0) : sin a = 0 := by
  sorry

#check sin_add

example (x : ℝ) : sin (x + x) = 2 * sin x * cos x := by
  rw [sin_add x x]
  field

#check tan_eq_sin_div_cos

example (x : ℝ) (hx : cos x ≠ 0) :
    tan x * cos x = sin x := by
  rw [tan_eq_sin_div_cos]
  field

example (a b c d e : ℝ) (h : a = b + c) (h' : a + e = d + c) : b + c + e = d + c := by
  rw [← h, h']

example (a b c d : ℝ) (h : a = b + b) (h' : b = c) (h'' : a = d) : b + c = d := by
  sorry


example (a b c d : ℝ) (h : c = d * a + b) (h' : b = d) : c = d * a + d := by
  rw [h'] at h
  rw [h]


example (a b c d : ℝ) (h : c = b * a - d) (h' : d = a * b) : c = 0 := by
  calc
    c = b * a - d     := by rw [h]
    _ = b * a - a * b := by rw [h']
    _ = 0             := by field

example (a b c : ℝ) (h : a = - b) :
    sin (a + 3 * b) = 2 * sin b * cos b := by
  calc
    sin (a + 3 * b) = sin (- b + 3 * b)              := by sorry
                  _ = sin (b + b)                    := by sorry
                  _ = sin b * cos b + cos b * sin b  := by sorry
                  _ = 2 * sin b * cos b              := by sorry

example (a b c d : ℝ) (h : c = d * a + b) (h' : b = a * d) : c = 2 * a * d := by
  sorry

#check sin_two_mul
#check cos_two_mul
#check sin_sq_add_cos_sq

example (x : ℝ) :
    sin x * cos (2 * x) = sin x - 2 * (sin x) ^ 3 := by
  sorry

example (x : ℝ) (hx : cos x ≠ 0) :
    1 / cos x ^ 2 - 1 = (tan x) ^ 2 := by
  sorry

example (x : ℝ) (hx : 1 - sin x ≠ 0) (hx₂ : cos x ≠ 0) :
    1 / cos x + tan x = cos x / (1 - sin x) := by
  sorry
