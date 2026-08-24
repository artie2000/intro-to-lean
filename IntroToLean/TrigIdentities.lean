/- Modified from https://github.com/PatrickMassot/GlimpseOfLean -/

import Mathlib

set_option warningAsError false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

section

open Lean Parser Tactic

-- TODO : make a good `field` tactic
macro (name := field) "field" : tactic =>
  `(tactic | first | field_simp; ring_nf)

end

open Real

-- TODO : comment-free version for workshop

/-
# Introduction to this tutorial

Let's look at a Lean proof without trying to understand any of the syntactical details.

If everything works, you currently see a panel to the right of this text with a message like
"No info found." This panel will start displaying interesting things inside the proof.

Note: any text between `/-` and `-/` or after a `--` is a comment for you
that is ignored by Lean.

We write `x : ℝ` to say `x` is a real number, which is written `x ∈ ℝ` on paper.

We claim that if `cos x` is not equal to `0`, then the following formula holds:
`sin x = (2 * tan (x / 2)) / (1 + (tan (x / 2)) ^ 2)`.

The next line describes the objects and assumptions, each with its name.
The following line is the claim we need to prove. -/
example (x : ℝ) (hx : cos (x / 2) ≠ 0) :
  sin x = (2 * tan (x / 2)) / (1 + (tan (x / 2)) ^ 2) := by -- This `by` keyword marks the beginning of the proof
  -- Put your text cursor here and watch the panel to the right.
  -- To the right of the blue `⊢` symbol is what we are trying to prove. Above this
  -- is our list of variables and hypotheses. As you read the proof, move your cursor from
  -- line to line (for example with the down-arrow button) and watch the panel change.
  calc
    sin x = sin (2 * (x / 2)) := by field
    _ = 2 * sin (x / 2) * cos (x / 2) := by rw [sin_two_mul]
  symm
  calc
    _ = 2 * sin (x / 2) * (1 / (cos (x / 2) * (1 + tan (x / 2) ^ 2))) := by
      rw [tan_eq_sin_div_cos]
      field
    _ = 2 * sin (x / 2) * (1 / (cos (x / 2) * (1 + tan (x / 2) ^ 2))) := by rfl
  congr
  rw [tan_eq_sin_div_cos]
  calc
    _ = cos (x / 2) / (sin (x / 2) ^ 2 + cos (x / 2) ^ 2) := by field
    _ = cos (x / 2) := by rw [sin_sq_add_cos_sq]; field

/--/
  -- Our goal is to prove that, for any positive `ε`, there exists a natural
  -- number `N` such that, for any natural number `n` at least `N`,
  --  `|f(u_n) - f(x₀)|` is at most `ε`.
  unfold seq_limit
  -- Fix a positive number `ε`.
  intros ε hε
  -- By assumption on `f` applied to this positive `ε`, we get a positive `δ`
  -- such that, for all real numbers `x`, if `|x - x₀| ≤ δ` then `|f(x) - f(x₀)| ≤ ε` (1).
  obtain ⟨δ, δ_pos, Hf⟩ : ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε := hf ε hε
  -- The assumption on `u` applied to this `δ` gives a natural number `N` such that
  -- for every natural number `n`, if `n ≥ N` then `|u_n - x₀| ≤ δ`   (2).
  obtain ⟨N, Hu⟩ : ∃ N, ∀ n ≥ N, |u n - x₀| ≤ δ := hu δ δ_pos
  -- Let's prove `N` is suitable.
  use N
  -- Fix `n` which is at least `N`. Let's prove `|f(u_n) - f(x₀)| ≤ ε`.
  intros n hn
  -- Thanks to (1) applied to `u_n`, it suffices to prove that `|u_n - x₀| ≤ δ`.
  apply Hf
  -- This follows from property (2) and our assumption on `n`.
  apply Hu n hn
  -- This finishes the proof!
-/


/-
# Computing

## The field tactic

The first kind of proof you meet when learning maths is a proof by calculation.
It may not sound like a proof, but this is actually using properties of operations on numbers,
such as addition and multiplication. We conveniently have a tactic `field` which knows about
most of these properties.
-/

example (a b c : ℝ) : (a * b) * c = b * (a * c) := by
  field

/-
It's your turn! Replace the word `sorry` below by a proof. In this case the proof is just `field`.
After you prove something, you will see a small "No goals" message, which is the indication that
your proof is finished.
-/

example (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  sorry

/-
In the first example above, take a closer look at where Lean displays parentheses.
For Lean, `a * b * c` is read as `(a * b) * c`, which is technically different to `a * (b * c)`!
The fact that they are equal is a theorem used by the `field` tactic when needed.
-/


/-
## The rewriting tactic

Now let's see how to use assumptions in our proofs. If we know `A = B`, then
we can replace `A` with `B` anywhere we like. This operation is called rewriting,
and the tactic for this is called `rw`. Carefully step through the proof below
and try to understand what is happening.
-/
example (a b c d e : ℝ) (h : a = b + c) (h' : b = d - e) : a + e = d + c := by
  rw [h]
  rw [h']
  field

/-
The `rw` tactic changes the current goal. After the first line of the above proof,
the new goal is `b + c + e = d + c`. So you can read this first proof step as saying:
"I wanted to prove, `a + e = d + c` but, since assumption `h` tells me `a = b + c`,
it's enough to prove `b + c + e = d + c`."

The `rw` tactic needs to be told exactly what to do. There are more powerful tactics
that can automate tedious steps for you, but we'll keep it simple for now.

You can combine multiple rewrites onto one line:
-/
example (a b c d e : ℝ) (h : a = b + c) (h' : b = d - e) : a + e = d + c := by
  rw [h, h']
  field

/-
Putting your cursor between `h` and `h'` shows you the intermediate proof state (try it).
The background colour changes to highlight what is new in green.

Now try it yourself. Remember that `field` can still do calculations - but it doesn't use
the assumptions `h` and `h'`
-/

example (a b c d : ℝ) (h : b = d + d) (h' : a = b + c) : a + b = c + 4 * d := by
  sorry

-- TODO : use trig identity instead?
/-
## Rewriting with an existing theorem

In the previous examples, we rewrote the goal using a local assumption. But we can
also use existing theorems - facts we already knows.
For example, let's prove an equation involving the `exp` function - something `field`
doesn't know about. We will rewrite twice with the theorem `exp_add x y`, which says that
`exp(x + y) = exp(x) * exp(y)`.
-/
example (a b c : ℝ) : exp (a + b + c) = exp a * exp b * exp c := by
  rw [exp_add (a + b) c]
  rw [exp_add a b]

/-
We didn't need to use `field` at the end because, after the second `rw`, the goal becomes
`exp a * exp b * exp c = exp a * exp b * exp c`, and Lean immediately sees the proof is done.

If we don't provide arguments to `exp_add`, Lean will try to guess them by finding
the first match for the left-hand side of the equation. In this case this work out fine, but
sometimes more control is needed.
-/
example (a b c : ℝ) : exp (a + b + c) = exp a * exp b * exp c := by
  rw [exp_add, exp_add]

/-
Let's do an exercise, where you also have to use the facts
`exp_sub x y : exp(x - y) = exp(x) / exp(y)` and `exp_zero : exp 0 = 1`.

Remember: `a + b - c` means `(a + b) - c`.
-/

example (a b c : ℝ) : exp (a + b - c) = (exp a * exp b) / (exp c * exp 0) := by
  sorry


/-
## Rewriting from right to left

We can also rewrite backwards, replacing the right-hand side of an equality with the
left-hand side, using `←`:
-/
example (a b c d e : ℝ) (h : a = b + c) (h' : a + e = d + c) : b + c + e = d + c := by
  rw [← h, h']

/-
Whenever you see a symbol that you don't see on your keyboard, such as ←,
you can put your mouse cursor over it and learn from the tooltip how to type it.
In the case of ←, you can type it by typing "\l ", so backslash-l-space.

Keep in mind that this rewriting direction is which side in the equality you want to
*use*, not about which side you want to *prove*. The `rw [← h]` in the previous example
replaced the right-hand side by the left-hand side, so it looked for `b + c` in the current
goal and replaced it with `a`.
-/

example (a b c d : ℝ) (h : a = b + b) (h' : b = c) (h'' : a = d) : b + c = d := by
  sorry


/-
## Rewriting in a local assumption

We can also perform rewriting in an assumption of the local context, using for instance
  `rw [exp_add x y] at h`
in order to replace `exp(x + y)` by `exp(x) * exp(y)` in assumption `h`.
-/

example (a b c d : ℝ) (h : c = d * a + b) (h' : b = d) : c = d * a + d := by
  rw [h'] at h
  rw [h]


/-
## Calculation layout using calc

The proof in the last example is very far away from what we would write on
paper. We can get a more natural layout using the `calc` tactic.
After each `:=` below, the goal is to prove equality with the preceding line
(or the left-hand side on the first line). Carefully check you understand what's
going on by putting your cursor after each `by` and looking at the tactic state.
-/

example (a b c d : ℝ) (h : c = b * a - d) (h' : d = a * b) : c = 0 := by
  calc
    c = b * a - d     := by rw [h]
    _ = b * a - a * b := by rw [h']
    _ = 0             := by field

/-
Let's do some exercises using `calc`.
-/

example (a b c : ℝ) (h : a = b + c) : exp (2 * a) = (exp b) ^ 2 * (exp c) ^ 2 := by
  calc
    exp (2 * a) = exp (2 * (b + c))                 := by sorry
              _ = exp ((b + b) + (c + c))           := by sorry
              _ = exp (b + b) * exp (c + c)         := by sorry
              _ = (exp b * exp b) * (exp c * exp c) := by sorry
              _ = (exp b) ^ 2 * (exp c) ^ 2         := by sorry

/-
From a practical point of view, when writing a `calc` proof, it is sometimes convenient to:
* pause the tactic state view update in VScode by clicking the Pause icon button
  in the top right corner of the Lean Infoview panel.
* write the full calculation, ending each line with ":= ?_"
* resume tactic state update by clicking the Play icon button and fill in proofs.

The underscores should be placed below the left-hand-side of the first line below the `calc`.
Aligning the equal signs and `:=` signs is not necessary but looks tidy.

You can write `calc?` to quickly get started with the correct syntax.
-/

example (a b c d : ℝ) (h : c = d * a + b) (h' : b = a * d) : c = 2 * a * d := by
  sorry

#check sin_two_mul
#check cos_two_mul'
#check sin_sq_add_cos_sq
#check tan_eq_sin_div_cos

example (x : ℝ) (hx : 1 - sin x ≠ 0) (hx₂ : cos x ≠ 0) :
    1 / cos x + tan x = cos x / (1 - sin x) := by
  calc
    _ = 1 / cos x + sin x / cos x := by rw [tan_eq_sin_div_cos]
    _ = (1 - ((sin x) ^ 2 + (cos x) ^ 2) + (cos x) ^ 2) / (cos x * (1 - sin x)) := by field
    _ = (1 - 1 + (cos x) ^ 2) / (cos x * (1 - sin x)) := by rw [sin_sq_add_cos_sq]
    _ = cos x / (1 - sin x) := by field

-- "quick" / uncontrolled alternative
example (x : ℝ) (hx : 1 - sin x ≠ 0) (hx₂ : cos x ≠ 0) :
    1 / cos x + tan x = cos x / (1 - sin x) := by
  rw [tan_eq_sin_div_cos]
  field
  rw [← sin_sq_add_cos_sq x]
  field

-- TODO
-- trig identities
-- "calc" earlier?
