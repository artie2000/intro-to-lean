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

end

open Real

/-
# Introduction to this tutorial

Let's look at a Lean proof without trying to understand any of the syntactical details.

If everything works, you currently see a panel to the right of this text with a message like
"No info found." This panel will start displaying interesting things inside the proof.

Note: any text between `/-` and `-/` or after a `--` is a comment for you
that is ignored by Lean.

We write `x : ℝ` to say x is a real number, which is written `x ∈ ℝ` on paper.

We will prove the tan half-angle formula: if cos(x/2) ≠ 0, then
sin x = 2 tan(x/2)/(1+tan^2(x/2)).

The next line describes the objects and assumptions, each with its name.
The line after that is the claim we need to prove. -/

example (x : ℝ) (hx : cos (x / 2) ≠ 0) :
  sin x = (2 * tan (x / 2)) / (1 + (tan (x / 2)) ^ 2) := by
  -- The `by` keyword above marks the beginning of the proof
  -- Put your text cursor here and watch the panel to the right.
  -- To the right of the blue `⊢` symbol is what we are trying to prove. Above this
  -- is our list of variables and hypotheses. As you read the proof, move your cursor from
  -- line to line (for example with the down-arrow button) and watch the panel change.

  -- Expand `tan` into `sin / cos`
  rw [tan_eq_sin_div_cos]

  -- Clear denominators, and expand and simplify both sides
  field

  -- Rearrange into a more helpful form
  suffices sin x * (sin (x * (1 / 2)) ^ 2 + cos (x * (1 / 2)) ^ 2) =
           2 * sin (x * (1 / 2)) * cos (x * (1 / 2)) by linear_combination this

  -- Use the sin double angle formula
  rw [← sin_two_mul]

  -- Use sin^2 + cos^2 = 1
  rw [sin_sq_add_cos_sq]

  -- Expand and simplify both sides
  field
  -- The panel to the right says `No goals`. The proof is done!


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


/-
## Rewriting with an existing theorem

In the previous examples, we rewrote the goal using a local assumption. But we can
also use existing theorems - facts we already know.
For example, let's prove an equation involving trig - something `field` doesn't know about.
We will rewrite with the theorem `sin_pi`, which says that sin(π) = 0,
and `cos_pi`, which says that cos(π) = -1.
You can hover over a theorem, or use `#check`, to see what it says.
-/

#check sin_zero
#check cos_zero

example (a b c : ℝ) : sin 0 + cos 0 = 1 := by
  rw [sin_zero]
  rw [cos_zero]
  field

/-
Let's do an exercise, where you also have to use the fact `sin_zero`.
-/

#check sin_zero

example (a b : ℝ) (h : a = b / 2) : sin (2 * a - b) = 0 := by
  sorry

/-
TODO
Sometimes, an existing theorem will take an argument
If we don't provide arguments to `exp_add`, Lean will try to guess them by finding
the first match for the left-hand side of the equation. In this case this work out fine, but
sometimes more control is needed.
-/
example (a b c : ℝ) : exp (a + b + c) = exp a * exp b * exp c := by
  rw [exp_add, exp_add]

/-
The `field` tactic can simplify fractions, as long as it can see
that the denominator is non-zero. This is what the assumption `hx` says in the next theorem.
What happens if you remove it?
-/

#check tan_eq_sin_div_cos

example (x : ℝ) (hx : cos x ≠ 0) :
    tan x * cos x = sin x := by
  rw [tan_eq_sin_div_cos]
  field


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
  `rw [sin_zero] at h`
in order to replace `sin 0` by `0` in assumption `h`.
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
TODO
Let's do an exercise using `calc`.
-/

example (a b c : ℝ) (h : a = 2 * b + c) : exp (2 * a) = (exp b) ^ 2 * (exp c) ^ 2 := by
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

/-
Here are some harder trig identities. Try these exercises - they're easier using `calc`.
-/

#check sin_two_mul
#check cos_two_mul'
#check sin_sq_add_cos_sq

example (x : ℝ) :
    sin x * cos (2 * x) = sin x - 2 * (sin x) ^ 3 := by
  sorry

example (x : ℝ) (hx : cos x ≠ 0) :
    1 / (cos x) ^ 2 - 1 = (tan x) ^ 2 := by
  sorry

example (x : ℝ) (hx : 1 - sin x ≠ 0) (hx₂ : cos x ≠ 0) :
    1 / cos x + tan x = cos x / (1 - sin x) := by
  sorry
