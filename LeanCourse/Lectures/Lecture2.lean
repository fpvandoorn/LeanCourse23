import LeanCourse.Common
open Real
noncomputable section
set_option linter.unusedVariables false

/- # Last Lecture -/

/- You type code on the left-hand side of the screen,
  and Lean automatically compiles the file and
  shows output in the *Lean Infoview* on the right.

  If you ever close the Infoview, you can press
  `ctrl+shift+enter` (or `cmd+shift+enter` on a Mac)
  to reopen it -/

/- Every expression in Lean has a type,
  and when applying a function to an argument,
  the argument must lie in the domain of the function.  -/
#check 1
#check fun x : ℝ ↦ x^2
#check (fun x : ℝ ↦ x^2) (π + 3)

/- Statements have type `Prop` and predicates on `A` have type `A → Prop`. -/
#check 3 < π
#check (Nat.Prime)


/- To prove a statement, you use *tactics* to construct a proof of that statement. -/

example : 2 + 2 = 4 := by rfl

example : 2 + 2 = 4 := by
  rfl

example : 2 + 2 = 4 := by {
  rfl
}




/-
# Practical remarks
* Please register on Basis for the examination
* Please register on eCampus for the course
* You can download the course repository from `tinyurl.com/LeanCourse23`.
* First assignment due 20.10.2023. Upload it to eCampus.
-/




/- # Rewriting

`rw` (short for "rewrite") is a tactic that changes a part of a goal to something equal to it.
-/

#check (mul_assoc : ∀ a b c : ℝ, a * b * c = a * (b * c))
#check (mul_comm : ∀ a b : ℝ, a * b = b * a)

example (a b c : ℝ) : a * b * c = b * (a * c) := sorry




/-
In the following lemma the commutator of two elements of a group is defined as
`⁅g, h⁆ = g * h * g⁻¹ * h⁻¹`
-/

section
variable {G : Type*} [Group G]
variable (g h : G)

#check commutatorElement_def g h
#check mul_inv_rev g h
#check inv_inv g

lemma inverse_of_a_commutator : ⁅g, h⁆⁻¹ = ⁅h, g⁆ := by sorry

end



/-
Variants of `rw`:
* `rw [lemma1, lemma2, ...]` is short for multiple rewrites in a row
* `rw [← my_lemma]` to rewrite `my_lemma` from right to left
* `rw [my_lemma] at h` to rewrite using `my_lemma` at `h`.
You have to know what lemma you need to rewrite with.
-/

example (a b c d : ℝ) (h : c = a*d - 1) (h' : b = a*d) : c = b - 1 := by sorry

/-
# Calculational proofs using `calc`
-/

example (a b c d : ℝ) (h : a + c = b*a - d) (h' : d = a*b) : a + c = 0 := sorry


/- A ring is a collection of objects `R` with operations `+`, `*`,
constants `0` and `1` and negation `-` satisfying the following axioms. -/
section
variable (R : Type*) [Ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (add_left_neg : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)


/- Let us use `calc` to prove the following from the axioms of rings. -/

example {a b c : R} (h : a + b = a + c) : b = c := by sorry

end


/- `ring` is a tactic that automatically proves equalities in commutative rings. -/

example (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by sorry

example (a b c d : ℝ) (h1 : c = d * a + b) (h2 : b = a * d) : c = 2 * a * d := by sorry

example (a b c : ℝ) (h1 : 2 * a ≤ 3 * b) (h2 : 1 ≤ a) (h3 : c = 2) :
    c + a ≤ 5 * b := by sorry




/-
**Forwards Reasoning** is reasoning forwards from the hypotheses that other facts must hold.
We can do this with the `have` tactic.
-/

example (p q r : Prop) (h1 : p → q) (h2 : q → r) : p → r := by sorry

/-
**Backwards reasoning** is where we chain implications backwards, deducing
what we want to prove from a combination of other statements (potentially even stronger ones).
We do this with the `apply` tactic.
-/

example (p q r : Prop) (h1 : p → q) (h2 : q → r) : p → r := by sorry

example : Continuous (fun x ↦ 2 + x * Real.sin x) := by sorry




/-
# Difference between `rw` and `apply`
- `rw` can be used to rewrite a subexpression (almost) anywhere in the goal,
  `apply` has to match the outermost thing you are trying to prove.
- *generally* you use `rw` with an equality, and `apply` with implications and "for all" statements.
-/




/- In the following lemma, notice that `a`, `b`, `c`
  are inside curly braces `{...}`.
  This means that these arguments are *implicit*:
  they don't have to be stated, but will be figured out by Lean automatically. -/

lemma my_lemma {a b c : ℝ} (h : a + b = a + c) : b = c :=
    add_left_cancel h

example {b c : ℝ} (h : 2 + b = 2 + c) : b = c := sorry -- prove using `my_lemma`
