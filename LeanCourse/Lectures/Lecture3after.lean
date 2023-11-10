import LeanCourse.Common
open Real
noncomputable section
set_option linter.unusedVariables false







/- # Last Lecture -/

/-
Tactics we saw last time:
* `rfl` for reflexivity
* `rw` for rewriting
* `calc` for structured calculations
* `ring` for computations using the axioms of a (commutative) ring
* `linarith` for reasoning with linear (in)equalities
* `have` for forwards reasoning
* `apply` for backwards reasoning
* `intro` for introducing a hypothesis
-/

/-
# Practical remarks
* Reminder: first assignment due 20.10.2023. Upload it to eCampus.
* To get the latest version of this repository, run `git pull` on the command line.
* Today we're going to discuss the material of chapters 2.3, 2.4, 2.5 and 3.1
from Mathematics in Lean
-/


/- Curly braces `{...}` indicate that an argument is implicit. -/

lemma my_lemma {a b c : ℝ} (h : a + b = a + c) : b = c := by exact add_left_cancel h

example {x y z : ℝ} (h : x + 2 = x + (y + z)) :
    2 = y + z :=
  my_lemma h

/- {G : Type*} and [Group G] are both implicit arguments -/
#check mul_right_inv

/- # Orders -/

section Real
variable (a b c d e x y z : ℝ)

#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_antisymm : a ≤ b → b ≤ a → a = b)


/- We can apply these lemmas manually, or use the `rfl`/`trans`/`calc` tactics. -/

example (x : ℝ) : x ≤ x := by exact le_refl x
example (x : ℝ) : x ≤ x := by apply le_refl
example (x : ℝ) : x ≤ x := by rfl



example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans
  · exact h₀
  · exact h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by {
  trans y
  · assumption
  · assumption
}


example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  calc a
      ≤ b := h₀
    _ < c := h₁
    _ ≤ d := h₂
    _ < e := h₃

example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by linarith


/- mathlib has lemmas that all common operations are monotone. Here are a few examples. -/

#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (mul_le_mul : a ≤ b → c ≤ d → 0 ≤ c → 0 ≤ b → a * c ≤ b * d)
#check exp_le_exp

#check (exp_le_exp.1 : exp a ≤ exp b → a ≤ b)
#check (exp_le_exp.2 : a ≤ b → exp a ≤ exp b)

/-
To use an "if and only if" statement `h`, you can use any of the following
- `apply h.1`
- `apply h.2`
- `rw [h]`
- `rw [← h]`
-/

example (h : a ≤ b) : exp a ≤ exp b := by
  apply exp_le_exp.2
  exact h

example (h : a ≤ b) : exp a ≤ exp b := by
  rw [exp_le_exp]
  exact h





example (h : exp a ≤ exp b) : a ≤ b := by
  apply exp_le_exp.1
  exact h

example (h : exp a ≤ exp b) : a ≤ b := by
  rw [exp_le_exp] at h
  exact h



/- `gcongr` is very convenient for monotonicity of functions. -/

example (h : a ≤ b) (h2 : b ≤ c) : exp a ≤ exp c := by
  gcongr
  exact le_trans h h2


example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  gcongr



example (h : a ≤ b) (h2 : b < c) (h3 : x ≤ y) : a + x ≤ c + y := by {
  gcongr
  apply le_of_lt
  calc a
     ≤ b := h
   _ < c := h2
  -- linarith
}


/- Remark: for equalities, you should use `congr` instead of `gcongr` -/

example (h : a = b) : c - exp b = c - exp a := by
  congr
  symm
  exact h



/- # Finding Lemmas -/

/-

* Use `exact?`, `apply?`, `rw?` or `simp?` to find a lemma.

* Guess the name of the lemma
  - You can search lemmas in the API documentation:
    https://leanprover-community.github.io/mathlib4_docs/
  - When typing a name, a list of suggested completions automatically shows up
  - You can also press `ctrl-space` (or `cmd-space` on a Mac) to see the list of suggestions.
  - Pressing `ctrl-space` twice displays more information about the available completions.
  - You can also press `ctrl-T` (or `cmd-T`) to search for a lemma name (choosing an option shows you where it is proven)

  Naming conventions:
  - a theorem named `A_of_B_of_C` establishes something of the form `A` from hypotheses of the form `B` and `C`.
  - `A`, `B`, and `C` approximate the way we might read the statement out loud.
  - Example: a theorem showing `x + y ≤ ...` will probably start with `add_le`.
    After typing `add_le` the autocomplete will give you some helpful choices.

* If you right-click on a definition or theorem in VS Code, the editor will show a menu with the option to jump to the file where the theorem is proven, and you can find similar theorems nearby.
-/



example (h : a < b) (h3 : x ≤ y) : a + exp x < b + exp y := by {
  apply add_lt_add_of_lt_of_le
  · assumption
  · gcongr

}




/- Divisibility also gives an order. Warning: divisibility uses a unicode character,
which can be written using `\|`. -/

example (n m k : ℕ) (h₀ : n ∣ m) (h₁ : m ∣ k) : n ∣ k := by {
  trans m
  · assumption
  · assumption
}

example (n m k : ℕ) : m ∣ n * m * k := by {
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left
}



/- We can prove if and only if statements using `constructor`.
  Afterwards we have to prove both implications. -/

example : a + b ≤ c ↔ a ≤ c - b := by {
  constructor
  · intro h
    apply le_sub_left_of_add_le
    rw [add_comm]
    exact h
  · intro h
    exact le_sub_iff_add_le.mp h
}



/- The tactics for universal quantification and implication are the same.
* We can use `intro` to prove an universal quantification or implication.
* We can use `apply` or `specialize` to use an universal quantification or implication in a hypothesis. -/

def NonDecreasing (f : ℝ → ℝ) := ∀ x₁ x₂ : ℝ, x₁ ≤ x₂ → f x₁ ≤ f x₂

example (f g : ℝ → ℝ) (hg : NonDecreasing g) (hf : NonDecreasing f) :
    NonDecreasing (g ∘ f) := by
  sorry

example (f g : ℝ → ℝ) (hf : NonDecreasing f) (hg : NonDecreasing g) :
    NonDecreasing (fun x ↦ f x + g x) := by
  sorry




/- The following theorems characterize `min`.
Let's use it to prove that `min` is commutative. -/
#check (min : ℝ → ℝ → ℝ)
#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by sorry

end Real

/- We can also work with abstract orders, such as an arbitrary partial order. -/

section PartialOrder

-- mathlib usually uses Greek letters for types
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)

/- every preorder comes automatically with an associated strict order -/
example : x < y ↔ x ≤ y ∧ x ≠ y := by exact?


/- the reverse order `≥`/`>` is defined from `≤`/`<`.
  Some tactics don't work well with `≥`/`>`,
  so in mathlib we prefer to state things using `≤`/`<` -/
example : x ≥ y ↔ y ≤ x := by rfl
example : x > y ↔ y < x := by rfl

end PartialOrder


/- A lattice is a partial order with two operations `⊔` and `⊓` that correspond to the least upper bound and greatest lower bound of two elements in the order. -/

section Lattice

variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ (x ⊔ y) = x := by sorry

end Lattice
