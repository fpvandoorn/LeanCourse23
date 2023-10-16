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
-/


/- Curly braces `{...}` indicate that an argument is implicit. -/

lemma my_lemma {a b c : ℝ} (h : a + b = a + c) : b = c :=
  add_left_cancel h

/- {G : Type*} and [Group G] are both implicit arguments -/
#check mul_right_inv

/- # Orders -/

section Real
variable (a b c x y z : ℝ)

#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_antisymm : a ≤ b → b ≤ a → a = b)


/- We can apply these lemmas manually, or use the `rfl`/`trans`/`calc` tactics. -/

example (x : ℝ) : x ≤ x := by sorry

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by sorry



example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by sorry


/- `gcongr` is very convenient for monotonicity of functions. -/

example (h : a ≤ b) : c - exp b ≤ c - exp a := by sorry



example (h : a ≤ b) (h2 : b ≤ c) : exp a ≤ exp c := by sorry



example (h : a ≤ b) (h2 : b < c) (h3 : x ≤ y) : a + x ≤ c + y := by sorry



example (h : a < b) (h3 : x ≤ y) : a + x < b + y := by sorry


/- Remark: for equalities, `congr` is better than `gcongr` -/

example (h : a = b) : c - exp b = c - exp a := by sorry



/- # Finding Lemmas -/

/-

* API documentation: https://leanprover-community.github.io/mathlib4_docs/

* Use `exact?`, `apply?`, `rw?` or `simp?` to find a lemma.

* If you right-click on an existing theorem name in VS Code, the editor will show a menu with the option to jump to the file where the theorem is proven, and you can find similar theorems nearby.

* Guess the name of the lemma
  - When typing a name, a list of suggested completions automatically shows up
  - You can also press `ctrl-space` (or `cmd-space` on a Mac) to see the list of suggestions.
  - Pressing `ctrl-space` twice displays more information about the available completions.
  - You can also press `ctrl-T` (or `cmd-T`) to search for a lemma name (choosing an option shows you where it is proven)

  Naming conventions:
  - a theorem named `A_of_B_of_C` establishes something of the form `A` from hypotheses of the form `B` and `C`.
  - `A`, `B`, and `C` approximate the way we might read the statement out loud.
  - Example: a theorem showing `x + y ≤ ...` will probably start with `add_le`.
    After typing `add_le` the autocomplete will give you some helpful choices.
-/


example : 2*a*b ≤ a^2 + b^2 := by sorry


/- # Other operations -/


/- The following theorems characterize `min`.
Let's use it to prove that `min` is commutative. -/
#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)


example : min a b = min b a := by sorry

end Real

/- Divisibility also gives an order. Warning: divisibility uses a unicode character,
which can be written using `\|`. -/

example (n m k : ℕ) (h₀ : n ∣ m) (h₁ : m ∣ k) : n ∣ k := by sorry

example (n m k : ℕ) : m ∣ n * m * k := by sorry


/- We can also work with abstract orders, such as an arbitrary partial order. -/

section PartialOrder

-- mathlib usually uses Greek letters for types
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)

-- every preorder comes automatically with an associated strict order
example : x < y ↔ x ≤ y ∧ x ≠ y := by exact?


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