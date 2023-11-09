import LeanCourse.Common
set_option linter.unusedVariables false
open Nat

/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 2, sections 3, 4 and 5
  Read chapter 3, sections 1, 2, 4, 5.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 27.10.2023.

* When you hand in your solution, make sure that the file compiles!
  If you didn't manage to complete a particular exercise, make sure that the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/

lemma exercise2_1 {α : Type*} {p q : α → Prop} :
    (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
    exact exists_or

section Surjectivity

/- Lean's mathematical library knows what a surjective function is, but let's define it here
ourselves and prove some things about it. -/
def SurjectiveFunction (f : ℝ → ℝ) : Prop :=
  ∀ (y : ℝ), ∃ (x : ℝ), f x = y

variable {f g : ℝ → ℝ} {x : ℝ}

/- `rfl` or `simp` can compute the following.
  `simp` is a very useful tactic that can simplify many expressions. -/
example : (g ∘ f) x = g (f x) := by simp

lemma exercise2_2 (h : SurjectiveFunction (g ∘ f)) : SurjectiveFunction g := by
  intro y
  rcases h y with ⟨x, hx⟩
  use f x
  rw [← hx]
  simp


/- Hint: you are allowed to use the previous exercise in this exercise! -/
lemma exercise2_3 (hf : SurjectiveFunction f) :
    SurjectiveFunction (g ∘ f) ↔ SurjectiveFunction g := by
  constructor
  · exact exercise2_2
  intro h
  intro y
  have gy: ∃ x, g x = y := by exact h y
  rcases gy with ⟨z, gz⟩
  have fz: ∃ x, f x = z := by exact hf z
  rcases fz with ⟨x, fz⟩
  use x
  simp
  rw [fz]
  exact gz



/- Composing a surjective function by a linear function to the left and the right will still result
in a surjective function. The `ring` tactic will be very useful here! -/
lemma exercise2_4 (hf : SurjectiveFunction f) :
    SurjectiveFunction (fun x ↦ 2 * f (3 * (x + 4)) + 1) := by
  intro y
  have h: ∃ x, f x = (y - 1) / 2 := by exact hf ((y - 1) / 2)
  rcases h with ⟨z, hz⟩
  use (z - 12) / 3
  simp
  ring
  rw [hz]
  ring


end Surjectivity





section Growth

/- Given two sequences of natural numbers `s` and `t`. We say that `s` eventually grows faster than
  `t` if for all `k : ℕ`, `s_n` will be at least as large as `k * t_n` for large enough `n`. -/
def EventuallyGrowsFaster (s t : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, k * t n ≤ s n

variable {s t : ℕ → ℕ} {k : ℕ}

/- Hint: `simp` can help you simplify expressions like the following.
  Furthermore, `gcongr` will be helpful! -/
example : (fun n ↦ n * s n) k = k * s k := by simp

lemma exercise2_5 : EventuallyGrowsFaster (fun n ↦ n * s n) s := by
  intro k
  use k
  intros N hN
  simp
  gcongr


/- For the following exercise, it will be useful to know that you can write `max a b`
  to take the maximum of `a` and `b`, and that this lemma holds  -/
lemma useful_fact (a b c : ℕ) : c ≥ max a b ↔ c ≥ a ∧ c ≥ b := by simp


lemma exercise2_6 {s₁ s₂ t₁ t₂ : ℕ → ℕ}
    (h₁ : EventuallyGrowsFaster s₁ t₁) (h₂ : EventuallyGrowsFaster s₂ t₂) :
    EventuallyGrowsFaster (s₁ + s₂) (t₁ + t₂) := by
  intro k
  have h: ∃ N₁ : ℕ, ∀ n ≥ N₁, k * t₁ n ≤ s₁ n := by exact h₁ k
  have h': ∃ N₂ : ℕ, ∀ n ≥ N₂, k * t₂ n ≤ s₂ n := by exact h₂ k
  rcases h with ⟨N₁, hN₁⟩
  rcases h' with ⟨N₂, hN₂⟩
  use max N₁ N₂
  intros n hn
  simp
  rw [mul_add]
  gcongr
  apply hN₁
  . exact le_of_max_le_left hn
  apply hN₂
  . exact le_of_max_le_right hn




/- Optional hard exercise 1:
Find a function that is nowhere zero and grows faster than itself when shifted by one. -/
lemma exercise2_7 : ∃ (s : ℕ → ℕ), EventuallyGrowsFaster (fun n ↦ s (n+1)) s ∧ ∀ n, s n ≠ 0 := by
  use fun n => n !  + 1
  constructor
  case h.right =>
    intro n
    exact succ_ne_zero (n !)
  intro k
  use k
  intro n
  simp
  intro h
  have h1: k * n ! ≤ n * n ! := by gcongr
  have h2: k ≤ n ! + 1 := by
    calc
      k ≤ n := by exact h
      _ ≤ n ! := by exact self_le_factorial n
      _ ≤ n ! + 1 := by linarith

  calc
    k * (n ! + 1) = k * n ! + k * 1 := by ring
    _ ≤ n * n ! + k * 1 := by linarith
    _ ≤ n * n ! + n ! + 1 := by linarith
    _ ≤ (n + 1) * n ! + 1 := by linarith
    _ ≤ (n + 1) ! + 1 := by rw [factorial_succ]



example : (n + 1) * (n + 1) + 1 = n * n + 2 * n + 2 := by ring


/- Optional hard exercise 2:
Show that a function that satisfies the conditions of the last
exercise, then it must necessarily tend to infinity.
The following fact will be useful. Also, the first step of the proof is already given. -/

lemma useful_fact2 {n m : ℕ} (hn : n ≥ m + 1) : ∃ k ≥ m, k + 1 = n := by
  use n - 1
  constructor
  · exact le_pred_of_lt hn
  · have : 1 ≤ n := by exact one_le_of_lt hn
    exact Nat.sub_add_cancel this

lemma exercise2_8 (hs : EventuallyGrowsFaster (fun n ↦ s (n+1)) s) (h2s : ∀ n, s n ≠ 0) :
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, s n ≥ k := by
  have h3s : ∀ n, 1 ≤ s n := by
    intro n
    exact one_le_iff_ne_zero.mpr (h2s n)
  sorry

   /-
  intro k
  induction k with
  | zero =>
    use 0
    intros n hn
    calc
      s n ≥ 1 := by exact h3s n
      _ ≥ 0 := by linarith
  | succ k ih =>
    use k + 1
    intros n hn
    calc
      s n ≥ s (k + 1) := by sorry
      _ ≥ k + 1 := by apply?
      _ ≥ succ k := by linarith
  -/
end Growth
