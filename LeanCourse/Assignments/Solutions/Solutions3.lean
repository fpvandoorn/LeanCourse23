import LeanCourse.Common
import LeanCourse.MIL.C03_Logic.solutions.Solutions_S06_Sequences_and_Convergence
set_option linter.unusedVariables false
open Nat Real Function Set

/-
* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 3, sections 3 and 6
  Read chapter 4, all sections.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  Feel free to skip exercises if you are confident that you can do them.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 3.11.2023.

* When you hand in your solution, make sure that the file compiles!
  If you didn't manage to complete a particular exercise, make sure that the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/


/- Prove the law of excluded middle without using `by_cases` or lemmas from the library.
You will need to use `by_contra` in the proof. -/
lemma exercise3_1 (p : Prop) : p ∨ ¬ p := by
  by_contra h
  apply h
  right
  intro h2
  apply h
  left
  assumption

/- This is an exercise about finding lemmas from the library.
`A ≃ B` means that there is a bijection from `A` to `B`.
`A × B` is the cartesian product of the types `A` and `B`.
So in this exercise you are asked to prove that there is a bijective correspondence between
  functions from `ℤ × ℕ` to `ℤ × ℤ`
and
  functions from `ℕ` to `ℕ`
Your proof is supposed to only combine results from the library,
you are not supposed to define the bijection yourself.
Note: you can use `calc` blocks with `≃`. -/
lemma exercise3_2 : (ℤ × ℕ → ℤ × ℤ) ≃ (ℕ → ℕ) := by
  -- have h1 : ℤ × ℤ ≃ ℤ := by exact Denumerable.pair
  -- have h2 : ℤ ≃ ℕ := by exact Equiv.intEquivNat
  have h1 : ℤ × ℕ ≃ ℕ := by exact Denumerable.eqv (ℤ × ℕ)
  have h2 : ℤ × ℤ ≃ ℕ := by exact Denumerable.eqv (ℤ × ℤ)
  exact Equiv.arrowCongr h1 h2

/- ## Converging sequences

In the next few exercises, you prove more lemmas about converging sequences. -/

/-- From the lecture, the sequence `u` of real numbers converges to `l`. -/
def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

/- Let's prove that reindexing a convergent sequence
by a reindexing function that tends to infinity
produces a sequence that converges to the same value. -/
lemma exercise3_3 {s : ℕ → ℝ} {r : ℕ → ℕ} {a : ℝ}
    (hs : SequentialLimit s a) (hr : ∀ m : ℕ, ∃ N : ℕ, ∀ n ≥ N, r n ≥ m) :
    SequentialLimit (s ∘ r) a := by
  intro ε hε
  obtain ⟨N, hN⟩ := hs ε hε
  obtain ⟨K, hK⟩ := hr N
  use K
  intro n hn
  apply hN
  apply hK
  assumption



/- Let's prove the squeeze theorem for sequences.
You will want to use the lemma in the library that states
`|a| < b ↔ -b < a ∧ a < b`. -/
lemma exercise3_4 {s₁ s₂ s₃ : ℕ → ℝ} {a : ℝ}
    (hs₁ : SequentialLimit s₁ a) (hs₃ : SequentialLimit s₃ a)
    (hs₁s₂ : ∀ n, s₁ n ≤ s₂ n) (hs₂s₃ : ∀ n, s₂ n ≤ s₃ n) :
    SequentialLimit s₂ a := by
  intro ε hε
  obtain ⟨N, hN⟩ := hs₁ ε hε
  obtain ⟨N', hN'⟩ := hs₃ ε hε
  let N'' := max N N'
  use N''
  intro n hn
  specialize hN n (le_of_max_le_left hn)
  specialize hN' n (le_of_max_le_right hn)
  specialize hs₁s₂ n
  specialize hs₂s₃ n
  rw [abs_lt] at hN hN' ⊢
  obtain ⟨h₁N, h₂N⟩ := hN
  obtain ⟨h₁N', h₂N'⟩ := hN'
  constructor
  · linarith
  · linarith

/- Let's prove that the sequence `n ↦ 1 / (n+1)` converges to `0`.
  It will be useful to know that if `x : ℝ` then `⌈x⌉₊ : ℕ` is `x` rounded up
  (in fact, it's rounded up to 0 if `x ≤ 0`). You will need some lemmas from the library, and `simp`
  will be useful to simplify.
  In the goal you will see `↑n`. This is the number `n : ℕ` interpreted as a real number `↑n : ℝ`.
  To type this number yourself, you have to write `(n : ℝ)`.
-/
#check ⌈π⌉₊
#check fun n : ℕ ↦ (n : ℝ)

lemma exercise3_5 : SequentialLimit (fun n ↦ 1 / (n+1)) 0 := by {
  intro ε hε
  use ⌈1 / ε⌉₊
  intro n hn
  simp at hn
  simp [abs_inv]
  rw [inv_lt]
  · have fact1 : (n : ℝ) + 1 ≤ |(n : ℝ) + 1| := by apply?
    linarith
  · -- positivity
    rw [abs_pos]
    apply?
  · assumption
}


/- Use the previous exercises to prove that `n ↦ sin n / (n + 1)` converges to 0.
  I will prove for you that `n ↦ -1 / (n + 1)` also converges to `0`. -/

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (hs : SequentialLimit s a) :
    SequentialLimit (fun n ↦ c * s n) (c * a) := by
  intro ε hε
  obtain ⟨N, hN⟩ := hs (ε / max |c| 1) (by positivity)
  use N
  intro n hn
  specialize hN n hn
  simp
  calc |c * s n - c * a|
      = |c * (s n - a)| := by ring
    _ = |c| * |s n - a| := by exact abs_mul c (s n - a)
    _ ≤ max |c| 1 * |s n - a| := by gcongr; exact le_max_left |c| 1
    _ < max |c| 1 * (ε / max |c| 1) := by gcongr
    _ = ε := by refine mul_div_cancel' ε ?hb; positivity

lemma use_me : SequentialLimit (fun n ↦ (-1) / (n+1)) 0 := by
  have : SequentialLimit (fun n ↦ (-1) * (1 / (n+1))) (-1 * 0) :=
    convergesTo_mul_const (-1) exercise3_5
  simp at this
  simp [neg_div, this]

lemma exercise3_6 : SequentialLimit (fun n ↦ sin n / (n+1)) 0 := by
  apply exercise3_4 use_me exercise3_5
  · intro n
    gcongr
    apply?
  · intro n
    gcongr
    apply?

/- Now let's prove that if a convergent sequence is nondecreasing, then it must stay below the
limit. -/
def NondecreasingSequence (u : ℕ → ℝ) : Prop :=
  ∀ n m, n ≤ m → u n ≤ u m

lemma exercise3_7 (u : ℕ → ℝ) (l : ℝ) (h1 : SequentialLimit u l) (h2 : NondecreasingSequence u) :
    ∀ n, u n ≤ l := by
  intro n
  by_contra hn
  have : u n > l := by exact not_le.mp hn
  obtain ⟨N, hN⟩ := h1 (u n - l) (by linarith)
  specialize hN (max n N) (by apply?)
  rw [← not_le] at hN
  apply hN
  have : u n ≤ u (max n N) := h2 _ _ (by apply?)
  rw [abs_eq_self.2]
  · gcongr
  · rw [sub_nonneg]
    linarith

/- ## Sets

In the next few exercises, you prove more lemmas about converging sequences. -/


lemma exercise3_8 {α β : Type*} (f : α → β) (s : Set α) (t : Set β) :
    f '' s ∩ t = f '' (s ∩ f ⁻¹' t) := by
  ext y; constructor
  · rintro ⟨⟨x, xs, rfl⟩, fxv⟩
    use x, ⟨xs, fxv⟩
  · rintro ⟨x, ⟨⟨xs, fxv⟩, rfl⟩⟩
    exact ⟨⟨x, xs, rfl⟩, fxv⟩

lemma exercise3_9 :
    (fun x : ℝ ↦ x ^ 2) ⁻¹' {y | y ≥ 4} = { x : ℝ | x ≤ -2 } ∪ { x : ℝ | x ≥ 2 } := by
  ext x
  simp [show (4 : ℝ) = 2 ^ 2 by norm_num, sq_le_sq, le_abs']

/- As mentioned in exercise 2, `α × β` is the cartesian product of the types `α` and `β`.
Elements of the cartesian product are denoted `(a, b)`, and the projections are `.1` and `.2`.
As an example, here are two ways to state when two elements of the cartesian product are equal. -/

variable {α β γ : Type*}
example (a a' : α) (b b' : β) : (a, b) = (a', b') ↔ a = a' ∧ b = b' := Prod.ext_iff
example (x y : α × β) : x = y ↔ x.1 = y.1 ∧ x.2 = y.2 := Prod.ext_iff

/- Hard exercise: Let's prove that if `f : α → γ` and `g : β → γ` are injective function whose
  ranges partition `γ`, then `Set α × Set β` is in bijective correspondence to `Set γ`.

  To help you along the way, some ways to reformulate the hypothesis are given,
  which might be more useful than the stated hypotheses. -/
lemma exercise3_10 {f : α → γ} {g : β → γ} (hf : Injective f) (hg : Injective g)
    (h1 : range f ∩ range g = ∅) (h2 : range f ∪ range g = univ) :
    ∃ (L : Set α × Set β → Set γ) (R : Set γ → Set α × Set β), L ∘ R = id ∧ R ∘ L = id := by
  -- h1' and h1'' will be useful as arguments to `simp` to simplify your goal.
  have h1' : ∀ x y, f x ≠ g y
  · intro x y h
    apply h1.subset
    exact ⟨⟨x, h⟩, ⟨y, rfl⟩⟩
  have h1'' : ∀ y x, g y ≠ f x
  · intro x y
    symm
    apply h1'
  have h2' : ∀ x, x ∈ range f ∪ range g := eq_univ_iff_forall.1 h2
  have hf' : ∀ x x', f x = f x' ↔ x = x' := fun x x' ↦ hf.eq_iff
  let L : Set α × Set β → Set γ :=
    fun (s, t) ↦ f '' s ∪ g '' t
  let R : Set γ → Set α × Set β :=
    fun s ↦ (f ⁻¹' s, g ⁻¹' s)
  use L
  use R
  constructor
  · ext s x
    obtain ⟨x, rfl⟩|⟨x, rfl⟩ := h2' x
    · simp [h1'', hf.eq_iff]
    · simp [h1', hg.eq_iff]
  · ext s x
    · simp [hf.eq_iff, h1'']
    · simp [hg.eq_iff, h1']
