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
  rw[not_or] at h /-is that use of libary? -/
  have h1 : ¬ p := h.left
  have h2: ¬ ¬ p := h.right
  contradiction


/- ## Converging sequences

In the next few exercises, you prove more lemmas about converging sequences. -/

/-- From the lecture, the sequence `u` of real numbers converges to `l`. -/
def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

/- Let's prove that reindexing a convergent sequence
by a reindexing function that tends to infinity
produces a sequence that converges to the same value. -/
lemma exercise3_2 {s : ℕ → ℝ} {r : ℕ → ℕ} {a : ℝ}
    (hs : SequentialLimit s a) (hr : ∀ m : ℕ, ∃ N : ℕ, ∀ n ≥ N, r n ≥ m) :
    SequentialLimit (s ∘ r) a := by
  intro ε hε
  obtain ⟨N, hN⟩ := hs ε hε
  obtain ⟨M, hM⟩ := hr N
  use M
  intro n hn
  specialize hM n hn
  specialize hN (r n) hM
  simp [hN]





/- Let's prove the squeeze theorem for sequences.
You will want to use the lemma in the library that states
`|a| < b ↔ -b < a ∧ a < b`. -/
lemma exercise3_3 {s₁ s₂ s₃ : ℕ → ℝ} {a : ℝ}
    (hs₁ : SequentialLimit s₁ a) (hs₃ : SequentialLimit s₃ a)
    (hs₁s₂ : ∀ n, s₁ n ≤ s₂ n) (hs₂s₃ : ∀ n, s₂ n ≤ s₃ n) :
    SequentialLimit s₂ a := by
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := hs₁ (ε / 2) (by linarith)
  obtain ⟨N₃, hN₃⟩ := hs₃ (ε / 2) (by linarith)
  use max N₁ N₃
  intro n hn
  calc
    |s₂ n - a| ≤ |s₃ n - s₂ n|  :=  by sorry
    _ < ε / 2 + ε / 2 :=  by sorry
    _ = ε := by linarith


/- Let's prove that the sequence `n ↦ 1 / (n+1)` converges to `0`.
  It will be useful to know that if `x : ℝ` then `⌈x⌉₊ : ℕ` is `x` rounded up
  (in fact, it's rounded up to 0 if `x ≤ 0`). You will need some lemmas from the library, and `simp`
  will be useful to simplify.
  In the goal you will see `↑n`. This is the number `n : ℕ` interpreted as a real number `↑n : ℝ`.
  To type this number yourself, you have to write `(n : ℝ)`.
-/
#check ⌈π⌉₊
#check fun n : ℕ ↦ (n : ℝ)

lemma one_div_lt_div_eq_gt {a b : ℝ} (hb : a > 0) (hd : b > 0) : 1 / a < 1 / b ↔  b < a := by
  rw[lt_div_iff hd, div_eq_mul_one_div, one_mul, mul_comm,mul_div, mul_one]
  apply div_lt_one
  assumption

lemma exercise3_4 : SequentialLimit (fun n ↦ 1 / (n+1)) 0 := by
  intro ε hε
  let N := ⌈1 / ε⌉₊
  use N
  intro n hn
  simp
  have hε':  1 / ε ≤ ⌈1 / ε⌉₊ := by apply le_ceil
  have hε'': ε ≥ 1 / ⌈1 / ε⌉₊ := by calc
    ε = 1 / (1 / ε) := by simp
    _ ≥ 1 / ⌈1 / ε⌉₊ := by apply one_div_le_one_div_of_le; apply div_pos; linarith; apply hε; apply hε'
  have N': (N : ℝ) > 0 := by calc
    (N : ℝ) ≥ 1 / ε := by apply hε'
    _ > 0 := by apply one_div_pos.2; apply hε
  have hn': 0 < (n : ℝ) := by
    calc
      0 < (N:ℝ)  := by simp at N'; simp; apply N'
      _ ≤ (n:ℝ) := by simp; simp at hn; apply hn

  calc
    |((n : ℝ) + 1)⁻¹| = |1 / ((n : ℝ) + 1)| := by ring
    _ = 1 / ((n : ℝ) + 1) := by apply abs_of_pos; apply one_div_pos.2; linarith
    _ < 1 / (n : ℝ) := by apply one_div_lt_one_div_of_lt; apply hn'; linarith
    _ ≤ 1 / N := by apply one_div_le_one_div_of_le; apply N'; simp at hn; simp; apply hn
    _ = 1 / ⌈1 / ε⌉₊ := by rfl
    _ ≤ ε := by apply hε''




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
    convergesTo_mul_const (-1) exercise3_4
  simp at this
  simp [neg_div, this]

lemma exercise3_5 : SequentialLimit (fun n ↦ sin n / (n+1)) 0 := by
  intro ε hε
  let N := ⌈1 / ε⌉₊
  use N
  intro n hn
  simp
  apply abs_lt.2
  have hε' : ε ≥  1 / N := by calc
    ε = 1 / (1 / ε) := by simp
    _ ≥  1 / N := by apply one_div_le_one_div_of_le; simp; apply hε; simp; apply le_ceil
  have hn' : (n : ℝ) > 0 := by
    calc
      0 < (N:ℝ)  := by simp; apply hε
      _ ≤ (n:ℝ) := by simp at hn; simp; apply hn

  constructor
  calc
    -ε ≤  -(1 / N) := by apply neg_le_neg; apply hε'
    _ ≤ -(1 / n) := by apply neg_le_neg; apply one_div_le_one_div_of_le; simp; apply hε; simp at hn; simp; apply hn
    _ < -(1 / (n + 1)) := by apply neg_lt_neg; apply one_div_lt_one_div_of_lt; apply hn'; linarith
    _ =  -1 / (n + 1) := by ring
    _ ≤  sin (n) / (n + 1) := by apply div_le_div_of_le; linarith; apply neg_one_le_sin

  calc
    sin (n) / (n + 1) ≤ 1 / (n + 1) := by apply div_le_div_of_le;  linarith; apply sin_le_one
    _ < 1 / n := by apply one_div_lt_one_div_of_lt; simp; simp at hn'; apply hn'; linarith
    _ ≤ 1 / N := by apply one_div_le_one_div_of_le; simp; apply hε; simp; simp at hn; apply hn
    _ ≤ ε := by apply hε'



/- Now let's prove that if a convergent sequence is nondecreasing, then it must stay below the
limit. -/
def NondecreasingSequence (u : ℕ → ℝ) : Prop :=
  ∀ n m, n ≤ m → u n ≤ u m

lemma exercise3_6 (u : ℕ → ℝ) (l : ℝ) (h1 : SequentialLimit u l) (h2 : NondecreasingSequence u) :
    ∀ n, u n ≤ l := by
  intro n
  sorry





/- ## Sets

In the next few exercises, you prove more lemmas about converging sequences. -/


lemma exercise3_7 {α β : Type*} (f : α → β) (s : Set α) (t : Set β) :
    f '' s ∩ t = f '' (s ∩ f ⁻¹' t) := by simp [image_inter_preimage]


lemma pow_le_pow_of_le_left_ex{a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) : a ^ n ≤ b ^ n := by{
  induction n with
  | zero => simp
  | succ n ih =>
    rw[pow_add, pow_one, pow_add, pow_one]
    apply mul_le_mul
    · apply ih
    · apply hab
    . apply ha
    . apply pow_nonneg; apply le_trans ha hab
}


lemma root_four: sqrt (4:ℝ) = 2 := by
  calc
    sqrt (4:ℝ) = sqrt ((2 ^ 2):ℝ) := by ring
    _ = |2| := by exact sqrt_sq_eq_abs 2
    _ = 2 := by simp

lemma exercise3_8 : (fun x : ℝ ↦ x ^ 2) ⁻¹' {y | y ≥ 4} = { x : ℝ | x ≤ -2 } ∪ { x : ℝ | x ≥ 2 } := by
  ext x
  simp
  have four : (4 : ℝ) = 2 ^ 2 := by ring
  have two_x : 2 ≤ |x| ↔ x ≤ -2 ∨ 2 ≤ x := by apply le_abs'
  rw[← two_x]
  constructor
  . intro h
    calc
      2 = sqrt (4: ℝ) := by symm; apply root_four
      _ ≤ sqrt ((x^2):ℝ)  := by apply Real.sqrt_le_sqrt; apply h
      _ = |x| := by exact sqrt_sq_eq_abs x

  . intro h
    calc
      4 = 2 ^ 2 := by ring
      _ ≤ |x| ^ 2:= by apply pow_le_pow_of_le_left_ex; linarith; apply h
      _ = x ^ 2 := by simp

 /-intro h
    calc
      2 = sqrt (4: ℝ) := by simp
      _ ≤ sqrt ((x^2):ℝ)  := by apply Real.sqrt_le_sqrt; apply h
      _ = (x ^ 2) ^ (1 / 2) := by sorry
      _ = x := by apply
      _ = |x| := by apply abs_of_nonneg; apply pow_nonneg; linarith-/



/- As mentioned in exercise 2, `α × β` is the cartesian product of the types `α` and `β`.
Elements of the cartesian product are denoted `(a, b)`, and the projections are `.1` and `.2`.
As an example, here are two ways to state when two elements of the cartesian product are equal. -/

variable {α β γ : Type*}
example (a a' : α) (b b' : β) : (a, b) = (a', b') ↔ a = a' ∧ b = b' := Prod.ext_iff
example (x y : α × β) : x = y ↔ x.1 = y.1 ∧ x.2 = y.2 := Prod.ext_iff

/- Hard exercise: Let's prove that if `f : α → γ` and `g : β → γ` are injective function whose
  ranges partition `γ`, then `Set α × Set β` is in bijective correspondence to `Set γ`.

  To help you along the way, some ways to reformulate the hypothesis are given,
  which might be more useful than the stated hypotheses.
  Remember: you can use `simp [hyp]` to simplify using hypothesis `hyp`. -/
lemma exercise3_9 {f : α → γ} {g : β → γ} (hf : Injective f) (hg : Injective g)
    (h1 : range f ∩ range g = ∅) (h2 : range f ∪ range g = univ) :
    ∃ (L : Set α × Set β → Set γ) (R : Set γ → Set α × Set β), L ∘ R = id ∧ R ∘ L = id := by
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
    fun (s, t) ↦ { x | ∃ y, x = f y ∧ y ∈ s } ∪ { x | ∃ y, x = g y ∧ y ∈ t }
  let R : Set γ → Set α × Set β :=
    fun s ↦ ({ x | ∃ y, x = y ∧ f y ∈ s }, { x | ∃ y, x = y ∧ g y ∈ s })
  sorry
