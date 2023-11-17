import LeanCourse.Common
set_option linter.unusedVariables false
open Real Function
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

/-
* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 5, all sections (mostly section 2)
  Read chapter 6, all sections (mostly sections 1 and 2).

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  Feel free to skip exercises if you are confident that you can do them.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 10.11.2023.

* When you hand in your solution, make sure that the file compiles!
  If you didn't manage to complete a particular exercise, make sure that the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/


open Nat Finset BigOperators in
lemma exercise4_1 (n : ℕ) :
    (∑ i in range (n + 1), i ^ 3 : ℚ) = (∑ i in range (n + 1), i : ℚ) ^ 2 := by
  have : ∀ n, (∑ i in range (n + 1), i : ℚ) = n * (n + 1) / 2
  · intro n; induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih]
      push_cast
      ring
  rw [this]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

open Set in
/-
Suppose `(A i)_i` is a sequence of sets indexed by a well-ordered type
(this is an order where every nonempty set has a minimum element).
We now define a new sequence by `C n = A n \ (⋃ i < n, A i)`.
In this exercise, we show that the new sequence is pairwise disjoint but has the same union as the
original sequence.
-/
lemma exercise4_2 {ι α : Type*} [LinearOrder ι] [wf : WellFoundedLT ι] (A C : ι → Set α)
  (hC : ∀ i, C i = A i \ ⋃ j < i, A j) : Pairwise (Disjoint on C) ∧ ⋃ i, C i = ⋃ i, A i := by
  have h := wf.wf.has_min
  have lem1 : ∀ i j, i < j → Disjoint (C i) (C j)
  · intro i j hij
    simp [disjoint_left, hC]
    tauto
  constructor
  · intro i j hij
    obtain h|h := hij.lt_or_lt
    · exact lem1 i j h
    · exact (lem1 j i h).symm
  · apply subset_antisymm
    · gcongr with i
      rw [hC]
      exact?
    · simp [subset_def]
      intros x i hx
      obtain ⟨i₀, h1i₀, h2i₀⟩ := h { i : ι | x ∈ A i } ⟨i, hx⟩
      use i₀
      simp [hC]
      use h1i₀
      intro j hj h2j
      exact h2i₀ j h2j hj




/-- Let's prove that the positive reals form a group under multiplication.
Note: in this exercise `rw` and `simp` will not be that helpful, since the definition is hidden
behind notation. But you can use apply to use the lemmas about real numbers. -/

def PosReal : Type := {x : ℝ // 0 < x}

@[ext] lemma PosReal.ext (x y : PosReal) (h : x.1 = y.1) : x = y := Subtype.ext h

lemma exercise4_3 : Group PosReal where
  mul x y := ⟨x.1 * y.1, mul_pos x.2 y.2⟩
  mul_assoc x y z := by ext; apply mul_assoc
  one := ⟨1, by norm_num⟩
  one_mul x := by ext; apply one_mul
  mul_one x := by ext; apply mul_one
  inv x := ⟨x.1⁻¹, inv_pos.mpr x.2⟩
  mul_left_inv x := by ext; apply inv_mul_cancel; exact x.2.ne'


/- Next, we'll prove that if `2 ^ n - 1` is prime, then `n` is prime.
The first exercise is a preparation, and I've given you a skeleton of the proof for the
second exercise. Note how we do some computations in the integers, since the subtraction on `ℕ`
is less well-behaved.
(The converse is not true, because `89 ∣ 2 ^ 11 - 1`) -/

open Nat in
lemma exercise4_4 (n : ℕ) :
    ¬ Nat.Prime n ↔ n = 0 ∨ n = 1 ∨ ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ n = a * b := by
  rw [← or_assoc, ← Nat.le_one_iff_eq_zero_or_eq_one, ← not_lt, ← imp_iff_not_or, Nat.prime_def_lt']
  push_neg
  simp
  -- the easiest way is probably to apply `constructor` here,
  -- but we can also apply some congruence rules manually.
  apply imp_congr
  · rw?
  apply exists_congr
  intro k
  apply and_congr_right
  intro hk
  rw [dvd_def, ← exists_and_left]
  apply exists_congr
  intro l
  apply and_congr_left
  intro h
  subst h
  rw [succ_le]
  apply lt_mul_iff_one_lt_right
  linarith

lemma exercise4_5 (n : ℕ) (hn : Nat.Prime (2 ^ n - 1)) : Nat.Prime n := by
  by_contra h2n
  rw [exercise4_4] at h2n
  obtain rfl|rfl|⟨a, b, ha, hb, rfl⟩ := h2n
  · simp at hn
  · norm_num at hn
  have h : (2 : ℤ) ^ a - 1 ∣ (2 : ℤ) ^ (a * b) - 1
  · rw [← Int.modEq_zero_iff_dvd]
    calc (2 : ℤ) ^ (a * b) - 1
        ≡ ((2 : ℤ) ^ a) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by rw [pow_mul]
      _ ≡ (1 : ℤ) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by gcongr; exact?
      _ ≡ 0 [ZMOD (2 : ℤ) ^ a - 1] := by simp
  have h2 : 2 ^ 2 ≤ 2 ^ a := by gcongr; norm_num
  have h3 : 1 ≤ 2 ^ a := by linarith
  have h4 : 2 ^ a - 1 ≠ 1 := by zify; simp [h3]; linarith
  have h5 : 2 ^ a - 1 < 2 ^ (a * b) - 1 := by
    apply tsub_lt_tsub_right_of_le h3
    gcongr
    · norm_num
    refine lt_mul_right ?h2.hn hb
    linarith
  have h6' : 2 ^ 0 ≤ 2 ^ (a * b) := by gcongr; norm_num; exact?
  have h6 : 1 ≤ 2 ^ (a * b) := h6'
  have h' : 2 ^ a - 1 ∣ 2 ^ (a * b) - 1
  · norm_cast at h
  rw [Nat.prime_def_lt] at hn
  apply h4
  apply hn.2 _ h5
  norm_cast at h

lemma exercise4_6 (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ¬ IsSquare (a ^ 2 + b) ∨ ¬ IsSquare (b ^ 2 + a) := by
  have h1 : ∀ {a b : ℕ}, 0 < a → a ≤ b → ¬ IsSquare (b ^ 2 + a)
  · intro a b ha hab ⟨c, hc⟩
    rw [pow_two] at hc
    have : b * b < c * c := by linarith
    have : b < c := by exact?
    have : c * c < (b + 1) * (b + 1) := by linarith
    have : c < b + 1 := by exact?
    exact?
  obtain h|h := le_total a b
  · exact .inr (h1 ha h)
  · exact .inl (h1 hb h)
