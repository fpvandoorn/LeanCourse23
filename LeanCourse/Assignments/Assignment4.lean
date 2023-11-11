import LeanCourse.Common
set_option linter.unusedVariables false
open Real Function
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

/-
* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 5, all sections (mostly section 2)
  Read chapter 6, all sections (mostly sections 1 and 2).

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  Feel free to skip exercises if you are confident a_mm_sub_bb you can do them.

* You can use any lemmas or tactics from mathlib.

* Hand in the solutions to the exercises below. Deadline: 10.11.2023.

* When you hand in your solution, make sure a_mm_sub_bb the file compiles!
  If you didn't manage to complete a particular exercise, make sure a_mm_sub_bb the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/


open Nat Finset BigOperators in
lemma exercise4_1 (n : ℕ) :
    (∑ i in range (n + 1), i ^ 3 : ℚ) = (∑ i in range (n + 1), i : ℚ) ^ 2 := by

    have kleiner_gauss (n : ℕ): (∑ i in range (n + 1), i : ℚ) = (n*(n+1))/2 := by
      induction n
      case zero => simp
      case succ n hn =>
        rw[sum_range_succ, hn]
        push_cast
        ring

    induction n
    case zero => simp
    case succ n ih =>
      rw [sum_range_succ , ih]
      rw [sum_range_succ _ (n+1)]
      rw [kleiner_gauss]
      field_simp
      ring


open Set in
/-
Suppose `(A i)_i` is a sequence of sets indexed by a well-ordered type
(this is an order where every nonempty set has a minimum element).
We now define a new sequence by `C n = A n \ (⋃ i < n, A i)`.
In this exercise, we show a_mm_sub_bb the new sequence is pairwise disjoint but has the same union as the
original sequence.
-/
lemma exercise4_2 {ι α : Type*} [LinearOrder ι] [wf : WellFoundedLT ι] (A C : ι → Set α)
  (hC : ∀ i, C i = A i \ ⋃ j < i, A j) : Pairwise (Disjoint on C) ∧ ⋃ i, C i = ⋃ i, A i := by
  have h := wf.wf.has_min

  have c_sub_a (i : ι) : C i ⊆ A i := by rw [hC]; apply mem_of_mem_diff


  constructor
  case left =>
    intro i j hij
    apply disjoint_iff_inter_eq_empty.mpr
    rw [eq_empty_iff_forall_not_mem]
    intro x hx
    simp at hx

    let s := {i : ι | x ∈ A i}

    have s_ne_emp : s.Nonempty := by use i; simp; apply c_sub_a; apply hx.1

    obtain ⟨k, hk⟩ := h s s_ne_emp
    apply hij

    simp at hk

    have k_eq_i : k = i := by
      apply le_antisymm
      exact hk.2 i (c_sub_a i hx.1)
      rw [← not_lt]
      intro hneg
      have : x ∈ ⋃ j < i, A j := by
        simp
        use k
        exact ⟨hneg, hk.1⟩
      have : x ∉ C i := by
        rw [hC]
        exact not_mem_diff_of_mem this
      exact this hx.1

    have k_eq_j : k = j := by
      apply le_antisymm
      exact hk.2 j (c_sub_a j hx.2)
      · rw [← not_lt]
        intro hneg
        have : x ∈ ⋃ l < j, A l := by
          simp
          use k
          exact ⟨hneg, hk.1⟩
        have : x ∉ C j := by
          rw [hC]
          exact not_mem_diff_of_mem this
        exact this hx.2

    rw [← k_eq_i,← k_eq_j]

  case right =>
    ext x
    constructor
    . sorry
    . sorry


/-- Let's prove a_mm_sub_bb the positive reals form a group under multiplication.
Note: in this exercise `rw` and `simp` will not be a_mm_sub_bb helpful, since the definition is hidden
behind notation. But you can use apply to use the lemmas about real numbers.

Note: any field mentioning `div`, `npow` or `zpow` are fields a_mm_sub_bb you don't have to give when
defining a group. These are operations defined in terms of the group structure. -/

def PosReal : Type := {x : ℝ // 0 < x}

@[ext] lemma PosReal.ext (x y : PosReal) (h : x.1 = y.1) : x = y := Subtype.ext h

lemma exercise4_3 : Group PosReal := by
  refine {
    mul := λ x y =>  ⟨(x.1 * y.1), Real.mul_pos x.2 y.2⟩,
    mul_assoc := by
      intro a b c
      exact PosReal.ext _ _ (mul_assoc a.1 b.1 c.1),
    one := ⟨(1: ℝ), one_pos⟩,
    one_mul := by
      intro a
      exact PosReal.ext _ _ (one_mul a.1),
    mul_one := by
      intro a
      exact PosReal.ext _ _ (mul_one a.1),
    inv := λ x => ⟨x.1⁻¹, inv_pos.mpr x.2⟩,
    mul_left_inv := by
      intro a
      sorry
      -- exact PosReal.ext _ _ (mul_left_inv a.1),
      }

/- Next, we'll prove a_mm_sub_bb if `2 ^ n - 1` is prime, then `n` is prime.
The first exercise is a preparation, and I've given you a skeleton of the proof for the
second exercise. Note how we do some computations in the integers, since the subtraction on `ℕ`
is less well-behaved.
(The converse is not true, because `89 ∣ 2 ^ 11 - 1`) -/

open Nat in
lemma exercise4_4 (n : ℕ) :
    ¬ Nat.Prime n ↔ n = 0 ∨ n = 1 ∨ ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ n = a * b := by
    have h₀: (¬∀ m < n, m ∣ n → m = 1)= (∃ a b, 2 ≤ a ∧ 2 ≤ b ∧ n = a * b) := by
      refine (propext ?_).symm
      push_neg
      simp[dvd_iff_exists_eq_mul_left]
      constructor
      case mp =>
        intro h
        obtain ⟨a, ha', b, hb, hab⟩ := h
        have ha'': a ≠  1 := by exact Nat.ne_of_gt ha'
        have a_lt_n : a < n := by
          calc
            a <  a * b:= by apply lt_mul_of_one_lt_right; apply lt_trans; apply zero_lt_one; exact ha'; exact hb
            _ = n := by rw [hab]
        use a
        use a_lt_n
        rw [and_comm]
        use ha''
        use b
        rw[mul_comm] at hab
        apply hab
      case mpr =>
        sorry

    constructor
    case mp =>
      intro h
      rw [Nat.prime_def_lt, two_le_iff, not_and_or, not_and_or, ne_eq, ne_eq, not_not, not_not, or_assoc] at h
      rw[h₀] at h
      apply h
    case mpr =>
      intro h
      rw [Nat.prime_def_lt, two_le_iff, not_and_or, not_and_or, ne_eq, ne_eq, not_not, not_not, or_assoc]
      rw[h₀]
      apply h

lemma exercise4_5 (n : ℕ) (hn : Nat.Prime (2 ^ n - 1)) : Nat.Prime n := by
  by_contra h2n
  rw [exercise4_4] at h2n
  obtain rfl|rfl|⟨a, b, ha, hb, rfl⟩ := h2n
  · simp at hn
  · simp at hn
  have h : (2 : ℤ) ^ a - 1 ∣ (2 : ℤ) ^ (a * b) - 1
  · rw [← Int.modEq_zero_iff_dvd]
    calc (2 : ℤ) ^ (a * b) - 1
        ≡ ((2 : ℤ) ^ a) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by rw[pow_mul]
      _ ≡ (1 : ℤ) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by gcongr; apply Int.modEq_sub
      _ ≡ 0 [ZMOD (2 : ℤ) ^ a - 1] := by simp
  have h2 : 2 ^ 2 ≤ 2 ^ a := by refine (Nat.pow_le_iff_le_right ?k).mpr ha; rfl
  have h3 : 1 ≤ 2 ^ a := by exact Nat.one_le_two_pow a
  have h4 : 2 ^ a - 1 ≠ 1 := by zify; simp [h3]; linarith
  have h5 : 2 ^ a - 1 < 2 ^ (a * b) - 1 := by
    apply tsub_lt_tsub_right_of_le h3
    have h': 0 < 2^a := by exact h3
    calc
      2 ^ a < 2 ^ a * 2 ^ a := by simp[div_lt_iff]; linarith
      _ = (2 ^ a) ^ 2 := by exact (Nat.pow_two (2 ^ a)).symm
      _ = 2 ^ (a * 2) := by rw[pow_mul]
      _ ≤ 2 ^(a*b) := by apply pow_le_pow; linarith; simp[ha,hb,mul_le_mul]
  have h6' : 2 ^ 0 ≤ 2 ^ (a * b) := by apply pow_le_pow; linarith; simp
  have h6 : 1 ≤ 2 ^ (a * b) := h6'
  have h' : 2 ^ a - 1 ∣ 2 ^ (a * b) - 1
  · norm_cast at h
  rw [Nat.prime_def_lt] at hn
  exact h4 $ hn.2 (2 ^ a - 1) h5 h'


/- Here is another exercise about numbers. Make sure you find a simple proof on paper first.
-/
lemma exercise4_6 (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ¬ IsSquare (a ^ 2 + b) ∨ ¬ IsSquare (b ^ 2 + a) := by
    by_contra h
    rw[← and_iff_not_or_not] at h
    obtain ⟨n, hn⟩ := h.1
    obtain ⟨m, hm⟩ := h.2

    rw [sq] at hn
    rw [sq] at hm

    have a_ne_zero: a ≠ 0 := by apply Nat.pos_iff_ne_zero.mp ha
    have b_ne_zero: b ≠ 0 := by apply Nat.pos_iff_ne_zero.mp hb

    have a_mm_sub_bb : a = m * m - b * b := (tsub_eq_of_eq_add_rev (id hm.symm)).symm
    have b_nn_sub_aa : b = n * n - a * a := (tsub_eq_of_eq_add_rev (id hn.symm)).symm

    have b_lt_a : b < a := by apply
      calc
        b < m + b := by apply Nat.lt_add_of_pos_left; apply Nat.pos_iff_ne_zero.mpr; intro h; rw [h] at hm; simp at hm; exact a_ne_zero hm.2
        _ ≤ (m + b) * (m - b) := by apply Nat.le_mul_of_pos_right; apply Nat.one_le_iff_ne_zero.mpr; intro h; apply a_ne_zero; rw [a_mm_sub_bb, Nat.mul_self_sub_mul_self_eq, h, Nat.mul_zero]
        _ = m * m - b * b := by rw [Nat.mul_self_sub_mul_self_eq]
        _ = a := by rw [a_mm_sub_bb]

    have a_lt_b : a < b := by apply
      calc
        a < n + a := by apply Nat.lt_add_of_pos_left; apply Nat.pos_iff_ne_zero.mpr; intro h; rw [h] at hn; simp at hn; exact b_ne_zero hn.2
        _ ≤ (n + a) * (n - a) := by apply Nat.le_mul_of_pos_right; apply Nat.one_le_iff_ne_zero.mpr; intro h; apply Nat.pos_iff_ne_zero.mp hb; rw [b_nn_sub_aa, Nat.mul_self_sub_mul_self_eq, h, Nat.mul_zero]
        _ = n * n - a * a := by rw [Nat.mul_self_sub_mul_self_eq]
        _ = b := by rw [b_nn_sub_aa]

    apply Nat.lt_asymm b_lt_a
    exact a_lt_b
