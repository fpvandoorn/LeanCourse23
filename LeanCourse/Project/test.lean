import Mathlib

set_option autoImplicit true
open FiniteDimensional Polynomial
open scoped Classical Polynomial

--! This is a test whit use using ℂs and instead Complex numbers


def G (z₁ z₂ : ℂ): Set ℂ := {z : ℂ | ∃ r : ℝ, z = ((r : ℂ) * z₁ + 1 - r * z₂)}
def C (z₁ : ℂ) (r : ℝ): Set ℂ := {z : ℂ | (z.re - z₁.re) ^ 2 + ( z.im -  z₁.im) ^ 2 = r}

def Z_one_M (M : Set ℂ) : Set ℂ := {z : ℂ| ∃ z₁ z₂ z₃ z₄ : ℂ,  z ∈ (G z₁ z₂ ∩ G z₃ z₄) ∧ z₁ ≠ z₃ ∧ z₁ ≠ z₄ ∧ z₁ ∈ M ∧ z₂ ∈ M ∧ z₃ ∈ M ∧ z₄ ∈ M}
def Z_two_M (M : Set ℂ) : Set ℂ := {z : ℂ| ∃ z₁ z₂ z₃ z₄ z₅ : ℂ,  z ∈ (G z₁ z₂ ∩ C z₃ (Complex.normSq (z₄ -  z₅))) ∧ z₄ ≠ z₅ ∧  z₁ ∈ M ∧ z₂ ∈ M ∧ z₃ ∈ M ∧ z₄ ∈ M ∧ z₅ ∈ M}
def Z_three_M (M : Set ℂ) : Set ℂ := {z : ℂ| ∃ z₁ z₂ z₃ z₄ z₅ z₆ : ℂ,  z ∈ (C z₁ (Complex.normSq (z₂ -  z₃)) ∩ C z₄ (Complex.normSq (z₅ -  z₆))) ∧ z₁ ≠ z₄ ∧ z₂ ≠ z₃ ∧ z₅ ≠ z₆ ∧ z₁ ∈ M ∧ z₂ ∈ M ∧ z₃ ∈ M ∧ z₄ ∈ M ∧ z₅ ∈ M ∧ z₆ ∈ M}

def Z_M (M : Set ℂ) : Set ℂ := M ∪ Z_one_M M ∪ Z_two_M M ∪ Z_three_M M

def M_I (M : Set ℂ) : ℕ → Set ℂ
  | 0 => M
  | (Nat.succ n) => Z_M (M_I M n)

def M_inf (M : Set ℂ) : Set ℂ := ⋃ n : ℕ, M_I M n

noncomputable def K_zero (M : Set ℂ) : IntermediateField ℚ  ℂ := IntermediateField.adjoin ℚ ({(z : ℂ)  | z ∈ M} ∪ {(z.re - z.im : ℂ)  | z ∈ M})

theorem Classfication_z_in_M_inf (M : Set ℂ) (z : ℂ) :
z ∈ M_inf M ↔
  ∃ (n : ℕ) (L : ℕ →  (IntermediateField ℚ ℂ)) (H : ∀ i,  Module (L i) (L (i + 1))),
  z ∈ L n ∧  K_zero M = L 0 ∧ (∀ i < n, FiniteDimensional.finrank (L i) (L (i + 1)) = 2) := sorry

lemma Classfication_z_in_M_inf_2m (M : Set ℂ) (z : ℂ) :
  z ∈ M_inf M ↔ ∃ (m : ℕ) ,((2  : ℕ) ^ m : WithBot ℕ) = Polynomial.degree (minpoly (K_zero M) z) := sorry

def is_complex_rational (z : ℂ) : Prop :=
  ∃ (q : ℚ), z.re = q ∧ z.im = 0

lemma K_zero_eq_rational_if_M_sub_Q (M : Set ℂ) (h : M ⊆ {z : ℂ | is_complex_rational z}) : K_zero M = ℚ := by
  sorry
  --Todo ask how to use this: apply IntermediateField.adjoin_le_subfield or IntermediateField.adjoin_le_iff
#check IntermediateField.adjoin_le_subfield

section constructionDoubleCube
noncomputable def P : (Polynomial ℚ) := monomial 3 1 - 2 -- x^3 - 2
noncomputable def P' : (Polynomial ℚ) := X ^ 3 - 2 -- x^3 - 2

lemma P_eqq : P = P' := by simp[P, P']; symm; apply Polynomial.X_pow_eq_monomial


lemma P_irreducible : Irreducible P := by --! Use den_dvd_of_is_root as Rational root theorem
  sorry

lemma degree_third_root_of_two : Polynomial.degree (minpoly ℚ ((2 : ℝ) ^ (1/3))) = 3 := by
  have h: minpoly ℚ ((2 : ℝ) ^ (1/3)) = P := by
    symm
    apply minpoly.eq_of_irreducible_of_monic
    case hp1 => exact P_irreducible
    case hp2 =>
      simp[P]
      have h: ((2:ℝ) ^ (1/3:ℝ)) ^ 3 = 2 := by
        rw [one_div]
        change ((2:ℝ)  ^ (Nat.cast 3)⁻¹) ^ (3:ℝ) = _
        --rw [Real.rpow_nat_inv_pow_nat (show 2 ≥ 0 by norm_num) (show 3 ≠ 0 by decide)] --TODO: Needs Mathlib update
        sorry
      --rw[← one_div, h] --TODO: Needs Mathlib update
      sorry
    case hp3 => rw[P_eqq]; rw[Polynomial.Monic.def]; apply monic_X_pow_sub_C; simp
  rw[h, P_eqq]
  simp[P']
  apply Polynomial.degree_X_pow_sub_C
  linarith


lemma third_root_of_two_not_in_M_inf (M := {⟨0,0⟩ ,⟨1,0⟩}) :
  (⟨(2 : ℝ) ^ (1/3), 0⟩ : ℂ) ∉ M_inf M := by
  rw[Classfication_z_in_M_inf_2m M ⟨(2 : ℝ) ^ (1/3), 0⟩]
  by_contra h
  sorry

end constructionDoubleCube


section constructionAngleTrisection
noncomputable def H : Polynomial ℚ := monomial 3 8 - monomial 1 6 - 1 -- 8x^3 - 6x - 1
noncomputable def H' : Polynomial ℚ := monomial 3 1 - monomial 1 6/8 - 1/8 -- x^3 - 6/8 x - 1/8

lemma H_irreducible : Irreducible H := sorry --! Use den_dvd_of_is_root as Rational root theorem

lemma pi_third_not_in_M_inf (M := {⟨0,0⟩ ,⟨1,0⟩,  Complex.exp (Real.pi/3) }) :
  (Complex.exp ((Real.pi/3)/3) : ℂ) ∉ M_inf M := sorry

lemma Angle_not_Trisectable(M := {⟨0,0⟩ ,⟨1,0⟩, Complex.exp (α)}) :
  ∃ (α : ℂ), (Complex.exp (α/3) : ℂ) ∉ M_inf M := by
  use (Real.pi/3)
  exact pi_third_not_in_M_inf M

end constructionAngleTrisection
