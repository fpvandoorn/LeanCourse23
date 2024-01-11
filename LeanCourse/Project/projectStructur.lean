import Mathlib

set_option autoImplicit true
open FiniteDimensional Polynomial
open scoped Classical Polynomial

structure Point where x : ℂ

def G (z₁ z₂ : Point): Set Point := {z : Point | ∃ r : ℝ, z.x = ((r : ℂ) * z₁.x + 1 - r * z₂.x)}
def C (z₁ : Point) (r : ℝ): Set Point := {z : Point | (z.x.re - z₁.x.re) ^ 2 + ( z.x.im -  z₁.x.im) ^ 2 = r}

def Z_one_M (M : Set Point) : Set Point := {z : Point| ∃ z₁ z₂ z₃ z₄ : Point,  z ∈ (G z₁ z₂ ∩ G z₃ z₄) ∧ z₁ ≠ z₃ ∧ z₁ ≠ z₄ ∧ z₁ ∈ M ∧ z₂ ∈ M ∧ z₃ ∈ M ∧ z₄ ∈ M}
def Z_two_M (M : Set Point) : Set Point := {z : Point| ∃ z₁ z₂ z₃ z₄ z₅ : Point,  z ∈ (G z₁ z₂ ∩ C z₃ (Complex.normSq (z₄.x -  z₅.x))) ∧ z₄ ≠ z₅ ∧  z₁ ∈ M ∧ z₂ ∈ M ∧ z₃ ∈ M ∧ z₄ ∈ M ∧ z₅ ∈ M}
def Z_three_M (M : Set Point) : Set Point := {z : Point| ∃ z₁ z₂ z₃ z₄ z₅ z₆ : Point,  z ∈ (C z₁ (Complex.normSq (z₂.x -  z₃.x)) ∩ C z₄ (Complex.normSq (z₅.x -  z₆.x))) ∧ z₁ ≠ z₄ ∧ z₂ ≠ z₃ ∧ z₅ ≠ z₆ ∧ z₁ ∈ M ∧ z₂ ∈ M ∧ z₃ ∈ M ∧ z₄ ∈ M ∧ z₅ ∈ M ∧ z₆ ∈ M}

def Z_M (M : Set Point) : Set Point := M ∪ Z_one_M M ∪ Z_two_M M ∪ Z_three_M M

def M_I (M : Set Point) : ℕ → Set Point
  | 0 => M
  | (Nat.succ n) => Z_M (M_I M n)

def M_inf (M : Set Point) : Set Point := ⋃ n : ℕ, M_I M n

noncomputable def K_zero (M : Set Point) : IntermediateField ℚ  ℂ := IntermediateField.adjoin ℚ ({(z.x : ℂ)  | z ∈ M} ∪ {(z.x.re - z.x.im : ℂ)  | z ∈ M})

theorem Classfication_z_in_M_inf (M : Set Point) (z : Point) :
z ∈ M_inf M ↔
  ∃ (n : ℕ) (L : ℕ →  (IntermediateField ℚ ℂ)) (H : ∀ i,  Module (L i) (L (i + 1))),
  z.x ∈ L n ∧  K_zero M = L 0 ∧ (∀ i < n, FiniteDimensional.finrank (L i) (L (i + 1)) = 2) := by sorry

lemma Classfication_z_in_M_inf_2m (M : Set Point) (z : Point) :
  z ∈ M_inf M ↔ ∃ m : ℕ , ((2  : ℕ) ^ m : WithBot ℕ) = Polynomial.degree (minpoly (K_zero M) z.x) := sorry

def is_complex_rational (z : ℂ) : Prop :=
  ∃ (q : ℚ), z.re = q ∧ z.im = 0

lemma K_zero_eq_rational_if_M_sub_Q (M : Set Point) (h : M ⊆ {z : Point | is_complex_rational z.x}) : K_zero M = ℚ := sorry


section constructionDoubleCube
noncomputable def P' : (Polynomial ℚ) := monomial 3 1 - 2 -- x^3 - 2

lemma P'_irreducible : Irreducible P' := sorry --! Use den_dvd_of_is_root as Rational root theorem

lemma third_root_of_two_not_in_M_inf (M := {⟨0,0⟩ ,⟨1,0⟩}) :
  (⟨(2 : ℝ) ^ (1/3), 0⟩ : Point) ∉ M_inf M := sorry

end constructionDoubleCube


section constructionAngleTrisection
noncomputable def H : Polynomial ℚ := monomial 3 8 - monomial 1 6 - 1 -- 8x^3 - 6x - 1
noncomputable def H' : Polynomial ℚ := monomial 3 1 - monomial 1 6/8 - 1/8 -- x^3 - 6/8 x - 1/8

lemma H_irreducible : Irreducible H := sorry --! Use den_dvd_of_is_root as Rational root theorem

lemma pi_third_not_in_M_inf (M := {⟨0,0⟩ ,⟨1,0⟩,  ⟨Complex.exp (Real.pi/3)⟩ }) :
  (⟨Complex.exp ((Real.pi/3)/3)⟩ : Point) ∉ M_inf M := sorry

lemma Angle_not_Trisectable(M := {⟨0,0⟩ ,⟨1,0⟩, ⟨Complex.exp (α)⟩}) :
  ∃ (α : ℂ), (⟨Complex.exp (α/3)⟩ : Point) ∉ M_inf M := by
  use (Real.pi/3)
  exact pi_third_not_in_M_inf M

end constructionAngleTrisection
