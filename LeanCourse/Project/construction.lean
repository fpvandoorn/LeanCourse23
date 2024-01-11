import LeanCourse.Common
import Mathlib.FieldTheory.IntermediateField
import Mathlib.FieldTheory.Galois
import Mathlib.FieldTheory.Adjoin
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib

set_option autoImplicit true

open FiniteDimensional Polynomial

open scoped Classical Polynomial


namespace constructionProof

section constructionDef
-- Define point of the complex plane
structure Point where
  x : ℂ

-- Define a line in the complex plane
def G (z₁ z₂ : Point): Set Point := {z : Point | ∃ r : ℝ, z.x = ((r : ℂ) * z₁.x + 1 - r * z₂.x)}

-- Define a circle in the complex plane
def C (z₁ : Point) (r : ℝ): Set Point := {z : Point | (z.x.re - z₁.x.re) ^ 2 + ( z.x.im -  z₁.x.im) ^ 2 = r}

-- Def Z1 to Z3
def Z_one_M (M : Set Point) : Set Point := {z : Point| ∃ z₁ z₂ z₃ z₄ : Point,  z ∈ (G z₁ z₂ ∩ G z₃ z₄) ∧ z₁ ≠ z₃ ∧ z₁ ≠ z₄ ∧ z₁ ∈ M ∧ z₂ ∈ M ∧ z₃ ∈ M ∧ z₄ ∈ M}

def Z_two_M (M : Set Point) : Set Point := {z : Point| ∃ z₁ z₂ z₃ z₄ z₅ : Point,  z ∈ (G z₁ z₂ ∩ C z₃ (Complex.normSq (z₄.x -  z₅.x))) ∧ z₄ ≠ z₅ ∧  z₁ ∈ M ∧ z₂ ∈ M ∧ z₃ ∈ M ∧ z₄ ∈ M ∧ z₅ ∈ M}

def Z_three_M (M : Set Point) : Set Point := {z : Point| ∃ z₁ z₂ z₃ z₄ z₅ z₆ : Point,  z ∈ (C z₁ (Complex.normSq (z₂.x -  z₃.x)) ∩ C z₄ (Complex.normSq (z₅.x -  z₆.x))) ∧ z₁ ≠ z₄ ∧ z₂ ≠ z₃ ∧ z₅ ≠ z₆ ∧ z₁ ∈ M ∧ z₂ ∈ M ∧ z₃ ∈ M ∧ z₄ ∈ M ∧ z₅ ∈ M ∧ z₆ ∈ M}


-- Def Z(M)
def Z_M (M : Set Point) : Set Point := M ∪ Z_one_M M ∪ Z_two_M M ∪ Z_three_M M

-- Def M_I and M_inf
def M_I (M : Set Point) : ℕ → Set Point
  | 0 => M
  | (Nat.succ n) => Z_M (M_I M n)

def M_inf (M : Set Point) : Set Point := ⋃ n : ℕ, M_I M n

end constructionDef

section constructionGalois
-- Def K_0 ℚ(M ∪ M.conj)
--TODO: Chech if there is a way to define K_0 computable
noncomputable def K_zero (M : Set Point) : IntermediateField ℚ  ℂ := IntermediateField.adjoin ℚ ({(z.x : ℂ)  | z ∈ M} ∪ {(z.x.re - z.x.im : ℂ)  | z ∈ M})


/- theorem Classfication_z_in_M_inf (M : Set Point) (z : Point) :
z ∈ M_inf M ↔
∃ n : ℕ, n → L
 -/
lemma Classfication_z_in_M_inf_2m (M : Set Point) (z : Point) :
  z ∈ M_inf M ↔ ∃ m : ℕ , ((2  : ℕ) ^ m : WithBot ℕ) = Polynomial.degree (minpoly (K_zero M) z.x)
   := sorry


lemma K_zero_eq_ration (M : Set Point) : M = {⟨0,0⟩ ,⟨1,0⟩} → (K_zero M) = ℚ := by
  intro h
  unfold K_zero
  simp[h]
  sorry

section constructionDoubleCube

noncomputable def P : (Polynomial ℚ) := X ^ 3 - 2 --TODO: Tidy up
noncomputable def P' : (Polynomial ℚ) := monomial 3 1 - 2 --TODO: Tidy up

lemma P_irreducible : Irreducible P := by
  rw[P]
  by_contra h
  sorry

lemma third_root_of_two_not_in_M_inf (M := {⟨0,0⟩ ,⟨1,0⟩}) :
  (⟨(2 : ℝ) ^ (1/3), 0⟩ : Point) ∉ M_inf M := by
  by_contra h
  rw[constructionProof.Classfication_z_in_M_inf_2m M ⟨(2 : ℝ) ^ (1/3), 0⟩] at h
  obtain ⟨m, hm⟩ := h

  have p : minpoly ℚ (2  ^ (1/3): ℂ ) = X ^ 3 - 2 := by
    symm
    apply minpoly.eq_of_irreducible_of_monic
    case hp1 => exact P_irreducible
    case hp2 => sorry
    /- calc ↑(aeval (2 ^ (1 / 3))) (X ^ 3 - 2) --TODO: add simp_rpow https://github.com/teorth/symmetric_project/blob/master/SymmetricProject/Tactic/RPowSimp.lean#L305-L306
      _ = (((2 : ℝ) ^ (1 / 3 : ℝ)) ^ 3) - 2 := by sorry
      _ = 2 - 2 := by simp
      _ = 0 := by simp -/
    case hp3 => rw[Polynomial.Monic.def]; apply monic_X_pow_sub_C; simp
  have p_deg : Polynomial.degree (P) = 3 := by
    calc degree P
    _ = Polynomial.degree ((X ^ 3 - 2) : ℚ[X]) := by rw[P]
    _ = Polynomial.degree ((X ^ 3 - 2 * (X ^ 0)): ℚ[X]) := by simp
    _ = Polynomial.degree ((X ^ 3): ℚ[X]) := by sorry
    _ = 3 := by simp
  have KQ : (K_zero M) = ℚ := by apply K_zero_eq_ration; sorry --! Why does rfl not work here?
  --rw[KQ, p, p_deg] at hm
  have h' : ((2  : ℕ) ^ m : WithBot ℕ) ≠  3 := by
    induction m with
    | zero => simp
    | succ m hm => rw[pow_add]; simp; sorry
  --contradiction
  sorry

section constructionAngleTrisection

noncomputable def H : Polynomial ℚ := monomial 3 8 - monomial 1 6 - 1
noncomputable def H' : Polynomial ℚ := monomial 3 1 - monomial 1 (6/8) - (1/8)
noncomputable def H'' : Polynomial ℚ :=  monomial 0 (1/8)

lemma H_irred : Irreducible H := by
  by_contra h
  simp only [H] at h
  sorry

lemma unit_of_H' : IsUnit H'' := by
  refine isUnit_of_dvd_one ?h
  have h : monomial 0 (8 * (1/8)) =  8  * H'' := by
    rw[H'']
    symm
    apply Polynomial.C_mul_monomial
  simp at h
  exact Dvd.intro_left 8 (id h.symm)


lemma H'_irred : Irreducible H' := by
  have h : H' = H''* H := by
    simp[H,H',H'']
    sorry
  sorry  -- irreducible_units_mul

variable (α := π/3)
