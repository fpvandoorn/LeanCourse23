import Mathlib

open FiniteDimensional Polynomial
open scoped Classical Polynomial

noncomputable def P : (Polynomial ℚ) := monomial 3 1 - 2 -- x^3 - 2
noncomputable def P' : (Polynomial ℚ) := X ^ 3 - 2 -- x^3 - 2

lemma P_eqq : P = P' := by simp[P, P']; symm; apply Polynomial.X_pow_eq_monomial

lemma P_irreducible : Irreducible P := by
  rw[Polynomial.Monic.irreducible_iff_natDegree']
  . simp
    constructor
    case left => sorry
    case right => --This case
      sorry
  rw[P_eqq]; rw[Polynomial.Monic.def]; apply monic_X_pow_sub_C; simp
