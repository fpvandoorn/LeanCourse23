import Mathlib

-- Start LeanCourse.Common
set_option warningAsError false

section
open Lean Parser Tactic

macro (name := ring) "ring" : tactic =>
  `(tactic| first | ring1 | ring_nf)

macro (name := ring_at) "ring" cfg:config ? loc:location : tactic =>
  `(tactic| ring_nf $cfg ? $loc)

end

namespace Nat
open Lean Elab Term Meta

def elabIdentFactorial : TermElab := fun stx expectedType? =>
  match stx with
  | `($name:ident) => do
    let name := name.getId
    if name.hasMacroScopes then
      -- I think this would mean the name appears from within a quote.
      -- I'm not sure how to properly deal with this, and it seems ok to just not.
      throwUnsupportedSyntax
    else
      try
        elabIdent stx expectedType?
      catch e =>
        match name with
        | .str n s =>
          if s.endsWith "!" then
            let name' := Name.str n (s.dropRight 1)
            try
              elabTerm (← `(Nat.factorial $(mkIdent name'))) expectedType?
            catch _ =>
              throw e
          else
            throw e
        | _ => throw e
  | _ => throwUnsupportedSyntax

attribute [scoped term_elab ident] elabIdentFactorial

attribute [eliminator] Nat.recAux

@[elab_as_elim]
def two_step_induction {P : ℕ → Sort*} (zero : P 0) (one : P 1)
    (step : ∀ (k : ℕ), (IH0 : P k) → (IH1 : P (k + 1)) → P (k + 2)) (n : ℕ) :
    P n := by
  induction n using Nat.strongRec with
  | ind n ih =>
    rcases n with _|n
    · exact zero
    rcases n with _|n
    · exact one
    apply step
    · apply ih; linarith
    · apply ih; linarith



end Nat

namespace Filter
variable {α β : Type*} {m : α → β}
@[gcongr]
theorem map_le_map {F G : Filter α} (h : F ≤ G) : map m F ≤ map m G :=
  map_mono h

@[gcongr]
theorem comap_le_comap {F G : Filter β} (h : F ≤ G) : comap m F ≤ comap m G :=
  comap_mono h
end Filter

attribute [gcongr] interior_mono closure_mono

section ExtraLemmas

lemma pow_self_ne_zero (n : ℕ) : n ^ n ≠ 0 := by
  by_cases hn : n = 0
  · simp [hn]
  · positivity

open Real

attribute [simp] div_left_inj' neg_eq_self_iff eq_neg_self_iff sqrt_eq_zero' Int.ModEq.rfl

end ExtraLemmas
-- END LeanCourse.Common

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
  ∃ L : IntermediateField ℚ  ℂ ,  z ∈ L ↔
  \ -/

lemma Classfication_z_in_M_inf (M : Set Point) (z : Point) :
  z ∈ M_inf M ↔ ∃ m : ℕ , ((2  : ℕ) ^ m : WithBot ℕ) = Polynomial.degree (minpoly (K_zero M) z.x)
   := sorry


lemma K_zero_eq_ration (M : Set Point) : M = {⟨0,0⟩ ,⟨1,0⟩} → (K_zero M) = ℚ := sorry


section constructionDoubleCube

noncomputable def P : (Polynomial ℚ) := X ^ 3 - 2 --TODO: Tidy up

lemma P_irreducible : Irreducible P := by sorry

lemma third_root_of_two_not_in_M_inf (M := {⟨0,0⟩ ,⟨1,0⟩}) :
  (⟨(2 : ℝ) ^ (1/3), 0⟩ : Point) ∉ M_inf M := by
  by_contra h
  rw[constructionProof.Classfication_z_in_M_inf M ⟨(2 : ℝ) ^ (1/3), 0⟩] at h
  obtain ⟨m, hm⟩ := h

  have p : minpoly ℚ (2  ^ (1/3): ℂ ) = X ^ 3 - 2 := by
    symm
    apply minpoly.eq_of_irreducible_of_monic
    case hp1 => exact P_irreducible
    case hp2 => sorry
      /- simp
      calc
        _ = 2 ^ ((1/3) * 3) - 2 := by exact rfl
        _ = 2 - 2 := by norm_num
        _ = 0 := by simp -/ -- Worng 0 not of Type @OfNat.ofNat ℂ 0 Zero.toOfNat0 : ℂ
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
