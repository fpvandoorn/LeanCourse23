import LeanCourse.Common

namespace construction

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
