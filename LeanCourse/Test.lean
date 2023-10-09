import Mathlib.Tactic

/- This is a test file. Lean is configured correctly if you see the output "32" when
  mousing over or clicking on the next line, and you see no other errors in this file. -/
#eval 2 ^ 5

example {G : Type} [Group G] (x : G) : x * x⁻¹ = 1 := by simp