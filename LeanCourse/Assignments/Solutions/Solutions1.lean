import LeanCourse.Common

/-

* Make sure to follow the instructions in the README to install Lean and set up this repository locally.

* Read chapter 1 and sections 2.1 and 2.2 in Mathematics in Lean.
  https://leanprover-community.github.io/mathematics_in_lean

* Do the following exercises (you don't have to hand these in):
  - `LeanCourse/MIL/C02_Basics/S01_Calculating.lean`
  - `LeanCourse/MIL/C02_Basics/S02_Proving_Identities_in_Algebraic_Structures.lean`
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 20.10.2023.
-/

/-
Do the next exercise using only the `rw` tactic with lemmas `add_comm` and `add_assoc`.
-/

lemma exercise1_1 (a b c d : ℝ) : a + b + c + d = d + (b + a) + c := by
  rw [add_comm a b, add_assoc d, add_comm d]


/-
Also do the proof using `calc`, where on each `calc` line, you use `rw` only once.
-/
lemma exercise1_2 (a b c d : ℝ) : a + b + c + d = d + (b + a) + c := by
  calc a + b + c + d
      = b + a + c + d := by rw [add_comm a b]
    _ = d + (b + a + c) := by rw [add_comm d]
    _ = d + (b + a) + c := by rw [add_assoc d]

/-
Do the following exercise using the `rw` tactic only.

The following lemmas may be useful.

`pow_two x       : x^2 = x*x`
`mul_add a b c   : a*(b + c) = a*b + a*c`
`add_mul a b c   : (a + b)*c = a*c + b*c`
`mul_sub a b c   : a*(b - c) = a*b - a*c`
`sub_mul a b c   : (a - b)*c = a*c - b*c`
`add_sub a b c   : a + (b - c) = (a + b) - c`
`sub_add a b c   : a - b + c = a - (b - c)`
`add_assoc a b c : (a + b) + c = a + (b + c)`
`sub_sub a b c   : a - b - c = a - (b + c)`
`sub_self a      : a - a = 0`
`add_zero a      : a + 0 = a`
`zero_add a      : 0 + a = a`
-/

lemma exercise1_3 (a b : ℝ) : (a + b) * (a - b) = a^2 - b^2 := by
  rw [pow_two a]
  rw [pow_two b]
  rw [mul_sub (a+b) a b]
  rw [add_mul a b a]
  rw [add_mul a b b]
  rw [mul_comm b a]
  rw [← sub_sub]
  rw [← add_sub]
  rw [sub_self]
  rw [add_zero]

-- Now redo it with `ring`.

lemma exercise1_4 (a b : ℝ) : (a + b) * (a - b) = a^2 - b^2 := by ring
