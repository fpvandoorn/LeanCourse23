import LeanCourse.Common
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.FieldTheory.Minpoly.Basic
set_option linter.unusedVariables false
noncomputable section
open Real Function BigOperators
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

/-
* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 7 and 8, all sections.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  Feel free to skip exercises if you are confident that you can do them.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 17.11.2023.

* When you hand in your solution, make sure that the file compiles!
  If you didn't manage to complete a particular exercise, make sure that the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/


section LinearMap

variable {R M₁ M₂ N : Type*} [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup N]
  [Module R M₁] [Module R M₂] [Module R N]

/- Define the coproduct of two linear maps that send (x, y) ↦ f x + g y. -/

def exercise5_1 (f : M₁ →ₗ[R] N) (g : M₂ →ₗ[R] N) : M₁ × M₂ →ₗ[R] N where
  toFun x := f x.1 + g x.2
  map_add' := by
    intro x y
    simp
    exact add_add_add_comm _ _ _ _
  map_smul' := by simp

example (f : M₁ →ₗ[R] N) (g : M₂ →ₗ[R] N) (x : M₁) (y : M₂) :
  exercise5_1 f g (x, y) = f x + g y := by rfl


end LinearMap

section Ring
variable {R : Type*} [CommRing R]


/- Let's define ourselves what it means to be a unit in a ring and then
  prove that the units of a ring form a group.
  Hint: I recommend that you first prove that the product of two units is again a unit,
  and that you define the inverse of a unit separately using `Exists.choose`.
  Hint 2: to prove associativity, use something like `intros; ext; apply mul_assoc`
  (`rw` doesn't work well because of the casts) -/

#check Exists.choose
#check Exists.choose_spec
def IsAUnit (x : R) : Prop := ∃ y, y * x = 1



instance exercise5_2 : Group {x : R // IsAUnit x} where
  one := ⟨1, by unfold IsAUnit; use 1; simp⟩
  mul := λ x y => ⟨x.1 * y.1, by
    unfold IsAUnit; unfold IsAUnit at x; unfold IsAUnit at y
    have h₁: ∃ z₁, z₁ * x.1 * y.1 = y.1 := by obtain ⟨z₁, hz₁⟩ := x.2; use z₁; rw [hz₁, one_mul]
    have h₂:  ∃ z₂, z₂  * y.1 = 1 := by obtain ⟨z₂, hz₂⟩ := y.2; use z₂;
    have h₃: ∃ z₃, z₃ * (x.1 * y.1) = 1 := by obtain ⟨z₁, hz₁⟩ := h₁; obtain ⟨z₂, hz₂⟩ := h₂; use z₂ * z₁; rw [mul_assoc z₂, ← mul_assoc z₁,  hz₁, hz₂]
    exact h₃⟩
  one_mul := by intro x; ext; exact one_mul x.1
  mul_one := by intro x; ext; exact mul_one x.1
  mul_assoc := by intro x y z; ext; exact mul_assoc x.1 y.1 z.1
  inv := λ x => ⟨Exists.choose (x.2) , by use x.1; rw[mul_comm, Exists.choose_spec x.2]⟩
  mul_left_inv := by
    intro a; ext;
    calc
    _ = (Exists.choose (a.2)) * a.1 := by rfl
    _ = 1 := by rw [Exists.choose_spec a.2]


-- you have the correct group structure if this is true by `rfl`
example (x y : {x : R // IsAUnit x}) : (↑(x * y) : R) = ↑x * ↑y := by rfl

end Ring



/- The Frobenius morphism in a field of characteristic p is the map `x ↦ x ^ p`.
Let's prove that the Frobenius morphism is additive, without using that
fact from the library. -/
#check CharP.cast_eq_zero_iff
#check Finset.sum_congr
variable (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [CharP K p] in
open Nat Finset in
lemma exercise5_3 (x y : K) : (x + y) ^ p = x ^ p + y ^ p := by
  rw [add_pow]
  have h2 : p.Prime := hp.out
  have h3 : 0 < p := h2.pos
  have h4 : range p = insert 0 (Ioo 0 p)
  · ext (_|_) <;> simp [h3]
  have h5 : ∀ i ∈ Ioo 0 p, p ∣ Nat.choose p i := by
    intro i hi
    simp at hi
    refine Prime.dvd_choose_self h2 ?hk hi.2
    symm
    exact Nat.ne_of_lt hi.1
  have h6 : ∑ i in Ioo 0 p, x ^ i * y ^ (p - i) * Nat.choose p i = 0 :=
    calc
      _ =  ∑ i in Ioo 0 p, x ^ i * y ^ (p - i) * 0 := by
        have h: ∀ i ∈  Ioo 0 p, x ^ i * y ^ (p - i) * Nat.choose p i = x ^ i * y ^ (p - i) * 0 := by
          intro i hi;
          have h': (Nat.choose p i : K) = 0 := by rw [CharP.cast_eq_zero_iff K p]; exact h5 i hi
          rw [h']
        apply sum_congr rfl h
      _ = 0 := by simp
  simp [sum_range_succ, tsub_self, _root_.pow_zero, mul_one, Nat.choose_self, mul_one, Finset.sum_insert left_not_mem_Ioo, Nat.choose_zero_right p, add_comm, h6, h4]



/- Let's prove that if `M →ₗ[R] M` forms a module over `R`, then `R` must be a commutative ring.
  To prove this we have to additionally assume that `M` contains at least two elements, and
`smul_eq_zero : r • x = 0 ↔ r = 0 ∨ x = 0` (this is given by the `NoZeroSMulDivisors` class).
-/
#check exists_ne
lemma exercise5_4 {R M M' : Type*} [Ring R] [AddCommGroup M] [Module R M] [Nontrivial M]
    [NoZeroSMulDivisors R M] [Module R (M →ₗ[R] M)]
    (h : ∀ (r : R) (f : M →ₗ[R] M) (x : M), (r • f) x = r • f x)
    (r s : R) : r * s = s * r := by
    by_contra h1
    have h2: r * s - s * r ≠ 0 := by exact mt sub_eq_zero.mp h1
    have h3: r * s - s * r = 0 := by
      let id: (M →ₗ[R] M) := LinearMap.id
      have : (r * s - s * r) • id = 0 := by sorry -- use Algebra 1 which i haven't heard yet
      sorry -- use obtain
    exact h2 h3

  /- have h1 : ∀ (r s : R) (f : M →ₗ[R] M) (x : M) , (r * s) • f x = (s * r) • f x := by
      intro r s f x
      calc (r * s ) • f x
      _ = ((r * s) • f) x := by sorry
      _ = (s * r) • f x := by sorry
    exact h1 r s (λ x ↦ x) 1 -/

  /- by_contra h1
  have h2 : r * s - s * r ≠ 0 := by exact mt sub_eq_zero.mp h1
  have h3 : r * s - s * r = 0 := by
    calc r * s - s * r
    _ = r * s - s * s + s * s - s * r := by rw [sub_add_cancel]
    _ =  (r - s) * s + s * (s - r) := by rw[← sub_mul, ← add_sub, ← mul_sub]
    _ = s * (r - s) + s * (s - r) := by sorry
    _ = s * (r - s + s - r) := by rw[←mul_add, add_sub]
    _ = 0 := by rw [sub_add_comm, sub_self, zero_add, sub_self, mul_zero]
  exact h2 h3 -/
