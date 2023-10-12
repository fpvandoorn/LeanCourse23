import LeanCourse.Common
import Mathlib.Algebra.Order.Floor
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Irrational

def EvenNat (n : Nat) := Even n

def OddNat (n : Nat) := Odd n

lemma even_double (n : Nat) : EvenNat (2*n) := even_two_mul n

lemma odd_succ_even (n : Nat) (h : EvenNat n) : OddNat (n + 1) := by
  refine Even.add_odd h ?_
  norm_num

lemma even_succ_odd (n : Nat) (h : OddNat n) : EvenNat (n + 1) := by
  refine Odd.add_odd h ?_
  norm_num

lemma odd_succ_double (n : Nat) : OddNat (2*n + 1) := odd_two_mul_add_one n

def continuous (f : ℝ → ℝ) := Continuous f

lemma continuous_Id : continuous (fun x : ℝ ↦ x) := continuous_id

def differentiable (f : ℝ → ℝ) := Differentiable ℝ f

lemma differentiable.continuous (f : ℝ → ℝ) (h : differentiable f) : continuous f :=
Differentiable.continuous h

lemma differentiable_identity : differentiable (fun x : ℝ ↦ x) := differentiable_id

noncomputable def floor : ℝ → ℝ := fun x ↦ ⌊x⌋

notation (priority := high) "⌊" a "⌋" => floor a

lemma differentiable_cst (a : ℝ) : differentiable fun _ ↦ a := differentiable_const a

declare_aesop_rule_sets [obviously_continuous]

@[app_unexpander Exists] def unexpandExists' : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $_* => $_) => throw ()
  | `($(_) $p) => let x := Lean.mkIdent `x; `(∃ $x:ident, $p $x)
  | _ => throw ()
