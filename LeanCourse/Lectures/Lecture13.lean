import LeanCourse.Common
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.Convolution
import Mathlib.Data.Real.Irrational
import Mathlib.MeasureTheory.Function.Jacobian
open BigOperators Function Set Real Topology
open MeasureTheory Interval Convolution ENNReal
noncomputable section
set_option linter.unusedVariables false
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)


/- # Today: Measure Theory and Integral Calculus

We cover the short chapter 11 from Mathematics in Lean. -/

/-
Last time we discussed differential analysis.
-/







example (a b : ℝ) : ∫ x in a..b, x = (b ^ 2 - a ^ 2) / 2 :=
  integral_id

example (f : ℝ → ℝ) : ℝ → ℝ := fun x ↦
  ∫ t in (0)..x, f t

example (a b : ℝ) : ∫ x in a..b, exp x = exp b - exp a :=
  integral_exp

/- the notation `[[a, b]]` (in namespace `Interval`) means `uIcc a b`, i.e.
the interval from `min a b` to `max a b` -/
example {a b : ℝ} (h : (0 : ℝ) ∉ [[a, b]]) : ∫ x in a..b, 1 / x = log (b / a) :=
  integral_one_div h

example (a b : ℝ) : ∫ x in a..b, exp (x + 3) = exp (b + 3) - exp (a + 3) := by
  rw [@intervalIntegral.integral_comp_add_right]
  exact integral_exp


/- We have the fundamental theorem of calculus in Lean. -/

example (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) :
    deriv (fun u ↦ ∫ x : ℝ in a..u, f x) b = f b :=
  (hf.integral_hasStrictDerivAt a b).hasDerivAt.deriv

example {f : ℝ → ℝ} {a b : ℝ} {f' : ℝ → ℝ} (h : ∀ x ∈ [[a, b]], HasDerivAt f (f' x) x)
    (h' : Continuous f') : ∫ y in a..b, f' y = f b - f a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt h (h'.intervalIntegrable _ _)

/- We can use this to compute integrals if we know the antiderivative. -/

example (a b : ℝ) : ∫ x in a..b, 2 * x * exp (x ^ 2) =
    exp (b ^ 2) - exp (a ^ 2) := by
  have h1 : ∀ x ∈ [[a, b]], HasDerivAt
    (fun x ↦ exp (x ^ 2))
    (2 * x * exp (x ^ 2)) x
  · intro x hx
    rw [show 2 * x * exp (x ^ 2) = exp (x ^ 2) * (2 * x) by ring]
    apply HasDerivAt.comp (h₂ := exp) (h := fun x ↦ x ^ 2)
    exact hasDerivAt_exp (x ^ 2)
    convert hasDerivAt_pow 2 x
    simp
  have h2 : IntervalIntegrable (fun x ↦ 2 * x * exp (x ^ 2)) volume a b
  · apply Continuous.intervalIntegrable
    continuity
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt h1 h2


/- If you `open Convolution`, you get the convolution of two functions. -/

example (f : ℝ → ℝ) (g : ℝ → ℝ) : f ⋆ g = fun x ↦ ∫ t, f t * g (x - t) :=
  rfl

/- The measure of a set lives in the extended non-negative reals `[0, ∞]`. -/
#check ℝ≥0∞
example : ℝ≥0∞ = WithTop {x : ℝ // 0 ≤ x} := rfl
example : (∞ + 5) = ∞ := by simp
example : (∞ * 0) = 0 := by simp

/- More generally, Mathlib develops Lebesgue integration, which requires measure theory.

The basic notion is that of a "σ-algebra".
A σ-algebra is called `MeasurableSpace` in Lean.
It consists of a collection of sets, called the *measurable* sets.
The empty set is measurable,
and the measurable sets are closed under complementation and countable unions. -/

variable {X : Type*} [MeasurableSpace X]

example : MeasurableSet (∅ : Set X) :=
  MeasurableSet.empty

example {s : Set X} (hs : MeasurableSet s) : MeasurableSet (sᶜ) :=
  hs.compl

example {f : ℕ → Set X} (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋃ b, f b) :=
  MeasurableSet.iUnion h



/-
We now can define measures.

On paper, a measure on a set equipped with a σ-algebra
is a function from the measurable sets to `[0, ∞]` that is additive on countable disjoint unions.

In Mathlib, we extend the measure to any set `s`
as the infimum of measures of measurable sets containing `s`.
Of course, many lemmas still require measurability assumptions, but not all.
-/

variable {μ : Measure X}

example : μ ∅ = 0 :=
  measure_empty

example {s : ℕ → Set X} (hmeas : ∀ i, MeasurableSet (s i)) (hdis : Pairwise (Disjoint on s)) :
    μ (⋃ i, s i) = ∑' i, μ (s i) :=
  μ.m_iUnion hmeas hdis

example (s : Set X) : μ s = ⨅ (t ⊇ s) (h : MeasurableSet t), μ t :=
  measure_eq_iInf s

example (s : ℕ → Set X) : μ (⋃ i, s i) ≤ ∑' i, μ (s i) :=
  measure_iUnion_le s

/- We say that a property `P` holds almost everywhere if the set of elements
where it doesn't hold has measure 0. -/
example {P : X → Prop} : (∀ᵐ x ∂μ, P x) ↔ μ {x | ¬ P x} = 0 :=
  Iff.rfl

/- Various spaces have a canonical measure associated to them, called `volume`. -/
example : MeasureSpace ℝ := by infer_instance
#check (volume : Measure ℝ)

example (a b : ℝ) (h : a ≤ b) :
    (volume (Icc a b)).toReal = b - a := by
  simp [h]

#check volume_Icc

/- The collection of measurable sets on `ℝ` is the smallest σ-algebra containing the open sets. -/
example : BorelSpace ℝ := by infer_instance

#check NullMeasurableSet

/- The collection of measurable sets on `ℝ` is the smallest σ-algebra containing the open sets.

Remark: `rw` will not rewrite inside a binder (like `fun x`, `∃ x`, `∫ x` or `∀ᶠ x`). Use
`simp_rw`, `simp only` or `unfold` instead. -/
example : ∀ᵐ x : ℝ, Irrational x := by {
  unfold Irrational
  refine Countable.ae_not_mem ?h volume
  exact countable_range Rat.cast
}


/- A map is measurable if preimages of measurable sets under that map are measurable. -/
#print Measurable
#check Continuous.measurable

/- A map `f` into a normed group is integrable (rougly) when it is measurable and the map
  `x ↦ ‖f x‖` has a finite integral. -/
#check Integrable

example : ¬ Integrable (fun x ↦ 1 : ℝ → ℝ) := by
  intro h
  rw [@integrable_const_iff] at h
  simp at h






/- We can take the integrals for functions intro a Banach space.
This version of the integral is called the *Bochner integral*.
The integral is denoted `∫ a, f x ∂μ` -/
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : X → E}

example {f g : X → E} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ x, f x + g x ∂μ = ∫ x, f x ∂μ + ∫ x, g x ∂μ :=
  integral_add hf hg


/-
* We can write `∫ x in s, f x ∂μ` for the integral restricted to a set.
* In the following example, we compute the integral of a constant map
* The function `ENNReal.toReal` sends `∞` to `0`. -/
example {s : Set X} (c : E) : ∫ x in s, c ∂μ = (μ s).toReal • c :=
  set_integral_const c

/-
* We can abbreviate `∫ x, f x ∂volume` to `∫ x, f x`
* We write `∫ x in a..b, f x ∂μ` for the integral on an interval (whose sign is reversed if `b < a`)
-/
example {f : ℝ → E} {a b c : ℝ} : ∫ x in a..b, c • f x = c • ∫ x in a..b, f x :=
  intervalIntegral.integral_smul c f

example {f : ℝ → E} {a b : ℝ} : ∫ x in b..a, f x = - ∫ x in a..b, f x :=
  intervalIntegral.integral_symm a b

open Filter

/- Here is a version of the dominated convergence theorem. -/
example {F : ℕ → X → E} {f : X → E} (bound : X → ℝ)
    (hmeas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hint : Integrable bound μ) (hbound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ bound x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n : ℕ ↦ F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n ↦ ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) :=
  tendsto_integral_of_dominated_convergence bound hmeas hint hbound hlim


/- Here is the statement of Fubini's theorem. -/
variable {X Y : Type*} [MeasurableSpace X] {μ : Measure X} [SigmaFinite μ]
    [MeasurableSpace Y] {ν : Measure Y} [SigmaFinite ν] in
example (f : X × Y → E) (hf : Integrable f (μ.prod ν)) :
    ∫ z, f z ∂ μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ :=
  integral_prod f hf

/- There is a version of the change of variables theorem. -/
example {s : Set ℝ} {f f' : ℝ → ℝ}
    (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
    (hf : InjOn f s) (g : ℝ → E) : ∫ x in f '' s, g x = ∫ x in s, |f' x| • g (f x) :=
  integral_image_eq_integral_abs_deriv_smul hs hf' hf g


/- Here is a computation using the change of variables theorem. -/
example (f : ℝ → ℝ) :
    ∫ x in (0)..π, sin x * f (cos x) = ∫ y in (-1)..1, f y := by
  rw [intervalIntegral.integral_of_le (by positivity),
      intervalIntegral.integral_of_le (by norm_num)]
  simp only [← integral_Icc_eq_integral_Ioc]
  have : Icc (-1) 1 = cos '' Icc 0 π
  · have := bijOn_cos
    exact (BijOn.image_eq this).symm
  rw [this, integral_image_eq_integral_abs_deriv_smul]
  rotate_left
  · exact measurableSet_Icc
  · intro x hx
    exact (hasDerivAt_cos x).hasDerivWithinAt
  · exact injOn_cos
  · simp
    apply set_integral_congr
    · exact measurableSet_Icc
    · intro x hx
      simp
      left
      symm
      simp
      exact sin_nonneg_of_mem_Icc hx

/- # Exercises

Feel free to either do the exercises, or work on your project.
-/

/- There are special cases of the change of variables theorems for affine transformations
  (but you can also use the change of variable theorem above) -/
example (a b : ℝ) :
    ∫ x in a..b, sin (x / 2 + 3) =
    2 * cos (a / 2 + 3) - 2 * cos (b / 2 + 3) := by
  sorry

/- Use the change of variables theorem for this exercise. -/
example (f : ℝ → ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    ∫ x in s, exp x * f (exp x) = ∫ y in exp '' s, f y := by
  sorry

example (x : ℝ) : ∫ t in (0)..x, t * exp t = (x - 1) * exp x + 1 := by
  sorry
