import LeanCourse.Common
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow
open BigOperators Function Set Real Topology
noncomputable section
set_option linter.unusedVariables false
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)


/- # Today: Differential Calculus

We cover chapter 10 from Mathematics in Lean. -/

/-
Last time we discussed topology.
-/


/- We write `deriv` to compute the derivative of a function.
`simp` can compute the derivatives of standard functions. -/

example (x : ℝ) : deriv Real.sin x = Real.cos x := by simp

example (x : ℂ) :
    deriv (fun y ↦ Complex.sin (y + 3)) x = Complex.cos (x + 3) := by simp

/- Not every function has a derivative. As usual, in mathlib we just define the derivative of a non-differentiable function to be `0`. -/

variable (f : ℝ → ℝ) (x : ℝ) in
#check (deriv_zero_of_not_differentiableAt :
  ¬ DifferentiableAt ℝ f x → deriv f x = 0)

/- So proving that `deriv f x = y` doesn't necessarily mean that `f` is differentiable.
Often it is nicer to use the predicate `HasDerivAt f y x`, which states that `f`
is differentiable and `f'(x) = y`. -/

example (x : ℝ) : HasDerivAt Real.sin (Real.cos x) x := by exact?

/- We can also specify that a function has a derivative without specifying its
derivative. -/

example (x : ℝ) : DifferentiableAt ℝ sin x :=
  (hasDerivAt_sin x).differentiableAt

/- Each of these has their own lemmas. -/

#check HasDerivAt.add
#check deriv_add
#check DifferentiableAt.add


example (x : ℝ) :
    HasDerivAt (fun x ↦ Real.cos x + Real.sin x)
    (Real.cos x - Real.sin x) x := by sorry






/- We can also take the derivative of functions that take values in a
(normed) vector space. -/

example (x : ℝ) : deriv (fun x ↦ ((Real.cos x) ^ 2, (Real.sin x) ^ 2)) x =
    (- 2 * Real.cos x * Real.sin x, 2 * Real.sin x * Real.cos x) := by sorry

/-
Lean has the following names for intervals
("c" = closed, "o" = open, "i" = infinity)
Icc a b = [a, b]
Ico a b = [a, b)
Ioc a b = (a, b]
Ioo a b = (a, b)
Ici a   = [a, ∞)
Ioi a   = (a, ∞)
Iic b   = (-∞, b]
Iio b   = (-∞, b)

The intermediate value theorem states that if `f` is continuous and
`f a ≤ y ≤ f b`, then there is an `x ∈ [a, b]` with `f(x) = y`.
-/

example {f : ℝ → ℝ} {a b y : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    Icc (f a) (f b) ⊆ f '' Icc a b :=
  intermediate_value_Icc hab hf
-- Note that we only require `f` to be continuous on `[a, b]`


/-
The mean value theorem states that if `f` is continuus on `[a, b]`
and differentiable on `(a, b)` then there is a `c ∈ (a, b)` where `f'(c)` is the
average slope of `f` on `[a, b]`
-/

example (f : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hf' : DifferentiableOn ℝ f (Ioo a b)) :
    ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  exists_deriv_eq_slope f hab hf hf'


/- Rolle's theorem is the special case where `f a = f b`.
Why is there no differentiability requirement on `f` here? -/
example {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b) :
    ∃ c ∈ Ioo a b, deriv f c = 0 :=
  exists_deriv_eq_zero hab hfc hfI



/- For multivariate functions, we have a different notion of derivative.
We can generalize the notion of derivative to normed spaces.

A *normed group* is an abelian group with a norm satisfying the following rules.
-/

section NormedGroup

variable {E : Type*} [NormedAddCommGroup E]

#check (norm : E → ℝ)

example (x : E) : 0 ≤ ‖x‖ :=
  norm_nonneg x

example {x : E} : ‖x‖ = 0 ↔ x = 0 :=
  norm_eq_zero

example (x y : E) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ :=
  norm_add_le x y

/- This turns `E` into a metric space. -/
example (x y : E) : dist x y = ‖x - y‖ :=
  dist_eq_norm x y

/- A *normed space* is a normed group that is a vector space
satisfying the following condition. -/

variable [NormedSpace ℝ E]

example (a : ℝ) (x : E) : ‖a • x‖ = |a| * ‖x‖ :=
  norm_smul a x


/- A complete normed space is known as a *Banach space*. Every finite-dimensional vector space is complete. -/

example [FiniteDimensional ℝ E] : CompleteSpace E := by infer_instance

/- In the above examples, we could also replace `ℝ` by `ℂ`
or another *normed field*. -/

end NormedGroup

/- Morphisms between normed spaces are continuous linear maps `E →L[𝕜] F`. -/
section NormedSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]


example : E →L[𝕜] E := ContinuousLinearMap.id 𝕜 E

example (f : E →L[𝕜] F) : E → F := f

example (f : E →L[𝕜] F) : Continuous f := f.cont

example (f : E →L[𝕜] F) : E →ₗ[𝕜] F := f

/- Continuous linear maps have an operator norm. -/

example (f : E →L[𝕜] F) (x : E) : ‖f x‖ ≤ ‖f‖ * ‖x‖ :=
  f.le_op_norm x

example (f : E →L[𝕜] F) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ x, ‖f x‖ ≤ M * ‖x‖) : ‖f‖ ≤ M :=
  f.op_norm_le_bound hMp hM


/- Defining differentiability requires asymptotic comparisons. -/

section Asymptotics
open Asymptotics

variable {α : Type*} (l : Filter α) (f : α → E) (g : α → F)

example (c : ℝ) : IsBigOWith c l f g ↔ ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ :=
  isBigOWith_iff

example : f =O[l] g ↔ ∃ C, IsBigOWith C l f g :=
  isBigO_iff_isBigOWith

example : f =o[l] g ↔ ∀ C > 0, IsBigOWith C l f g :=
  isLittleO_iff_forall_isBigOWith

end Asymptotics

/- We define the *Fréchet derivative* of any function between normed spaces. -/

example (f : E → F) (f' : E →L[𝕜] F) (x₀ : E) :
    HasFDerivAt f f' x₀ ↔
    (fun x ↦ f x - f x₀ - f' (x - x₀)) =o[𝓝 x₀] fun x ↦ x - x₀ := by
  rfl

example (f : E → F) (f' : E →L[𝕜] F) (x₀ : E) (hff' : HasFDerivAt f f' x₀) :
    fderiv 𝕜 f x₀ = f' :=
  hff'.fderiv

/- We write `ContDiff 𝕜 n f` to say that `f` is `C^n`, i.e. it is
  `n`-times continuously differentiable.
  Here `n` lives in `ℕ∞`, which is `ℕ` with an extra top element `⊤` added ("∞"). -/

variable {f g : E → F} {n : ℕ∞}
example (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n (fun x ↦ (f x, 2 • f x + g x)) := by sorry

example : ContDiff 𝕜 0 f ↔ Continuous f := contDiff_zero

example {n : ℕ} : ContDiff 𝕜 (n+1) f ↔
  Differentiable 𝕜 f ∧ ContDiff 𝕜 n (fderiv 𝕜 f) := contDiff_succ_iff_fderiv

example : ContDiff 𝕜 ⊤ f ↔ ∀ n : ℕ, ContDiff 𝕜 n f := contDiff_top

end NormedSpace



/- # Exercises -/

example (x : ℝ) :
    deriv (fun x ↦ Real.exp (x ^ 2)) x = 2 * x * Real.exp (x ^ 2) := by sorry

/- If you have a continuous injective function `ℝ → ℝ` then `f` is monotone or antitone. This is a possible first step in proving that result.
Prove this by contradiction using the intermediate value theorem. -/
example {f : ℝ → ℝ} (hf : Continuous f) (h2f : Injective f) {a b x : ℝ}
    (hab : a ≤ b) (h2ab : f a < f b) (hx : x ∈ Icc a b) : f a ≤ f x := by sorry


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {n : ℕ∞} in
/- In this exercise you should combine the right lemmas from the library, in particular `IsBoundedBilinearMap.contDiff`. -/
example (L : E →L[𝕜] E →L[𝕜] E) (f g : E → E) (hf : ContDiff 𝕜 n f)
    (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n (fun z : E × E ↦ L (f z.1) (g z.2)) := by sorry


/- If you finish these exercises, continue with the exercises of lecture 11. -/
