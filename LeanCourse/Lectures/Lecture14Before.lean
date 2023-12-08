import LeanCourse.Common
import LeanCourse.DiffGeom
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.LinearAlgebra.TensorProduct
import Mathlib.Analysis.NormedSpace.Dual
open Set ENat Manifold Metric FiniteDimensional Bundle Function
attribute [local instance] Real.fact_zero_lt_one
noncomputable section
set_option linter.unusedVariables false
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)


/- # Today: Differential Geometry

This is not yet in Mathematics in Lean. -/

/-
Last time we discussed integral calculus.
-/



/-
Ingredients needed for manifolds:
A partial homeomorphism (local homeomorphism) from `X → Y` is
  a homeomorphism from an open subset `s ⊆ X` to an open subset `t ⊆ Y`.
-/
#check LocalEquiv -- An equiv between a subset of the domain and a subset of the codomain
#check LocalHomeomorph -- A homeomorphism between open subsets of the domain and codomain


/-
A topological space is locally euclidean if you have a
partial homeomorphism to `ℝⁿ` around each point in `X`.
-/
#check ChartedSpace


/-
A smooth manifold is `X` an charted space structure such that for any two charts the
coordinate change function between the charts is smooth on their common domain.
-/
variable {n : Type*} [Fintype n] {M : Type*} [TopologicalSpace M] [ChartedSpace (n → ℝ) M]
  [SmoothManifoldWithCorners 𝓘(ℝ, n → ℝ) M]

/- `e.symm ≫ₕ e' : ℝⁿ → ℝⁿ` is the coordinate change function from `e` to `e'`. -/
example {e e' : LocalHomeomorph M (n → ℝ)}
    (he : e ∈ atlas (n → ℝ) M) (he' : e' ∈ atlas (n → ℝ) M) :
    ContDiffOn ℝ ⊤ (e.symm ≫ₕ e') (e.symm ≫ₕ e').source := by
  have := (contDiffGroupoid ⊤ 𝓘(ℝ, n → ℝ)).compatible he he'
  simpa using this.1

/- Here `contDiffGroupoid` specifies the groupoid structure on local homeomorphisms stating that
coordinate change functions must be smooth -/
#check contDiffGroupoid

/- We can also equip a manifold with another groupoid structure, to define the class of
`C^k` manifolds or analytic manifolds, or other classes of manifolds. -/
#check StructureGroupoid

/- The general definition of manifolds in mathlib is more general:
* It can be over a field other than `ℝ` or `ℂ`, like the p-adic numbers
* It can have infinite dimension
* It can have boundary or corners
-/


/-
To cover manifolds with boundaries and corners,
every manifold `M` is modelled by a _model space_ `H`.
There is a map `I : H → E` where `E` is a normed space over a field `𝕜`.

Example: `E = ℝⁿ`, `H` is a half-space, and `I : H → E` is the inclusion.
This map `I` is called a _model with corners_. `𝓘(ℝ, E)` is notation for the identity map `E → E`.
`𝓡∂ n` is the inclusion from the half-space into `ℝⁿ`
-/
#check ModelWithCorners
#check 𝓘(ℝ, n → ℝ)
#check 𝓡∂ 3

section examples

section unitInterval
open unitInterval

#check I -- I is notation for the interval [0, 1]

/- the interval [0, 1] is modelled by two charts with model space [0, ∞),
so it is a topological manifold -/
example : ChartedSpace (EuclideanHalfSpace 1) I := by
  show_term infer_instance

/- To state that it is a smooth manifold, we have to say that all coordinate changes
live in the groupoid of smooth maps -/
example : HasGroupoid I (contDiffGroupoid ∞ (𝓡∂ 1)) := by
  infer_instance

/- This is the same as saying that `I` forms a smooth manifold. -/
example : SmoothManifoldWithCorners (𝓡∂ 1) I := by
  infer_instance

/- atlases are not maximal in general -/
#check (contDiffGroupoid ∞ (𝓡∂ 1)).maximalAtlas I

end unitInterval

/- the sphere in a finite-dimensional inner product space is a smooth manifold -/

variable (n : ℕ) (E : Type*) [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [Fact (finrank ℝ E = n + 1)]
#check SmoothManifoldWithCorners (𝓡 n) (sphere (0 : E) 1)

/- the map 𝕊ⁿ ↪ ℝⁿ⁺¹ is smooth -/
example : Smooth (𝓡 n) 𝓘(ℝ, E) ((·) : sphere (0 : E) 1 → E) := by
  exact?

/- the circle is a Lie group -/
example : LieGroup (𝓡 1) circle := by
  infer_instance



/- declaring a general smooth manifold is a little verbose. -/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable
  -- declare a smooth manifold `M` over the pair `(E, H)`.
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners 𝕜 E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M]
  -- declare a smooth manifold `N` over the pair `(F, G)`.
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  (J : ModelWithCorners 𝕜 F G) {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [SmoothManifoldWithCorners J N]

/- A differentiable map between manifolds induces a map on tangent spaces. -/

example (f : M → N) (hf : MDifferentiable I J f) (x : M) :
    TangentSpace I x →L[𝕜] TangentSpace J (f x) :=
  mfderiv I J f x

example {f g : M → M} (x : M)
    (hg : MDifferentiableAt I I g (f x)) (hf : MDifferentiableAt I I f x) :
    mfderiv I I (g ∘ f) x = (mfderiv I I g (f x)).comp (mfderiv I I f x) :=
  mfderiv_comp x hg hf

/- A differentiable map between manifolds induces a map on the tangent bundle. -/

example (f : M → N) (hf : MDifferentiable I J f) : TangentBundle I M → TangentBundle J N :=
  tangentMap I J f

example [AddGroup N] [LieAddGroup J N] {f g : M → N} {n : ℕ∞}
    (hf : ContMDiff I J n f) (hg : ContMDiff I J n g) : ContMDiff I J n (f + g) :=
  hf.add hg

/- We also have smooth vector bundles -/

/- Given a continuous surjection `π : Z → M`.
A trivialization of `π` at `x : M` with fiber `F` is a neighborhood `U` of `x` and a homeomorphism
`ϕ : π ⁻¹' U → U × F` that commutes with projections.
-/
#check Trivialization
/- Fiber bundles have trivializations around each point in the base manifold -/
#check FiberBundle
/- In vector bundles the trivializations induce linear maps on the fibers.
Interestingly, for infinite-dimensional manifolds you need an additional continuity condition. -/
#check VectorBundle
/- In smooth vector bundles the trivializations are smooth. -/
#check SmoothVectorBundle

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  (IB : ModelWithCorners 𝕜 E H) {B : Type*} [TopologicalSpace B] [ChartedSpace H B]
  [SmoothManifoldWithCorners IB B]

-- Let `E₁` and `E₂` be smooth vector bundles over `B`

variable (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] (E₁ : B → Type*)
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [∀ x : B, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [SmoothVectorBundle F₁ E₁ IB]
variable (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] (E₂ : B → Type*)
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [∀ x : B, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [SmoothVectorBundle F₂ E₂ IB]


-- The product of two bundles is a smooth vector bundle.

example : SmoothVectorBundle (F₁ × F₂) (E₁ ×ᵇ E₂) IB := by
  exact?

-- We can take construct the bundle of continuous linear maps between bundles.

variable [∀ x, TopologicalAddGroup (E₁ x)] [∀ x, TopologicalAddGroup (E₂ x)]
  [∀ x, ContinuousSMul 𝕜 (E₂ x)]


example : SmoothVectorBundle (F₁ →L[𝕜] F₂) (Bundle.ContinuousLinearMap (.id 𝕜) E₁ E₂) IB := by
  exact?

-- We can pull back vector bundles.

variable (f : C^∞⟮I, M; IB, B⟯)

example : SmoothVectorBundle F₁ ((f : M → B) *ᵖ E₁) I := by
  exact?

/- Patrick Massot, Oliver Nash and I have proven sphere eversion,
as a corollary of Gromov's h-principle -/

def Immersion (f : M → N) : Prop := ∀ m, Injective (mfderiv I J f m)

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (finrank ℝ E = 3)]

local notation "ℝ³" => E
local notation "𝕊²" => sphere (0 : ℝ³) 1

theorem sphere_eversion : ∃ f : ℝ → 𝕊² → ℝ³,
    (ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ³) ∞ (uncurry f)) ∧
    (f 0 = λ x : 𝕊² ↦ (x : ℝ³)) ∧
    (f 1 = λ x : 𝕊² ↦ -(x : ℝ³)) ∧
    ∀ t, Immersion (𝓡 2) 𝓘(ℝ, ℝ³) (f t) :=
  sorry -- formalized, but not yet in mathlib

end examples






/-! ## Exercises -/

/- Define a local homeomorphism from `ℝ` to `ℝ` which is just `x ↦ -x`, but on `(-1, 1)`. In
Lean, the interval `(-1, 1)` is denoted by `Ioo (-1 : ℝ) 1` (where `o` stands for _open_). -/

example : LocalHomeomorph ℝ ℝ where
  toFun := fun x ↦ -x
  invFun := fun x ↦ -x
  source := Ioo (-1) 1
  target := sorry
  map_source' := by
    sorry
  map_target' := by
    sorry
  left_inv' := by
    sorry
  right_inv' := by
    sorry
  open_source := sorry
  open_target := sorry
  continuous_toFun := sorry
  continuous_invFun := sorry

/-
We will define two smooth maps on `[0, 1]`. This is not yet trivial, since mathlib still
misses many lemmas about manifolds.
-/

open unitInterval

def g : I → ℝ := Subtype.val

-- smoothness results for `EuclideanSpace` are expressed for general `L^p` spaces
-- (as `EuclideanSpace` has the `L^2` norm), in:
#check PiLp.contDiff_coord
#check PiLp.contDiffOn_iff_coord

-- this is the charted space structure on `I`
#check IccManifold

example : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ g := by
  sorry

lemma msmooth_of_smooth {f : ℝ → I} {s : Set ℝ} (h : ContDiffOn ℝ ∞ (fun x ↦ (f x : ℝ)) s) :
    ContMDiffOn 𝓘(ℝ) (𝓡∂ 1) ∞ f s := by
  sorry
