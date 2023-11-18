import LeanCourse.Common
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow
set_option linter.unusedVariables false
noncomputable section
open BigOperators Function Set Real Filter Classical Topology
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

/-
* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 9 and 10, all sections

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  Feel free to skip exercises if you are confident that you can do them.
  There are solutions in the solution folder in case you get stuck.

# You have two options for this assignment

1. Hand in the solutions to the exercises below. Deadline: 24.11.2023.
2. If you have already chosen a project, and your project doesn't require topology or analysis, you can work on your project. If you do, push a decent amount of work to your fork of the repository by 24.11. In this case you do not have to upload anything on eCampus.

* When you hand in your solution, make sure that the file compiles!
  If you didn't manage to complete a particular exercise, make sure that the proof still compiles,
  by replacing the proof (or part of the proof) by `sorry`.
-/




/- Here is a technical exercise using filters,
that was useful in something I did recently. Useful lemmas here are
* `Filter.Eventually.filter_mono`
* `Filter.Eventually.mono` -/
lemma exercise6_1 {ι α : Type*} {p : ι → Prop} {q : Prop} {a b : α}
    {L : Filter ι} {F G : Filter α}
    (hbF : ∀ᶠ x in F, x ≠ b) (haG : ∀ᶠ x in G, x ≠ a) (haF : pure a ≤ F) (hbG : pure b ≤ G) :
    (∀ᶠ i in L, p i ↔ q) ↔
    Tendsto (fun i ↦ if p i then a else b) L (if q then F else G) := by
  have hab : a ≠ b
  · sorry
  rw [tendsto_iff_eventually]
  sorry

/- To be more concrete, we can use the previous lemma to prove the following.
if we denote the characteristic function of `A` by `1_A`, and `f : ℝ → ℝ` is a function,
then  `f * 1_{s i}` tends to `f * 1_t` iff `x ∈ s i` eventually means the same as `x ∈ t` for all `x`. (note that this does *not* necessarily mean that `s i = t` eventually).
Here it lemmas are `indicator_apply` and `apply_ite` -/
lemma exercise6_2 {ι : Type*} {L : Filter ι} {s : ι → Set ℝ} {t : Set ℝ} {f : ℝ → ℝ}
    (ha : ∀ x, f x ≠ 0) :
    (∀ x, ∀ᶠ i in L, x ∈ s i ↔ x ∈ t) ↔
    Tendsto (fun i ↦ Set.indicator (s i) f) L (𝓝 (Set.indicator t f)) := by
  rw [tendsto_pi_nhds]
  sorry

section

variable (α : Type*)
 [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]

/-
In the next three exercises we will show that every continuous injective function `ℝ → ℝ` is
either strictly monotone or strictly antitone.

We start by proving a slightly harder version of the exercise in class.
We generalize the real numbers to an arbitrary type `α`
that satisfies all the conditions required for the intermediate value theorem.
If you want to prove this by using the intermediate value theorem only once,
then use `intermediate_value_uIcc`.
`uIcc a b` is the unordered interval `[min a b, max a b]`.
Useful lemmas: `uIcc_of_le` and `mem_uIcc`. -/
lemma exercise6_3 {f : α → α} (hf : Continuous f) (h2f : Injective f) {a b x : α}
    (hab : a ≤ b) (h2ab : f a < f b) (hx : a ≤ x) : f a ≤ f x := by
  sorry

/- Now use this and the intermediate value theorem again
to prove that `f` is at least monotone on `[a, ∞)`. -/
lemma exercise6_4 {f : α → α} (hf : Continuous f) (h2f : Injective f) {a b : α}
    (hab : a ≤ b) (h2ab : f a < f b) : StrictMonoOn f (Ici a) := by
  sorry

/-
Now we can finish just by using the previous exercise multiple times.
In this proof we take advantage that we did the previous exercise for an arbitrary order,
because that allows us to apply it to `ℝ` with the reversed order `≥`.
This is called `OrderDual ℝ`. This allows us to get that `f` is also strictly monotone on
`(-∞, b]`.
Now finish the proof yourself.
You do not need to apply the intermediate value theorem in this exercise.
-/
lemma exercise6_5 (f : ℝ → ℝ) (hf : Continuous f) (h2f : Injective f) :
    StrictMono f ∨ StrictAnti f := by
  have h3f : ∀ {a b : ℝ} (hab : a ≤ b) (h2ab : f a < f b), StrictMonoOn f (Iic b)
  · intro a b hab h2ab
    have := exercise6_4 (OrderDual ℝ) hf h2f hab h2ab
    convert this using 0
    exact strict_mono_on_dual_iff.symm
  sorry


/-
Let's prove that the absolute value function is not differentiable at 0.
You can do this by showing that the left derivative and the right derivative do exist,
but are not equal. We can state this with `HasDerivWithinAt`
To make the proof go through, we need to show that the intervals have unique derivatives.
An example of a set that doesn't have unique derivatives is the set `ℝ × {0}`
as a subset of `ℝ × ℝ`, since that set doesn't contains only points in the `x`-axis,
so within that set there is no way to know what the derivative of a function should be
in the direction of the `y`-axis.

The following lemmas will be useful
* `HasDerivWithinAt.congr`
* `uniqueDiffWithinAt_convex`
* `HasDerivWithinAt.derivWithin`
* `DifferentiableAt.derivWithin`.
-/

lemma exercise6_6 : ¬ DifferentiableAt ℝ (fun x : ℝ ↦ |x|) 0 := by
  intro h
  have h1 : HasDerivWithinAt (fun x : ℝ ↦ |x|) 1 (Ici 0) 0
  · sorry
  have h2 : HasDerivWithinAt (fun x : ℝ ↦ |x|) (-1) (Iic 0) 0
  · sorry
  have h3 : UniqueDiffWithinAt ℝ (Ici (0 : ℝ)) 0 := by
    sorry
  have h4 : UniqueDiffWithinAt ℝ (Iic (0 : ℝ)) 0 := by
    sorry
  sorry
