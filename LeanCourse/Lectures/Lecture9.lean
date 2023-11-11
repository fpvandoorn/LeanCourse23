import LeanCourse.Common
import Mathlib.GroupTheory.Perm.Subgroup
open BigOperators Finset Function Real
noncomputable section
set_option linter.unusedVariables false
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

-- (not much changed compared to the "before" version)

/- Practical:
* **I have updated the version of mathlib for this repository**. Rerun `lake exe cache get!`.
  See the `README` file for detailed instructions.
* Start thinking about a formalization projects.
* Over the next couple of classes we'll cover some topics in undergraduate mathematics, and see
  how this is done in Lean.
  - Group theory: group homomorphisms, subgroups, quotient groups, group actions
  - Ring theory: ideals, units, polynomials
  - Topology: Topological spaces, metric spaces, Hausdorff spaces, compact sets
  - Calculus: total derivative of a multivariate function
  - Integration: measures
-/

/- # Today: Group theory

We cover section 8.1 from Mathematics in Lean.

Chapter 7 covers some of the design decisions for algebraic structures.
I recommend that you read through it, but I won't cover it in detail in class. -/


/-
Last time we discussed structures and classes
-/



/- ## A note on coercions

You can specify *coercions* to say that an element of one type can be silently coerced to an element
of another type. We've already seen the coercions
`ℕ → ℤ → ℚ → ℝ → ℂ`
for numbers.
-/

#check fun n : ℕ ↦ (n : ℚ)

def PosReal : Type := {x : ℝ // x > 0}

instance : Coe PosReal Real := ⟨fun x ↦ x.1⟩

def diff (x y : PosReal) : ℝ := x - y

/- coercions can be composed. -/
#check fun (x : PosReal) ↦ (x : ℂ)




/-
* We use `CoeSort` to coerce to `Type _` (or `Sort _`)
* We use `CoeFun` to coerce to functions.
-/
structure PointedType where
  carrier : Type*
  pt : carrier

instance : CoeSort PointedType Type* := ⟨fun α ↦ α.carrier⟩

structure PointedFunction (X Y : PointedType) where
  toFun : X → Y
  toFun_pt : toFun X.pt = Y.pt

infix:50 " →. " => PointedFunction

instance {X Y : PointedType} : CoeFun (X →. Y) (fun _ ↦ X → Y) := ⟨fun e ↦ e.toFun⟩

-- these two are hints to the pretty printer to print these operations a bit nicer.
attribute [pp_dot] PointedType.pt
attribute [coe] PointedFunction.toFun

namespace PointedFunction

variable {X Y Z : PointedType}

@[simp] lemma coe_pt (f : X →. Y) : f X.pt = Y.pt := f.toFun_pt

lemma comp (g : Y →. Z) (f : X →. Y) : X →. Z :=
{ toFun := g ∘ f
  toFun_pt := by simp }

end PointedFunction


/- # Monoids

The type of monoids structures on a type `M` with multiplicative notation is `Monoid M`.

The additive notation version is `AddMonoid`. The commutative versions add the `Comm`
prefix before `Monoid`.
-/

example {M : Type*} [Monoid M] (x : M) : x * 1 = x := mul_one x

example {M : Type*} [AddCommMonoid M] (x y : M) : x + y = y + x := add_comm x y

/-
Note in particular that `AddMonoid` exists, although it would be very confusing to use
additive notation in a non-commutative case on paper.
-/

/-
The type of morphisms between monoids `M` and `N` is called `MonoidHom M N` and denoted by
`M →* N`. The additive version is called `AddMonoidHom` and denoted by `M →+ N`.

They both have a coercion to functions.
-/

example {M N : Type*} [Monoid M] [Monoid N] (x y : M) (f : M →* N) : f (x * y) = f x * f y := by exact f.map_mul x y

example {M N : Type*} [AddMonoid M] [AddMonoid N] (f : M →+ N) : f 0 = 0 :=
  f.map_zero

/-
Those morphisms are bundled maps, ie they package together a map and some properties of this map.
Chapter 7 of MiL contain a lot more explanations about that.
Here we simply note the slightly unfortunate consequence that we cannot use ordinary function
composition. We need to use `MonoidHom.comp` and `AddMonoidHom.comp`.
-/

example {M N P : Type*} [AddMonoid M] [AddMonoid N] [AddMonoid P]
    (f : M →+ N) (g : N →+ P) : M →+ P := g.comp f


/- # Groups and their morphisms -/

example {G : Type*} [Group G] (x : G) : x * x⁻¹ = 1 := mul_inv_self x

/-
Similar to the `ring` tactic that we saw earlier, there is a `group` tactic that proves
every identity which follows from the group axioms with any extra assumption
(hence one can see it as a tactic proving identities that hold in free groups).
-/

example {G : Type*} [Group G] (x y z : G) : x * (y * z) * (x*z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by
  group

-- And there is similar a tactic for identities in commutative additive groups called `abel`.

example {G : Type*} [AddCommGroup G] (x y z : G) : z + x + (y - z - x) = y := by
  abel

-- Groups morphisms are nothing but monoid morphisms between groups

example {G H : Type*} [Group G] [Group H] (x y : G) (f : G →* H) : f (x * y) = f x * f y :=
  f.map_mul x y

example {G H : Type*} [Group G] [Group H] (x : G) (f : G →* H) : f (x⁻¹) = (f x)⁻¹ :=
  f.map_inv x

-- Note that preserving 1 is automatic
example {G H : Type*} [Group G] [Group H] (f : G → H) (h : ∀ x y, f (x * y) = f x * f y) :
    G →* H :=
  MonoidHom.mk' f h

/-
There is also a type `MulEquiv` of group (or monoid) isomorphisms denoted by `≃*` (and
`AddEquiv` denoted by `≃+` in additive notation).
The inverse of `f : G ≃* H` is `f.symm : H ≃* G`, composition is `MulEquiv.trans` and
the identity isomorphism of `G` is `MulEquiv.refl G`.
This type is automatically coerced to morphisms and functions.
-/

example {G H : Type*} [Group G] [Group H] (f : G ≃* H) :
    f.trans f.symm = MulEquiv.refl G := by exact?






/-
# Subgroups

In the same way group morphisms are bundled, subgroups are also bundles made of a set in `G`
and some stability properties.
-/


example {G : Type*} [Group G] (H : Subgroup G) {x y : G} (hx : x ∈ H) (hy : y ∈ H) : x * y ∈ H :=
  H.mul_mem hx hy

example {G : Type*} [Group G] (H : Subgroup G) {x : G} (hx : x ∈ H) : x⁻¹ ∈ H :=
  H.inv_mem hx

/-
In the above example, it is important to understand that `Subgroup G` is the type of subgroups
of `G`. It is not a predicate on `Set G`.
But it is endowed with a coercion to `Set G` and a membership predicate on `G`.
See Chapter 7 of MiL for explanations about why and how things are
set up like this.

Of course the type class instance system knows that a subgroup of a group inherits a group
structure.
-/

example {G : Type*} [Group G] (H : Subgroup G) : Group H := by infer_instance

/-
But note this is subtler than it looks. The object `H` is not a type, but Lean automatically
inserts a coercion to type using subtypes. So the above example can be restated more explicitly
as:
-/

example {G : Type*} [Group G] (H : Subgroup G) : Group {x : G // x ∈ H} := by infer_instance

/-
An important benefit of having a type `Subgroup G` instead of a predicate
`IsSubgroup : Set G → Prop` is that one can easily endow it with additional structure.
Crucially this includes a complete lattice structure with respect to inclusion.
For instance, instead of having a lemma stating that an intersection of two subgroups of `G`, we
have the lattice operation `⊓` and all lemmas about lattices are readily available.
-/

example {G : Type*} [Group G] : CompleteLattice (Subgroup G) := by infer_instance

example {G : Type*} [Group G] (H H' : Subgroup G) :
    ((H ⊓ H' : Subgroup G) : Set G) = (H : Set G) ∩ (H' : Set G) := by rfl

example {G : Type*} [Group G] (H H' : Subgroup G) :
    ((H ⊔ H' : Subgroup G) : Set G) = Subgroup.closure ((H : Set G) ∪ (H' : Set G)) := by
  simp [Subgroup.closure_union]

/-
Another subtlety is `G` itself does not have type `Subgroup G`, so we need a way to talk
about `G` seen as a subgroup of `G`. This is also provided by the lattice structure.
We are talking about the top element of this lattice.
-/

example {G : Type*} [Group G] (x : G) : x ∈ (⊤ : Subgroup G) := trivial

/-
Similarly the bottom element of this lattice is the subgroup whose only element is the
neutral element.
-/

example {G : Type*} [Group G] (x : G) : x ∈ (⊥ : Subgroup G) ↔ x = 1 := Subgroup.mem_bot

-- One can push and pull subgroups using morphisms.

example {G H : Type*} [Group G] [Group H] (G' : Subgroup G) (f : G →* H) : Subgroup H :=
  Subgroup.map f G'

example {G H : Type*} [Group G] [Group H] (H' : Subgroup H) (f : G →* H) : Subgroup G :=
  Subgroup.comap f H'

/-
In particular the preimage of the bottom subgroup under a morphism `f` is a subgroup called
the kernel of `f` and its range is also a subgroup.
-/


example {G H : Type*} [Group G] [Group H] (f : G →* H) (g : G) :
    g ∈ MonoidHom.ker f ↔ f g = 1 :=
  f.mem_ker

example {G H : Type*} [Group G] [Group H] (f : G →* H) (h : H) :
    h ∈ MonoidHom.range f ↔ ∃ g : G, f g = h :=
  f.mem_range





/- # Quotient groups -/

section QuotientGroup

example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : Group (G ⧸ H) := inferInstance


example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : G →* G ⧸ H :=
QuotientGroup.mk' H

-- The universal property of quotient groups
example {G : Type*} [Group G] (N : Subgroup G) [N.Normal] {M : Type*}
  [Group M] (φ : G →* M) (h : N ≤ MonoidHom.ker φ) : G ⧸ N →* M :=
QuotientGroup.lift N φ h

-- First isomorphism theorem
example {G : Type*} [Group G] {M : Type*} [Group M] (φ : G →* M) :
    G ⧸ MonoidHom.ker φ →* MonoidHom.range φ :=
  QuotientGroup.quotientKerEquivRange φ

example {G G': Type*} [Group G] [Group G']
    {N : Subgroup G} [N.Normal] {N' : Subgroup G'} [N'.Normal]
    {φ : G →* G'} (h : N ≤ Subgroup.comap φ N') : G ⧸ N →* G'⧸ N':=
  QuotientGroup.map N N' φ h

end QuotientGroup





/- # Group actions -/

section GroupActions

example {G X : Type*} [Group G] [MulAction G X] (g g' : G) (x : X) :
    g • (g' • x) = (g * g') • x :=
  (mul_smul g g' x).symm


/- The underlying group morphism is called `MulAction.toPermHom`. -/


open MulAction

example {G X : Type*} [Group G] [MulAction G X] : G →* Equiv.Perm X :=
  toPermHom G X

/-
As an illustration let us see how to define the Cayley isomorphism that embeds any group `G` into
a permutation group, namely `Perm G`.
-/

def CayleyIsoMorphism (G : Type*) [Group G] : G ≃* (toPermHom G G).range := by
  exact?

/-
Note that nothing before the above definition required having a group rather than a monoid (or any
type endowed with a multiplication operation really).

The group condition really enters the picture when we will want to partition `X` into orbits.
The corresponding equivalence relation on `X` is called `MulAction.orbitRel`.
It is not declared as a global instance.
-/

example {G X : Type*} [Group G] [MulAction G X] : Setoid X := orbitRel G X

example {G X : Type*} [Group G] [MulAction G X] :
    X ≃ (ω : orbitRel.Quotient G X) × (orbit G (Quotient.out' ω)) :=
  MulAction.selfEquivSigmaOrbits G X

example {G X : Type*} [Group G] [MulAction G X] (x : X) :
    orbit G x ≃ G ⧸ stabilizer G x :=
  MulAction.orbitEquivQuotientStabilizer G x

-- Lagrange theorem
example {G : Type*} [Group G] (H : Subgroup G) : G ≃ (G ⧸ H) × H :=
  Subgroup.groupEquivQuotientProdSubgroup

end GroupActions


/- # Exercises -/

variable {G H K : Type*} [Group G] [Group H] [Group K]
open Subgroup

/- Define the conjugate of a subgroup. -/
def conjugate (x : G) (H : Subgroup G) : Subgroup G where
  carrier := {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}
  one_mem' := by sorry
  inv_mem' := by sorry
  mul_mem' := by sorry

/- Now let's prove that a group acts on its own subgroups by conjugation. -/

lemma conjugate_one (H : Subgroup G) : conjugate 1 H = H := by sorry

lemma conjugate_mul (x y : G) (H : Subgroup G) :
    conjugate (x * y) H = conjugate x (conjugate y H) := by sorry

instance : MulAction G (Subgroup G) where
  smul := conjugate
  one_smul := sorry
  mul_smul := sorry


/- State and prove that the preimage of `U` under the composition of `φ` and `ψ` is a preimage
of a preimage of `U`. Use `comap` and `comp` in the statement. -/
example (φ : G →* H) (ψ : H →* K) (U : Subgroup K) : sorry := sorry

/- State and prove that the image of `S` under the composition of `φ` and `ψ`
is a image of an image of `S`. -/
example (φ : G →* H) (ψ : H →* K) (S : Subgroup G) : sorry := sorry
