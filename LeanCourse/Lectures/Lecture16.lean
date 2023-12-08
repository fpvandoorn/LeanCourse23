import LeanCourse.Common
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Exponential
set_option linter.unusedVariables false
open Lean Meta Elab Parser Tactic

/- # Today: Second peek into Lean internals
-/


/- Last time we saw how to define:
* notation
* macros
* syntax
* tactics
-/


/- Before we continue, first a little quiz.
What do I do wrong in the following examples? -/


/- Is there anything wrong with the statement of this theorem? -/
/-- This is a docstring -/
def prod_equiv_prod {α₁ α₂ β₁ β₂ : Type*}
    (e₁ : α₁ ≃ β₁) (e₂ : α₂ ≃ β₂) : α₁ × α₂ ≃ β₁ × β₂ :=
  Equiv.prodCongr e₁ e₂

theorem prod_equiv_prod_fst {α₁ α₂ β₁ β₂ : Type*}
    (e₁ : α₁ ≃ β₁) (e₂ : α₂ ≃ β₂) (x : α₁ × α₂)  :
    (prod_equiv_prod e₁ e₂ x).1 = e₁ x.1 := rfl

-- make sure to use `def` when you're defining something
-- #lint

/- Can I prove the sorry's in the script below? -/
lemma my_equality (a b : ℕ) : (a + b) + a ≤ 2 * (a + b) := by
  set c : ℕ := a + b
  linarith


/- Will the following tactic work? -/
-- rw cannot rewrite under binders (∃, ∀, ∑, ∫, ...)
example {p q : ℕ → Prop} (h : ∃ x, p x)
    (h2 : ∀ x, p x ↔ q x) : ∃ x, q x := by
  simp_rw [h2] at h
  assumption


/- Will either of the following tactics work? -/
example {f : ℕ → ℕ} {p : ℕ → Prop}
    (h : ∀ x, p x → f x = x) :
    ∀ x, p x → f (f x) = x := by
  intros x hx
  -- rw [h x hx]
  -- simp_rw [h x hx]
  simp [*]

-- take-away: simp and simp_rw only rewrite if
-- they can prove the side-conditions


/- ## Now let's continue writing some tactics

To do something nontrivial, we have to get information from the context.
We do this using `let x ← t`. This executes `t` and stores the result in `x`. -/

elab "report" : tactic => do
  let goal ← getMainGoal
  logInfo m!"Current goal: {goal}"

example : True := by
  report
  trivial

example : ∀ p q : ℕ, p + q = q + p  := by
  report
  exact add_comm


/- We can abbreviate this by using `← t` anywhere to mean "the result of running `t`" -/

elab "report2" : tactic => do
  logInfo m!"Current goal: {← getMainGoal}"

example : ∀ p q : ℕ, p + q = q + p := by
  report2
  exact add_comm







/- Now let's implement an actual tactic: the assumption tactic.
We go through each assumption and look whether the type of the assumption is
*definitionally equal* to the target. -/

elab "my_assumption" : tactic => do
  withMainContext do
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    -- withReducible do
    if ← isDefEq ldecl.type (← getMainTarget) then
      closeMainGoal ldecl.toExpr
      logInfo m!"found hypothesis {ldecl.toExpr} with type: {← inferType ldecl.toExpr}"
      return
  throwTacticEx `my_assumption (← getMainGoal)
    m!"unable to find matching hypothesis of type {indentExpr (← getMainTarget)}"

example (n m : ℕ) (h1 : 0 ≤ m) (h2 : n = 0) (h3 : m ≤ 9) : n = 0 := by
  my_assumption

example (p q : ℕ) : p + q = q + p := by
  my_assumption

def double (x : ℕ) : ℕ := x + x

example (n : ℕ) (h1 : double n = 12) : n + n = 12 := by
  my_assumption


/- To see why the `isImplementationDetail` line is important, consider the following proof.
What is `my_lemma` in the proof? -/
theorem my_lemma : ∀ (n : ℕ), 0 + n = n + 0
  | 0 => rfl
  | (Nat.succ n) => by rw [Nat.add_succ, my_lemma n]
    -- my_lemma (Nat.succ n)
example : 1 = 2 := by
  my_assumption


/- Let's see why the `withMainContext` line is important. -/

example : ∀ (n m : ℕ) (h1 : 0 ≤ m) (h2 : n = 0) (h3 : m ≤ 9), n = 0 := by
  intros
  my_assumption






/- As a second example, we want to write a tactic that creates a new hypothesis
`a₁ + a₂ = b₁ + b₂` from the assumptions `a₁ = b₁` and `a₂ = b₂`. -/

example (a b c d : ℕ) (h : a = b) (h' : c = d) : a + c = b + d := by
  have H := congrArg₂ HAdd.hAdd h h' -- add_eq h h' with H
  exact H

elab "add_eq" eq₁:ident eq₂:ident " with " new:ident : tactic =>
  withMainContext do
    let newTerm  ← `(congrArg₂ HAdd.hAdd $eq₁ $eq₂)
    let prf ← elabTerm newTerm none
    let typ ← inferType prf
    let hyp := #[{userName := new.getId, type := typ, value := prf}]
    let (newFVars, newGoal) ← (← getMainGoal).assertHypotheses hyp
    replaceMainGoal [newGoal]

example (a b c d : ℕ) (h : a = b) (h' : c = d) : a + c = b + d := by
  add_eq h h' with H
  exact H

/- If we want to be more flexible, and make the `with H` optional,
we can do this by separately declare a syntax and elaboration rules for that syntax.
elab = syntax + elab_rules -/

syntax "add_eq'" ident ident ("with" ident)? : tactic

elab_rules : tactic
| `(tactic| add_eq' $eq₁:ident $eq₂:ident $[with $new]?) =>
  withMainContext do
    logInfo m!"{new}" -- we print the variable `new`
    let prfStx  ← `(congr (congrArg HAdd.hAdd $eq₁) $eq₂)
    let prf ← elabTerm prfStx none
    let typ ← inferType prf
    -- we use the name `new`, or make a name ourselves
    let newName := match new with
    | some ident => ident.getId
    | none => `newEq
    let (newFVars, newGoal) ← (← getMainGoal).assertHypotheses
      #[{userName := newName, type := typ, value := prf}]
    replaceMainGoal [newGoal]

example (a b c d : ℕ) (h : a = b) (h' : c = d) : a + c = b + d  := by
  add_eq' h h'
  assumption








/- Here we do something similar: we multiply both sides of a hypothesis by
a constant (and remove the existing hypothesis) -/

example (a b c : ℤ) (hyp : a = b) : c * a = c * b := by
  replace hyp := congr_arg (fun x ↦ c * x) hyp
  exact hyp

elab "mul_left" x:term l:location : tactic =>
  withMainContext do
    match expandLocation l with
    | .targets #[hyp] false => do
      let hypTerm : Term := ⟨hyp⟩
      let prfStx ← `(congr_arg (fun y ↦ $x * y) $hypTerm)
      let prf ← elabTerm prfStx none
      let typ ← inferType prf
      let fvarId ← getFVarId hyp
      let (newFVars, newGoal) ← (← getMainGoal).assertHypotheses
        #[{userName := hyp.getId, type := typ, value := prf}]
      let newGoal ← newGoal.clear fvarId
      replaceMainGoal [newGoal]
    | _ => throwError "You can use this tactic only at one hypothesis."


example (a b c : ℤ) (hyp : a = b) : c * a = c * b := by
  mul_left c at hyp
  exact hyp
