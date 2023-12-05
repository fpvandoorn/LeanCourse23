import LeanCourse.Common
import Mathlib.Tactic
set_option linter.unusedVariables false
open Lean Meta Elab Parser Tactic PrettyPrinter

/- # Today: First peek into Lean internals
-/


/- We will learn the basics of:
* notation
* macros
* tactics
-/


/- Notation in Lean is extensible. You can define your own notation. Here is a simple example. -/

notation "𝔽₂" => ZMod 2

example (n : 𝔽₂) : n + n = 0 := by simp

/- Here we define our own infix notation, the `:65` specifies the *precedence* of the notation.
Multiplication has higher precedence than addition. -/

#check 1 + 1
infix:65 " +' " => Add.add
#eval 3 +' 5 * 2



/- We can see different kinds of syntax -/

#check `(1+1)
#check `(term|(3 + 1) * (3 +' 1))
#check `(tactic| constructor)
#check `(command| #eval 1+1)


/- You can also define more complicated notations, like notation that binds a variable. -/

notation3 "do_twice" (...) " ↦ " r:60:(scoped f => f ∘ f) => r

#check do_twice x ↦ x ^ 2
#check (do_twice x ↦ x ^ 2) 3
#eval (do_twice x ↦ x ^ 2) 3


/- If you want to declare your own notation,
I recommend copying and modifying an existing notation declaration from Mathlib. -/



/- You can be even more flexible with *macros*. -/
macro "∑ " x:ident " : " l:term ", " f:term : term => `(List.sum (List.map (fun $x => $f) $l))
#eval ∑ x : [1,2,3], x ^ 3

/- Remark: macros are not pretty-printed by themselves. -/
#check ∑ x : [1,2,3], x ^ 3



/- Declaring your own pretty-printer is a bit cumbersome.
Luckily `notation` and similar commands do it for you. -/

@[app_unexpander List.sum]
def unexpListMap : Unexpander
  | `($_ $a) =>
    match a with
    | `(List.map $f $l) =>
      match f with
      | `(fun $x:ident ↦ $f) => `(∑ $x : $l, $f)
      | _ => throw ()
    | _ => throw ()
  | _ => throw ()

#check ∑ x : [1,2,3], x ^ 3

/- You can also declare macros for tactics, commands. -/

macro "split" : tactic => `(tactic| constructor)
macro "quit" : tactic => `(tactic| all_goals sorry)

example : 2 + 2 = 5 ∧ 5 < 6 := by
  split
  quit


/- We can also write commands using macros. -/

macro "#show" t:term : command => `(command|#check $t)

#show 5

/- In fact, the commands `infix` and `notation` are themselves implemented using macros,
They are macros that generate new macros. -/








/-
`macro` is short for `syntax` + `macro_rules`.
You can declare multiple macro rules
-/

syntax "easy" : tactic

-- example : True := by easy

macro_rules | `(tactic|easy) => `(tactic|assumption)
macro_rules | `(tactic|easy) => `(tactic|focus (simp; done))
macro_rules | `(tactic|easy) => `(tactic|focus (ring_nf; done))

example (n m : ℕ) (h : n ≠ m) : n ≠ m ∧ n + m = m + n ∧ 0 ≤ n := by
  refine ⟨?_, ?_, ?_⟩
  all_goals easy


/- With macros we can write down some shortcuts combining existing tactics.
For more control, it is useful to use `elab`.

Let's see some examples. -/

elab "my_tac" : tactic => logInfo "Hello"

example : True := by
  my_tac
  trivial

/- We can use `do` to execute multiple instructions. -/

elab "my_tac2" : tactic => do
  logInfo "Hello"
  logInfo "world."

example : True := by
  my_tac2
  trivial

/- We can throw errors using `throwError`. -/

elab "my_failure" : tactic => do
  logInfo "Hello"
  throwError "Oops"

example : True := by
  my_failure


/- `t <|> t'` executes `t`, and only if `t` fails, we execute `t'` instead. -/

elab "try_hard" : tactic => do
  throwError "Oops" <|> logInfo "Ok"

example : True := by
  try_hard
  trivial



/- To do something nontrivial, we have to get information from the context.
We do this using `let x ← t`. This executes `t` and stores the result in `x`. -/

elab "report" : tactic => do
  let tgt ← getMainTarget
  logInfo m!"Current goal: {tgt}"

example : True := by
  report
  trivial

example : ∀ p q : ℕ, p + q = q + p  := by
  report
  exact add_comm

/- We can abbreviate this by using `← t` anywhere to mean "the result of running `t`" -/

elab "report2" : tactic => do
  logInfo m!"Current goal: {← getMainTarget}"

example : ∀ p q : ℕ, p + q = q + p := by
  report2
  exact add_comm







/- Now let's implement an actual tactic: the assumption tactic.
We go through each assumption and look whether the type of the assumption is
*definitionally equal* to the target. -/

elab "my_assumption" : tactic => do
  let target ← getMainTarget
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    if ← isDefEq ldecl.type target then
      closeMainGoal ldecl.toExpr
      return
  throwTacticEx `my_assumption (← getMainGoal)
    m!"unable to find matching hypothesis of type {indentExpr target}"

example (n m : ℕ) (h1 : 0 ≤ m) (h2 : n = 0) (h3 : m ≤ 9) : n = 0 := by
  my_assumption

example (p q : ℕ) : p + q = q + p := by
  my_assumption

def double (x : ℕ) : ℕ := x + x

example (n : ℕ) (h1 : double n = 12) : n + n = 12 := by
  my_assumption








/- As a second example, we want to write a tactic that creates a new hypothesis
`a₁ + a₂ = b₁ + b₂` from the assumptions `a₁ = b₁` and `a₂ = b₂`. -/

example (a b c d : ℕ) (h : a = b) (h' : c = d) : a + c = b + d := by
  have H := congrArg₂ HAdd.hAdd h h'
  exact H

elab "add_eq" eq₁:ident eq₂:ident " with " new:ident : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let newTerm  ← `(congrArg₂ HAdd.hAdd $eq₁ $eq₂)
    let prf ← elabTerm newTerm none
    let typ ← inferType prf
    let (_newFVars, newGoal) ← goal.assertHypotheses
      #[{userName := new.getId, type := typ, value := prf}]
    replaceMainGoal [newGoal]

example (a b c d : ℕ) (h : a = b) (h' : c = d) : a + c = b + d := by
  add_eq h h' with H
  exact H

/- If we want to be more flexible, and make the `with H` optional,
we can do this by separately declare a syntax and elaboration rules for that syntax.
elab = syntax + elab_rules -/

syntax "add_eq'" ident ident ("with" ident)? : tactic

elab_rules : tactic
| `(tactic| add_eq' $eq₁:ident $eq₂:ident $[with $new]?) => do
  logInfo m!"{new}" -- we print the variable `new`
  let goal ← getMainGoal
  goal.withContext do
    let newTerm  ← `(congr (congrArg HAdd.hAdd $eq₁) $eq₂)
    let prf ← elabTerm newTerm none
    let typ ← inferType prf
    -- we use the name `new`, or make a name ourselves
    let newName := match new with
    | some ident => ident.getId
    | none => `newEq
    let (_newFVars, newGoal) ← goal.assertHypotheses
      #[{userName := newName, type := typ, value := prf}]
    replaceMainGoal [newGoal]

example (a b c d : ℕ) (h : a = b) (h' : c = d) : a + c = b + d  := by
  add_eq' h h' with H
  assumption








/- Here we do something similar: we multiply both sides of a hypothesis by
a constant -/

example (a b c : ℤ) (hyp : a = b) : c*a = c*b := by
  replace hyp := congr_arg (fun x ↦ c*x) hyp
  exact hyp

elab "mul_left" x:term l:location : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    match expandLocation l with
    | .targets #[hyp] false => do
      let hypTerm : Term := ⟨hyp⟩
      let prfStx ← `(congr_arg (fun y ↦ $x*y) $hypTerm)
      let prf ← elabTerm prfStx none
      let typ ← inferType prf
      let fvarId ← getFVarId hyp
      let (_newFVars, newGoal) ← goal.assertHypotheses
        #[{userName := hyp.getId, type := typ, value := prf}]
      replaceMainGoal [← newGoal.clear fvarId]
    | _ => throwError "You can use this tactic only at one hypothesis."


example (a b c : ℤ) (hyp : a = b) : c*a = c*b := by
  mul_left c at hyp
  exact hyp
