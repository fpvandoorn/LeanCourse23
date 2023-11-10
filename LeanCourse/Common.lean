import Mathlib.Tactic

-- don't edit this file!

set_option warningAsError false

section
open Lean Parser Tactic

macro (name := ring) "ring" : tactic =>
  `(tactic| first | ring1 | ring_nf)

macro (name := ring_at) "ring" cfg:config ? loc:location : tactic =>
  `(tactic| ring_nf $cfg ? $loc)

end

namespace Nat
open Lean Elab Term Meta

def elabIdentFactorial : TermElab := fun stx expectedType? =>
  match stx with
  | `($name:ident) => do
    let name := name.getId
    if name.hasMacroScopes then
      -- I think this would mean the name appears from within a quote.
      -- I'm not sure how to properly deal with this, and it seems ok to just not.
      throwUnsupportedSyntax
    else
      try
        elabIdent stx expectedType?
      catch e =>
        match name with
        | .str n s =>
          if s.endsWith "!" then
            let name' := Name.str n (s.dropRight 1)
            try
              elabTerm (← `(Nat.factorial $(mkIdent name'))) expectedType?
            catch _ =>
              throw e
          else
            throw e
        | _ => throw e
  | _ => throwUnsupportedSyntax

attribute [scoped term_elab ident] elabIdentFactorial

attribute [eliminator] Nat.recAux

@[elab_as_elim]
def two_step_induction {P : ℕ → Sort*} (zero : P 0) (one : P 1)
    (step : ∀ (k : ℕ), (IH0 : P k) → (IH1 : P (k + 1)) → P (k + 2)) (n : ℕ) :
    P n := by
  induction n using Nat.strongRec with
  | ind n ih =>
    rcases n with _|n
    · exact zero
    rcases n with _|n
    · exact one
    apply step
    · apply ih; linarith
    · apply ih; linarith



end Nat

section ExtraLemmas

lemma pow_self_ne_zero (n : ℕ) : n ^ n ≠ 0 := by
  by_cases hn : n = 0
  · simp [hn]
  · positivity

open Real

attribute [simp] div_left_inj' neg_eq_self_iff eq_neg_self_iff sqrt_eq_zero' Int.ModEq.rfl

end ExtraLemmas
