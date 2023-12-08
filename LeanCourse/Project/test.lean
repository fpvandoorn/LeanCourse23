import LeanCourse.Common
import Mathlib.FieldTheory.IntermediateField
import Mathlib.FieldTheory.Adjoin

set_option autoImplicit true

variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E]

lemma trivail_expansion (X : Set F) : IntermediateField.adjoin F X = F := by
  unfold IntermediateField.adjoin
  simp
  rw [@Subfield.closure_union]
  --have h: ((Set.range ↑(RingHom.id F)) ⊔ Subfield.closure X) ⊆ F := by sorry
  --rw[subset_antisymm_iff.mpr]
  --apply Subfield.closure_le
  sorry
