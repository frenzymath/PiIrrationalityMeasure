/-
Copyright PNT+ contributors. Released under Apache 2.0; see LICENSE.
Adapted from PrimeNumberTheoremAnd at a5154676af9aa3095150ee410cdda80555aa0642.
Blueprint metadata and unused incomplete preliminary lemmas are omitted.
-/
import Batteries.Tactic.Lemma
import Mathlib.Algebra.Notation.Support

set_option lang.lemmaCmd true

namespace Function

variable {α : Type*} [Zero α]

theorem support_id : support (id : α → α) = {0}ᶜ := by
  ext; simp

theorem support_id' {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ :=
  support_id

end Function
