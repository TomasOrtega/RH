import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPseudoCharacterOfApproximatedByTraces
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPsCharOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSemisimple
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PsChar.isPsChar_of_polyApprox_trc` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIsPseudoCharacterOfApproximatedByTraces.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.isPseudoCharacter_of_approximatedByTraces : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a : ℕ) (T : Γ → PadicAlgCl l) (C : Set (Γ →* GL (Fin a) (PadicAlgCl l))), PolyApprox T (trc '' C) → IsPsChar a T := by
  first | exact @GlobalTheory.PsChar.isPsChar_of_polyApprox_trc | exact GlobalTheory.PsChar.isPsChar_of_polyApprox_trc | (intros; apply GlobalTheory.PsChar.isPsChar_of_polyApprox_trc <;> assumption)
