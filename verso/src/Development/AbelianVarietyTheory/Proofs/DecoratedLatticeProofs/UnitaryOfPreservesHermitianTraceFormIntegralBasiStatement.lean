import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryOfPreservesHermitianTraceFormIntegralBasi
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FUnitaryOfPreservesHermitianTraceFormIntegralBasi.lean&line=83#L83)
-/
theorem _root_.GlobalTheory.T.unitary_of_preserves_hermitianTraceForm_integralBasis : ∀ (I : AutInst) {N : ℕ} (e : Fin N → Fin I.n → I.E) (M : Matrix (Fin I.n) (Fin I.n) I.E), IsZBasis I e →
    (∀ i j, trForm I (M *ᵥ e i) (M *ᵥ e j) = trForm I (e i) (e j)) →
    Formalism.UG.cT (starRingEnd I.E) M * I.J * M = I.J := by
  first | exact @GlobalTheory.CuspGeo.unitary_of_trForm_zBasis | exact GlobalTheory.CuspGeo.unitary_of_trForm_zBasis | (intros; apply GlobalTheory.CuspGeo.unitary_of_trForm_zBasis <;> assumption)
