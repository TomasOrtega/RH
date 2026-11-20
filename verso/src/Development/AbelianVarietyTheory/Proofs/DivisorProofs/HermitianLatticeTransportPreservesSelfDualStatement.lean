import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeTransportPreservesSelfDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHermitianLatticeTransportPreservesSelfDual.lean&line=96#L96)
-/
theorem _root_.GlobalTheory.T.hermitianLatticeTransport_preserves_selfDual : ∀ (D : D7) (X : Fields) (s : Seam D X), s.Ok → ∀ (n : ℕ), StandardLatticesGL3.SD D (StandardLatticesGL3.stdL D n) ∧ ∀ L : Submodule (𝓞 X.E) (Sp X.E n), IsSdLat L → StandardLatticesGL3.SD D (s.lat L) := by
  first | exact @GlobalTheory.SeamSelfDual.seam_selfDual | exact GlobalTheory.SeamSelfDual.seam_selfDual | (intros; apply GlobalTheory.SeamSelfDual.seam_selfDual <;> assumption)
