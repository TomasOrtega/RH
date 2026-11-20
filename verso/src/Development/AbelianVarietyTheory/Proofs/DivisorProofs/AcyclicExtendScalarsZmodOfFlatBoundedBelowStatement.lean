import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AcyclicExtendScalarsZmodOfFlatBoundedBelow
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsUliftHomAdditive
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAcyclicExtendScalarsZmodOfFlatBoundedBelow.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.acyclic_extendScalars_zmod_of_flat_boundedBelow : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (K : Cx (ZMod Q)) (a : ℤ) [K.IsStrictlyGE a], (∀ n, FlatS (K.X n)) → K.Acyclic → (extCx (ZMod.castHom hq (ZMod q)) K).Acyclic := by
  first | exact @GlobalTheory.EtC.flatExtAcyc.main | exact GlobalTheory.EtC.flatExtAcyc.main | (intros; apply GlobalTheory.EtC.flatExtAcyc.main <;> assumption)
