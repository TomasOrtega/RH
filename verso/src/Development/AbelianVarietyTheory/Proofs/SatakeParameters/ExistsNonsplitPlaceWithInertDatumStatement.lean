import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNonsplitPlaceWithInertDatum
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FExistsNonsplitPlaceWithInertDatum.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.exists_nonsplit_place_with_inertDatum : ∀ (D : D7) (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))), (∀ s : SplitPlace D.host.E, s.v ≠ v) → ∃ w : HeightOneSpectrum (𝓞 D.host.E), NG.OverPl w v ∧ ¬ IsSplitPl D.host w ∧ Nonempty (InertDatum D.host.E n v w) := by
  first | exact @GlobalTheory.InertDatumExist.exists_inertDatum | exact GlobalTheory.InertDatumExist.exists_inertDatum | (intros; apply GlobalTheory.InertDatumExist.exists_inertDatum <;> assumption)
