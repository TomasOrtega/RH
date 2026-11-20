import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrimeSetExponentTransportFieldIsomorphism
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TwU.SeamExp.expS_seam` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FPrimeSetExponentTransportFieldIsomorphism.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.primeSetExponent_transport_fieldIsomorphism : ∀ {D : D7} {X : Fields} (s : Seam D X), s.Ok → ∀ (SS : Finset (HeightOneSpectrum (𝓞 X.E))) (P : HeightOneSpectrum (𝓞 X.E)), expS (SS.map (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s.iE)).toEmbedding) (seamP s P) = expS SS P := by
  first | exact @GlobalTheory.TwU.SeamExp.expS_seam | exact GlobalTheory.TwU.SeamExp.expS_seam | (intros; apply GlobalTheory.TwU.SeamExp.expS_seam <;> assumption)
