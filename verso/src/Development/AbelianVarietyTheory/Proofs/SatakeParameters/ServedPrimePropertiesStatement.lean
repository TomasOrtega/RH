import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ServedPrimeProperties
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ModelsOK
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FServedPrimeProperties.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.servedPrime_properties : ∀ (D : D7) (p : ℕ), p.Prime → IsResidueClassZero D p → HNeZero D.host p → hP D p ≠ 0 ∧ jacobiSym (-(D.host.d : ℤ)) p = -1 ∧ Nat.Coprime (Ideal.absNorm D.host.ccK) p := by
  first | exact @GlobalTheory.TwU.Served.served_facts | exact GlobalTheory.TwU.Served.served_facts | (intros; apply GlobalTheory.TwU.Served.served_facts <;> assumption)
