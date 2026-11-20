import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDvrExtensionEmbedding
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_complete_dvr_ext_numberField_sqrt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FExistsDvrExtensionEmbedding.lean&line=43#L43)
-/
theorem _root_.GlobalTheory.T.exists_dvr_extension_embedding : ∀ (W Qq E K : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] [IsAdicComplete (IsLocalRing.maximalIdeal W) W] [Field E] [Field K] [NumberField K] (i : E →+* Qq) (e : E →+* K) (a : W), ∃ (O Kf : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (_ : Field Kf) (_ : Algebra O Kf) (ι : Qq →+* Kf) (j : W →+* O) (w : O) (eK : K →+* Kf), IsFractionRing O Kf ∧ (∀ x : W, ι (algebraMap W Qq x) = algebraMap O Kf (j x)) ∧ j.Finite ∧ IsAdicComplete (IsLocalRing.maximalIdeal O) O ∧ w ^ 2 = j a ∧ ∀ x : E, eK (e x) = ι (i x) := by
  first | exact @GlobalTheory.exists_complete_dvr_ext_numberField_sqrt | exact GlobalTheory.exists_complete_dvr_ext_numberField_sqrt | (intros; apply GlobalTheory.exists_complete_dvr_ext_numberField_sqrt <;> assumption)
