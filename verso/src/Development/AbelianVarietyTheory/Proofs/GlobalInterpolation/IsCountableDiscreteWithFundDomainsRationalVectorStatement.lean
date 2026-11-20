import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsCountableDiscreteWithFundDomainsRationalVector
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AdelicUnitaryHaarMeasure
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RationalStabiliserDomains.isDiscreteWithDomains_HstabFin` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FIsCountableDiscreteWithFundDomainsRationalVector.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.isCountableDiscreteWithFundDomains_rationalVectorStabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x : Fin 1 → Fin M → E, hE σ J (x 0) (x 0) ≠ 0 → IsDiscreteWithDomains (HstabFin (AF F) σ J x) := by
  first | exact @GlobalTheory.RationalStabiliserDomains.isDiscreteWithDomains_HstabFin | exact GlobalTheory.RationalStabiliserDomains.isDiscreteWithDomains_HstabFin | (intros; apply GlobalTheory.RationalStabiliserDomains.isDiscreteWithDomains_HstabFin <;> assumption)
