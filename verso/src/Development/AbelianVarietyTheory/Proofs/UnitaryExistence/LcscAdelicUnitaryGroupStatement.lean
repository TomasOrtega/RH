import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FUnitaryExistence%2FLcscAdelicUnitaryGroup.lean&line=134#L134)
-/
theorem _root_.GlobalTheory.T.lcsc_adelic_unitary_group : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), LocallyCompactSpace (HA (AF F) σ J) ∧ SecondCountableTopology (HA (AF F) σ J) ∧ T2Space (HA (AF F) σ J) := by
  first | exact @GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary | exact GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary | (intros; apply GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary <;> assumption)
