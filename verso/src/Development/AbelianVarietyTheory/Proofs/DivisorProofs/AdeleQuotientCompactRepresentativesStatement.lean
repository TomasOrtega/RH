import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleQuotientCompactRepresentatives
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAdeleQuotientCompactRepresentatives.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.adele_quotient_compact_representatives : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ C : Set (AE F E), IsCompact C ∧ ∀ a : AE F E, ∃ α : E, a - inclR (F := F) (AF F) α ∈ C := by
  first | exact @GlobalTheory.AdeleCocompactExt.exists_compact_adele_ext | exact GlobalTheory.AdeleCocompactExt.exists_compact_adele_ext | (intros; apply GlobalTheory.AdeleCocompactExt.exists_compact_adele_ext <;> assumption)
