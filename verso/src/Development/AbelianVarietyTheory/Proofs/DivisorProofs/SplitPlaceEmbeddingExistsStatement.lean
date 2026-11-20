import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceEmbeddingExists
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSplitPlaceEmbeddingExists.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.split_place_embedding_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ v : Pl F, SplitsFully E v → Nonempty (E →ₐ[F] Fv F v) := by
  first | exact @GlobalTheory.SplitEmbed.exists_algHom_of_splitsFully | exact GlobalTheory.SplitEmbed.exists_algHom_of_splitsFully | (intros; apply GlobalTheory.SplitEmbed.exists_algHom_of_splitsFully <;> assumption)
