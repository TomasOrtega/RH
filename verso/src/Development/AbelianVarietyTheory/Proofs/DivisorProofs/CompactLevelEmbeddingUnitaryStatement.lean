import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactLevelEmbeddingUnitary
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCompactLevelEmbeddingUnitary.lean&line=67#L67)
-/
theorem _root_.GlobalTheory.T.compact_level_embedding_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (d : ℕ) (W : Spc F E d) (c : E) (hc : c ≠ 0) (v : Pl F) (t : E →ₐ[F] Fv F v)
    (g : GL (Fin d) (Fv F v)) (x : GLoc σ (c • W.J.map σ) v), IsCompAt σ (c • W.J.map σ) t 1 g x →
    (toGAd hσ W.J hc).symm (GlobalTheory.AdelicU.emb σ (c • W.J.map σ) v x) ∈ UAt σ W (evFin F v) ∧
      (mat ((toGAd hσ W.J hc).symm (GlobalTheory.AdelicU.emb σ (c • W.J.map σ) v x))).map (piW t) = g.1 := by
  first | exact @GlobalTheory.ThetaLocalBridge.emb_mem_uAt_piW | exact GlobalTheory.ThetaLocalBridge.emb_mem_uAt_piW | (intros; apply GlobalTheory.ThetaLocalBridge.emb_mem_uAt_piW <;> assumption)
