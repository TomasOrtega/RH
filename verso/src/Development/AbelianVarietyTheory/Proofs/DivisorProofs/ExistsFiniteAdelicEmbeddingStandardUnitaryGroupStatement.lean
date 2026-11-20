import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicEmbeddingStandardUnitaryGroup
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FinEmbStd.exists_finEmb` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsFiniteAdelicEmbeddingStandardUnitaryGroup.lean&line=115#L115)
-/
theorem _root_.GlobalTheory.T.exists_finiteAdelicEmbedding_standardUnitaryGroup : ∀ {D : D7} (V : HSp D) (n : ℕ), V.gram = 1 → V.rank = n → ∃ ι : Formalism.MainNotions.StandardLatticesGL3.GA D n →* GA D V,
  (∀ x, IsFinPt V (ι x) x) ∧ Function.Injective ι ∧ ι.range = GfC V ∧
    ∀ x, (∃ γ ∈ GQ V, finHom V γ = finHom V (ι x)) ↔ x ∈ ratG D n := by
  first | exact @GlobalTheory.FinEmbStd.exists_finEmb | exact GlobalTheory.FinEmbStd.exists_finEmb | (intros; apply GlobalTheory.FinEmbStd.exists_finEmb <;> assumption)
