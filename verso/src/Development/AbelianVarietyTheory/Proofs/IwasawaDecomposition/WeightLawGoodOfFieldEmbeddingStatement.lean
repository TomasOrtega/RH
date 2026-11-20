import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightLawGoodOfFieldEmbedding
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mem.LatGood.lawGood` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FWeightLawGoodOfFieldEmbedding.lean&line=203#L203)
-/
theorem _root_.GlobalTheory.T.weight_law_good_of_field_embedding : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n), FOk emb σ → S.Ok → ∀ h, S.LawGood emb lam h := by
  first | exact @GlobalTheory.Mem.LatGood.lawGood | exact GlobalTheory.Mem.LatGood.lawGood | (intros; apply GlobalTheory.Mem.LatGood.lawGood <;> assumption)
