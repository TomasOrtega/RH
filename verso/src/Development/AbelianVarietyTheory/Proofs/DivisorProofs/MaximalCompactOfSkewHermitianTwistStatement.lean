import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOfSkewHermitianTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMaximalCompactOfSkewHermitianTwist.lean&line=141#L141)
-/
theorem _root_.GlobalTheory.T.maximal_compact_of_skew_hermitian_twist : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (d r s : ℕ) (W : Spc F E d), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∃ K, IsMaxCpt σ (c • W.J.map σ) K ∧ ∀ k ∈ K, (toGAd hσ W.J hc).symm k ∈ KInf σ W B.emb := by
  first | exact @GlobalTheory.ThK.SqIntMaxCpt.exists_isMaxCpt_le_kInf | exact GlobalTheory.ThK.SqIntMaxCpt.exists_isMaxCpt_le_kInf | (intros; apply GlobalTheory.ThK.SqIntMaxCpt.exists_isMaxCpt_le_kInf <;> assumption)
