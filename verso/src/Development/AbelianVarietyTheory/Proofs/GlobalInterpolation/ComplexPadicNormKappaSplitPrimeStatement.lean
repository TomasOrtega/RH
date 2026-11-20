import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ComplexPadicNormKappaSplitPrime
import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.BaseEx
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FComplexPadicNormKappaSplitPrime.lean&line=64#L64)
-/
theorem _root_.GlobalTheory.T.complexPadic_norm_kappa_splitPrime : ∀ (D : D7) (γ₀ : IsoK D) (k : KapChoice γ₀) (q : ℕ) [Fact q.Prime], SplitK D q → ∀ ι : ℂ ≃+* ℂ_[q], ‖ι k.kappa‖ = ‖ι (k.rt q)‖ ^ (-(k.yP q)) := by
  first | exact @GlobalTheory.KapSplitNorm.norm_kappa_split | exact GlobalTheory.KapSplitNorm.norm_kappa_split | (intros; apply GlobalTheory.KapSplitNorm.norm_kappa_split <;> assumption)
