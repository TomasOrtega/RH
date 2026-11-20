import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TranslateMemTwistedJacquetKernelRamified
import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CartanCoinv.translate_mem_twKer` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FTranslateMemTwistedJacquetKernelRamified.lean&line=58#L58)
-/
theorem _root_.GlobalTheory.T.translate_mem_twistedJacquetKernel_ramified : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (u : (w.adicCompletion E)ˣ), 1 ≤ a → Valued.v (u : w.adicCompletion E) = 1 → χ u ≠ 1 → ∀ y : V, (∀ k ∈ GlobalTheory.LFun.KGL w a, ρ k y = (((χ (Matrix.GeneralLinearGroup.det k))⁻¹ : ℂˣ) : ℂ) • y) → ∀ g, ρ g y ∈ GlobalTheory.PRep.twKer ρ (GlobalTheory.LFun.KGL w a) 1 := by
  first | exact @GlobalTheory.CartanCoinv.translate_mem_twKer | exact GlobalTheory.CartanCoinv.translate_mem_twKer | (intros; apply GlobalTheory.CartanCoinv.translate_mem_twKer <;> assumption)
