import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationDivLeOneCofinite
import Mathlib
import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FValuationDivLeOneCofinite.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_finset_valuation_div_le_one_of_isLocGen : ∀ (K : Type) [Field K] [NumberField K] (I : FractionalIdeal (𝓞 K)⁰ K) (u : K),
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∀ p ∉ S, ∀ a : K, Formalism.L2.LamCM.IsLocGen p a I → u ≠ 0 →
      p.valuation K (a / u) ≤ 1 := by
  first | exact @GlobalTheory.LocGenVal.valuation_div_le_one_cofinite | exact GlobalTheory.LocGenVal.valuation_div_le_one_cofinite | (intros; apply GlobalTheory.LocGenVal.valuation_div_le_one_cofinite <;> assumption)
