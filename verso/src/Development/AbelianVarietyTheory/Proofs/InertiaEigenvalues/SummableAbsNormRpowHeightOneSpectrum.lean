import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CountableIdealSummableAbsNormRpow

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem summable_absNorm_rpow_heightOneSpectrum :
    ∀ (F : Type) [Field F] [NumberField F] (σ : ℝ), 1 < σ →
      Summable (fun v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) =>
        (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ)) :=
  fun F _ _ σ hσ => ((GlobalTheory.countable_ideal_and_summable_absNorm_rpow F).2 σ hσ).2

end GlobalTheory
