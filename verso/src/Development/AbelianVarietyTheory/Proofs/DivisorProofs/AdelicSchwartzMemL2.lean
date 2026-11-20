import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergWordL2Bound
open NumberField MeasureTheory

namespace GlobalTheory.WeilM

/- English proof (translation)
Introduce `F _ _ κ _`. Use `letI : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _`. Introduce `μ hμ Φ hΦ`. Take `⟨n, g, f, hg, rfl⟩` from `GlobalTheory.ThetaSobolevBase.exists_sumPure hΦ`. Conclude with `memLp_finset_sum' _ fun i _ => GlobalTheory.ThetaSobolevBase.memLp_pureA μ hμ (f i) (hg i)`.
-/
theorem schA_memLp_two : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    letI : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
    ∀ μ : MeasureTheory.Measure (κ → AdeleRing (𝓞 F) F), μ.IsAddHaarMeasure →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, MeasureTheory.MemLp Φ 2 μ := by
  intro F _ _ κ _
  letI : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
  intro μ hμ Φ hΦ
  obtain ⟨n, g, f, hg, rfl⟩ := GlobalTheory.ThetaSobolevBase.exists_sumPure hΦ
  exact memLp_finset_sum' _ fun i _ => GlobalTheory.ThetaSobolevBase.memLp_pureA μ hμ (f i) (hg i)

end GlobalTheory.WeilM
