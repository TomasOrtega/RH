import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartConeComponent
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartDivisorComponents
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiProjPrime)
open GroundTheory.Heights₂.Heights (segreChartComponents mem_segreChartComponents)

/- English proof (translation)
Introduce `K _ _ ι _ W m σ i hW W' hW'`. Establish `hmin` using `mem_segreChartComponents.1 hW'`. Establish `: W'.IsPrime` using `hmin.1.1`. Set `φ : MvPolynomial (Σ k, ι k) ℂ →+* MvPolynomial (Fin m) ℂ` to `chartSubst σ i`. Establish `: (W'.comap φ).IsPrime` using `Ideal.comap_isPrime φ W'`.

Establish `hle : W.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ W'.comap φ`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `f hf`. Use `show φ (MvPolynomial.map (Int.castRingHom ℂ) f) ∈ W'`. Establish `h` using `ChartDivisorComponents.chartSection_mem hW.2.1 σ i hf`.

Rewrite `h` using `[chartSection_eq_chartSubst]`. Conclude with `hmin.1.2 h`. Take `⟨W'', hW'', hW''le⟩` from `Ideal.exists_minimalPrimes_le hle`. Conclude with `⟨W'', hW'', Ideal.map_le_iff_le_comap.2 hW''le⟩`.
-/
theorem ChartConeComponent.proof : ChartConeComponent.Statement := by
  intro K _ _ ι _ W m σ i hW W' hW'
  have hmin := mem_segreChartComponents.1 hW'
  have : W'.IsPrime := hmin.1.1
  let φ : MvPolynomial (Σ k, ι k) ℂ →+* MvPolynomial (Fin m) ℂ := chartSubst σ i
  have : (W'.comap φ).IsPrime := Ideal.comap_isPrime φ W'
  have hle : W.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ W'.comap φ := by
    rw [Ideal.map_le_iff_le_comap]
    intro f hf
    show φ (MvPolynomial.map (Int.castRingHom ℂ) f) ∈ W'
    have h := ChartDivisorComponents.chartSection_mem hW.2.1 σ i hf
    rw [chartSection_eq_chartSubst] at h
    exact hmin.1.2 h
  obtain ⟨W'', hW'', hW''le⟩ := Ideal.exists_minimalPrimes_le hle
  exact ⟨W'', hW'', Ideal.map_le_iff_le_comap.2 hW''le⟩

end GroundTheory.Heights₂.Heights.Targets
