import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.ProjLineLimit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLatticeLeSpanNormStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLatticeSpanTwistShiftStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalChartLatticeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinrankLeAddOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLatticeDimensionUpperStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TendstoOfAsymptoticBoundsStatement
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefSectionsAsymptotic

namespace PositivityTheory.Tls2.Nef

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

/- English proof (translation)
Introduce `K _ ι _ Ω _ _ y D a hV hB hN`. Break down `Nat.eq_zero_or_pos D with rfl | hD` into its components or cases. Conclude with `GlobalTheory.CompanionTheory.Ar.Pub.NefRRModel.nefRR_dimZero y a hV hB`. Take `⟨e, c, hc, hmem⟩` from `GlobalTheory.T.chart_lattice_span_twist_shift K ι Ω y D hV hB`. Establish `hinj : Function.Injective (LinearMap.mulLeft ℚ c)` using `mul_right_injective₀ hc`.

Establish `hle : ∀ τ : ℕ, (Submodule.span ℚ (chartLatNm y a τ : Set Ω)).map (LinearMap.mulLeft ℚ c) ≤ chartLatQ y ((τ : ℤ) • a + fun k => (e k : ℤ)) 1`. Introduce `τ`. Introduce and unpack `_ ⟨s, hs, rfl⟩`. Conclude with `hmem a τ s hs`. Establish `hfd : ∀ τ : ℕ, FiniteDimensional ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω))`.

Introduce `τ`. Use `haveI := GlobalTheory.T.finiteDimensional_chart_lattice K ι Ω y D ((τ : ℤ) • a + fun k => (e k : ℤ)) hV`. Use `haveI : FiniteDimensional ℚ ((Submodule.span ℚ (chartLatNm y a τ : Set Ω)).map (LinearMap.mulLeft ℚ c)) := Submodule.finiteDimensional_of_le (hle τ)`. Conclude with `LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective _ hinj _).symm`. Establish `hup : ∀ τ : ℕ, Module.finrank ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω)) ≤ Module.finrank ℚ (chartLatQ y ((τ : ℤ) • a + fun k => (e k : ℤ)) 1)`.

Introduce `τ`. Use `haveI := GlobalTheory.T.finiteDimensional_chart_lattice K ι Ω y D ((τ : ℤ) • a + fun k => (e k : ℤ)) hV`. Rewrite using `[(Submodule.equivMapOfInjective _ hinj (Submodule.span ℚ (chartLatNm y a τ : Set Ω))).finrank_eq]`. Conclude with `Submodule.finrank_mono (hle τ)`. Establish `hlow : ∀ τ : ℕ, Module.finrank ℚ (chartLatQ y ((τ : ℤ) • a + 0) 1) ≤ Module.finrank ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω))`.

Introduce `τ`. Use `haveI := hfd τ`. Establish `hsub : chartLatQ y ((τ : ℤ) • a + 0) 1 ≤ Submodule.span ℚ (chartLatNm y a τ : Set Ω)`. Rewrite using `[add_zero, ← chartLatQ_eq_smul_one]`. Conclude with `GlobalTheory.T.chart_lattice_le_span_norm K ι Ω y a τ`.

Conclude with `Submodule.finrank_mono hsub`. Use `⟨hfd, ?_⟩` and prove the remaining obligations. Apply `GlobalTheory.T.tendsto_of_asymptotic_bounds (fun τ => (Module.finrank ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω)) : ℝ)) _ D` to reduce the goal to its premises. Introduce `ε hε filter_upwards [GlobalTheory.CompanionTheory.NefLower.nef_sections_lower K ι Ω y D a 0 hD hV hB hN ε hε] with n hn`. Conclude with `hn.trans (by exact_mod_cast hlow n)`.

Introduce `ε hε filter_upwards [GlobalTheory.T.chart_lattice_dimension_upper K ι Ω y D a (fun k => (e k : ℤ)) hD hV hB hN ε hε] with n hn`. Conclude with `le_trans (by exact_mod_cast hup n) hn`.
-/
theorem nefRR : GlobalTheory.CompanionTheory.Ar.Pub.NefRR := by
  intro K _ ι _ Ω _ _ y D a hV hB hN
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · exact GlobalTheory.CompanionTheory.Ar.Pub.NefRRModel.nefRR_dimZero y a hV hB
  obtain ⟨e, c, hc, hmem⟩ := GlobalTheory.T.chart_lattice_span_twist_shift K ι Ω y D hV hB
  have hinj : Function.Injective (LinearMap.mulLeft ℚ c) := mul_right_injective₀ hc
  have hle : ∀ τ : ℕ, (Submodule.span ℚ (chartLatNm y a τ : Set Ω)).map (LinearMap.mulLeft ℚ c) ≤
      chartLatQ y ((τ : ℤ) • a + fun k => (e k : ℤ)) 1 := by
    intro τ
    rintro _ ⟨s, hs, rfl⟩
    exact hmem a τ s hs
  have hfd : ∀ τ : ℕ, FiniteDimensional ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω)) := by
    intro τ
    haveI := GlobalTheory.T.finiteDimensional_chart_lattice K ι Ω y D ((τ : ℤ) • a + fun k => (e k : ℤ)) hV
    haveI : FiniteDimensional ℚ ((Submodule.span ℚ (chartLatNm y a τ : Set Ω)).map (LinearMap.mulLeft ℚ c)) :=
      Submodule.finiteDimensional_of_le (hle τ)
    exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective _ hinj _).symm
  have hup : ∀ τ : ℕ, Module.finrank ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω)) ≤
      Module.finrank ℚ (chartLatQ y ((τ : ℤ) • a + fun k => (e k : ℤ)) 1) := by
    intro τ
    haveI := GlobalTheory.T.finiteDimensional_chart_lattice K ι Ω y D ((τ : ℤ) • a + fun k => (e k : ℤ)) hV
    rw [(Submodule.equivMapOfInjective _ hinj (Submodule.span ℚ (chartLatNm y a τ : Set Ω))).finrank_eq]
    exact Submodule.finrank_mono (hle τ)
  have hlow : ∀ τ : ℕ, Module.finrank ℚ (chartLatQ y ((τ : ℤ) • a + 0) 1) ≤
      Module.finrank ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω)) := by
    intro τ
    haveI := hfd τ
    have hsub : chartLatQ y ((τ : ℤ) • a + 0) 1 ≤ Submodule.span ℚ (chartLatNm y a τ : Set Ω) := by
      rw [add_zero, ← chartLatQ_eq_smul_one]
      exact GlobalTheory.T.chart_lattice_le_span_norm K ι Ω y a τ
    exact Submodule.finrank_mono hsub
  refine ⟨hfd, ?_⟩
  apply GlobalTheory.T.tendsto_of_asymptotic_bounds (fun τ => (Module.finrank ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω)) : ℝ)) _ D
  · intro ε hε
    filter_upwards [GlobalTheory.CompanionTheory.NefLower.nef_sections_lower K ι Ω y D a 0 hD hV hB hN ε hε] with n hn
    exact hn.trans (by exact_mod_cast hlow n)
  · intro ε hε
    filter_upwards [GlobalTheory.T.chart_lattice_dimension_upper K ι Ω y D a (fun k => (e k : ℤ)) hD hV hB hN ε hε] with n hn
    exact le_trans (by exact_mod_cast hup n) hn

end PositivityTheory.Tls2.Nef
