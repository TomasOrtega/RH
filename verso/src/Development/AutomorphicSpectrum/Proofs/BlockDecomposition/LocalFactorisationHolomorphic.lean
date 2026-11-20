import Mathlib

open Filter Topology

namespace GlobalTheory.CompanionTheory.Entire

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem local_factorisation :
    ∀ A : ℂ → ℂ, Differentiable ℂ A → (∃ z, A z ≠ 0) → ∀ s₀ : ℂ,
      ∃ (k : ℕ) (U : Set ℂ) (u : ℂ → ℂ), IsOpen U ∧ s₀ ∈ U ∧ DifferentiableOn ℂ u U ∧
        ∀ s ∈ U, u s ≠ 0 ∧ A s = (s - s₀) ^ k * u s := by
  intro A hA hne s₀
  have han : AnalyticAt ℂ A s₀ := hA.analyticAt s₀
  have hnz : ¬ ∀ᶠ z in 𝓝 s₀, A z = 0 := by
    intro hev
    obtain ⟨z, hz⟩ := hne
    exact hz (AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (fun w _ => hA.analyticAt w) isPreconnected_univ (Set.mem_univ s₀) hev (Set.mem_univ z))
  obtain ⟨n, g, hg, hg0, hev⟩ := han.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnz
  have hall : ∀ᶠ z in 𝓝 s₀, AnalyticAt ℂ g z ∧ g z ≠ 0 ∧ A z = (z - s₀) ^ n * g z :=
    hg.eventually_analyticAt.and ((hg.continuousAt.eventually_ne hg0).and
      (hev.mono fun z hz => by simpa [smul_eq_mul] using hz))
  obtain ⟨U, hU, hUo, hsU⟩ := eventually_nhds_iff.mp hall
  exact ⟨n, U, g, hUo, hsU, fun z hz => (hU z hz).1.differentiableAt.differentiableWithinAt,
    fun z hz => ⟨(hU z hz).2.1, (hU z hz).2.2⟩⟩

end GlobalTheory.CompanionTheory.Entire
