import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimVec

/- English proof (translation)
Introduce `M _ _ _ g hg`. Set `e : M ≃ₗ[ℂ] (Fin (Module.finrank ℂ M) → ℂ)` to `(Module.finBasis ℂ M).equivFun`. Set `s : ℕ → ℂ` to `fun k => ((‖e (g k)‖⁻¹ : ℝ) : ℂ)`. Establish `hv : ∀ k, e (g k) ≠ 0` using `fun k h => hg k (by simpa using h)`. Establish `hmem : ∀ k, s k • e (g k) ∈ Metric.sphere (0 : Fin (Module.finrank ℂ M) → ℂ) 1`.

Introduce `k`. Establish `hn : ‖e (g k)‖ ≠ 0` using `norm_ne_zero_iff.mpr (hv k)`. Rewrite using `[mem_sphere_zero_iff_norm, norm_smul]`. Simplify using `only [s, Complex.norm_real, norm_inv, norm_norm]`. Conclude with `inv_mul_cancel₀ hn`.

Take `⟨v, hvs, φ, hφ, hlim⟩` from `(isCompact_sphere (0 : Fin (Module.finrank ℂ M) → ℂ) 1).tendsto_subseq hmem`. Establish `hv0 : v ≠ 0`. Introduce `h`. Rewrite `hvs` using `[h]`. Simplify using `at hvs`.

Use `⟨fun k => s (φ k), φ, e.symm v, hφ, by simpa using hv0, fun ℓ => ?_⟩` and prove the remaining obligations. Set `L : (Fin (Module.finrank ℂ M) → ℂ) →ₗ[ℂ] ℂ` to `ℓ ∘ₗ e.symm.toLinearMap`. Establish `hL : Continuous L` using `LinearMap.continuous_of_finiteDimensional L`. Establish `h` using `(hL.tendsto v).comp hlim`. Establish `hfun : (L ∘ ((fun k => s k • e (g k)) ∘ φ)) = fun k => s (φ k) * ℓ (g (φ k))`.

Use function extensionality and compare the values at `k`. Simplify using `[L]`. Rewrite `h` using `[hfun]`. Simplify `h` using `[L]`.
-/
theorem normalised_subseq_limit : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (g : ℕ → M), (∀ k, g k ≠ 0) → ∃ (c : ℕ → ℂ) (φ : ℕ → ℕ) (G : M), StrictMono φ ∧ G ≠ 0 ∧ ∀ ℓ : Module.Dual ℂ M, Tendsto (fun k => c k * ℓ (g (φ k))) atTop (𝓝 (ℓ G)) := by
  intro M _ _ _ g hg
  let e : M ≃ₗ[ℂ] (Fin (Module.finrank ℂ M) → ℂ) := (Module.finBasis ℂ M).equivFun
  let s : ℕ → ℂ := fun k => ((‖e (g k)‖⁻¹ : ℝ) : ℂ)
  have hv : ∀ k, e (g k) ≠ 0 := fun k h => hg k (by simpa using h)
  have hmem : ∀ k, s k • e (g k) ∈ Metric.sphere (0 : Fin (Module.finrank ℂ M) → ℂ) 1 := by
    intro k
    have hn : ‖e (g k)‖ ≠ 0 := norm_ne_zero_iff.mpr (hv k)
    rw [mem_sphere_zero_iff_norm, norm_smul]
    simp only [s, Complex.norm_real, norm_inv, norm_norm]
    exact inv_mul_cancel₀ hn
  obtain ⟨v, hvs, φ, hφ, hlim⟩ := (isCompact_sphere (0 : Fin (Module.finrank ℂ M) → ℂ) 1).tendsto_subseq hmem
  have hv0 : v ≠ 0 := by
    intro h
    rw [h] at hvs
    simp at hvs
  refine ⟨fun k => s (φ k), φ, e.symm v, hφ, by simpa using hv0, fun ℓ => ?_⟩
  let L : (Fin (Module.finrank ℂ M) → ℂ) →ₗ[ℂ] ℂ := ℓ ∘ₗ e.symm.toLinearMap
  have hL : Continuous L := LinearMap.continuous_of_finiteDimensional L
  have h := (hL.tendsto v).comp hlim
  have hfun : (L ∘ ((fun k => s k • e (g k)) ∘ φ)) = fun k => s (φ k) * ℓ (g (φ k)) := by
    funext k
    simp [L]
  rw [hfun] at h
  simpa [L] using h

end GlobalTheory.CompanionTheory.LimVec
