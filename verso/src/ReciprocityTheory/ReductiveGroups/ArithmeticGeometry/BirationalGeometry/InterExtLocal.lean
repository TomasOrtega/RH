import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterExt

noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial Filter Topology

/- English proof (translation)
Introduce `K _ ι _ P e Ψ₀ φ φ' g g' hφ hg`. Establish `hS : ∀ (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) y w, sheetDensity P Ψ φ g y w = sheetDensity P Ψ φ' g' y w`. Introduce `Ψ y w`. Unfold `sheetDensity`. Use `split_ifs with hγ`.

Use `set γ := hγ.choose with hγdef`. Establish `hev` using `hγ.choose_spec.2`. Establish `hmem : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts P` using `hev.mono fun y' h => h.2.1`. Establish `hy : γ y ∈ mcPts P` using `hmem.self_of_nhds`. Rewrite using `[hg _ hy]`.

Establish `hH : ∀ k, cxHessian (fun y' => φ k (γ y')) y = cxHessian (fun y' => φ' k (γ y')) y`. Introduce `k`. Establish `hloc : (fun y' => φ k (γ y')) =ᶠ[𝓝 y] (fun y' => φ' k (γ y'))` using `hmem.mono fun y' h => hφ k _ h`. Establish `h2` using `hloc.fderiv (𝕜 := ℝ)`. Unfold `cxHessian`.

Rewrite using `[h2.fderiv_eq]`. Unfold `maDensity`. Simplify using `only [hH]`. Both sides reduce to the same expression. Conclude with `⟨by simp only [ptsIntegralAt, hS], by simp only [ptsIntegral, ptsIntegralAt, hS]⟩`.
-/
theorem ptsLocal : PtsLocalStatement := by
  intro K _ ι _ P e Ψ₀ φ φ' g g' hφ hg
  have hS : ∀ (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) y w,
      sheetDensity P Ψ φ g y w = sheetDensity P Ψ φ' g' y w := by
    intro Ψ y w
    unfold sheetDensity
    split_ifs with hγ
    · set γ := hγ.choose with hγdef
      have hev := hγ.choose_spec.2
      have hmem : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts P := hev.mono fun y' h => h.2.1
      have hy : γ y ∈ mcPts P := hmem.self_of_nhds
      rw [hg _ hy]
      have hH : ∀ k, cxHessian (fun y' => φ k (γ y')) y = cxHessian (fun y' => φ' k (γ y')) y := by
        intro k
        have hloc : (fun y' => φ k (γ y')) =ᶠ[𝓝 y] (fun y' => φ' k (γ y')) :=
          hmem.mono fun y' h => hφ k _ h
        have h2 := hloc.fderiv (𝕜 := ℝ)
        unfold cxHessian
        rw [h2.fderiv_eq]
      unfold maDensity
      simp only [hH]
    · rfl
  exact ⟨by simp only [ptsIntegralAt, hS], by simp only [ptsIntegral, ptsIntegralAt, hS]⟩

end ReciprocityTheory.ChartRestriction.G.Geo
