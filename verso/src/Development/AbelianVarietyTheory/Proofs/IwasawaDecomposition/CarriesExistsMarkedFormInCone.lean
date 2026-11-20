import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

/- English proof (translation)
Introduce `O _ bar w0 c X₀ _ _ _ m δ₀ v t hbal hv hpos hc₀ ht hsum X _ _ _ m' δ hc`. Take `⟨e₀, s₀, hδ₀⟩` from `hc₀`. Take `⟨e, s, hδ⟩` from `hc`. Use `set g : X ≃ₗ[O] X₀ := e.trans e₀.symm with hg`. Use `⟨pull g.toLinearMap v, pull_mem _ hbal, fun y => by simpa using hpos (g y), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[evalZ_pull _ g.surjective]`. Conclude with `OrbMark.orbFun_evalZ_self w0 hv hbal.1`. Use `⟨fun j => t (s₀.symm (s j)), fun j => ht _, LinearMap.ext₂ fun a b => ?_⟩` and prove the remaining obligations. Establish `h1` using `LinearMap.congr_fun₂ hsum (g a) (g b)`. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul] at h1 ⊢`.

Use `show ((v (g a) (g b) : ℤ) : ℝ) = _`. Rewrite using `[h1]`. Establish `key : ∀ i, (δ₀ i (g a) (g b) : ℝ) = (c.δ (s₀ i) (e a) (e b) : ℝ)` using `fun i => by`. Rewrite using `[hδ₀ i, pull_apply]`. Simplify using `[hg]`.

Establish `key' : ∀ j, (δ j a b : ℝ) = (c.δ (s j) (e a) (e b) : ℝ)` using `fun j => by`. Rewrite using `[hδ j, pull_apply]`. Both sides reduce to the same expression. Simplify using `only [key, key']`. Rewrite using `[← (s.trans s₀.symm).sum_comp]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem carries_exists_marked : ∀ {O : Type} [CommRing O] (bar : O → O) (w0 : O) (c : FormFamily O) {X₀ : Type} [AddCommGroup X₀] [Module O X₀] [Module.Finite O X₀] {m : ℕ} (δ₀ : Fin m → LinearMap.BilinForm ℤ X₀) (v : LinearMap.BilinForm ℤ X₀) (t : Fin m → ℝ),
  v ∈ balForms bar X₀ → v ≠ 0 → (∀ y, 0 ≤ v y y) → c.Carries δ₀ → (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m' : ℕ) (δ : Fin m' → LinearMap.BilinForm ℤ X), c.Carries δ →
    ∃ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) ∧ (OrbMark.orbFun O w0 v).evalZ β = 1 ∧ InRCone δ β := by
  intro O _ bar w0 c X₀ _ _ _ m δ₀ v t hbal hv hpos hc₀ ht hsum X _ _ _ m' δ hc
  obtain ⟨e₀, s₀, hδ₀⟩ := hc₀
  obtain ⟨e, s, hδ⟩ := hc
  set g : X ≃ₗ[O] X₀ := e.trans e₀.symm with hg
  refine ⟨pull g.toLinearMap v, pull_mem _ hbal, fun y => by simpa using hpos (g y), ?_, ?_⟩
  · rw [evalZ_pull _ g.surjective]
    exact OrbMark.orbFun_evalZ_self w0 hv hbal.1
  · refine ⟨fun j => t (s₀.symm (s j)), fun j => ht _, LinearMap.ext₂ fun a b => ?_⟩
    have h1 := LinearMap.congr_fun₂ hsum (g a) (g b)
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul] at h1 ⊢
    show ((v (g a) (g b) : ℤ) : ℝ) = _
    rw [h1]
    have key : ∀ i, (δ₀ i (g a) (g b) : ℝ) = (c.δ (s₀ i) (e a) (e b) : ℝ) := fun i => by
      rw [hδ₀ i, pull_apply]; simp [hg]
    have key' : ∀ j, (δ j a b : ℝ) = (c.δ (s j) (e a) (e b) : ℝ) := fun j => by
      rw [hδ j, pull_apply]; rfl
    simp only [key, key']
    rw [← (s.trans s₀.symm).sum_comp]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp

end GlobalTheory.PolFan
