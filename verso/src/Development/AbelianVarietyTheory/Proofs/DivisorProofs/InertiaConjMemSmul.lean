import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Introduce `K Ω _ _ _ V g σ hσ`. Rewrite `hσ`, the goal using `[mem_inertia_iff]`. Take `⟨h1, h2⟩` from `hσ`. Establish `hn : ∀ z : Ω, V.valuation z < 1 → (g • V).valuation (g z) < 1`. Introduce `z hz`.

Rewrite `hz`, the goal using `[← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or]`. Break down `hz with hz | hz` into its components or cases. Use `left`. Simplify using `[hz]`. Use `right`.

Rewrite using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]`. Introduce `h`. Apply `hz` to reduce the goal to its premises. Establish `: (g⁻¹ • (g z)⁻¹) = z⁻¹`. Express the relevant statement in the definitionally equal form `g⁻¹ ((g z)⁻¹) = z⁻¹`.

Rewrite using `[map_inv₀]`. Simplify using the standard rewrite rules. Rewrite `h` using `[this]`. Then use the resulting hypothesis. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul, mul_smul, inv_smul_smul, h1]`.

Introduce `x hx`. Rewrite `hx` using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]`. Use `set y := g⁻¹ • x with hy`. Establish `hxy : x = g y` using `by simp [hy]`. Establish `: (g * σ * g⁻¹) x - x = g (σ y - y)`.

Rewrite using `[map_sub, hxy]`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `hn _ (h2 y hx)`.
-/
theorem inertia_conj_mem_smul : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω)
    (g σ : Ω ≃ₐ[K] Ω), σ ∈ inertia K V → g * σ * g⁻¹ ∈ inertia K (g • V) := by
  intro K Ω _ _ _ V g σ hσ
  rw [mem_inertia_iff] at hσ ⊢
  obtain ⟨h1, h2⟩ := hσ

  have hn : ∀ z : Ω, V.valuation z < 1 → (g • V).valuation (g z) < 1 := by
    intro z hz
    rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or] at hz ⊢
    rcases hz with hz | hz
    · left; simp [hz]
    · right
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      intro h
      apply hz
      have : (g⁻¹ • (g z)⁻¹) = z⁻¹ := by
        change g⁻¹ ((g z)⁻¹) = z⁻¹
        rw [map_inv₀]
        simp
      rwa [this] at h
  refine ⟨?_, ?_⟩
  · rw [mul_smul, mul_smul, inv_smul_smul, h1]
  · intro x hx
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at hx
    set y := g⁻¹ • x with hy
    have hxy : x = g y := by simp [hy]
    have : (g * σ * g⁻¹) x - x = g (σ y - y) := by
      rw [map_sub, hxy]
      simp
    rw [this]
    exact hn _ (h2 y hx)

end GlobalTheory
