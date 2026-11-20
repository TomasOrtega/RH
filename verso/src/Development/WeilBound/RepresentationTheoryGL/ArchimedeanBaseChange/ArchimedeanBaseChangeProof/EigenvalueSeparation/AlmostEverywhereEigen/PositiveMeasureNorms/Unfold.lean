import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.OneStepOf
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
open MeasureTheory

namespace PositivityTheory.Rg.BcB.E2.P.Unfold

/- English proof (translation)
Establish `: MeasurableConstSMul X.Γ X.G` using `⟨fun γ => measurable_const_mul (γ : X.G)⟩`. Establish `: SMulInvariantMeasure X.Γ X.G X.μ` using `⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩`. Use `set g : X.G → ℂ := fun z => φ (x⁻¹ * z) * u z with hg`. Establish `hgc : Continuous g` using `(hφ.1.comp (continuous_const.mul continuous_id)).mul hu`. Establish `hgs : HasCompactSupport g` using `HasCompactSupport.mul_right (hφ.2.comp_homeomorph (Homeomorph.mulLeft x⁻¹))`.

Establish `hgi : Integrable g X.μ` using `hgc.integrable_of_hasCompactSupport hgs`. Establish `hpt : ∀ z, ker X.Γ φ x z * u z = ∑' γ : X.Γ, g (γ • z)`. Introduce `z`. Establish `h1 : ∀ γ : X.Γ, g (γ • z) = φ (x⁻¹ * (γ : X.G) * z) * u z`. Introduce `γ`.

Establish `h2 : γ • z = (γ : X.G) * z` using `rfl`. Simplify using `only [hg, h2, hinv γ γ.2 z, mul_assoc]`. Simplify using `only [h1]`. Rewrite using `[tsum_mul_right, ker, tsum_eq_finsum ((hk X φ hφ).1 x z)]`. Establish `hmeas : ∀ γ : X.Γ, Continuous fun z => g (γ • z)` using `fun γ => hgc.comp (continuous_const.mul continuous_id)`.

Establish `hfin : ∑' γ : X.Γ, ∫⁻ z, ‖g (γ • z)‖ₑ ∂X.ν ≠ ⊤`. Establish `h3 : ∑' γ : X.Γ, ∫⁻ z, ‖g (γ • z)‖ₑ ∂X.ν = ∫⁻ z, ‖g z‖ₑ ∂X.μ` using `(X.fd.lintegral_eq_tsum'' fun z => ‖g z‖ₑ).symm`. Rewrite using `[h3]`. Conclude with `hgi.2.ne`. Simplify using `only [hpt]`.

Rewrite using `[integral_tsum (fun γ => (hmeas γ).aestronglyMeasurable) hfin]`. Use `(X.fd.integral_eq_tsum'' g hgi).symm.trans ?_` and prove the remaining obligations. Rewrite using `[← integral_mul_left_eq_self g x]`. Simplify using `[hg]`.
-/
theorem unfolded (hk : KerBasic) (X : Ctx) (φ u : X.G → ℂ) (hφ : Tst φ) (hu : Continuous u)
    (hinv : ∀ γ ∈ X.Γ, ∀ x, u (γ * x) = u x) (x : X.G) :
    ∫ y, ker X.Γ φ x y * u y ∂X.ν = ∫ y, φ y * u (x * y) ∂X.μ := by
  have : MeasurableConstSMul X.Γ X.G := ⟨fun γ => measurable_const_mul (γ : X.G)⟩
  have : SMulInvariantMeasure X.Γ X.G X.μ := ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩
  set g : X.G → ℂ := fun z => φ (x⁻¹ * z) * u z with hg
  have hgc : Continuous g := (hφ.1.comp (continuous_const.mul continuous_id)).mul hu
  have hgs : HasCompactSupport g :=
    HasCompactSupport.mul_right (hφ.2.comp_homeomorph (Homeomorph.mulLeft x⁻¹))
  have hgi : Integrable g X.μ := hgc.integrable_of_hasCompactSupport hgs
  have hpt : ∀ z, ker X.Γ φ x z * u z = ∑' γ : X.Γ, g (γ • z) := by
    intro z
    have h1 : ∀ γ : X.Γ, g (γ • z) = φ (x⁻¹ * (γ : X.G) * z) * u z := by
      intro γ
      have h2 : γ • z = (γ : X.G) * z := rfl
      simp only [hg, h2, hinv γ γ.2 z, mul_assoc]
    simp only [h1]
    rw [tsum_mul_right, ker, tsum_eq_finsum ((hk X φ hφ).1 x z)]
  have hmeas : ∀ γ : X.Γ, Continuous fun z => g (γ • z) := fun γ =>
    hgc.comp (continuous_const.mul continuous_id)
  have hfin : ∑' γ : X.Γ, ∫⁻ z, ‖g (γ • z)‖ₑ ∂X.ν ≠ ⊤ := by
    have h3 : ∑' γ : X.Γ, ∫⁻ z, ‖g (γ • z)‖ₑ ∂X.ν = ∫⁻ z, ‖g z‖ₑ ∂X.μ :=
      (X.fd.lintegral_eq_tsum'' fun z => ‖g z‖ₑ).symm
    rw [h3]
    exact hgi.2.ne
  simp only [hpt]
  rw [integral_tsum (fun γ => (hmeas γ).aestronglyMeasurable) hfin]
  refine (X.fd.integral_eq_tsum'' g hgi).symm.trans ?_
  rw [← integral_mul_left_eq_self g x]
  simp [hg]

end PositivityTheory.Rg.BcB.E2.P.Unfold

namespace PositivityTheory.Rg.BcB.E2.P

/- English proof (translation)
Introduce `hk hc X φ u hφ hu hinv`. Conclude with `⟨fun x => Unfold.unfolded hk X φ u hφ hu hinv x, hc X φ u hφ hu.locallyIntegrable⟩`.
-/
theorem unfold : KerBasic → ConvCont → Unfold := by
  intro hk hc X φ u hφ hu hinv
  exact ⟨fun x => Unfold.unfolded hk X φ u hφ hu hinv x, hc X φ u hφ hu.locallyIntegrable⟩

end PositivityTheory.Rg.BcB.E2.P
