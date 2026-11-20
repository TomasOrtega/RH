import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns

open MeasureTheory PositivityTheory.Rg.BcB.E1
open scoped ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.KernelComposition

/- English proof (translation)
Use `haveI : MeasurableConstSMul X.Γ X.G := ⟨fun γ => measurable_const_mul (γ : X.G)⟩`. Use `haveI : SMulInvariantMeasure X.Γ X.G X.μ := ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩`. Use `set g : X.G → ℂ := fun z => φ (x⁻¹ * z) * ker X.Γ ψ z y with hg`. Establish `hkc : Continuous fun z => ker X.Γ ψ z y` using `(hk X ψ hψ).2.1.comp (continuous_id.prodMk continuous_const)`. Establish `hgc : Continuous g` using `(hφ.1.comp (continuous_const.mul continuous_id)).mul hkc`.

Establish `hgs : HasCompactSupport g` using `HasCompactSupport.mul_right (hφ.2.comp_homeomorph (Homeomorph.mulLeft x⁻¹))`. Establish `hgi : Integrable g X.μ` using `hgc.integrable_of_hasCompactSupport hgs`. Establish `hpt : ∀ z, ker X.Γ φ x z * ker X.Γ ψ z y = ∑' γ : X.Γ, g (γ • z)`. Introduce `z`. Establish `h1 : ∀ γ : X.Γ, g (γ • z) = φ (x⁻¹ * (γ : X.G) * z) * ker X.Γ ψ z y`.

Introduce `γ`. Establish `h2 : γ • z = (γ : X.G) * z` using `rfl`. Simplify using `only [hg, h2, (hk X ψ hψ).2.2.1 γ γ.2 z y |>.1, mul_assoc]`. Simplify using `only [h1]`. Rewrite using `[tsum_mul_right, ker, tsum_eq_finsum ((hk X φ hφ).1 x z)]`.

Establish `hmeas : ∀ γ : X.Γ, Continuous fun z => g (γ • z)` using `fun γ => hgc.comp (continuous_const.mul continuous_id)`. Establish `hfin : ∑' γ : X.Γ, ∫⁻ z, ‖g (γ • z)‖ₑ ∂X.ν ≠ ∞`. Establish `h3 : ∑' γ : X.Γ, ∫⁻ z, ‖g (γ • z)‖ₑ ∂X.ν = ∫⁻ z, ‖g z‖ₑ ∂X.μ` using `(X.fd.lintegral_eq_tsum'' fun z => ‖g z‖ₑ).symm`. Rewrite using `[h3]`. Conclude with `hgi.2.ne`.

Simplify using `only [hpt]`. Rewrite using `[integral_tsum (fun γ => (hmeas γ).aestronglyMeasurable) hfin]`. Conclude with `(X.fd.integral_eq_tsum'' g hgi).symm`.
-/
theorem integral_ker_mul_eq_unfolded (hk : KerBasic) (X : Ctx) (φ ψ : X.G → ℂ) (hφ : Tst φ)
    (hψ : Tst ψ) (x y : X.G) :
    ∫ z, ker X.Γ φ x z * ker X.Γ ψ z y ∂X.ν = ∫ z, φ (x⁻¹ * z) * ker X.Γ ψ z y ∂X.μ := by
  haveI : MeasurableConstSMul X.Γ X.G := ⟨fun γ => measurable_const_mul (γ : X.G)⟩
  haveI : SMulInvariantMeasure X.Γ X.G X.μ := ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩
  set g : X.G → ℂ := fun z => φ (x⁻¹ * z) * ker X.Γ ψ z y with hg
  have hkc : Continuous fun z => ker X.Γ ψ z y :=
    (hk X ψ hψ).2.1.comp (continuous_id.prodMk continuous_const)
  have hgc : Continuous g := (hφ.1.comp (continuous_const.mul continuous_id)).mul hkc
  have hgs : HasCompactSupport g :=
    HasCompactSupport.mul_right (hφ.2.comp_homeomorph (Homeomorph.mulLeft x⁻¹))
  have hgi : Integrable g X.μ := hgc.integrable_of_hasCompactSupport hgs
  have hpt : ∀ z, ker X.Γ φ x z * ker X.Γ ψ z y = ∑' γ : X.Γ, g (γ • z) := by
    intro z
    have h1 : ∀ γ : X.Γ, g (γ • z) = φ (x⁻¹ * (γ : X.G) * z) * ker X.Γ ψ z y := by
      intro γ
      have h2 : γ • z = (γ : X.G) * z := rfl
      simp only [hg, h2, (hk X ψ hψ).2.2.1 γ γ.2 z y |>.1, mul_assoc]
    simp only [h1]
    rw [tsum_mul_right, ker, tsum_eq_finsum ((hk X φ hφ).1 x z)]
  have hmeas : ∀ γ : X.Γ, Continuous fun z => g (γ • z) := fun γ =>
    hgc.comp (continuous_const.mul continuous_id)
  have hfin : ∑' γ : X.Γ, ∫⁻ z, ‖g (γ • z)‖ₑ ∂X.ν ≠ ∞ := by
    have h3 : ∑' γ : X.Γ, ∫⁻ z, ‖g (γ • z)‖ₑ ∂X.ν = ∫⁻ z, ‖g z‖ₑ ∂X.μ :=
      (X.fd.lintegral_eq_tsum'' fun z => ‖g z‖ₑ).symm
    rw [h3]
    exact hgi.2.ne
  simp only [hpt]
  rw [integral_tsum (fun γ => (hmeas γ).aestronglyMeasurable) hfin]
  exact (X.fd.integral_eq_tsum'' g hgi).symm

/- English proof (translation)
Establish `hC : IsCompact ((fun w => x * w * y⁻¹) '' (tsupport φ * tsupport ψ))` using `(hφ.2.isCompact.mul hψ.2.isCompact).image (by fun_prop)`. Establish `hfin` using `X.proper _ hC`. Use `set s : Finset X.Γ := hfin.toFinset with hs`. Establish `hmem : ∀ γ : X.Γ, x⁻¹ * (γ : X.G) * y ∈ tsupport φ * tsupport ψ → γ ∈ s`. Introduce `γ h`.

Rewrite using `[hs, Set.Finite.mem_toFinset]`. Conclude with `⟨_, h, by simp [mul_assoc]⟩`. Establish `h1 : ∀ z, φ z * ker X.Γ ψ (x * z) y = ∑ γ ∈ s, φ z * ψ (z⁻¹ * (x⁻¹ * (γ : X.G) * y))`. Introduce `z`. Distinguish the cases in `hz : z ∈ tsupport φ`.

Rewrite using `[ker, finsum_eq_sum_of_support_subset (s := s), Finset.mul_sum]`. Use `Finset.sum_congr rfl fun γ _ => ?_` and prove the remaining obligations. Simplify using `only [mul_inv_rev, mul_assoc]`. Introduce `γ hγ`. Use `Finset.mem_coe.2 (hmem γ ?_)` and prove the remaining obligations.

Establish `hγ' : (x * z)⁻¹ * (γ : X.G) * y ∈ tsupport ψ` using `subset_tsupport _ hγ`. Use `⟨z, hz, _, hγ', ?_⟩` and prove the remaining obligations. Simplify using `[mul_assoc]`. Simplify using `[image_eq_zero_of_notMem_tsupport hz]`. Establish `hint : ∀ w : X.G, Integrable (fun z => φ z * ψ (z⁻¹ * w)) X.μ`.

Introduce `w`. Establish `hcont : Continuous fun z => φ z * ψ (z⁻¹ * w)` using `hφ.1.mul (hψ.1.comp (continuous_inv.mul continuous_const))`. Conclude with `hcont.integrable_of_hasCompactSupport (HasCompactSupport.mul_right hφ.2)`. Simplify using `only [h1]`. Rewrite using `[integral_finset_sum _ fun γ _ => hint _, ker, finsum_eq_sum_of_support_subset (s := s)]`.

Both sides reduce to the same expression. Introduce `γ hγ`. Conclude with `Finset.mem_coe.2 (hmem γ ((hc X φ ψ hφ hψ).2.1 hγ))`.
-/
theorem integral_shifted_eq_ker_cv (hc : CvTest) (X : Ctx) (φ ψ : X.G → ℂ) (hφ : Tst φ)
    (hψ : Tst ψ) (x y : X.G) :
    ∫ z, φ z * ker X.Γ ψ (x * z) y ∂X.μ = ker X.Γ (cv X.μ φ ψ) x y := by
  have hC : IsCompact ((fun w => x * w * y⁻¹) '' (tsupport φ * tsupport ψ)) :=
    (hφ.2.isCompact.mul hψ.2.isCompact).image (by fun_prop)
  have hfin := X.proper _ hC
  set s : Finset X.Γ := hfin.toFinset with hs
  have hmem : ∀ γ : X.Γ, x⁻¹ * (γ : X.G) * y ∈ tsupport φ * tsupport ψ → γ ∈ s := by
    intro γ h
    rw [hs, Set.Finite.mem_toFinset]
    exact ⟨_, h, by simp [mul_assoc]⟩
  have h1 : ∀ z, φ z * ker X.Γ ψ (x * z) y =
      ∑ γ ∈ s, φ z * ψ (z⁻¹ * (x⁻¹ * (γ : X.G) * y)) := by
    intro z
    by_cases hz : z ∈ tsupport φ
    · rw [ker, finsum_eq_sum_of_support_subset (s := s), Finset.mul_sum]
      · refine Finset.sum_congr rfl fun γ _ => ?_
        simp only [mul_inv_rev, mul_assoc]
      · intro γ hγ
        refine Finset.mem_coe.2 (hmem γ ?_)
        have hγ' : (x * z)⁻¹ * (γ : X.G) * y ∈ tsupport ψ := subset_tsupport _ hγ
        refine ⟨z, hz, _, hγ', ?_⟩
        simp [mul_assoc]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  have hint : ∀ w : X.G, Integrable (fun z => φ z * ψ (z⁻¹ * w)) X.μ := by
    intro w
    have hcont : Continuous fun z => φ z * ψ (z⁻¹ * w) :=
      hφ.1.mul (hψ.1.comp (continuous_inv.mul continuous_const))
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.mul_right hφ.2)
  simp only [h1]
  rw [integral_finset_sum _ fun γ _ => hint _, ker,
    finsum_eq_sum_of_support_subset (s := s)]
  · rfl
  · intro γ hγ
    exact Finset.mem_coe.2 (hmem γ ((hc X φ ψ hφ hψ).2.1 hγ))

/- English proof (translation)
Introduce `hk hc X φ ψ hφ hψ x y`. Rewrite using `[integral_ker_mul_eq_unfolded hk X φ ψ hφ hψ x y, ← integral_shifted_eq_ker_cv hc X φ ψ hφ hψ x y, ← integral_mul_left_eq_self (fun z => φ (x⁻¹ * z) * ker X.Γ ψ z y) x]`. Simplify using the standard rewrite rules.
-/
theorem kerMul_of_kerBasic_of_cvTest : KerBasic → CvTest → KerMul := by
  intro hk hc X φ ψ hφ hψ x y
  rw [integral_ker_mul_eq_unfolded hk X φ ψ hφ hψ x y,
    ← integral_shifted_eq_ker_cv hc X φ ψ hφ hψ x y,
    ← integral_mul_left_eq_self (fun z => φ (x⁻¹ * z) * ker X.Γ ψ z y) x]
  simp

end GlobalTheory.CompanionTheory.KernelComposition
