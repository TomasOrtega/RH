import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemPtsOverOfMemMcPts
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OneMemChartLatNm

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChartTwist

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat.UnitChart

/- English proof (translation)
Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `h` using `hu k`. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_add₀ h]`. Use `congr 1`.

Use linear arithmetic over natural numbers and integers.
-/
theorem prod_pow_toNat {K : Type} [Fintype K] {F : Type} [Field F] (u : K → F) (hu : ∀ k, u k ≠ 0) (a : K → ℤ) :
    ∏ k, u k ^ (a k).toNat = (∏ k, u k ^ a k) * ∏ k, u k ^ (-a k).toNat := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have h := hu k
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ h]
  congr 1
  omega

/- English proof (translation)
Introduce `K _ J _ Ω _ y L _ z a s w h hw c hy hz`. Take `⟨dg, dh, g, f, hg, hf, hd, e, hn, ev⟩` from `h`. Establish `hM : ∀ m : K → ℕ, aeval z (cMon c m) ≠ 0` using `fun m => by`. Rewrite using `[aeval_cMon]`. Conclude with `Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hz k)`.

Use `⟨w * ∏ k, z ⟨k, c k⟩ ^ a k, mul_ne_zero hw (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hz k)), dg + fun k => (a k).toNat, dh + fun k => (-a k).toNat, g * cMon c fun k => (a k).toNat, f * cMon c fun k => (-a k).toNat, homog_mul hg (homog_cMon c _), homog_mul hf (homog_cM …` and prove the remaining obligations. Establish `h1` using `hd k`. Simplify using `only [Pi.add_apply, Pi.zero_apply] at h1 ⊢`. Use `push_cast`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[map_mul, map_mul, aeval_cMon, aeval_cMon, e, prod_pow_toNat (fun k => y ⟨k, c k⟩) hy a]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_mul, map_mul, aeval_cMon, aeval_cMon, ev, prod_pow_toNat (fun k => z ⟨k, c k⟩) hz a]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasVal_twist : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω]
    (y : (Σ k, J k) → Ω) (L : Type) [Field L] (z : (Σ k, J k) → L) (a : K → ℤ) (s : Ω) (w : L),
    Small.HasVal y (0 : K → ℤ) s z w → w ≠ 0 → ∀ c : (k : K) → J k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      (∀ k, z ⟨k, c k⟩ ≠ 0) → ∃ v : L, v ≠ 0 ∧ Small.HasVal y a (s * ∏ k, y ⟨k, c k⟩ ^ a k) z v := by
  intro K _ J _ Ω _ y L _ z a s w h hw c hy hz
  obtain ⟨dg, dh, g, f, hg, hf, hd, e, hn, ev⟩ := h
  have hM : ∀ m : K → ℕ, aeval z (cMon c m) ≠ 0 := fun m => by
    rw [aeval_cMon]
    exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hz k)
  refine ⟨w * ∏ k, z ⟨k, c k⟩ ^ a k,
    mul_ne_zero hw (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hz k)),
    dg + fun k => (a k).toNat, dh + fun k => (-a k).toNat,
    g * cMon c fun k => (a k).toNat, f * cMon c fun k => (-a k).toNat,
    homog_mul hg (homog_cMon c _), homog_mul hf (homog_cMon c _), fun k => ?_, ?_,
    by rw [map_mul]; exact mul_ne_zero hn (hM _), ?_⟩
  · have h1 := hd k
    simp only [Pi.add_apply, Pi.zero_apply] at h1 ⊢
    push_cast
    omega
  · rw [map_mul, map_mul, aeval_cMon, aeval_cMon, e,
      prod_pow_toNat (fun k => y ⟨k, c k⟩) hy a]
    ring
  · rw [map_mul, map_mul, aeval_cMon, aeval_cMon, ev,
      prod_pow_toNat (fun k => z ⟨k, c k⟩) hz a]
    ring

end GlobalTheory.CompanionTheory.Ar.ChartTwist
