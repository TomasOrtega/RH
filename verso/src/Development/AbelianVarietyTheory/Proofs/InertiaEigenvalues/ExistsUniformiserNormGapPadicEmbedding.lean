import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRamificationOverPlaceOfCdvrReadingInCp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifGap

open NumberField IsDedekindDomain Formalism.L2.Pj GlobalTheory.GeoTie

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [NumberField F] (φ : F →+* ℂ_[p])

/- English proof (translation)
Distinguish the cases in `h0 : x = 0`. Rewrite using `[h0]`. Conclude with `zero_le'`. Rewrite `hx`, the goal using `[← WithZero.exp_log h0]`. Rewrite `hx` using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`.

Rewrite using `[WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (hx : x < 1) : x ≤ WithZero.exp (-1) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le'
  · rw [← WithZero.exp_log h0] at hx ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
    rw [WithZero.exp_le_exp]
    omega

/- English proof (translation)
Take `⟨n, d, hnd⟩` from `HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (placeAt φ) x hx.le`. Establish `hd : ‖φ ((d : 𝓞 F) : F)‖ = 1` using `le_antisymm (norm_int_le_one φ _) (not_lt.1 d.2)`. Establish `hdv : (placeAt φ).valuation F (algebraMap (𝓞 F) F (d : 𝓞 F)) ≤ 1`. Rewrite using `[HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `HeightOneSpectrum.intValuation_le_one _ _`.

Establish `hn : (placeAt φ).intValuation n < 1`. Establish `h0 : (placeAt φ).valuation F (algebraMap (𝓞 F) F n) < 1`. Rewrite using `[← hnd, map_mul]`. Conclude with `(mul_le_of_le_one_right' hdv).trans_lt hx`. Rewrite `h0` using `[HeightOneSpectrum.valuation_of_algebraMap]`. Then use the resulting hypothesis.

Establish `hnm : ‖φ (n : F)‖ < 1` using `(mem_placeAt φ n).1 ((HeightOneSpectrum.intValuation_lt_one_iff_mem _ n).1 hn)`. Establish `h2` using `congrArg (fun t => ‖φ t‖) hnd`. Simplify using `only [map_mul, norm_mul] at h2`. Establish `h3 : ‖φ x‖ * ‖φ ((d : 𝓞 F) : F)‖ = ‖φ (n : F)‖` using `h2`. Rewrite `h3` using `[hd, mul_one]`.

Rewrite using `[h3]`. Conclude with `hnm`.
-/
theorem norm_lt_one_of_valuation_lt_one {x : F} (hx : (placeAt φ).valuation F x < 1) : ‖φ x‖ < 1 := by
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (placeAt φ) x hx.le
  have hd : ‖φ ((d : 𝓞 F) : F)‖ = 1 := le_antisymm (norm_int_le_one φ _) (not_lt.1 d.2)
  have hdv : (placeAt φ).valuation F (algebraMap (𝓞 F) F (d : 𝓞 F)) ≤ 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_le_one _ _
  have hn : (placeAt φ).intValuation n < 1 := by
    have h0 : (placeAt φ).valuation F (algebraMap (𝓞 F) F n) < 1 := by
      rw [← hnd, map_mul]
      exact (mul_le_of_le_one_right' hdv).trans_lt hx
    rwa [HeightOneSpectrum.valuation_of_algebraMap] at h0
  have hnm : ‖φ (n : F)‖ < 1 := (mem_placeAt φ n).1 ((HeightOneSpectrum.intValuation_lt_one_iff_mem _ n).1 hn)
  have h2 := congrArg (fun t => ‖φ t‖) hnd
  simp only [map_mul, norm_mul] at h2
  have h3 : ‖φ x‖ * ‖φ ((d : 𝓞 F) : F)‖ = ‖φ (n : F)‖ := h2
  rw [hd, mul_one] at h3
  rw [h3]; exact hnm

/- English proof (translation)
Introduce `p _ F _ _ φ`. Use `set v := (placeAt φ).valuation F with hv`. Take `⟨ϖ, hϖ⟩` from `HeightOneSpectrum.valuation_exists_uniformizer F (placeAt φ)`. Establish `hϖ1 : v ϖ < 1`. Rewrite using `[hϖ, ← WithZero.exp_zero, WithZero.exp_lt_exp]`.

Evaluate the numerical expressions. Establish `hϖ0 : ϖ ≠ 0`. Introduce `h`. Rewrite `hϖ` using `[h, map_zero]`. Conclude with `WithZero.zero_ne_coe hϖ`.

Use `⟨ϖ, norm_pos_iff.2 ((map_ne_zero φ).2 hϖ0), norm_lt_one_of_valuation_lt_one φ hϖ1, fun c hc => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hc0 : c = 0`. Rewrite using `[hc0, map_zero, norm_zero]`. Conclude with `norm_nonneg _`. Establish `hvc : v c < 1`.

Assume the negation of the conclusion as `hge`. Rewrite `hge` using `[not_lt]`. Establish `hinv : v c⁻¹ ≤ 1`. Rewrite using `[map_inv₀]`. Conclude with `inv_le_one_of_one_le₀ hge`.

Establish `h1` using `GlobalTheory.ReadingOver.norm_le_one_of_valuation_le_one φ hinv`. Rewrite `h1` using `[map_inv₀, norm_inv]`. Establish `hpos : 0 < ‖φ c‖` using `norm_pos_iff.2 ((map_ne_zero φ).2 hc0)`. Use `(inv_le_one₀ hpos).1 h1` as an intermediate fact. Conclude with `absurd hc (not_lt.2 this)`.

Establish `hq : v (c / ϖ) ≤ 1`. Rewrite using `[map_div₀, hϖ]`. Conclude with `div_le_one_of_le₀ (le_exp_neg_one_of_lt_one hvc) zero_le'`. Establish `h1` using `GlobalTheory.ReadingOver.norm_le_one_of_valuation_le_one φ hq`. Rewrite `h1` using `[map_div₀, norm_div]`.

Establish `hpos : 0 < ‖φ ϖ‖` using `norm_pos_iff.2 ((map_ne_zero φ).2 hϖ0)`. Conclude with `(div_le_one hpos).1 h1`.
-/
theorem exists_unif_norm_gap : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p]),
    ∃ ϖ : F, 0 < ‖φ ϖ‖ ∧ ‖φ ϖ‖ < 1 ∧ ∀ c : F, ‖φ c‖ < 1 → ‖φ c‖ ≤ ‖φ ϖ‖ := by
  intro p _ F _ _ φ
  set v := (placeAt φ).valuation F with hv
  obtain ⟨ϖ, hϖ⟩ := HeightOneSpectrum.valuation_exists_uniformizer F (placeAt φ)
  have hϖ1 : v ϖ < 1 := by
    rw [hϖ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  refine ⟨ϖ, norm_pos_iff.2 ((map_ne_zero φ).2 hϖ0), norm_lt_one_of_valuation_lt_one φ hϖ1, fun c hc => ?_⟩
  by_cases hc0 : c = 0
  · rw [hc0, map_zero, norm_zero]; exact norm_nonneg _
  have hvc : v c < 1 := by
    by_contra hge
    rw [not_lt] at hge
    have hinv : v c⁻¹ ≤ 1 := by
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ hge
    have h1 := GlobalTheory.ReadingOver.norm_le_one_of_valuation_le_one φ hinv
    rw [map_inv₀, norm_inv] at h1
    have hpos : 0 < ‖φ c‖ := norm_pos_iff.2 ((map_ne_zero φ).2 hc0)
    have := (inv_le_one₀ hpos).1 h1
    exact absurd hc (not_lt.2 this)
  have hq : v (c / ϖ) ≤ 1 := by
    rw [map_div₀, hϖ]
    exact div_le_one_of_le₀ (le_exp_neg_one_of_lt_one hvc) zero_le'
  have h1 := GlobalTheory.ReadingOver.norm_le_one_of_valuation_le_one φ hq
  rw [map_div₀, norm_div] at h1
  have hpos : 0 < ‖φ ϖ‖ := norm_pos_iff.2 ((map_ne_zero φ).2 hϖ0)
  exact (div_le_one hpos).1 h1

end GlobalTheory.UnifGap

end
