import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

/- English proof (translation)
Introduce `l _ r S x a h`. Establish `hl : (0 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).pos`. Establish `hδ : (0 : ℝ) < ((l : ℝ)⁻¹) ^ r` using `by positivity`. Take `⟨y, hy⟩` from `(UniformSpace.Completion.denseRange_coe (α := PadicAlgCl l)).exists_dist_lt x hδ`. Establish `hdiff : ∀ σ : GQ l, (l : ℤ_[l]) ^ r ∣ a σ - (((a σ).appr r : ℕ) : ℤ_[l])`.

Introduce `σ`. Conclude with `Ideal.mem_span_singleton.1 (PadicInt.appr_spec r (a σ))`. Use `⟨y, fun σ => (((a σ).appr r : ℕ) : ℤ), ?_, ?_⟩` and prove the remaining obligations. Introduce `σ hσ`. Establish `hY : ‖(y : ℂ_[l]) - x‖ ≤ ((l : ℝ)⁻¹) ^ r`.

Rewrite using `[← dist_eq_norm, dist_comm]`. Conclude with `hy.le`. Establish `hAB : ‖algebraMap ℚ_[l] ℂ_[l] ((a σ - (((a σ).appr r : ℕ) : ℤ_[l]) : ℤ_[l]) : ℚ_[l])‖ ≤ ((l : ℝ)⁻¹) ^ r`. Rewrite using `[norm_algebraMap', PadicInt.padic_norm_e_of_padicInt]`. Take `⟨c, hc⟩` from `hdiff σ`.

Rewrite using `[hc, norm_mul, norm_pow, PadicInt.norm_p]`. Use `PadicInt.norm_le_one c` as an intermediate fact. Establish `h0 : (0:ℝ) ≤ ((l : ℝ)⁻¹) ^ r` using `hδ.le`. Combine the equalities or inequalities in the displayed calculation. Establish `key : (((σ y - y - ((((((a σ).appr r : ℕ) : ℤ)) : Om l))) : PadicAlgCl l) : ℂ_[l]) = (Formalism.Per.σC σ x - x - algebraMap ℚ_[l] ℂ_[l] (a σ : ℚ_[l])) + (Formalism.Per.σC σ ((y : ℂ_[l]) - x) - ((y : ℂ_[l]) - x)) + (algebraMap ℚ_[l] ℂ_[l] (a σ : ℚ_[l]) - ((((a σ).appr r : ℕ)) : ℂ_ …`.

Establish `h1 : ((σ y : PadicAlgCl l) : ℂ_[l]) = Formalism.Per.σC σ (y : ℂ_[l])` using `(GlobalTheory.RingBasics.σC_coe σ y).symm`. Generalize the expression as in `algebraMap ℚ_[l] ℂ_[l] (a σ : ℚ_[l]) = A`. Rewrite using `[map_sub]`. Use `push_cast`. Rewrite using `[h1]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hAB' : ‖algebraMap ℚ_[l] ℂ_[l] (a σ : ℚ_[l]) - ((((a σ).appr r : ℕ)) : ℂ_[l])‖ ≤ ((l : ℝ)⁻¹) ^ r`. Simplify `hAB` using `only [PadicInt.coe_sub, PadicInt.coe_natCast, map_sub, map_natCast]`. Rewrite using `[← PadicComplex.norm_extends, key]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h σ hσ) ?_)) hAB')` and prove the remaining obligations.

Rewrite using `[sub_eq_add_neg]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Rewrite using `[GlobalTheory.RingBasics.norm_σC]`. Conclude with `hY`. Rewrite using `[norm_neg]`.

Conclude with `hY`. Introduce `σ _`. Establish `: (a σ) = (a σ - (((a σ).appr r : ℕ) : ℤ_[l])) + (((a σ).appr r : ℕ) : ℤ_[l])` using `by ring`. Rewrite using `[this]`. Use `dvd_add (hdiff σ) ?_` and prove the remaining obligations.

Use `map_dvd (Int.castRingHom ℤ_[l]) (by assumption : (l : ℤ) ^ r ∣ (((a σ).appr r : ℕ) : ℤ))` as an intermediate fact. Simplify using `using this`.
-/
theorem approx_algebraic_integer : ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (S : Set (GQ l)) (x : ℂ_[l]) (a : GQ l → ℤ_[l]), (∀ σ ∈ S, ‖Formalism.Per.σC σ x - x - algebraMap ℚ_[l] ℂ_[l] (a σ : ℚ_[l])‖ ≤ ((l : ℝ)⁻¹) ^ r) → ∃ (y : Om l) (b : GQ l → ℤ), (∀ σ ∈ S, ‖σ y - y - (b σ : Om l)‖ ≤ ((l : ℝ)⁻¹) ^ r) ∧ ∀ σ, (l : ℤ) ^ r ∣ b σ → (l : ℤ_[l]) ^ r ∣ a σ := by
  intro l _ r S x a h
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hδ : (0 : ℝ) < ((l : ℝ)⁻¹) ^ r := by positivity
  obtain ⟨y, hy⟩ := (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl l)).exists_dist_lt x hδ
  have hdiff : ∀ σ : GQ l, (l : ℤ_[l]) ^ r ∣ a σ - (((a σ).appr r : ℕ) : ℤ_[l]) := by
    intro σ
    exact Ideal.mem_span_singleton.1 (PadicInt.appr_spec r (a σ))
  refine ⟨y, fun σ => (((a σ).appr r : ℕ) : ℤ), ?_, ?_⟩
  · intro σ hσ
    have hY : ‖(y : ℂ_[l]) - x‖ ≤ ((l : ℝ)⁻¹) ^ r := by
      rw [← dist_eq_norm, dist_comm]; exact hy.le
    have hAB : ‖algebraMap ℚ_[l] ℂ_[l] ((a σ - (((a σ).appr r : ℕ) : ℤ_[l]) : ℤ_[l]) : ℚ_[l])‖ ≤ ((l : ℝ)⁻¹) ^ r := by
      rw [norm_algebraMap', PadicInt.padic_norm_e_of_padicInt]
      obtain ⟨c, hc⟩ := hdiff σ
      rw [hc, norm_mul, norm_pow, PadicInt.norm_p]
      have := PadicInt.norm_le_one c
      have h0 : (0:ℝ) ≤ ((l : ℝ)⁻¹) ^ r := hδ.le
      calc ((l : ℝ)⁻¹) ^ r * ‖c‖ ≤ ((l : ℝ)⁻¹) ^ r * 1 := mul_le_mul_of_nonneg_left this h0
        _ = _ := mul_one _
    have key : (((σ y - y - ((((((a σ).appr r : ℕ) : ℤ)) : Om l))) : PadicAlgCl l) : ℂ_[l]) =
        (Formalism.Per.σC σ x - x - algebraMap ℚ_[l] ℂ_[l] (a σ : ℚ_[l])) +
        (Formalism.Per.σC σ ((y : ℂ_[l]) - x) - ((y : ℂ_[l]) - x)) +
        (algebraMap ℚ_[l] ℂ_[l] (a σ : ℚ_[l]) - ((((a σ).appr r : ℕ)) : ℂ_[l])) := by
      have h1 : ((σ y : PadicAlgCl l) : ℂ_[l]) = Formalism.Per.σC σ (y : ℂ_[l]) := (GlobalTheory.RingBasics.σC_coe σ y).symm
      generalize algebraMap ℚ_[l] ℂ_[l] (a σ : ℚ_[l]) = A
      rw [map_sub]
      push_cast
      rw [h1]
      ring
    have hAB' : ‖algebraMap ℚ_[l] ℂ_[l] (a σ : ℚ_[l]) - ((((a σ).appr r : ℕ)) : ℂ_[l])‖ ≤ ((l : ℝ)⁻¹) ^ r := by
      simpa only [PadicInt.coe_sub, PadicInt.coe_natCast, map_sub, map_natCast] using hAB
    rw [← PadicComplex.norm_extends, key]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h σ hσ) ?_)) hAB')
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [GlobalTheory.RingBasics.norm_σC]; exact hY
    · rw [norm_neg]; exact hY
  · intro σ _
    have : (a σ) = (a σ - (((a σ).appr r : ℕ) : ℤ_[l])) + (((a σ).appr r : ℕ) : ℤ_[l]) := by ring
    rw [this]
    refine dvd_add (hdiff σ) ?_
    have := map_dvd (Int.castRingHom ℤ_[l]) (by assumption : (l : ℤ) ^ r ∣ (((a σ).appr r : ℕ) : ℤ))
    simpa using this

end GlobalTheory.PMon.Ram
