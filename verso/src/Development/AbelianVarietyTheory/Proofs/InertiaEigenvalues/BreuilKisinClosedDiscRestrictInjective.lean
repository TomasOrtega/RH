import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscGaugeCompletionBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormCoeffWittDiscStatement

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

/- English proof (translation)
Introduce `l _ K bk ρ ρ' h0 hle h1 R hR`. Establish `hρ0 : 0 < ρ` using `h0.trans_le hle`. Take `⟨a, ha1, ha2, ha3, -⟩` from `GlobalTheory.T.exists_gaussNorm_coeff_wittDisc l K bk ρ hρ0 h1`. Take `⟨a', ha1', ha2', -, -⟩` from `GlobalTheory.T.exists_gaussNorm_coeff_wittDisc l K bk ρ' h0 (hle.trans_lt h1)`. Take `⟨-, -, hdense, -⟩` from `GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l bk.S (X : bk.S) ρ`.

Establish `htors : ∀ z : Disc l (0 : Wq l bk.a) 1, l • z = 0 → z = 0`. Introduce `z hz`. Rewrite `hz` using `[nsmul_eq_mul]`. Conclude with `((isUnit_l_disc l (0 : Wq l bk.a) 1).mul_right_eq_zero).1 hz`. Establish `hbound : ∀ (σ : ℝ≥0), 0 < σ → ∀ (b : bk.DS σ →+ Disc l (0 : Wq l bk.a) 1) (n : ℕ), (∀ y, ‖b y‖ * (σ : ℝ) ^ n ≤ ‖y‖) → ∀ y, ‖b y‖ ≤ ((σ : ℝ) ^ n)⁻¹ * ‖y‖`.

Introduce `σ hσ b n hb y`. Establish `hp : (0 : ℝ) < (σ : ℝ) ^ n` using `pow_pos (by exact_mod_cast hσ) n`. Rewrite using `[inv_mul_eq_div, le_div_iff₀ hp]`. Conclude with `hb y`. Establish `hcoef : ∀ n y, a' n (R y) = a n y`.

Introduce `n`. Establish `e` using `hdense (Disc l (0 : Wq l bk.a) 1) htors ((a' n).comp R.toAddMonoidHom) (a n) (AddMonoidHomClass.continuous_of_bound _ (((ρ' : ℝ) ^ n)⁻¹) fun y => (hbound ρ' h0 (a' n) n (ha2' n) (R y)).trans (mul_le_mul_of_nonneg_left (hR.norm_le y) (inv_nonneg.2 (by positivity)))) (AddMonoidHomC …`. Express the relevant statement in the definitionally equal form `a' n (R (toDisc l (X : bk.S) ρ x)) = a n (toDisc l (X : bk.S) ρ x)`. Rewrite using `[hR.ext x, RingHom.id_apply, ha1', ha1])`. Introduce `y`.

Conclude with `DFunLike.congr_fun e y`. Use `(injective_iff_map_eq_zero R).2 fun y hy => ?_` and prove the remaining obligations. Establish `h` using `ha3 y 0 le_rfl fun n => by rw [← hcoef n y, hy, map_zero, norm_zero, zero_mul]`. Conclude with `norm_le_zero_iff.1 h`.
-/
theorem disc_restrict_injective : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ ρ' : ℝ≥0), 0 < ρ' → ρ' ≤ ρ →
    ρ < 1 → ∀ R : bk.DS ρ →+* bk.DS ρ', IsDiscMap (RingHom.id bk.S) R → Function.Injective R := by
  intro l _ K bk ρ ρ' h0 hle h1 R hR
  have hρ0 : 0 < ρ := h0.trans_le hle
  obtain ⟨a, ha1, ha2, ha3, -⟩ := GlobalTheory.T.exists_gaussNorm_coeff_wittDisc l K bk ρ hρ0 h1
  obtain ⟨a', ha1', ha2', -, -⟩ := GlobalTheory.T.exists_gaussNorm_coeff_wittDisc l K bk ρ' h0 (hle.trans_lt h1)
  obtain ⟨-, -, hdense, -⟩ := GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l bk.S (X : bk.S) ρ
  have htors : ∀ z : Disc l (0 : Wq l bk.a) 1, l • z = 0 → z = 0 := by
    intro z hz
    rw [nsmul_eq_mul] at hz
    exact ((isUnit_l_disc l (0 : Wq l bk.a) 1).mul_right_eq_zero).1 hz
  have hbound : ∀ (σ : ℝ≥0), 0 < σ → ∀ (b : bk.DS σ →+ Disc l (0 : Wq l bk.a) 1) (n : ℕ),
      (∀ y, ‖b y‖ * (σ : ℝ) ^ n ≤ ‖y‖) → ∀ y, ‖b y‖ ≤ ((σ : ℝ) ^ n)⁻¹ * ‖y‖ := by
    intro σ hσ b n hb y
    have hp : (0 : ℝ) < (σ : ℝ) ^ n := pow_pos (by exact_mod_cast hσ) n
    rw [inv_mul_eq_div, le_div_iff₀ hp]
    exact hb y
  have hcoef : ∀ n y, a' n (R y) = a n y := by
    intro n
    have e := hdense (Disc l (0 : Wq l bk.a) 1) htors ((a' n).comp R.toAddMonoidHom) (a n)
      (AddMonoidHomClass.continuous_of_bound _ (((ρ' : ℝ) ^ n)⁻¹) fun y =>
        (hbound ρ' h0 (a' n) n (ha2' n) (R y)).trans
          (mul_le_mul_of_nonneg_left (hR.norm_le y) (inv_nonneg.2 (by positivity))))
      (AddMonoidHomClass.continuous_of_bound _ (((ρ : ℝ) ^ n)⁻¹) (hbound ρ hρ0 (a n) n (ha2 n)))
      (fun x => by
        change a' n (R (toDisc l (X : bk.S) ρ x)) = a n (toDisc l (X : bk.S) ρ x)
        rw [hR.ext x, RingHom.id_apply, ha1', ha1])
    intro y
    exact DFunLike.congr_fun e y
  refine (injective_iff_map_eq_zero R).2 fun y hy => ?_
  have h := ha3 y 0 le_rfl fun n => by rw [← hcoef n y, hy, map_zero, norm_zero, zero_mul]
  exact norm_le_zero_iff.1 h

end GlobalTheory.BSP
