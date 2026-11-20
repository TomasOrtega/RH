import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open NumberField Matrix MeasureTheory Filter Topology
open GroundTheory.Global GroundTheory.Automorphic
open GroundTheory.Automorphic.Adele2
open Ad3 Ad3.R
open scoped NumberField.AdeleRing

set_option maxSynthPendingDepth 1
set_option synthInstance.maxSize 1000

namespace GlobalTheory.CompanionTheory.RankinSelberg

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem weyl_inv_val {R : Type*} [CommRing R] :
    (((w0 : GL (Fin 2) R)⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = !![0, -1; 1, 0] := rfl

/- English proof (translation)
Rewrite using `[weyl_inv_val]`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]`.
-/
theorem vecMul_weyl_inv {R : Type*} [CommRing R] (r : Fin 2 → R) :
    r ᵥ* (((w0 : GL (Fin 2) R)⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = ![r 1, -r 0] := by
  rw [weyl_inv_val]
  funext i
  fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/- English proof (translation)
Use function extensionality and compare the values at `r`. Rewrite using `[rightTranslate_apply, vecMul_weyl_inv]`. Both sides reduce to the same expression.
-/
theorem sFA_eq (Φ : (Fin 2 → 𝔸[ℚ]) → ℂ) :
    sFA Φ = rightTranslate (w0⁻¹ : GL (Fin 2) 𝔸[ℚ]) (adelicFourier2 ℚ Φ) := by
  funext r
  rw [rightTranslate_apply, vecMul_weyl_inv]
  rfl

/- English proof (translation)
Establish `h : (g : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]).det = ((GeneralLinearGroup.det g : (𝔸[ℚ])ˣ) : 𝔸[ℚ])` using `rfl`. Rewrite using `[Matrix.coe_units_inv, Matrix.inv_def, h, Ring.inverse_unit]`.
-/
theorem inv_val (g : G2) : ((g⁻¹ : G2) : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) =
    (((GeneralLinearGroup.det g)⁻¹ : (𝔸[ℚ])ˣ) : 𝔸[ℚ]) • (g : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]).adjugate := by
  have h : (g : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]).det = ((GeneralLinearGroup.det g : (𝔸[ℚ])ˣ) : 𝔸[ℚ]) := rfl
  rw [Matrix.coe_units_inv, Matrix.inv_def, h, Ring.inverse_unit]

/- English proof (translation)
Establish `hd : ((inv2 g : G2) : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) = !![(((GeneralLinearGroup.det g)⁻¹ : (𝔸[ℚ])ˣ) : 𝔸[ℚ]), 0; 0, (((GeneralLinearGroup.det g)⁻¹ : (𝔸[ℚ])ˣ) : 𝔸[ℚ])] * (g : Matrix (Fin 2) (Fin 2) 𝔸[ℚ])` using `rfl`. Rewrite using `[hd, inv_val g, weyl_inv_val, Matrix.adjugate_fin_two]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]`.
-/
theorem det_inverse_twist_weyl_transpose (g : G2) :
    ((inv2 g : G2) : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) *
        (((w0 : G2)⁻¹ : G2) : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) =
      (((w0 : G2)⁻¹ : G2) : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) *
        ((g⁻¹ : G2) : Matrix (Fin 2) (Fin 2) 𝔸[ℚ])ᵀ := by
  have hd : ((inv2 g : G2) : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) =
      !![(((GeneralLinearGroup.det g)⁻¹ : (𝔸[ℚ])ˣ) : 𝔸[ℚ]), 0; 0, (((GeneralLinearGroup.det g)⁻¹ : (𝔸[ℚ])ˣ) : 𝔸[ℚ])] *
        (g : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) := rfl
  rw [hd, inv_val g, weyl_inv_val, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

/- English proof (translation)
Establish `h : (fun i : Fin 2 => algebraMap ℚ 𝔸[ℚ] ((0 : Fin 2 → ℚ) i)) = 0`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Rewrite using `[Ad3.R.row, h, zero_vecMul]`.
-/
theorem row_zero (g : G2) : Ad3.R.row 0 g = 0 := by
  have h : (fun i : Fin 2 => algebraMap ℚ 𝔸[ℚ] ((0 : Fin 2 → ℚ) i)) = 0 := by
    funext i
    simp
  rw [Ad3.R.row, h, zero_vecMul]

/- English proof (translation)
Rewrite using `[hf.tsum_eq_add_tsum_ite 0, add_comm]`. Use `congr 1`. Use `tsum_subtype {ξ : Fin 2 → ℚ | ξ ≠ 0} f` as an intermediate fact. Use `this.trans (tsum_congr fun ξ => ?_)` and prove the remaining obligations. Apply the tactic sequence `by_cases h : ξ = 0 <;> simp [Set.indicator, h]`.
-/
theorem tsum_nz_add {f : (Fin 2 → ℚ) → ℂ} (hf : Summable f) :
    ∑' ξ : NZ, f ξ.1 + f 0 = ∑' ξ, f ξ := by
  classical
  rw [hf.tsum_eq_add_tsum_ite 0, add_comm]
  congr 1
  have := tsum_subtype {ξ : Fin 2 → ℚ | ξ ≠ 0} f
  refine this.trans (tsum_congr fun ξ => ?_)
  by_cases h : ξ = 0 <;> simp [Set.indicator, h]

def rotQ : (Fin 2 → ℚ) ≃ (Fin 2 → ℚ) where
  toFun ξ := ![ξ 1, -ξ 0]
  invFun ξ := ![-ξ 1, ξ 0]
  left_inv ξ := by funext i; fin_cases i <;> simp
  right_inv ξ := by funext i; fin_cases i <;> simp

/- English proof (translation)
Rewrite using `[vecMul_weyl_inv]`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp [rotQ]`.
-/
theorem alg_rotQ (ξ : Fin 2 → ℚ) :
    (fun i => algebraMap ℚ 𝔸[ℚ] (rotQ ξ i)) =
      (fun i => algebraMap ℚ 𝔸[ℚ] (ξ i)) ᵥ* (((w0 : G2)⁻¹ : G2) : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) := by
  rw [vecMul_weyl_inv]
  funext i
  fin_cases i <;> simp [rotQ]

/- English proof (translation)
Rewrite using `[sFA_eq, rightTranslate_apply, Ad3.R.row, vecMul_vecMul, det_inverse_twist_weyl_transpose, ← vecMul_vecMul, alg_rotQ]`.
-/
theorem sFA_row (Φ : (Fin 2 → 𝔸[ℚ]) → ℂ) (g : G2) (ξ : Fin 2 → ℚ) :
    sFA Φ (Ad3.R.row ξ (inv2 g)) = adelicFourier2 ℚ Φ ((fun i => algebraMap ℚ 𝔸[ℚ] (rotQ ξ i)) ᵥ*
      ((g⁻¹ : G2) : Matrix (Fin 2) (Fin 2) 𝔸[ℚ])ᵀ) := by
  rw [sFA_eq, rightTranslate_apply, Ad3.R.row, vecMul_vecMul, det_inverse_twist_weyl_transpose, ← vecMul_vecMul, alg_rotQ]

/- English proof (translation)
Introduce `Φ hΦ`. Establish `hF` using `adelicFourier2_mem_schwartzBruhat2 hΦ`. Establish `hS : sFA Φ ∈ schwartzBruhat2 ℚ`. Rewrite using `[sFA_eq]`. Conclude with `rightTranslate_mem_schwartzBruhat2 _ hF`.

Use `⟨hS, ?_, fun g => ?_⟩` and prove the remaining obligations. Establish `hdet : ((IdeleGroup.ideleModule ℚ (GeneralLinearGroup.det ((w0 : G2)⁻¹)) : ℝ)) = 1`. Establish `: GeneralLinearGroup.det ((w0 : G2)⁻¹) = 1` using `by ext1`. Express the relevant statement in the definitionally equal form `Matrix.det (((w0 : G2)⁻¹ : G2) : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) = 1`. Rewrite using `[weyl_inv_val, Matrix.det_fin_two_of]`.

Simplify using the standard rewrite rules. Rewrite using `[this, map_one]`. Both sides reduce to the same expression. Establish `h0 : sFA (sFA Φ) 0 = adelicFourier2 ℚ (sFA Φ) 0`. Rewrite using `[sFA_eq (sFA Φ), rightTranslate_apply, zero_vecMul]`.

Rewrite using `[h0, sFA_eq Φ, adelicFourier2_rightTranslate, zero_vecMul, adelicFourier2_adelicFourier2 hΦ, hdet]`. Simplify using the standard rewrite rules. Establish `s1 : Summable fun ξ => Φ (Ad3.R.row ξ g)` using `(poisson_rightTranslate hΦ g).1.of_norm`. Establish `s2 : Summable fun ξ => sFA Φ (Ad3.R.row ξ (inv2 g))` using `(poisson_rightTranslate hS (inv2 g)).1.of_norm`. Establish `e1 : th Φ g + Φ 0 = ∑' ξ, Φ (Ad3.R.row ξ g)`.

Use `tsum_nz_add s1` as an intermediate fact. Rewrite `this` using `[row_zero]`. Conclude with `this`. Establish `e2 : th (sFA Φ) (inv2 g) + sFA Φ 0 = ∑' ξ, sFA Φ (Ad3.R.row ξ (inv2 g))`. Use `tsum_nz_add s2` as an intermediate fact.

Rewrite `this` using `[row_zero]`. Conclude with `this`. Rewrite using `[e1, e2]`. Simplify using `only [sFA_row]`. Rewrite using `[rotQ.tsum_eq (fun ξ => adelicFourier2 ℚ Φ ((fun i => algebraMap ℚ 𝔸[ℚ] (ξ i)) ᵥ* ((g⁻¹ : G2) : Matrix (Fin 2) (Fin 2) 𝔸[ℚ])ᵀ))]`.

Establish `hc : (((Dt g)⁻¹ : ℝ) : ℂ) = (((IdeleGroup.ideleModule ℚ (Matrix.GeneralLinearGroup.det g) : ℝ))⁻¹ : ℂ)`. Rewrite using `[Complex.ofReal_inv]`. Both sides reduce to the same expression. Rewrite using `[hc]`. Simplify using `only [Ad3.R.row]`.

Conclude with `tsum_rightTranslate_eq hΦ g`.
-/
theorem theta_functional_equation : Ad3.R.AdelicThetaPoissonSummation := by
  intro Φ hΦ
  have hF := adelicFourier2_mem_schwartzBruhat2 hΦ
  have hS : sFA Φ ∈ schwartzBruhat2 ℚ := by
    rw [sFA_eq]
    exact rightTranslate_mem_schwartzBruhat2 _ hF
  refine ⟨hS, ?_, fun g => ?_⟩
  · have hdet : ((IdeleGroup.ideleModule ℚ (GeneralLinearGroup.det ((w0 : G2)⁻¹)) : ℝ)) = 1 := by
      have : GeneralLinearGroup.det ((w0 : G2)⁻¹) = 1 := by
        ext1
        change Matrix.det (((w0 : G2)⁻¹ : G2) : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) = 1
        rw [weyl_inv_val, Matrix.det_fin_two_of]
        simp
      rw [this, map_one]
      rfl
    have h0 : sFA (sFA Φ) 0 = adelicFourier2 ℚ (sFA Φ) 0 := by
      rw [sFA_eq (sFA Φ), rightTranslate_apply, zero_vecMul]
    rw [h0, sFA_eq Φ, adelicFourier2_rightTranslate, zero_vecMul, adelicFourier2_adelicFourier2 hΦ,
      hdet]
    simp
  · have s1 : Summable fun ξ => Φ (Ad3.R.row ξ g) := (poisson_rightTranslate hΦ g).1.of_norm
    have s2 : Summable fun ξ => sFA Φ (Ad3.R.row ξ (inv2 g)) := (poisson_rightTranslate hS (inv2 g)).1.of_norm
    have e1 : th Φ g + Φ 0 = ∑' ξ, Φ (Ad3.R.row ξ g) := by
      have := tsum_nz_add s1
      rw [row_zero] at this
      exact this
    have e2 : th (sFA Φ) (inv2 g) + sFA Φ 0 = ∑' ξ, sFA Φ (Ad3.R.row ξ (inv2 g)) := by
      have := tsum_nz_add s2
      rw [row_zero] at this
      exact this
    rw [e1, e2]
    simp only [sFA_row]
    rw [rotQ.tsum_eq (fun ξ => adelicFourier2 ℚ Φ ((fun i => algebraMap ℚ 𝔸[ℚ] (ξ i)) ᵥ*
      ((g⁻¹ : G2) : Matrix (Fin 2) (Fin 2) 𝔸[ℚ])ᵀ))]
    have hc : (((Dt g)⁻¹ : ℝ) : ℂ) =
        (((IdeleGroup.ideleModule ℚ (Matrix.GeneralLinearGroup.det g) : ℝ))⁻¹ : ℂ) := by
      rw [Complex.ofReal_inv]
      rfl
    rw [hc]
    simp only [Ad3.R.row]
    exact tsum_rightTranslate_eq hΦ g

end GlobalTheory.CompanionTheory.RankinSelberg

end
