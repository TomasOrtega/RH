import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EchEqOneIff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SummableNormSiegelThetaSeriesTerms

open Matrix Complex GlobalTheory.SW GlobalTheory.SW.FourierJ
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.FourierJ.Row

variable {ι : Type} [Fintype ι]

omit [Fintype ι] in
/- English proof (translation)
Use extensionality with `i`. Simplify using `[qv]`.
-/
theorem qv_smul (v : ι → ℚ) (r : ℚ) : qv (r • v) = (r : ℂ) • qv v := by
  ext i; simp [qv]

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] in

/- English proof (translation)
Introduce `ι _ _ R hR τ hτ hτ' hdet`. Establish `hτS : _root_.GlobalTheory.IsSiegel τ` using `hτ`. Establish `hRc : (R : ℂ) ≠ 0` using `by exact_mod_cast hR.ne'`. Use `set Ω : Matrix ι ι ℂ := ((R ^ 2 : ℕ) : ℂ) • τ with hΩdef`. Establish `hΩ : _root_.GlobalTheory.IsSiegel Ω` using `hτS.natCast_smul (pow_pos hR 2)`.

Establish `hΩinv : Ω⁻¹ = ((R : ℂ) ^ 2)⁻¹ • τ⁻¹`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Rewrite using `[hΩdef, smul_mul_smul_comm, Matrix.nonsing_inv_mul τ hdet]`. Use `push_cast`. Rewrite using `[inv_mul_cancel₀ (pow_ne_zero 2 hRc), one_smul]`.

Establish `T1 : ∀ (a : ι → ℚ) (ζ : ι → ℂ) (m : ι → ℤ), _root_.GlobalTheory.SW.FourierJ.gs τ ζ (a + (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zv m) = _root_.GlobalTheory.riemannThetaTerm (fun i => (a i : ℝ) / R) 0 Ω ((R : ℂ) • ζ) m`. Introduce `a ζ m`. Establish `hv : _root_.GlobalTheory.SW.qv (a + (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zv m) = (R : ℂ) • fun i => ((m i : ℤ) : ℂ) + (((a i : ℝ) / R : ℝ) : ℂ)`. Use function extensionality and compare the values at `i`. Simplify using `only [_root_.GlobalTheory.SW.qv, _root_.GlobalTheory.SW.FourierJ.zv, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [_root_.GlobalTheory.riemannThetaTerm_def, _root_.GlobalTheory.SW.FourierJ.gs, hv, Pi.zero_apply, Complex.ofReal_zero, add_zero]`. Generalize the expression as in `(fun i => ((m i : ℤ) : ℂ) + (((a i : ℝ) / R : ℝ) : ℂ)) = x`.

Use `congr 1`. Simplify using `only [hΩdef, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `T2 : ∀ (a : ι → ℚ) (ζ : ι → ℂ) (m : ι → ℤ), _root_.GlobalTheory.SW.FourierJ.ech (a ⬝ᵥ ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m)) * _root_.GlobalTheory.SW.FourierJ.gs (-τ⁻¹) (ζ ᵥ* τ⁻¹) ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m) = _root_.GlobalTheory.riemannThetaTe …`.

Introduce `a ζ m`. Establish `hv : _root_.GlobalTheory.SW.qv ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m) = (R : ℂ)⁻¹ • fun i => ((m i : ℤ) : ℂ)`. Use function extensionality and compare the values at `i`. Simplify using `[_root_.GlobalTheory.SW.qv, _root_.GlobalTheory.SW.FourierJ.zv]`. Establish `hsymm : ζ ᵥ* τ⁻¹ = τ⁻¹ *ᵥ ζ`.

Rewrite using `[← Matrix.mulVec_transpose, hτS.isSymm.inv.eq]`. Establish `hq : (((a ⬝ᵥ ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m) : ℚ)) : ℂ) = (fun i => ((m i : ℤ) : ℂ)) ⬝ᵥ fun i => (((a i : ℝ) / R : ℝ) : ℂ)`. Simplify using `only [dotProduct, Pi.smul_apply, _root_.GlobalTheory.SW.FourierJ.zv, smul_eq_mul]`. Use `push_cast`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`.

Establish `hsplit : (fun i => (Ω⁻¹ *ᵥ ((R : ℂ) • ζ)) i + (((a i : ℝ) / R : ℝ) : ℂ)) = Ω⁻¹ *ᵥ ((R : ℂ) • ζ) + fun i => (((a i : ℝ) / R : ℝ) : ℂ)` using `rfl`. Simplify using `only [_root_.GlobalTheory.riemannThetaTerm_def, Pi.zero_apply, Complex.ofReal_zero, add_zero, hsplit]`. Rewrite using `[_root_.GlobalTheory.SW.FourierJ.gs, _root_.GlobalTheory.SW.FourierJ.ech, ← Complex.exp_add, hv, hsymm, hq]`. Generalize the expression as in `(fun i => ((m i : ℤ) : ℂ)) = x`. Use `congr 1`.

Simplify using `only [hΩinv, Matrix.neg_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, dotProduct_neg, dotProduct_add, smul_eq_mul]`. Apply the tactic sequence `first | (field_simp; ring) | field_simp | ring`. Use `⟨_root_.GlobalTheory.siegelGaussIntegral Ω, ?_, fun a ζ => ?_⟩` and prove the remaining obligations. Establish `h` using `hΩ.siegelGaussIntegral_sq_mul_det`. Rewrite `h` using `[hΩdef, smul_smul, Matrix.det_smul]`.

Rewrite using `[show ((-I) * (R : ℂ) ^ 2) = -I * ((R ^ 2 : ℕ) : ℂ) by push_cast; ring]`. Conclude with `h`. Establish `hS1` using `hΩ.summable_norm_riemannThetaTerm (fun i => (a i : ℝ) / R) 0 ((R : ℂ) • ζ)`. Establish `hS2` using `hΩ.neg_inv.summable_norm_riemannThetaTerm 0 (fun i => (a i : ℝ) / R) (Ω⁻¹ *ᵥ ((R : ℂ) • ζ))`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `hS1.congr fun m => by rw [T1]`. Use `hS2.congr fun m => ?_` and prove the remaining obligations. Rewrite using `[← T2, norm_mul, _root_.GlobalTheory.SW.FourierJ.norm_ech, one_mul]`. Establish `e1 : ∑' m : ι → ℤ, _root_.GlobalTheory.SW.FourierJ.gs τ ζ (a + (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zv m) = _root_.GlobalTheory.riemannTheta (fun i => (a i : ℝ) / R) 0 Ω ((R : ℂ) • ζ)`. Rewrite using `[_root_.GlobalTheory.riemannTheta_def]`.

Conclude with `tsum_congr fun m => T1 a ζ m`. Establish `e2 : ∑' m : ι → ℤ, _root_.GlobalTheory.SW.FourierJ.ech (a ⬝ᵥ ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m)) * _root_.GlobalTheory.SW.FourierJ.gs (-τ⁻¹) (ζ ᵥ* τ⁻¹) ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m) = _root_.GlobalTheory.riemannTheta 0 (fun i => (a i : ℝ) / R) …`. Rewrite using `[_root_.GlobalTheory.riemannTheta_def]`. Conclude with `tsum_congr fun m => T2 a ζ m`. Establish `hw : (R : ℂ) • ζ ⬝ᵥ Ω⁻¹ *ᵥ ((R : ℂ) • ζ) = ζ ⬝ᵥ τ⁻¹ *ᵥ ζ`.

Rewrite using `[hΩinv]`. Simplify using `only [Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]`. Apply the tactic sequence `first | (field_simp; ring) | field_simp`. Rewrite using `[e1, e2, hΩ.riemannTheta_eq_neg_inv, hw]`. Establish `hexp : cexp (π * I * (ζ ⬝ᵥ τ⁻¹ *ᵥ ζ)) * cexp (-(π * I) * (ζ ⬝ᵥ τ⁻¹ *ᵥ ζ)) = 1`.

Rewrite using `[← Complex.exp_add, ← Complex.exp_zero]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Take the linear combination `(_root_.GlobalTheory.siegelGaussIntegral Ω * _root_.GlobalTheory.riemannTheta 0 (fun i => (a i : ℝ) / R) (-Ω⁻¹) (Ω⁻¹ *ᵥ ((R : ℂ) • ζ))) * hexp`.
-/
theorem _root_.GlobalTheory.SW.FourierJ.Row.poisson_class : ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
    (R : ℕ), 0 < R → ∀ τ ∈ _root_.GlobalTheory.SW.Siegel ι, -τ⁻¹ ∈ _root_.GlobalTheory.SW.Siegel ι →
    IsUnit τ.det → ∃ c : ℂ, c ^ 2 * (((-I) * (R : ℂ) ^ 2) ^ Fintype.card ι * τ.det) = 1 ∧
    ∀ (a : ι → ℚ) (ζ : ι → ℂ),
    (Summable fun m : ι → ℤ => ‖_root_.GlobalTheory.SW.FourierJ.gs τ ζ (a + (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zv m)‖) ∧
    (Summable fun m : ι → ℤ =>
      ‖_root_.GlobalTheory.SW.FourierJ.gs (-τ⁻¹) (ζ ᵥ* τ⁻¹) ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m)‖) ∧
    cexp (π * I * (ζ ⬝ᵥ τ⁻¹ *ᵥ ζ)) *
      ∑' m : ι → ℤ, _root_.GlobalTheory.SW.FourierJ.gs τ ζ (a + (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zv m) =
    c * ∑' m : ι → ℤ, _root_.GlobalTheory.SW.FourierJ.ech (a ⬝ᵥ ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m)) *
      _root_.GlobalTheory.SW.FourierJ.gs (-τ⁻¹) (ζ ᵥ* τ⁻¹) ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m) := by
  intro ι _ _ R hR τ hτ hτ' hdet
  have hτS : _root_.GlobalTheory.IsSiegel τ := hτ
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  set Ω : Matrix ι ι ℂ := ((R ^ 2 : ℕ) : ℂ) • τ with hΩdef
  have hΩ : _root_.GlobalTheory.IsSiegel Ω := hτS.natCast_smul (pow_pos hR 2)
  have hΩinv : Ω⁻¹ = ((R : ℂ) ^ 2)⁻¹ • τ⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [hΩdef, smul_mul_smul_comm, Matrix.nonsing_inv_mul τ hdet]
    push_cast
    rw [inv_mul_cancel₀ (pow_ne_zero 2 hRc), one_smul]
  have T1 : ∀ (a : ι → ℚ) (ζ : ι → ℂ) (m : ι → ℤ),
      _root_.GlobalTheory.SW.FourierJ.gs τ ζ (a + (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zv m) =
      _root_.GlobalTheory.riemannThetaTerm (fun i => (a i : ℝ) / R) 0 Ω ((R : ℂ) • ζ) m := by
    intro a ζ m
    have hv : _root_.GlobalTheory.SW.qv (a + (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zv m) =
        (R : ℂ) • fun i => ((m i : ℤ) : ℂ) + (((a i : ℝ) / R : ℝ) : ℂ) := by
      funext i
      simp only [_root_.GlobalTheory.SW.qv, _root_.GlobalTheory.SW.FourierJ.zv, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
      push_cast
      field_simp
      ring
    simp only [_root_.GlobalTheory.riemannThetaTerm_def, _root_.GlobalTheory.SW.FourierJ.gs, hv, Pi.zero_apply, Complex.ofReal_zero,
      add_zero]
    generalize (fun i => ((m i : ℤ) : ℂ) + (((a i : ℝ) / R : ℝ) : ℂ)) = x
    congr 1
    simp only [hΩdef, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul,
      smul_dotProduct, smul_eq_mul]
    push_cast
    ring
  have T2 : ∀ (a : ι → ℚ) (ζ : ι → ℂ) (m : ι → ℤ),
      _root_.GlobalTheory.SW.FourierJ.ech (a ⬝ᵥ ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m)) *
        _root_.GlobalTheory.SW.FourierJ.gs (-τ⁻¹) (ζ ᵥ* τ⁻¹) ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m) =
      _root_.GlobalTheory.riemannThetaTerm 0 (fun i => (a i : ℝ) / R) (-Ω⁻¹) (Ω⁻¹ *ᵥ ((R : ℂ) • ζ)) m := by
    intro a ζ m
    have hv : _root_.GlobalTheory.SW.qv ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m) =
        (R : ℂ)⁻¹ • fun i => ((m i : ℤ) : ℂ) := by
      funext i
      simp [_root_.GlobalTheory.SW.qv, _root_.GlobalTheory.SW.FourierJ.zv]
    have hsymm : ζ ᵥ* τ⁻¹ = τ⁻¹ *ᵥ ζ := by
      rw [← Matrix.mulVec_transpose, hτS.isSymm.inv.eq]
    have hq : (((a ⬝ᵥ ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m) : ℚ)) : ℂ) =
        (fun i => ((m i : ℤ) : ℂ)) ⬝ᵥ fun i => (((a i : ℝ) / R : ℝ) : ℂ) := by
      simp only [dotProduct, Pi.smul_apply, _root_.GlobalTheory.SW.FourierJ.zv, smul_eq_mul]
      push_cast
      exact Finset.sum_congr rfl fun i _ => by ring
    have hsplit : (fun i => (Ω⁻¹ *ᵥ ((R : ℂ) • ζ)) i + (((a i : ℝ) / R : ℝ) : ℂ)) =
        Ω⁻¹ *ᵥ ((R : ℂ) • ζ) + fun i => (((a i : ℝ) / R : ℝ) : ℂ) := rfl
    simp only [_root_.GlobalTheory.riemannThetaTerm_def, Pi.zero_apply, Complex.ofReal_zero, add_zero, hsplit]
    rw [_root_.GlobalTheory.SW.FourierJ.gs, _root_.GlobalTheory.SW.FourierJ.ech, ← Complex.exp_add, hv, hsymm, hq]
    generalize (fun i => ((m i : ℤ) : ℂ)) = x
    congr 1
    simp only [hΩinv, Matrix.neg_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul,
      smul_dotProduct, dotProduct_neg, dotProduct_add, smul_eq_mul]
    first | (field_simp; ring) | field_simp | ring
  refine ⟨_root_.GlobalTheory.siegelGaussIntegral Ω, ?_, fun a ζ => ?_⟩
  · have h := hΩ.siegelGaussIntegral_sq_mul_det
    rw [hΩdef, smul_smul, Matrix.det_smul] at h
    rw [show ((-I) * (R : ℂ) ^ 2) = -I * ((R ^ 2 : ℕ) : ℂ) by push_cast; ring]
    exact h
  have hS1 := hΩ.summable_norm_riemannThetaTerm (fun i => (a i : ℝ) / R) 0 ((R : ℂ) • ζ)
  have hS2 := hΩ.neg_inv.summable_norm_riemannThetaTerm 0 (fun i => (a i : ℝ) / R)
    (Ω⁻¹ *ᵥ ((R : ℂ) • ζ))
  refine ⟨?_, ?_, ?_⟩
  · exact hS1.congr fun m => by rw [T1]
  · refine hS2.congr fun m => ?_
    rw [← T2, norm_mul, _root_.GlobalTheory.SW.FourierJ.norm_ech, one_mul]
  · have e1 : ∑' m : ι → ℤ, _root_.GlobalTheory.SW.FourierJ.gs τ ζ (a + (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zv m) =
        _root_.GlobalTheory.riemannTheta (fun i => (a i : ℝ) / R) 0 Ω ((R : ℂ) • ζ) := by
      rw [_root_.GlobalTheory.riemannTheta_def]
      exact tsum_congr fun m => T1 a ζ m
    have e2 : ∑' m : ι → ℤ, _root_.GlobalTheory.SW.FourierJ.ech (a ⬝ᵥ ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m)) *
        _root_.GlobalTheory.SW.FourierJ.gs (-τ⁻¹) (ζ ᵥ* τ⁻¹) ((R : ℚ)⁻¹ • _root_.GlobalTheory.SW.FourierJ.zv m) =
        _root_.GlobalTheory.riemannTheta 0 (fun i => (a i : ℝ) / R) (-Ω⁻¹) (Ω⁻¹ *ᵥ ((R : ℂ) • ζ)) := by
      rw [_root_.GlobalTheory.riemannTheta_def]
      exact tsum_congr fun m => T2 a ζ m
    have hw : (R : ℂ) • ζ ⬝ᵥ Ω⁻¹ *ᵥ ((R : ℂ) • ζ) = ζ ⬝ᵥ τ⁻¹ *ᵥ ζ := by
      rw [hΩinv]
      simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
        smul_eq_mul]
      first | (field_simp; ring) | field_simp
    rw [e1, e2, hΩ.riemannTheta_eq_neg_inv, hw]
    have hexp : cexp (π * I * (ζ ⬝ᵥ τ⁻¹ *ᵥ ζ)) * cexp (-(π * I) * (ζ ⬝ᵥ τ⁻¹ *ᵥ ζ)) = 1 := by
      rw [← Complex.exp_add, ← Complex.exp_zero]
      congr 1
      ring
    linear_combination (_root_.GlobalTheory.siegelGaussIntegral Ω *
      _root_.GlobalTheory.riemannTheta 0 (fun i => (a i : ℝ) / R) (-Ω⁻¹) (Ω⁻¹ *ᵥ ((R : ℂ) • ζ))) * hexp

end GlobalTheory.SW.FourierJ.Row
