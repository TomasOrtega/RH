import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmR
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RWConstMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralCompUnitMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilCentralCharacterHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NontrivialGaloisPlaceDegreeTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentIdealRat
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.CenTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.CenThetaNs

section Local

open Matrix Ad3.K.GL2LocalData

/- English proof (translation)
Introduce `F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hfr hcont σ hσ η hη c Φ hΦ g t x ht`. Establish `h : ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det` using `⟨t, ht⟩`. Establish `h0 : Algebra.norm F (h.choose : E) = (g.val).det` using `h.choose_spec`. Establish `hne : Algebra.norm F (h.choose : E) ≠ 0` using `(h.choose.isUnit.map (Algebra.norm F : E →* F)).ne_zero`. Take `⟨u, hu⟩ : ∃ u : Eˣ, t = h.choose * u` from `⟨h.choose⁻¹ * t, by group⟩`.

Establish `hN : Algebra.norm F (u : E) = 1`. Establish `e : Algebra.norm F (h.choose : E) * Algebra.norm F (u : E) = Algebra.norm F (h.choose : E) * 1`. Rewrite using `[← map_mul, ← Units.val_mul, ← hu, ht, h0, mul_one]`. Conclude with `mul_left_cancel₀ hne e`. Establish `hfun : (fun y => Φ (y * (t : E))) = fun y => (((c u)⁻¹ : ℂˣ) : ℂ) * Φ (y * (h.choose : E))`.

Use function extensionality and compare the values at `y`. Rewrite using `[hu, Units.val_mul, ← mul_assoc]`. Conclude with `hΦ.2.2 u hN _`. Establish `hcu : ((c u : ℂˣ) : ℂ) * (((c u)⁻¹ : ℂˣ) : ℂ) = 1`. Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`.

Use `show piG χ σ (muE E χ) (lamE E χ η) c g Φ x = _`. Rewrite using `[piG, dif_pos h, hfun, GlobalTheory.CompanionTheory.WeilChoice.rW_const_mul, hu, map_mul, Units.val_mul]`. Take the linear combination `(-(((c h.choose : ℂˣ) : ℂ) * (((modulus (g.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ)) * rW χ σ (muE E χ) (lamE E χ η) (g.val 0 0 / (g.val).det) (g.val 0 1) (g.val 1 0 / (g.val).det) (g.val 1 1) (fun x => Φ (x * (h.choose : E))) x)) * hcu`.
-/
theorem piG_choice : ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η =>
    ∀ (c : Eˣ →* ℂˣ), ∀ Φ ∈ SBc F E c, ∀ (g : GL (Fin 2) F) (t : Eˣ) (x : E),
      Algebra.norm F (t : E) = (g.val).det →
      piE E χ σ η c g Φ x = ((c t : ℂˣ) : ℂ) * (((modulus (g.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ)) *
        rW χ σ (muE E χ) (lamE E χ η) (g.val 0 0 / (g.val).det) (g.val 0 1)
          (g.val 1 0 / (g.val).det) (g.val 1 1) (fun y => Φ (y * (t : E))) x := by
  intro F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hfr hcont σ hσ η hη c Φ hΦ g t x ht
  have h : ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det := ⟨t, ht⟩
  have h0 : Algebra.norm F (h.choose : E) = (g.val).det := h.choose_spec
  have hne : Algebra.norm F (h.choose : E) ≠ 0 :=
    (h.choose.isUnit.map (Algebra.norm F : E →* F)).ne_zero
  obtain ⟨u, hu⟩ : ∃ u : Eˣ, t = h.choose * u := ⟨h.choose⁻¹ * t, by group⟩
  have hN : Algebra.norm F (u : E) = 1 := by
    have e : Algebra.norm F (h.choose : E) * Algebra.norm F (u : E) =
        Algebra.norm F (h.choose : E) * 1 := by
      rw [← map_mul, ← Units.val_mul, ← hu, ht, h0, mul_one]
    exact mul_left_cancel₀ hne e
  have hfun : (fun y => Φ (y * (t : E))) =
      fun y => (((c u)⁻¹ : ℂˣ) : ℂ) * Φ (y * (h.choose : E)) := by
    funext y
    rw [hu, Units.val_mul, ← mul_assoc]
    exact hΦ.2.2 u hN _
  have hcu : ((c u : ℂˣ) : ℂ) * (((c u)⁻¹ : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  show piG χ σ (muE E χ) (lamE E χ η) c g Φ x = _
  rw [piG, dif_pos h, hfun, GlobalTheory.CompanionTheory.WeilChoice.rW_const_mul, hu, map_mul, Units.val_mul]
  linear_combination (-(((c h.choose : ℂˣ) : ℂ) * (((modulus (g.val).det : ℝ) : ℂ) ^ (1 / 2 : ℂ)) *
      rW χ σ (muE E χ) (lamE E χ η) (g.val 0 0 / (g.val).det) (g.val 0 1)
        (g.val 1 0 / (g.val).det) (g.val 1 1) (fun x => Φ (x * (h.choose : E))) x)) * hcu

/- English proof (translation)
Introduce `F _ _ _ _ _ _ _ χ hχc hχ E _ _ _ _ _ _ _ hd hc σ hσ η hη c Φ hΦ a g x`. Use `set ae : Eˣ := Units.map (algebraMap F E).toMonoidHom a with hae`. Establish `hav : (ae : E) = algebraMap F E (a : F)` using `rfl`. Establish `hNa : Algebra.norm F (ae : E) = (a : F) ^ 2`. Rewrite using `[hav, Algebra.norm_algebraMap, hd]`.

Establish `ha0 : (a : F) ≠ 0` using `a.ne_zero`. Establish `hdet : ((dg2 a a * g).val).det = (a : F) ^ 2 * (g.val).det` using `by show ((dg2 a a).val * g.val).det = _`. Rewrite using `[Matrix.det_mul]`. Use `congr 1`. Simplify using `[dg2, Matrix.det_fin_two]`.

Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `h : ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det`. Use `swap`. Establish `h' : ¬ ∃ t : Eˣ, Algebra.norm F (t : E) = ((dg2 a a * g).val).det`. Introduce and unpack `⟨t, ht⟩`.

Use `h ⟨ae⁻¹ * t, ?_⟩` and prove the remaining obligations. Establish `e : (a : F) ^ 2 * Algebra.norm F ((ae⁻¹ * t : Eˣ) : E) = (a : F) ^ 2 * (g.val).det`. Rewrite using `[← hNa, ← map_mul, ← Units.val_mul, mul_inv_cancel_left, ht, hdet, hNa]`. Conclude with `mul_left_cancel₀ (pow_ne_zero 2 ha0) e`. Use `show piG _ _ _ _ _ _ _ _ = _ * piG _ _ _ _ _ _ _ _`.

Rewrite using `[piG, piG, dif_neg h, dif_neg h', mul_zero]`. Take `⟨t, ht⟩` from `h`. Establish `hN' : Algebra.norm F ((ae * t : Eˣ) : E) = ((dg2 a a * g).val).det`. Rewrite using `[Units.val_mul, map_mul, hNa, ht, hdet]`. Establish `L` using `piG_choice F χ hχc hχ E hd hc σ hσ η hη c Φ hΦ (dg2 a a * g) (ae * t) x hN'`.

Establish `R` using `piG_choice F χ hχc hχ E hd hc σ hσ η hη c Φ hΦ g t x ht`. Rewrite using `[L, R]`. Establish `hD : (g.val).det ≠ 0`. Rewrite using `[← ht]`. Conclude with `(t.isUnit.map (Algebra.norm F : E →* F)).ne_zero`.

Establish `e00 : (dg2 a a * g).val 0 0 = (a : F) * g.val 0 0` using `by show ((dg2 a a).val * g.val) 0 0 = _`. Simplify using `[dg2, Matrix.mul_apply, Fin.sum_univ_two]`. Establish `e01 : (dg2 a a * g).val 0 1 = (a : F) * g.val 0 1` using `by show ((dg2 a a).val * g.val) 0 1 = _`. Simplify using `[dg2, Matrix.mul_apply, Fin.sum_univ_two]`. Establish `e10 : (dg2 a a * g).val 1 0 = (a : F) * g.val 1 0` using `by show ((dg2 a a).val * g.val) 1 0 = _`.

Simplify using `[dg2, Matrix.mul_apply, Fin.sum_univ_two]`. Establish `e11 : (dg2 a a * g).val 1 1 = (a : F) * g.val 1 1` using `by show ((dg2 a a).val * g.val) 1 1 = _`. Simplify using `[dg2, Matrix.mul_apply, Fin.sum_univ_two]`. Rewrite using `[e00, e01, e10, e11, hdet]`. Use `set D : F := (g.val).det with hDdef`.

Use `set g1 : Matrix (Fin 2) (Fin 2) F := !![g.val 0 0 / D, g.val 0 1; g.val 1 0 / D, g.val 1 1] with hg1def`. Establish `hg1 : g1.det = 1`. Establish `: D = g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0`. Rewrite using `[hDdef, Matrix.det_fin_two]`. Rewrite using `[hg1def, Matrix.det_fin_two_of]`.

Clear the denominators using the available nonvanishing facts. Conclude with `this.symm`. Establish `hΨ : (fun y => Φ (y * ((ae * t : Eˣ) : E))) ∈ SBE E`. Use `⟨hΦ.1.comp_continuous (continuous_id.mul continuous_const), ?_⟩` and prove the remaining obligations. Conclude with `hΦ.2.1.comp_homeomorph (Homeomorph.mulRight₀ (((ae * t : Eˣ) : E)) (Units.ne_zero _))`.

Establish `hrep` using `congrFun (GlobalTheory.CompanionTheory.WeilTorus.wRepM F χ hχc hχ E hd hc σ hσ η hη g1 hg1 a⁻¹ (fun y => Φ (y * ((ae * t : Eˣ) : E))) hΨ) x`. Establish `hm : rWE E χ σ η !![((a⁻¹ : Fˣ) : F), 0; 0, (((a⁻¹)⁻¹ : Fˣ) : F)] (fun y => Φ (y * ((ae * t : Eˣ) : E))) = fun u => (nsg E ((a⁻¹ : Fˣ) : F) * ((modulus ((a⁻¹ : Fˣ) : F) : ℝ) : ℂ)) * Φ (u * (t : E))`. Use function extensionality and compare the values at `u`. Establish `e : algebraMap F E ((a⁻¹ : Fˣ) : F) * u * ((ae * t : Eˣ) : E) = u * (t : E)`. Establish `e1 : algebraMap F E ((a⁻¹ : Fˣ) : F) * (ae : E) = 1`.

Rewrite using `[hav, ← map_mul, Units.val_inv_eq_inv_val, inv_mul_cancel₀ ha0, map_one]`. Rewrite using `[Units.val_mul]`. Combine the equalities or inequalities in the displayed calculation. Use `show rW χ σ (muE E χ) (lamE E χ η) ((a⁻¹ : Fˣ) : F) 0 0 (((a⁻¹)⁻¹ : Fˣ) : F) (fun y => Φ (y * ((ae * t : Eˣ) : E))) u = _`. Rewrite using `[rW, if_pos rfl, mul_zero, zero_mul, AddChar.map_zero_eq_one]`.

Simplify using `only [Circle.coe_one, one_mul, e]`. Use `set k : ℂ := nsg E ((a⁻¹ : Fˣ) : F) * ((modulus ((a⁻¹ : Fˣ) : F) : ℝ) : ℂ) with hkdef`. Establish `hr : rWE E χ σ η g1 (fun u => k * Φ (u * (t : E))) x = k * rW χ σ (muE E χ) (lamE E χ η) (g.val 0 0 / D) (g.val 0 1) (g.val 1 0 / D) (g.val 1 1) (fun y => Φ (y * (t : E))) x` using `GlobalTheory.CompanionTheory.WeilChoice.rW_const_mul χ σ (muE E χ) (lamE E χ η) _ _ _ _ k (fun y => Φ (y * (t : E))) x`. Establish `hl : rWE E χ σ η (g1 * !![((a⁻¹ : Fˣ) : F), 0; 0, (((a⁻¹)⁻¹ : Fˣ) : F)]) (fun y => Φ (y * ((ae * t : Eˣ) : E))) x = rW χ σ (muE E χ) (lamE E χ η) ((a : F) * g.val 0 0 / ((a : F) ^ 2 * D)) ((a : F) * g.val 0 1) ((a : F) * g.val 1 0 / ((a : F) ^ 2 * D)) ((a : F) * g.val 1 1) (fun y …`. Establish `f00 : (g1 * !![((a⁻¹ : Fˣ) : F), 0; 0, (((a⁻¹)⁻¹ : Fˣ) : F)]) 0 0 = (a : F) * g.val 0 0 / ((a : F) ^ 2 * D)`.

Simplify using `[hg1def, Matrix.mul_apply, Fin.sum_univ_two]`. Clear the denominators using the available nonvanishing facts. Establish `f01 : (g1 * !![((a⁻¹ : Fˣ) : F), 0; 0, (((a⁻¹)⁻¹ : Fˣ) : F)]) 0 1 = (a : F) * g.val 0 1`. Simplify using `[hg1def, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]`. Establish `f10 : (g1 * !![((a⁻¹ : Fˣ) : F), 0; 0, (((a⁻¹)⁻¹ : Fˣ) : F)]) 1 0 = (a : F) * g.val 1 0 / ((a : F) ^ 2 * D)`.

Simplify using `[hg1def, Matrix.mul_apply, Fin.sum_univ_two]`. Clear the denominators using the available nonvanishing facts. Establish `f11 : (g1 * !![((a⁻¹ : Fˣ) : F), 0; 0, (((a⁻¹)⁻¹ : Fˣ) : F)]) 1 1 = (a : F) * g.val 1 1`. Simplify using `[hg1def, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]`. Simplify using `only [rWm]`.

Rewrite using `[f00, f01, f10, f11]`. Rewrite `hrep` using `[hm, hl, hr]`. Rewrite using `[hrep]`. Establish `hmpos : 0 < (modulus (a : F) : ℝ)`. Conclude with `GroundTheory.LocalField.modulus_pos ha0` after adjusting the coercions.

Establish `hmod : (((modulus ((a : F) ^ 2 * D) : ℝ)) : ℂ) ^ (1 / 2 : ℂ) = ((modulus (a : F) : ℝ) : ℂ) * (((modulus D : ℝ) : ℂ) ^ (1 / 2 : ℂ))`. Establish `e : (modulus ((a : F) ^ 2 * D) : ℝ) = (modulus (a : F) : ℝ) ^ 2 * (modulus D : ℝ)`. Rewrite using `[modulus_mul, GlobalTheory.CompanionTheory.NormModulus.modulus_pow_nat]`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite using `[e]`. Conclude with `GlobalTheory.CompanionTheory.WeilCentral.cpow_half_sq_mul _ _ hmpos (NNReal.coe_nonneg _)`. Establish `hinv : nsg E ((a⁻¹ : Fˣ) : F) = ((η a : ℂˣ) : ℂ)`. Establish `h1 : ((η a : ℂˣ) : ℂ) * ((η a : ℂˣ) : ℂ) = 1`. Rewrite using `[hη]`.

Unfold `nsg`. Apply the tactic sequence `split_ifs <;> norm_num`. Establish `h2 : ((η a⁻¹ : ℂˣ) : ℂ) * ((η a : ℂˣ) : ℂ) = 1`. Rewrite using `[← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]`. Rewrite using `[← hη a⁻¹]`.

Conclude with `mul_right_cancel₀ (Units.ne_zero (η a)) (h2.trans h1.symm)`. Establish `hminv : ((modulus ((a⁻¹ : Fˣ) : F) : ℝ) : ℂ) = ((modulus (a : F) : ℝ) : ℂ)⁻¹`. Rewrite using `[Units.val_inv_eq_inv_val, GroundTheory.LocalField.modulus_inv]`. Use `push_cast`. Both sides reduce to the same expression.

Establish `hcen : (((resF (F` using `F) c * η) a : ℂˣ) : ℂ) = ((c ae : ℂˣ) : ℂ) * ((η a : ℂˣ) : ℂ) := by`. Rewrite using `[MonoidHom.mul_apply, Units.val_mul]`. Both sides reduce to the same expression. Establish `hm1 : ((modulus (a : F) : ℝ) : ℂ) * ((modulus (a : F) : ℝ) : ℂ)⁻¹ = 1` using `mul_inv_cancel₀ (by exact_mod_cast hmpos.ne')`. Rewrite using `[hmod, hkdef, hinv, hminv, hcen, map_mul, Units.val_mul]`.

Generalize the expression as in `rW χ σ (muE E χ) (lamE E χ η) (g.val 0 0 / D) (g.val 0 1) (g.val 1 0 / D) (g.val 1 1) (fun y => Φ (y * (t : E))) x = X`. Take the linear combination `(((c ae : ℂˣ) : ℂ) * ((c t : ℂˣ) : ℂ) * (((modulus D : ℝ) : ℂ) ^ (1 / 2 : ℂ)) * ((η a : ℂˣ) : ℂ) * X) * hm1`.
-/
theorem piG_cen : ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η =>
    ∀ (c : Eˣ →* ℂˣ), ∀ Φ ∈ SBc F E c, ∀ (a : Fˣ) (g : GL (Fin 2) F) (x : E),
      piE E χ σ η c (dg2 a a * g) Φ x =
        (((resF (F := F) c * η) a : ℂˣ) : ℂ) * piE E χ σ η c g Φ x := by
  intro F _ _ _ _ _ _ _ χ hχc hχ E _ _ _ _ _ _ _ hd hc σ hσ η hη c Φ hΦ a g x
  set ae : Eˣ := Units.map (algebraMap F E).toMonoidHom a with hae
  have hav : (ae : E) = algebraMap F E (a : F) := rfl
  have hNa : Algebra.norm F (ae : E) = (a : F) ^ 2 := by
    rw [hav, Algebra.norm_algebraMap, hd]
  have ha0 : (a : F) ≠ 0 := a.ne_zero
  have hdet : ((dg2 a a * g).val).det = (a : F) ^ 2 * (g.val).det := by
    show ((dg2 a a).val * g.val).det = _
    rw [Matrix.det_mul]
    congr 1
    simp [dg2, Matrix.det_fin_two]
    ring
  by_cases h : ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det
  swap
  · have h' : ¬ ∃ t : Eˣ, Algebra.norm F (t : E) = ((dg2 a a * g).val).det := by
      rintro ⟨t, ht⟩
      refine h ⟨ae⁻¹ * t, ?_⟩
      have e : (a : F) ^ 2 * Algebra.norm F ((ae⁻¹ * t : Eˣ) : E) = (a : F) ^ 2 * (g.val).det := by
        rw [← hNa, ← map_mul, ← Units.val_mul, mul_inv_cancel_left, ht, hdet, hNa]
      exact mul_left_cancel₀ (pow_ne_zero 2 ha0) e
    show piG _ _ _ _ _ _ _ _ = _ * piG _ _ _ _ _ _ _ _
    rw [piG, piG, dif_neg h, dif_neg h', mul_zero]
  obtain ⟨t, ht⟩ := h
  have hN' : Algebra.norm F ((ae * t : Eˣ) : E) = ((dg2 a a * g).val).det := by
    rw [Units.val_mul, map_mul, hNa, ht, hdet]
  have L := piG_choice F χ hχc hχ E hd hc σ hσ η hη c Φ hΦ (dg2 a a * g) (ae * t) x hN'
  have R := piG_choice F χ hχc hχ E hd hc σ hσ η hη c Φ hΦ g t x ht
  rw [L, R]
  have hD : (g.val).det ≠ 0 := by
    rw [← ht]
    exact (t.isUnit.map (Algebra.norm F : E →* F)).ne_zero
  have e00 : (dg2 a a * g).val 0 0 = (a : F) * g.val 0 0 := by
    show ((dg2 a a).val * g.val) 0 0 = _
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (dg2 a a * g).val 0 1 = (a : F) * g.val 0 1 := by
    show ((dg2 a a).val * g.val) 0 1 = _
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (dg2 a a * g).val 1 0 = (a : F) * g.val 1 0 := by
    show ((dg2 a a).val * g.val) 1 0 = _
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (dg2 a a * g).val 1 1 = (a : F) * g.val 1 1 := by
    show ((dg2 a a).val * g.val) 1 1 = _
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
  rw [e00, e01, e10, e11, hdet]
  set D : F := (g.val).det with hDdef
  set g1 : Matrix (Fin 2) (Fin 2) F := !![g.val 0 0 / D, g.val 0 1; g.val 1 0 / D, g.val 1 1] with hg1def
  have hg1 : g1.det = 1 := by
    have : D = g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0 := by
      rw [hDdef, Matrix.det_fin_two]
    rw [hg1def, Matrix.det_fin_two_of]
    field_simp
    exact this.symm
  have hΨ : (fun y => Φ (y * ((ae * t : Eˣ) : E))) ∈ SBE E := by
    refine ⟨hΦ.1.comp_continuous (continuous_id.mul continuous_const), ?_⟩
    exact hΦ.2.1.comp_homeomorph (Homeomorph.mulRight₀ (((ae * t : Eˣ) : E)) (Units.ne_zero _))
  have hrep := congrFun (GlobalTheory.CompanionTheory.WeilTorus.wRepM F χ hχc hχ E hd hc σ hσ η hη g1 hg1 a⁻¹
    (fun y => Φ (y * ((ae * t : Eˣ) : E))) hΨ) x
  have hm : rWE E χ σ η !![((a⁻¹ : Fˣ) : F), 0; 0, (((a⁻¹)⁻¹ : Fˣ) : F)]
      (fun y => Φ (y * ((ae * t : Eˣ) : E))) =
      fun u => (nsg E ((a⁻¹ : Fˣ) : F) * ((modulus ((a⁻¹ : Fˣ) : F) : ℝ) : ℂ)) * Φ (u * (t : E)) := by
    funext u
    have e : algebraMap F E ((a⁻¹ : Fˣ) : F) * u * ((ae * t : Eˣ) : E) = u * (t : E) := by
      have e1 : algebraMap F E ((a⁻¹ : Fˣ) : F) * (ae : E) = 1 := by
        rw [hav, ← map_mul, Units.val_inv_eq_inv_val, inv_mul_cancel₀ ha0, map_one]
      rw [Units.val_mul]
      calc _ = (algebraMap F E ((a⁻¹ : Fˣ) : F) * (ae : E)) * (u * (t : E)) := by ring
        _ = _ := by rw [e1, one_mul]
    show rW χ σ (muE E χ) (lamE E χ η) ((a⁻¹ : Fˣ) : F) 0 0 (((a⁻¹)⁻¹ : Fˣ) : F)
      (fun y => Φ (y * ((ae * t : Eˣ) : E))) u = _
    rw [rW, if_pos rfl, mul_zero, zero_mul, AddChar.map_zero_eq_one]
    simp only [Circle.coe_one, one_mul, e]
  set k : ℂ := nsg E ((a⁻¹ : Fˣ) : F) * ((modulus ((a⁻¹ : Fˣ) : F) : ℝ) : ℂ) with hkdef
  have hr : rWE E χ σ η g1 (fun u => k * Φ (u * (t : E))) x =
      k * rW χ σ (muE E χ) (lamE E χ η) (g.val 0 0 / D) (g.val 0 1) (g.val 1 0 / D) (g.val 1 1)
        (fun y => Φ (y * (t : E))) x :=
    GlobalTheory.CompanionTheory.WeilChoice.rW_const_mul χ σ (muE E χ) (lamE E χ η) _ _ _ _ k (fun y => Φ (y * (t : E))) x
  have hl : rWE E χ σ η (g1 * !![((a⁻¹ : Fˣ) : F), 0; 0, (((a⁻¹)⁻¹ : Fˣ) : F)])
      (fun y => Φ (y * ((ae * t : Eˣ) : E))) x =
      rW χ σ (muE E χ) (lamE E χ η) ((a : F) * g.val 0 0 / ((a : F) ^ 2 * D)) ((a : F) * g.val 0 1)
        ((a : F) * g.val 1 0 / ((a : F) ^ 2 * D)) ((a : F) * g.val 1 1)
        (fun y => Φ (y * ((ae * t : Eˣ) : E))) x := by
    have f00 : (g1 * !![((a⁻¹ : Fˣ) : F), 0; 0, (((a⁻¹)⁻¹ : Fˣ) : F)]) 0 0 =
        (a : F) * g.val 0 0 / ((a : F) ^ 2 * D) := by
      simp [hg1def, Matrix.mul_apply, Fin.sum_univ_two]
      field_simp
    have f01 : (g1 * !![((a⁻¹ : Fˣ) : F), 0; 0, (((a⁻¹)⁻¹ : Fˣ) : F)]) 0 1 = (a : F) * g.val 0 1 := by
      simp [hg1def, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
    have f10 : (g1 * !![((a⁻¹ : Fˣ) : F), 0; 0, (((a⁻¹)⁻¹ : Fˣ) : F)]) 1 0 =
        (a : F) * g.val 1 0 / ((a : F) ^ 2 * D) := by
      simp [hg1def, Matrix.mul_apply, Fin.sum_univ_two]
      field_simp
    have f11 : (g1 * !![((a⁻¹ : Fˣ) : F), 0; 0, (((a⁻¹)⁻¹ : Fˣ) : F)]) 1 1 = (a : F) * g.val 1 1 := by
      simp [hg1def, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
    simp only [rWm]
    rw [f00, f01, f10, f11]
  rw [hm, hl, hr] at hrep
  rw [hrep]
  have hmpos : 0 < (modulus (a : F) : ℝ) := by
    exact_mod_cast GroundTheory.LocalField.modulus_pos ha0
  have hmod : (((modulus ((a : F) ^ 2 * D) : ℝ)) : ℂ) ^ (1 / 2 : ℂ) =
      ((modulus (a : F) : ℝ) : ℂ) * (((modulus D : ℝ) : ℂ) ^ (1 / 2 : ℂ)) := by
    have e : (modulus ((a : F) ^ 2 * D) : ℝ) = (modulus (a : F) : ℝ) ^ 2 * (modulus D : ℝ) := by
      rw [modulus_mul, GlobalTheory.CompanionTheory.NormModulus.modulus_pow_nat]
      push_cast
      rfl
    rw [e]
    exact GlobalTheory.CompanionTheory.WeilCentral.cpow_half_sq_mul _ _ hmpos (NNReal.coe_nonneg _)
  have hinv : nsg E ((a⁻¹ : Fˣ) : F) = ((η a : ℂˣ) : ℂ) := by
    have h1 : ((η a : ℂˣ) : ℂ) * ((η a : ℂˣ) : ℂ) = 1 := by
      rw [hη]
      unfold nsg
      split_ifs <;> norm_num
    have h2 : ((η a⁻¹ : ℂˣ) : ℂ) * ((η a : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
    rw [← hη a⁻¹]
    exact mul_right_cancel₀ (Units.ne_zero (η a)) (h2.trans h1.symm)
  have hminv : ((modulus ((a⁻¹ : Fˣ) : F) : ℝ) : ℂ) = ((modulus (a : F) : ℝ) : ℂ)⁻¹ := by
    rw [Units.val_inv_eq_inv_val, GroundTheory.LocalField.modulus_inv]
    push_cast
    rfl
  have hcen : (((resF (F := F) c * η) a : ℂˣ) : ℂ) = ((c ae : ℂˣ) : ℂ) * ((η a : ℂˣ) : ℂ) := by
    rw [MonoidHom.mul_apply, Units.val_mul]
    rfl
  have hm1 : ((modulus (a : F) : ℝ) : ℂ) * ((modulus (a : F) : ℝ) : ℂ)⁻¹ = 1 :=
    mul_inv_cancel₀ (by exact_mod_cast hmpos.ne')
  rw [hmod, hkdef, hinv, hminv, hcen, map_mul, Units.val_mul]
  generalize rW χ σ (muE E χ) (lamE E χ η) (g.val 0 0 / D) (g.val 0 1) (g.val 1 0 / D) (g.val 1 1)
    (fun y => Φ (y * (t : E))) x = X
  linear_combination (((c ae : ℂˣ) : ℂ) * ((c t : ℂˣ) : ℂ) * (((modulus D : ℝ) : ℂ) ^ (1 / 2 : ℂ)) *
    ((η a : ℂˣ) : ℂ) * X) * hm1

end Local

/- English proof (translation)
Introduce `K _ _ h2 c v m hok hsp a g ξ`. Establish `hstd : IsStd (GP.psiF v)` using `GlobalTheory.CompanionTheory.StdCharQ.stdChar v`. Establish `hχc : Continuous ((GP.psiF v)⁻¹ : AddChar (Qv v) Circle)`. Establish `: (((GP.psiF v)⁻¹ : AddChar (Qv v) Circle) : Qv v → Circle) = fun x => (GP.psiF v x)⁻¹`. Use function extensionality and compare the values at `x`.

Conclude with `AddChar.inv_apply' _ _`. Rewrite using `[this]`. Conclude with `hstd.1.inv`. Establish `hχ1 : (GP.psiF v)⁻¹ ≠ 1` using `inv_ne_one.mpr hstd.2.1`. Consider the cases of `m with`.

Consider the case `@sp w₁ w₂ i₁ i₂ Φ => exact absurd trivial hsp`. Consider the case `@ns w i σ η Φ => haveI := i`. Take `⟨-, hσ, hη, hΦ⟩` from `hok`. Conclude with `piG_cen (Qv v) _ hχc hχ1 (Kv K w) (GlobalTheory.CompanionTheory.QuadPlace.finrank_eq_two_of_ne_refl K h2 v w i σ hσ) (continuous_adicCompletionMap v w) σ hσ η hη _ Φ hΦ a g _`.
-/
theorem val_central : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
    ∀ (c : HeckeCharacter K) (v : Pl) (m : LM c v), m.ok → ¬ m.IsSp →
    ∀ (a : (Qv v)ˣ) (g : GL (Fin 2) (Qv v)) (ξ : K), m.val (dg2 a a * g) ξ = omW m a * m.val g ξ := by
  intro K _ _ h2 c v m hok hsp a g ξ
  have hstd : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.StdCharQ.stdChar v
  have hχc : Continuous ((GP.psiF v)⁻¹ : AddChar (Qv v) Circle) := by
    have : (((GP.psiF v)⁻¹ : AddChar (Qv v) Circle) : Qv v → Circle) = fun x => (GP.psiF v x)⁻¹ := by
      funext x; exact AddChar.inv_apply' _ _
    rw [this]
    exact hstd.1.inv
  have hχ1 : (GP.psiF v)⁻¹ ≠ 1 := inv_ne_one.mpr hstd.2.1
  cases m with
  | @sp w₁ w₂ i₁ i₂ Φ => exact absurd trivial hsp
  | @ns w i σ η Φ =>
    haveI := i
    obtain ⟨-, hσ, hη, hΦ⟩ := hok
    exact piG_cen (Qv v) _ hχc hχ1 (Kv K w)
      (GlobalTheory.CompanionTheory.QuadPlace.finrank_eq_two_of_ne_refl K h2 v w i σ hσ)
      (continuous_adicCompletionMap v w) σ hσ η hη _ Φ hΦ a g _

end GlobalTheory.CompanionTheory.CenThetaNs
