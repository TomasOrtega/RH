import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPart
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousQuaternaryQuadraticForm
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.EqAmOfBarEq

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

variable {E : Type} [Field E] [NumberField E] (D : Dat ℚ E)

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem barW_coe (z : (A E)ˣ) : ((Units.map (D.bar : A E →* A E) z : (A E)ˣ) : A E) = D.bar z := rfl

/- English proof (translation)
Rewrite using `[← barW_coe, Units.mul_inv]`.
-/
private theorem bar_mul_barInv (z : (A E)ˣ) :
    D.bar (z : A E) * (((Units.map (D.bar : A E →* A E) z)⁻¹ : (A E)ˣ) : A E) = 1 := by
  rw [← barW_coe, Units.mul_inv]

/- English proof (translation)
Simplify using `only [sZ, Units.val_mul, aE_val, dM_val]`. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]`.
-/
private theorem sZ_val (z : (A E)ˣ) :
    (sZ D z).val = !![(z : A E), 0; 0, (((Units.map (D.bar : A E →* A E) z)⁻¹ : (A E)ˣ) : A E)] := by
  simp only [sZ, Units.val_mul, aE_val, dM_val]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem em_val (h : GL (Fin 2) (A ℚ)) (i j : Fin 2) : (em E h).val i j = am E (h.val i j) := rfl

/- English proof (translation)
Rewrite using `[← D.am_ideleNorm z, ← map_mul, Units.mul_inv, map_one]`.
-/
private theorem am_norm_mul (z : (A E)ˣ) :
    (z : A E) * D.bar z * am E (((ideleNorm ℚ E z)⁻¹ : (A ℚ)ˣ) : A ℚ) = 1 := by
  rw [← D.am_ideleNorm z, ← map_mul, Units.mul_inv, map_one]

/- English proof (translation)
Establish `h2` using `am_norm_mul D z`. Establish `h3` using `bar_mul_barInv D z`. Take the linear combination `((z : A E) * am E (((ideleNorm ℚ E z)⁻¹ : (A ℚ)ˣ) : A ℚ)) * h3 - (((Units.map (D.bar : A E →* A E) z)⁻¹ : (A E)ˣ) : A E) * h2`.
-/
private theorem barInv_eq (z : (A E)ˣ) :
    (((Units.map (D.bar : A E →* A E) z)⁻¹ : (A E)ˣ) : A E) = am E (((ideleNorm ℚ E z)⁻¹ : (A ℚ)ˣ) : A ℚ) * z := by
  have h2 := am_norm_mul D z
  have h3 := bar_mul_barInv D z
  linear_combination ((z : A E) * am E (((ideleNorm ℚ E z)⁻¹ : (A ℚ)ˣ) : A ℚ)) * h3 - (((Units.map (D.bar : A E →* A E) z)⁻¹ : (A E)ˣ) : A E) * h2

/- English proof (translation)
Simplify using `only [sZ, map_mul, mul_inv, aE_mul, dM_mul]`. Rewrite using `[mul_assoc, mul_assoc, ← mul_assoc (dM _) (aE z'), dM_mul_aE, ← mul_assoc (aE z')]`.
-/
private theorem sZ_mul (z z' : (A E)ˣ) : sZ D (z * z') = sZ D z * sZ D z' := by
  simp only [sZ, map_mul, mul_inv, aE_mul, dM_mul]
  rw [mul_assoc, mul_assoc, ← mul_assoc (dM _) (aE z'), dM_mul_aE, ← mul_assoc (aE z')]

/- English proof (translation)
Establish `h : Continuous (Units.map (D.bar : A E →* A E))` using `Continuous.units_map _ D.continuous_bar`. Conclude with `continuous_aE.mul (continuous_dM.comp h.inv)`.
-/
private theorem sZ_cont : Continuous (sZ D) := by
  have h : Continuous (Units.map (D.bar : A E →* A E)) := Continuous.units_map _ D.continuous_bar
  exact continuous_aE.mul (continuous_dM.comp h.inv)

/- English proof (translation)
Establish `h : ideleNorm ℚ E (Units.map (D.bar : A E →* A E) z) = ideleNorm ℚ E z` using `D.ideleNorm_barU z`. Rewrite using `[sZ, nu_mul, nu_aE, nu_dM, map_inv, h, mul_inv_cancel]`.
-/
private theorem nu_sZ (z : (A E)ˣ) : nu ℚ (sZ D z) = 1 := by
  have h : ideleNorm ℚ E (Units.map (D.bar : A E →* A E) z) = ideleNorm ℚ E z := D.ideleNorm_barU z
  rw [sZ, nu_mul, nu_aE, nu_dM, map_inv, h, mul_inv_cancel]

/- English proof (translation)
Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [Dat.herm, Dat.mkE_def, X0, rp]`.
-/
private theorem hermitian_standardVector : D.herm (rp X0) = !![0, rt D.θ; -rt D.θ, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Dat.herm, Dat.mkE_def, X0, rp]

/- English proof (translation)
Apply `D.herm_injective` to reduce the goal to its premises. Rewrite using `[D.herm_act, hermitian_standardVector, h1]`.
-/
private theorem action_fixes_standardVector {h : GL (Fin 2) (A E)}
    (h1 : h.val * !![0, rt D.θ; -rt D.θ, 0] * D.star2 h.val = !![0, rt D.θ; -rt D.θ, 0]) :
    D.act h (rp X0) = rp X0 := by
  apply D.herm_injective
  rw [D.herm_act, hermitian_standardVector, h1]

/- English proof (translation)
Apply `action_fixes_standardVector` to reduce the goal to its premises. Establish `h3 : (z : A E) * ((z⁻¹ : (A E)ˣ) : A E) = 1` using `Units.mul_inv z`. Establish `h4 : D.bar ((z⁻¹ : (A E)ˣ) : A E) * D.bar (z : A E) = 1`. Rewrite using `[← map_mul, Units.inv_mul, map_one]`. Rewrite using `[sZ_val]`.

Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;>`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two, Dat.conjTransposeGal_apply]`. Take the linear combination `(rt D.θ) * h3`. Take the linear combination `(rt D.θ) * h4`.
-/
private theorem act_sZ (z : (A E)ˣ) : D.act (sZ D z) (rp X0) = rp X0 := by
  apply action_fixes_standardVector
  have h3 : (z : A E) * ((z⁻¹ : (A E)ˣ) : A E) = 1 := Units.mul_inv z
  have h4 : D.bar ((z⁻¹ : (A E)ˣ) : A E) * D.bar (z : A E) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  rw [sZ_val]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Dat.conjTransposeGal_apply]
  · linear_combination (rt D.θ) * h3
  · linear_combination (rt D.θ) * h4

/- English proof (translation)
Apply `action_fixes_standardVector` to reduce the goal to its premises. Establish `hd : am E (g 0 0) * am E (g 1 1) - am E (g 0 1) * am E (g 1 0) = 1`. Rewrite using `[← map_mul, ← map_mul, ← map_sub, specialLinear_det_entries, map_one]`. Establish `e : (em E (gl g)).val = !![am E (g 0 0), am E (g 0 1); am E (g 1 0), am E (g 1 1)]`. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> rfl`.

Rewrite using `[e]`. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;>`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two, Dat.conjTransposeGal_apply, D.bar_am]`. Expand and normalize the polynomial expressions, which then agree. Take the linear combination `(rt D.θ) * hd`.

Take the linear combination `(-rt D.θ) * hd`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem act_em (g : G1 ℚ) : D.act (em E (gl g)) (rp X0) = rp X0 := by
  apply action_fixes_standardVector
  have hd : am E (g 0 0) * am E (g 1 1) - am E (g 0 1) * am E (g 1 0) = 1 := by
    rw [← map_mul, ← map_mul, ← map_sub, specialLinear_det_entries, map_one]
  have e : (em E (gl g)).val = !![am E (g 0 0), am E (g 0 1); am E (g 1 0), am E (g 1 1)] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  rw [e]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Dat.conjTransposeGal_apply, D.bar_am]
  · ring
  · linear_combination (rt D.θ) * hd
  · linear_combination (-rt D.θ) * hd
  · ring

/- English proof (translation)
Take `⟨γ₁, h₁⟩` from `exists_ratGL_aE (F := E) e`. Take `⟨γ₂, h₂⟩` from `exists_ratGL_dM (F := E) (Units.map (D.σ : E →* E) e)⁻¹`. Use `⟨γ₁ * γ₂, ?_⟩` and prove the remaining obligations. Establish `h : (Units.map (D.bar : A E →* A E) (IdeleGroup.diagonal E e))⁻¹ = IdeleGroup.diagonal E (Units.map (D.σ : E →* E) e)⁻¹`. Rewrite using `[map_inv]`.

Use `congr 1`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[barW_coe, coe_diagonal, coe_diagonal, D.bar_rt]`. Both sides reduce to the same expression. Rewrite using `[sZ, h, map_mul, h₁, h₂]`.
-/
private theorem sZ_diag (e : Eˣ) : ∃ γ, sZ D (IdeleGroup.diagonal E e) = ratGL E 2 γ := by
  obtain ⟨γ₁, h₁⟩ := exists_ratGL_aE (F := E) e
  obtain ⟨γ₂, h₂⟩ := exists_ratGL_dM (F := E) (Units.map (D.σ : E →* E) e)⁻¹
  refine ⟨γ₁ * γ₂, ?_⟩
  have h : (Units.map (D.bar : A E →* A E) (IdeleGroup.diagonal E e))⁻¹ =
      IdeleGroup.diagonal E (Units.map (D.σ : E →* E) e)⁻¹ := by
    rw [map_inv]
    congr 1
    apply Units.ext
    rw [barW_coe, coe_diagonal, coe_diagonal, D.bar_rt]
    rfl
  rw [sZ, h, map_mul, h₁, h₂]

/- English proof (translation)
Establish `hn` using `am_norm_mul D z`. Establish `hb` using `barInv_eq D z`. Establish `hN` using `D.am_ideleNorm z`. Establish `hc : ∀ i j, (em E (gl (cD (ideleNorm ℚ E z)⁻¹ g))).val i j = am E ((cD (ideleNorm ℚ E z)⁻¹ g).1 i j)` using `fun _ _ => rfl`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[Units.val_mul, Units.val_mul, sZ_val, hb]`. Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Fin.sum_univ_two, hc, em_val, gl_val, cD_val]`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [inv_inv, map_mul, hN]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `hN` using `[GroundTheory.Global.coe_ideleNorm]`. Rewrite using `[hN]`. Take the linear combination `(-(am E (g 0 1)) * (z : A E)) * hn`. Expand and normalize the polynomial expressions, which then agree. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem sZ_conj (z : (A E)ˣ) (g : G1 ℚ) :
    sZ D z * em E (gl g) = em E (gl (cD (ideleNorm ℚ E z)⁻¹ g)) * sZ D z := by
  have hn := am_norm_mul D z
  have hb := barInv_eq D z
  have hN := D.am_ideleNorm z
  have hc : ∀ i j, (em E (gl (cD (ideleNorm ℚ E z)⁻¹ g))).val i j = am E ((cD (ideleNorm ℚ E z)⁻¹ g).1 i j) := fun _ _ => rfl
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, sZ_val, hb]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hc, em_val, gl_val, cD_val]
  fin_cases i <;> fin_cases j <;> simp [inv_inv, map_mul, hN]
  · ring
  · rw [GroundTheory.Global.coe_ideleNorm] at hN
    rw [hN]
    linear_combination (-(am E (g 0 1)) * (z : A E)) * hn
  · ring
  · ring

/- English proof (translation)
Establish `hb` using `barInv_eq D z`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, sZ_val, hb]`. Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Fin.sum_univ_two, em_val, dM_val]`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem sZ_scalar (z : (A E)ˣ) :
    sZ D z = Matrix.GeneralLinearGroup.scalar (Fin 2) z * em E (dM (ideleNorm ℚ E z)⁻¹) := by
  have hb := barInv_eq D z
  apply Units.ext
  rw [Units.val_mul, sZ_val, hb]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, em_val, dM_val]
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar]
  · ring

/- English proof (translation)
Simplify using `[q4, qr, rp, map_sub, map_mul, map_pow]`.
-/
private theorem quadraticForm_rational_points (δ : ℚ) (ξ : Fin 4 → ℚ) : q4 δ (rp ξ) = rt (qr δ ξ) := by
  simp [q4, qr, rp, map_sub, map_mul, map_pow]

end UpperTheory.ConvolutionTheory.RankTwoDescent

/- English proof (translation)
Introduce `E _ _ _ D`. Use `⟨sZ_mul D, sZ_cont D, nu_sZ D, nu_gl, act_sZ D, act_em D, sZ_diag D, sZ_conj D, sZ_scalar D, ?_, quadraticForm_rational_points D.δ⟩` and prove the remaining obligations. Introduce `x hx v`. Rewrite using `[D.quadForm_act, hx]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.szLaws :
    SzLaws := by
  intro E _ _ _ D
  refine ⟨sZ_mul D, sZ_cont D, nu_sZ D, nu_gl, act_sZ D, act_em D, sZ_diag D, sZ_conj D, sZ_scalar D, ?_, quadraticForm_rational_points D.δ⟩
  intro x hx v
  rw [D.quadForm_act, hx]
  simp
