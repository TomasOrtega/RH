import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormMulApplyLeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisTransferFactorKrylovDet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisBorderedMatrixNormalFormInvariantsStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.GLCompact

/- English proof (translation)
Establish `hcol : ∀ j : ℕ, ((act g Y).1 ^ j) *ᵥ (act g Y).2.1 = (g : Matrix (Fin r) (Fin r) k) *ᵥ ((Y.1 ^ j) *ᵥ Y.2.1)`. Introduce `j`. Simplify using `only [act]`. Rewrite using `[Units.conj_pow, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]`. Use extensionality with `i j`.

Simplify using `only [Bm, Matrix.of_apply, Matrix.mul_apply, hcol]`. Simplify using `[Matrix.mulVec, dotProduct]`.
-/
theorem Bm_act {k : Type} [CommRing k] {r : ℕ} (g : GL (Fin r) k) (Y : Gl r k) :
    Bm (act g Y) = (g : Matrix (Fin r) (Fin r) k) * Bm Y := by
  have hcol : ∀ j : ℕ, ((act g Y).1 ^ j) *ᵥ (act g Y).2.1 =
      (g : Matrix (Fin r) (Fin r) k) *ᵥ ((Y.1 ^ j) *ᵥ Y.2.1) := by
    intro j
    simp only [act]
    rw [Units.conj_pow, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc,
      Units.inv_mul, Matrix.mul_one]
  ext i j
  simp only [Bm, Matrix.of_apply, Matrix.mul_apply, hcol]
  simp [Matrix.mulVec, dotProduct]

/- English proof (translation)
Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Simplify using `only [Bm, Matrix.of_apply]`. Conclude with `(continuous_apply i).comp ((continuous_fst.pow (j : ℕ)).matrix_mulVec (continuous_fst.comp continuous_snd))`.
-/
theorem continuous_Bm {k : Type} [NormedField k] {r : ℕ} : Continuous (fun Y : Gl r k => Bm Y) := by
  refine continuous_matrix fun i j => ?_
  simp only [Bm, Matrix.of_apply]
  exact (continuous_apply i).comp
    ((continuous_fst.pow (j : ℕ)).matrix_mulVec (continuous_fst.comp continuous_snd))

/- English proof (translation)
Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Simplify using `only [Cm, Matrix.of_apply]`. Conclude with `(continuous_apply j).comp (((continuous_fst.comp (continuous_snd.comp continuous_snd))).matrix_vecMul (continuous_fst.pow (i : ℕ)))`.
-/
theorem continuous_Cm {k : Type} [NormedField k] {r : ℕ} : Continuous (fun Y : Gl r k => Cm Y) := by
  refine continuous_matrix fun i j => ?_
  simp only [Cm, Matrix.of_apply]
  exact (continuous_apply j).comp
    (((continuous_fst.comp (continuous_snd.comp continuous_snd))).matrix_vecMul
      (continuous_fst.pow (i : ℕ)))

end GlobalTheory.JR.GLCompact

/- English proof (translation)
Establish `hv : IsCompact (Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : F) 1)` using `isCompact_univ_pi fun _ => isCompact_closedBall 0 1`. Establish `hm : IsCompact {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ 1}`. Establish `h : {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ 1} = Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : F) 1`. Use extensionality with `A`. Conclude with `⟨fun h i _ j _ => by simpa using h i j, fun h i j => by simpa using h i (Set.mem_univ i) j (Set.mem_univ j)⟩`.

Rewrite using `[h]`. Conclude with `isCompact_univ_pi fun _ => hv`. Establish `h : {Z : Gl n F | (∀ i j, ‖Z.1 i j‖ ≤ 1) ∧ (∀ i, ‖Z.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Z.2.2.1 i‖ ≤ 1) ∧ ‖Z.2.2.2‖ ≤ 1} = {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ 1} ×ˢ ((Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : F) 1) ×ˢ ((Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : …`. Use extensionality with `Z`. Simplify using the standard rewrite rules.

Rewrite using `[h]`. Conclude with `hm.prod (hv.prod (hv.prod (isCompact_closedBall 0 1)))`.
-/
private theorem isCompact_unit_box (F : Type) [NontriviallyNormedField F] [ProperSpace F] (n : ℕ) :
    IsCompact {Z : Gl n F | (∀ i j, ‖Z.1 i j‖ ≤ 1) ∧ (∀ i, ‖Z.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Z.2.2.1 i‖ ≤ 1) ∧
      ‖Z.2.2.2‖ ≤ 1} := by
  have hv : IsCompact (Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : F) 1) :=
    isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have hm : IsCompact {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ 1} := by
    have h : {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ 1} =
        Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : F) 1 := by
      ext A
      exact ⟨fun h i _ j _ => by simpa using h i j,
        fun h i j => by simpa using h i (Set.mem_univ i) j (Set.mem_univ j)⟩
    rw [h]
    exact isCompact_univ_pi fun _ => hv
  have h : {Z : Gl n F | (∀ i j, ‖Z.1 i j‖ ≤ 1) ∧ (∀ i, ‖Z.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Z.2.2.1 i‖ ≤ 1) ∧
      ‖Z.2.2.2‖ ≤ 1} = {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ 1} ×ˢ
        ((Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : F) 1) ×ˢ
          ((Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : F) 1) ×ˢ Metric.closedBall (0 : F) 1)) := by
    ext Z; simp
  rw [h]
  exact hm.prod (hv.prod (hv.prod (isCompact_closedBall 0 1)))

/- English proof (translation)
Introduce `F _ _ n Y hY`. Establish `: ProperSpace F` using `ProperSpace.of_locallyCompactSpace F`. Take `⟨-, -, hCB, -, -⟩` from `GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants F n`. Establish `hdet : (Cm Y).det * (Bm Y).det ≠ 0`. Rewrite using `[← Matrix.det_mul, hCB Y]`.

Conclude with `hY`. Establish `hB : IsUnit (Bm Y).det` using `isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul hdet)`. Establish `hC : IsUnit (Cm Y).det` using `isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul hdet)`. Establish `hψ : Continuous (fun Z : Gl n F => (Bm Z * (Bm Y)⁻¹, MulOpposite.op ((Cm Y)⁻¹ * Cm Z)))` using `(GlobalTheory.JR.GLCompact.continuous_Bm.matrix_mul continuous_const).prodMk (MulOpposite.continuous_op.comp (continuous_const.matrix_mul GlobalTheory.JR.GLCompact.continuous_Cm))`. Establish `hK` using `Units.isClosedEmbedding_embedProduct.isCompact_preimage ((isCompact_unit_box F n).image hψ)`.

Use `HasCompactSupport.intro hK ?_` and prove the remaining obligations. Introduce `g hg`. Establish `hgY : act g Y ∉ {Z : Gl n F | (∀ i j, ‖Z.1 i j‖ ≤ 1) ∧ (∀ i, ‖Z.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Z.2.2.1 i‖ ≤ 1) ∧ ‖Z.2.2.2‖ ≤ 1}`. Introduce `hmem`. Use `hg ⟨act g Y, hmem, Prod.ext ?_ ?_⟩` and prove the remaining obligations.

Use `show Bm (act g Y) * (Bm Y)⁻¹ = (g : Matrix (Fin n) (Fin n) F)`. Rewrite using `[GlobalTheory.JR.GLCompact.Bm_act, Matrix.mul_nonsing_inv_cancel_right _ _ hB]`. Use `show MulOpposite.op ((Cm Y)⁻¹ * Cm (act g Y)) = MulOpposite.op ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)`. Rewrite using `[GlobalTheory.JR.TransferFactor.Cm_act, Matrix.nonsing_inv_mul_cancel_left _ _ hC]`. Establish `h0 : unitG n F (act g Y) = 0` using `Set.indicator_of_notMem hgY _`.

Simplify using `[h0]`.
-/
theorem GlobalTheory.JR.orbG_integrand_hasCompactSupport : ∀ (F : Type) [NontriviallyNormedField F] [LocallyCompactSpace F] (n : ℕ) (Y : Gl n F), Delta (inv Y) ≠ 0 → HasCompactSupport (fun g : GL (Fin n) F => unitG n F (act g Y) * omega (act g Y)) := by
  intro F _ _ n Y hY
  have : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  obtain ⟨-, -, hCB, -, -⟩ := GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants F n
  have hdet : (Cm Y).det * (Bm Y).det ≠ 0 := by
    rw [← Matrix.det_mul, hCB Y]
    exact hY
  have hB : IsUnit (Bm Y).det := isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul hdet)
  have hC : IsUnit (Cm Y).det := isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul hdet)

  have hψ : Continuous (fun Z : Gl n F =>
      (Bm Z * (Bm Y)⁻¹, MulOpposite.op ((Cm Y)⁻¹ * Cm Z))) :=
    (GlobalTheory.JR.GLCompact.continuous_Bm.matrix_mul continuous_const).prodMk
      (MulOpposite.continuous_op.comp (continuous_const.matrix_mul GlobalTheory.JR.GLCompact.continuous_Cm))
  have hK := Units.isClosedEmbedding_embedProduct.isCompact_preimage
    ((isCompact_unit_box F n).image hψ)
  refine HasCompactSupport.intro hK ?_
  intro g hg
  have hgY : act g Y ∉ {Z : Gl n F | (∀ i j, ‖Z.1 i j‖ ≤ 1) ∧ (∀ i, ‖Z.2.1 i‖ ≤ 1) ∧
      (∀ i, ‖Z.2.2.1 i‖ ≤ 1) ∧ ‖Z.2.2.2‖ ≤ 1} := by
    intro hmem
    refine hg ⟨act g Y, hmem, Prod.ext ?_ ?_⟩
    · show Bm (act g Y) * (Bm Y)⁻¹ = (g : Matrix (Fin n) (Fin n) F)
      rw [GlobalTheory.JR.GLCompact.Bm_act, Matrix.mul_nonsing_inv_cancel_right _ _ hB]
    · show MulOpposite.op ((Cm Y)⁻¹ * Cm (act g Y)) =
        MulOpposite.op ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
      rw [GlobalTheory.JR.TransferFactor.Cm_act, Matrix.nonsing_inv_mul_cancel_left _ _ hC]
  have h0 : unitG n F (act g Y) = 0 := Set.indicator_of_notMem hgY _
  simp [h0]
