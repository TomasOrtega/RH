import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffLinearSubstitutionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WirtingerDerivsCompHolomorphicPullbackDz

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.ChartGlue GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix ComplexConjugate

namespace GlobalTheory.GoodTop.CorrHolo

variable {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]

def coordMat (L : V n →L[ℂ] V n) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun c a => L (coordVec a) c

variable {φ : V n → V n} {w : V n}

end GlobalTheory.GoodTop.CorrHolo

namespace GlobalTheory.GoodTop

open CorrHolo

set_option autoImplicit false in
open MeasureTheory Filter Topology in
open scoped ContDiff Matrix ComplexConjugate in
/- English proof (translation)
The claim follows from `_root_.GlobalTheory.LineForm.chain_sum_coordVec _`.
-/
private lemma apply_coordVec_eq_sum_coordMat {n : ℕ} (L : _root_.ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] _root_.ReciprocityTheory.L2DbarEstimates.V n)
    (a : Fin n) : L (_root_.GlobalTheory.GoodMetric.coordVec a) =
      ∑ c, _root_.GlobalTheory.GoodTop.CorrHolo.coordMat L c a • _root_.GlobalTheory.GoodMetric.coordVec c :=
  _root_.GlobalTheory.LineForm.chain_sum_coordVec _

set_option autoImplicit false in
open MeasureTheory Filter Topology in
open scoped ContDiff Matrix ComplexConjugate in
/- English proof (translation)
Use extensionality with `i j`. Simplify using `[_root_.GlobalTheory.HermFrame.mdel_apply, Matrix.sum_apply]`.
-/
private lemma mdel_sum_smul_coordVec {n : ℕ} {r : Type}
    (G : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (z : _root_.ReciprocityTheory.L2DbarEstimates.V n) (x : Fin n → ℂ) :
    _root_.GlobalTheory.HermFrame.mdel G z (∑ c, x c • _root_.GlobalTheory.GoodMetric.coordVec c) =
      ∑ c, x c • _root_.GlobalTheory.HermFrame.mdel G z (_root_.GlobalTheory.GoodMetric.coordVec c) := by
  ext i j
  simp [_root_.GlobalTheory.HermFrame.mdel_apply, Matrix.sum_apply]

set_option autoImplicit false in
open MeasureTheory Filter Topology in
open scoped ContDiff Matrix ComplexConjugate in
/- English proof (translation)
Use extensionality with `i j`. Simplify using `[_root_.GlobalTheory.HermFrame.mdbar_apply, Matrix.sum_apply]`.
-/
private lemma mdbar_sum_smul_coordVec {n : ℕ} {r : Type}
    (G : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (z : _root_.ReciprocityTheory.L2DbarEstimates.V n) (y : Fin n → ℂ) :
    _root_.GlobalTheory.HermFrame.mdbar G z (∑ d, y d • _root_.GlobalTheory.GoodMetric.coordVec d) =
      ∑ d, starRingEnd ℂ (y d) • _root_.GlobalTheory.HermFrame.mdbar G z (_root_.GlobalTheory.GoodMetric.coordVec d) := by
  ext i j
  simp [_root_.GlobalTheory.HermFrame.mdbar_apply, Matrix.sum_apply]

set_option autoImplicit false in
open MeasureTheory Filter Topology in
open scoped ContDiff Matrix ComplexConjugate in
/- English proof (translation)
Use extensionality with `i j`. Simplify using `[_root_.GlobalTheory.HermFrame.mddbar_apply, Matrix.sum_apply, Finset.mul_sum, mul_assoc]`. Rewrite using `[Finset.sum_comm]`.
-/
private lemma mddbar_sum_smul_coordVec {n : ℕ} {r : Type}
    (G : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (z : _root_.ReciprocityTheory.L2DbarEstimates.V n) (x y : Fin n → ℂ) :
    _root_.GlobalTheory.HermFrame.mddbar G z (∑ c, x c • _root_.GlobalTheory.GoodMetric.coordVec c)
        (∑ d, y d • _root_.GlobalTheory.GoodMetric.coordVec d) =
      ∑ c, ∑ d, (x c * starRingEnd ℂ (y d)) •
        _root_.GlobalTheory.HermFrame.mddbar G z (_root_.GlobalTheory.GoodMetric.coordVec c) (_root_.GlobalTheory.GoodMetric.coordVec d) := by
  ext i j
  simp [_root_.GlobalTheory.HermFrame.mddbar_apply, Matrix.sum_apply, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

set_option autoImplicit false in
open MeasureTheory Filter Topology in
open scoped ContDiff Matrix ComplexConjugate in
/- English proof (translation)
Simplify using `only [_root_.GlobalTheory.HermFrame.curv_eq hG hu, mdel_sum_smul_coordVec, mdbar_sum_smul_coordVec, mddbar_sum_smul_coordVec, Matrix.transpose_sum, Matrix.transpose_smul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub, Finset.sum_sub_distrib, smul_smul …`.
-/
private lemma curv_sum_smul_coordVec {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]
    (G : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (z : _root_.ReciprocityTheory.L2DbarEstimates.V n) (hG : _root_.GlobalTheory.HermFrame.MContDiffAt 2 G z)
    (hu : IsUnit (G z).det) (x y : Fin n → ℂ) :
    _root_.GlobalTheory.HermFrame.curv G z (∑ c, x c • _root_.GlobalTheory.GoodMetric.coordVec c)
        (∑ d, y d • _root_.GlobalTheory.GoodMetric.coordVec d) =
      ∑ c, ∑ d, (x c * starRingEnd ℂ (y d)) •
        _root_.GlobalTheory.HermFrame.curv G z (_root_.GlobalTheory.GoodMetric.coordVec c) (_root_.GlobalTheory.GoodMetric.coordVec d) := by
  simp only [_root_.GlobalTheory.HermFrame.curv_eq hG hu, mdel_sum_smul_coordVec,
    mdbar_sum_smul_coordVec, mddbar_sum_smul_coordVec,
    Matrix.transpose_sum, Matrix.transpose_smul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul, smul_sub, Finset.sum_sub_distrib, smul_smul, Finset.smul_sum]

set_option autoImplicit false in
open MeasureTheory Filter Topology in
open scoped ContDiff Matrix ComplexConjugate in
/- English proof (translation)
Set `f : _root_.ReciprocityTheory.L2DbarEstimates.V n →+ Matrix r r ℂ` to `{ toFun := _root_.GlobalTheory.HermFrame.conn G z map_zero' := by simpa using _root_.GlobalTheory.HermFrame.conn_smul_vec G z 0 0 map_add' := _root_.GlobalTheory.HermFrame.conn_add_vec G z }`. Express the relevant statement in the definitionally equal form `f (∑ c, x c • v c) = _`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun c _ => _root_.GlobalTheory.HermFrame.conn_smul_vec G z (x c) (v c)`.
-/
private lemma conn_sum_smul {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]
    (G : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (z : _root_.ReciprocityTheory.L2DbarEstimates.V n) (x : Fin n → ℂ) (v : Fin n → _root_.ReciprocityTheory.L2DbarEstimates.V n) :
    _root_.GlobalTheory.HermFrame.conn G z (∑ c, x c • v c) =
      ∑ c, x c • _root_.GlobalTheory.HermFrame.conn G z (v c) := by
  let f : _root_.ReciprocityTheory.L2DbarEstimates.V n →+ Matrix r r ℂ :=
    { toFun := _root_.GlobalTheory.HermFrame.conn G z
      map_zero' := by simpa using _root_.GlobalTheory.HermFrame.conn_smul_vec G z 0 0
      map_add' := _root_.GlobalTheory.HermFrame.conn_add_vec G z }
  change f (∑ c, x c • v c) = _
  rw [map_sum]
  exact Finset.sum_congr rfl fun c _ => _root_.GlobalTheory.HermFrame.conn_smul_vec G z (x c) (v c)

set_option autoImplicit false in
open MeasureTheory Filter Topology in
open scoped ContDiff Matrix ComplexConjugate in

/- English proof (translation)
Establish `hφd : DifferentiableAt ℂ φ w` using `hφ.differentiableAt (by norm_num)`. Establish `h₀' : _root_.GlobalTheory.HermFrame.MContDiffAt 1 G₀ (φ w)` using `fun a b => (h₀ a b).of_le (by norm_num)`. Establish `h₁' : _root_.GlobalTheory.HermFrame.MContDiffAt 1 G₁ (φ w)` using `fun a b => (h₁ a b).of_le (by norm_num)`. Take `⟨J, hJ⟩ : ∃ J, J = _root_.GlobalTheory.GoodTop.CorrHolo.coordMat (fderiv ℂ φ w)` from `⟨_, rfl⟩`. Establish `hL : ∀ a, fderiv ℂ φ w (_root_.GlobalTheory.GoodMetric.coordVec a) = ∑ c, J c a • _root_.GlobalTheory.GoodMetric.coordVec c`.

Introduce `a`. Rewrite using `[hJ]`. Conclude with `apply_coordVec_eq_sum_coordMat _ a`. Establish `hcurv : ∀ G : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ, _root_.GlobalTheory.HermFrame.MContDiffAt 2 G (φ w) → IsUnit (G (φ w)).det → _root_.GlobalTheory.GoodTop.curvAt (fun x => G (φ x)) w = fun a b => ∑ c, ∑ d, (J c a * (J.map (starRingEnd ℂ)) d b) • _root_.Gl …`. Introduce `G hG hu`.

Use function extensionality and compare the values at `a b`. Simplify using `only [_root_.GlobalTheory.GoodTop.curvAt, Matrix.map_apply]`. Rewrite using `[_root_.GlobalTheory.HermFrame.curv_comp_holo hG hu hφ, hL, hL, curv_sum_smul_coordVec G _ hG hu]`. Establish `hρc : DifferentiableAt ℝ (fun y => (ρ y : ℂ)) (φ w)` using `Complex.ofRealCLM.differentiableAt.comp _ hρ`. Establish `hdbar : _root_.GlobalTheory.GoodTop.cutForm (fun x => ρ (φ x)) (fun x => G₀ (φ x)) (fun x => G₁ (φ x)) w = fun a b => ∑ c, ∑ d, (J c a * (J.map (starRingEnd ℂ)) d b) • _root_.GlobalTheory.GoodTop.cutForm ρ G₀ G₁ (φ w) c d`.

Use function extensionality and compare the values at `a b`. Simplify using `only [_root_.GlobalTheory.GoodTop.cutForm, Matrix.map_apply]`. Establish `hw` using `_root_.GlobalTheory.dbar_comp_holo (u := fun y => (ρ y : ℂ)) hρc hφd`. Rewrite using `[hw, _root_.GlobalTheory.HermFrame.conn_comp_holo h₁' hφd, _root_.GlobalTheory.HermFrame.conn_comp_holo h₀' hφd, hL, hL, conn_sum_smul, conn_sum_smul, map_sum, ← Finset.sum_sub_distrib, Finset.sum_smul]`. Simplify using `only [map_smulₛₗ, Finset.smul_sum]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Simplify using `only [← smul_sub, smul_smul, smul_eq_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `hdet : J.det * (J.map (starRingEnd ℂ)).det = ((‖(fderiv ℂ φ w).det‖ ^ 2 : ℝ) : ℂ)`. Establish `h1 : J.det = (fderiv ℂ φ w).det`. Establish `hJm : J = LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis (EuclideanSpace.basisFun (Fin n) ℂ).toBasis (fderiv ℂ φ w : _root_.ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] _root_.ReciprocityTheory.L2DbarEstimates.V n)`. Use extensionality with `c a`. Simplify using `[hJ, _root_.GlobalTheory.GoodTop.CorrHolo.coordMat, LinearMap.toMatrix_apply, _root_.GlobalTheory.GoodMetric.coordVec]`.

Rewrite using `[hJm, LinearMap.det_toMatrix]`. Establish `h2 : (J.map (starRingEnd ℂ)).det = starRingEnd ℂ J.det` using `(RingHom.map_det (starRingEnd ℂ) J).symm`. Rewrite using `[h2, Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]`. Unfold `_root_.GlobalTheory.GoodTop.corrC`. Rewrite using `[hcurv G₁ h₁ u₁, hcurv G₀ h₀ u₀, hdbar, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← hdet, ← _root_.GlobalTheory.GoodTop.mixTop_subst]`. Use `congr 1`. Use function extensionality and compare the values at `i a b`. Unfold `_root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one`.

Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem _root_.GlobalTheory.GoodTop.corrC_comp_holo {n : ℕ} {r : Type} [Fintype r]
    [DecidableEq r] {ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ} {G₀ G₁ : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ}
    {φ : _root_.ReciprocityTheory.L2DbarEstimates.V n → _root_.ReciprocityTheory.L2DbarEstimates.V n} {w : _root_.ReciprocityTheory.L2DbarEstimates.V n} (hφ : ContDiffAt ℂ 2 φ w)
    (hρ : DifferentiableAt ℝ ρ (φ w))
    (h₀ : _root_.GlobalTheory.HermFrame.MContDiffAt 2 G₀ (φ w)) (u₀ : IsUnit (G₀ (φ w)).det)
    (h₁ : _root_.GlobalTheory.HermFrame.MContDiffAt 2 G₁ (φ w))
    (u₁ : IsUnit (G₁ (φ w)).det) :
    _root_.GlobalTheory.GoodTop.corrC (fun x => ρ (φ x)) (fun x => G₀ (φ x)) (fun x => G₁ (φ x)) w =
      ((‖(fderiv ℂ φ w).det‖ ^ 2 : ℝ) : ℂ) * _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ (φ w) := by
  have hφd : DifferentiableAt ℂ φ w := hφ.differentiableAt (by norm_num)
  have h₀' : _root_.GlobalTheory.HermFrame.MContDiffAt 1 G₀ (φ w) := fun a b => (h₀ a b).of_le (by norm_num)
  have h₁' : _root_.GlobalTheory.HermFrame.MContDiffAt 1 G₁ (φ w) := fun a b => (h₁ a b).of_le (by norm_num)
  obtain ⟨J, hJ⟩ : ∃ J, J = _root_.GlobalTheory.GoodTop.CorrHolo.coordMat (fderiv ℂ φ w) := ⟨_, rfl⟩
  have hL : ∀ a, fderiv ℂ φ w (_root_.GlobalTheory.GoodMetric.coordVec a) =
      ∑ c, J c a • _root_.GlobalTheory.GoodMetric.coordVec c := by
    intro a
    rw [hJ]
    exact apply_coordVec_eq_sum_coordMat _ a
  have hcurv : ∀ G : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ, _root_.GlobalTheory.HermFrame.MContDiffAt 2 G (φ w) →
      IsUnit (G (φ w)).det → _root_.GlobalTheory.GoodTop.curvAt (fun x => G (φ x)) w =
        fun a b => ∑ c, ∑ d, (J c a * (J.map (starRingEnd ℂ)) d b) •
          _root_.GlobalTheory.GoodTop.curvAt G (φ w) c d := by
    intro G hG hu
    funext a b
    simp only [_root_.GlobalTheory.GoodTop.curvAt, Matrix.map_apply]
    rw [_root_.GlobalTheory.HermFrame.curv_comp_holo hG hu hφ, hL, hL,
      curv_sum_smul_coordVec G _ hG hu]
  have hρc : DifferentiableAt ℝ (fun y => (ρ y : ℂ)) (φ w) :=
    Complex.ofRealCLM.differentiableAt.comp _ hρ
  have hdbar : _root_.GlobalTheory.GoodTop.cutForm (fun x => ρ (φ x)) (fun x => G₀ (φ x))
      (fun x => G₁ (φ x)) w = fun a b => ∑ c, ∑ d, (J c a * (J.map (starRingEnd ℂ)) d b) •
        _root_.GlobalTheory.GoodTop.cutForm ρ G₀ G₁ (φ w) c d := by
    funext a b
    simp only [_root_.GlobalTheory.GoodTop.cutForm, Matrix.map_apply]
    have hw := _root_.GlobalTheory.dbar_comp_holo (u := fun y => (ρ y : ℂ)) hρc hφd

    rw [hw, _root_.GlobalTheory.HermFrame.conn_comp_holo h₁' hφd,
      _root_.GlobalTheory.HermFrame.conn_comp_holo h₀' hφd, hL, hL, conn_sum_smul,
      conn_sum_smul, map_sum, ← Finset.sum_sub_distrib, Finset.sum_smul]
    simp only [map_smulₛₗ, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    simp only [← smul_sub, smul_smul, smul_eq_mul]
    congr 1
    ring
  have hdet : J.det * (J.map (starRingEnd ℂ)).det = ((‖(fderiv ℂ φ w).det‖ ^ 2 : ℝ) : ℂ) := by
    have h1 : J.det = (fderiv ℂ φ w).det := by
      have hJm : J = LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
          (EuclideanSpace.basisFun (Fin n) ℂ).toBasis (fderiv ℂ φ w : _root_.ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] _root_.ReciprocityTheory.L2DbarEstimates.V n) := by
        ext c a
        simp [hJ, _root_.GlobalTheory.GoodTop.CorrHolo.coordMat, LinearMap.toMatrix_apply,
          _root_.GlobalTheory.GoodMetric.coordVec]
      rw [hJm, LinearMap.det_toMatrix]
    have h2 : (J.map (starRingEnd ℂ)).det = starRingEnd ℂ J.det :=
      (RingHom.map_det (starRingEnd ℂ) J).symm
    rw [h2, Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]
  unfold _root_.GlobalTheory.GoodTop.corrC
  rw [hcurv G₁ h₁ u₁, hcurv G₀ h₀ u₀, hdbar, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hdet, ← _root_.GlobalTheory.GoodTop.mixTop_subst]
  congr 1
  funext i a b
  unfold _root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one
  split_ifs <;> rfl

end GlobalTheory.GoodTop
