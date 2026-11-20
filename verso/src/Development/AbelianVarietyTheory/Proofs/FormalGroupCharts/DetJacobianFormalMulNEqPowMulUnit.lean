import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.LawRightUnit
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalGroupLawCompMulNZero

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF

namespace GlobalTheory.MulJacobian

variable {R : Type} [CommRing R] {d : ℕ}

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => rfl`. Consider the case `succ n ih => rw [mulF, mulN, ih]`.
-/
theorem mulF_eq_mulN (G : FGLaw R d) (N : ℕ) : mulF G.F N = mulN G N := by
  induction N with
  | zero => rfl
  | succ n ih => rw [mulF, mulN, ih]

def invMat (G : FGLaw R d) : Matrix (Fin d) (Fin d) (PS R 1 d) :=
  Matrix.of fun j i => ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), i) (G.F j))

/- English proof (translation)
Rewrite using `[invMat, Matrix.of_apply, GlobalTheory.GaugeAdjoint.constantCoeff_ev GlobalTheory.ChartTrans.axis_GP, ← GlobalTheory.FormalMulN.coeff_single_one, GlobalTheory.FormalMulN.lin_F_right, Matrix.one_apply]`.
-/
theorem const_invMat (G : FGLaw R d) (j i : Fin d) :
    constantCoeff (invMat G j i) = (1 : Matrix (Fin d) (Fin d) R) j i := by
  rw [invMat, Matrix.of_apply, GlobalTheory.GaugeAdjoint.constantCoeff_ev GlobalTheory.ChartTrans.axis_GP,
    ← GlobalTheory.FormalMulN.coeff_single_one, GlobalTheory.FormalMulN.lin_F_right, Matrix.one_apply]

/- English proof (translation)
Rewrite using `[MvPowerSeries.isUnit_iff_constantCoeff, RingHom.map_det]`. Establish `: (constantCoeff (σ` using `σ) (R := R)).mapMatrix M = 1 := by`. Use extensionality with `j i`. Conclude with `h j i`. Rewrite using `[this, Matrix.det_one]`.

Conclude with `isUnit_one`.
-/
theorem isUnit_det_of_const {σ : Type} (M : Matrix (Fin d) (Fin d) (MvPowerSeries σ R))
    (h : ∀ j i, constantCoeff (M j i) = (1 : Matrix (Fin d) (Fin d) R) j i) : IsUnit M.det := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff, RingHom.map_det]
  have : (constantCoeff (σ := σ) (R := R)).mapMatrix M = 1 := by
    ext j i
    exact h j i
  rw [this, Matrix.det_one]
  exact isUnit_one

/- English proof (translation)
Unfold `Dof`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single l]`. Rewrite using `[Pi.single_eq_same, invMat, Matrix.of_apply]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `m _ hm`. Rewrite using `[Pi.single_eq_of_ne hm, map_zero, zero_mul]`. Simplify using the standard rewrite rules.
-/
theorem dof_single (G : FGLaw R d) (c : R) (l : Fin d) (f : PS R 1 d) :
    Dof G.F (Pi.single l c) f = C c * ∑ j, pderiv R ((0 : Fin 1), j) f * invMat G j l := by
  unfold Dof
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single l]
  · rw [Pi.single_eq_same, invMat, Matrix.of_apply]
    ring
  · intro m _ hm
    rw [Pi.single_eq_of_ne hm, map_zero, zero_mul]
  · simp

/- English proof (translation)
Take `⟨h0, h1, h2⟩` from `GlobalTheory.FormalMulN.mulN_hom R d G N`. Establish `hφ : GP (mulN G N)` using `h0`. Use `ext1 i l`. Establish `h` using `GlobalTheory.HomChain.dof_hom G G (mulN G N) h0 h1 (Pi.single l 1) (pt R d 0 i)`. Establish `e1 : (dLin (mulN G N)).mulVec (Pi.single l 1) = Pi.single l (N : R)`.

Rewrite using `[h2, Matrix.smul_mulVec, Matrix.one_mulVec, ← Pi.single_smul, smul_eq_mul, mul_one]`. Establish `e2 : ev (n` using `1) ![mulN G N] (pt R d 0 i) = mulN G N i := GlobalTheory.GaugeAdjoint.ev_pt (single_point_zero_constant hφ) 0 i`. Establish `e3 : ∑ j, pderiv R ((0 : Fin 1), j) (pt R (n` using `1) d 0 i) * invMat G j l = invMat G i l := by`. Rewrite using `[Finset.sum_eq_single i]`. Simplify using `[pt]`.

Introduce `j _ hj`. Rewrite using `[pt, pderiv_X_of_ne (by simpa using hj.symm), zero_mul]`. Simplify using the standard rewrite rules. Rewrite `h` using `[e1, e2, dof_single, dof_single, e3, GlobalTheory.ChartTrans.ev_C_mul _ (single_point_zero_constant hφ), map_one, one_mul, map_natCast]`. Rewrite using `[Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]`.

Conclude with `h`.
-/
theorem jac_mul_invMat (G : FGLaw R d) (N : ℕ) :
    (Matrix.of fun i j : Fin d => pderiv R ((0 : Fin 1), j) (mulN G N i)) * invMat G =
      (N : PS R 1 d) • Matrix.of fun i l => ev (n := 1) ![mulN G N] (invMat G i l) := by
  obtain ⟨h0, h1, h2⟩ := GlobalTheory.FormalMulN.mulN_hom R d G N
  have hφ : GP (mulN G N) := h0
  ext1 i l
  have h := GlobalTheory.HomChain.dof_hom G G (mulN G N) h0 h1 (Pi.single l 1) (pt R d 0 i)
  have e1 : (dLin (mulN G N)).mulVec (Pi.single l 1) = Pi.single l (N : R) := by
    rw [h2, Matrix.smul_mulVec, Matrix.one_mulVec, ← Pi.single_smul, smul_eq_mul, mul_one]
  have e2 : ev (n := 1) ![mulN G N] (pt R d 0 i) = mulN G N i :=
    GlobalTheory.GaugeAdjoint.ev_pt (single_point_zero_constant hφ) 0 i
  have e3 : ∑ j, pderiv R ((0 : Fin 1), j) (pt R (n := 1) d 0 i) * invMat G j l = invMat G i l := by
    rw [Finset.sum_eq_single i]
    · simp [pt]
    · intro j _ hj
      rw [pt, pderiv_X_of_ne (by simpa using hj.symm), zero_mul]
    · simp
  rw [e1, e2, dof_single, dof_single, e3, GlobalTheory.ChartTrans.ev_C_mul _ (single_point_zero_constant hφ), map_one, one_mul,
    map_natCast] at h
  rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  exact h

/- English proof (translation)
Introduce `R _ d G N`. Establish `hφ : GP (mulN G N)` using `GlobalTheory.FormalMulN.const_mulN G N`. Take `⟨a, ha⟩` from `isUnit_det_of_const (invMat G) (const_invMat G)`. Take `⟨b, hb⟩` from `isUnit_det_of_const (Matrix.of fun i l => ev (n := 1) ![mulN G N] (invMat G i l)) (fun i l => by`. Rewrite using `[Matrix.of_apply, GlobalTheory.GaugeAdjoint.constantCoeff_ev (single_point_zero_constant hφ), const_invMat])`.

Establish `h` using `congrArg Matrix.det (jac_mul_invMat G N)`. Rewrite `h` using `[Matrix.det_mul, Matrix.det_smul, Fintype.card_fin, ← ha, ← hb]`. Use `⟨b * a⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[mulF_eq_mulN, Units.val_mul, ← mul_assoc, ← h, Units.mul_inv_cancel_right]`.
-/
theorem det_jac_mulF : ∀ (R : Type) [CommRing R] (d : ℕ) (F : FGLaw R d) (N : ℕ),
    ∃ U : (PS R 1 d)ˣ, Matrix.det (Matrix.of fun i j : Fin d =>
      MvPowerSeries.pderiv R ((0 : Fin 1), j) (mulF F.F N i)) = (N : PS R 1 d) ^ d * U := by
  intro R _ d G N
  have hφ : GP (mulN G N) := GlobalTheory.FormalMulN.const_mulN G N
  obtain ⟨a, ha⟩ := isUnit_det_of_const (invMat G) (const_invMat G)
  obtain ⟨b, hb⟩ := isUnit_det_of_const
    (Matrix.of fun i l => ev (n := 1) ![mulN G N] (invMat G i l)) (fun i l => by
      rw [Matrix.of_apply, GlobalTheory.GaugeAdjoint.constantCoeff_ev (single_point_zero_constant hφ), const_invMat])
  have h := congrArg Matrix.det (jac_mul_invMat G N)
  rw [Matrix.det_mul, Matrix.det_smul, Fintype.card_fin, ← ha, ← hb] at h
  refine ⟨b * a⁻¹, ?_⟩
  rw [mulF_eq_mulN, Units.val_mul, ← mul_assoc, ← h, Units.mul_inv_cancel_right]

end GlobalTheory.MulJacobian
