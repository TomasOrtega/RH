import Formalism.HermitianCurvature.StatementTL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameCompletion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Sq2UnitOfEqOneOfSq2EqDiv
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HomogeneityNaturalDegree

open Matrix Finset
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.TL

namespace TLC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

/- English proof (translation)
Establish `hH : ∀ i j : Fin (2 * r + k + 1), star (Hpk k r i j) = Hpk k r j i`. Introduce `i j`. Simplify using `only [Hpk, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | (exfalso; omega) | norm_num`. Simplify using `only [herm, dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', star_star, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hH]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem herm_swap_eq_zero_of_eq_zero {k r : ℕ} (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) w v = star (herm (Hpk k r) v w) := by
  have hH : ∀ i j : Fin (2 * r + k + 1), star (Hpk k r i j) = Hpk k r j i := by
    intro i j
    simp only [Hpk, Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | norm_num
  simp only [herm, dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hH]
  ring

/- English proof (translation)
Establish `hdec` using `HermitianFormSums.complete0 hz' (HermitianFormSums.hzz hT') hB0 hu huz`. Establish `h1 : herm (Hpk k r) u y = ∑ j, herm (Hpk k r) u (B0 j) * herm (Hpk k r) (B0 j) y` using `by conv_lhs => rw [hdec]`. Conclude with `HermitianFormSums.herm_lsum _ _ _ _ _`. Rewrite using `[h1, HermitianFormSums.herm_rsum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[herm_swap_eq_zero_of_eq_zero y (B0 j), star_mul']`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem herm_Hpk_frame_sum_of_orthogonal {z' y u : Fin (2 * r + k + 1) → ℂ} {B0 : Fin k → Fin (2 * r + k + 1) → ℂ}
    (hz' : inWb k r z') (hT' : 0 < Tz k r z') (hB0 : IsFrameOf k r [z'] B0) (a : ℂ) (hu : inWb k r u)
    (huz : herm (Hpk k r) u z' = 0) :
    herm (Hpk k r) u (∑ j, (a * herm (Hpk k r) y (B0 j)) • B0 j) = star a * herm (Hpk k r) u y := by
  have hdec := HermitianFormSums.complete0 hz' (HermitianFormSums.hzz hT') hB0 hu huz
  have h1 : herm (Hpk k r) u y = ∑ j, herm (Hpk k r) u (B0 j) * herm (Hpk k r) (B0 j) y := by
    conv_lhs => rw [hdec]
    exact HermitianFormSums.herm_lsum _ _ _ _ _
  rw [h1, HermitianFormSums.herm_rsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [herm_swap_eq_zero_of_eq_zero y (B0 j), star_mul']
  ring

/- English proof (translation)
Rewrite using `[show (∑ j, β j • B0 j) = ∑ j, (a * herm (Hpk k r) y (B0 j)) • B0 j from Finset.sum_congr rfl fun j _ => by rw [hβ j], herm_Hpk_frame_sum_of_orthogonal hz' hT' hB0 a hu huz, huy, mul_zero]`.
-/
theorem xf_perp {z' y u : Fin (2 * r + k + 1) → ℂ} {B0 : Fin k → Fin (2 * r + k + 1) → ℂ} (hz' : inWb k r z')
    (hT' : 0 < Tz k r z') (hB0 : IsFrameOf k r [z'] B0) (β : Fin k → ℂ) (a : ℂ)
    (hβ : ∀ j, β j = a * herm (Hpk k r) y (B0 j)) (hu : inWb k r u) (huz : herm (Hpk k r) u z' = 0)
    (huy : herm (Hpk k r) u y = 0) : herm (Hpk k r) u (∑ j, β j • B0 j) = 0 := by
  rw [show (∑ j, β j • B0 j) = ∑ j, (a * herm (Hpk k r) y (B0 j)) • B0 j from
    Finset.sum_congr rfl fun j _ => by rw [hβ j], herm_Hpk_frame_sum_of_orthogonal hz' hT' hB0 a hu huz, huy, mul_zero]

/- English proof (translation)
Establish `hx'` using `hx`. Take `⟨-, hgl, hGG⟩` from `hx'`. Take `⟨hbig, -⟩` from `hCell k r Wp Wq Bs x hx`. Take `⟨-, hsq, -, hcell⟩` from `hOm k r Wp Wq Bs B0 hB0`. Take `⟨Bs', -, -, hF, -⟩` from `Q.LieAlgebraWeightVectors.geom_package Bs.z_mem Bs.z'_mem Bs.T_pos Bs.T'_pos hgl hGG.ne'`.

Establish `hν1 : C6.sq2 (C6.unitOf (Tz k r Bs.z') (Gf k r Bs.z Bs.z' (wCell k r (Fin.last r) x.1 * x.2)) (omC Bs B0 (wCell k r (Fin.last r) x.1 * x.2))) = 1` using `AdmissibleLieWords.sq2_unitOf_eq_one_of_sq2_eq_div Bs.T'_pos hbig.2.1 (hsq _ hbig.1)`. Establish `hF2 : IsFrameOf k r [Bs.z', ∑ j, C6.unitOf (Tz k r Bs.z') (Gf k r Bs.z Bs.z' (wCell k r (Fin.last r) x.1 * x.2)) (omC Bs B0 (wCell k r (Fin.last r) x.1 * x.2)) j • B0 j] Bs'`. Use `⟨hF.1, hF.2.1, fun i v hv => ?_⟩` and prove the remaining obligations. Simplify using `only [List.mem_cons, List.not_mem_nil, or_false] at hv`. Break down `hv with rfl | rfl` into its components or cases.

Conclude with `hF.2.2 i _ (by simp)`. Use `xf_perp Bs.z'_mem Bs.T'_pos hB0 _ (((Real.sqrt (Tz k r Bs.z' / Gf k r Bs.z Bs.z' (wCell k r (Fin.last r) x.1 * x.2)) : ℝ) : ℂ) * conj (∏ a, x.1 a)) (fun j => ?_) (hF.1 i) (hF.2.2 i Bs.z' (by simp)) (hF.2.2 i (x.2⁻¹ *ᵥ Bs.z) (by simp))` and prove the remaining obligations. Simplify using `only [C6.unitOf, Pi.smul_apply, smul_eq_mul, hcell x hx j, mul_assoc]`. Establish `hcap` using `hCapF Wq k r Bs.z' Bs.π' B0 Bs' _ Bs.k_pos Bs.z'_mem Bs.T'_pos ⟨Bs.π'_rep, Bs.π'_cont⟩ hB0 hν1 hF2`. Establish `hgl2` using `(frame_general_linear Wq k r (k - 1) Bs.z' Bs.π' Bs' ⟨Bs.π'_rep, Bs.π'_cont⟩ (HermitianFormSums.frame_sub hF2)).2`.

Establish `hne : ((GGl k r Bs.z Bs.z' x.2 : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hGG.ne'`. Use extensionality with `v`. Establish `hfn` using `congrArg (fun T : Wq →L[ℂ] Wp => T v) (X.fn_apply 5 (X.t Y 1 1 Φ) x hx)`. Establish `ht` using `P5.Kfp.diagonal_transfer_action X Bs.z_mem Bs.z'_mem Bs.π'_rep Bs.π'_cont (c := x.1) (g := x.2) hx Bs' hF Y Φ v`. Simplify using `only [Module.End.mul_apply] at ht`.

Simplify using `only [_root_.smul_apply, fnVal] at hfn`. Rewrite `hfn` using `[ht]`. Simplify using `only [xFib, _root_.smul_apply, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply, hcap, hgl2]`. Rewrite using `[hfn, smul_smul, mul_inv_cancel₀ hne, one_smul]`.
-/
theorem xf_rad (hCell : CellVals) (hOm : OmFacts) (hCapF : CapVFrame) {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (Bs : B.RealPlaceData k r Wp Wq) (X : ActualOps k r Bs.z Bs.z' Bs.π Bs.π')
    {B0 : Fin k → Fin (2 * r + k + 1) → ℂ} (hB0 : IsFrameOf k r [Bs.z'] B0) (Y : ℂ)
    (Φ : RadSp k r Bs.z Bs.z' Bs.π Bs.π') (x : (Fin r → ℂ) × Mx k r) (hx : x ∈ DomR k r Bs.z Bs.z') :
    (X.t Y 1 1 Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = ((GGl k r Bs.z Bs.z' x.2 : ℝ) : ℂ) •
      xFib Bs B0 (Y + ((k : ℂ) - 2) / 2) (wCell k r (Fin.last r) x.1 * x.2) ((Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2) := by
  have hx' := hx
  obtain ⟨-, hgl, hGG⟩ := hx'
  obtain ⟨hbig, -⟩ := hCell k r Wp Wq Bs x hx
  obtain ⟨-, hsq, -, hcell⟩ := hOm k r Wp Wq Bs B0 hB0
  obtain ⟨Bs', -, -, hF, -⟩ := Q.LieAlgebraWeightVectors.geom_package Bs.z_mem Bs.z'_mem Bs.T_pos Bs.T'_pos hgl hGG.ne'
  have hν1 : C6.sq2 (C6.unitOf (Tz k r Bs.z') (Gf k r Bs.z Bs.z' (wCell k r (Fin.last r) x.1 * x.2))
      (omC Bs B0 (wCell k r (Fin.last r) x.1 * x.2))) = 1 :=
    AdmissibleLieWords.sq2_unitOf_eq_one_of_sq2_eq_div Bs.T'_pos hbig.2.1 (hsq _ hbig.1)
  have hF2 : IsFrameOf k r [Bs.z', ∑ j, C6.unitOf (Tz k r Bs.z') (Gf k r Bs.z Bs.z' (wCell k r (Fin.last r) x.1 * x.2))
      (omC Bs B0 (wCell k r (Fin.last r) x.1 * x.2)) j • B0 j] Bs' := by
    refine ⟨hF.1, hF.2.1, fun i v hv => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact hF.2.2 i _ (by simp)
    · refine xf_perp Bs.z'_mem Bs.T'_pos hB0 _
        (((Real.sqrt (Tz k r Bs.z' / Gf k r Bs.z Bs.z' (wCell k r (Fin.last r) x.1 * x.2)) : ℝ) : ℂ) *
          conj (∏ a, x.1 a)) (fun j => ?_) (hF.1 i) (hF.2.2 i Bs.z' (by simp))
          (hF.2.2 i (x.2⁻¹ *ᵥ Bs.z) (by simp))
      simp only [C6.unitOf, Pi.smul_apply, smul_eq_mul, hcell x hx j, mul_assoc]
  have hcap := hCapF Wq k r Bs.z' Bs.π' B0 Bs' _ Bs.k_pos Bs.z'_mem Bs.T'_pos ⟨Bs.π'_rep, Bs.π'_cont⟩ hB0 hν1 hF2
  have hgl2 := (frame_general_linear Wq k r (k - 1) Bs.z' Bs.π' Bs' ⟨Bs.π'_rep, Bs.π'_cont⟩ (HermitianFormSums.frame_sub hF2)).2
  have hne : ((GGl k r Bs.z Bs.z' x.2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hGG.ne'
  ext v
  have hfn := congrArg (fun T : Wq →L[ℂ] Wp => T v) (X.fn_apply 5 (X.t Y 1 1 Φ) x hx)
  have ht := P5.Kfp.diagonal_transfer_action X Bs.z_mem Bs.z'_mem Bs.π'_rep Bs.π'_cont (c := x.1) (g := x.2) hx Bs' hF Y Φ v
  simp only [Module.End.mul_apply] at ht
  simp only [_root_.smul_apply, fnVal] at hfn
  rw [ht] at hfn
  simp only [xFib, _root_.smul_apply, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply, hcap, hgl2]
  rw [hfn, smul_smul, mul_inv_cancel₀ hne, one_smul]

section fib

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Simplify using `only [capV, Q.chatA, map_sum, map_smul, Pi.star_apply]`.
-/
theorem xf_capV_sum (π' : Mx k r → (Wq →L[ℂ] Wq)) (B0 : Fin k → Fin (2 * r + k + 1) → ℂ) (w : ℂ) (ν : Fin k → ℂ) :
    capV π' B0 w ν = ∑ i : Fin k, ∑ j : Fin k, ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * star (ν i) * ν j) •
      LinearMap.toContinuousLinearMap (qminor (EB π' B0) (skip1 i) (skip1 j) w : Module.End ℂ Wq) := by
  simp only [capV, Q.chatA, map_sum, map_smul, Pi.star_apply]

/- English proof (translation)
Rewrite using `[show (fun ν : Fin k → ℂ => capV π' B0 w ν) = fun ν => ∑ i : Fin k, ∑ j : Fin k, ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * star (ν i) * ν j) • LinearMap.toContinuousLinearMap (qminor (EB π' B0) (skip1 i) (skip1 j) w : Module.End ℂ Wq) from`. Use function extensionality and compare the values at `(xf_capV_sum π' B0 w)]`. Use `ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_` and prove the remaining obligations. Establish `hs : ContDiff ℝ ∞ (fun ν : Fin k → ℂ => star (ν i))` using `Complex.conjCLE.contDiff.comp (contDiff_apply ℝ ℂ i)`. Conclude with `((contDiff_const.mul hs).mul (contDiff_apply ℝ ℂ j)).smul contDiff_const`.
-/
theorem xf_capV_cd (π' : Mx k r → (Wq →L[ℂ] Wq)) (B0 : Fin k → Fin (2 * r + k + 1) → ℂ) (w : ℂ) :
    ContDiff ℝ ∞ (fun ν : Fin k → ℂ => capV π' B0 w ν) := by
  rw [show (fun ν : Fin k → ℂ => capV π' B0 w ν) = fun ν => ∑ i : Fin k, ∑ j : Fin k,
      ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * star (ν i) * ν j) •
        LinearMap.toContinuousLinearMap (qminor (EB π' B0) (skip1 i) (skip1 j) w : Module.End ℂ Wq) from
    funext (xf_capV_sum π' B0 w)]
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
  have hs : ContDiff ℝ ∞ (fun ν : Fin k → ℂ => star (ν i)) :=
    Complex.conjCLE.contDiff.comp (contDiff_apply ℝ ℂ i)
  exact ((contDiff_const.mul hs).mul (contDiff_apply ℝ ℂ j)).smul contDiff_const

def xfPi (π' : Mx k r → (Wq →L[ℂ] Wq)) (B0 : Fin k → Fin (2 * r + k + 1) → ℂ) (w : ℂ) (ν : Fin k → ℂ) :
    C6.EndH Wp Wq :=
  (ContinuousLinearMap.compL ℂ Wq Wq Wp).flip (capV π' B0 w ν)

/- English proof (translation)
Conclude with `(((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip).restrictScalars ℝ).contDiff.comp (xf_capV_cd π' B0 w)`.
-/
theorem xf_Pi_cd (π' : Mx k r → (Wq →L[ℂ] Wq)) (B0 : Fin k → Fin (2 * r + k + 1) → ℂ) (w : ℂ) :
    ContDiff ℝ ∞ (xfPi (Wp := Wp) π' B0 w) := by
  exact (((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip).restrictScalars ℝ).contDiff.comp (xf_capV_cd π' B0 w)

/- English proof (translation)
Take `⟨q, -, hq⟩` from `h`. Establish `hP : P = fun g => MvPolynomial.eval (Sum.elim (fun x => g x.1 x.2) (fun x => star (g x.1 x.2))) q` using `funext hq`. Substitute `hP` using the available equality. Use `clear hq`. Proceed by induction on `q using MvPolynomial.induction_on`.

Use `next a =>`. Simplify using `only [MvPolynomial.eval_C]`. Conclude with `contDiff_const`. Use `next p q hp hq =>`. Simplify using `only [map_add]`.

Conclude with `hp.add hq`. Use `next p i hp =>`. Simplify using `only [map_mul, MvPolynomial.eval_X]`. Use `hp.mul ?_` and prove the remaining obligations. Break down `i with ⟨a, b⟩ | ⟨a, b⟩` into its components or cases.

Apply the tactic sequence `exact JCx1.contDiff_entry a b`. Apply the tactic sequence `exact Complex.conjCLE.contDiff.comp (JCx1.contDiff_entry a b)`.
-/
private theorem contDiff_of_isPolyDeg' {k r κ : ℕ} {P : B.Mat k r → ℂ} (h : U.IsPolyDeg κ P) : ContDiff ℝ ∞ P := by
  obtain ⟨q, -, hq⟩ := h
  have hP : P = fun g => MvPolynomial.eval (Sum.elim (fun x => g x.1 x.2) (fun x => star (g x.1 x.2))) q := funext hq
  subst hP
  clear hq
  induction q using MvPolynomial.induction_on
  next a =>
    simp only [MvPolynomial.eval_C]
    exact contDiff_const
  next p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  next p i hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    refine hp.mul ?_
    rcases i with ⟨a, b⟩ | ⟨a, b⟩
    · exact JCx1.contDiff_entry a b
    · exact Complex.conjCLE.contDiff.comp (JCx1.contDiff_entry a b)

/- English proof (translation)
Take `⟨hom, hsq, -, -⟩` from `hOm k r Wp Wq Bs B0 hB0`. Establish `hGc : ContDiff ℝ ∞ (fun g : B.Mat k r => ((Gf k r Bs.z Bs.z' g : ℝ) : ℂ))` using `Complex.ofRealCLM.contDiff.comp (JCx1.contDiff_Gf Bs.z Bs.z')`. Establish `hoc : ∀ a, ContDiff ℝ ∞ (fun g => omC Bs B0 g a)` using `fun a => contDiff_of_isPolyDeg' (hom a)`. Use `⟨fun g₀ hg₀ => ?_, fun ε hε i => ?_⟩` and prove the remaining obligations. Use `⟨{g | Gf k r Bs.z Bs.z' g₀ / 2 < Gf k r Bs.z Bs.z' g}, fun g => xfPi Bs.π' B0 w (AdmissibleLieWords.utv (Gf k r Bs.z Bs.z' g₀) (Tz k r Bs.z') (Gf k r Bs.z Bs.z') (omC Bs B0) g), isOpen_lt continuous_const (JCx1.contDiff_Gf Bs.z Bs.z').continuous, half_lt_self hg₀.2, ?_, fun g hg …` and prove the remaining obligations.

Conclude with `((xf_Pi_cd Bs.π' B0 w).comp (AdmissibleLieWords.utv_cd (T := Tz k r Bs.z') hg₀.2 hGc hoc)).contDiffOn`. Conclude with `congrArg (xfPi (Wp := Wp) Bs.π' B0 w) (AdmissibleLieWords.utv_eq hg₀.2 Bs.T'_pos _ _ hg)`. Conclude with `fibre_cost_estimate k r k k (omC Bs B0) (omC Bs B0) (Gf k r Bs.z Bs.z') (Tz k r Bs.z') (Tz k r Bs.z') (C6.EndH Wp Wq) (fun p => xfPi Bs.π' B0 w p.1) Set.univ hom hom (gram_function_polynomial k r Bs.z Bs.z') Bs.T'_pos Bs.T'_pos hsq hsq isOpen_univ (Set.subset_univ _) ((xf_Pi_cd B …`.
-/
theorem xf_bound (hOm : OmFacts) (Bs : B.RealPlaceData k r Wp Wq) {B0 : Fin k → Fin (2 * r + k + 1) → ℂ}
    (hB0 : IsFrameOf k r [Bs.z'] B0) (w : ℂ) : C6.FibBound Bs (xFib Bs B0 w) := by
  obtain ⟨hom, hsq, -, -⟩ := hOm k r Wp Wq Bs B0 hB0
  have hGc : ContDiff ℝ ∞ (fun g : B.Mat k r => ((Gf k r Bs.z Bs.z' g : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (JCx1.contDiff_Gf Bs.z Bs.z')
  have hoc : ∀ a, ContDiff ℝ ∞ (fun g => omC Bs B0 g a) := fun a => contDiff_of_isPolyDeg' (hom a)
  refine ⟨fun g₀ hg₀ => ?_, fun ε hε i => ?_⟩
  · refine ⟨{g | Gf k r Bs.z Bs.z' g₀ / 2 < Gf k r Bs.z Bs.z' g},
      fun g => xfPi Bs.π' B0 w (AdmissibleLieWords.utv (Gf k r Bs.z Bs.z' g₀) (Tz k r Bs.z') (Gf k r Bs.z Bs.z') (omC Bs B0) g),
      isOpen_lt continuous_const (JCx1.contDiff_Gf Bs.z Bs.z').continuous, half_lt_self hg₀.2, ?_, fun g hg _ => ?_⟩
    · exact ((xf_Pi_cd Bs.π' B0 w).comp (AdmissibleLieWords.utv_cd (T := Tz k r Bs.z') hg₀.2 hGc hoc)).contDiffOn
    · exact congrArg (xfPi (Wp := Wp) Bs.π' B0 w) (AdmissibleLieWords.utv_eq hg₀.2 Bs.T'_pos _ _ hg)
  · exact fibre_cost_estimate k r k k (omC Bs B0) (omC Bs B0) (Gf k r Bs.z Bs.z') (Tz k r Bs.z') (Tz k r Bs.z')
      (C6.EndH Wp Wq) (fun p => xfPi Bs.π' B0 w p.1) Set.univ hom hom (gram_function_polynomial k r Bs.z Bs.z')
      Bs.T'_pos Bs.T'_pos hsq hsq isOpen_univ (Set.subset_univ _)
      ((xf_Pi_cd Bs.π' B0 w).comp contDiff_fst).contDiffOn ε hε i

/- English proof (translation)
Take `⟨-, hsq, hcov, -⟩` from `hOm k r Wp Wq Bs B0 hB0`. Introduce `p hp g hg J`. Establish `hGf : Gf k r Bs.z Bs.z' (B.sgs p g) = Gf k r Bs.z Bs.z' g` using `JCx1.needs.gf_sgs Bs hp g`. Establish `hsum : ∀ (c : ℂ) (v : Fin k → ℂ), ∑ j, (c • v) j • B0 j = c • ∑ j, v j • B0 j`. Introduce `c v`.

Simplify using `only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]`. Establish `hE` using `hCapE Wq k r Bs.z' Bs.π' B0 (C6.unitOf (Tz k r Bs.z') (Gf k r Bs.z Bs.z' g) (omC Bs B0 g)) (C6.unitOf (Tz k r Bs.z') (Gf k r Bs.z Bs.z' (B.sgs p g)) (omC Bs B0 (B.sgs p g))) (Matrix.of p.2.1) Bs.k_pos Bs.z'_mem Bs.T'_pos ⟨Bs.π'_rep, Bs.π'_cont⟩ hB0 (AdmissibleLieWords.sq2_unitOf_ …`. Use extensionality with `v`. Establish `hv` using `congrArg (fun T : Wq →L[ℂ] Wq => T v) hE`. Simplify using `only [ContinuousLinearMap.comp_apply] at hv`.

Simplify using `only [xFib, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply, hv]`.
-/
theorem xf_equiv (hOm : OmFacts) (hCapE : CapVEquiv) (Bs : B.RealPlaceData k r Wp Wq) {B0 : Fin k → Fin (2 * r + k + 1) → ℂ}
    (hB0 : IsFrameOf k r [Bs.z'] B0) (w : ℂ) :
    ∀ p, Bs.inSS p → ∀ g ∈ C6.domL Bs ∅, ∀ J : Wq →L[ℂ] Wp,
      xFib Bs B0 w g ((Bs.π (Matrix.of p.1.1)).comp (J.comp (Bs.π' (Matrix.of p.2.1)⁻¹))) =
        (Bs.π (Matrix.of p.1.1)).comp ((xFib Bs B0 w (B.sgs p g) J).comp (Bs.π' (Matrix.of p.2.1)⁻¹)) := by
  obtain ⟨-, hsq, hcov, -⟩ := hOm k r Wp Wq Bs B0 hB0
  intro p hp g hg J
  have hGf : Gf k r Bs.z Bs.z' (B.sgs p g) = Gf k r Bs.z Bs.z' g := JCx1.needs.gf_sgs Bs hp g
  have hsum : ∀ (c : ℂ) (v : Fin k → ℂ), ∑ j, (c • v) j • B0 j = c • ∑ j, v j • B0 j := by
    intro c v
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
  have hE := hCapE Wq k r Bs.z' Bs.π' B0 (C6.unitOf (Tz k r Bs.z') (Gf k r Bs.z Bs.z' g) (omC Bs B0 g))
    (C6.unitOf (Tz k r Bs.z') (Gf k r Bs.z Bs.z' (B.sgs p g)) (omC Bs B0 (B.sgs p g))) (Matrix.of p.2.1)
    Bs.k_pos Bs.z'_mem Bs.T'_pos ⟨Bs.π'_rep, Bs.π'_cont⟩ hB0
    (AdmissibleLieWords.sq2_unitOf_eq_one_of_sq2_eq_div Bs.T'_pos hg.2.1 (hsq g hg.1)) hp.2.2.1
    (by simp only [C6.unitOf, hsum, hGf, hcov p hp g hg, Matrix.mulVec_smul]) w
  ext v
  have hv := congrArg (fun T : Wq →L[ℂ] Wq => T v) hE
  simp only [ContinuousLinearMap.comp_apply] at hv
  simp only [xFib, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply, hv]

end fib

end TLC

/- English proof (translation)
Establish `hH : ∀ i j : Fin (2 * r + k + 1), star (Hpk k r i j) = Hpk k r j i`. Introduce `i j`. Simplify using `only [Hpk, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | (exfalso; omega) | norm_num`. Simplify using `only [herm, dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', star_star, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hH]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem herm_Hpk_swap {k r : ℕ} (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) w v = star (herm (Hpk k r) v w) := by
  have hH : ∀ i j : Fin (2 * r + k + 1), star (Hpk k r i j) = Hpk k r j i := by
    intro i j
    simp only [Hpk, Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | norm_num
  simp only [herm, dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hH]
  ring

/- English proof (translation)
Take `⟨n, rfl⟩ : ∃ n, k = n + 1` from `⟨k - 1, by omega⟩`. Establish `hbw : ∀ i : Fin (2 * r + (n + 1) + 1), r ≤ i.val → i.val ≤ r + (n + 1) → inWb (n + 1) r (bvec i)`. Introduce `i h1 h2 j hj`. Simplify using `only [bvec, Pi.single_apply]`. Use `split_ifs with h`.

Substitute `h` using the available equality. Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression. Choose the witnesses or unpack the hypotheses as in `⟨a, ha, hind⟩ : ∃ a, inWb (n + 1) r a ∧ ∀ c : ℂ, a ≠ c • z' := by`. Take `⟨i0, hi0⟩ : ∃ i : Fin (2 * r + (n + 1) + 1), i.val = r` from `⟨⟨r, by omega⟩, rfl⟩`.

Take `⟨i1, hi1⟩ : ∃ i : Fin (2 * r + (n + 1) + 1), i.val = r + 1` from `⟨⟨r + 1, by omega⟩, rfl⟩`. Establish `hne : i0 ≠ i1` using `fun h => by rw [h] at hi0; omega`. Distinguish the cases in `h : ∀ c : ℂ, bvec i0 ≠ c • z'`. Conclude with `⟨_, hbw i0 (by omega) (by omega), h⟩`. Simplify using `only [ne_eq, not_forall, not_not] at h`.

Take `⟨c0, h0⟩` from `h`. Use `⟨_, hbw i1 (by omega) (by omega), fun c hc => ?_⟩` and prove the remaining obligations. Establish `e0` using `congrFun h0 i0`. Establish `e1` using `congrFun hc i0`. Establish `e2` using `congrFun hc i1`.

Simplify using `only [bvec, Pi.single_apply, Pi.smul_apply, smul_eq_mul, if_neg hne] at e0 e1 e2`. Establish `hz0 : z' i0 ≠ 0` using `fun h => by rw [h, mul_zero] at e0; exact one_ne_zero e0`. Establish `hc0 : c = 0` using `(mul_eq_zero.mp e1.symm).resolve_right hz0`. Rewrite `e2` using `[hc0, zero_mul]`. Conclude with `one_ne_zero e2`.

Take `⟨e, he, hez, hee, -⟩` from `Q.LieAlgebraWeightVectors.exists_unit hz' hT' ha hind`. Take `⟨Bs, hBs⟩` from `Q.LieAlgebraWeightVectors.exists_frame he hz' hT'`. Use `⟨Fin.cons e (fun i => Bs (Fin.cast (by omega) i)), fun i => ?_, fun i j => ?_, fun i v hv => ?_⟩` and prove the remaining obligations. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `using he`.

Simplify using `using hBs.1 _`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j`. Simplify using `using hee`. Simplify using `only [Fin.cons_zero, Fin.cons_succ]`. Rewrite using `[herm_Hpk_swap _ e, hBs.2.2 _ e (by simp), star_zero, if_neg (Fin.succ_ne_zero j).symm]`.

Simplify using `only [Fin.cons_zero, Fin.cons_succ]`. Rewrite using `[hBs.2.2 _ e (by simp), if_neg (Fin.succ_ne_zero i)]`. Simplify using `only [Fin.cons_succ]`. Rewrite using `[hBs.2.1]`. Simplify using `[Fin.ext_iff]`.

Simplify using `only [List.mem_cons, List.not_mem_nil, or_false] at hv`. Substitute `hv` using the available equality. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `using hez`. Simplify using `using hBs.2.2 _ _ (by simp)`.
-/
private theorem exists_isFrameOf_singleton_of_Tz_pos {k r : ℕ} {z' : Fin (2 * r + k + 1) → ℂ} (hk : 1 ≤ k) (hz' : inWb k r z')
    (hT' : 0 < Tz k r z') : ∃ B0 : Fin k → Fin (2 * r + k + 1) → ℂ, IsFrameOf k r [z'] B0 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hbw : ∀ i : Fin (2 * r + (n + 1) + 1), r ≤ i.val → i.val ≤ r + (n + 1) → inWb (n + 1) r (bvec i) := by
    intro i h1 h2 j hj
    simp only [bvec, Pi.single_apply]
    split_ifs with h
    · subst h
      omega
    · rfl
  obtain ⟨a, ha, hind⟩ : ∃ a, inWb (n + 1) r a ∧ ∀ c : ℂ, a ≠ c • z' := by
    obtain ⟨i0, hi0⟩ : ∃ i : Fin (2 * r + (n + 1) + 1), i.val = r := ⟨⟨r, by omega⟩, rfl⟩
    obtain ⟨i1, hi1⟩ : ∃ i : Fin (2 * r + (n + 1) + 1), i.val = r + 1 := ⟨⟨r + 1, by omega⟩, rfl⟩
    have hne : i0 ≠ i1 := fun h => by rw [h] at hi0; omega
    by_cases h : ∀ c : ℂ, bvec i0 ≠ c • z'
    · exact ⟨_, hbw i0 (by omega) (by omega), h⟩
    · simp only [ne_eq, not_forall, not_not] at h
      obtain ⟨c0, h0⟩ := h
      refine ⟨_, hbw i1 (by omega) (by omega), fun c hc => ?_⟩
      have e0 := congrFun h0 i0
      have e1 := congrFun hc i0
      have e2 := congrFun hc i1
      simp only [bvec, Pi.single_apply, Pi.smul_apply, smul_eq_mul, if_neg hne] at e0 e1 e2
      have hz0 : z' i0 ≠ 0 := fun h => by rw [h, mul_zero] at e0; exact one_ne_zero e0
      have hc0 : c = 0 := (mul_eq_zero.mp e1.symm).resolve_right hz0
      rw [hc0, zero_mul] at e2
      exact one_ne_zero e2
  obtain ⟨e, he, hez, hee, -⟩ := Q.LieAlgebraWeightVectors.exists_unit hz' hT' ha hind
  obtain ⟨Bs, hBs⟩ := Q.LieAlgebraWeightVectors.exists_frame he hz' hT'
  refine ⟨Fin.cons e (fun i => Bs (Fin.cast (by omega) i)), fun i => ?_, fun i j => ?_, fun i v hv => ?_⟩
  · refine Fin.cases ?_ (fun j => ?_) i
    · simpa using he
    · simpa using hBs.1 _
  · refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simpa using hee
    · simp only [Fin.cons_zero, Fin.cons_succ]
      rw [herm_Hpk_swap _ e, hBs.2.2 _ e (by simp), star_zero, if_neg (Fin.succ_ne_zero j).symm]
    · simp only [Fin.cons_zero, Fin.cons_succ]
      rw [hBs.2.2 _ e (by simp), if_neg (Fin.succ_ne_zero i)]
    · simp only [Fin.cons_succ]
      rw [hBs.2.1]
      simp [Fin.ext_iff]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    subst hv
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hez
    · simpa using hBs.2.2 _ _ (by simp)

/- English proof (translation)
Introduce `hCell hOm hCapF hCapE Wp Wq _ _ _ _ _ _ P Bs X`. Take `⟨B0, hB0⟩` from `exists_isFrameOf_singleton_of_Tz_pos Bs.k_pos Bs.z'_mem Bs.T'_pos`. Conclude with `⟨B0, hB0, fun Y => ⟨TLC.xf_bound hOm Bs hB0 _, TLC.xf_equiv hOm hCapE Bs hB0 _, fun Φ x hx => TLC.xf_rad hCell hOm hCapF Bs X hB0 Y Φ x hx⟩⟩`.
-/
theorem x_fibre_of_parts : TL.XFibOfParts := by
  intro hCell hOm hCapF hCapE Wp Wq _ _ _ _ _ _ P Bs X
  obtain ⟨B0, hB0⟩ := exists_isFrameOf_singleton_of_Tz_pos Bs.k_pos Bs.z'_mem Bs.T'_pos
  exact ⟨B0, hB0, fun Y => ⟨TLC.xf_bound hOm Bs hB0 _, TLC.xf_equiv hOm hCapE Bs hB0 _,
    fun Φ x hx => TLC.xf_rad hCell hOm hCapF Bs X hB0 Y Φ x hx⟩⟩

end Formalism.FourierDecayAlt.P
