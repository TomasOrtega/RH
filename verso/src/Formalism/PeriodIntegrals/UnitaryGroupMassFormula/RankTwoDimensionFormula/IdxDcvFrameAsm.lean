import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxDcvFrame
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxAFrG
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxAJacE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IdxDSI

noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp
  PI.UnitaryDimensionFormula.unitaryCongruence PI.UnitaryDimensionFormula.NormCutK PI.UnitaryDimensionFormula.FrameX

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `D X u e hE`. Use `set eps := epsX X e with heps`. Use `set G : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := Matrix.of fun l j => Formalism.UG.hform (sigA X.B.I) (JA X.B.I) (cv e u l) (bv e u j) with hGdef`. Establish `hGint : ∀ l j, G l j ∈ IntAf X.B.I.F X.B.I.E` using `fun l j => hA_int X.B.I (cv_Lf hJ hE u l) (bv_Lf hJ hE u j)`. Establish `hGc : ∀ l j, ZMod' X.B.I X.B.g (G l j - if l = j then eps else 0)` using `fun l j => G_cong hJ hE u l j`.

Take `⟨y, hy, hyE⟩` from `hG D X e hE G hGint hGc`. Use `set M := (eps * y) • G.adjugate with hMdef`. Establish `hM : M * G = eps • (1 : Matrix (Fin D.R.k) (Fin D.R.k) _)` using `FrameAlg.inv_on G eps y hyE`. Establish `hMint : ∀ i l, M i l ∈ IntAf X.B.I.F X.B.I.E` using `fun i l => mul_mem (mul_mem (eps_int hE) hy) (int_adj hGint i l)`. Establish `hMe : ∀ i l, M i l * eps = M i l` using `fun i l => by show eps * y * G.adjugate i l * eps = eps * y * G.adjugate i l`.

Use `eps_idem (X := X) hE.2.1` as an intermediate fact. Take the linear combination `(y * G.adjugate i l) * this`. Establish `hse : sigA X.B.I eps * sigA X.B.I eps = sigA X.B.I eps`. Rewrite using `[← map_mul, eps_idem hE.2.1]`. Use `⟨bv e u, fun i => ∑ l, sigA X.B.I (M i l) • cv e u l, ⟨eps_idem hE.2.1, eps_orth, fun i => ?_, fun i => ?_, fun i j => ?_⟩, fun i => ⟨bv_Lf hJ hE u i, ?_⟩, fun i w hw => ⟨?_, ?_⟩, fun i j => ⟨?_, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[bv, smul_smul, eps_idem hE.2.1]`. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[cv, smul_comm (sigA X.B.I eps) (sigA X.B.I (M i l)), smul_smul (sigA X.B.I eps), hse]`. Conclude with `FrameAlg.dual_fix (sigA X.B.I) (JA X.B.I) (hS X.B.I).1 (bv e u) (cv e u) eps M hM i j`.

Conclude with `Submodule.sum_mem _ fun l _ => smul_int_mem (sigA_mem X.B.I (hMint i l)) (cv_Lf hJ hE u l)`. Rewrite using `[hA_symm X.B.I w, bv, hA_smul_right]`. Use `fixV_perp hS hE.2.1 u (X.bw i) w hw` as an intermediate fact. Rewrite using `[eps_eq, show E1 X e * X.ew * hA X.B.I w (Qv X e u (X.bw i)) = X.ew * (E1 X e * hA X.B.I w (Qv X e u (X.bw i))) by ring, this, mul_zero, map_zero]`. Rewrite using `[hA_symm X.B.I w, ← hL_apply, map_sum]`.

Establish `hz : ∀ l, hL X.B.I w (sigA X.B.I (M i l) • cv e u l) = 0` using `fun l => by`. Rewrite using `[hL_apply, hA_smul_right, cv, hA_smul_right, sig_eps]`. Use `fixV_perp hS hE.2.1 u (X.bwd l) w hw` as an intermediate fact. Rewrite using `[show sigA X.B.I (M i l) * (E1 X e * sigA X.B.I X.ew * hA X.B.I w (Qv X e u (X.bwd l))) = sigA X.B.I (M i l) * sigA X.B.I X.ew * (E1 X e * hA X.B.I w (Qv X e u (X.bwd l))) by ring, this, mul_zero]`. Rewrite using `[Finset.sum_eq_zero fun l _ => hz l, map_zero]`.

Establish `hsum : hA X.B.I (∑ l, sigA X.B.I (M i l) • cv e u l) (X.bw j) = ∑ l, M i l * hA X.B.I (cv e u l) (X.bw j)` using `by show Formalism.UG.hform (sigA X.B.I) (JA X.B.I) _ _ = _`. Rewrite using `[FrameAlg.h_sum_left]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[FrameAlg.h_smul_left, sigA_sigA]`. Both sides reduce to the same expression.

Establish `h1 : ZMod' X.B.I X.B.g (∑ l, M i l * (hA X.B.I (cv e u l) (X.bw j) - if l = j then eps else 0))` using `Z_sum X.B.I X.B.g _ _ fun l _ => Z_smul X.B.I X.B.g (hMint i l) (cbw_cong hJ hE u l j)`. Establish `h2 : ZMod' X.B.I X.B.g (∑ l, M i l * (G l j - if l = j then eps else 0))` using `Z_sum X.B.I X.B.g _ _ fun l _ => Z_smul X.B.I X.B.g (hMint i l) (hGc l j)`. Establish `hMG : ∑ l, M i l * G l j = if i = j then eps else 0`. Use `congrFun (congrFun hM i) j` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]`.

Establish `hs : ∀ (F : Fin D.R.k → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F), ∑ l, M i l * (F l - if l = j then eps else 0) = ∑ l, M i l * F l - M i j` using `fun F => by`. Simplify using `only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, hMe]`. Rewrite `h2` using `[hs, hMG]`. Rewrite `h1` using `[hs]`. Use `to_ew hE (hA_int X.B.I (Submodule.sum_mem _ fun l _ => smul_int_mem (sigA_mem X.B.I (hMint i l)) (cv_Lf hJ hE u l)) ((frame_Lf X).2.2.2.1 j)) (i = j) ?_` and prove the remaining obligations.

Rewrite using `[hsum]`. Use `Z_sub X.B.I X.B.g h1 h2` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Conclude with `to_ew hE (hA_int X.B.I ((frame_Lf X).2.2.2.2 i) (bv_Lf hJ hE u j)) (i = j) (bwdb_cong hJ hE u i j)`.
-/
theorem idxDFrame_of (hS : IdxDSig) (hJ : IdxDJacE) (hG : FrGram) : IdxDFrame := by
  intro D X u e hE
  set eps := epsX X e with heps
  set G : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) :=
    Matrix.of fun l j => Formalism.UG.hform (sigA X.B.I) (JA X.B.I) (cv e u l) (bv e u j) with hGdef
  have hGint : ∀ l j, G l j ∈ IntAf X.B.I.F X.B.I.E := fun l j =>
    hA_int X.B.I (cv_Lf hJ hE u l) (bv_Lf hJ hE u j)
  have hGc : ∀ l j, ZMod' X.B.I X.B.g (G l j - if l = j then eps else 0) := fun l j => G_cong hJ hE u l j
  obtain ⟨y, hy, hyE⟩ := hG D X e hE G hGint hGc
  set M := (eps * y) • G.adjugate with hMdef
  have hM : M * G = eps • (1 : Matrix (Fin D.R.k) (Fin D.R.k) _) := FrameAlg.inv_on G eps y hyE
  have hMint : ∀ i l, M i l ∈ IntAf X.B.I.F X.B.I.E := fun i l =>
    mul_mem (mul_mem (eps_int hE) hy) (int_adj hGint i l)
  have hMe : ∀ i l, M i l * eps = M i l := fun i l => by
    show eps * y * G.adjugate i l * eps = eps * y * G.adjugate i l
    have := eps_idem (X := X) hE.2.1
    linear_combination (y * G.adjugate i l) * this
  have hse : sigA X.B.I eps * sigA X.B.I eps = sigA X.B.I eps := by
    rw [← map_mul, eps_idem hE.2.1]
  refine ⟨bv e u, fun i => ∑ l, sigA X.B.I (M i l) • cv e u l, ⟨eps_idem hE.2.1, eps_orth, fun i => ?_,
    fun i => ?_, fun i j => ?_⟩, fun i => ⟨bv_Lf hJ hE u i, ?_⟩, fun i w hw => ⟨?_, ?_⟩, fun i j => ⟨?_, ?_⟩⟩
  · rw [bv, smul_smul, eps_idem hE.2.1]
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [cv, smul_comm (sigA X.B.I eps) (sigA X.B.I (M i l)), smul_smul (sigA X.B.I eps), hse]
  · exact FrameAlg.dual_fix (sigA X.B.I) (JA X.B.I) (hS X.B.I).1 (bv e u) (cv e u) eps M hM i j
  · exact Submodule.sum_mem _ fun l _ => smul_int_mem (sigA_mem X.B.I (hMint i l)) (cv_Lf hJ hE u l)
  · rw [hA_symm X.B.I w, bv, hA_smul_right]
    have := fixV_perp hS hE.2.1 u (X.bw i) w hw
    rw [eps_eq, show E1 X e * X.ew * hA X.B.I w (Qv X e u (X.bw i)) =
      X.ew * (E1 X e * hA X.B.I w (Qv X e u (X.bw i))) by ring, this, mul_zero, map_zero]
  · rw [hA_symm X.B.I w, ← hL_apply, map_sum]
    have hz : ∀ l, hL X.B.I w (sigA X.B.I (M i l) • cv e u l) = 0 := fun l => by
      rw [hL_apply, hA_smul_right, cv, hA_smul_right, sig_eps]
      have := fixV_perp hS hE.2.1 u (X.bwd l) w hw
      rw [show sigA X.B.I (M i l) * (E1 X e * sigA X.B.I X.ew * hA X.B.I w (Qv X e u (X.bwd l))) =
        sigA X.B.I (M i l) * sigA X.B.I X.ew * (E1 X e * hA X.B.I w (Qv X e u (X.bwd l))) by ring, this, mul_zero]
    rw [Finset.sum_eq_zero fun l _ => hz l, map_zero]
  ·
    have hsum : hA X.B.I (∑ l, sigA X.B.I (M i l) • cv e u l) (X.bw j) =
        ∑ l, M i l * hA X.B.I (cv e u l) (X.bw j) := by
      show Formalism.UG.hform (sigA X.B.I) (JA X.B.I) _ _ = _
      rw [FrameAlg.h_sum_left]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [FrameAlg.h_smul_left, sigA_sigA]; rfl
    have h1 : ZMod' X.B.I X.B.g (∑ l, M i l * (hA X.B.I (cv e u l) (X.bw j) - if l = j then eps else 0)) :=
      Z_sum X.B.I X.B.g _ _ fun l _ => Z_smul X.B.I X.B.g (hMint i l) (cbw_cong hJ hE u l j)
    have h2 : ZMod' X.B.I X.B.g (∑ l, M i l * (G l j - if l = j then eps else 0)) :=
      Z_sum X.B.I X.B.g _ _ fun l _ => Z_smul X.B.I X.B.g (hMint i l) (hGc l j)
    have hMG : ∑ l, M i l * G l j = if i = j then eps else 0 := by
      have := congrFun (congrFun hM i) j
      simpa [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] using this
    have hs : ∀ (F : Fin D.R.k → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F),
        ∑ l, M i l * (F l - if l = j then eps else 0) = ∑ l, M i l * F l - M i j := fun F => by
      simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        if_true, hMe]
    rw [hs, hMG] at h2
    rw [hs] at h1
    refine to_ew hE (hA_int X.B.I (Submodule.sum_mem _ fun l _ =>
      smul_int_mem (sigA_mem X.B.I (hMint i l)) (cv_Lf hJ hE u l)) ((frame_Lf X).2.2.2.1 j)) (i = j) ?_
    rw [hsum]
    have := Z_sub X.B.I X.B.g h1 h2
    convert this using 1
    ring
  · exact to_ew hE (hA_int X.B.I ((frame_Lf X).2.2.2.2 i) (bv_Lf hJ hE u j)) (i = j) (bwdb_cong hJ hE u i j)

/- English proof (translation)
The claim follows from `idxDFrame_of idxDSig idxDJacE frGram`.
-/
theorem idxDFrame : IdxDFrame := idxDFrame_of idxDSig idxDJacE frGram

end PI.UnitaryDimensionFormula
