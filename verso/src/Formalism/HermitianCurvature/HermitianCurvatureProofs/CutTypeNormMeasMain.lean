import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutTypeNormMeasV

namespace Formalism.FourierDecayAlt.P.CutBP.TNM

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory Matrix

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section aux

variable {k r : ℕ}

/- English proof (translation)
Introduce `i hi`. Establish `hzi : z i = 0` using `hz i hi`. Simplify using `only [D.prW]`. Simplify using `only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hzi, mul_zero, sub_zero]`. Use `split_ifs with h`.

It suffices to derive a contradiction. Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression.
-/
theorem prW_inWb {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    inWb k r (D.prW k r z v) := by
  intro i hi
  have hzi : z i = 0 := hz i hi
  simp only [D.prW]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hzi, mul_zero, sub_zero]
  split_ifs with h
  · exfalso; omega
  · rfl

/- English proof (translation)
Establish `key : ∀ (x y : Fin (2 * r + k + 1) → ℂ) (c : ℂ), herm (Hpk k r) (x - c • y) z = herm (Hpk k r) x z - c * herm (Hpk k r) y z`. Introduce `x y c`. Simplify using `only [herm, Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul]`. Simplify using `only [D.prW]`. Rewrite using `[key, div_mul_cancel₀ _ hzz, sub_self]`.
-/
theorem projection_hermitian_orthogonal (z v : Fin (2 * r + k + 1) → ℂ) (hzz : herm (Hpk k r) z z ≠ 0) :
    herm (Hpk k r) (D.prW k r z v) z = 0 := by
  have key : ∀ (x y : Fin (2 * r + k + 1) → ℂ) (c : ℂ),
      herm (Hpk k r) (x - c • y) z = herm (Hpk k r) x z - c * herm (Hpk k r) y z := by
    intro x y c
    simp only [herm, Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  simp only [D.prW]
  rw [key, div_mul_cancel₀ _ hzz, sub_self]

def prWL (z : Fin (2 * r + k + 1) → ℂ) : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] (Fin (2 * r + k + 1) → ℂ) where
  toFun := D.prW k r z
  map_add' := Formalism.FourierDecayAlt.P.Dx2.DF.prW_add z
  map_smul' c v := Formalism.FourierDecayAlt.P.Dx2.DF.prW_smul z v c

/- English proof (translation)
The claim follows from `(prWL (k := k) (r := r) z).continuous_of_finiteDimensional`.
-/
theorem prW_cont (z : Fin (2 * r + k + 1) → ℂ) : Continuous (D.prW k r z) :=
  (prWL (k := k) (r := r) z).continuous_of_finiteDimensional

/- English proof (translation)
Establish `hZ : Continuous (fun γ : B.Mat k r => Zhat k r S.z S.z' γ)`. Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Simplify using `only [Zhat, herm]`. Conclude with `continuous_const.dotProduct (continuous_const.matrix_mulVec (continuous_id.matrix_mulVec continuous_const))`. Use `show Continuous (fun γ : B.Mat k r => ∑ j, (Zhat k r S.z S.z' γ).adjugate j (Fin.last r) • (γ *ᵥ fvec k r S.z' j))`.

Use `continuous_finset_sum _ fun j _ => ?_` and prove the remaining obligations. Conclude with `((continuous_apply (Fin.last r)).comp ((continuous_apply j).comp hZ.matrix_adjugate)).smul (continuous_id.matrix_mulVec continuous_const)`.
-/
theorem cofR_cont {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (S : B.RealPlaceData k r Wp Wq) : Continuous (D.cofR S) := by
  have hZ : Continuous (fun γ : B.Mat k r => Zhat k r S.z S.z' γ) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Zhat, herm]
    exact continuous_const.dotProduct (continuous_const.matrix_mulVec (continuous_id.matrix_mulVec continuous_const))
  show Continuous (fun γ : B.Mat k r =>
    ∑ j, (Zhat k r S.z S.z' γ).adjugate j (Fin.last r) • (γ *ᵥ fvec k r S.z' j))
  refine continuous_finset_sum _ fun j _ => ?_
  exact ((continuous_apply (Fin.last r)).comp ((continuous_apply j).comp hZ.matrix_adjugate)).smul
    (continuous_id.matrix_mulVec continuous_const)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem gd_eq {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} (p : KB.Pl P Wp Wq)
    (c : Fin (P.r + 1) → ℂ) :
    gd p c = B.gq p.T.base ((fun i : Fin P.r => c i.castSucc), c (Fin.last P.r)) := rfl

end aux

section main

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P p Y A hThr hY ρ`. Take `⟨hmU, hmW, -, -, -, hzeq, -⟩` from `Formalism.FourierDecayAlt.P.Topx1.vecw_base_parts p.T.base p.hF`. Take `⟨hν, hνz, hνν, -, -⟩` from `id p.hF`. Establish `he : inWb P.k P.r (p.m₀ *ᵥ p.ν')` using `hmW p.ν' hν`. Establish `hee : herm (Hpk P.k P.r) (p.m₀ *ᵥ p.ν') (p.m₀ *ᵥ p.ν') = 1`.

Rewrite using `[Formalism.FourierDecayAlt.P.Dx2.DF.herm_m0_mulVec_invariant p.m₀ hmU]`. Conclude with `hνν`. Establish `hez : herm (Hpk P.k P.r) (p.m₀ *ᵥ p.ν') p.T.base.z = 0`. Rewrite using `[hzeq, Formalism.FourierDecayAlt.P.Qx8.herm_smul_right', Formalism.FourierDecayAlt.P.Dx2.DF.herm_m0_mulVec_invariant p.m₀ hmU, hνz, mul_zero]`. Establish `hzW : inWb P.k P.r p.T.base.z` using `(Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z p.T.base).1`.

Establish `hzz : herm (Hpk P.k P.r) p.T.base.z p.T.base.z ≠ 0`. Rewrite using `[Formalism.FourierDecayAlt.P.Dx2.DF.herm_self_alt]`. Use `p.T.base.T_pos` as an intermediate fact. Introduce `h`. Establish `h2` using `congrArg Complex.re h`.

Simplify using `at h2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hzneg : (herm (Hpk P.k P.r) p.T.base.z p.T.base.z).re < 0`. Rewrite using `[Formalism.FourierDecayAlt.P.Dx2.DF.herm_self_alt]`. Use `p.T.base.T_pos` as an intermediate fact.

Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Establish `he0 : p.m₀ *ᵥ p.ν' ≠ 0`. Introduce `h0`. Rewrite `hee` using `[h0]`.

Simplify using `[herm] at hee`. Take `⟨H, hHm, hHU, hHe⟩` from `hHM P.k P.r p.T.base.z (p.m₀ *ᵥ p.ν') hzW hzneg he hez hee`. Use `set TT : ℝ := Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' with hTT`. Use `set D0 : Set (Fin (P.r + 1) → ℂ) := {c | (∀ i, c i ≠ 0) ∧ TT < Complex.normSq (c (Fin.last P.r))} with hD0def`. Use `set Φ : (Fin (P.r + 1) → ℂ) → ℝ := fun c => ‖B.hsVec ((p.TP.E ρ).comp ((p.T.base.π (H (wq p c))).comp (B.JF p.T.base Y (gd p c))))‖ with hΦ`.

Establish `hGform : ∀ c : Fin (P.r + 1) → ℂ, TBB.Gp p (TBB.bigPt P.r c) = Complex.normSq (∏ a : Fin P.r, c a.castSucc) * (Complex.normSq (c (Fin.last P.r)) - TT)`. Introduce `c`. Use `show D.ptG TT P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c) = _`. Unfold `D.ptG`. Rewrite using `[Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one, Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc, Complex.normSq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h1 : ∀ c ∈ D0, ‖B.hsVec ((p.TP.E ρ).comp (p.V Y (TBB.bigPt P.r c)))‖ = Φ c`. Introduce `c hc`. Take `⟨hd, hζ⟩` from `hc`. Establish `hG : 0 < TBB.Gp p (TBB.bigPt P.r c)`.

Rewrite using `[hGform]`. Establish `h0 : (∏ a : Fin P.r, c a.castSucc) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun a _ => hd _`. Conclude with `mul_pos (Complex.normSq_pos.2 h0) (by linarith)`. Take `⟨hA, hhA, hB, hhB, l, hVeq, hAw, hl0⟩` from `vDecomp p Y c hd hG`. Use `set w := wq p c with hw`.

Establish `uA : IsUnit hA.det` using `Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hhA.1`. Establish `hwA : w = hA⁻¹ *ᵥ (l • (p.m₀ *ᵥ p.ν'))`. Rewrite using `[← hAw, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ uA, Matrix.one_mulVec]`. Establish `hw0 : w ≠ 0`. Introduce `h0`.

Rewrite `hAw` using `[h0, Matrix.mulVec_zero]`. Conclude with `(smul_ne_zero hl0 he0) hAw.symm`. Establish `hwW : inWb P.k P.r w` using `prW_inWb (k := P.k) (r := P.r) hzW _`. Establish `hwz : herm (Hpk P.k P.r) w p.T.base.z = 0` using `projection_hermitian_orthogonal (k := P.k) (r := P.r) _ _ hzz`. Take `⟨l', hl'⟩` from `hHe w hwW hwz hw0`.

Establish `hHUw` using `hHU w`. Use `set Mw := H w with hMw`. Establish `uH : IsUnit Mw.det` using `Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hHUw.1`. Establish `hl'0 : l' ≠ 0`. Introduce `h0`.

Rewrite `hl'` using `[h0, zero_smul]`. Apply `hw0` to reduce the goal to its premises. Rewrite using `[← Matrix.one_mulVec w, ← Matrix.nonsing_inv_mul _ uH, ← Matrix.mulVec_mulVec, hl', Matrix.mulVec_zero]`. Establish `hHinv : Mw⁻¹ *ᵥ (p.m₀ *ᵥ p.ν') = l'⁻¹ • w`. Establish `h0 : Mw⁻¹ *ᵥ (Mw *ᵥ w) = w`.

Rewrite using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ uH, Matrix.one_mulVec]`. Rewrite `h0` using `[hl', Matrix.mulVec_smul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[smul_smul, inv_mul_cancel₀ hl'0, one_smul]`. Use `_ = l'⁻¹ • w := by rw [h0]`.

Use `set g := hA * Mw⁻¹ with hgdef`. Establish `hg : g ∈ UWset P.k P.r p.T.base.z` using `Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_mul hhA (Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_inv (hHU w))`. Establish `hge : g *ᵥ (p.m₀ *ᵥ p.ν') = (l'⁻¹ * l) • (p.m₀ *ᵥ p.ν')`. Rewrite using `[hgdef, ← Matrix.mulVec_mulVec, hHinv, Matrix.mulVec_smul, hAw, smul_smul]`. Establish `hcomm` using `hTC P Wp p.T.base.π p.T.base.z (p.m₀ *ᵥ p.ν') p.TP p.T.base.π_rep p.T.base.π_cont p.T.base.π_unitary (by have := p.hl.2.2; omega) hzW p.T.base.T_pos he hez hee g hg (l'⁻¹ * l) hge ρ`.

Establish `hgH : g * Mw = hA`. Rewrite using `[hgdef, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ uH, Matrix.mul_one]`. Establish `hπA : p.T.base.π hA = (p.T.base.π g).comp (p.T.base.π Mw)`. Rewrite using `[← hgH]`. Conclude with `p.T.base.π_rep.2 g hg Mw hHUw`.

Establish `key : (p.TP.E ρ).comp (p.V Y (TBB.bigPt P.r c)) = Formalism.FourierDecayAlt.P.Dx2.VV.CinL p.T.base g hB ((p.TP.E ρ).comp ((p.T.base.π Mw).comp (B.JF p.T.base Y (gd p c))))`. Rewrite using `[hVeq, Formalism.FourierDecayAlt.P.Dx2.VV.CinL_apply, Formalism.FourierDecayAlt.P.Dx2.VV.CinL_apply]`. Unfold `Formalism.FourierDecayAlt.P.Dx2.VV.Cin`. Rewrite using `[hπA]`. Use extensionality with `v`.

Use `congrArg (fun L : Wp →L[ℂ] Wp => L ((p.T.base.π Mw) ((B.JF p.T.base Y (gd p c)) ((p.T.base.π' hB⁻¹) v)))) hcomm` as an intermediate fact. Simplify using `using this`. Rewrite using `[key, CutBP.hsVec_norm_CinL p.T.base hg hhB]`. Establish `h2 : ∀ c : Fin (P.r + 1) → ℂ, (∀ i, c i ≠ 0) → c ∉ D0 → p.V Y (TBB.bigPt P.r c) = 0`. Introduce `c hc hcD`.

Establish `hζ : Complex.normSq (c (Fin.last P.r)) ≤ TT`. Assume the negation of the conclusion as `h`. Conclude with `hcD ⟨hc, lt_of_not_ge h⟩`. Establish `hG : ¬ 0 < TBB.Gp p (TBB.bigPt P.r c)`. Rewrite using `[hGform]`.

Conclude with `not_lt.2 (mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) (by linarith))`. Use `show D.vecV p.T.base p.ν' p.m₀ Y (TBB.bigPt P.r c) = 0`. Unfold `D.vecV`. Rewrite using `[dif_neg]`. Conclude with `fun h => hG h.2`.

Establish `hD0 : MeasurableSet D0`. Establish `ho1 : IsOpen {c : Fin (P.r + 1) → ℂ | ∀ i, c i ≠ 0}`. Simplify using `only [Set.setOf_forall]`. Conclude with `isOpen_iInter_of_finite fun i => isOpen_ne_fun (continuous_apply i) continuous_const`. Establish `ho2 : IsOpen {c : Fin (P.r + 1) → ℂ | TT < Complex.normSq (c (Fin.last P.r))}` using `isOpen_lt continuous_const (Complex.continuous_normSq.comp (continuous_apply _))`.

Establish `ho : IsOpen D0` using `ho1.inter ho2`. Conclude with `ho.measurableSet`. Establish `hqmap : Set.MapsTo (fun c : Fin (P.r + 1) → ℂ => ((fun i : Fin P.r => c i.castSucc), c (Fin.last P.r))) D0 (JF.QDom P.k P.r p.T.base.z p.T.base.z')` using `fun c hc => ⟨fun a => hc.1 _, hc.2⟩`. Establish `hqc : Continuous (fun c : Fin (P.r + 1) → ℂ => ((fun i : Fin P.r => c i.castSucc), c (Fin.last P.r)))` using `(continuous_pi fun i => continuous_apply _).prodMk (continuous_apply _)`. Establish `hJ : ContinuousOn (fun c => B.JF p.T.base Y (gd p c)) D0`.

Establish `h0 : ContDiffOn ℝ ((0 : ℕ) : WithTop ℕ∞) (fun q => B.JF p.T.base Y (B.gq p.T.base q)) (JF.QDom P.k P.r p.T.base.z p.T.base.z')` using `Formalism.FourierDecayAlt.P.jacquet_smooth_coordinates P.k P.r Wp Wq p.T.base A 0 Y hThr hY`. Establish `h1' : ContinuousOn (fun q => B.JF p.T.base Y (B.gq p.T.base q)) (JF.QDom P.k P.r p.T.base.z p.T.base.z')` using `h0.continuousOn`. Establish `e : (fun c => B.JF p.T.base Y (gd p c)) = (fun q => B.JF p.T.base Y (B.gq p.T.base q)) ∘ (fun c : Fin (P.r + 1) → ℂ => ((fun i : Fin P.r => c i.castSucc), c (Fin.last P.r)))`. Use function extensionality and compare the values at `c`. Rewrite using `[Function.comp_apply, gd_eq]`.

Rewrite using `[e]`. Conclude with `h1'.comp hqc.continuousOn hqmap`. Establish `hgd : ContinuousOn (fun c => gd p c) D0`. Establish `h1' : ContinuousOn (fun q => B.gq p.T.base q) (JF.QDom P.k P.r p.T.base.z p.T.base.z')` using `(Formalism.FourierDecayAlt.P.BigCellOpenDomain.gq_contDiffOn p.T.base 0).continuousOn`. Establish `e : (fun c => gd p c) = (fun q => B.gq p.T.base q) ∘ (fun c : Fin (P.r + 1) → ℂ => ((fun i : Fin P.r => c i.castSucc), c (Fin.last P.r)))`.

Use function extensionality and compare the values at `c`. Rewrite using `[Function.comp_apply, gd_eq]`. Rewrite using `[e]`. Conclude with `h1'.comp hqc.continuousOn hqmap`. Establish `hwq : ContinuousOn (fun c => wq p c) D0` using `((prW_cont (k := P.k) (r := P.r) p.T.base.z).comp (cofR_cont (k := P.k) (r := P.r) p.T.base)).comp_continuousOn hgd`.

Establish `hπH : Measurable (fun u => p.T.base.π (H u))`. Set `U : Set (Fin (2 * P.r + P.k + 1) → Fin (2 * P.r + P.k + 1) → ℂ)` to `UWset P.k P.r p.T.base.z`. Set `f : (Fin (2 * P.r + P.k + 1) → Fin (2 * P.r + P.k + 1) → ℂ) → (Wp →L[ℂ] Wp)` to `fun m => p.T.base.π (Matrix.of m)`. Establish `hf : ContinuousOn f U` using `p.T.base.π_cont`. Establish `hH' : Measurable (fun u => (Matrix.of.symm (H u) : Fin (2 * P.r + P.k + 1) → Fin (2 * P.r + P.k + 1) → ℂ))` using `hHm`.

Establish `hr : Continuous (U.restrict f)` using `hf.restrict`. Conclude with `hr.measurable.comp (hH'.subtype_mk (h := fun u => hHU u))`. Establish `hA1 : AEStronglyMeasurable (fun c => p.T.base.π (H (wq p c))) (volume.restrict D0)` using `(hπH.comp_aemeasurable (hwq.aemeasurable hD0)).aestronglyMeasurable`. Establish `hA2 : AEStronglyMeasurable (fun c => B.JF p.T.base Y (gd p c)) (volume.restrict D0)` using `hJ.aestronglyMeasurable hD0`. Establish `hsc : Continuous (fun X : Wq →L[ℂ] Wp => B.hsVec X)`.

Unfold `B.hsVec`. Conclude with `(PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => (ContinuousLinearMap.apply ℂ Wp (stdOrthonormalBasis ℂ Wq i)).continuous)`. Establish `hGc : Continuous (fun x : (Wp →L[ℂ] Wp) × (Wq →L[ℂ] Wp) => ‖B.hsVec ((p.TP.E ρ).comp (x.1.comp x.2))‖)` using `(hsc.comp (continuous_const.clm_comp (continuous_fst.clm_comp continuous_snd))).norm`. Establish `h3 : AEStronglyMeasurable Φ (volume.restrict D0)`. Establish `e : Φ = (fun x : (Wp →L[ℂ] Wp) × (Wq →L[ℂ] Wp) => ‖B.hsVec ((p.TP.E ρ).comp (x.1.comp x.2))‖) ∘ (fun c => (p.T.base.π (H (wq p c)), B.JF p.T.base Y (gd p c)))`.

Rewrite using `[hΦ]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `hGc.comp_aestronglyMeasurable (hA1.prodMk hA2)`. Establish `hind : AEStronglyMeasurable (D0.indicator Φ) volume` using `(aestronglyMeasurable_indicator_iff hD0).2 h3`.

Use `hind.congr ?_` and prove the remaining obligations. Use `filter_upwards [TDM.ae_all_ne P.r] with c hc`. Distinguish the cases in `hcD : c ∈ D0`. Rewrite using `[Set.indicator_of_mem hcD, h1 c hcD]`. Rewrite using `[Set.indicator_of_notMem hcD, h2 c hc hcD, ContinuousLinearMap.comp_zero]`.

Unfold `B.hsVec`. Simplify using `only [ContinuousLinearMap.zero_apply]`. Use `symm`. Rewrite using `[norm_eq_zero]`. Use `first`.

Consider the case `exact WithLp.toLp_zero 2 _`. Consider the case `rfl`. Consider the case `(ext i; simp)`.
-/
theorem typeNormMeas_of_typeComm_houseMeas (hTC : TypeComm) (hHM : HouseMeas) : TDM.TypeNormMeas := by
  intro Wp Wq _ _ _ _ _ _ P p Y A hThr hY ρ
  obtain ⟨hmU, hmW, -, -, -, hzeq, -⟩ := Formalism.FourierDecayAlt.P.Topx1.vecw_base_parts p.T.base p.hF
  obtain ⟨hν, hνz, hνν, -, -⟩ := id p.hF
  have he : inWb P.k P.r (p.m₀ *ᵥ p.ν') := hmW p.ν' hν
  have hee : herm (Hpk P.k P.r) (p.m₀ *ᵥ p.ν') (p.m₀ *ᵥ p.ν') = 1 := by
    rw [Formalism.FourierDecayAlt.P.Dx2.DF.herm_m0_mulVec_invariant p.m₀ hmU]; exact hνν
  have hez : herm (Hpk P.k P.r) (p.m₀ *ᵥ p.ν') p.T.base.z = 0 := by
    rw [hzeq, Formalism.FourierDecayAlt.P.Qx8.herm_smul_right', Formalism.FourierDecayAlt.P.Dx2.DF.herm_m0_mulVec_invariant p.m₀ hmU, hνz, mul_zero]
  have hzW : inWb P.k P.r p.T.base.z := (Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z p.T.base).1
  have hzz : herm (Hpk P.k P.r) p.T.base.z p.T.base.z ≠ 0 := by
    rw [Formalism.FourierDecayAlt.P.Dx2.DF.herm_self_alt]
    have := p.T.base.T_pos
    intro h
    have h2 := congrArg Complex.re h
    simp at h2; linarith
  have hzneg : (herm (Hpk P.k P.r) p.T.base.z p.T.base.z).re < 0 := by
    rw [Formalism.FourierDecayAlt.P.Dx2.DF.herm_self_alt]
    have := p.T.base.T_pos
    simp; linarith
  have he0 : p.m₀ *ᵥ p.ν' ≠ 0 := by
    intro h0; rw [h0] at hee; simp [herm] at hee
  obtain ⟨H, hHm, hHU, hHe⟩ := hHM P.k P.r p.T.base.z (p.m₀ *ᵥ p.ν') hzW hzneg he hez hee
  set TT : ℝ := Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' with hTT
  set D0 : Set (Fin (P.r + 1) → ℂ) := {c | (∀ i, c i ≠ 0) ∧ TT < Complex.normSq (c (Fin.last P.r))} with hD0def
  set Φ : (Fin (P.r + 1) → ℂ) → ℝ := fun c =>
    ‖B.hsVec ((p.TP.E ρ).comp ((p.T.base.π (H (wq p c))).comp (B.JF p.T.base Y (gd p c))))‖ with hΦ

  have hGform : ∀ c : Fin (P.r + 1) → ℂ, TBB.Gp p (TBB.bigPt P.r c) =
      Complex.normSq (∏ a : Fin P.r, c a.castSucc) * (Complex.normSq (c (Fin.last P.r)) - TT) := by
    intro c
    show D.ptG TT P.r (Formalism.FourierDecayAlt.P.PBJ.bigPt c) = _
    unfold D.ptG
    rw [Formalism.FourierDecayAlt.P.PBM.ptMatN_bigPt_head, Formalism.FourierDecayAlt.P.PBJ.Dens.ptMatN_bigPt, Formalism.FourierDecayAlt.P.PBM.hMat_one,
      Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_castSucc, Complex.normSq_mul]
    ring

  have h1 : ∀ c ∈ D0, ‖B.hsVec ((p.TP.E ρ).comp (p.V Y (TBB.bigPt P.r c)))‖ = Φ c := by
    intro c hc
    obtain ⟨hd, hζ⟩ := hc
    have hG : 0 < TBB.Gp p (TBB.bigPt P.r c) := by
      rw [hGform]
      have h0 : (∏ a : Fin P.r, c a.castSucc) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hd _
      exact mul_pos (Complex.normSq_pos.2 h0) (by linarith)
    obtain ⟨hA, hhA, hB, hhB, l, hVeq, hAw, hl0⟩ := vDecomp p Y c hd hG
    set w := wq p c with hw
    have uA : IsUnit hA.det := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hhA.1
    have hwA : w = hA⁻¹ *ᵥ (l • (p.m₀ *ᵥ p.ν')) := by
      rw [← hAw, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ uA, Matrix.one_mulVec]
    have hw0 : w ≠ 0 := by
      intro h0
      rw [h0, Matrix.mulVec_zero] at hAw
      exact (smul_ne_zero hl0 he0) hAw.symm
    have hwW : inWb P.k P.r w := prW_inWb (k := P.k) (r := P.r) hzW _
    have hwz : herm (Hpk P.k P.r) w p.T.base.z = 0 := projection_hermitian_orthogonal (k := P.k) (r := P.r) _ _ hzz
    obtain ⟨l', hl'⟩ := hHe w hwW hwz hw0
    have hHUw := hHU w
    set Mw := H w with hMw
    have uH : IsUnit Mw.det := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hHUw.1
    have hl'0 : l' ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hl'
      apply hw0
      rw [← Matrix.one_mulVec w, ← Matrix.nonsing_inv_mul _ uH, ← Matrix.mulVec_mulVec, hl', Matrix.mulVec_zero]
    have hHinv : Mw⁻¹ *ᵥ (p.m₀ *ᵥ p.ν') = l'⁻¹ • w := by
      have h0 : Mw⁻¹ *ᵥ (Mw *ᵥ w) = w := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ uH, Matrix.one_mulVec]
      rw [hl', Matrix.mulVec_smul] at h0
      calc Mw⁻¹ *ᵥ (p.m₀ *ᵥ p.ν') = l'⁻¹ • (l' • Mw⁻¹ *ᵥ (p.m₀ *ᵥ p.ν')) := by
            rw [smul_smul, inv_mul_cancel₀ hl'0, one_smul]
        _ = l'⁻¹ • w := by rw [h0]
    set g := hA * Mw⁻¹ with hgdef
    have hg : g ∈ UWset P.k P.r p.T.base.z :=
      Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_mul hhA (Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_inv (hHU w))
    have hge : g *ᵥ (p.m₀ *ᵥ p.ν') = (l'⁻¹ * l) • (p.m₀ *ᵥ p.ν') := by
      rw [hgdef, ← Matrix.mulVec_mulVec, hHinv, Matrix.mulVec_smul, hAw, smul_smul]
    have hcomm := hTC P Wp p.T.base.π p.T.base.z (p.m₀ *ᵥ p.ν') p.TP p.T.base.π_rep p.T.base.π_cont
      p.T.base.π_unitary (by have := p.hl.2.2; omega) hzW p.T.base.T_pos he hez hee g hg (l'⁻¹ * l) hge ρ
    have hgH : g * Mw = hA := by
      rw [hgdef, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ uH, Matrix.mul_one]
    have hπA : p.T.base.π hA = (p.T.base.π g).comp (p.T.base.π Mw) := by
      rw [← hgH]; exact p.T.base.π_rep.2 g hg Mw hHUw
    have key : (p.TP.E ρ).comp (p.V Y (TBB.bigPt P.r c)) = Formalism.FourierDecayAlt.P.Dx2.VV.CinL p.T.base g hB
        ((p.TP.E ρ).comp ((p.T.base.π Mw).comp (B.JF p.T.base Y (gd p c)))) := by
      rw [hVeq, Formalism.FourierDecayAlt.P.Dx2.VV.CinL_apply, Formalism.FourierDecayAlt.P.Dx2.VV.CinL_apply]
      unfold Formalism.FourierDecayAlt.P.Dx2.VV.Cin
      rw [hπA]
      ext v
      have := congrArg (fun L : Wp →L[ℂ] Wp => L ((p.T.base.π Mw) ((B.JF p.T.base Y (gd p c))
        ((p.T.base.π' hB⁻¹) v)))) hcomm
      simpa using this
    rw [key, CutBP.hsVec_norm_CinL p.T.base hg hhB]

  have h2 : ∀ c : Fin (P.r + 1) → ℂ, (∀ i, c i ≠ 0) → c ∉ D0 → p.V Y (TBB.bigPt P.r c) = 0 := by
    intro c hc hcD
    have hζ : Complex.normSq (c (Fin.last P.r)) ≤ TT := by
      by_contra h; exact hcD ⟨hc, lt_of_not_ge h⟩
    have hG : ¬ 0 < TBB.Gp p (TBB.bigPt P.r c) := by
      rw [hGform]
      exact not_lt.2 (mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) (by linarith))
    show D.vecV p.T.base p.ν' p.m₀ Y (TBB.bigPt P.r c) = 0
    unfold D.vecV
    rw [dif_neg]
    exact fun h => hG h.2

  have hD0 : MeasurableSet D0 := by
    have ho1 : IsOpen {c : Fin (P.r + 1) → ℂ | ∀ i, c i ≠ 0} := by
      simp only [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_ne_fun (continuous_apply i) continuous_const
    have ho2 : IsOpen {c : Fin (P.r + 1) → ℂ | TT < Complex.normSq (c (Fin.last P.r))} :=
      isOpen_lt continuous_const (Complex.continuous_normSq.comp (continuous_apply _))
    have ho : IsOpen D0 := ho1.inter ho2
    exact ho.measurableSet
  have hqmap : Set.MapsTo (fun c : Fin (P.r + 1) → ℂ => ((fun i : Fin P.r => c i.castSucc), c (Fin.last P.r))) D0
      (JF.QDom P.k P.r p.T.base.z p.T.base.z') := fun c hc => ⟨fun a => hc.1 _, hc.2⟩
  have hqc : Continuous (fun c : Fin (P.r + 1) → ℂ => ((fun i : Fin P.r => c i.castSucc), c (Fin.last P.r))) :=
    (continuous_pi fun i => continuous_apply _).prodMk (continuous_apply _)
  have hJ : ContinuousOn (fun c => B.JF p.T.base Y (gd p c)) D0 := by
    have h0 : ContDiffOn ℝ ((0 : ℕ) : WithTop ℕ∞) (fun q => B.JF p.T.base Y (B.gq p.T.base q))
        (JF.QDom P.k P.r p.T.base.z p.T.base.z') :=
      Formalism.FourierDecayAlt.P.jacquet_smooth_coordinates P.k P.r Wp Wq p.T.base A 0 Y hThr hY
    have h1' : ContinuousOn (fun q => B.JF p.T.base Y (B.gq p.T.base q))
        (JF.QDom P.k P.r p.T.base.z p.T.base.z') := h0.continuousOn
    have e : (fun c => B.JF p.T.base Y (gd p c)) = (fun q => B.JF p.T.base Y (B.gq p.T.base q)) ∘
        (fun c : Fin (P.r + 1) → ℂ => ((fun i : Fin P.r => c i.castSucc), c (Fin.last P.r))) := by
      funext c; rw [Function.comp_apply, gd_eq]
    rw [e]
    exact h1'.comp hqc.continuousOn hqmap
  have hgd : ContinuousOn (fun c => gd p c) D0 := by
    have h1' : ContinuousOn (fun q => B.gq p.T.base q) (JF.QDom P.k P.r p.T.base.z p.T.base.z') :=
      (Formalism.FourierDecayAlt.P.BigCellOpenDomain.gq_contDiffOn p.T.base 0).continuousOn
    have e : (fun c => gd p c) = (fun q => B.gq p.T.base q) ∘
        (fun c : Fin (P.r + 1) → ℂ => ((fun i : Fin P.r => c i.castSucc), c (Fin.last P.r))) := by
      funext c; rw [Function.comp_apply, gd_eq]
    rw [e]
    exact h1'.comp hqc.continuousOn hqmap
  have hwq : ContinuousOn (fun c => wq p c) D0 :=
    ((prW_cont (k := P.k) (r := P.r) p.T.base.z).comp (cofR_cont (k := P.k) (r := P.r) p.T.base)).comp_continuousOn hgd
  have hπH : Measurable (fun u => p.T.base.π (H u)) := by
    let U : Set (Fin (2 * P.r + P.k + 1) → Fin (2 * P.r + P.k + 1) → ℂ) := UWset P.k P.r p.T.base.z
    let f : (Fin (2 * P.r + P.k + 1) → Fin (2 * P.r + P.k + 1) → ℂ) → (Wp →L[ℂ] Wp) :=
      fun m => p.T.base.π (Matrix.of m)
    have hf : ContinuousOn f U := p.T.base.π_cont
    have hH' : Measurable (fun u => (Matrix.of.symm (H u) : Fin (2 * P.r + P.k + 1) → Fin (2 * P.r + P.k + 1) → ℂ)) :=
      hHm
    have hr : Continuous (U.restrict f) := hf.restrict
    exact hr.measurable.comp (hH'.subtype_mk (h := fun u => hHU u))
  have hA1 : AEStronglyMeasurable (fun c => p.T.base.π (H (wq p c))) (volume.restrict D0) :=
    (hπH.comp_aemeasurable (hwq.aemeasurable hD0)).aestronglyMeasurable
  have hA2 : AEStronglyMeasurable (fun c => B.JF p.T.base Y (gd p c)) (volume.restrict D0) :=
    hJ.aestronglyMeasurable hD0
  have hsc : Continuous (fun X : Wq →L[ℂ] Wp => B.hsVec X) := by
    unfold B.hsVec
    exact (PiLp.continuous_toLp 2 _).comp
      (continuous_pi fun i => (ContinuousLinearMap.apply ℂ Wp (stdOrthonormalBasis ℂ Wq i)).continuous)
  have hGc : Continuous (fun x : (Wp →L[ℂ] Wp) × (Wq →L[ℂ] Wp) => ‖B.hsVec ((p.TP.E ρ).comp (x.1.comp x.2))‖) :=
    (hsc.comp (continuous_const.clm_comp (continuous_fst.clm_comp continuous_snd))).norm
  have h3 : AEStronglyMeasurable Φ (volume.restrict D0) := by
    have e : Φ = (fun x : (Wp →L[ℂ] Wp) × (Wq →L[ℂ] Wp) => ‖B.hsVec ((p.TP.E ρ).comp (x.1.comp x.2))‖) ∘
        (fun c => (p.T.base.π (H (wq p c)), B.JF p.T.base Y (gd p c))) := by
      rw [hΦ]; rfl
    rw [e]
    exact hGc.comp_aestronglyMeasurable (hA1.prodMk hA2)
  have hind : AEStronglyMeasurable (D0.indicator Φ) volume := (aestronglyMeasurable_indicator_iff hD0).2 h3
  refine hind.congr ?_
  filter_upwards [TDM.ae_all_ne P.r] with c hc
  by_cases hcD : c ∈ D0
  · rw [Set.indicator_of_mem hcD, h1 c hcD]
  · rw [Set.indicator_of_notMem hcD, h2 c hc hcD, ContinuousLinearMap.comp_zero]
    unfold B.hsVec
    simp only [ContinuousLinearMap.zero_apply]
    symm
    rw [norm_eq_zero]
    first
      | exact WithLp.toLp_zero 2 _
      | rfl
      | (ext i; simp)

end main

end

end Formalism.FourierDecayAlt.P.CutBP.TNM
