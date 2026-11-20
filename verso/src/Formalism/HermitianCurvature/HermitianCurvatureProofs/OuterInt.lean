import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChiLIntegrable
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableUnipotentNormRpowNeg

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

section outer

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `: CompleteSpace Wp` using `FiniteDimensional.complete ℂ Wp`. Establish `hsW : SigmaFinite S.μW` using `Dx2.OrbJ.sigmaF S.haarW`. Establish `hsW' : SigmaFinite S.μW'` using `Dx2.OrbJ.sigmaF S.haarW'`. Establish `hfW : IsFiniteMeasure S.μW` using `⟨by rw [hW1]; exact ENNReal.one_lt_top⟩`. Establish `hfW' : IsFiniteMeasure S.μW'` using `⟨by rw [hW1']; exact ENNReal.one_lt_top⟩`.

Use `set γ := U.mMap k r 0 (U.hMat σ d) γ0 with hγ`. Establish `hγG : γ ∈ B.GV k r`. Use `(Formalism.FourierDecayAlt.P.slice_membership k r 0).1 (U.hMat σ d) γ0 (hMat_det_ne σ d hd) hγ0` as an intermediate fact. Conclude with `this`. Use `set f : B.SS k r → (Wq →L[ℂ] Wp) := fun p => theta0 S.z σ.symm p • D.orbIntegrand S γ F p with hf`.

Establish `hfm : AEStronglyMeasurable f S.μSS` using `(theta0_meas S.z σ.symm).aestronglyMeasurable.smul (Dx3.integrand_aesm S hγG hFc)`. Establish `hSS` using `muSS_eq S hN`. Use `set P := (S.μW.prod (QN k r)).prod (S.μW'.prod (QN k r)) with hP`. Establish `hfm' : AEStronglyMeasurable f (P.map (TN k r))` using `by rw [← hSS]; exact hfm`. Establish `hTm : AEMeasurable (TN k r) P` using `TN_meas.aemeasurable`.

Use `set P2 := (S.μW.prod S.μW').prod ((QN k r).prod (QN k r)) with hP2`. Establish `hsw` using `Dx2.SL.measurePreserving_prod_middle_swap S.μW (QN k r) S.μW' (QN k r)`. Use `set G2 : (Mt k r × Mt k r) × ((U.RC k r 0 × (G.UT r → ℂ)) × (U.RC k r 0 × (G.UT r → ℂ))) → (Wq →L[ℂ] Wp) := fun x => f (TN k r ((x.1.1, x.2.1), (x.1.2, x.2.2))) with hG2`. Establish `hG2e : G2 = (f ∘ TN k r) ∘ (Dx2.SL.swap4 (α` using `Mt k r) (β := U.RC k r 0 × (G.UT r → ℂ)) (γ := Mt k r) (δ := U.RC k r 0 × (G.UT r → ℂ))).symm := by`. Use function extensionality and compare the values at `x`.

Both sides reduce to the same expression. Establish `hfTm : AEStronglyMeasurable (f ∘ TN k r) P` using `hfm'.comp_aemeasurable hTm`. Establish `hG2m : AEStronglyMeasurable G2 P2`. Rewrite using `[hG2e]`. Conclude with `hfTm.comp_measurePreserving (hsw.symm _)`.

Establish `hae : ∀ᵐ x ∂(S.μW.prod S.μW'), Matrix.of x.1 ∈ UWset k r S.z ∧ Matrix.of x.2 ∈ UWset k r S.z'`. Establish `b1` using `(Measure.quasiMeasurePreserving_fst (μ := S.μW) (ν := S.μW')).ae (Dx2.OrbJ.ae_mem S.haarW)`. Establish `b2` using `(Measure.quasiMeasurePreserving_snd (μ := S.μW) (ν := S.μW')).ae (Dx2.OrbJ.ae_mem S.haarW')`. Use `filter_upwards [b1, b2] with x h1 h2 using ⟨h1, h2⟩`. Establish `hin` using `fun x : Mt k r × Mt k r => fun hx : Matrix.of x.1 ∈ UWset k r S.z ∧ Matrix.of x.2 ∈ UWset k r S.z' => inner_int S z0 z0' hz hz' σ d hd γ0 hγ0 hrel F hFc M Bs hBs hBsf hdom x.1 x.2 hx.1 hx.2`.

Establish `hG2i : Integrable G2 P2`. Rewrite using `[integrable_prod_iff hG2m]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hae] with x hx using (hin x hx).1`. Use `Integrable.of_bound hG2m.norm.integral_prod_right' (M * (U.muXi k r 0 0 σ Bs).toReal) ?_ filter_upwards [hae] with x hx` and prove the remaining obligations.

Rewrite using `[Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]`. Conclude with `(hin x hx).2.2`. Establish `hfTi : Integrable (f ∘ TN k r) P`. Use `(hsw.symm _).integrable_comp_emb (MeasurableEquiv.measurableEmbedding _) (g := f ∘ TN k r)` as an intermediate fact. Rewrite using `[← this, ← hG2e]`.

Conclude with `hG2i`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hSS]`. Conclude with `(integrable_map_measure hfm' hTm).2 hfTi`. Rewrite using `[hSS, integral_map hTm hfm']`.

Establish `e` using `(hsw.symm _).integral_comp' (f ∘ TN k r)`. Express the relevant statement in the definitionally equal form `∫ x, (f ∘ TN k r) x ∂P = _`. Rewrite using `[← e]`. Express the relevant statement in the definitionally equal form `∫ x, G2 x ∂P2 = _`. Rewrite using `[hP2, integral_prod G2 hG2i]`.

Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hae] with x hx using (hin x hx).2.1`.
-/
theorem outer_int (S : B.RealPlaceData k r Wp Wq) (hN : S.μN = D.muN k r) (hW1 : S.μW Set.univ = 1)
    (hW1' : S.μW' Set.univ = 1) (z0 z0' : Fin (2 * 0 + k + 1) → ℂ)
    (hz : S.z = liftVec k r 0 z0) (hz' : S.z' = liftVec k r 0 z0')
    (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (hd : ∀ a, d a ≠ 0) (γ0 : B.Mat k 0) (hγ0 : γ0 ∈ B.GV k 0)
    (hrel : C6.IsRelevant S (U.mMap k r 0 (U.hMat σ d) γ0)) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (hFc : ContinuousOn F (B.GV k r)) (M : ℝ) (Bs : Set (U.Xi k r 0 0 σ)) (hBs : MeasurableSet Bs)
    (hBsf : U.muXi k r 0 0 σ Bs < ⊤)
    (hdom : ∀ (ξ : U.Xi k r 0 0 σ) (γ : B.Mat k 0), γ ∈ B.GV k 0 →
      ‖F (U.gaXi k 0 σ d ξ (fun a => a.elim0) γ)‖ ≤ Bs.indicator (fun _ => M) ξ) :
    Integrable (fun p => theta0 S.z σ.symm p • D.orbIntegrand S (U.mMap k r 0 (U.hMat σ d) γ0) F p) S.μSS ∧
      ∫ p, theta0 S.z σ.symm p • D.orbIntegrand S (U.mMap k r 0 (U.hMat σ d) γ0) F p ∂S.μSS =
        ∫ x, conjL S x.1 x.2 (U.PhiFun (s := 0) k 0 σ d S.z S.z' F (fun a => a.elim0)
          ((midB r 0 (Matrix.of x.1))⁻¹ * γ0 * midB r 0 (Matrix.of x.2))) ∂(S.μW.prod S.μW') := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have hsW : SigmaFinite S.μW := Dx2.OrbJ.sigmaF S.haarW
  have hsW' : SigmaFinite S.μW' := Dx2.OrbJ.sigmaF S.haarW'
  have hfW : IsFiniteMeasure S.μW := ⟨by rw [hW1]; exact ENNReal.one_lt_top⟩
  have hfW' : IsFiniteMeasure S.μW' := ⟨by rw [hW1']; exact ENNReal.one_lt_top⟩
  set γ := U.mMap k r 0 (U.hMat σ d) γ0 with hγ
  have hγG : γ ∈ B.GV k r := by
    have := (Formalism.FourierDecayAlt.P.slice_membership k r 0).1 (U.hMat σ d) γ0 (hMat_det_ne σ d hd) hγ0
    exact this
  set f : B.SS k r → (Wq →L[ℂ] Wp) := fun p => theta0 S.z σ.symm p • D.orbIntegrand S γ F p with hf
  have hfm : AEStronglyMeasurable f S.μSS :=
    (theta0_meas S.z σ.symm).aestronglyMeasurable.smul (Dx3.integrand_aesm S hγG hFc)

  have hSS := muSS_eq S hN
  set P := (S.μW.prod (QN k r)).prod (S.μW'.prod (QN k r)) with hP
  have hfm' : AEStronglyMeasurable f (P.map (TN k r)) := by rw [← hSS]; exact hfm
  have hTm : AEMeasurable (TN k r) P := TN_meas.aemeasurable
  set P2 := (S.μW.prod S.μW').prod ((QN k r).prod (QN k r)) with hP2
  have hsw := Dx2.SL.measurePreserving_prod_middle_swap S.μW (QN k r) S.μW' (QN k r)
  set G2 : (Mt k r × Mt k r) × ((U.RC k r 0 × (G.UT r → ℂ)) × (U.RC k r 0 × (G.UT r → ℂ))) → (Wq →L[ℂ] Wp) :=
    fun x => f (TN k r ((x.1.1, x.2.1), (x.1.2, x.2.2))) with hG2
  have hG2e : G2 = (f ∘ TN k r) ∘ (Dx2.SL.swap4 (α := Mt k r) (β := U.RC k r 0 × (G.UT r → ℂ)) (γ := Mt k r)
      (δ := U.RC k r 0 × (G.UT r → ℂ))).symm := by
    funext x; rfl
  have hfTm : AEStronglyMeasurable (f ∘ TN k r) P := hfm'.comp_aemeasurable hTm
  have hG2m : AEStronglyMeasurable G2 P2 := by
    rw [hG2e]
    exact hfTm.comp_measurePreserving (hsw.symm _)

  have hae : ∀ᵐ x ∂(S.μW.prod S.μW'), Matrix.of x.1 ∈ UWset k r S.z ∧ Matrix.of x.2 ∈ UWset k r S.z' := by
    have b1 := (Measure.quasiMeasurePreserving_fst (μ := S.μW) (ν := S.μW')).ae (Dx2.OrbJ.ae_mem S.haarW)
    have b2 := (Measure.quasiMeasurePreserving_snd (μ := S.μW) (ν := S.μW')).ae (Dx2.OrbJ.ae_mem S.haarW')
    filter_upwards [b1, b2] with x h1 h2 using ⟨h1, h2⟩
  have hin := fun x : Mt k r × Mt k r => fun hx : Matrix.of x.1 ∈ UWset k r S.z ∧ Matrix.of x.2 ∈ UWset k r S.z' =>
    inner_int S z0 z0' hz hz' σ d hd γ0 hγ0 hrel F hFc M Bs hBs hBsf hdom x.1 x.2 hx.1 hx.2
  have hG2i : Integrable G2 P2 := by
    rw [integrable_prod_iff hG2m]
    refine ⟨?_, ?_⟩
    · filter_upwards [hae] with x hx using (hin x hx).1
    · refine Integrable.of_bound hG2m.norm.integral_prod_right' (M * (U.muXi k r 0 0 σ Bs).toReal) ?_
      filter_upwards [hae] with x hx
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact (hin x hx).2.2

  have hfTi : Integrable (f ∘ TN k r) P := by
    have := (hsw.symm _).integrable_comp_emb (MeasurableEquiv.measurableEmbedding _) (g := f ∘ TN k r)
    rw [← this, ← hG2e]; exact hG2i
  refine ⟨?_, ?_⟩
  · rw [hSS]; exact (integrable_map_measure hfm' hTm).2 hfTi
  · rw [hSS, integral_map hTm hfm']
    have e := (hsw.symm _).integral_comp' (f ∘ TN k r)
    change ∫ x, (f ∘ TN k r) x ∂P = _
    rw [← e]
    change ∫ x, G2 x ∂P2 = _
    rw [hP2, integral_prod G2 hG2i]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx using (hin x hx).2.1

/- English proof (translation)
Take `⟨M, Bs, hBs, hBsf, hdom⟩` from `slice_dom k r hr σ d hd F hFc R hFs`. Take `⟨hint, heq⟩` from `outer_int S hN hW1 hW1' z0 z0' hz hz' σ d hd γ0 hγ0 hrel F hFc M Bs hBs hBsf hdom`. Establish `hγG : U.mMap k r 0 (U.hMat σ d) γ0 ∈ B.GV k r` using `(Formalism.FourierDecayAlt.P.slice_membership k r 0).1 (U.hMat σ d) γ0 (hMat_det_ne σ d hd) hγ0`. Establish `hw' : ∀ a : Fin r, w.symm a.castSucc = (σ.symm.symm a).castSucc` using `by simpa using hw`. Establish `hnc` using `theta0_normCut S hγG hdd hZw σ.symm hw'`.

Establish `hex : ∃ θ, D.IsNormCut S (U.mMap k r 0 (U.hMat σ d) γ0) (D.muR S (U.mMap k r 0 (U.hMat σ d) γ0) w) θ ∧ Integrable (fun p => θ p • D.orbIntegrand S (U.mMap k r 0 (U.hMat σ d) γ0) F p) S.μSS` using `⟨_, hnc, hint⟩`. Unfold `D.orbJ`. Rewrite using `[dif_pos hex, Formalism.FourierDecayAlt.P.orbital_integral_indep_choice k r Wp Wq S _ _ hrel (Formalism.FourierDecayAlt.P.radial_measure_is_haar k r Wp Wq S _ w dd hγG hdd hZw) F hex.choose _ hex.choose_spec.1 hnc hex.choose_spec.2 hint, heq]`.
-/
theorem orbJ_mMap (S : B.RealPlaceData k r Wp Wq) (hN : S.μN = D.muN k r) (hW1 : S.μW Set.univ = 1)
    (hW1' : S.μW' Set.univ = 1) (z0 z0' : Fin (2 * 0 + k + 1) → ℂ)
    (hz : S.z = liftVec k r 0 z0) (hz' : S.z' = liftVec k r 0 z0')
    (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (hd : ∀ a, d a ≠ 0) (γ0 : B.Mat k 0) (hγ0 : γ0 ∈ B.GV k 0)
    (hrel : C6.IsRelevant S (U.mMap k r 0 (U.hMat σ d) γ0))
    (w : Equiv.Perm (Fin (r + 1))) (dd : Fin (r + 1) → ℂ) (hdd : ∀ a, dd a ≠ 0)
    (hZw : Zhat k r S.z S.z' (U.mMap k r 0 (U.hMat σ d) γ0) = C2.monoP w dd)
    (hw : ∀ a : Fin r, w.symm a.castSucc = (σ a).castSucc)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hFc : ContinuousOn F (B.GV k r)) (hr : 1 ≤ r) (R : ℝ)
    (hFs : ∀ g ∈ B.GV k r, F g ≠ 0 → B.gN g ≤ R) :
    D.orbJ S (U.mMap k r 0 (U.hMat σ d) γ0) (D.muR S (U.mMap k r 0 (U.hMat σ d) γ0) w) F =
      ∫ x, conjL S x.1 x.2 (U.PhiFun (s := 0) k 0 σ d S.z S.z' F (fun a => a.elim0)
        ((midB r 0 (Matrix.of x.1))⁻¹ * γ0 * midB r 0 (Matrix.of x.2))) ∂(S.μW.prod S.μW') := by
  obtain ⟨M, Bs, hBs, hBsf, hdom⟩ := slice_dom k r hr σ d hd F hFc R hFs
  obtain ⟨hint, heq⟩ := outer_int S hN hW1 hW1' z0 z0' hz hz' σ d hd γ0 hγ0 hrel F hFc M Bs hBs hBsf hdom
  have hγG : U.mMap k r 0 (U.hMat σ d) γ0 ∈ B.GV k r :=
    (Formalism.FourierDecayAlt.P.slice_membership k r 0).1 (U.hMat σ d) γ0 (hMat_det_ne σ d hd) hγ0
  have hw' : ∀ a : Fin r, w.symm a.castSucc = (σ.symm.symm a).castSucc := by simpa using hw
  have hnc := theta0_normCut S hγG hdd hZw σ.symm hw'
  have hex : ∃ θ, D.IsNormCut S (U.mMap k r 0 (U.hMat σ d) γ0) (D.muR S (U.mMap k r 0 (U.hMat σ d) γ0) w) θ ∧
      Integrable (fun p => θ p • D.orbIntegrand S (U.mMap k r 0 (U.hMat σ d) γ0) F p) S.μSS :=
    ⟨_, hnc, hint⟩
  unfold D.orbJ
  rw [dif_pos hex, Formalism.FourierDecayAlt.P.orbital_integral_indep_choice k r Wp Wq S _ _ hrel
    (Formalism.FourierDecayAlt.P.radial_measure_is_haar k r Wp Wq S _ w dd hγG hdd hZw) F hex.choose _ hex.choose_spec.1 hnc
    hex.choose_spec.2 hint, heq]

end outer

end Formalism.FourierDecayAlt.P.PBM
