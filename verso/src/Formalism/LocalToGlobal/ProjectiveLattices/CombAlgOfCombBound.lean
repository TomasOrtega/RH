import Formalism.LocalToGlobal.ProjectiveLattices.NumericalH1Condition
import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.IntegralExtensionOfRegR1

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra
  Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {T : Top D} (h : LawsP T)

/- English proof (translation)
Introduce and unpack `la _ ⟨y0, rfl⟩`. Take `⟨T', io, e, ho, z, hz, eta, heta, hq⟩` from `y0.2`. Take `⟨η, hη⟩` from `T.G.liesTotal h.points_condition h.bc66 hj la T' io e ho z hz`. Set `y : T.PtA j la` to `PtV.mk la ho z hz η hη`. Establish `hyv : vAtV y = vAtV y0` using `funext fun g => by show y.1.1 g = y0.1.1 g`.

Rewrite using `[hq]`. Both sides reduce to the same expression. Establish `hv : ∀ w (F : (recB h.toLawsCore).Cusp j w), (recPJ h j hj).vAt la y ((recPJ h j hj).inc w F) = vAtV y0 F.1` using `fun w F => by`. Rewrite using `[recPJ_vAt_inc, hyv]`. Establish `hd : (recPJ h j hj).depth S.sW wL la y = ⨅ k, vAtV y0 (G.w k).1`.

Unfold `PJ.depth`. Rewrite using `[← hspan, iInf_span_eq (X := recPJ h j hj) G.w la ((recPJ h j hj).vAt la y) ((recPJ h j hj).vAt_zero la y) ((recPJ h j hj).vAt_add la y) ((recPJ h j hj).vAt_smul la y) (fun _ ha => vAdd_int_nonneg la ha)]`. Simplify using `only [hv]`. Take `⟨h0, h1⟩` from `(hX la y).1 hjm`. Rewrite `h0`, `h1` using `[hv]`.

Rewrite `h1` using `[hd]`. Use `⟨h0, fun htop => ?_⟩` and prove the remaining obligations. Establish `h2` using `h1 htop`. Rewrite `h2` using `[EReal.coe_add, EReal.coe_mul, EReal.coe_toReal htop (vAtV_ne_bot y0 _)]`. Conclude with `h2`.
-/
theorem combAlg_of_combBound (j : ℕ) (hj : InR D j) (hjm : j < D.R.m) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPJ h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (cb : ℝ)
    (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ)
    (hspan : @Submodule.span (𝓞 (recB h.toLawsCore).KO) _ _ _ (WeightFamilies.Prov.modOC (recB h.toLawsCore) j wL)
      (Set.range G.w) = (recPJ h j hj).WWc S.sW wL)
    (hX : CombBound G S cb nus) :
    CombAlg (T.Q.Xo j) T.Q.c (fun k => (G.w k).1) G.et.1 nus (cb / (2 * (G.iet : ℝ))) := by
  rintro la _ ⟨y0, rfl⟩
  obtain ⟨T', io, e, ho, z, hz, eta, heta, hq⟩ := y0.2
  obtain ⟨η, hη⟩ := T.G.liesTotal h.points_condition h.bc66 hj la T' io e ho z hz
  let y : T.PtA j la := PtV.mk la ho z hz η hη
  have hyv : vAtV y = vAtV y0 := funext fun g => by
    show y.1.1 g = y0.1.1 g
    rw [hq]
    rfl
  have hv : ∀ w (F : (recB h.toLawsCore).Cusp j w),
      (recPJ h j hj).vAt la y ((recPJ h j hj).inc w F) = vAtV y0 F.1 := fun w F => by
    rw [recPJ_vAt_inc, hyv]
  have hd : (recPJ h j hj).depth S.sW wL la y = ⨅ k, vAtV y0 (G.w k).1 := by
    unfold PJ.depth
    rw [← hspan, iInf_span_eq (X := recPJ h j hj) G.w la ((recPJ h j hj).vAt la y)
      ((recPJ h j hj).vAt_zero la y) ((recPJ h j hj).vAt_add la y) ((recPJ h j hj).vAt_smul la y)
      (fun _ ha => vAdd_int_nonneg la ha)]
    simp only [hv]
  obtain ⟨h0, h1⟩ := (hX la y).1 hjm
  rw [hv] at h0 h1
  rw [hd] at h1
  refine ⟨h0, fun htop => ?_⟩
  have h2 := h1 htop
  rw [EReal.coe_add, EReal.coe_mul, EReal.coe_toReal htop (vAtV_ne_bot y0 _)] at h2
  exact h2

end Formalism.L2.Pj
