import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuRegSmooth
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsVertFactorPos
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHermExtend
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsProjSmoothAlong
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsVertFactorSmooth
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PTopNPoly
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PGlueRegularised
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology Metric Set

namespace MuRegSmooth

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Introduce `z hz`. Take `⟨U, hU, F, hF, hfF⟩` from `hf z hz`. Take `⟨V, hV, G, hG, hgG⟩` from `hg z hz`. Use `⟨U ∩ V, Filter.inter_mem hU hV, fun w => F w * G w, (hF.mono inter_subset_left).mul (hG.mono inter_subset_right), fun w hw => ?_⟩` and prove the remaining obligations. Use `show f w * g w = F w * G w`.

Rewrite using `[hfF w ⟨hw.1.1, hw.2⟩, hgG w ⟨hw.1.2, hw.2⟩]`.
-/
theorem smoothAlong_mul {S : Set ((Σ k, ι k) → ℂ)} {f g : ((Σ k, ι k) → ℂ) → ℝ} (hf : SmoothAlong S f)
    (hg : SmoothAlong S g) : SmoothAlong S fun z => f z * g z := by
  intro z hz
  obtain ⟨U, hU, F, hF, hfF⟩ := hf z hz
  obtain ⟨V, hV, G, hG, hgG⟩ := hg z hz
  refine ⟨U ∩ V, Filter.inter_mem hU hV, fun w => F w * G w,
    (hF.mono inter_subset_left).mul (hG.mono inter_subset_right), fun w hw => ?_⟩
  show f w * g w = F w * G w
  rw [hfF w ⟨hw.1.1, hw.2⟩, hgG w ⟨hw.1.2, hw.2⟩]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `z _`. Conclude with `⟨univ, univ_mem, fun _ => 1, contDiffOn_const, fun w _ => by simp⟩`. Consider the case `insert a s ha ih`.

Establish `h` using `smoothAlong_mul (hf a (Finset.mem_insert_self a s)) (ih fun p hp => hf p (Finset.mem_insert_of_mem hp))`. Introduce `z hz`. Take `⟨U, hU, G, hG, hfG⟩` from `h z hz`. Conclude with `⟨U, hU, G, hG, fun w hw => by show ∏ p ∈ insert a s, f p w = G w`. Rewrite using `[Finset.prod_insert ha]`.

Conclude with `hfG w hw⟩`.
-/
theorem smoothAlong_prod {S : Set ((Σ k, ι k) → ℂ)} {α : Type} (s : Finset α)
    {f : α → ((Σ k, ι k) → ℂ) → ℝ} (hf : ∀ p ∈ s, SmoothAlong S (f p)) :
    SmoothAlong S fun z => ∏ p ∈ s, f p z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro z _
    exact ⟨univ, univ_mem, fun _ => 1, contDiffOn_const, fun w _ => by simp⟩
  | insert a s ha ih =>
    have h := smoothAlong_mul (hf a (Finset.mem_insert_self a s))
      (ih fun p hp => hf p (Finset.mem_insert_of_mem hp))
    intro z hz
    obtain ⟨U, hU, G, hG, hfG⟩ := h z hz
    exact ⟨U, hU, G, hG, fun w hw => by
      show ∏ p ∈ insert a s, f p w = G w
      rw [Finset.prod_insert ha]; exact hfG w hw⟩

/- English proof (translation)
Introduce `z hz`. Take `⟨U, hU, F, hF, hfF⟩` from `hf z hz`. Conclude with `⟨U, hU, fun w => Real.exp (F w), Real.contDiff_exp.comp_contDiffOn hF, fun w hw => by show Real.exp (f w) = Real.exp (F w); rw [hfF w hw]⟩`.
-/
theorem smoothAlong_exp {S : Set ((Σ k, ι k) → ℂ)} {f : ((Σ k, ι k) → ℂ) → ℝ} (hf : SmoothAlong S f) :
    SmoothAlong S fun z => Real.exp (f z) := by
  intro z hz
  obtain ⟨U, hU, F, hF, hfF⟩ := hf z hz
  exact ⟨U, hU, fun w => Real.exp (F w), Real.contDiff_exp.comp_contDiffOn hF,
    fun w hw => by show Real.exp (f w) = Real.exp (F w); rw [hfF w hw]⟩

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Establish `: {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0}`. Use extensionality with `z`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `isOpen_iInter_of_finite fun k => isOpen_iUnion fun i => isOpen_ne_fun (continuous_apply _) continuous_const`.
-/
theorem isOpen_blocks : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z; simp
  rw [this]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

/- English proof (translation)
Introduce `_ hz` and use `⟨_, isOpen_blocks.mem_nhds hz.1, f, hf, fun _ _ => rfl⟩`.
-/
theorem smoothAlong_of_contDiffOn {P : Ideal (MRing ι)} {f : ((Σ k, ι k) → ℂ) → ℝ}
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) : SmoothAlong (mcPts P) f :=
  fun _ hz => ⟨_, isOpen_blocks.mem_nhds hz.1, f, hf, fun _ _ => rfl⟩

/- English proof (translation)
Establish `hball : ∀ j, ∃ δ : ℝ, 0 < δ ∧ cthickening δ (S.R.chart j '' closure (S.R.mid j)) ⊆ (S.R.chart j).target`. Introduce `j`. Establish `hK : IsCompact (S.R.chart j '' closure (S.R.mid j))` using `isClosed_closure.isCompact.image_of_continuousOn ((S.R.chart j).continuousOn.mono (S.R.closure_mid j))`. Establish `hsub : S.R.chart j '' closure (S.R.mid j) ⊆ (S.R.chart j).target` using `image_subset_iff.2 fun x hx => (S.R.chart j).map_source (S.R.closure_mid j hx)`. Conclude with `hK.exists_cthickening_subset_open (S.R.chart j).open_target hsub`.

Use `choose δ hδ hδs using hball`. Establish `hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, t < δ j` using `Filter.eventually_all.2 fun j => nhdsWithin_le_nhds (gt_mem_nhds (hδ j))`. Use `filter_upwards [hev, hS.compare, self_mem_nhdsWithin] with t htδ hcmp ht`. Establish `ht0 : (0 : ℝ) < t` using `ht`. Conclude with `(Regular.GlueRegularised.proof M.Xc d M.atlas S.R S.ρ S.η S.Cη (S.K t) t (S.e1 t) S.cutoff ht0 (ht0.trans_le (S.e1_ge t ht0)) (fun j x hx => ((closedBall_subset_closedBall (htδ j).le).trans (closedBall_subset_cthickening (mem_image_of_mem _ hx) _)).trans (hδs j)) hcmp).1`.
-/
theorem regWeight_smooth {P : Ideal (MRing ι)} {d : ℕ} {M : CxModel P d} {Xo : Set ((Σ k, ι k) → ℂ)}
    {A : HermLine ι} (S : LogLogRegularisationSetting M Xo A) (hS : S.IsTied) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), M.atlas.Smooth (S.regWeight t) := by
  have hball : ∀ j, ∃ δ : ℝ, 0 < δ ∧
      cthickening δ (S.R.chart j '' closure (S.R.mid j)) ⊆ (S.R.chart j).target := by
    intro j
    have hK : IsCompact (S.R.chart j '' closure (S.R.mid j)) :=
      isClosed_closure.isCompact.image_of_continuousOn
        ((S.R.chart j).continuousOn.mono (S.R.closure_mid j))
    have hsub : S.R.chart j '' closure (S.R.mid j) ⊆ (S.R.chart j).target :=
      image_subset_iff.2 fun x hx => (S.R.chart j).map_source (S.R.closure_mid j hx)
    exact hK.exists_cthickening_subset_open (S.R.chart j).open_target hsub
  choose δ hδ hδs using hball
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, t < δ j :=
    Filter.eventually_all.2 fun j => nhdsWithin_le_nhds (gt_mem_nhds (hδ j))
  filter_upwards [hev, hS.compare, self_mem_nhdsWithin] with t htδ hcmp ht
  have ht0 : (0 : ℝ) < t := ht
  exact (Regular.GlueRegularised.proof M.Xc d M.atlas S.R S.ρ S.η S.Cη (S.K t) t (S.e1 t) S.cutoff ht0
    (ht0.trans_le (S.e1_ge t ht0))
    (fun j x hx => ((closedBall_subset_closedBall (htδ j).le).trans
      (closedBall_subset_cthickening (mem_image_of_mem _ hx) _)).trans (hδs j)) hcmp).1

/- English proof (translation)
Rewrite using `[Finset.prod_comm, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `h0 : ‖c k‖ ≠ 0` using `norm_ne_zero_iff.mpr (hc k)`. Establish `hsum : ∀ s' : Finset ℕ, ‖c k‖ ^ (∑ p ∈ s', b p k) = ∏ p ∈ s', ‖c k‖ ^ b p k`. Introduce `s'`.

Proceed by induction on `s' using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert q s' hq ih => rw [Finset.sum_insert hq, Finset.prod_insert hq, zpow_add₀ h0, ih]`. Rewrite using `[Pi.add_apply, Finset.sum_apply, zpow_add₀ h0, hsum]`.
-/
theorem prod_norm_zpow_add_sum {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (a : K → ℤ) (s : Finset ℕ) (b : ℕ → K → ℤ) :
    (∏ k, ‖c k‖ ^ (a + ∑ p ∈ s, b p) k) = (∏ k, ‖c k‖ ^ a k) * ∏ p ∈ s, ∏ k, ‖c k‖ ^ b p k := by
  rw [Finset.prod_comm, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have h0 : ‖c k‖ ≠ 0 := norm_ne_zero_iff.mpr (hc k)
  have hsum : ∀ s' : Finset ℕ, ‖c k‖ ^ (∑ p ∈ s', b p k) = ∏ p ∈ s', ‖c k‖ ^ b p k := by
    intro s'
    induction s' using Finset.induction_on with
    | empty => simp
    | insert q s' hq ih => rw [Finset.sum_insert hq, Finset.prod_insert hq, zpow_add₀ h0, ih]
  rw [Pi.add_apply, Finset.sum_apply, zpow_add₀ h0, hsum]

end MuRegSmooth

open MuRegSmooth TopNPoly in

/- English proof (translation)
Introduce `II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B`. Use `filter_upwards [regWeight_smooth X.S X.S_tied] with t ht`. Establish `hPm : IsMultiHomogIdeal (mCoordIdeal D.y)` using `D.arith.2.1.2.1`. Use `set F : ((Σ k, ι k) → ℂ) → ℝ := fun z => X.S.ref.h z * Real.exp (X.S.regWeight t (X.M.proj z)) * ∏ p ∈ D.SB B, D.vertFactor p z with hFdef`. Establish `hpos : ∀ z ∈ mcPts (mCoordIdeal D.y), 0 < F z` using `fun z hz => mul_pos (mul_pos (X.S.ref.pos z hz.1) (Real.exp_pos _)) (Finset.prod_pos fun p hp => hV II Ψ K ι Ω E D p (Finset.mem_filter.1 hp).1 z hz)`.

Establish `hhom : ∀ z ∈ mcPts (mCoordIdeal D.y), ∀ c : K → ℂ, (∀ k, c k ≠ 0) → F (torusSmul c z) = (∏ k, ‖c k‖ ^ muTwDeg X.H B k) * F z`. Introduce `z hz c hc`. Establish `hcz : torusSmul c z ∈ mcPts (mCoordIdeal D.y)` using `mcPts_smul hPm c hc hz`. Establish `hproj : X.M.proj (torusSmul c z) = X.M.proj z` using `((X.M.fibre z hz _ hcz).2 ⟨c, hc, rfl⟩).symm`. Establish `href : X.S.ref.h (torusSmul c z) = (∏ k, ‖c k‖ ^ X.H.aMu k) * X.S.ref.h z`.

Rewrite using `[show torusSmul c z = fun p => c p.1 * z p from rfl, X.S.ref.smul c z hc, X.S.ref_deg]`. Both sides reduce to the same expression. Establish `hvf : ∏ p ∈ D.SB B, D.vertFactor p (torusSmul c z) = (∏ p ∈ D.SB B, ∏ k, ‖c k‖ ^ D.vdeg p k) * ∏ p ∈ D.SB B, D.vertFactor p z`. Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun p hp => (hVS II Ψ K ι Ω E D p (Finset.mem_filter.1 hp).1).1 z hz c hc`.

Simplify using `only [hFdef]`. Rewrite using `[href, hproj, hvf, muTwDeg, prod_norm_zpow_add_sum hc]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsm : SmoothAlong (mcPts (mCoordIdeal D.y)) F` using `smoothAlong_mul (smoothAlong_mul (smoothAlong_of_contDiffOn X.S.ref_smooth) (smoothAlong_exp (hP II Ψ K ι Ω E D X.M _ ht))) (smoothAlong_prod _ fun p hp => (hVS II Ψ K ι Ω E D p (Finset.mem_filter.1 hp).1).2)`. Take `⟨Z, hZa, hZs, hZh⟩` from `hE K ι (mCoordIdeal D.y) (muTwDeg X.H B) F hPm hpos hhom hsm`.

Unfold `muReg`. Use `smoothRep_smooth_of (Z := Z) hZa hZs fun z hz => ?_` and prove the remaining obligations. Take `⟨c, hc, hzc⟩` from `exists_eq_smul_orbitRep z`. Establish `hw0` using `orbitRep_blocks hz.1`. Establish `hwP : orbitRep z ∈ mcPts (mCoordIdeal D.y)`.

Establish `h` using `mcPts_smul hPm (fun k => (c k)⁻¹) (fun k => inv_ne_zero (hc k)) hz`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `p`. Establish `hp : z p = c p.1 * orbitRep z p` using `congrFun hzc p`. Rewrite using `[hp, ← mul_assoc, inv_mul_cancel₀ (hc _), one_mul]`.

Establish `hG0 : 0 < X.S.ref.h (orbitRep z) * Real.exp (X.S.regWeight t (X.M.proj (orbitRep z)))` using `mul_pos (X.S.ref.pos _ hw0) (Real.exp_pos _)`. Establish `hreg : (X.S.regLine t).h (orbitRep z) = X.S.ref.h (orbitRep z) * Real.exp (X.S.regWeight t (X.M.proj (orbitRep z)))` using `hermOfFun_h_orbitRep hz.1 hG0`. Establish `hFw : (X.S.regLine t).h (orbitRep z) * ∏ p ∈ D.SB B, D.vertFactor p (orbitRep z) = F (orbitRep z)`. Rewrite using `[hreg]`. Rewrite using `[hZh z hz, hermOfFun_h_smul hc hzc hz.1 (by rw [hFw]; exact hpos _ hwP), hFw]`.

Use `conv_lhs => rw [hzc]`. Conclude with `hhom _ hwP c hc`.
-/
theorem MuRegSmooth.proof (hE : HermExtend.Statement) (hP : ProjSmoothAlong.Statement)
    (hVS : VertFactorSmooth.Statement) (hV : VertFactorPos.Statement) : MuRegSmooth.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B
  filter_upwards [regWeight_smooth X.S X.S_tied] with t ht
  have hPm : IsMultiHomogIdeal (mCoordIdeal D.y) := D.arith.2.1.2.1
  set F : ((Σ k, ι k) → ℂ) → ℝ := fun z =>
    X.S.ref.h z * Real.exp (X.S.regWeight t (X.M.proj z)) * ∏ p ∈ D.SB B, D.vertFactor p z with hFdef
  have hpos : ∀ z ∈ mcPts (mCoordIdeal D.y), 0 < F z := fun z hz =>
    mul_pos (mul_pos (X.S.ref.pos z hz.1) (Real.exp_pos _))
      (Finset.prod_pos fun p hp => hV II Ψ K ι Ω E D p (Finset.mem_filter.1 hp).1 z hz)
  have hhom : ∀ z ∈ mcPts (mCoordIdeal D.y), ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
      F (torusSmul c z) = (∏ k, ‖c k‖ ^ muTwDeg X.H B k) * F z := by
    intro z hz c hc
    have hcz : torusSmul c z ∈ mcPts (mCoordIdeal D.y) := mcPts_smul hPm c hc hz
    have hproj : X.M.proj (torusSmul c z) = X.M.proj z :=
      ((X.M.fibre z hz _ hcz).2 ⟨c, hc, rfl⟩).symm
    have href : X.S.ref.h (torusSmul c z) = (∏ k, ‖c k‖ ^ X.H.aMu k) * X.S.ref.h z := by
      rw [show torusSmul c z = fun p => c p.1 * z p from rfl, X.S.ref.smul c z hc, X.S.ref_deg]
      rfl
    have hvf : ∏ p ∈ D.SB B, D.vertFactor p (torusSmul c z) =
        (∏ p ∈ D.SB B, ∏ k, ‖c k‖ ^ D.vdeg p k) * ∏ p ∈ D.SB B, D.vertFactor p z := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun p hp =>
        (hVS II Ψ K ι Ω E D p (Finset.mem_filter.1 hp).1).1 z hz c hc
    simp only [hFdef]
    rw [href, hproj, hvf, muTwDeg, prod_norm_zpow_add_sum hc]
    ring
  have hsm : SmoothAlong (mcPts (mCoordIdeal D.y)) F :=
    smoothAlong_mul (smoothAlong_mul (smoothAlong_of_contDiffOn X.S.ref_smooth)
      (smoothAlong_exp (hP II Ψ K ι Ω E D X.M _ ht)))
      (smoothAlong_prod _ fun p hp => (hVS II Ψ K ι Ω E D p (Finset.mem_filter.1 hp).1).2)
  obtain ⟨Z, hZa, hZs, hZh⟩ := hE K ι (mCoordIdeal D.y) (muTwDeg X.H B) F hPm hpos hhom hsm
  unfold muReg
  refine smoothRep_smooth_of (Z := Z) hZa hZs fun z hz => ?_
  obtain ⟨c, hc, hzc⟩ := exists_eq_smul_orbitRep z
  have hw0 := orbitRep_blocks hz.1
  have hwP : orbitRep z ∈ mcPts (mCoordIdeal D.y) := by
    have h := mcPts_smul hPm (fun k => (c k)⁻¹) (fun k => inv_ne_zero (hc k)) hz
    convert h using 1
    funext p
    have hp : z p = c p.1 * orbitRep z p := congrFun hzc p
    rw [hp, ← mul_assoc, inv_mul_cancel₀ (hc _), one_mul]
  have hG0 : 0 < X.S.ref.h (orbitRep z) * Real.exp (X.S.regWeight t (X.M.proj (orbitRep z))) :=
    mul_pos (X.S.ref.pos _ hw0) (Real.exp_pos _)
  have hreg : (X.S.regLine t).h (orbitRep z) =
      X.S.ref.h (orbitRep z) * Real.exp (X.S.regWeight t (X.M.proj (orbitRep z))) :=
    hermOfFun_h_orbitRep hz.1 hG0
  have hFw : (X.S.regLine t).h (orbitRep z) * ∏ p ∈ D.SB B, D.vertFactor p (orbitRep z) = F (orbitRep z) := by
    rw [hreg]
  rw [hZh z hz, hermOfFun_h_smul hc hzc hz.1 (by rw [hFw]; exact hpos _ hwP), hFw]
  conv_lhs => rw [hzc]
  exact hhom _ hwP c hc

end GroundTheory.Heights₂.Heights.LowerBoundFree
