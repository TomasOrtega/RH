import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPtsBddConv
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETailMass
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PModelFibreSumAeSheet
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PModelFibreFinite
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.LintegralFibSum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeI
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDensityNonnegOffNullSet
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocDensDivJacN
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv.Push.DCont

section General

variable {e : ℕ} {X : Type} [TopologicalSpace X]

def ReHolAt (A : FinHolAtlas e X) (f : X → ℝ) (y₀ : X) : Prop :=
  ∃ W : Set X, IsOpen W ∧ y₀ ∈ W ∧ ∃ G : X → ℂ, A.HoloOn W G ∧ ∀ z ∈ W, f z = (G z).re

/- English proof (translation)
Introduce `z hz`. Take `⟨j, hj⟩` from `A.cover z`. Establish `h1 : (A.chart j).symm (A.chart j z) = z` using `(A.chart j).left_inv hj`. Establish `hu : A.chart j z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W` using `⟨(A.chart j).map_source hj, by rw [Set.mem_preimage, h1]; exact hz⟩`. Establish `hc : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j z)` using `(h j _ hu).continuousAt`.

Establish `hc2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ (A.chart j)) z` using `ContinuousAt.comp hc ((A.chart j).continuousAt hj)`. Establish `hev : ((f ∘ (A.chart j).symm) ∘ (A.chart j)) =ᶠ[𝓝 z] f` using `by filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy`. Simplify using `[(A.chart j).left_inv hy]`. Conclude with `(hc2.congr hev).continuousWithinAt`.
-/
theorem holoOn_continuousOn {A : FinHolAtlas e X} {W : Set X} {f : X → ℂ} (h : A.HoloOn W f) :
    ContinuousOn f W := by
  intro z hz
  obtain ⟨j, hj⟩ := A.cover z
  have h1 : (A.chart j).symm (A.chart j z) = z := (A.chart j).left_inv hj
  have hu : A.chart j z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W :=
    ⟨(A.chart j).map_source hj, by rw [Set.mem_preimage, h1]; exact hz⟩
  have hc : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j z) := (h j _ hu).continuousAt
  have hc2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ (A.chart j)) z :=
    ContinuousAt.comp hc ((A.chart j).continuousAt hj)
  have hev : ((f ∘ (A.chart j).symm) ∘ (A.chart j)) =ᶠ[𝓝 z] f := by
    filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
    simp [(A.chart j).left_inv hy]
  exact (hc2.congr hev).continuousWithinAt

/- English proof (translation)
Take `⟨W, hW, hy, G, hG, hWG⟩` from `hg`. Take `⟨T, hT, hTo, hyT⟩` from `mem_nhds_iff.1 h`. Conclude with `⟨W ∩ T, hW.inter hTo, ⟨hy, hyT⟩, G, fun j u hu => hG j u ⟨hu.1, hu.2.1⟩, fun z hz => (hT hz.2).trans (hWG z hz.1)⟩`.
-/
theorem ReHolAt.congr {A : FinHolAtlas e X} {f g : X → ℝ} {y₀ : X} (hg : ReHolAt A g y₀)
    (h : f =ᶠ[𝓝 y₀] g) : ReHolAt A f y₀ := by
  obtain ⟨W, hW, hy, G, hG, hWG⟩ := hg
  obtain ⟨T, hT, hTo, hyT⟩ := mem_nhds_iff.1 h
  exact ⟨W ∩ T, hW.inter hTo, ⟨hy, hyT⟩, G, fun j u hu => hG j u ⟨hu.1, hu.2.1⟩,
    fun z hz => (hT hz.2).trans (hWG z hz.1)⟩

/- English proof (translation)
Take `⟨W, hW, hy, G, hG, hWG⟩` from `hf`. Take `⟨W', hW', hy', G', hG', hWG'⟩` from `hg`. Use `⟨W ∩ W', hW.inter hW', ⟨hy, hy'⟩, fun z => G z + G' z, fun j u hu => ?_, fun z hz => ?_⟩` and prove the remaining obligations. Conclude with `(hG j u ⟨hu.1, hu.2.1⟩).add (hG' j u ⟨hu.1, hu.2.2⟩)`. Use `show f z + g z = (G z + G' z).re`.

Rewrite using `[hWG z hz.1, hWG' z hz.2, Complex.add_re]`.
-/
theorem ReHolAt.add {A : FinHolAtlas e X} {f g : X → ℝ} {y₀ : X} (hf : ReHolAt A f y₀)
    (hg : ReHolAt A g y₀) : ReHolAt A (fun y => f y + g y) y₀ := by
  obtain ⟨W, hW, hy, G, hG, hWG⟩ := hf
  obtain ⟨W', hW', hy', G', hG', hWG'⟩ := hg
  refine ⟨W ∩ W', hW.inter hW', ⟨hy, hy'⟩, fun z => G z + G' z, fun j u hu => ?_, fun z hz => ?_⟩
  · exact (hG j u ⟨hu.1, hu.2.1⟩).add (hG' j u ⟨hu.1, hu.2.2⟩)
  · show f z + g z = (G z + G' z).re
    rw [hWG z hz.1, hWG' z hz.2, Complex.add_re]

/- English proof (translation)
Take `⟨W, hW, hy, G, hG, hWG⟩` from `hf`. Use `⟨W, hW, hy, fun z => (c : ℂ) * G z, fun j u hu => ?_, fun z hz => ?_⟩` and prove the remaining obligations. Conclude with `analyticAt_const.mul (hG j u hu)`. Use `show c * f z = ((c : ℂ) * G z).re`. Rewrite using `[hWG z hz, Complex.re_ofReal_mul]`.
-/
theorem ReHolAt.const_mul {A : FinHolAtlas e X} {f : X → ℝ} {y₀ : X} (c : ℝ) (hf : ReHolAt A f y₀) :
    ReHolAt A (fun y => c * f y) y₀ := by
  obtain ⟨W, hW, hy, G, hG, hWG⟩ := hf
  refine ⟨W, hW, hy, fun z => (c : ℂ) * G z, fun j u hu => ?_, fun z hz => ?_⟩
  · exact analyticAt_const.mul (hG j u hu)
  · show c * f z = ((c : ℂ) * G z).re
    rw [hWG z hz, Complex.re_ofReal_mul]

/- English proof (translation)
Use `(hf.add (hg.const_mul (-1))).congr (Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Use `show f y - g y = f y + -1 * g y`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ReHolAt.sub {A : FinHolAtlas e X} {f g : X → ℝ} {y₀ : X} (hf : ReHolAt A f y₀)
    (hg : ReHolAt A g y₀) : ReHolAt A (fun y => f y - g y) y₀ := by
  refine (hf.add (hg.const_mul (-1))).congr (Eventually.of_forall fun y => ?_)
  show f y - g y = f y + -1 * g y
  ring

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Use `⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ => 0, fun j u _ => analyticAt_const, ?_⟩` and prove the remaining obligations. Introduce `z _`. Simplify using the standard rewrite rules.

Consider the case `insert a s ha ih`. Use `((hf a (Finset.mem_insert_self _ _)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))).congr (Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Use `show ∑ i ∈ insert a s, f i y = f a y + ∑ i ∈ s, f i y`. Rewrite using `[Finset.sum_insert ha]`.
-/
theorem ReHolAt.sum {A : FinHolAtlas e X} {J : Type} (s : Finset J) {f : J → X → ℝ} {y₀ : X}
    (hf : ∀ i ∈ s, ReHolAt A (f i) y₀) : ReHolAt A (fun y => ∑ i ∈ s, f i y) y₀ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ => 0, fun j u _ => analyticAt_const, ?_⟩
    intro z _
    simp
  | insert a s ha ih =>
    refine ((hf a (Finset.mem_insert_self _ _)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))).congr (Eventually.of_forall fun y => ?_)
    show ∑ i ∈ insert a s, f i y = f a y + ∑ i ∈ s, f i y
    rw [Finset.sum_insert ha]

/- English proof (translation)
Establish `hS : IsOpen {w : ℂ | w / f y₀ ∈ Complex.slitPlane}` using `Complex.isOpen_slitPlane.preimage (continuous_id.div_const _)`. Establish `hW'` using `(holoOn_continuousOn hf).isOpen_inter_preimage hW hS`. Use `⟨_, hW', ⟨hy, ?_⟩, fun z => Complex.log (f z / f y₀) + (Real.log ‖f y₀‖ : ℂ), fun j u hu => ?_, fun z hz => ?_⟩` and prove the remaining obligations. Use `show f y₀ / f y₀ ∈ Complex.slitPlane`. Rewrite using `[div_self h0]`.

Conclude with `Complex.one_mem_slitPlane`. Establish `h1 : AnalyticAt ℂ (f ∘ (A.chart j).symm) u` using `hf j u ⟨hu.1, hu.2.1⟩`. Conclude with `((h1.div_const (c := f y₀)).clog hu.2.2).add analyticAt_const`. Establish `hz0 : f z ≠ 0` using `fun h => by`. Use `Complex.slitPlane_ne_zero hz.2` as an intermediate fact.

Simplify using `[h] at this`. Rewrite using `[Complex.add_re, Complex.log_re, norm_div, Real.log_div (norm_ne_zero_iff.2 hz0) (norm_ne_zero_iff.2 h0), Complex.ofReal_re]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem reHolAt_log_norm {A : FinHolAtlas e X} {W : Set X} {f : X → ℂ} {y₀ : X} (hW : IsOpen W)
    (hf : A.HoloOn W f) (hy : y₀ ∈ W) (h0 : f y₀ ≠ 0) :
    ReHolAt A (fun y => Real.log ‖f y‖) y₀ := by
  have hS : IsOpen {w : ℂ | w / f y₀ ∈ Complex.slitPlane} :=
    Complex.isOpen_slitPlane.preimage (continuous_id.div_const _)
  have hW' := (holoOn_continuousOn hf).isOpen_inter_preimage hW hS
  refine ⟨_, hW', ⟨hy, ?_⟩, fun z => Complex.log (f z / f y₀) + (Real.log ‖f y₀‖ : ℂ),
    fun j u hu => ?_, fun z hz => ?_⟩
  · show f y₀ / f y₀ ∈ Complex.slitPlane
    rw [div_self h0]
    exact Complex.one_mem_slitPlane
  · have h1 : AnalyticAt ℂ (f ∘ (A.chart j).symm) u := hf j u ⟨hu.1, hu.2.1⟩
    exact ((h1.div_const (c := f y₀)).clog hu.2.2).add analyticAt_const
  · have hz0 : f z ≠ 0 := fun h => by
      have := Complex.slitPlane_ne_zero hz.2
      simp [h] at this
    rw [Complex.add_re, Complex.log_re, norm_div, Real.log_div (norm_ne_zero_iff.2 hz0) (norm_ne_zero_iff.2 h0),
      Complex.ofReal_re]
    ring

end General

section Model

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {d : ℕ}

def IsSecOn (M : CxModel P d) (U : Set M.Xc) (s : M.Xc → (Σ k, ι k) → ℂ) : Prop :=
  (∀ y ∈ U, s y ∈ mcPts P ∧ M.proj (s y) = y) ∧ ∀ p, M.atlas.HoloOn U fun y => s y p

/- English proof (translation)
Establish `hz` using `(hs.1 y₀ hy).1`. Establish `hz'` using `(hs'.1 y₀ hy').1`. Use `choose i hi using hz.1`. Take `⟨c₀, hc₀, hcz⟩` from `(M.fibre _ hz _ hz').1 (by rw [(hs.1 y₀ hy).2, (hs'.1 y₀ hy').2])`. Establish `hi' : ∀ k, s' y₀ ⟨k, i k⟩ ≠ 0`.

Introduce `k`. Rewrite using `[hcz]`. Conclude with `mul_ne_zero (hc₀ k) (hi k)`. Establish `hR : ∀ k ∈ (Finset.univ : Finset K), ReHolAt M.atlas (fun y => (a k : ℝ) * (Real.log ‖s' y ⟨k, i k⟩‖ - Real.log ‖s y ⟨k, i k⟩‖)) y₀` using `fun k _ => ((reHolAt_log_norm hU' (hs'.2 _) hy' (hi' k)).sub (reHolAt_log_norm hU (hs.2 _) hy (hi k))).const_mul _`. Use `(ReHolAt.sum Finset.univ hR).congr ?_` and prove the remaining obligations.

Establish `hev : ∀ᶠ y in 𝓝 y₀, ∀ k, s y ⟨k, i k⟩ ≠ 0` using `eventually_all.2 fun k => ((holoOn_continuousOn (hs.2 ⟨k, i k⟩)).continuousAt (hU.mem_nhds hy)).eventually_ne (hi k)`. Use `filter_upwards [hU.mem_nhds hy, hU'.mem_nhds hy', hev] with y h1 h2 h3`. Establish `hm` using `(hs.1 y h1).1`. Establish `hm'` using `(hs'.1 y h2).1`. Take `⟨c, hc, hcy⟩` from `(M.fibre _ hm _ hm').1 (by rw [(hs.1 y h1).2, (hs'.1 y h2).2])`.

Establish `hnc : ∀ k, ‖c k‖ ≠ 0` using `fun k => norm_ne_zero_iff.2 (hc k)`. Rewrite using `[hcy, hF _ hm c hc, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hnc k)) (hpos _ hm).ne', Real.log_prod (fun k _ => zpow_ne_zero _ (hnc k)), add_sub_cancel_right]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `h4 : torusSmul c (s y) ⟨k, i k⟩ = c k * s y ⟨k, i k⟩` using `rfl`. Rewrite using `[h4, Real.log_zpow, norm_mul, Real.log_mul (hnc k) (norm_ne_zero_iff.2 (h3 k)), add_sub_cancel_right]`.
-/
theorem reHolAt_log_sections {M : CxModel P d} {U U' : Set M.Xc} {s s' : M.Xc → (Σ k, ι k) → ℂ}
    {a : K → ℤ} {F : ((Σ k, ι k) → ℂ) → ℝ} (hU : IsOpen U) (hU' : IsOpen U') (hs : IsSecOn M U s)
    (hs' : IsSecOn M U' s')
    (hF : ∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → F (torusSmul c z) = (∏ k, ‖c k‖ ^ a k) * F z)
    (hpos : ∀ z ∈ mcPts P, 0 < F z) {y₀ : M.Xc} (hy : y₀ ∈ U) (hy' : y₀ ∈ U') :
    ReHolAt M.atlas (fun y => Real.log (F (s' y)) - Real.log (F (s y))) y₀ := by
  classical
  have hz := (hs.1 y₀ hy).1
  have hz' := (hs'.1 y₀ hy').1
  choose i hi using hz.1
  obtain ⟨c₀, hc₀, hcz⟩ := (M.fibre _ hz _ hz').1 (by rw [(hs.1 y₀ hy).2, (hs'.1 y₀ hy').2])
  have hi' : ∀ k, s' y₀ ⟨k, i k⟩ ≠ 0 := by
    intro k
    rw [hcz]
    exact mul_ne_zero (hc₀ k) (hi k)
  have hR : ∀ k ∈ (Finset.univ : Finset K), ReHolAt M.atlas
      (fun y => (a k : ℝ) * (Real.log ‖s' y ⟨k, i k⟩‖ - Real.log ‖s y ⟨k, i k⟩‖)) y₀ := fun k _ =>
    ((reHolAt_log_norm hU' (hs'.2 _) hy' (hi' k)).sub
      (reHolAt_log_norm hU (hs.2 _) hy (hi k))).const_mul _
  refine (ReHolAt.sum Finset.univ hR).congr ?_
  have hev : ∀ᶠ y in 𝓝 y₀, ∀ k, s y ⟨k, i k⟩ ≠ 0 := eventually_all.2 fun k =>
    ((holoOn_continuousOn (hs.2 ⟨k, i k⟩)).continuousAt (hU.mem_nhds hy)).eventually_ne (hi k)
  filter_upwards [hU.mem_nhds hy, hU'.mem_nhds hy', hev] with y h1 h2 h3
  have hm := (hs.1 y h1).1
  have hm' := (hs'.1 y h2).1
  obtain ⟨c, hc, hcy⟩ := (M.fibre _ hm _ hm').1 (by rw [(hs.1 y h1).2, (hs'.1 y h2).2])
  have hnc : ∀ k, ‖c k‖ ≠ 0 := fun k => norm_ne_zero_iff.2 (hc k)
  rw [hcy, hF _ hm c hc, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hnc k))
    (hpos _ hm).ne', Real.log_prod (fun k _ => zpow_ne_zero _ (hnc k)), add_sub_cancel_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h4 : torusSmul c (s y) ⟨k, i k⟩ = c k * s y ⟨k, i k⟩ := rfl
  rw [h4, Real.log_zpow, norm_mul, Real.log_mul (hnc k) (norm_ne_zero_iff.2 (h3 k)), add_sub_cancel_right]

/- English proof (translation)
Use `set x := (M.atlas.chart j).symm y with hx`. Take `⟨U₁, hU₁, hx₁, -, s₁, hs₁, hh₁, G₁, hG₁, he₁⟩` from `hsec x x ⟨Q.mem_U x, hyY⟩`. Take `⟨U₂, hU₂, hx₂, -, s₂, hs₂, hh₂, G₂, hG₂, he₂⟩` from `hsec x₀ x ⟨hx₀, hyY⟩`. Take `⟨W, hW, hxW, G₃, hG₃, he₃⟩` from `(reHolAt_log_sections (M := M) (F := B.h) (a := B.a) hU₂ hU₁ ⟨hs₂, hh₂⟩ ⟨hs₁, hh₁⟩ (fun z _ c hc => B.smul c z hc) (fun z hz => B.pos z hz.1) hx₂ hx₁).const_mul c`. Establish `hOo : IsOpen ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' (U₁ ∩ U₂ ∩ W))` using `(M.atlas.chart j).isOpen_inter_preimage_symm ((hU₁.inter hU₂).inter hW)`.

Establish `hyO : y ∈ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' (U₁ ∩ U₂ ∩ W)` using `⟨hy, ⟨⟨hx₁, hx₂⟩, hxW⟩⟩`. Establish `h1 : (fun y' => Q.φ x ((M.atlas.chart j).symm y')) =ᶠ[nhds y] (fun w => (fun y' => Q.φ x₀ ((M.atlas.chart j).symm y')) w + ((fun w' => G₁ ((M.atlas.chart j).symm w') - G₂ ((M.atlas.chart j).symm w') + G₃ ((M.atlas.chart j).symm w')) w).re)` using `by filter_upwards [hOo.mem_nhds hyO] with w hw`. Establish `e1` using `he₁ _ hw.2.1.1`. Establish `e2` using `he₂ _ hw.2.1.2`. Establish `e3` using `he₃ _ hw.2.2`.

Simplify using `only [Complex.add_re, Complex.sub_re] at *`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hessCGerm _ _ _ h1]`. Establish `hopen : IsOpen ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' (Q.U x₀ ∩ Y))` using `(M.atlas.chart j).isOpen_inter_preimage_symm ((Q.isOpen_U x₀).inter hY)`. Establish `hsmooth : ContDiffAt ℝ 2 (fun y' => Q.φ x₀ ((M.atlas.chart j).symm y')) y` using `((hsm x₀ j).contDiffAt (hopen.mem_nhds ⟨hy, ⟨hx₀, hyY⟩⟩)).of_le (WithTop.coe_le_coe.2 le_top)`.

Conclude with `ReciprocityTheory.AnForm.A.hessC_add_re_analytic _ _ _ hsmooth (((hG₁ j y ⟨hy, hx₁⟩).sub (hG₂ j y ⟨hy, hx₂⟩)).add (hG₃ j y ⟨hy, hxW⟩))`.
-/
theorem hessC_base_eq {M : CxModel P d} {Y : Set M.Xc} (c : ℝ) (B : HermLine ι) (Q : LocPot M.Xc)
    (j : Fin M.atlas.n)
    (hsm : ∀ x, M.atlas.SmoothOn (Q.U x ∩ Y) (Q.φ x)) (hY : IsOpen Y)
    (hsec : ∀ x, ∀ y₀ ∈ Q.U x ∩ Y, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ Q.U x ∩ Y ∧
      ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (P) ∧ M.proj (s y') = y') ∧
        (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧
          ∀ y' ∈ U, Q.φ x y' - (fun z => c * Real.log (B.h z)) (s y') = (G y').re)
    {y : Fin d → ℂ} (hy : y ∈ (M.atlas.chart j).target) (hyY : (M.atlas.chart j).symm y ∈ Y)
    {x₀ : M.Xc} (hx₀ : (M.atlas.chart j).symm y ∈ Q.U x₀) :
    hessC (fun y' => Q.φ ((M.atlas.chart j).symm y) ((M.atlas.chart j).symm y')) y =
      hessC (fun y' => Q.φ x₀ ((M.atlas.chart j).symm y')) y := by
  set x := (M.atlas.chart j).symm y with hx
  obtain ⟨U₁, hU₁, hx₁, -, s₁, hs₁, hh₁, G₁, hG₁, he₁⟩ := hsec x x ⟨Q.mem_U x, hyY⟩
  obtain ⟨U₂, hU₂, hx₂, -, s₂, hs₂, hh₂, G₂, hG₂, he₂⟩ := hsec x₀ x ⟨hx₀, hyY⟩
  obtain ⟨W, hW, hxW, G₃, hG₃, he₃⟩ :=
    (reHolAt_log_sections (M := M) (F := B.h) (a := B.a) hU₂ hU₁ ⟨hs₂, hh₂⟩ ⟨hs₁, hh₁⟩
      (fun z _ c hc => B.smul c z hc) (fun z hz => B.pos z hz.1) hx₂ hx₁).const_mul c
  have hOo : IsOpen ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' (U₁ ∩ U₂ ∩ W)) :=
    (M.atlas.chart j).isOpen_inter_preimage_symm ((hU₁.inter hU₂).inter hW)
  have hyO : y ∈ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' (U₁ ∩ U₂ ∩ W) :=
    ⟨hy, ⟨⟨hx₁, hx₂⟩, hxW⟩⟩
  have h1 : (fun y' => Q.φ x ((M.atlas.chart j).symm y')) =ᶠ[nhds y]
      (fun w => (fun y' => Q.φ x₀ ((M.atlas.chart j).symm y')) w +
        ((fun w' => G₁ ((M.atlas.chart j).symm w') - G₂ ((M.atlas.chart j).symm w') +
          G₃ ((M.atlas.chart j).symm w')) w).re) := by
    filter_upwards [hOo.mem_nhds hyO] with w hw
    have e1 := he₁ _ hw.2.1.1
    have e2 := he₂ _ hw.2.1.2
    have e3 := he₃ _ hw.2.2
    simp only [Complex.add_re, Complex.sub_re] at *
    linarith
  rw [hessCGerm _ _ _ h1]
  have hopen : IsOpen ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' (Q.U x₀ ∩ Y)) :=
    (M.atlas.chart j).isOpen_inter_preimage_symm ((Q.isOpen_U x₀).inter hY)
  have hsmooth : ContDiffAt ℝ 2 (fun y' => Q.φ x₀ ((M.atlas.chart j).symm y')) y :=
    ((hsm x₀ j).contDiffAt (hopen.mem_nhds ⟨hy, ⟨hx₀, hyY⟩⟩)).of_le (WithTop.coe_le_coe.2 le_top)
  exact ReciprocityTheory.AnForm.A.hessC_add_re_analytic _ _ _ hsmooth
    (((hG₁ j y ⟨hy, hx₁⟩).sub (hG₂ j y ⟨hy, hx₂⟩)).add (hG₃ j y ⟨hy, hxW⟩))

end Model

/- English proof (translation)
Introduce `K _ ι _ P n M Y c B Φ j hY hΦs hsec y₀ hy₀`. Apply `ContinuousAt.continuousWithinAt` to reduce the goal to its premises. Use `set x₀ := (M.atlas.chart j).symm y₀ with hx₀`. Establish `hVo : IsOpen ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' (Y ∩ ⋂ i, (Φ i).U x₀))` using `(M.atlas.chart j).isOpen_inter_preimage_symm (hY.inter (isOpen_iInter_of_finite fun i => (Φ i).isOpen_U _))`. Establish `hy0V : y₀ ∈ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' (Y ∩ ⋂ i, (Φ i).U x₀)` using `⟨hy₀.1, hy₀.2, Set.mem_iInter.2 fun i => (Φ i).mem_U _⟩`.

Establish `heq : maDens (fun i y' => (Φ i).φ x₀ ((M.atlas.chart j).symm y')) =ᶠ[nhds y₀] locDens M.atlas Φ j` using `by filter_upwards [hVo.mem_nhds hy0V] with y hy`. Unfold `locDens`. Use `maDens_congr_hessC _ _ _ fun i => ?_` and prove the remaining obligations. Conclude with `(hessC_base_eq (c i) (B i) (Φ i) j (hΦs i) hY (hsec i) hy.1 hy.2.1 (Set.mem_iInter.1 hy.2.2 i)).symm`. Use `ContinuousAt.congr ?_ heq` and prove the remaining obligations.

Use `(maDens_continuousOn _ _ hVo fun i => ?_).continuousAt (hVo.mem_nhds hy0V)` and prove the remaining obligations. Conclude with `((hΦs i x₀ j).of_le (WithTop.coe_le_coe.2 le_top)).mono fun y hy => ⟨hy.1, Set.mem_iInter.1 hy.2.2 i, hy.2.1⟩`.
-/
theorem locDens_continuousOn_of_sections : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (Y : Set M.Xc) (c : Fin n → ℝ) (B : Fin n → HermLine ι) (Φ : Fin n → LocPot M.Xc) (j : Fin M.atlas.n), IsOpen Y → (∀ i x, M.atlas.SmoothOn ((Φ i).U x ∩ Y) ((Φ i).φ x)) → (∀ i, ∀ x, ∀ y₀ ∈ (Φ i).U x ∩ Y, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Φ i).U x ∩ Y ∧ ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (P) ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧ ∀ y' ∈ U, (Φ i).φ x y' - (fun z => c i * Real.log ((B i).h z)) (s y') = (G y').re) → ContinuousOn (locDens M.atlas Φ j) ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' Y) := by
  intro K _ ι _ P n M Y c B Φ j hY hΦs hsec y₀ hy₀
  apply ContinuousAt.continuousWithinAt
  set x₀ := (M.atlas.chart j).symm y₀ with hx₀
  have hVo : IsOpen ((M.atlas.chart j).target ∩
      (M.atlas.chart j).symm ⁻¹' (Y ∩ ⋂ i, (Φ i).U x₀)) :=
    (M.atlas.chart j).isOpen_inter_preimage_symm
      (hY.inter (isOpen_iInter_of_finite fun i => (Φ i).isOpen_U _))
  have hy0V : y₀ ∈ (M.atlas.chart j).target ∩
      (M.atlas.chart j).symm ⁻¹' (Y ∩ ⋂ i, (Φ i).U x₀) :=
    ⟨hy₀.1, hy₀.2, Set.mem_iInter.2 fun i => (Φ i).mem_U _⟩
  have heq : maDens (fun i y' => (Φ i).φ x₀ ((M.atlas.chart j).symm y')) =ᶠ[nhds y₀]
      locDens M.atlas Φ j := by
    filter_upwards [hVo.mem_nhds hy0V] with y hy
    unfold locDens
    refine maDens_congr_hessC _ _ _ fun i => ?_
    exact (hessC_base_eq (c i) (B i) (Φ i) j (hΦs i) hY (hsec i) hy.1 hy.2.1
      (Set.mem_iInter.1 hy.2.2 i)).symm
  refine ContinuousAt.congr ?_ heq
  refine (maDens_continuousOn _ _ hVo fun i => ?_).continuousAt (hVo.mem_nhds hy0V)
  exact ((hΦs i x₀ j).of_le (WithTop.coe_le_coe.2 le_top)).mono
    fun y hy => ⟨hy.1, Set.mem_iInter.1 hy.2.2 i, hy.2.1⟩

end GlobalTheory.CompanionTheory.Ar.Giv.Push.DCont
