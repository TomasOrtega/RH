import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralCongrPotentials
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionFamilyDefectFormula
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFunctorialHolomorphic
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace PositivityTheory.Xgp.vert_deg

/- English proof (translation)
Introduce `j hj`. Use `potSmoothAt A Q h x j ⟨(A.chart j).map_source hj, ?_⟩` and prove the remaining obligations. Use `show (A.chart j).symm (A.chart j x) ∈ Q.U x`. Rewrite using `[(A.chart j).left_inv hj]`. Conclude with `Q.mem_U x`.
-/
theorem isC2At_of_isPotential {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {Q : LocPot X}
    (h : IsPotential A Q) (x : X) : IsTwiceDifferentiableAt A Q x := by
  intro j hj
  refine potSmoothAt A Q h x j ⟨(A.chart j).map_source hj, ?_⟩
  show (A.chart j).symm (A.chart j x) ∈ Q.U x
  rw [(A.chart j).left_inv hj]
  exact Q.mem_U x

/- English proof (translation)
Take `⟨Ψ, hΨ⟩` from `goodProjExists K ι P D hP`. Conclude with `fun j => GlobalTheory.CompanionTheory.Ar.Cmp.OneSlot.zeros_null R Ψ hP hΨ hs hsP j`.
-/
theorem isNull_zeros {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {D : ℕ}
    (R : AnLogRes P J D) (hP : IsArithVar P (D + 1)) {s : MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a)
    (hsP : s ∉ P) : IsNull R.A {x | eval (R.lift x x) (map (Int.castRingHom ℂ) s) = 0} := by
  obtain ⟨Ψ, hΨ⟩ := goodProjExists K ι P D hP
  exact fun j => GlobalTheory.CompanionTheory.Ar.Cmp.OneSlot.zeros_null R Ψ hP hΨ hs hsP j

/- English proof (translation)
Use `⟨{y | y ∈ U ∧ F y / F x ∈ Complex.slitPlane}, ?_, ⟨hx, ?_⟩, fun y hy => hy.1, fun y => Complex.log (F y / F x) + ((Real.log ‖F x‖ : ℝ) : ℂ), fun j y hy => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Use `isOpen_iff_mem_nhds.mpr fun z hz => ?_` and prove the remaining obligations. Establish `hc` using `GlobalTheory.CompanionTheory.Ar.PB.Proj.continuousAt_of_holoOn A hF hz.1`. Use `filter_upwards [hU.mem_nhds hz.1, (hc.div_const (F x)).eventually_mem (Complex.isOpen_slitPlane.mem_nhds hz.2)] with w h1 h2`. Conclude with `⟨h1, h2⟩`.

Rewrite using `[div_self h0]`. Conclude with `Complex.one_mem_slitPlane`. Establish `h1 : AnalyticAt ℂ (fun y' => F ((A.chart j).symm y') / F x) y` using `(hF j y ⟨hy.1, hy.2.1⟩).div analyticAt_const h0`. Conclude with `(h1.clog hy.2.2).add analyticAt_const`. Establish `hq : F y / F x ≠ 0` using `Complex.slitPlane_ne_zero hy.2`.

Establish `hy0 : F y ≠ 0` using `fun h => hq (by rw [h, zero_div])`. Use `⟨hy0, ?_⟩` and prove the remaining obligations. Rewrite using `[Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div, Real.log_div (norm_ne_zero_iff.2 hy0) (norm_ne_zero_iff.2 h0)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_log {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {U : Set X} (hU : IsOpen U)
    {F : X → ℂ} (hF : A.HoloOn U F) {x : X} (hx : x ∈ U) (h0 : F x ≠ 0) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∃ G : X → ℂ, A.HoloOn V G ∧
      ∀ y ∈ V, F y ≠ 0 ∧ Real.log ‖F y‖ = (G y).re := by
  refine ⟨{y | y ∈ U ∧ F y / F x ∈ Complex.slitPlane}, ?_, ⟨hx, ?_⟩, fun y hy => hy.1,
    fun y => Complex.log (F y / F x) + ((Real.log ‖F x‖ : ℝ) : ℂ), fun j y hy => ?_, fun y hy => ?_⟩
  · refine isOpen_iff_mem_nhds.mpr fun z hz => ?_
    have hc := GlobalTheory.CompanionTheory.Ar.PB.Proj.continuousAt_of_holoOn A hF hz.1
    filter_upwards [hU.mem_nhds hz.1, (hc.div_const (F x)).eventually_mem
      (Complex.isOpen_slitPlane.mem_nhds hz.2)] with w h1 h2
    exact ⟨h1, h2⟩
  · rw [div_self h0]
    exact Complex.one_mem_slitPlane
  · have h1 : AnalyticAt ℂ (fun y' => F ((A.chart j).symm y') / F x) y :=
      (hF j y ⟨hy.1, hy.2.1⟩).div analyticAt_const h0
    exact (h1.clog hy.2.2).add analyticAt_const
  · have hq : F y / F x ≠ 0 := Complex.slitPlane_ne_zero hy.2
    have hy0 : F y ≠ 0 := fun h => hq (by rw [h, zero_div])
    refine ⟨hy0, ?_⟩
    rw [Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div,
      Real.log_div (norm_ne_zero_iff.2 hy0) (norm_ne_zero_iff.2 h0)]
    ring

/- English proof (translation)
Break down `h with rfl | ⟨f, g, df, dg, hf, hg, hfP, hgP, -, hn, -, -⟩` into its components or cases. Use `⟨∅, fun j => by simp, fun x _ => ⟨Set.univ, isOpen_univ, Set.mem_univ x, fun _ => 0, fun j => analyticOnNhd_const, fun y _ => by simp⟩⟩` and prove the remaining obligations. Use `⟨{x | eval (R.lift x x) (map (Int.castRingHom ℂ) f) = 0} ∪ {x | eval (R.lift x x) (map (Int.castRingHom ℂ) g) = 0}, fun j => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[Set.preimage_union, Set.inter_union_distrib_left]`. Conclude with `measure_union_null (isNull_zeros R hP hf hfP j) (isNull_zeros R hP hg hgP j)`.

Simplify using `only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or] at hx`. Take `⟨V, hV, hxV, hVU, G, hG, hGe⟩` from `exists_log R.A (R.isOpen_U x) (holoOn_eval_lift R x f) (R.mem_U x) hx.1`. Take `⟨V', hV', hxV', -, G', hG', hGe'⟩` from `exists_log R.A (R.isOpen_U x) (holoOn_eval_lift R x g) (R.mem_U x) hx.2`. Use `⟨V ∩ V', hV.inter hV', ⟨hxV, hxV'⟩, fun y => G y - G' y, fun j y hy => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Conclude with `(hG j y ⟨hy.1, hy.2.1⟩).sub (hG' j y ⟨hy.1, hy.2.2⟩)`.

Establish `hz` using `R.mem x y (hVU hy.1)`. Establish `e` using `congrArg Real.log (hn _ hz)`. Rewrite `e` using `[Real.log_mul (norm_ne_zero_iff.2 (hGe y hy.1).1) (B.pos _ hz.1).ne', Real.log_mul (norm_ne_zero_iff.2 (hGe' y hy.2).1) (A.pos _ hz.1).ne', (hGe y hy.1).2, (hGe' y hy.2).2]`. Use `show Real.log (A.h (R.lift x y)) - Real.log (B.h (R.lift x y)) = (G y - G' y).re`. Rewrite using `[Complex.sub_re]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_samePot {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {D : ℕ}
    (R : AnLogRes P J D) (hP : IsArithVar P (D + 1)) {T : Finset ℕ} {α : ℕ → ℝ} {A B : HermLine ι}
    (h : A = B ∨ VertClose P T α A B) :
    ∃ N : Set R.X, IsNull R.A N ∧ SamePot R.A Nᶜ (potOf R A) (potOf R B) := by
  rcases h with rfl | ⟨f, g, df, dg, hf, hg, hfP, hgP, -, hn, -, -⟩
  · refine ⟨∅, fun j => by simp, fun x _ => ⟨Set.univ, isOpen_univ, Set.mem_univ x, fun _ => 0,
      fun j => analyticOnNhd_const, fun y _ => by simp⟩⟩
  · refine ⟨{x | eval (R.lift x x) (map (Int.castRingHom ℂ) f) = 0} ∪
      {x | eval (R.lift x x) (map (Int.castRingHom ℂ) g) = 0}, fun j => ?_, fun x hx => ?_⟩
    · rw [Set.preimage_union, Set.inter_union_distrib_left]
      exact measure_union_null (isNull_zeros R hP hf hfP j) (isNull_zeros R hP hg hgP j)
    · simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or] at hx
      obtain ⟨V, hV, hxV, hVU, G, hG, hGe⟩ :=
        exists_log R.A (R.isOpen_U x) (holoOn_eval_lift R x f) (R.mem_U x) hx.1
      obtain ⟨V', hV', hxV', -, G', hG', hGe'⟩ :=
        exists_log R.A (R.isOpen_U x) (holoOn_eval_lift R x g) (R.mem_U x) hx.2
      refine ⟨V ∩ V', hV.inter hV', ⟨hxV, hxV'⟩, fun y => G y - G' y, fun j y hy => ?_, fun y hy => ?_⟩
      · exact (hG j y ⟨hy.1, hy.2.1⟩).sub (hG' j y ⟨hy.1, hy.2.2⟩)
      · have hz := R.mem x y (hVU hy.1)
        have e := congrArg Real.log (hn _ hz)
        rw [Real.log_mul (norm_ne_zero_iff.2 (hGe y hy.1).1) (B.pos _ hz.1).ne',
          Real.log_mul (norm_ne_zero_iff.2 (hGe' y hy.2).1) (A.pos _ hz.1).ne',
          (hGe y hy.1).2, (hGe' y hy.2).2] at e
        show Real.log (A.h (R.lift x y)) - Real.log (B.h (R.lift x y)) = (G y - G' y).re
        rw [Complex.sub_re]
        linarith

end PositivityTheory.Xgp.vert_deg

/- English proof (translation)
Introduce `hE K _ ι _ P D L L' T α hP hL hL' hV Am s hAm hs`. Take `⟨J, ⟨R⟩⟩` from `exists_anLogRes hE hP`. Use `choose N hN hS using fun j => PositivityTheory.Xgp.vert_deg.exists_samePot R hP (hV j)`. Rewrite using `[ptsIntegral_eq_mInt' hE resBridge R hP hL hAm hs, ptsIntegral_eq_mInt' hE resBridge R hP hL' hAm hs]`. Use `(mInt_congr_samePot D R.X R.A (⋃ j, N j)ᶜ _ _ _ _ (fun j => ?_) (fun j x hx => hS j x ?_) (fun j x _ => PositivityTheory.Xgp.vert_deg.isC2At_of_isPotential _ (isPotential_potOf R (hL' j)) x) (fun _ _ => rfl)).1` and prove the remaining obligations.

Rewrite using `[compl_compl, Set.preimage_iUnion, Set.inter_iUnion]`. Conclude with `measure_iUnion_null fun i => hN i j`. Conclude with `fun h => hx (Set.mem_iUnion.2 ⟨j, h⟩)`.
-/
theorem PositivityTheory.Xgp.t_vert_deg : ResExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ) (L L' : Fin D → HermLine ι) (T : Finset ℕ) (α : ℕ → ℝ), IsArithVar P (D + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsSmoothHerm (L' j)) → (∀ j, L j = L' j ∨ VertClose P T α (L j) (L' j)) → ∀ (Am : HermLine ι) (s : MRing ι), IsSmoothHerm Am → IsSectionOn P Am s → ptsIntegral P (pot L) (logNorm Am s) = ptsIntegral P (pot L') (logNorm Am s) := by
  intro hE K _ ι _ P D L L' T α hP hL hL' hV Am s hAm hs
  obtain ⟨J, ⟨R⟩⟩ := exists_anLogRes hE hP
  choose N hN hS using fun j => PositivityTheory.Xgp.vert_deg.exists_samePot R hP (hV j)
  rw [ptsIntegral_eq_mInt' hE resBridge R hP hL hAm hs, ptsIntegral_eq_mInt' hE resBridge R hP hL' hAm hs]
  refine (mInt_congr_samePot D R.X R.A (⋃ j, N j)ᶜ _ _ _ _ (fun j => ?_) (fun j x hx => hS j x ?_)
    (fun j x _ => PositivityTheory.Xgp.vert_deg.isC2At_of_isPotential _ (isPotential_potOf R (hL' j)) x)
    (fun _ _ => rfl)).1
  · rw [compl_compl, Set.preimage_iUnion, Set.inter_iUnion]
    exact measure_iUnion_null fun i => hN i j
  · exact fun h => hx (Set.mem_iUnion.2 ⟨j, h⟩)
