import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussTubeOfTubeGood
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContourShiftGaussianDecayStatement

noncomputable section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

/- English proof (translation)
Establish `hC : IsCompact ((fun s : ℝ => (s, c)) '' Set.Icc a b)` using `isCompact_Icc.image (Continuous.prodMk continuous_id continuous_const)`. Establish `hCΩ : (fun s : ℝ => (s, c)) '' Set.Icc a b ⊆ Ω`. Introduce and unpack `_ ⟨s, hs', rfl⟩`. Conclude with `hs s hs'`. Take `⟨M₀, hM₀⟩` from `hG.3 _ hCΩ hC`.

Use `⟨Real.exp ((|a| + |b|) * |t.1| + |c| * |t.2|) * |M₀|, by positivity, ?_⟩` and prove the remaining obligations. Introduce `l hl hlc`. Establish `hmem : l ∈ PositivityTheory.RgEis.tube ((fun s : ℝ => (s, c)) '' Set.Icc a b)` using `by show (l.1.re, l.2.re) ∈ (fun s : ℝ => (s, c)) '' Set.Icc a b`. Conclude with `⟨l.1.re, hl, Prod.ext rfl hlc.symm⟩`. Establish `hGl` using `hM₀ l hmem`.

Establish `hre : (-GlobalTheory.CompanionTheory.TubeFourier.dot l t).re = -(l.1.re * t.1 + l.2.re * t.2)`. Simplify using `[GlobalTheory.CompanionTheory.TubeFourier.dot]`. Establish `hx : |l.1.re| ≤ |a| + |b|` using `abs_le.2 ⟨by linarith [neg_abs_le a, abs_nonneg b, hl.1], by linarith [le_abs_self b, abs_nonneg a, hl.2]⟩`. Establish `hexp : ‖Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot l t)‖ ≤ Real.exp ((|a| + |b|) * |t.1| + |c| * |t.2|)`. Rewrite using `[Complex.norm_exp, hre, hlc]`.

Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Establish `e1 : -(l.1.re * t.1) ≤ (|a| + |b|) * |t.1|`. Combine the equalities or inequalities in the displayed calculation. Establish `e2 : -(c * t.2) ≤ |c| * |t.2|`. Rewrite using `[← abs_mul]`.

Conclude with `neg_le_abs _`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[norm_smul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem shiftFst_bound {Ω : Set (ℝ × ℝ)} {G : ℂ × ℂ → X} (hG : GaussTube G Ω) {a b c : ℝ}
    (hs : ∀ s ∈ Set.Icc a b, (s, c) ∈ Ω) (t : ℝ × ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ l : ℂ × ℂ, l.1.re ∈ Set.Icc a b → l.2.re = c →
      ‖Complex.exp (-dot l t) • G l‖ ≤ M * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2)) := by
  have hC : IsCompact ((fun s : ℝ => (s, c)) '' Set.Icc a b) :=
    isCompact_Icc.image (Continuous.prodMk continuous_id continuous_const)
  have hCΩ : (fun s : ℝ => (s, c)) '' Set.Icc a b ⊆ Ω := by
    rintro _ ⟨s, hs', rfl⟩
    exact hs s hs'
  obtain ⟨M₀, hM₀⟩ := hG.3 _ hCΩ hC
  refine ⟨Real.exp ((|a| + |b|) * |t.1| + |c| * |t.2|) * |M₀|, by positivity, ?_⟩
  intro l hl hlc
  have hmem : l ∈ PositivityTheory.RgEis.tube ((fun s : ℝ => (s, c)) '' Set.Icc a b) := by
    show (l.1.re, l.2.re) ∈ (fun s : ℝ => (s, c)) '' Set.Icc a b
    exact ⟨l.1.re, hl, Prod.ext rfl hlc.symm⟩
  have hGl := hM₀ l hmem
  have hre : (-GlobalTheory.CompanionTheory.TubeFourier.dot l t).re = -(l.1.re * t.1 + l.2.re * t.2) := by
    simp [GlobalTheory.CompanionTheory.TubeFourier.dot]
  have hx : |l.1.re| ≤ |a| + |b| :=
    abs_le.2 ⟨by linarith [neg_abs_le a, abs_nonneg b, hl.1], by linarith [le_abs_self b, abs_nonneg a, hl.2]⟩
  have hexp : ‖Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot l t)‖ ≤
      Real.exp ((|a| + |b|) * |t.1| + |c| * |t.2|) := by
    rw [Complex.norm_exp, hre, hlc]
    apply Real.exp_le_exp.2
    have e1 : -(l.1.re * t.1) ≤ (|a| + |b|) * |t.1| := by
      calc -(l.1.re * t.1) ≤ |l.1.re * t.1| := neg_le_abs _
        _ = |l.1.re| * |t.1| := abs_mul _ _
        _ ≤ (|a| + |b|) * |t.1| := mul_le_mul_of_nonneg_right hx (abs_nonneg _)
    have e2 : -(c * t.2) ≤ |c| * |t.2| := by
      rw [← abs_mul]
      exact neg_le_abs _
    linarith
  rw [norm_smul]
  calc ‖Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot l t)‖ * ‖G l‖
      ≤ Real.exp ((|a| + |b|) * |t.1| + |c| * |t.2|) *
          (|M₀| * Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2))) :=
        mul_le_mul hexp (hGl.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le))
          (norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp ((|a| + |b|) * |t.1| + |c| * |t.2|) * |M₀| *
          Real.exp (-(l.1.im ^ 2 + l.2.im ^ 2)) := by ring

/- English proof (translation)
Establish `h` using `(integrable_exp_neg_mul_sq one_pos).mul_prod (integrable_exp_neg_mul_sq one_pos)`. Rewrite `h` using `[← MeasureTheory.Measure.volume_eq_prod]`. Use `h.congr (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `only [neg_mul, one_mul]`.
-/
theorem integrable_exp_neg_sq_prod :
    Integrable (fun y : ℝ × ℝ => Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2)) := by
  have h := (integrable_exp_neg_mul_sq one_pos).mul_prod (integrable_exp_neg_mul_sq one_pos)
  rw [← MeasureTheory.Measure.volume_eq_prod] at h
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [neg_mul, one_mul]

/- English proof (translation)
Take `⟨M, -, hM⟩` from `GlobalTheory.CompanionTheory.TubeFourier.shiftFst_bound hG hs t`. Establish `htp : Continuous (GlobalTheory.CompanionTheory.TubeFourier.pt (s, c))`. Establish `h : GlobalTheory.CompanionTheory.TubeFourier.pt (s, c) = fun y : ℝ × ℝ => ((s : ℂ) + (y.1 : ℂ) * Complex.I, (c : ℂ) + (y.2 : ℂ) * Complex.I)`. Use function extensionality and compare the values at `y`. Simplify using `only [GlobalTheory.CompanionTheory.TubeFourier.pt, Complex.mk_eq_add_mul_I]`.

Rewrite using `[h]`. Use `fun_prop`. Establish `hmem : ∀ y, GlobalTheory.CompanionTheory.TubeFourier.pt (s, c) y ∈ PositivityTheory.RgEis.tube Ω` using `fun _ => hs s hsm`. Establish `hGc : Continuous (fun y => G (GlobalTheory.CompanionTheory.TubeFourier.pt (s, c) y))` using `hG.2.comp_continuous htp hmem`. Establish `hpair : Continuous (fun l : ℂ × ℂ => GlobalTheory.CompanionTheory.TubeFourier.dot l t)`.

Simplify using `only [GlobalTheory.CompanionTheory.TubeFourier.dot]`. Use `fun_prop`. Establish `hE : Continuous (fun y => Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot (GlobalTheory.CompanionTheory.TubeFourier.pt (s, c) y) t))` using `(hpair.comp htp).neg.cexp`. Use `MeasureTheory.Integrable.mono' (GlobalTheory.CompanionTheory.TubeFourier.integrable_exp_neg_sq_prod.const_mul M) (hE.smul hGc).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Use `(hM (GlobalTheory.CompanionTheory.TubeFourier.pt (s, c) y) hsm rfl).trans (le_of_eq ?_)` and prove the remaining obligations.

Use `show M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2)) = M * (Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2))`. Rewrite using `[← Real.exp_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem shiftFst_integrable {Ω : Set (ℝ × ℝ)} {G : ℂ × ℂ → X} (hG : GaussTube G Ω) {a b c : ℝ}
    (hs : ∀ s ∈ Set.Icc a b, (s, c) ∈ Ω) (t : ℝ × ℝ) {s : ℝ} (hsm : s ∈ Set.Icc a b) :
    Integrable (fun y : ℝ × ℝ => Complex.exp (-dot (pt (s, c) y) t) • G (pt (s, c) y)) := by
  obtain ⟨M, -, hM⟩ := GlobalTheory.CompanionTheory.TubeFourier.shiftFst_bound hG hs t
  have htp : Continuous (GlobalTheory.CompanionTheory.TubeFourier.pt (s, c)) := by
    have h : GlobalTheory.CompanionTheory.TubeFourier.pt (s, c) = fun y : ℝ × ℝ =>
        ((s : ℂ) + (y.1 : ℂ) * Complex.I, (c : ℂ) + (y.2 : ℂ) * Complex.I) := by
      funext y
      simp only [GlobalTheory.CompanionTheory.TubeFourier.pt, Complex.mk_eq_add_mul_I]
    rw [h]
    fun_prop
  have hmem : ∀ y, GlobalTheory.CompanionTheory.TubeFourier.pt (s, c) y ∈ PositivityTheory.RgEis.tube Ω := fun _ => hs s hsm
  have hGc : Continuous (fun y => G (GlobalTheory.CompanionTheory.TubeFourier.pt (s, c) y)) := hG.2.comp_continuous htp hmem
  have hpair : Continuous (fun l : ℂ × ℂ => GlobalTheory.CompanionTheory.TubeFourier.dot l t) := by
    simp only [GlobalTheory.CompanionTheory.TubeFourier.dot]
    fun_prop
  have hE : Continuous (fun y => Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot (GlobalTheory.CompanionTheory.TubeFourier.pt (s, c) y) t)) :=
    (hpair.comp htp).neg.cexp
  refine MeasureTheory.Integrable.mono'
    (GlobalTheory.CompanionTheory.TubeFourier.integrable_exp_neg_sq_prod.const_mul M)
    (hE.smul hGc).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  refine (hM (GlobalTheory.CompanionTheory.TubeFourier.pt (s, c) y) hsm rfl).trans (le_of_eq ?_)
  show M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2)) = M * (Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2))
  rw [← Real.exp_add]
  congr 2
  ring

/- English proof (translation)
Establish `h` using `shiftFst_integrable hG hs t hsm`. Unfold `phi`. Rewrite `h`, the goal using `[Measure.volume_eq_prod]`. Conclude with `integral_prod_symm _ h`.
-/
theorem phi_eq_iterated {Ω : Set (ℝ × ℝ)} {G : ℂ × ℂ → X} (hG : GaussTube G Ω) {a b c : ℝ}
    (hs : ∀ s ∈ Set.Icc a b, (s, c) ∈ Ω) (t : ℝ × ℝ) {s : ℝ} (hsm : s ∈ Set.Icc a b) :
    phi G (s, c) t = ∫ y₂ : ℝ, ∫ y₁ : ℝ,
      Complex.exp (-dot (pt (s, c) (y₁, y₂)) t) • G (pt (s, c) (y₁, y₂)) := by
  have h := shiftFst_integrable hG hs t hsm
  unfold phi
  rw [Measure.volume_eq_prod] at h ⊢
  exact integral_prod_symm _ h

end GlobalTheory.CompanionTheory.TubeFourier

/- English proof (translation)
Introduce `X _ _ _ Ω G hG a b c hab hs t`. Rewrite using `[GlobalTheory.CompanionTheory.TubeFourier.phi_eq_iterated hG hs t (Set.left_mem_Icc.2 hab), GlobalTheory.CompanionTheory.TubeFourier.phi_eq_iterated hG hs t (Set.right_mem_Icc.2 hab)]`. Take `⟨M, hM0, hM⟩` from `GlobalTheory.CompanionTheory.TubeFourier.shiftFst_bound hG hs t`. Use `integral_congr_ae (ae_of_all _ fun y₂ => ?_)` and prove the remaining obligations. Establish `hline : DifferentiableOn ℂ (fun z : ℂ => G (z, ⟨c, y₂⟩)) {z : ℂ | z.re ∈ Set.Icc a b}`.

Establish `h1` using `hG.1 ((0 : ℂ), (⟨c, y₂⟩ : ℂ)) ((1 : ℂ), (0 : ℂ))`. Establish `heq : ∀ τ : ℂ, ((0 : ℂ), (⟨c, y₂⟩ : ℂ)) + τ • ((1 : ℂ), (0 : ℂ)) = (τ, ⟨c, y₂⟩)` using `fun τ => Prod.ext (by simp) (by simp)`. Simplify using `only [heq] at h1`. Use `h1.mono fun z hz => ?_` and prove the remaining obligations. Conclude with `hs z.re hz`.

Establish `hpair : Differentiable ℂ (fun z : ℂ => Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot (z, ⟨c, y₂⟩) t))`. Simplify using `only [GlobalTheory.CompanionTheory.TubeFourier.dot]`. Use `fun_prop`. Establish `hdiff : DifferentiableOn ℂ (fun z : ℂ => Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot (z, ⟨c, y₂⟩) t) • G (z, ⟨c, y₂⟩)) {z : ℂ | z.re ∈ Set.Icc a b}` using `hpair.differentiableOn.smul hline`. Establish `hbound : ∀ z : ℂ, z.re ∈ Set.Icc a b → ‖Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot (z, ⟨c, y₂⟩) t) • G (z, ⟨c, y₂⟩)‖ ≤ M * Real.exp (-z.im ^ 2)`.

Introduce `z hz`. Use `(hM (z, ⟨c, y₂⟩) hz rfl).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hM0)` and prove the remaining obligations. Use `show -(z.im ^ 2 + y₂ ^ 2) ≤ -z.im ^ 2`. Combine the linear relations using `[sq_nonneg y₂]`. Conclude with `GlobalTheory.T.contour_shift_gaussian_decay X (fun z : ℂ => Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot (z, ⟨c, y₂⟩) t) • G (z, ⟨c, y₂⟩)) a b M hab hdiff hbound`.
-/
theorem GlobalTheory.CompanionTheory.TubeFourier.phi_shift_fst :
    ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (Ω : Set (ℝ × ℝ)) (G : ℂ × ℂ → X),
      GaussTube G Ω → ∀ a b c : ℝ, a ≤ b → (∀ s ∈ Set.Icc a b, (s, c) ∈ Ω) →
        ∀ t : ℝ × ℝ, phi G (a, c) t = phi G (b, c) t := by
  intro X _ _ _ Ω G hG a b c hab hs t
  rw [GlobalTheory.CompanionTheory.TubeFourier.phi_eq_iterated hG hs t (Set.left_mem_Icc.2 hab),
    GlobalTheory.CompanionTheory.TubeFourier.phi_eq_iterated hG hs t (Set.right_mem_Icc.2 hab)]
  obtain ⟨M, hM0, hM⟩ := GlobalTheory.CompanionTheory.TubeFourier.shiftFst_bound hG hs t
  refine integral_congr_ae (ae_of_all _ fun y₂ => ?_)
  have hline : DifferentiableOn ℂ (fun z : ℂ => G (z, ⟨c, y₂⟩)) {z : ℂ | z.re ∈ Set.Icc a b} := by
    have h1 := hG.1 ((0 : ℂ), (⟨c, y₂⟩ : ℂ)) ((1 : ℂ), (0 : ℂ))
    have heq : ∀ τ : ℂ, ((0 : ℂ), (⟨c, y₂⟩ : ℂ)) + τ • ((1 : ℂ), (0 : ℂ)) = (τ, ⟨c, y₂⟩) :=
      fun τ => Prod.ext (by simp) (by simp)
    simp only [heq] at h1
    refine h1.mono fun z hz => ?_
    exact hs z.re hz
  have hpair : Differentiable ℂ (fun z : ℂ => Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot (z, ⟨c, y₂⟩) t)) := by
    simp only [GlobalTheory.CompanionTheory.TubeFourier.dot]
    fun_prop
  have hdiff : DifferentiableOn ℂ
      (fun z : ℂ => Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot (z, ⟨c, y₂⟩) t) • G (z, ⟨c, y₂⟩))
      {z : ℂ | z.re ∈ Set.Icc a b} :=
    hpair.differentiableOn.smul hline
  have hbound : ∀ z : ℂ, z.re ∈ Set.Icc a b →
      ‖Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot (z, ⟨c, y₂⟩) t) • G (z, ⟨c, y₂⟩)‖ ≤
        M * Real.exp (-z.im ^ 2) := by
    intro z hz
    refine (hM (z, ⟨c, y₂⟩) hz rfl).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hM0)
    show -(z.im ^ 2 + y₂ ^ 2) ≤ -z.im ^ 2
    linarith [sq_nonneg y₂]
  exact GlobalTheory.T.contour_shift_gaussian_decay X
    (fun z : ℂ => Complex.exp (-GlobalTheory.CompanionTheory.TubeFourier.dot (z, ⟨c, y₂⟩) t) • G (z, ⟨c, y₂⟩))
    a b M hab hdiff hbound
