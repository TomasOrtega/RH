import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.SmoothPf
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.IntegralRestrictC
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.KerInt

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal ContDiff

namespace PositivityTheory.Rg.Sw.HSt.Conv

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.GRH PositivityTheory.Rg.Sw.HSt.MI

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section

variable {n m : ℕ} {e : ℤ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0} {f : G → ℂ}
  {U : Set ℂ} {d : Polynomial ℂ} {Ê : ℂ → G → ℂ} {t : ℝ}

/- English proof (translation)
Introduce and unpack `⟨x₀, z₀⟩ ⟨-, hz₀⟩`. Take `⟨ε, εpos, hε⟩` from `Metric.isOpen_iff.1 hU z₀ hz₀`. Establish `rpos : 0 < ε / 2` using `by positivity`. Establish `hsub : Metric.closedBall z₀ (ε / 2) ⊆ U` using `(Metric.closedBall_subset_ball (by linarith)).trans hε`. Use `set S : Set (X × ℂ) := (univ : Set X) ×ˢ Metric.ball z₀ (ε / 2) with hSdef`.

Use `set K : X × ℂ → ℂ := fun p => (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ w in C(z₀, ε / 2), ((w - p.2) ^ 2)⁻¹ • Φ p.1 w with hKdef`. Establish `heq : ∀ p ∈ S, deriv (Φ p.1) p.2 = K p` using `fun p hp => (Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable hU hsub (hd p.1) hp.2).symm`. Establish `hS : IsOpen S` using `isOpen_univ.prod Metric.isOpen_ball`. Establish `hmem : (x₀, z₀) ∈ S` using `⟨trivial, Metric.mem_ball_self rpos⟩`. Establish `hK : ContinuousOn K S`.

Rewrite using `[continuousOn_iff_continuous_restrict]`. Establish `hsph : ∀ θ : ℝ, circleMap z₀ (ε / 2) θ ∈ U` using `fun θ => hsub (Metric.sphere_subset_closedBall (circleMap_mem_sphere z₀ rpos.le θ))`. Establish `h3 : Continuous (fun q : S × ℝ => Φ q.1.1.1 (circleMap z₀ (ε / 2) q.2))`. Use `hc.comp_continuous (f := fun q : S × ℝ => (q.1.1.1, circleMap z₀ (ε / 2) q.2)) (by fun_prop) (fun q => ⟨trivial, hsph q.2⟩)` as an intermediate fact. Conclude with `this`.

Establish `h2 : Continuous (fun q : S × ℝ => ((circleMap z₀ (ε / 2) q.2 - q.1.1.2) ^ 2)⁻¹)`. Use `Continuous.inv₀ (by fun_prop) ?_` and prove the remaining obligations. Introduce `q h`. Establish `hq : q.1.1.2 ∈ Metric.ball z₀ (ε / 2)` using `q.1.2.2`. Establish `h0 : circleMap z₀ (ε / 2) q.2 = q.1.1.2` using `sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h)`.

Establish `hs` using `circleMap_mem_sphere z₀ rpos.le q.2`. Rewrite `hs` using `[h0]`. Rewrite `hs` using `[Metric.mem_sphere]`. Rewrite `hq` using `[Metric.mem_ball]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h1 : Continuous (fun q : S × ℝ => deriv (circleMap z₀ (ε / 2)) q.2)`. Simplify using `only [deriv_circleMap]`. Use `fun_prop`. Establish `hI` using `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := MeasureTheory.volume) (f := fun (q : S) (θ : ℝ) => deriv (circleMap z₀ (ε / 2)) θ • ((circleMap z₀ (ε / 2) θ - q.1.2) ^ 2)⁻¹ • Φ q.1.1 (circleMap z₀ (ε / 2) θ)) (h1.smul (h2.smul h3)) 0 (2 * Real.pi)`. Establish `hI2` using `(continuous_const (y := (2 * Real.pi * Complex.I : ℂ)⁻¹)).mul hI`.

Use `hI2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `q`. Simplify using `only [Set.restrict_apply, hKdef, circleIntegral, smul_eq_mul, Pi.mul_apply]`. Establish `hat : ContinuousAt (fun p : X × ℂ => deriv (Φ p.1) p.2) (x₀, z₀)`. Use `(hK.continuousAt (hS.mem_nhds hmem)).congr ?_` and prove the remaining obligations.

Use `filter_upwards [hS.mem_nhds hmem] with p hp using (heq p hp).symm`. Conclude with `hat.continuousWithinAt`.
-/
private theorem taylor_cont_lemma {X : Type} [TopologicalSpace X] {U : Set ℂ} (hU : IsOpen U)
    (Φ : X → ℂ → ℂ) (hc : ContinuousOn (fun p : X × ℂ => Φ p.1 p.2) (univ ×ˢ U))
    (hd : ∀ x, DifferentiableOn ℂ (Φ x) U) :
    ContinuousOn (fun p : X × ℂ => deriv (Φ p.1) p.2) (univ ×ˢ U) := by
  rintro ⟨x₀, z₀⟩ ⟨-, hz₀⟩
  obtain ⟨ε, εpos, hε⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  have rpos : 0 < ε / 2 := by positivity
  have hsub : Metric.closedBall z₀ (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hε
  set S : Set (X × ℂ) := (univ : Set X) ×ˢ Metric.ball z₀ (ε / 2) with hSdef
  set K : X × ℂ → ℂ := fun p =>
    (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ w in C(z₀, ε / 2), ((w - p.2) ^ 2)⁻¹ • Φ p.1 w with hKdef
  have heq : ∀ p ∈ S, deriv (Φ p.1) p.2 = K p := fun p hp =>
    (Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable hU hsub (hd p.1)
      hp.2).symm
  have hS : IsOpen S := isOpen_univ.prod Metric.isOpen_ball
  have hmem : (x₀, z₀) ∈ S := ⟨trivial, Metric.mem_ball_self rpos⟩
  have hK : ContinuousOn K S := by
    rw [continuousOn_iff_continuous_restrict]
    have hsph : ∀ θ : ℝ, circleMap z₀ (ε / 2) θ ∈ U := fun θ =>
      hsub (Metric.sphere_subset_closedBall (circleMap_mem_sphere z₀ rpos.le θ))
    have h3 : Continuous (fun q : S × ℝ => Φ q.1.1.1 (circleMap z₀ (ε / 2) q.2)) := by
      have := hc.comp_continuous (f := fun q : S × ℝ => (q.1.1.1, circleMap z₀ (ε / 2) q.2))
        (by fun_prop) (fun q => ⟨trivial, hsph q.2⟩)
      exact this
    have h2 : Continuous (fun q : S × ℝ => ((circleMap z₀ (ε / 2) q.2 - q.1.1.2) ^ 2)⁻¹) := by
      refine Continuous.inv₀ (by fun_prop) ?_
      intro q h
      have hq : q.1.1.2 ∈ Metric.ball z₀ (ε / 2) := q.1.2.2
      have h0 : circleMap z₀ (ε / 2) q.2 = q.1.1.2 := sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h)
      have hs := circleMap_mem_sphere z₀ rpos.le q.2
      rw [h0] at hs
      rw [Metric.mem_sphere] at hs
      rw [Metric.mem_ball] at hq
      linarith
    have h1 : Continuous (fun q : S × ℝ => deriv (circleMap z₀ (ε / 2)) q.2) := by
      simp only [deriv_circleMap]
      fun_prop
    have hI := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := MeasureTheory.volume)
      (f := fun (q : S) (θ : ℝ) => deriv (circleMap z₀ (ε / 2)) θ •
        ((circleMap z₀ (ε / 2) θ - q.1.2) ^ 2)⁻¹ • Φ q.1.1 (circleMap z₀ (ε / 2) θ))
      (h1.smul (h2.smul h3)) 0 (2 * Real.pi)
    have hI2 := (continuous_const (y := (2 * Real.pi * Complex.I : ℂ)⁻¹)).mul hI
    convert hI2 using 1
    funext q
    simp only [Set.restrict_apply, hKdef, circleIntegral, smul_eq_mul, Pi.mul_apply]
  have hat : ContinuousAt (fun p : X × ℂ => deriv (Φ p.1) p.2) (x₀, z₀) := by
    refine (hK.continuousAt (hS.mem_nhds hmem)).congr ?_
    filter_upwards [hS.mem_nhds hmem] with p hp using (heq p hp).symm
  exact hat.continuousWithinAt

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] in
/- English proof (translation)
Introduce `r`. Proceed by induction on `r with`. Consider the case `zero`. Simplify using `only [iteratedDeriv_zero]`. Use `⟨?_, fun x => hD.hol x⟩` and prove the remaining obligations.

Conclude with `hD.cont.comp (continuous_swap.continuousOn) (fun y hy => ⟨hy.2, trivial⟩)`. Consider the case `succ k ih`. Simplify using `only [iteratedDeriv_succ]`. Conclude with `⟨taylor_cont_lemma hD.hU _ ih.1 ih.2, fun x => (ih.2 x).deriv hD.hU⟩`.
-/
theorem taylor_cont (hD : HD m n e G Pp Γ ι s₀ Ht f U d Ê t) : ∀ r : ℕ,
    ContinuousOn (fun y : G × ℂ => iteratedDeriv r (Ê · y.1) y.2) (univ ×ˢ U) ∧
      ∀ x, DifferentiableOn ℂ (iteratedDeriv r (Ê · x)) U := by
  intro r
  induction r with
  | zero =>
    simp only [iteratedDeriv_zero]
    refine ⟨?_, fun x => hD.hol x⟩
    exact hD.cont.comp (continuous_swap.continuousOn) (fun y hy => ⟨hy.2, trivial⟩)
  | succ k ih =>
    simp only [iteratedDeriv_succ]
    exact ⟨taylor_cont_lemma hD.hU _ ih.1 ih.2, fun x => (ih.2 x).deriv hD.hU⟩

end

/- English proof (translation)
Establish `hx' : xᴴ * JJ n * x = JJ n` using `hx`. Establish `hJ : JJ n * JJ n = -1`. Simplify using `[JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]`. Establish `hl : (-(JJ n * xᴴ * JJ n)) * x = 1`. Establish `e : JJ n * xᴴ * JJ n * x = JJ n * (xᴴ * JJ n * x)` using `by simp only [Matrix.mul_assoc]`.

Rewrite using `[neg_mul, e, hx', hJ, neg_neg]`. Conclude with `Matrix.det_ne_zero_of_left_inverse hl`.
-/
theorem gset_inv {n : ℕ} {x : M2 n} (hx : InG x) : x ∈ Inv n := by
  have hx' : xᴴ * JJ n * x = JJ n := hx
  have hJ : JJ n * JJ n = -1 := by
    simp [JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  have hl : (-(JJ n * xᴴ * JJ n)) * x = 1 := by
    have e : JJ n * xᴴ * JJ n * x = JJ n * (xᴴ * JJ n * x) := by simp only [Matrix.mul_assoc]
    rw [neg_mul, e, hx', hJ, neg_neg]
  exact Matrix.det_ne_zero_of_left_inverse hl

/- English proof (translation)
Simplify using `[mR, Matrix.coe_units_inv]`.
-/
theorem mR_inv {n : ℕ} (y : GR n) : (mR y)⁻¹ = mR y⁻¹ := by
  simp [mR, Matrix.coe_units_inv]

/- English proof (translation)
Introduce `m n e _ _ G _ _ _ _ _ _ Pp Γ ι s₀ Ht f U d Ê t hD g`. Take `⟨ν, hν⟩ : ∃ ν : Measure (GR n), ν.IsHaarMeasure` from `⟨Measure.haar, inferInstance⟩`. Take `⟨μK, hμK⟩ : ∃ μ : Measure (KR n), μ.IsHaarMeasure` from `⟨Measure.haar, inferInstance⟩`. Take `⟨β, hβs, hβc, hβ0⟩` from `exists_bump m e ν μK`. Establish `hmR : Continuous (fun u : GR n => mR u)` using `Units.continuous_val.comp continuous_subtype_val`.

Establish `hcont : ∀ z ∈ U, Continuous (fun u : GR n => Ê z (g * ι u))`. Introduce `z hz`. Use `hD.cont.comp_continuous (f := fun u : GR n => (z, g * ι u)) (continuous_const.prodMk (continuous_const.mul hD.ιc)) (fun u => ⟨hz, trivial⟩)` as an intermediate fact. Conclude with `this`. Establish `hcont' : ∀ r : ℕ, Continuous (fun u : GR n => iteratedDeriv r (Ê · (g * ι u)) s₀)`.

Introduce `r`. Use `(taylor_cont hD r).1.comp_continuous (f := fun u : GR n => (g * ι u, s₀)) ((continuous_const.mul hD.ιc).prodMk continuous_const) (fun u => ⟨trivial, hD.hs⟩)` as an intermediate fact. Conclude with `this`. Establish `hmc : ∀ (a : ℂ → ℂ) (c z : ℂ) (r : ℕ), iteratedDeriv r (fun w => a w * c) z = iteratedDeriv r a z * c`. Introduce `a c z r`.

Establish `hfun : (fun w => a w * c) = (fun w => c * a w)` using `funext fun w => mul_comm _ _`. Rewrite using `[hfun, iteratedDeriv_const_mul_field, mul_comm]`. Establish `hloc : ∀ (f₁ f₂ : ℂ → ℂ) (r : ℕ), (∀ z ∈ U, f₁ z = f₂ z) → iteratedDeriv r f₁ s₀ = iteratedDeriv r f₂ s₀`. Introduce `f₁ f₂ r hf`. Establish `hev : f₁ =ᶠ[𝓝[univ] s₀] f₂`.

Rewrite using `[nhdsWithin_univ]`. Conclude with `Filter.eventually_of_mem (hD.hU.mem_nhds hD.hs) hf`. Use `Filter.EventuallyEq.iteratedDerivWithin_eq (n := r) hev (hf s₀ hD.hs)` as an intermediate fact. Simplify `this` using `only [iteratedDerivWithin_univ]`. Establish `key : ∀ x ∈ MI.Inv n, DifferentiableOn ℂ (fun z => Psi m e ν μK β (fun u => Ê z (g * ι u)) x) U ∧ ∀ r : ℕ, iteratedDeriv r (fun z => Psi m e ν μK β (fun u => Ê z (g * ι u)) x) s₀ = Psi m e ν μK β (fun u => iteratedDeriv r (Ê · (g * ι u)) s₀) x`.

Introduce `x hx`. Take `⟨W, hW, C, hC, hCz⟩` from `kk_supp m e μK hβc x hx`. Establish `hk0 : Continuous (fun u : GR n => x⁻¹ * mR u)` using `continuous_const.mul hmR`. Establish `hk : Continuous (fun u : GR n => kk m e μK β (x, mR u))` using `(tw_contDiff m e μK hβs).continuous.comp hk0`. Establish `hI` using `holInt ν hC hD.hU (fun u z => Ê z (g * ι u) • kk m e μK β (x, mR u)) (fun u hu z => by simp [hCz x (mem_of_mem_nhds hW) u hu]) (by`.

Establish `h1 : ContinuousOn (fun p : GR n × ℂ => Ê p.2 (g * ι p.1)) (C ×ˢ U)` using `hD.cont.comp ((continuous_snd.prodMk (continuous_const.mul (hD.ιc.comp continuous_fst))).continuousOn) (fun p hp => ⟨hp.2, trivial⟩)`. Conclude with `h1.smul (hk.comp continuous_fst).continuousOn)`. Use the proof step `(fun u _ => (hD.hol (g * ι u)).smul_const _)`. Use `⟨hI.1, fun r => ?_⟩` and prove the remaining obligations. Simplify using `only [Psi]`.

Rewrite using `[hI.2 s₀ hD.hs r]`. Simplify using `only [smul_eq_mul]`. Use `congr 1`. Use function extensionality and compare the values at `u`. Conclude with `hmc _ _ _ _`.

Use `⟨fun z x => Psi m e ν μK β (fun u => Ê z (g * ι u)) x, MI.Inv n, fun z => cw m e ν μK β (z - s₀), MI.isOpen_Inv, fun x hx => gset_inv hx, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `((cw_differentiable ν μK hβs.continuous hβc).comp (differentiable_id.sub_const s₀)).differentiableOn`. Simplify using `using hβ0`. Introduce `z hz y`. Simplify using `only [Psi, kk, smul_eq_mul]`.

Rewrite using `[← integral_mul_left_eq_self _ y]`. Use `conv_U hD ν μK hβs.continuous hβc z hz g y` as an intermediate fact. Rewrite using `[← this]`. Use `congr 1`. Use function extensionality and compare the values at `u`.

Rewrite using `[mR_inv, ← mR_mul, ← mul_assoc, inv_mul_cancel, one_mul]`. Introduce `z hz`. Conclude with `psi_contDiffOn m e ν μK hβs hβc _ (hcont z hz)`. Introduce `r`. Conclude with `(psi_contDiffOn m e ν μK hβs hβc _ (hcont' r)).congr (fun x hx => (key x hx).2 r)`.

Introduce `x hx`. Conclude with `(key x hx).1`. Introduce `Q y`. Establish `hx₀ : mR y ∈ MI.Inv n` using `gset_inv y.2`. Take `⟨C, hC, hCz⟩` from `Lk_zero m e μK hβc (lowQ Q) hx₀`.

Establish `hL` using `Lk_cont m e μK hβs (lowQ Q) hx₀`. Establish `hI` using `holInt ν hC hD.hU (fun u z => Ê z (g * ι u) * Lk m e μK β (lowQ Q) (mR y) u) (fun u hu z => by simp [hCz u hu]) (by`. Establish `h1 : ContinuousOn (fun p : GR n × ℂ => Ê p.2 (g * ι p.1)) (C ×ˢ U)` using `hD.cont.comp ((continuous_snd.prodMk (continuous_const.mul (hD.ιc.comp continuous_fst))).continuousOn) (fun p hp => ⟨hp.2, trivial⟩)`. Conclude with `h1.mul (hL.comp continuous_fst).continuousOn)`. Use the proof step `(fun u _ => (hD.hol (g * ι u)).mul_const _)`.

Establish `hrc : ∀ z ∈ U, rC (lowQ Q) (Psi m e ν μK β (fun u => Ê z (g * ι u))) (mR y) = ∫ u, Ê z (g * ι u) * Lk m e μK β (lowQ Q) (mR y) u ∂ν`. Introduce `z hz`. Conclude with `rC_psi m e ν μK hβs hβc (fun u => Ê z (g * ι u)) (hcont z hz) (lowQ Q) hx₀`. Use `⟨hI.1.congr hrc, fun r => ?_⟩` and prove the remaining obligations. Rewrite using `[hloc _ _ r hrc, hI.2 s₀ hD.hs r]`.

Rewrite using `[MI.rC_congr MI.isOpen_Inv hx₀ (fun x hx => (key x hx).2 r) (lowQ Q), rC_psi m e ν μK hβs hβc _ (hcont' r) (lowQ Q) hx₀]`. Use `congr 1`. Use function extensionality and compare the values at `u`. Conclude with `hmc _ _ _ _`.
-/
theorem smoothX : SmoothX := by
  intro m n e _ _ G _ _ _ _ _ _ Pp Γ ι s₀ Ht f U d Ê t hD g
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (GR n), ν.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  obtain ⟨μK, hμK⟩ : ∃ μ : Measure (KR n), μ.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  obtain ⟨β, hβs, hβc, hβ0⟩ := exists_bump m e ν μK
  have hmR : Continuous (fun u : GR n => mR u) := Units.continuous_val.comp continuous_subtype_val
  have hcont : ∀ z ∈ U, Continuous (fun u : GR n => Ê z (g * ι u)) := by
    intro z hz
    have := hD.cont.comp_continuous (f := fun u : GR n => (z, g * ι u))
      (continuous_const.prodMk (continuous_const.mul hD.ιc)) (fun u => ⟨hz, trivial⟩)
    exact this
  have hcont' : ∀ r : ℕ, Continuous (fun u : GR n => iteratedDeriv r (Ê · (g * ι u)) s₀) := by
    intro r
    have := (taylor_cont hD r).1.comp_continuous (f := fun u : GR n => (g * ι u, s₀))
      ((continuous_const.mul hD.ιc).prodMk continuous_const) (fun u => ⟨trivial, hD.hs⟩)
    exact this
  have hmc : ∀ (a : ℂ → ℂ) (c z : ℂ) (r : ℕ),
      iteratedDeriv r (fun w => a w * c) z = iteratedDeriv r a z * c := by
    intro a c z r
    have hfun : (fun w => a w * c) = (fun w => c * a w) := funext fun w => mul_comm _ _
    rw [hfun, iteratedDeriv_const_mul_field, mul_comm]
  have hloc : ∀ (f₁ f₂ : ℂ → ℂ) (r : ℕ), (∀ z ∈ U, f₁ z = f₂ z) →
      iteratedDeriv r f₁ s₀ = iteratedDeriv r f₂ s₀ := by
    intro f₁ f₂ r hf
    have hev : f₁ =ᶠ[𝓝[univ] s₀] f₂ := by
      rw [nhdsWithin_univ]
      exact Filter.eventually_of_mem (hD.hU.mem_nhds hD.hs) hf
    have := Filter.EventuallyEq.iteratedDerivWithin_eq (n := r) hev (hf s₀ hD.hs)
    simpa only [iteratedDerivWithin_univ] using this
  have key : ∀ x ∈ MI.Inv n,
      DifferentiableOn ℂ (fun z => Psi m e ν μK β (fun u => Ê z (g * ι u)) x) U ∧
      ∀ r : ℕ, iteratedDeriv r (fun z => Psi m e ν μK β (fun u => Ê z (g * ι u)) x) s₀ =
        Psi m e ν μK β (fun u => iteratedDeriv r (Ê · (g * ι u)) s₀) x := by
    intro x hx
    obtain ⟨W, hW, C, hC, hCz⟩ := kk_supp m e μK hβc x hx
    have hk0 : Continuous (fun u : GR n => x⁻¹ * mR u) := continuous_const.mul hmR
    have hk : Continuous (fun u : GR n => kk m e μK β (x, mR u)) :=
      (tw_contDiff m e μK hβs).continuous.comp hk0
    have hI := holInt ν hC hD.hU (fun u z => Ê z (g * ι u) • kk m e μK β (x, mR u))
      (fun u hu z => by simp [hCz x (mem_of_mem_nhds hW) u hu])
      (by
        have h1 : ContinuousOn (fun p : GR n × ℂ => Ê p.2 (g * ι p.1)) (C ×ˢ U) :=
          hD.cont.comp ((continuous_snd.prodMk (continuous_const.mul (hD.ιc.comp continuous_fst))).continuousOn)
            (fun p hp => ⟨hp.2, trivial⟩)
        exact h1.smul (hk.comp continuous_fst).continuousOn)
      (fun u _ => (hD.hol (g * ι u)).smul_const _)
    refine ⟨hI.1, fun r => ?_⟩
    simp only [Psi]
    rw [hI.2 s₀ hD.hs r]
    simp only [smul_eq_mul]
    congr 1
    funext u
    exact hmc _ _ _ _
  refine ⟨fun z x => Psi m e ν μK β (fun u => Ê z (g * ι u)) x, MI.Inv n,
    fun z => cw m e ν μK β (z - s₀), MI.isOpen_Inv, fun x hx => gset_inv hx, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((cw_differentiable ν μK hβs.continuous hβc).comp (differentiable_id.sub_const s₀)).differentiableOn
  · simpa using hβ0
  · intro z hz y
    simp only [Psi, kk, smul_eq_mul]
    rw [← integral_mul_left_eq_self _ y]
    have := conv_U hD ν μK hβs.continuous hβc z hz g y
    rw [← this]
    congr 1
    funext u
    rw [mR_inv, ← mR_mul, ← mul_assoc, inv_mul_cancel, one_mul]
  · intro z hz
    exact psi_contDiffOn m e ν μK hβs hβc _ (hcont z hz)
  · intro r
    exact (psi_contDiffOn m e ν μK hβs hβc _ (hcont' r)).congr (fun x hx => (key x hx).2 r)
  · intro x hx
    exact (key x hx).1
  · intro Q y
    have hx₀ : mR y ∈ MI.Inv n := gset_inv y.2
    obtain ⟨C, hC, hCz⟩ := Lk_zero m e μK hβc (lowQ Q) hx₀
    have hL := Lk_cont m e μK hβs (lowQ Q) hx₀
    have hI := holInt ν hC hD.hU (fun u z => Ê z (g * ι u) * Lk m e μK β (lowQ Q) (mR y) u)
      (fun u hu z => by simp [hCz u hu])
      (by
        have h1 : ContinuousOn (fun p : GR n × ℂ => Ê p.2 (g * ι p.1)) (C ×ˢ U) :=
          hD.cont.comp ((continuous_snd.prodMk (continuous_const.mul (hD.ιc.comp continuous_fst))).continuousOn)
            (fun p hp => ⟨hp.2, trivial⟩)
        exact h1.mul (hL.comp continuous_fst).continuousOn)
      (fun u _ => (hD.hol (g * ι u)).mul_const _)
    have hrc : ∀ z ∈ U, rC (lowQ Q) (Psi m e ν μK β (fun u => Ê z (g * ι u))) (mR y) =
        ∫ u, Ê z (g * ι u) * Lk m e μK β (lowQ Q) (mR y) u ∂ν := by
      intro z hz
      exact rC_psi m e ν μK hβs hβc (fun u => Ê z (g * ι u)) (hcont z hz) (lowQ Q) hx₀
    refine ⟨hI.1.congr hrc, fun r => ?_⟩
    rw [hloc _ _ r hrc, hI.2 s₀ hD.hs r]
    rw [MI.rC_congr MI.isOpen_Inv hx₀ (fun x hx => (key x hx).2 r) (lowQ Q),
      rC_psi m e ν μK hβs hβc _ (hcont' r) (lowQ Q) hx₀]
    congr 1
    funext u
    exact hmc _ _ _ _

end PositivityTheory.Rg.Sw.HSt.Conv
