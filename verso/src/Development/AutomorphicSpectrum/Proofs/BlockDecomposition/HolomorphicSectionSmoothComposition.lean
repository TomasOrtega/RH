import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapPrBPtMP
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.CxSmooth

/- English proof (translation)
Take `⟨r, hr, hrU⟩` from `Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hc)`. Establish `hd : ∀ ζ ∈ Metric.closedBall c r, DifferentiableAt ℂ h ζ` using `fun ζ hζ => hh.differentiableAt (hU.mem_nhds (hrU hζ))`. Establish `hA : AnalyticAt ℂ (fun w => ((2 * (Real.pi : ℂ) * Complex.I) ^ n)⁻¹ * ReciprocityTheory.AnForm.Osgood.fctlCLM c hr h hd (ReciprocityTheory.AnForm.Osgood.kern c r w)) c` using `analyticAt_const.mul (((ReciprocityTheory.AnForm.Osgood.fctlCLM c hr h hd).analyticAt _).comp (ReciprocityTheory.AnForm.Osgood.kern_analyticAt c hr))`. Establish `h2 : (2 * (Real.pi : ℂ) * Complex.I) ^ n ≠ 0` using `pow_ne_zero _ (mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)) Complex.I_ne_zero)`. Use `hA.congr ?_` and prove the remaining obligations.

Use `filter_upwards [Metric.ball_mem_nhds c hr] with w hw`. Rewrite using `[ReciprocityTheory.AnForm.Osgood.fctlCLM_kern hr hd hw]`. Conclude with `inv_mul_cancel_left₀ h2 (h w)`.
-/
private theorem analyticAt_of_differentiableOn_open {n : ℕ} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    {h : (Fin n → ℂ) → ℂ} (hh : DifferentiableOn ℂ h U) {c : Fin n → ℂ} (hc : c ∈ U) :
    AnalyticAt ℂ h c := by
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hc)
  have hd : ∀ ζ ∈ Metric.closedBall c r, DifferentiableAt ℂ h ζ :=
    fun ζ hζ => hh.differentiableAt (hU.mem_nhds (hrU hζ))
  have hA : AnalyticAt ℂ (fun w => ((2 * (Real.pi : ℂ) * Complex.I) ^ n)⁻¹ *
      ReciprocityTheory.AnForm.Osgood.fctlCLM c hr h hd (ReciprocityTheory.AnForm.Osgood.kern c r w)) c :=
    analyticAt_const.mul
      (((ReciprocityTheory.AnForm.Osgood.fctlCLM c hr h hd).analyticAt _).comp
        (ReciprocityTheory.AnForm.Osgood.kern_analyticAt c hr))
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) ^ n ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)) Complex.I_ne_zero)
  refine hA.congr ?_
  filter_upwards [Metric.ball_mem_nhds c hr] with w hw
  rw [ReciprocityTheory.AnForm.Osgood.fctlCLM_kern hr hd hw]
  exact inv_mul_cancel_left₀ h2 (h w)

/- English proof (translation)
Set `e` to `Fintype.equivFin ι`. Set `φ : (Fin (Fintype.card ι) → ℂ) →L[ℂ] (ι → ℂ)` to `LinearMap.toContinuousLinearMap (LinearMap.funLeft ℂ ℂ e)`. Set `ψ : (ι → ℂ) →L[ℂ] (Fin (Fintype.card ι) → ℂ)` to `LinearMap.toContinuousLinearMap (LinearMap.funLeft ℂ ℂ e.symm)`. Establish `hφψ : ∀ w, φ (ψ w) = w` using `fun w => funext fun i => by simp [φ, ψ]`. Establish `hmem : ψ z ∈ φ ⁻¹' U`.

Rewrite using `[Set.mem_preimage, hφψ]`. Conclude with `hz`. Establish `hA` using `analyticAt_of_differentiableOn_open (hU.preimage φ.continuous) (hf.comp φ.differentiableOn (Set.mapsTo_preimage φ U)) hmem`. Establish `hB` using `hA.comp (ψ.analyticAt z)`. Establish `heq : (f ∘ ⇑φ) ∘ ⇑ψ = f` using `funext fun w => by simp only [Function.comp_apply, hφψ]`.

Rewrite `hB` using `[heq]`. Then use the resulting hypothesis.
-/
theorem analyticAt_of_differentiableOn {ι : Type} [Fintype ι] {U : Set (ι → ℂ)} (hU : IsOpen U)
    {f : (ι → ℂ) → ℂ} (hf : DifferentiableOn ℂ f U) {z : ι → ℂ} (hz : z ∈ U) :
    AnalyticAt ℂ f z := by
  classical
  let e := Fintype.equivFin ι
  let φ : (Fin (Fintype.card ι) → ℂ) →L[ℂ] (ι → ℂ) :=
    LinearMap.toContinuousLinearMap (LinearMap.funLeft ℂ ℂ e)
  let ψ : (ι → ℂ) →L[ℂ] (Fin (Fintype.card ι) → ℂ) :=
    LinearMap.toContinuousLinearMap (LinearMap.funLeft ℂ ℂ e.symm)
  have hφψ : ∀ w, φ (ψ w) = w := fun w => funext fun i => by simp [φ, ψ]
  have hmem : ψ z ∈ φ ⁻¹' U := by
    rw [Set.mem_preimage, hφψ]
    exact hz
  have hA := analyticAt_of_differentiableOn_open (hU.preimage φ.continuous)
    (hf.comp φ.differentiableOn (Set.mapsTo_preimage φ U)) hmem
  have hB := hA.comp (ψ.analyticAt z)
  have heq : (f ∘ ⇑φ) ∘ ⇑ψ = f := funext fun w => by simp only [Function.comp_apply, hφψ]
  rwa [heq] at hB

/- English proof (translation)
Introduce `k _ Y p σ ι _ T s f z₀ hT hs hd hz h`. Take `⟨W, ι', _, g, F, O, hyW, hO, hmem, hF, hev⟩` from `h`. Establish `hN : IsOpen (T ∩ s ⁻¹' ptsIn p σ W)` using `hs.isOpen_inter_preimage hT (isOpen_ptsIn W)`. Establish `hzN : z₀ ∈ T ∩ s ⁻¹' ptsIn p σ W` using `⟨hz, hyW⟩`. Establish `hG : AnalyticAt ℂ (fun z a => ev p σ W (g a) (s z)) z₀` using `analyticAt_pi_iff.2 fun a => analyticAt_of_differentiableOn hN (hd W (g a)) hzN`.

Establish `hcont : ContinuousAt s z₀` using `hs.continuousAt (hT.mem_nhds hz)`. Establish `h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F ∘ fun z a => ev p σ W (g a) (s z)) z₀` using `(hF.contDiffAt (hO.mem_nhds hmem)).comp z₀ (hG.contDiffAt.restrict_scalars ℝ)`. Conclude with `h1.congr_of_eventuallyEq (hev.comp_tendsto hcont)`.
-/
theorem contDiffAt_comp_of_cInfAt : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {ι : Type} [Fintype ι]
  {T : Set (ι → ℂ)} {s : (ι → ℂ) → CxPts p σ} {f : CxPts p σ → ℝ} {z₀ : ι → ℂ}, IsOpen T → ContinuousOn s T →
  (∀ (W : Y.Opens) (g : Γ(Y, W)), DifferentiableOn ℂ (CxPts.ev p σ W g ∘ s) (T ∩ s ⁻¹' ptsIn p σ W)) →
  z₀ ∈ T → CInfAt f (s z₀) → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f ∘ s) z₀ := by
  intro k _ Y p σ ι _ T s f z₀ hT hs hd hz h
  obtain ⟨W, ι', _, g, F, O, hyW, hO, hmem, hF, hev⟩ := h
  have hN : IsOpen (T ∩ s ⁻¹' ptsIn p σ W) := hs.isOpen_inter_preimage hT (isOpen_ptsIn W)
  have hzN : z₀ ∈ T ∩ s ⁻¹' ptsIn p σ W := ⟨hz, hyW⟩
  have hG : AnalyticAt ℂ (fun z a => ev p σ W (g a) (s z)) z₀ :=
    analyticAt_pi_iff.2 fun a => analyticAt_of_differentiableOn hN (hd W (g a)) hzN
  have hcont : ContinuousAt s z₀ := hs.continuousAt (hT.mem_nhds hz)
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F ∘ fun z a => ev p σ W (g a) (s z)) z₀ :=
    (hF.contDiffAt (hO.mem_nhds hmem)).comp z₀ (hG.contDiffAt.restrict_scalars ℝ)
  exact h1.congr_of_eventuallyEq (hev.comp_tendsto hcont)

end GlobalTheory.CompanionTheory.CxSmooth
