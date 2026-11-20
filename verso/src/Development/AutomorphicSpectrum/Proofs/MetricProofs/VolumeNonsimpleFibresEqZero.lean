import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxPosDens
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxSimple
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SetFibreFiniteOfGoodProj
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsSheetOnlyNull
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCriticalFibreInfinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetOnlyNull
import ReciprocityTheory.AnalyticForms.RegularLocalRings.MemConePtsIffChartIdeal
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxOnly

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GroundTheory.Heights₂.Heights.PtsSheetOnlyNull (ratio inv_smul_eq_cons ratio_smul_cons segre_scaleBlock
  differentiableAt_proj_segre differentiableAt_ratio swapProj swapProj_apply
  not_injective_of_coord_eventually_const)

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}

/- English proof (translation)
Use `⟨fun k => ?_, ?_⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `hz.1 k`. Use `⟨i, mul_ne_zero ?_ hi⟩` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp [hc]`. Conclude with `ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul hQ (fun k => if k = k0 then c else 1) z hz.2`.
-/
theorem mem_conePts (Q : Ideal (MRingOver ℂ ι)) (hQ : IsMultiHomogIdeal Q) (k0 : K) {c : ℂ}
    (hc : c ≠ 0) {z : (Σ k, ι k) → ℂ} (hz : z ∈ conePts Q) : scaleBlock k0 c z ∈ conePts Q := by
  refine ⟨fun k => ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    refine ⟨i, mul_ne_zero ?_ hi⟩
    split_ifs <;> simp [hc]
  · exact ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul hQ (fun k => if k = k0 then c else 1) z hz.2

/- English proof (translation)
Take `⟨k0⟩` from `‹Nonempty K›`. Use `⟨scaleBlock k0 (Ψ' (segre z) 0)⁻¹ z, mem_conePts Q hQh k0 (inv_ne_zero h0) hz, segre_scaleBlock _ _ _, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul]`. Conclude with `inv_smul_eq_cons _ h0`.
-/
theorem smul_mem_fibre {Q : Ideal (MRingOver ℂ ι)} (hQh : IsMultiHomogIdeal Q) [Nonempty K] {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ conePts Q) (Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (h0 : Ψ' (segre z) 0 ≠ 0) :
    (Ψ' (segre z) 0)⁻¹ • segre z ∈ setFibre (conePts Q) Ψ' (ratio (Ψ' (segre z))) := by
  obtain ⟨k0⟩ := ‹Nonempty K›
  refine ⟨scaleBlock k0 (Ψ' (segre z) 0)⁻¹ z, mem_conePts Q hQh k0 (inv_ne_zero h0) hz, segre_scaleBlock _ _ _, ?_⟩
  rw [map_smul]
  exact inv_smul_eq_cons _ h0

/- English proof (translation)
Introduce `z hz h`. Apply `hΨ' z hz` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Use `congrFun h (Equiv.swap 0 j i)` as an intermediate fact. Simplify `this` using `[swapProj_apply]`.
-/
theorem isGoodProj_swapProj {Q : Ideal (MRingOver ℂ ι)} {Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (hΨ' : IsSetGoodProj (conePts Q) Ψ') (j : Fin (e + 1)) : IsSetGoodProj (conePts Q) (swapProj j Ψ') := by
  intro z hz h
  apply hΨ' z hz
  funext i
  have := congrFun h (Equiv.swap 0 j i)
  simpa [swapProj_apply] using this

/- English proof (translation)
Assume the negation of the conclusion as `hall`. Use `push Not at hall`. Establish `: Nonempty K` using `hP.1`. Take `⟨t, ht⟩` from `hC e e V (fun y' => ratio (Ψ' (segre (γ y')))) hV hVne (fun y hy => (differentiableAt_ratio Ψ' (hγ y hy).1 (h0 y hy)).differentiableWithinAt) hall`. Use `(GlobalTheory.CompanionTheory.Ar.Pub.CxFib.setFibre_finite K ι Q e Ψ' hP hΨ' t).not_infinite ?_` and prove the remaining obligations.

Establish `hinj : Set.InjOn (fun y => (Ψ' (segre (γ y)) 0)⁻¹ • segre (γ y)) {y | y ∈ V ∧ ratio (Ψ' (segre (γ y))) = t}`. Introduce and unpack `y1 ⟨hy1, -⟩ y2 ⟨hy2, -⟩ h`. Establish `h'` using `congrArg Ψ h`. Simplify using `only [map_smul, (hγ y1 hy1).2.2, (hγ y2 hy2).2.2] at h'`. Establish `e0` using `congrFun h' 0`.

Simplify using `only [Pi.smul_apply, Fin.cons_zero, smul_eq_mul, mul_one] at e0`. Use function extensionality and compare the values at `i`. Establish `ei` using `congrFun h' i.succ`. Simplify using `only [Pi.smul_apply, Fin.cons_succ, smul_eq_mul] at ei`. Rewrite `ei` using `[e0]`.

Conclude with `mul_left_cancel₀ (inv_ne_zero (h0 y2 hy2)) ei`. Use `(Set.Infinite.image hinj ht).mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨y, ⟨hy, hty⟩, rfl⟩`. Use `smul_mem_fibre hP.2.1.2.1 (hγ y hy).2.1 Ψ' (h0 y hy)` as an intermediate fact. Rewrite `this` using `[hty]`. Then use the resulting hypothesis.
-/
theorem exists_injective (hC : GroundTheory.Heights₂.Heights.CriticalFibreInfinite.Statement) {Q : Ideal (MRingOver ℂ ι)} (hP : IsCxVar Q e)
    {Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hΨ' : IsSetGoodProj (conePts Q) Ψ')
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {V : Set (Fin e → ℂ)} (hV : IsOpen V) (hVne : V.Nonempty)
    (hγ : ∀ y ∈ V, DifferentiableAt ℂ γ y ∧ γ y ∈ conePts Q ∧ Ψ (segre (γ y)) = Fin.cons 1 y)
    (h0 : ∀ y ∈ V, Ψ' (segre (γ y)) 0 ≠ 0) :
    ∃ y ∈ V, Function.Injective (fderiv ℂ (fun y' => ratio (Ψ' (segre (γ y')))) y) := by
  by_contra hall
  push Not at hall
  have : Nonempty K := hP.1
  obtain ⟨t, ht⟩ := hC e e V (fun y' => ratio (Ψ' (segre (γ y')))) hV hVne
    (fun y hy => (differentiableAt_ratio Ψ' (hγ y hy).1 (h0 y hy)).differentiableWithinAt) hall
  refine (GlobalTheory.CompanionTheory.Ar.Pub.CxFib.setFibre_finite K ι Q e Ψ' hP hΨ' t).not_infinite ?_
  have hinj : Set.InjOn (fun y => (Ψ' (segre (γ y)) 0)⁻¹ • segre (γ y))
      {y | y ∈ V ∧ ratio (Ψ' (segre (γ y))) = t} := by
    rintro y1 ⟨hy1, -⟩ y2 ⟨hy2, -⟩ h
    have h' := congrArg Ψ h
    simp only [map_smul, (hγ y1 hy1).2.2, (hγ y2 hy2).2.2] at h'
    have e0 := congrFun h' 0
    simp only [Pi.smul_apply, Fin.cons_zero, smul_eq_mul, mul_one] at e0
    funext i
    have ei := congrFun h' i.succ
    simp only [Pi.smul_apply, Fin.cons_succ, smul_eq_mul] at ei
    rw [e0] at ei
    exact mul_left_cancel₀ (inv_ne_zero (h0 y2 hy2)) ei
  refine (Set.Infinite.image hinj ht).mono ?_
  rintro _ ⟨y, ⟨hy, hty⟩, rfl⟩
  have := smul_mem_fibre hP.2.1.2.1 (hγ y hy).2.1 Ψ' (h0 y hy)
  rwa [hty] at this

/- English proof (translation)
Assume the negation of the conclusion as `hall`. Use `push Not at hall`. Establish `hne : Ψ' (segre (γ y)) ≠ 0` using `hΨ' _ (hγ y hy).2.1`. Take `⟨j, hj⟩` from `Function.ne_iff.1 hne`. Establish `hj0 : j ≠ 0`.

Introduce and unpack `rfl`. Conclude with `hj (hall y hy)`. Establish `hcont : ContinuousOn (fun y' => Ψ' (segre (γ y')) j) V` using `fun y' hy' => (differentiableAt_pi.1 (differentiableAt_proj_segre Ψ' (hγ y' hy').1) j).continuousAt.continuousWithinAt`. Establish `hV'o : IsOpen (V ∩ (fun y' => Ψ' (segre (γ y')) j) ⁻¹' {0}ᶜ)` using `hcont.isOpen_inter_preimage hV isOpen_compl_singleton`. Establish `h0' : ∀ y' ∈ V ∩ (fun y' => Ψ' (segre (γ y')) j) ⁻¹' {0}ᶜ, swapProj j Ψ' (segre (γ y')) 0 ≠ 0`.

Introduce `y' hy'`. Simplify `hy'.2` using `[swapProj_apply]`. Take `⟨y1, hy1, hinj⟩` from `exists_injective hC hP (isGoodProj_swapProj hΨ' j) hV'o ⟨y, hy, hj⟩ (fun y' hy' => hγ y' hy'.1) h0'`. Use `not_injective_of_coord_eventually_const (j.pred hj0) 0 (differentiableAt_ratio _ (hγ y1 hy1.1).1 (h0' y1 hy1)) ?_ hinj` and prove the remaining obligations. Use `filter_upwards [hV'o.mem_nhds hy1] with y' hy'`.

Simplify using `[ratio, swapProj_apply, hall y' hy'.1]`.
-/
theorem exists_proj_ne_zero (hC : GroundTheory.Heights₂.Heights.CriticalFibreInfinite.Statement) {Q : Ideal (MRingOver ℂ ι)}
    (hP : IsCxVar Q e) {Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hΨ' : IsSetGoodProj (conePts Q) Ψ')
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {V : Set (Fin e → ℂ)} (hV : IsOpen V)
    (hγ : ∀ y ∈ V, DifferentiableAt ℂ γ y ∧ γ y ∈ conePts Q ∧ Ψ (segre (γ y)) = Fin.cons 1 y)
    {y : Fin e → ℂ} (hy : y ∈ V) : ∃ y' ∈ V, Ψ' (segre (γ y')) 0 ≠ 0 := by
  by_contra hall
  push Not at hall
  have hne : Ψ' (segre (γ y)) ≠ 0 := hΨ' _ (hγ y hy).2.1
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hj (hall y hy)
  have hcont : ContinuousOn (fun y' => Ψ' (segre (γ y')) j) V := fun y' hy' =>
    (differentiableAt_pi.1 (differentiableAt_proj_segre Ψ' (hγ y' hy').1) j).continuousAt.continuousWithinAt
  have hV'o : IsOpen (V ∩ (fun y' => Ψ' (segre (γ y')) j) ⁻¹' {0}ᶜ) :=
    hcont.isOpen_inter_preimage hV isOpen_compl_singleton
  have h0' : ∀ y' ∈ V ∩ (fun y' => Ψ' (segre (γ y')) j) ⁻¹' {0}ᶜ, swapProj j Ψ' (segre (γ y')) 0 ≠ 0 := by
    intro y' hy'
    simpa [swapProj_apply] using hy'.2
  obtain ⟨y1, hy1, hinj⟩ := exists_injective hC hP (isGoodProj_swapProj hΨ' j) hV'o ⟨y, hy, hj⟩
    (fun y' hy' => hγ y' hy'.1) h0'
  refine not_injective_of_coord_eventually_const (j.pred hj0) 0
    (differentiableAt_ratio _ (hγ y1 hy1.1).1 (h0' y1 hy1)) ?_ hinj
  filter_upwards [hV'o.mem_nhds hy1] with y' hy'
  simp [ratio, swapProj_apply, hall y' hy'.1]

/- English proof (translation)
Establish `hK : Nonempty K` using `hP.1`. Take `⟨k0⟩` from `hP.1`. Establish `hQh : IsMultiHomogIdeal Q` using `hP.2.1.2.1`. Use `set τ : (Fin e → ℂ) → Fin e → ℂ := fun y' => ratio (Ψ' (segre (γ y'))) with hτdef`. Establish `hcont0 : ContinuousOn (fun y' => Ψ' (segre (γ y')) 0) B` using `fun y' hy' => (differentiableAt_pi.1 (differentiableAt_proj_segre Ψ' (hγ y' hy').1) 0).continuousAt.continuousWithinAt`.

Use `set D := B ∩ (fun y' => Ψ' (segre (γ y')) 0) ⁻¹' {0}ᶜ with hDdef`. Establish `hDo : IsOpen D` using `hcont0.isOpen_inter_preimage hB isOpen_compl_singleton`. Establish `hyD : y ∈ D` using `⟨hyB, h0⟩`. Establish `hτd : DifferentiableOn ℂ τ D` using `fun y' hy' => (differentiableAt_ratio Ψ' (hγ y' hy'.1).1 hy'.2).differentiableWithinAt`. Establish `hτa : AnalyticAt ℂ τ y` using `GroundTheory.Heights₂.Heights.SheetOnlyNull.analyticOnNhd_of_differentiableOn hDo hτd y hyD`.

Establish `hτc : ContDiffAt ℂ 1 τ y` using `hτa.contDiffAt`. Use `set L := (LinearEquiv.ofInjectiveEndo (fderiv ℂ τ y : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) hinj).toContinuousLinearEquiv with hLdef`. Establish `hτL : HasFDerivAt τ (L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) y` using `hτa.differentiableAt.hasFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun v => rfl)`. Use `set φ := hτc.toOpenPartialHomeomorph τ hτL one_ne_zero with hφdef`. Establish `hφτ : ∀ y', φ y' = τ y'` using `fun y' => rfl`.

Establish `hysrc : y ∈ φ.source` using `hτc.mem_toOpenPartialHomeomorph_source hτL one_ne_zero`. Establish `hytgt : τ y ∈ φ.target` using `hτc.image_mem_toOpenPartialHomeomorph_target hτL one_ne_zero`. Establish `hsymm_y : φ.symm (τ y) = y` using `φ.left_inv hysrc`. Establish `hsymmc : ContDiffAt ℂ 1 φ.symm (τ y)` using `φ.contDiffAt_symm (f₀' := L) hytgt (by rw [hsymm_y]; exact hτL) (by rw [hsymm_y]; exact hτc)`. Establish `hev_D : ∀ᶠ t in 𝓝 (τ y), φ.symm t ∈ D` using `hsymmc.continuousAt.preimage_mem_nhds (by rw [hsymm_y]; exact hDo.mem_nhds hyD)`.

Establish `hev_d : ∀ᶠ t in 𝓝 (τ y), DifferentiableAt ℂ φ.symm t` using `(hsymmc.eventually (by simp)).mono fun t ht => ht.differentiableAt one_ne_zero`. Establish `hev_t : ∀ᶠ t in 𝓝 (τ y), t ∈ φ.target` using `φ.open_target.mem_nhds hytgt`. Use `set γ' : (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun t => scaleBlock k0 (Ψ' (segre (γ (φ.symm t))) 0)⁻¹ (γ (φ.symm t)) with hγ'def`. Establish `hγ'd : ∀ t, φ.symm t ∈ D → DifferentiableAt ℂ φ.symm t → DifferentiableAt ℂ γ' t`. Introduce `t ht hdt`.

Establish `hg : DifferentiableAt ℂ (fun t => γ (φ.symm t)) t` using `(hγ _ ht.1).1.comp t hdt`. Establish `hc : DifferentiableAt ℂ (fun t => (Ψ' (segre (γ (φ.symm t))) 0)⁻¹) t` using `((differentiableAt_pi.1 (differentiableAt_proj_segre Ψ' (hγ _ ht.1).1) 0).fun_inv ht.2).comp t hdt`. Use `differentiableAt_pi.2 fun p => ?_` and prove the remaining obligations. Simplify using `only [hγ'def, scaleBlock]`. Use `split_ifs`.

Conclude with `hc.fun_mul (differentiableAt_pi.1 hg p)`. Conclude with `(differentiableAt_const _).fun_mul (differentiableAt_pi.1 hg p)`. Establish `hsheet : IsSetSheet (conePts Q) Ψ' (τ y) ((Ψ' (segre (γ y)) 0)⁻¹ • segre (γ y)) γ'`. Use `⟨by simp only [hγ'def, hsymm_y, segre_scaleBlock], ?_⟩` and prove the remaining obligations. Use `filter_upwards [hev_D, hev_d, hev_t] with t h1 h2 h3`.

Use `⟨hγ'd t h1 h2, mem_conePts Q hQh k0 (inv_ne_zero h1.2) (hγ _ h1.1).2.1, ?_⟩` and prove the remaining obligations. Simplify using `only [hγ'def, segre_scaleBlock, map_smul]`. Rewrite using `[inv_smul_eq_cons _ h1.2]`. Conclude with `congrArg _ (φ.right_inv h3)`. Establish `hΨc : Continuous Ψ` using `LinearMap.continuous_of_finiteDimensional Ψ`.

Use `set w' := (Ψ' (segre (γ y)) 0)⁻¹ • segre (γ y) with hw'def`. Establish `hΨw' : Ψ w' = (Ψ' (segre (γ y)) 0)⁻¹ • (Fin.cons 1 y : Fin (e + 1) → ℂ)`. Rewrite using `[hw'def, map_smul, (hγ y hyB).2.2]`. Establish `hw'0 : Ψ w' 0 ≠ 0`. Rewrite using `[hΨw']`.

Simplify using `using h0`. Set `m : (Fin e → ℂ) × (((k : K) → ι k) → ℂ) → (Fin e → ℂ) × (((k : K) → ι k) → ℂ)` to `fun q => (ratio (Ψ q.2), (Ψ q.2 0)⁻¹ • q.2)`. Establish `hm0 : m (τ y, w') = (y, segre (γ y))`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show ratio (Ψ w') = y`.

Rewrite using `[hΨw', ratio_smul_cons (inv_ne_zero h0)]`. Use `show (Ψ w' 0)⁻¹ • w' = segre (γ y)`. Rewrite using `[hΨw', hw'def]`. Simplify using `[h0]`. Establish `h2 : Continuous fun q : (Fin e → ℂ) × (((k : K) → ι k) → ℂ) => Ψ q.2` using `hΨc.comp continuous_snd`.

Establish `h20 : ContinuousAt (fun q : (Fin e → ℂ) × (((k : K) → ι k) → ℂ) => Ψ q.2 0) (τ y, w')` using `((continuous_apply 0).comp h2).continuousAt`. Establish `hmc : ContinuousAt m (τ y, w')`. Use `ContinuousAt.prodMk ?_ ?_` and prove the remaining obligations. Use `continuousAt_pi.2 fun i => ?_` and prove the remaining obligations. Conclude with `ContinuousAt.div (f := fun q : (Fin e → ℂ) × (((k : K) → ι k) → ℂ) => Ψ q.2 i.succ) ((continuous_apply i.succ).comp h2).continuousAt h20 hw'0`.

Conclude with `(h20.inv₀ hw'0).smul continuous_snd.continuousAt`. Establish `hm : Tendsto m (𝓝 (τ y, w')) (𝓝 (y, segre (γ y)))` using `hm0 ▸ hmc.tendsto`. Establish `hev1` using `hm.eventually huniq`. Establish `hev2 : ∀ᶠ q in 𝓝 (τ y, w'), (m q).1 ∈ φ.source` using `((continuous_fst.tendsto _).comp hm).eventually (φ.open_source.mem_nhds hysrc)`. Establish `hev3 : ∀ᶠ q in 𝓝 (τ y, w'), Ψ q.2 0 ≠ 0` using `h20.eventually_ne hw'0`.

Use `⟨τ y, γ', hsheet, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hev1, hev2, hev3] with q hq1 hq2 hq3 hqf`. Take `⟨z, hz, hzs, hΨ'z⟩` from `hqf`. Establish `hfib : (m q).2 ∈ setFibre (conePts Q) Ψ (m q).1`. Use `smul_mem_fibre hQh hz Ψ (by rw [hzs]; exact hq3)` as an intermediate fact.

Rewrite `this` using `[hzs]`. Conclude with `this`. Establish `hE : (Ψ q.2 0)⁻¹ • q.2 = segre (γ (ratio (Ψ q.2)))` using `hq1 hfib`. Establish `hs' : Ψ' (segre (γ (ratio (Ψ q.2)))) = (Ψ q.2 0)⁻¹ • (Fin.cons 1 q.1 : Fin (e + 1) → ℂ)`. Rewrite using `[← hE, map_smul, hΨ'z]`.

Establish `hτs : τ (ratio (Ψ q.2)) = q.1` using `by show ratio (Ψ' (segre (γ (ratio (Ψ q.2))))) = q.1`. Rewrite using `[hs', ratio_smul_cons (inv_ne_zero hq3)]`. Establish `hsymm_q : φ.symm q.1 = ratio (Ψ q.2)`. Rewrite using `[← hτs]`. Conclude with `φ.left_inv hq2`.

Use `show q.2 = segre (scaleBlock k0 (Ψ' (segre (γ (φ.symm q.1))) 0)⁻¹ (γ (φ.symm q.1)))`. Rewrite using `[hsymm_q, segre_scaleBlock, hs', ← hE]`. Simplify using `[hq3]`.
-/
theorem isSimpleSheetPt_of_injective {Q : Ideal (MRingOver ℂ ι)} (hP : IsCxVar Q e)
    {Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    {B : Set (Fin e → ℂ)} (hB : IsOpen B)
    (hγ : ∀ y ∈ B, DifferentiableAt ℂ γ y ∧ γ y ∈ conePts Q ∧ Ψ (segre (γ y)) = Fin.cons 1 y)
    {y : Fin e → ℂ} (hyB : y ∈ B)
    (huniq : ∀ᶠ q in 𝓝 (y, segre (γ y)), q.2 ∈ setFibre (conePts Q) Ψ q.1 → q.2 = segre (γ q.1))
    (h0 : Ψ' (segre (γ y)) 0 ≠ 0)
    (hinj : Function.Injective (fderiv ℂ (fun y' => ratio (Ψ' (segre (γ y')))) y)) :
    cxSimple (conePts Q) Ψ' ((Ψ' (segre (γ y)) 0)⁻¹ • segre (γ y)) := by
  have hK : Nonempty K := hP.1
  obtain ⟨k0⟩ := hP.1
  have hQh : IsMultiHomogIdeal Q := hP.2.1.2.1
  set τ : (Fin e → ℂ) → Fin e → ℂ := fun y' => ratio (Ψ' (segre (γ y'))) with hτdef
  have hcont0 : ContinuousOn (fun y' => Ψ' (segre (γ y')) 0) B := fun y' hy' =>
    (differentiableAt_pi.1 (differentiableAt_proj_segre Ψ' (hγ y' hy').1) 0).continuousAt.continuousWithinAt
  set D := B ∩ (fun y' => Ψ' (segre (γ y')) 0) ⁻¹' {0}ᶜ with hDdef
  have hDo : IsOpen D := hcont0.isOpen_inter_preimage hB isOpen_compl_singleton
  have hyD : y ∈ D := ⟨hyB, h0⟩
  have hτd : DifferentiableOn ℂ τ D := fun y' hy' =>
    (differentiableAt_ratio Ψ' (hγ y' hy'.1).1 hy'.2).differentiableWithinAt
  have hτa : AnalyticAt ℂ τ y := GroundTheory.Heights₂.Heights.SheetOnlyNull.analyticOnNhd_of_differentiableOn hDo hτd y hyD
  have hτc : ContDiffAt ℂ 1 τ y := hτa.contDiffAt
  set L := (LinearEquiv.ofInjectiveEndo (fderiv ℂ τ y : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))
    hinj).toContinuousLinearEquiv with hLdef
  have hτL : HasFDerivAt τ (L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) y :=
    hτa.differentiableAt.hasFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun v => rfl)
  set φ := hτc.toOpenPartialHomeomorph τ hτL one_ne_zero with hφdef
  have hφτ : ∀ y', φ y' = τ y' := fun y' => rfl
  have hysrc : y ∈ φ.source := hτc.mem_toOpenPartialHomeomorph_source hτL one_ne_zero
  have hytgt : τ y ∈ φ.target := hτc.image_mem_toOpenPartialHomeomorph_target hτL one_ne_zero
  have hsymm_y : φ.symm (τ y) = y := φ.left_inv hysrc
  have hsymmc : ContDiffAt ℂ 1 φ.symm (τ y) :=
    φ.contDiffAt_symm (f₀' := L) hytgt (by rw [hsymm_y]; exact hτL) (by rw [hsymm_y]; exact hτc)
  have hev_D : ∀ᶠ t in 𝓝 (τ y), φ.symm t ∈ D :=
    hsymmc.continuousAt.preimage_mem_nhds (by rw [hsymm_y]; exact hDo.mem_nhds hyD)
  have hev_d : ∀ᶠ t in 𝓝 (τ y), DifferentiableAt ℂ φ.symm t :=
    (hsymmc.eventually (by simp)).mono fun t ht => ht.differentiableAt one_ne_zero
  have hev_t : ∀ᶠ t in 𝓝 (τ y), t ∈ φ.target := φ.open_target.mem_nhds hytgt
  set γ' : (Fin e → ℂ) → (Σ k, ι k) → ℂ :=
    fun t => scaleBlock k0 (Ψ' (segre (γ (φ.symm t))) 0)⁻¹ (γ (φ.symm t)) with hγ'def
  have hγ'd : ∀ t, φ.symm t ∈ D → DifferentiableAt ℂ φ.symm t → DifferentiableAt ℂ γ' t := by
    intro t ht hdt
    have hg : DifferentiableAt ℂ (fun t => γ (φ.symm t)) t := (hγ _ ht.1).1.comp t hdt
    have hc : DifferentiableAt ℂ (fun t => (Ψ' (segre (γ (φ.symm t))) 0)⁻¹) t :=
      ((differentiableAt_pi.1 (differentiableAt_proj_segre Ψ' (hγ _ ht.1).1) 0).fun_inv ht.2).comp t hdt
    refine differentiableAt_pi.2 fun p => ?_
    simp only [hγ'def, scaleBlock]
    split_ifs
    · exact hc.fun_mul (differentiableAt_pi.1 hg p)
    · exact (differentiableAt_const _).fun_mul (differentiableAt_pi.1 hg p)
  have hsheet : IsSetSheet (conePts Q) Ψ' (τ y) ((Ψ' (segre (γ y)) 0)⁻¹ • segre (γ y)) γ' := by
    refine ⟨by simp only [hγ'def, hsymm_y, segre_scaleBlock], ?_⟩
    filter_upwards [hev_D, hev_d, hev_t] with t h1 h2 h3
    refine ⟨hγ'd t h1 h2, mem_conePts Q hQh k0 (inv_ne_zero h1.2) (hγ _ h1.1).2.1, ?_⟩
    simp only [hγ'def, segre_scaleBlock, map_smul]
    rw [inv_smul_eq_cons _ h1.2]
    exact congrArg _ (φ.right_inv h3)
  have hΨc : Continuous Ψ := LinearMap.continuous_of_finiteDimensional Ψ
  set w' := (Ψ' (segre (γ y)) 0)⁻¹ • segre (γ y) with hw'def
  have hΨw' : Ψ w' = (Ψ' (segre (γ y)) 0)⁻¹ • (Fin.cons 1 y : Fin (e + 1) → ℂ) := by
    rw [hw'def, map_smul, (hγ y hyB).2.2]
  have hw'0 : Ψ w' 0 ≠ 0 := by
    rw [hΨw']
    simpa using h0
  let m : (Fin e → ℂ) × (((k : K) → ι k) → ℂ) → (Fin e → ℂ) × (((k : K) → ι k) → ℂ) :=
    fun q => (ratio (Ψ q.2), (Ψ q.2 0)⁻¹ • q.2)
  have hm0 : m (τ y, w') = (y, segre (γ y)) := by
    refine Prod.ext ?_ ?_
    · show ratio (Ψ w') = y
      rw [hΨw', ratio_smul_cons (inv_ne_zero h0)]
    · show (Ψ w' 0)⁻¹ • w' = segre (γ y)
      rw [hΨw', hw'def]
      simp [h0]
  have h2 : Continuous fun q : (Fin e → ℂ) × (((k : K) → ι k) → ℂ) => Ψ q.2 := hΨc.comp continuous_snd
  have h20 : ContinuousAt (fun q : (Fin e → ℂ) × (((k : K) → ι k) → ℂ) => Ψ q.2 0) (τ y, w') :=
    ((continuous_apply 0).comp h2).continuousAt
  have hmc : ContinuousAt m (τ y, w') := by
    refine ContinuousAt.prodMk ?_ ?_
    · refine continuousAt_pi.2 fun i => ?_
      exact ContinuousAt.div (f := fun q : (Fin e → ℂ) × (((k : K) → ι k) → ℂ) => Ψ q.2 i.succ)
        ((continuous_apply i.succ).comp h2).continuousAt h20 hw'0
    · exact (h20.inv₀ hw'0).smul continuous_snd.continuousAt
  have hm : Tendsto m (𝓝 (τ y, w')) (𝓝 (y, segre (γ y))) := hm0 ▸ hmc.tendsto
  have hev1 := hm.eventually huniq
  have hev2 : ∀ᶠ q in 𝓝 (τ y, w'), (m q).1 ∈ φ.source :=
    ((continuous_fst.tendsto _).comp hm).eventually (φ.open_source.mem_nhds hysrc)
  have hev3 : ∀ᶠ q in 𝓝 (τ y, w'), Ψ q.2 0 ≠ 0 := h20.eventually_ne hw'0
  refine ⟨τ y, γ', hsheet, ?_⟩
  filter_upwards [hev1, hev2, hev3] with q hq1 hq2 hq3 hqf
  obtain ⟨z, hz, hzs, hΨ'z⟩ := hqf
  have hfib : (m q).2 ∈ setFibre (conePts Q) Ψ (m q).1 := by
    have := smul_mem_fibre hQh hz Ψ (by rw [hzs]; exact hq3)
    rw [hzs] at this
    exact this
  have hE : (Ψ q.2 0)⁻¹ • q.2 = segre (γ (ratio (Ψ q.2))) := hq1 hfib
  have hs' : Ψ' (segre (γ (ratio (Ψ q.2)))) = (Ψ q.2 0)⁻¹ • (Fin.cons 1 q.1 : Fin (e + 1) → ℂ) := by
    rw [← hE, map_smul, hΨ'z]
  have hτs : τ (ratio (Ψ q.2)) = q.1 := by
    show ratio (Ψ' (segre (γ (ratio (Ψ q.2))))) = q.1
    rw [hs', ratio_smul_cons (inv_ne_zero hq3)]
  have hsymm_q : φ.symm q.1 = ratio (Ψ q.2) := by
    rw [← hτs]
    exact φ.left_inv hq2
  show q.2 = segre (scaleBlock k0 (Ψ' (segre (γ (φ.symm q.1))) 0)⁻¹ (γ (φ.symm q.1)))
  rw [hsymm_q, segre_scaleBlock, hs', ← hE]
  simp [hq3]

/- English proof (translation)
Use `set τ : (Fin e → ℂ) → Fin e → ℂ := fun y' => ratio (Ψ' (segre (γ y'))) with hτdef`. Use `set B := Prod.fst '' O with hBdef`. Establish `hBo : IsOpen B` using `isOpenMap_fst O hOo`. Establish `hγB : ∀ y ∈ B, DifferentiableAt ℂ γ y ∧ γ y ∈ conePts Q ∧ Ψ (segre (γ y)) = Fin.cons 1 y`. Introduce and unpack `_ ⟨q, hq, rfl⟩`.

Conclude with `(hO q hq).1`. Establish `hgc : ContinuousOn (fun y => (y, segre (γ y))) B` using `fun y hy => (continuousAt_id.prodMk (segre_differentiableAt (hγB y hy).1).continuousAt).continuousWithinAt`. Use `set D := B ∩ (fun y => (y, segre (γ y))) ⁻¹' O with hDdef`. Establish `hDo : IsOpen D` using `hgc.isOpen_inter_preimage hBo hOo`. Establish `hcont0 : ContinuousOn (fun y' => Ψ' (segre (γ y')) 0) B` using `fun y' hy' => (differentiableAt_pi.1 (differentiableAt_proj_segre Ψ' (hγB y' hy').1) 0).continuousAt.continuousWithinAt`.

Establish `hsub : {y | (y, segre (γ y)) ∈ O ∧ ¬ cxSimple (conePts Q) Ψ' ((Ψ' (segre (γ y)) 0)⁻¹ • segre (γ y))} ⊆ {y | y ∈ D ∧ Ψ' (segre (γ y)) 0 = 0} ∪ {y | y ∈ D ∧ Ψ' (segre (γ y)) 0 ≠ 0 ∧ ¬ Function.Injective (fderiv ℂ τ y)}`. Introduce and unpack `y ⟨hyO, hns⟩`. Establish `hyD : y ∈ D` using `⟨⟨_, hyO, rfl⟩, hyO⟩`. Distinguish the cases in `h0 : Ψ' (segre (γ y)) 0 = 0`. Conclude with `Or.inl ⟨hyD, h0⟩`.

Use `Or.inr ⟨hyD, h0, fun hinj => hns ?_⟩` and prove the remaining obligations. Establish `huniq : ∀ᶠ q in 𝓝 (y, segre (γ y)), q.2 ∈ setFibre (conePts Q) Ψ q.1 → q.2 = segre (γ q.1)` using `Filter.mem_of_superset (hOo.mem_nhds hyO) fun q hq => (hO q hq).2`. Conclude with `isSimpleSheetPt_of_injective hP hBo hγB hyD.1 huniq h0 hinj`. Use `measure_mono_null hsub (measure_union_null ?_ ?_)` and prove the remaining obligations. Apply `ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set` to reduce the goal to its premises.

Introduce and unpack `y ⟨hyD, -⟩`. Take `⟨r, hr, hball⟩` from `Metric.isOpen_iff.1 hDo y hyD`. Use `⟨Metric.ball y r, Metric.isOpen_ball, Metric.mem_ball_self hr, (convex_ball y r).isPreconnected, fun y' => Ψ' (segre (γ y')) 0, ?_, ?_, fun y' hy' => hy'.1.2⟩` and prove the remaining obligations. Conclude with `(osgood e D _ hDo (fun y' hy' => (differentiableAt_pi.1 (differentiableAt_proj_segre Ψ' (hγB y' hy'.1).1) 0).differentiableWithinAt)).mono hball`. Conclude with `exists_proj_ne_zero hC hP hΨ' Metric.isOpen_ball (fun y' hy' => hγB y' (hball hy').1) (Metric.mem_ball_self hr)`.

Apply `ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set` to reduce the goal to its premises. Introduce and unpack `y ⟨hyD, hy0, -⟩`. Establish `hD'o : IsOpen (D ∩ (fun y' => Ψ' (segre (γ y')) 0) ⁻¹' {0}ᶜ)` using `(hcont0.mono Set.inter_subset_left).isOpen_inter_preimage hDo isOpen_compl_singleton`. Take `⟨r, hr, hball⟩` from `Metric.isOpen_iff.1 hD'o y ⟨hyD, hy0⟩`. Establish `hτd : DifferentiableOn ℂ τ (D ∩ (fun y' => Ψ' (segre (γ y')) 0) ⁻¹' {0}ᶜ)` using `fun y' hy' => (differentiableAt_ratio Ψ' (hγB y' hy'.1.1).1 hy'.2).differentiableWithinAt`.

Use `⟨Metric.ball y r, Metric.isOpen_ball, Metric.mem_ball_self hr, (convex_ball y r).isPreconnected, fun y' => (ReciprocityTheory.AnForm.A.jacC τ y').det, (GroundTheory.Heights₂.Heights.SheetOnlyNull.analyticOnNhd_det_jacC hD'o hτd).mono hball, ?_, ?_⟩` and prove the remaining obligations. Take `⟨y1, hy1, hinj⟩` from `exists_injective hC hP hΨ' Metric.isOpen_ball ⟨y, Metric.mem_ball_self hr⟩ (fun y' hy' => hγB y' (hball hy').1.1) (fun y' hy' => (hball hy').2)`. Use `⟨y1, hy1, ?_⟩` and prove the remaining obligations. Use `show (ReciprocityTheory.AnForm.A.jacC τ y1).det ≠ 0`. Rewrite using `[ReciprocityTheory.AnForm.A.det_jacC]`.

Conclude with `(GroundTheory.Heights₂.Heights.SheetOnlyNull.injective_iff_det_ne_zero _).1 hinj`. Introduce and unpack `y' ⟨⟨-, -, hni⟩, -⟩ show (ReciprocityTheory.AnForm.A.jacC τ y').det = 0`. Rewrite using `[ReciprocityTheory.AnForm.A.det_jacC]`. Assume the negation of the conclusion as `hne`. Conclude with `hni ((GroundTheory.Heights₂.Heights.SheetOnlyNull.injective_iff_det_ne_zero _).2 hne)`.
-/
theorem piece_null (hC : GroundTheory.Heights₂.Heights.CriticalFibreInfinite.Statement) {Q : Ideal (MRingOver ℂ ι)} (hP : IsCxVar Q e)
    {Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hΨ' : IsSetGoodProj (conePts Q) Ψ')
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {O : Set ((Fin e → ℂ) × (((k : K) → ι k) → ℂ))} (hOo : IsOpen O)
    (hO : ∀ q ∈ O, (DifferentiableAt ℂ γ q.1 ∧ γ q.1 ∈ conePts Q ∧ Ψ (segre (γ q.1)) = Fin.cons 1 q.1) ∧
      (q.2 ∈ setFibre (conePts Q) Ψ q.1 → q.2 = segre (γ q.1))) :
    volume {y | (y, segre (γ y)) ∈ O ∧
      ¬ cxSimple (conePts Q) Ψ' ((Ψ' (segre (γ y)) 0)⁻¹ • segre (γ y))} = 0 := by
  set τ : (Fin e → ℂ) → Fin e → ℂ := fun y' => ratio (Ψ' (segre (γ y'))) with hτdef
  set B := Prod.fst '' O with hBdef
  have hBo : IsOpen B := isOpenMap_fst O hOo
  have hγB : ∀ y ∈ B, DifferentiableAt ℂ γ y ∧ γ y ∈ conePts Q ∧ Ψ (segre (γ y)) = Fin.cons 1 y := by
    rintro _ ⟨q, hq, rfl⟩
    exact (hO q hq).1
  have hgc : ContinuousOn (fun y => (y, segre (γ y))) B := fun y hy =>
    (continuousAt_id.prodMk (segre_differentiableAt (hγB y hy).1).continuousAt).continuousWithinAt
  set D := B ∩ (fun y => (y, segre (γ y))) ⁻¹' O with hDdef
  have hDo : IsOpen D := hgc.isOpen_inter_preimage hBo hOo
  have hcont0 : ContinuousOn (fun y' => Ψ' (segre (γ y')) 0) B := fun y' hy' =>
    (differentiableAt_pi.1 (differentiableAt_proj_segre Ψ' (hγB y' hy').1) 0).continuousAt.continuousWithinAt
  have hsub : {y | (y, segre (γ y)) ∈ O ∧ ¬ cxSimple (conePts Q) Ψ' ((Ψ' (segre (γ y)) 0)⁻¹ • segre (γ y))} ⊆
      {y | y ∈ D ∧ Ψ' (segre (γ y)) 0 = 0} ∪
        {y | y ∈ D ∧ Ψ' (segre (γ y)) 0 ≠ 0 ∧ ¬ Function.Injective (fderiv ℂ τ y)} := by
    rintro y ⟨hyO, hns⟩
    have hyD : y ∈ D := ⟨⟨_, hyO, rfl⟩, hyO⟩
    by_cases h0 : Ψ' (segre (γ y)) 0 = 0
    · exact Or.inl ⟨hyD, h0⟩
    · refine Or.inr ⟨hyD, h0, fun hinj => hns ?_⟩
      have huniq : ∀ᶠ q in 𝓝 (y, segre (γ y)), q.2 ∈ setFibre (conePts Q) Ψ q.1 → q.2 = segre (γ q.1) :=
        Filter.mem_of_superset (hOo.mem_nhds hyO) fun q hq => (hO q hq).2
      exact isSimpleSheetPt_of_injective hP hBo hγB hyD.1 huniq h0 hinj
  refine measure_mono_null hsub (measure_union_null ?_ ?_)
  · apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
    rintro y ⟨hyD, -⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hDo y hyD
    refine ⟨Metric.ball y r, Metric.isOpen_ball, Metric.mem_ball_self hr, (convex_ball y r).isPreconnected,
      fun y' => Ψ' (segre (γ y')) 0, ?_, ?_, fun y' hy' => hy'.1.2⟩
    · exact (osgood e D _ hDo (fun y' hy' => (differentiableAt_pi.1
        (differentiableAt_proj_segre Ψ' (hγB y' hy'.1).1) 0).differentiableWithinAt)).mono hball
    · exact exists_proj_ne_zero hC hP hΨ' Metric.isOpen_ball (fun y' hy' => hγB y' (hball hy').1)
        (Metric.mem_ball_self hr)
  · apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
    rintro y ⟨hyD, hy0, -⟩
    have hD'o : IsOpen (D ∩ (fun y' => Ψ' (segre (γ y')) 0) ⁻¹' {0}ᶜ) :=
      (hcont0.mono Set.inter_subset_left).isOpen_inter_preimage hDo isOpen_compl_singleton
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hD'o y ⟨hyD, hy0⟩
    have hτd : DifferentiableOn ℂ τ (D ∩ (fun y' => Ψ' (segre (γ y')) 0) ⁻¹' {0}ᶜ) := fun y' hy' =>
      (differentiableAt_ratio Ψ' (hγB y' hy'.1.1).1 hy'.2).differentiableWithinAt
    refine ⟨Metric.ball y r, Metric.isOpen_ball, Metric.mem_ball_self hr, (convex_ball y r).isPreconnected,
      fun y' => (ReciprocityTheory.AnForm.A.jacC τ y').det,
      (GroundTheory.Heights₂.Heights.SheetOnlyNull.analyticOnNhd_det_jacC hD'o hτd).mono hball, ?_, ?_⟩
    · obtain ⟨y1, hy1, hinj⟩ := exists_injective hC hP hΨ' Metric.isOpen_ball ⟨y, Metric.mem_ball_self hr⟩
        (fun y' hy' => hγB y' (hball hy').1.1) (fun y' hy' => (hball hy').2)
      refine ⟨y1, hy1, ?_⟩
      show (ReciprocityTheory.AnForm.A.jacC τ y1).det ≠ 0
      rw [ReciprocityTheory.AnForm.A.det_jacC]
      exact (GroundTheory.Heights₂.Heights.SheetOnlyNull.injective_iff_det_ne_zero _).1 hinj
    · rintro y' ⟨⟨-, -, hni⟩, -⟩
      show (ReciprocityTheory.AnForm.A.jacC τ y').det = 0
      rw [ReciprocityTheory.AnForm.A.det_jacC]
      by_contra hne
      exact hni ((GroundTheory.Heights₂.Heights.SheetOnlyNull.injective_iff_det_ne_zero _).2 hne)

/- English proof (translation)
Introduce `K _ ι _ Q e Ψ Ψ' hP hΨ hΨ'`. Establish `hloc : ∀ p : (Fin e → ℂ) × (((k : K) → ι k) → ℂ), ∃ (γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ) (O : Set ((Fin e → ℂ) × (((k : K) → ι k) → ℂ))), IsOpen O ∧ (∀ q ∈ O, (DifferentiableAt ℂ γ q.1 ∧ γ q.1 ∈ conePts Q ∧ Ψ (segre (γ q.1)) = Fin.cons 1 q.1) ∧ (q.2 ∈ setFibre (conePts Q) Ψ q.1 → q …`. Introduce `p`. Distinguish the cases in `hp : p.2 ∈ setFibre (conePts Q) Ψ p.1 ∧ cxSimple (conePts Q) Ψ p.2`. Take `⟨hpf, y0, γ, ⟨hseg, hsh⟩, hun⟩` from `hp`.

Establish `hy0 : y0 = p.1`. Take `⟨z, -, -, hΨz⟩` from `hpf`. Establish `h1` using `hsh.self_of_nhds.2.2`. Rewrite `h1` using `[hseg, hΨz]`. Use function extensionality and compare the values at `i`.

Establish `hi` using `congrFun h1 i.succ`. Simplify using `only [Fin.cons_succ] at hi`. Conclude with `hi.symm`. Substitute `hy0` using the available equality. Establish `hev : ∀ᶠ q in 𝓝 (p.1, p.2), (DifferentiableAt ℂ γ q.1 ∧ γ q.1 ∈ conePts Q ∧ Ψ (segre (γ q.1)) = Fin.cons 1 q.1) ∧ (q.2 ∈ setFibre (conePts Q) Ψ q.1 → q.2 = segre (γ q.1))` using `((continuous_fst.tendsto (p.1, p.2)).eventually hsh).and hun`.

Take `⟨O, hO, hOo, hpO⟩` from `eventually_nhds_iff.1 hev`. Conclude with `⟨γ, O, hOo, hO, fun _ _ => hpO⟩`. Conclude with `⟨fun _ _ => 0, ∅, isOpen_empty, by simp, fun h1 h2 => absurd ⟨h1, h2⟩ hp⟩`. Use `choose γ O hOo hO hpO using hloc`. Take `⟨T, hTc, hTU⟩` from `TopologicalSpace.isOpen_iUnion_countable O hOo`.

Use `measure_mono_null ?_ ((measure_biUnion_null_iff hTc).2 fun p _ => piece_null GroundTheory.Heights₂.Heights.CriticalFibreInfinite.proof hP hΨ' (hOo p) (hO p))` and prove the remaining obligations. Introduce and unpack `y ⟨w, hwf, hws, hwn⟩`. Establish `hmem : (y, w) ∈ ⋃ p ∈ T, O p` using `hTU ▸ Set.mem_iUnion.2 ⟨(y, w), hpO (y, w) hwf hws⟩`. Take `⟨p, hpT, hyw⟩` from `Set.mem_iUnion₂.1 hmem`. Establish `hw : w = segre (γ p y)` using `((hO p) (y, w) hyw).2 hwf`.

Substitute `hw` using the available equality. Conclude with `Set.mem_biUnion hpT ⟨hyw, hwn⟩`.
-/
theorem cxSimple_only_null : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → IsSetGoodProj (conePts Q) Ψ' →
    volume {y : Fin e → ℂ | ∃ w ∈ setFibre (conePts Q) Ψ y, cxSimple (conePts Q) Ψ w ∧
      ¬ cxSimple (conePts Q) Ψ' ((Ψ' w 0)⁻¹ • w)} = 0 := by
  intro K _ ι _ Q e Ψ Ψ' hP hΨ hΨ'
  classical
  have hloc : ∀ p : (Fin e → ℂ) × (((k : K) → ι k) → ℂ), ∃ (γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ)
      (O : Set ((Fin e → ℂ) × (((k : K) → ι k) → ℂ))), IsOpen O ∧
      (∀ q ∈ O, (DifferentiableAt ℂ γ q.1 ∧ γ q.1 ∈ conePts Q ∧ Ψ (segre (γ q.1)) = Fin.cons 1 q.1) ∧
        (q.2 ∈ setFibre (conePts Q) Ψ q.1 → q.2 = segre (γ q.1))) ∧
      (p.2 ∈ setFibre (conePts Q) Ψ p.1 → cxSimple (conePts Q) Ψ p.2 → p ∈ O) := by
    intro p
    by_cases hp : p.2 ∈ setFibre (conePts Q) Ψ p.1 ∧ cxSimple (conePts Q) Ψ p.2
    · obtain ⟨hpf, y0, γ, ⟨hseg, hsh⟩, hun⟩ := hp
      have hy0 : y0 = p.1 := by
        obtain ⟨z, -, -, hΨz⟩ := hpf
        have h1 := hsh.self_of_nhds.2.2
        rw [hseg, hΨz] at h1
        funext i
        have hi := congrFun h1 i.succ
        simp only [Fin.cons_succ] at hi
        exact hi.symm
      subst hy0
      have hev : ∀ᶠ q in 𝓝 (p.1, p.2),
          (DifferentiableAt ℂ γ q.1 ∧ γ q.1 ∈ conePts Q ∧ Ψ (segre (γ q.1)) = Fin.cons 1 q.1) ∧
            (q.2 ∈ setFibre (conePts Q) Ψ q.1 → q.2 = segre (γ q.1)) :=
        ((continuous_fst.tendsto (p.1, p.2)).eventually hsh).and hun
      obtain ⟨O, hO, hOo, hpO⟩ := eventually_nhds_iff.1 hev
      exact ⟨γ, O, hOo, hO, fun _ _ => hpO⟩
    · exact ⟨fun _ _ => 0, ∅, isOpen_empty, by simp, fun h1 h2 => absurd ⟨h1, h2⟩ hp⟩
  choose γ O hOo hO hpO using hloc
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable O hOo
  refine measure_mono_null ?_ ((measure_biUnion_null_iff hTc).2 fun p _ =>
    piece_null GroundTheory.Heights₂.Heights.CriticalFibreInfinite.proof hP hΨ' (hOo p) (hO p))
  rintro y ⟨w, hwf, hws, hwn⟩
  have hmem : (y, w) ∈ ⋃ p ∈ T, O p := hTU ▸ Set.mem_iUnion.2 ⟨(y, w), hpO (y, w) hwf hws⟩
  obtain ⟨p, hpT, hyw⟩ := Set.mem_iUnion₂.1 hmem
  have hw : w = segre (γ p y) := ((hO p) (y, w) hyw).2 hwf
  subst hw
  exact Set.mem_biUnion hpT ⟨hyw, hwn⟩

end GlobalTheory.CompanionTheory.Ar.Pub.CxOnly
