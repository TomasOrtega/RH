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
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.SegreChartProjObjects
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MemChartComponents
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsSegreChartFibreSum
set_option maxSynthPendingDepth 1

noncomputable section

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart.FibSum

open scoped Matrix
open GroundTheory.Heights₂.Heights (chartLift chartProjMatrix_mulVec chartWeight_of_coord segre_chartLift
  chartLift_segre_apply IsSheetAt sheetSum)
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet IsFiniteProjection)
open GroundTheory.Heights₂.Heights.PtsSegreChartFibreSum (isClosed_zeroSet exists_minimalPrime_of_mem_zeroSet
  exists_poly_of_not_mem logNorm_ofWeight_one isSectionOn_ofWeight_one)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Rewrite using `[eval_eq', eval_eq', Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Establish `hprod : ∏ p, (bsmul c z p) ^ m p = (∏ k, c k ^ a k) * ∏ p, z p ^ m p`. Simplify using `only [bsmul, mul_pow, Finset.prod_mul_distrib]`. Use `congr 1`.

Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `show ∏ i, c k ^ m ⟨k, i⟩ = c k ^ a k`. Rewrite using `[Finset.prod_pow_eq_pow_sum, hs m hm k]`. Rewrite using `[hprod]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem eval_bsmul_of_isMultiHomogC {s : MRingOver ℂ ι} {a : K → ℕ} (hs : IsMultiHomog s a) (c : K → ℂ)
    (z : (Σ k, ι k) → ℂ) :
    eval (bsmul c z) s = (∏ k, c k ^ a k) * eval z s := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hprod : ∏ p, (bsmul c z p) ^ m p = (∏ k, c k ^ a k) * ∏ p, z p ^ m p := by
    simp only [bsmul, mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, c k ^ m ⟨k, i⟩ = c k ^ a k
    rw [Finset.prod_pow_eq_pow_sum, hs m hm k]
  rw [hprod]
  ring

/- English proof (translation)
Use `⟨fun k => ?_, fun f hf => ?_⟩` and prove the remaining obligations. Take `⟨j, hj⟩` from `hz.1 k`. Conclude with `⟨j, mul_ne_zero (hc k) hj⟩`. Take `⟨S, hS, hQS⟩` from `hQ`. Establish `hle : Q ≤ RingHom.ker (MvPolynomial.eval (bsmul c z))`.

Rewrite using `[hQS, Ideal.span_le]`. Introduce `s hs`. Take `⟨a, ha⟩` from `hS s hs`. Rewrite using `[SetLike.mem_coe, RingHom.mem_ker, eval_bsmul_of_isMultiHomogC ha, hz.2 s (by rw [hQS]; exact Ideal.subset_span hs), mul_zero]`. Conclude with `hle hf`.
-/
theorem bsmul_mem_conePts {Q : Ideal (MRingOver ℂ ι)} (hQ : IsMultiHomogIdeal Q) {c : K → ℂ}
    (hc : ∀ k, c k ≠ 0) {z : (Σ k, ι k) → ℂ} (hz : z ∈ conePts Q) : bsmul c z ∈ conePts Q := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨j, hj⟩ := hz.1 k
    exact ⟨j, mul_ne_zero (hc k) hj⟩
  · obtain ⟨S, hS, hQS⟩ := hQ
    have hle : Q ≤ RingHom.ker (MvPolynomial.eval (bsmul c z)) := by
      rw [hQS, Ideal.span_le]
      intro s hs
      obtain ⟨a, ha⟩ := hS s hs
      rw [SetLike.mem_coe, RingHom.mem_ker, eval_bsmul_of_isMultiHomogC ha,
        hz.2 s (by rw [hQS]; exact Ideal.subset_span hs), mul_zero]
    exact hle hf

/- English proof (translation)
Use `⟨h.1, h.2.mono fun y' hy' => ⟨hy'.1, ⟨hy'.2.1.1, fun f hf => ?_⟩, hy'.2.2⟩⟩` and prove the remaining obligations. Rewrite using `[Ideal.mem_bot.1 hf]`. Simplify using the standard rewrite rules.
-/
theorem isSheet_bot_of_isSetSheet {e : ℕ} {Q : Ideal (MRingOver ℂ ι)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {y : Fin e → ℂ}
    {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    (h : IsSetSheet (conePts Q) Ψ y w γ) : IsSheet (⊥ : Ideal (MRing ι)) Ψ y w γ := by
  refine ⟨h.1, h.2.mono fun y' hy' => ⟨hy'.1, ⟨hy'.2.1.1, fun f hf => ?_⟩, hy'.2.2⟩⟩
  rw [Ideal.mem_bot.1 hf]
  simp

/- English proof (translation)
Take `⟨z, hz, hzi, hxe⟩` from `hx`. Establish `hw : (fun i' => x (σ.symm i')) = segre z`. Use function extensionality and compare the values at `i'`. Simplify using `[hxe]`. Use `⟨z, hz, hw.symm, ?_⟩` and prove the remaining obligations.

Rewrite using `[hw]`. Use function extensionality and compare the values at `r`. Use `Fin.cases ?_ (fun r => ?_) r` and prove the remaining obligations. Rewrite using `[hΨ0, hzi, Fin.cons_zero]`. Rewrite using `[Fin.cons_succ, chartProjMatrix_mulVec, hw]`.
-/
theorem mem_setFibre_of_chart {e m : ℕ} {S : Set ((Σ k, ι k) → ℂ)} {σ : Fin m ≃ ((k : K) → ι k)}
    {i : (k : K) → ι k} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hΨ0 : ∀ w, Ψ w 0 = w i)
    {x : Fin m → ℂ} (hx : x ∈ chartSet S σ i) :
    (fun i' => x (σ.symm i')) ∈ setFibre S Ψ (chartProjMatrix σ Ψ *ᵥ x) := by
  obtain ⟨z, hz, hzi, hxe⟩ := hx
  have hw : (fun i' => x (σ.symm i')) = segre z := by
    funext i'
    simp [hxe]
  refine ⟨z, hz, hw.symm, ?_⟩
  rw [hw]
  funext r
  refine Fin.cases ?_ (fun r => ?_) r
  · rw [hΨ0, hzi, Fin.cons_zero]
  · rw [Fin.cons_succ, chartProjMatrix_mulVec, hw]

/- English proof (translation)
Take `⟨z, hz, rfl, hΨw⟩` from `hw`. Establish `hzi : segre z i = 1`. Establish `h` using `hΨ0 (segre z)`. Rewrite `h` using `[hΨw, Fin.cons_zero]`. Conclude with `h.symm`.

Use `⟨⟨z, hz, hzi, rfl⟩, funext fun r => ?_⟩` and prove the remaining obligations. Rewrite using `[chartProjMatrix_mulVec]`. Simplify using `only [Equiv.apply_symm_apply]`. Rewrite using `[hΨw, Fin.cons_succ]`.
-/
theorem chart_of_mem_setFibre {e m : ℕ} {S : Set ((Σ k, ι k) → ℂ)} {σ : Fin m ≃ ((k : K) → ι k)}
    {i : (k : K) → ι k} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hΨ0 : ∀ w, Ψ w 0 = w i)
    {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} (hw : w ∈ setFibre S Ψ y) :
    (fun a => w (σ a)) ∈ chartSet S σ i ∧ chartProjMatrix σ Ψ *ᵥ (fun a => w (σ a)) = y := by
  obtain ⟨z, hz, rfl, hΨw⟩ := hw
  have hzi : segre z i = 1 := by
    have h := hΨ0 (segre z)
    rw [hΨw, Fin.cons_zero] at h
    exact h.symm
  refine ⟨⟨z, hz, hzi, rfl⟩, funext fun r => ?_⟩
  rw [chartProjMatrix_mulVec]
  simp only [Equiv.apply_symm_apply]
  rw [hΨw, Fin.cons_succ]

variable [DecidableEq K]

/- English proof (translation)
Take `⟨z, hz, hzi, rfl⟩` from `hx`. Establish `hne : ∀ k, z ⟨k, i k⟩ ≠ 0`. Establish `h1 : ∏ k, z ⟨k, i k⟩ ≠ 0`. Express the relevant statement in the definitionally equal form `segre z i ≠ 0`. Rewrite using `[hzi]`.

Conclude with `one_ne_zero`. Conclude with `fun k => (Finset.prod_ne_zero_iff.mp h1) k (Finset.mem_univ k)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `heq : chartLift σ i (fun a => segre z (σ a)) = bsmul (fun k => (z ⟨k, i k⟩)⁻¹) z`. Use function extensionality and compare the values at `p`.

Take `⟨k, j⟩` from `p`. Rewrite using `[chartLift_segre_apply σ i z hzi k j]`. Simplify using `only [bsmul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[heq]`.

Conclude with `bsmul_mem_conePts hQ (fun k => inv_ne_zero (hne k)) hz`. Rewrite using `[segre_chartLift σ i z hzi]`. Use function extensionality and compare the values at `i'`. Simplify using the standard rewrite rules.
-/
theorem chartLift_of_chartSet {m : ℕ} {Q : Ideal (MRingOver ℂ ι)} (hQ : IsMultiHomogIdeal Q)
    {σ : Fin m ≃ ((k : K) → ι k)} {i : (k : K) → ι k} {x : Fin m → ℂ}
    (hx : x ∈ chartSet (conePts Q) σ i) :
    chartLift σ i x ∈ conePts Q ∧ segre (chartLift σ i x) = fun i' => x (σ.symm i') := by
  obtain ⟨z, hz, hzi, rfl⟩ := hx
  have hne : ∀ k, z ⟨k, i k⟩ ≠ 0 := by
    have h1 : ∏ k, z ⟨k, i k⟩ ≠ 0 := by
      change segre z i ≠ 0
      rw [hzi]
      exact one_ne_zero
    exact fun k => (Finset.prod_ne_zero_iff.mp h1) k (Finset.mem_univ k)
  refine ⟨?_, ?_⟩
  · have heq : chartLift σ i (fun a => segre z (σ a)) = bsmul (fun k => (z ⟨k, i k⟩)⁻¹) z := by
      funext p
      obtain ⟨k, j⟩ := p
      rw [chartLift_segre_apply σ i z hzi k j]
      simp only [bsmul]
      ring
    rw [heq]
    exact bsmul_mem_conePts hQ (fun k => inv_ne_zero (hne k)) hz
  · rw [segre_chartLift σ i z hzi]
    funext i'
    simp

/- English proof (translation)
Take `⟨U, hUo, hxU, hsd, hsx, hsU, V, hV, hloc⟩` from `hsh.choose_spec`. Generalize the expression as in `hsh.choose = s at hsd hsx hsU hloc ⊢`. Establish `hxy : chartProjMatrix σ Ψ *ᵥ x = y` using `hx.2`. Rewrite `hxU`, `hsx` using `[hxy]`. Establish `hxC : x ∈ chartSet (conePts Q) σ i` using `hsub J hJ hx.1`.

Establish `hx1 : x (σ.symm i) = 1`. Take `⟨z, -, hzi, rfl⟩` from `hxC`. Simplify using `using hzi`. Use `set w : ((k : K) → ι k) → ℂ := fun i' => x (σ.symm i') with hw`. Establish `hγ' : IsSetSheet (conePts Q) Ψ y w (fun y' => chartLift σ i (s y'))`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show segre (chartLift σ i (s y)) = w`. Rewrite using `[hsx]`. Conclude with `(chartLift_of_chartSet hMH hxC).2`. Use `filter_upwards [hUo.mem_nhds hxU] with y' hy'`.

Establish `hsy'` using `hsU y' hy'`. Establish `hC'` using `hsub J hJ hsy'.2`. Use `⟨?_, (chartLift_of_chartSet hMH hC').1, ?_⟩` and prove the remaining obligations. Establish `hd : DifferentiableAt ℂ s y'` using `hsd.differentiableAt (hUo.mem_nhds hy')`. Use `differentiableAt_pi.2 fun p => ?_` and prove the remaining obligations.

Conclude with `differentiableAt_pi.1 hd (σ.symm (Function.update i p.1 p.2))`. Rewrite using `[(chartLift_of_chartSet hMH hC').2]`. Establish `hf` using `mem_setFibre_of_chart (Ψ := Ψ) hΨ0 hC'`. Rewrite `hf` using `[hsy'.1]`. Take `⟨_, _, _, h⟩` from `hf`.

Conclude with `h`. Establish `hex : ∃ γ, IsSetSheet (conePts Q) Ψ y w γ` using `⟨_, hγ'⟩`. Unfold `setSheetDensity`. Rewrite using `[dif_pos hex]`. Use `set γ := hex.choose with hγ_def`.

Establish `hγ : IsSetSheet (conePts Q) Ψ y w γ` using `hex.choose_spec`. Establish `hγan` using `sheet_analyticAt osgood (isSheet_bot_of_isSetSheet hγ)`. Establish `hγ'an` using `sheet_analyticAt osgood (isSheet_bot_of_isSetSheet hγ')`. Establish `hcseg : Continuous fun z : (Σ k, ι k) → ℂ => fun a : Fin m => segre z (σ a)`. Use `continuous_pi fun a => ?_` and prove the remaining obligations.

Simplify using `only [segre]`. Conclude with `continuous_finsetProd _ fun k _ => continuous_apply _`. Establish `hxy0 : (fun a => segre (γ y) (σ a)) = x`. Use function extensionality and compare the values at `a`. Rewrite using `[hγ.1]`.

Simplify using `[hw]`. Establish `ht : Tendsto (fun y' => fun a => segre (γ y') (σ a)) (𝓝 y) (𝓝 x)`. Establish `h2` using `(hcseg.continuousAt.comp hγan.continuousAt).tendsto`. Simplify using `only [Function.comp_def] at h2`. Rewrite `h2` using `[hxy0]`. Then use the resulting hypothesis.

Establish `hE4 : ∀ᶠ y' in 𝓝 y, ∀ J' ∈ chartComponents (conePts Q) σ i, J' ≠ J → (fun a => segre (γ y') (σ a)) ∉ zeroSet J'`. Use `(eventually_all_finset _).2 fun J' hJ' => ?_` and prove the remaining obligations. Distinguish the cases in `hJJ : J' = J`. Conclude with `Eventually.of_forall fun _ h => absurd hJJ h`. Conclude with `Filter.Eventually.mono (p := fun y' => (fun a => segre (γ y') (σ a)) ∈ (zeroSet J')ᶜ) (ht ((isClosed_zeroSet J').isOpen_compl.mem_nhds (hsep J' hJ' hJJ))) fun _ h _ => h`.

Establish `hseg : (fun y' => segre (γ y')) =ᶠ[𝓝 y] fun y' => segre (chartLift σ i (s y'))` using `by filter_upwards [hγ.2, hUo.mem_nhds hxU, ht hV, hE4] with y' hy' hyU hxV h4`. Take `⟨-, hmc, hΨy⟩` from `hy'`. Establish `hzi : segre (γ y') i = 1`. Establish `h` using `hΨ0 (segre (γ y'))`. Rewrite `h` using `[hΨy, Fin.cons_zero]`.

Conclude with `h.symm`. Establish `hC : (fun a => segre (γ y') (σ a)) ∈ chartSet (conePts Q) σ i` using `⟨γ y', hmc, hzi, rfl⟩`. Establish `hAx : chartProjMatrix σ Ψ *ᵥ (fun a => segre (γ y') (σ a)) = y'` using `(chart_of_mem_setFibre (Ψ := Ψ) hΨ0 ⟨γ y', hmc, rfl, hΨy⟩).2`. Take `⟨J', hJ', hxJ'⟩` from `hcov _ hC`. Establish `hJJ : J' = J`.

Assume the negation of the conclusion as `h`. Conclude with `h4 J' hJ' h hxJ'`. Establish `hxJ : (fun a => segre (γ y') (σ a)) ∈ zeroSet J` using `hJJ ▸ hxJ'`. Establish `hxs : (fun a => segre (γ y') (σ a)) = s y'`. Establish `h` using `hloc _ ⟨hxJ, hxV⟩ (by rw [hAx]; exact hyU)`.

Rewrite `h` using `[hAx]`. Then use the resulting hypothesis. Rewrite using `[← hxs]`. Conclude with `(segre_chartLift σ i (γ y') hzi).symm`. Establish `hy0 : ∀ k, ∃ j, γ y ⟨k, j⟩ ≠ 0` using `hγ.2.self_of_nhds.2.1.1`. Establish `hde` using `density_eq hL (isSectionOn_ofWeight_one (P := (⊥ : Ideal (MRing ι))) Ideal.isPrime_bot g hg) hγan hγ'an hy0 hseg`.

Rewrite `hde` using `[logNorm_ofWeight_one, logNorm_ofWeight_one]`. Rewrite using `[hde, chartWeight_of_coord g hx1, hsx]`. Both sides reduce to the same expression.
-/
theorem term_eq {e m : ℕ} {Q : Ideal (MRingOver ℂ ι)} {σ : Fin m ≃ ((k : K) → ι k)} {i : (k : K) → ι k}
    {L : Fin e → HermLine ι} {g : ((Σ k, ι k) → ℂ) → ℝ}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (hMH : IsMultiHomogIdeal Q) (hL : ∀ j, IsSmoothHerm (L j))
    (hg : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z p) = g z)
    (hΨ0 : ∀ w, Ψ w 0 = w i)
    (hsub : ∀ J ∈ chartComponents (conePts Q) σ i, zeroSet J ⊆ chartSet (conePts Q) σ i)
    (hcov : ∀ x ∈ chartSet (conePts Q) σ i, ∃ J ∈ chartComponents (conePts Q) σ i, x ∈ zeroSet J)
    {J : Ideal (MvPolynomial (Fin m) ℂ)} (hJ : J ∈ chartComponents (conePts Q) σ i)
    {y : Fin e → ℂ} {x : Fin m → ℂ}
    (hx : x ∈ GroundTheory.Heights₂.Heights.ComplexSets.fibre J (chartProjMatrix σ Ψ) y)
    (hsep : ∀ J' ∈ chartComponents (conePts Q) σ i, J' ≠ J → x ∉ zeroSet J')
    (hsh : ∃ s, IsSheetAt J (chartProjMatrix σ Ψ) x s) :
    chartWeight σ i g x * ReciprocityTheory.AnForm.maDens (fun k => chartPot σ i L k ∘ hsh.choose) y =
      setSheetDensity (conePts Q) Ψ (pot L) g y (fun i' => x (σ.symm i')) := by
  classical
  obtain ⟨U, hUo, hxU, hsd, hsx, hsU, V, hV, hloc⟩ := hsh.choose_spec
  generalize hsh.choose = s at hsd hsx hsU hloc ⊢
  have hxy : chartProjMatrix σ Ψ *ᵥ x = y := hx.2
  rw [hxy] at hxU hsx
  have hxC : x ∈ chartSet (conePts Q) σ i := hsub J hJ hx.1
  have hx1 : x (σ.symm i) = 1 := by
    obtain ⟨z, -, hzi, rfl⟩ := hxC
    simpa using hzi
  set w : ((k : K) → ι k) → ℂ := fun i' => x (σ.symm i') with hw
  have hγ' : IsSetSheet (conePts Q) Ψ y w (fun y' => chartLift σ i (s y')) := by
    refine ⟨?_, ?_⟩
    · show segre (chartLift σ i (s y)) = w
      rw [hsx]
      exact (chartLift_of_chartSet hMH hxC).2
    · filter_upwards [hUo.mem_nhds hxU] with y' hy'
      have hsy' := hsU y' hy'
      have hC' := hsub J hJ hsy'.2
      refine ⟨?_, (chartLift_of_chartSet hMH hC').1, ?_⟩
      · have hd : DifferentiableAt ℂ s y' := hsd.differentiableAt (hUo.mem_nhds hy')
        refine differentiableAt_pi.2 fun p => ?_
        exact differentiableAt_pi.1 hd (σ.symm (Function.update i p.1 p.2))
      · rw [(chartLift_of_chartSet hMH hC').2]
        have hf := mem_setFibre_of_chart (Ψ := Ψ) hΨ0 hC'
        rw [hsy'.1] at hf
        obtain ⟨_, _, _, h⟩ := hf
        exact h
  have hex : ∃ γ, IsSetSheet (conePts Q) Ψ y w γ := ⟨_, hγ'⟩
  unfold setSheetDensity
  rw [dif_pos hex]
  set γ := hex.choose with hγ_def
  have hγ : IsSetSheet (conePts Q) Ψ y w γ := hex.choose_spec
  have hγan := sheet_analyticAt osgood (isSheet_bot_of_isSetSheet hγ)
  have hγ'an := sheet_analyticAt osgood (isSheet_bot_of_isSetSheet hγ')
  have hcseg : Continuous fun z : (Σ k, ι k) → ℂ => fun a : Fin m => segre z (σ a) := by
    refine continuous_pi fun a => ?_
    simp only [segre]
    exact continuous_finsetProd _ fun k _ => continuous_apply _
  have hxy0 : (fun a => segre (γ y) (σ a)) = x := by
    funext a
    rw [hγ.1]
    simp [hw]
  have ht : Tendsto (fun y' => fun a => segre (γ y') (σ a)) (𝓝 y) (𝓝 x) := by
    have h2 := (hcseg.continuousAt.comp hγan.continuousAt).tendsto
    simp only [Function.comp_def] at h2
    rwa [hxy0] at h2
  have hE4 : ∀ᶠ y' in 𝓝 y, ∀ J' ∈ chartComponents (conePts Q) σ i, J' ≠ J →
      (fun a => segre (γ y') (σ a)) ∉ zeroSet J' := by
    refine (eventually_all_finset _).2 fun J' hJ' => ?_
    by_cases hJJ : J' = J
    · exact Eventually.of_forall fun _ h => absurd hJJ h
    · exact Filter.Eventually.mono (p := fun y' => (fun a => segre (γ y') (σ a)) ∈ (zeroSet J')ᶜ)
        (ht ((isClosed_zeroSet J').isOpen_compl.mem_nhds (hsep J' hJ' hJJ))) fun _ h _ => h
  have hseg : (fun y' => segre (γ y')) =ᶠ[𝓝 y] fun y' => segre (chartLift σ i (s y')) := by
    filter_upwards [hγ.2, hUo.mem_nhds hxU, ht hV, hE4] with y' hy' hyU hxV h4
    obtain ⟨-, hmc, hΨy⟩ := hy'
    have hzi : segre (γ y') i = 1 := by
      have h := hΨ0 (segre (γ y'))
      rw [hΨy, Fin.cons_zero] at h
      exact h.symm
    have hC : (fun a => segre (γ y') (σ a)) ∈ chartSet (conePts Q) σ i := ⟨γ y', hmc, hzi, rfl⟩
    have hAx : chartProjMatrix σ Ψ *ᵥ (fun a => segre (γ y') (σ a)) = y' :=
      (chart_of_mem_setFibre (Ψ := Ψ) hΨ0 ⟨γ y', hmc, rfl, hΨy⟩).2
    obtain ⟨J', hJ', hxJ'⟩ := hcov _ hC
    have hJJ : J' = J := by
      by_contra h
      exact h4 J' hJ' h hxJ'
    have hxJ : (fun a => segre (γ y') (σ a)) ∈ zeroSet J := hJJ ▸ hxJ'
    have hxs : (fun a => segre (γ y') (σ a)) = s y' := by
      have h := hloc _ ⟨hxJ, hxV⟩ (by rw [hAx]; exact hyU)
      rwa [hAx] at h
    rw [← hxs]
    exact (segre_chartLift σ i (γ y') hzi).symm
  have hy0 : ∀ k, ∃ j, γ y ⟨k, j⟩ ≠ 0 := hγ.2.self_of_nhds.2.1.1
  have hde := density_eq hL (isSectionOn_ofWeight_one (P := (⊥ : Ideal (MRing ι))) Ideal.isPrime_bot g hg)
    hγan hγ'an hy0 hseg
  rw [logNorm_ofWeight_one, logNorm_ofWeight_one] at hde
  rw [hde, chartWeight_of_coord g hx1, hsx]
  rfl

/- English proof (translation)
Introduce `K _ _ ι _ Q e m σ i L g Ψ hQ hL hg hΨ0 hfinF hzero hdim hfinp`. Use `set A := chartProjMatrix σ Ψ with hAdef`. Use `set C := chartComponents (conePts Q) σ i with hCdef`. Establish `hMH : IsMultiHomogIdeal Q` using `hQ.2.1.2.1`. Establish `hmin : ∀ J ∈ C, J ∈ (GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartIdeal (conePts Q) σ i).minimalPrimes` using `fun J hJ => GlobalTheory.CompanionTheory.Ar.Pub.CxChart.mem_chartComponents.1 hJ`.

Establish `hprime : ∀ J ∈ C, J.IsPrime` using `fun J hJ => (hmin J hJ).1.1`. Establish `hsub : ∀ J ∈ C, zeroSet J ⊆ chartSet (conePts Q) σ i`. Introduce `J hJ x hx`. Rewrite using `[← hzero]`. Conclude with `fun q hq => hx q ((hmin J hJ).1.2 hq)`.

Establish `hcov : ∀ x ∈ chartSet (conePts Q) σ i, ∃ J ∈ C, x ∈ zeroSet J`. Introduce `x hx`. Rewrite `hx` using `[← hzero]`. Take `⟨J, hJ, hxJ⟩` from `exists_minimalPrime_of_mem_zeroSet hx`. Conclude with `⟨J, GlobalTheory.CompanionTheory.Ar.Pub.CxChart.mem_chartComponents.2 hJ, hxJ⟩`.

Establish `hG1 : ∀ᵐ y, ∀ J ∈ C, ∀ x ∈ GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y, ∃ s, IsSheetAt J A x s`. Use `(eventually_all_finset C).2 fun J hJ => ?_` and prove the remaining obligations. Take `⟨Q', U, D, N, s, -, hUD, -, -, hvol, hfib⟩` from `GroundTheory.Heights₂.Heights.DiscriminantSheetCover.proof GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.full m e J A (hprime J hJ) (hdim J hJ) (hfinp J hJ)`. Establish `hae : (⋃ k, D k) ∈ ae volume` using `mem_ae_iff.2 hvol`. Use `filter_upwards [hae] with y hy x hx`.

Take `⟨k, hk⟩` from `Set.mem_iUnion.1 hy`. Take `⟨hrange, -, hsheet⟩` from `hfib k y ((hUD k).2.2.1 hk)`. Rewrite `hx` using `[hrange]`. Take `⟨j, rfl⟩` from `hx`. Conclude with `⟨_, hsheet j⟩`.

Establish `hG2 : ∀ᵐ y, ∀ J ∈ C, ∀ J' ∈ C, J' ≠ J → ∀ x ∈ GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y, x ∉ zeroSet J'`. Use `(eventually_all_finset C).2 fun J hJ => (eventually_all_finset C).2 fun J' hJ' => ?_` and prove the remaining obligations. Distinguish the cases in `hJJ : J' = J`. Conclude with `Eventually.of_forall fun _ h => absurd hJJ h`. Establish `hnle : ¬ J' ≤ J` using `fun hle => hJJ (le_antisymm hle ((hmin J hJ).2 ⟨hprime J' hJ', (hmin J' hJ').1.2⟩ hle))`.

Take `⟨f, hfJ', hfJ⟩` from `SetLike.not_le_iff_exists.1 hnle`. Take `⟨q, hq, hqz⟩` from `exists_poly_of_not_mem (hprime J hJ) (hfinp J hJ) hfJ`. Establish `hae : {y : Fin e → ℂ | MvPolynomial.eval y q = 0}ᶜ ∈ ae volume` using `compl_mem_ae_iff.2 (GroundTheory.Heights₂.Heights.DiscriminantSheetCover.volume_zero_set q hq)`. Use `filter_upwards [hae] with y hy _ x hx hxJ'`. Conclude with `hy (by rw [← hx.2]; exact hqz x hx.1 (hxJ' f hfJ'))`.

Use `filter_upwards [hG1, hG2] with y hy1 hy2`. Use `set ψ : (Fin m → ℂ) → ((k : K) → ι k) → ℂ := fun x i' => x (σ.symm i') with hψ`. Use `set S := ⋃ J ∈ (C : Set (Ideal (MvPolynomial (Fin m) ℂ))), GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y with hS`. Establish `hψS : ∀ x ∈ S, ψ x ∈ setFibre (conePts Q) Ψ y`. Introduce `x hx`.

Take `⟨J, hJ, hxJ⟩` from `Set.mem_iUnion₂.1 hx`. Establish `h` using `mem_setFibre_of_chart (Ψ := Ψ) hΨ0 (hsub J hJ hxJ.1)`. Rewrite `h` using `[hxJ.2]`. Then use the resulting hypothesis. Establish `himg : ψ '' S = setFibre (conePts Q) Ψ y`. Use `Set.Subset.antisymm ?_ fun w hw => ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `hψS x hx`. Take `⟨hC, hAw⟩` from `chart_of_mem_setFibre hΨ0 hw`. Take `⟨J, hJ, hxJ⟩` from `hcov _ hC`. Conclude with `⟨_, Set.mem_iUnion₂.2 ⟨J, hJ, hxJ, hAw⟩, funext fun i' => by simp [hψ]⟩`.

Establish `hinj : Set.InjOn ψ S` using `fun x _ x' _ h => funext fun a => by`. Simplify `congrFun h (σ a)` using `[hψ]`. Establish `hfinJ : ∀ J ∈ (C : Set (Ideal (MvPolynomial (Fin m) ℂ))), (GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y).Finite`. Introduce `J hJ`. Use `((hfinF y).image fun w a => w (σ a)).subset fun x hx => ?_` and prove the remaining obligations.

Use `⟨ψ x, hψS x (Set.mem_iUnion₂.2 ⟨J, hJ, hx⟩), funext fun a => by simp [hψ]⟩` and prove the remaining obligations. Establish `hdisj : (C : Set (Ideal (MvPolynomial (Fin m) ℂ))).PairwiseDisjoint fun J => GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y` using `fun J hJ J' hJ' hne => Set.disjoint_left.2 fun x hx hx' => hy2 J hJ J' hJ' (Ne.symm hne) x hx hx'.1`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun J hJ => ?_` and prove the remaining obligations. Simplify using `only [chartDens, sheetSum]`.

Use `finsum_mem_congr rfl fun x hx => ?_` and prove the remaining obligations. Rewrite using `[dif_pos (hy1 J hJ x hx)]`. Conclude with `(term_eq hMH hL hg hΨ0 hsub hcov hJ hx (fun J' hJ' h => hy2 J hJ J' hJ' h x hx) (hy1 J hJ x hx)).symm`.
-/
theorem fibreSum : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (L : Fin e → HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsCxVar Q e → (∀ j, IsSmoothHerm (L j)) →
    (∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z p) = g z) →
    (∀ w, Ψ w 0 = w i) → (∀ y, (setFibre (conePts Q) Ψ y).Finite) →
    GroundTheory.Heights₂.Heights.ComplexSets.zeroSet (GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartIdeal (conePts Q) σ i) =
      chartSet (conePts Q) σ i →
    (∀ J ∈ chartComponents (conePts Q) σ i, ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ)) →
    (∀ J ∈ chartComponents (conePts Q) σ i,
      GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J (chartProjMatrix σ Ψ)) →
    ∀ᵐ y, ∑ᶠ w ∈ setFibre (conePts Q) Ψ y, setSheetDensity (conePts Q) Ψ (pot L) g y w =
      ∑ J ∈ chartComponents (conePts Q) σ i,
        chartDens J (chartProjMatrix σ Ψ) (chartWeight σ i g) (chartPot σ i L) y := by
  intro K _ _ ι _ Q e m σ i L g Ψ hQ hL hg hΨ0 hfinF hzero hdim hfinp
  classical
  set A := chartProjMatrix σ Ψ with hAdef
  set C := chartComponents (conePts Q) σ i with hCdef
  have hMH : IsMultiHomogIdeal Q := hQ.2.1.2.1
  have hmin : ∀ J ∈ C, J ∈ (GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartIdeal (conePts Q) σ i).minimalPrimes :=
    fun J hJ => GlobalTheory.CompanionTheory.Ar.Pub.CxChart.mem_chartComponents.1 hJ
  have hprime : ∀ J ∈ C, J.IsPrime := fun J hJ => (hmin J hJ).1.1
  have hsub : ∀ J ∈ C, zeroSet J ⊆ chartSet (conePts Q) σ i := by
    intro J hJ x hx
    rw [← hzero]
    exact fun q hq => hx q ((hmin J hJ).1.2 hq)
  have hcov : ∀ x ∈ chartSet (conePts Q) σ i, ∃ J ∈ C, x ∈ zeroSet J := by
    intro x hx
    rw [← hzero] at hx
    obtain ⟨J, hJ, hxJ⟩ := exists_minimalPrime_of_mem_zeroSet hx
    exact ⟨J, GlobalTheory.CompanionTheory.Ar.Pub.CxChart.mem_chartComponents.2 hJ, hxJ⟩

  have hG1 : ∀ᵐ y, ∀ J ∈ C, ∀ x ∈ GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y, ∃ s, IsSheetAt J A x s := by
    refine (eventually_all_finset C).2 fun J hJ => ?_
    obtain ⟨Q', U, D, N, s, -, hUD, -, -, hvol, hfib⟩ :=
      GroundTheory.Heights₂.Heights.DiscriminantSheetCover.proof GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.full
        m e J A (hprime J hJ) (hdim J hJ) (hfinp J hJ)
    have hae : (⋃ k, D k) ∈ ae volume := mem_ae_iff.2 hvol
    filter_upwards [hae] with y hy x hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hy
    obtain ⟨hrange, -, hsheet⟩ := hfib k y ((hUD k).2.2.1 hk)
    rw [hrange] at hx
    obtain ⟨j, rfl⟩ := hx
    exact ⟨_, hsheet j⟩

  have hG2 : ∀ᵐ y, ∀ J ∈ C, ∀ J' ∈ C, J' ≠ J →
      ∀ x ∈ GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y, x ∉ zeroSet J' := by
    refine (eventually_all_finset C).2 fun J hJ => (eventually_all_finset C).2 fun J' hJ' => ?_
    by_cases hJJ : J' = J
    · exact Eventually.of_forall fun _ h => absurd hJJ h
    have hnle : ¬ J' ≤ J := fun hle =>
      hJJ (le_antisymm hle ((hmin J hJ).2 ⟨hprime J' hJ', (hmin J' hJ').1.2⟩ hle))
    obtain ⟨f, hfJ', hfJ⟩ := SetLike.not_le_iff_exists.1 hnle
    obtain ⟨q, hq, hqz⟩ := exists_poly_of_not_mem (hprime J hJ) (hfinp J hJ) hfJ
    have hae : {y : Fin e → ℂ | MvPolynomial.eval y q = 0}ᶜ ∈ ae volume :=
      compl_mem_ae_iff.2 (GroundTheory.Heights₂.Heights.DiscriminantSheetCover.volume_zero_set q hq)
    filter_upwards [hae] with y hy _ x hx hxJ'
    exact hy (by rw [← hx.2]; exact hqz x hx.1 (hxJ' f hfJ'))
  filter_upwards [hG1, hG2] with y hy1 hy2
  set ψ : (Fin m → ℂ) → ((k : K) → ι k) → ℂ := fun x i' => x (σ.symm i') with hψ
  set S := ⋃ J ∈ (C : Set (Ideal (MvPolynomial (Fin m) ℂ))),
    GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y with hS
  have hψS : ∀ x ∈ S, ψ x ∈ setFibre (conePts Q) Ψ y := by
    intro x hx
    obtain ⟨J, hJ, hxJ⟩ := Set.mem_iUnion₂.1 hx
    have h := mem_setFibre_of_chart (Ψ := Ψ) hΨ0 (hsub J hJ hxJ.1)
    rwa [hxJ.2] at h
  have himg : ψ '' S = setFibre (conePts Q) Ψ y := by
    refine Set.Subset.antisymm ?_ fun w hw => ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hψS x hx
    · obtain ⟨hC, hAw⟩ := chart_of_mem_setFibre hΨ0 hw
      obtain ⟨J, hJ, hxJ⟩ := hcov _ hC
      exact ⟨_, Set.mem_iUnion₂.2 ⟨J, hJ, hxJ, hAw⟩, funext fun i' => by simp [hψ]⟩
  have hinj : Set.InjOn ψ S := fun x _ x' _ h => funext fun a => by
    simpa [hψ] using congrFun h (σ a)
  have hfinJ : ∀ J ∈ (C : Set (Ideal (MvPolynomial (Fin m) ℂ))),
      (GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y).Finite := by
    intro J hJ
    refine ((hfinF y).image fun w a => w (σ a)).subset fun x hx => ?_
    refine ⟨ψ x, hψS x (Set.mem_iUnion₂.2 ⟨J, hJ, hx⟩), funext fun a => by simp [hψ]⟩
  have hdisj : (C : Set (Ideal (MvPolynomial (Fin m) ℂ))).PairwiseDisjoint
      fun J => GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y :=
    fun J hJ J' hJ' hne => Set.disjoint_left.2 fun x hx hx' => hy2 J hJ J' hJ' (Ne.symm hne) x hx hx'.1
  calc ∑ᶠ w ∈ setFibre (conePts Q) Ψ y, setSheetDensity (conePts Q) Ψ (pot L) g y w
      = ∑ᶠ w ∈ ψ '' S, setSheetDensity (conePts Q) Ψ (pot L) g y w := by rw [himg]
    _ = ∑ᶠ x ∈ S, setSheetDensity (conePts Q) Ψ (pot L) g y (ψ x) := finsum_mem_image hinj
    _ = ∑ᶠ J ∈ (C : Set (Ideal (MvPolynomial (Fin m) ℂ))),
          ∑ᶠ x ∈ GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y,
            setSheetDensity (conePts Q) Ψ (pot L) g y (ψ x) :=
        finsum_mem_biUnion hdisj C.finite_toSet hfinJ
    _ = ∑ J ∈ C, ∑ᶠ x ∈ GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y,
          setSheetDensity (conePts Q) Ψ (pot L) g y (ψ x) :=
        finsum_mem_coe_finset _ _
    _ = ∑ J ∈ C, chartDens J A (chartWeight σ i g) (chartPot σ i L) y := by
        refine Finset.sum_congr rfl fun J hJ => ?_
        simp only [chartDens, sheetSum]
        refine finsum_mem_congr rfl fun x hx => ?_
        rw [dif_pos (hy1 J hJ x hx)]
        exact (term_eq hMH hL hg hΨ0 hsub hcov hJ hx (fun J' hJ' h => hy2 J hJ J' hJ' h x hx)
          (hy1 J hJ x hx)).symm

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart.FibSum
