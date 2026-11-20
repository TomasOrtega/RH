import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StNbarLeviChartReg
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PNbarLeviChartReg
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PRefChartDisc
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PProjHoloLocal
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PProjSmoothAlong
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHermExtend
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHoloInjDerivInj
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PChartVelLift
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInjectiveHolomorphicInverse
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalOrbitChart

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
  GroundTheory.Heights₂.Heights.NineStatements Filter Topology
open ReciprocityTheory.AnForm (levi levi_comp levi_add_smul levi_re_analytic levi_congr)
open ReciprocityTheory.AnForm.M (IsCompatChart)

/- English proof (translation)
The claim follows from `ProjHoloLocal.proof localOrbitChart (IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicInverse.proof (IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicJacobianNeZero.proof IndefiniteRowSideFullHecke.ComplexSets.HolomorphicKernelFibre.proof IndefiniteRowSideFull …`.
-/
theorem projHoloLocal : ProjHoloLocal.Statement :=
  ProjHoloLocal.proof localOrbitChart
    (IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicInverse.proof
      (IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicJacobianNeZero.proof
        IndefiniteRowSideFullHecke.ComplexSets.HolomorphicKernelFibre.proof IndefiniteRowSideFullHecke.ComplexSets.CriticalFlatNotInjective.proof))

/- English proof (translation)
Introduce `II Ψ _ K _ ι _ Ω _ _ E _ _ D M e he γ hγ hmem h0`. Take `⟨W, hWo, hzW, F, hFd, hF⟩` from `projHoloLocal II Ψ K ι Ω E D M e he (γ 0) hmem.self_of_nhds h0`. Establish `hW : ∀ᶠ s in 𝓝 (0 : ℂ), γ s ∈ W` using `hγ.continuousAt.preimage_mem_nhds (hWo.mem_nhds hzW)`. Take `⟨S, hS, hSp⟩` from `(hγ.eventually_analyticAt.and hW).exists_mem`. Establish `hFa : AnalyticAt ℂ (fun s => F (γ s)) 0` using `DifferentiableOn.analyticAt (fun t ht => ((hFd.differentiableAt (hWo.mem_nhds (hSp t ht).2)).comp t (hSp t ht).1.differentiableAt).differentiableWithinAt) hS`.

Use `hFa.congr ?_` and prove the remaining obligations. Use `filter_upwards [hW, hmem] with s h1 h2`. Conclude with `(hF (γ s) ⟨h1, h2⟩).2.symm`.
-/
theorem projChartHolo : ProjChartHolo.Statement := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ D M e he γ hγ hmem h0
  obtain ⟨W, hWo, hzW, F, hFd, hF⟩ := projHoloLocal II Ψ K ι Ω E D M e he (γ 0) hmem.self_of_nhds h0
  have hW : ∀ᶠ s in 𝓝 (0 : ℂ), γ s ∈ W := hγ.continuousAt.preimage_mem_nhds (hWo.mem_nhds hzW)
  obtain ⟨S, hS, hSp⟩ := (hγ.eventually_analyticAt.and hW).exists_mem
  have hFa : AnalyticAt ℂ (fun s => F (γ s)) 0 :=
    DifferentiableOn.analyticAt (fun t ht =>
      ((hFd.differentiableAt (hWo.mem_nhds (hSp t ht).2)).comp t
        (hSp t ht).1.differentiableAt).differentiableWithinAt) hS
  refine hFa.congr ?_
  filter_upwards [hW, hmem] with s h1 h2
  exact (hF (γ s) ⟨h1, h2⟩).2.symm

def tanIdeal {σ : Type} [Fintype σ] (w v : σ → ℂ) : Ideal (MvPolynomial σ ℂ) where
  carrier := {h | eval w h = 0 ∧ ∑ i, eval w (pderiv i h) * v i = 0}
  add_mem' := by
    rintro a b ⟨ha0, ha1⟩ ⟨hb0, hb1⟩
    refine ⟨by simp [ha0, hb0], ?_⟩
    simp only [map_add, add_mul, Finset.sum_add_distrib, ha1, hb1, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    rintro g h ⟨h0, h1⟩
    refine ⟨by simp [h0], ?_⟩
    have hd : ∀ i, eval w (pderiv i (g * h)) = eval w g * eval w (pderiv i h) := by
      intro i
      simp [Derivation.leibniz, h0]
    simp only [smul_eq_mul, hd, mul_assoc, ← Finset.mul_sum, h1, mul_zero]

/- English proof (translation)
Set `B : (σ → ℂ) →ₗ[ℂ] Module.Dual ℂ (σ → ℂ)` to `LinearMap.mk₂ ℂ (fun v g => ∑ q, g q * v q) (fun a b g => by simp [mul_add, Finset.sum_add_distrib]) (fun c a g => by simp [Finset.mul_sum, mul_left_comm]) (fun a g g' => by simp [add_mul, Finset.sum_add_distrib]) (fun c a g => by simp [Finset.mul_sum, mul_assoc])`. Establish `hB : Function.Injective B`. Use `(injective_iff_map_eq_zero B).2 fun v hv => ?_` and prove the remaining obligations. Use function extensionality and compare the values at `q`. Use `LinearMap.congr_fun hv (Pi.single q 1)` as an intermediate fact.

Simplify `this` using `[B, Pi.single_apply]`. Establish `hinj : Function.Injective (B ∘ₗ f)` using `hB.comp hf`. Establish `hr : LinearMap.range (B ∘ₗ f) ≤ J.dualAnnihilator`. Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[Submodule.mem_dualAnnihilator]`.

Introduce `g hg`. Conclude with `h g hg x`. Establish `h1 : Module.finrank ℂ N = Module.finrank ℂ (LinearMap.range (B ∘ₗ f))` using `(LinearMap.finrank_range_of_inj hinj).symm`. Establish `h2` using `Submodule.finrank_mono hr`. Establish `h3` using `Subspace.finrank_add_finrank_dualAnnihilator_eq J`.

Simplify using `only [Module.finrank_fintype_fun_eq_card] at h3`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_add_le_of_perp {σ : Type} [Fintype σ] {N : Type} [AddCommGroup N] [Module ℂ N]
    [FiniteDimensional ℂ N] (J : Submodule ℂ (σ → ℂ)) (f : N →ₗ[ℂ] (σ → ℂ)) (hf : Function.Injective f)
    (h : ∀ g ∈ J, ∀ x, ∑ q, g q * f x q = 0) :
    Module.finrank ℂ N + Module.finrank ℂ J ≤ Fintype.card σ := by
  classical
  let B : (σ → ℂ) →ₗ[ℂ] Module.Dual ℂ (σ → ℂ) := LinearMap.mk₂ ℂ (fun v g => ∑ q, g q * v q)
    (fun a b g => by simp [mul_add, Finset.sum_add_distrib])
    (fun c a g => by simp [Finset.mul_sum, mul_left_comm])
    (fun a g g' => by simp [add_mul, Finset.sum_add_distrib])
    (fun c a g => by simp [Finset.mul_sum, mul_assoc])
  have hB : Function.Injective B := by
    refine (injective_iff_map_eq_zero B).2 fun v hv => ?_
    funext q
    have := LinearMap.congr_fun hv (Pi.single q 1)
    simpa [B, Pi.single_apply] using this
  have hinj : Function.Injective (B ∘ₗ f) := hB.comp hf
  have hr : LinearMap.range (B ∘ₗ f) ≤ J.dualAnnihilator := by
    rintro _ ⟨x, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro g hg
    exact h g hg x
  have h1 : Module.finrank ℂ N = Module.finrank ℂ (LinearMap.range (B ∘ₗ f)) :=
    (LinearMap.finrank_range_of_inj hinj).symm
  have h2 := Submodule.finrank_mono hr
  have h3 := Subspace.finrank_add_finrank_dualAnnihilator_eq J
  simp only [Module.finrank_fintype_fun_eq_card] at h3
  omega

/- English proof (translation)
Establish `hℓd : HasDerivAt (fun s : ℂ => z + s • v) v 0`. Establish `h` using `((hasDerivAt_id (0 : ℂ)).smul_const v).const_add z`. Simplify using `using h`. Establish `hℓ' : HasDerivAt (fun s : ℂ => fun q : (Σ k, ι k) => c q.1 * (z + s • v) q) (fun q => c q.1 * v q) 0` using `hasDerivAt_pi.2 fun q => (hasDerivAt_pi.1 hℓd q).const_mul (c q.1)`. Establish `h1` using `hasDerivAt_eval_comp f hℓ'`.

Establish `h2` using `(hasDerivAt_eval_comp f hℓd).const_mul (∏ k, c k ^ a k)`. Establish `heq : (fun s : ℂ => eval (fun q : (Σ k, ι k) => c q.1 * (z + s • v) q) f) = fun s => (∏ k, c k ^ a k) * eval (z + s • v) f`. Use function extensionality and compare the values at `s`. Conclude with `ReciprocityTheory.AnForm.R.eval_smul_of_isMultiHomog ha c (z + s • v)`. Rewrite `h1` using `[heq]`.

Establish `h3` using `h1.unique h2`. Simplify using `using h3`.
-/
theorem sum_pderiv_smul_of_multiHomog {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ} (ha : ReciprocityTheory.AnForm.R.IsMultiHomog f a) (c : K → ℂ)
    (z v : (Σ k, ι k) → ℂ) :
    ∑ i, eval (fun q : (Σ k, ι k) => c q.1 * z q) (pderiv i f) * (c i.1 * v i) =
      (∏ k, c k ^ a k) * ∑ i, eval z (pderiv i f) * v i := by
  have hℓd : HasDerivAt (fun s : ℂ => z + s • v) v 0 := by
    have h := ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add z
    simpa using h
  have hℓ' : HasDerivAt (fun s : ℂ => fun q : (Σ k, ι k) => c q.1 * (z + s • v) q)
      (fun q => c q.1 * v q) 0 :=
    hasDerivAt_pi.2 fun q => (hasDerivAt_pi.1 hℓd q).const_mul (c q.1)
  have h1 := hasDerivAt_eval_comp f hℓ'
  have h2 := (hasDerivAt_eval_comp f hℓd).const_mul (∏ k, c k ^ a k)
  have heq : (fun s : ℂ => eval (fun q : (Σ k, ι k) => c q.1 * (z + s • v) q) f) =
      fun s => (∏ k, c k ^ a k) * eval (z + s • v) f := by
    funext s
    exact ReciprocityTheory.AnForm.R.eval_smul_of_isMultiHomog ha c (z + s • v)
  rw [heq] at h1
  have h3 := h1.unique h2
  simpa using h3

/- English proof (translation)
Establish `: CharZero Ω` using `algebraRat.charZero Ω`. Take `rfl : inst = DivisionRing.toRatAlgebra` from `Subsingleton.elim _ _`. Establish `hPh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC (mCoordIdeal y))` using `isMultiHomogIdeal_pC hP.2.1.2.1`. Take `⟨p, hp, -⟩` from `ReciprocityTheory.AnForm.R.exists_chart z hz.1`. Establish `hy : ∀ k, y ⟨k, p k⟩ ≠ 0`.

Introduce `k h0`. Establish `hX : (X ⟨k, p k⟩ : MRing ι) ∈ mCoordIdeal y`. Rewrite using `[mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0]`. Simplify using the standard rewrite rules. Establish `h1` using `hz.2 _ hX`.

Rewrite `h1` using `[map_X, eval_X]`. Conclude with `hp k h1`. Use `set w := ReciprocityTheory.AnForm.R.affCoord p z with hwdef`. Use `set c : K → ℂ := fun k => (z ⟨k, p k⟩)⁻¹ with hcdef`. Establish `hc : ∀ k, c k ≠ 0` using `fun k => inv_ne_zero (hp k)`.

Establish `hwc : w = fun q => c q.1 * z q`. Use function extensionality and compare the values at `q`. Simplify using `[hwdef, hcdef, ReciprocityTheory.AnForm.R.affCoord, div_eq_inv_mul]`. Establish `hzero : ∀ h ∈ ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) p, eval w h = 0` using `(ReciprocityTheory.AnForm.R.mem_conePts_iff_chartIdeal hPh p z hp).1 ((mem_mcPts_iff_conePts_pC _ _).1 hz)`. Establish `hrank` using `GlobalTheory.CompanionTheory.Ar.PB.SmoothMan.card_le_finrank_jacSpanAt K ι Ω y n hP hsm p hy w hzero`.

Set `Dc : ((Σ k, ι k) → ℂ) →ₗ[ℂ] ((Σ k, ι k) → ℂ)` to `LinearMap.pi fun q => c q.1 • LinearMap.proj q`. Establish `hDc : ∀ v q, Dc v q = c q.1 * v q` using `fun v q => by simp [Dc]`. Establish `hDinj : Function.Injective Dc`. Use `(injective_iff_map_eq_zero Dc).2 fun v hv => ?_` and prove the remaining obligations. Use function extensionality and compare the values at `q`.

Use `congrFun hv q` as an intermediate fact. Rewrite `this` using `[hDc]`. Simplify `this` using `[hc q.1]`. Establish `hstep : ∀ v ∈ T, pC (mCoordIdeal y) ≤ tanIdeal w (Dc v)`. Introduce `v hv`.

Establish `hz1 : pC (mCoordIdeal y) ≤ tanIdeal z v`. Rewrite using `[pC, Ideal.span_le]`. Introduce and unpack `_ ⟨g, hg, rfl⟩`. Conclude with `⟨hz.2 g hg, hT v hv g hg⟩`. Take `⟨S, hS, hPS⟩` from `hPh`.

Establish `hsub : S ⊆ (pC (mCoordIdeal y) : Set _)`. Rewrite using `[hPS]`. Conclude with `Ideal.subset_span`. Rewrite using `[hPS, Ideal.span_le]`. Introduce `f hfS`.

Take `⟨a, ha⟩` from `hS f hfS`. Establish `hfP` using `hsub hfS`. Use `⟨hzero f (Ideal.mem_sup_left hfP), ?_⟩` and prove the remaining obligations. Establish `h3` using `sum_pderiv_smul_of_multiHomog ha c z v`. Rewrite `h3` using `[(hz1 hfP).2, mul_zero, ← hwc]`.

Simplify `h3` using `only [hDc]`. Establish `hchart : ∀ v ∈ T, (∀ k, v ⟨k, p k⟩ = 0) → ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) p ≤ tanIdeal w (Dc v)`. Introduce `v hv hv0`. Use `sup_le (hstep v hv) ?_` and prove the remaining obligations. Rewrite using `[Ideal.span_le]`.

Introduce and unpack `_ ⟨k, rfl⟩`. Use `⟨hzero _ (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)), ?_⟩` and prove the remaining obligations. Establish `hd : ∀ i, eval w (pderiv i (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ)) = if i = ⟨k, p k⟩ then 1 else 0`. Introduce `i`. Distinguish the cases in `hi : i = ⟨k, p k⟩`.

Substitute `hi` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg hi]`. Simplify using `[pderiv_X_of_ne (Ne.symm hi)]`. Simplify using `only [hd, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.

Rewrite using `[hDc, hv0 k, mul_zero]`. Set `Ψ : T →ₗ[ℂ] (K → ℂ)` to `(LinearMap.pi fun k => LinearMap.proj ⟨k, p k⟩) ∘ₗ T.subtype`. Establish `hΨ : ∀ (v : T) k, Ψ v k = (v : (Σ k, ι k) → ℂ) ⟨k, p k⟩` using `fun v k => rfl`. Establish `hker : Module.finrank ℂ (LinearMap.ker Ψ) + Module.finrank ℂ (ReciprocityTheory.AnForm.R.jacSpanAt (ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) p) w) ≤ Fintype.card (Σ k, ι k)`. Use `finrank_add_le_of_perp (N := ↥(LinearMap.ker Ψ)) _ (Dc ∘ₗ T.subtype ∘ₗ (LinearMap.ker Ψ).subtype) ?_ ?_` and prove the remaining obligations.

Conclude with `hDinj.comp (T.injective_subtype.comp (Submodule.injective_subtype _))`. Introduce `g hg x`. Establish `hxT : ((x : T) : (Σ k, ι k) → ℂ) ∈ T` using `(x : T).2`. Establish `hx0 : ∀ k, ((x : T) : (Σ k, ι k) → ℂ) ⟨k, p k⟩ = 0` using `fun k => by`. Use `congrFun (LinearMap.mem_ker.1 x.2) k` as an intermediate fact.

Simplify `this` using `[hΨ]`. Establish `hle` using `hchart _ hxT hx0`. Use `set u := Dc ((x : T) : (Σ k, ι k) → ℂ) with hu`. Set `ev : ((Σ k, ι k) → ℂ) →ₗ[ℂ] ℂ` to `{ toFun := fun g => ∑ q, g q * u q map_add' := fun a b => by simp [add_mul, Finset.sum_add_distrib] map_smul' := fun a b => by simp [Finset.mul_sum, mul_assoc] }`. Establish `hJ : ReciprocityTheory.AnForm.R.jacSpanAt (ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) p) w ≤ LinearMap.ker ev`.

Rewrite using `[ReciprocityTheory.AnForm.R.jacSpanAt, Submodule.span_le]`. Introduce and unpack `_ ⟨h, hh, rfl⟩`. Conclude with `(hle hh).2`. Conclude with `hJ hg`. Establish `hrn` using `LinearMap.finrank_range_add_finrank_ker Ψ`.

Establish `hrg : Module.finrank ℂ (LinearMap.range Ψ) ≤ Fintype.card K`. Use `Submodule.finrank_le (LinearMap.range Ψ)` as an intermediate fact. Simplify using `using this`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_coneTangent_le (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [inst : Algebra ℚ Ω] (y : (Σ k, ι k) → Ω) (n : ℕ) (hP : IsArithVar (mCoordIdeal y) (n + 1))
    (hsm : SmoothGenericFibreM y) (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts (mCoordIdeal y))
    (T : Submodule ℂ ((Σ k, ι k) → ℂ))
    (hT : ∀ v ∈ T, IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal y) z v) :
    Module.finrank ℂ T ≤ n + Fintype.card K := by
  classical
  have : CharZero Ω := algebraRat.charZero Ω
  obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  have hPh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC (mCoordIdeal y)) :=
    isMultiHomogIdeal_pC hP.2.1.2.1
  obtain ⟨p, hp, -⟩ := ReciprocityTheory.AnForm.R.exists_chart z hz.1
  have hy : ∀ k, y ⟨k, p k⟩ ≠ 0 := by
    intro k h0
    have hX : (X ⟨k, p k⟩ : MRing ι) ∈ mCoordIdeal y := by
      rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0]
      simp
    have h1 := hz.2 _ hX
    rw [map_X, eval_X] at h1
    exact hp k h1
  set w := ReciprocityTheory.AnForm.R.affCoord p z with hwdef
  set c : K → ℂ := fun k => (z ⟨k, p k⟩)⁻¹ with hcdef
  have hc : ∀ k, c k ≠ 0 := fun k => inv_ne_zero (hp k)
  have hwc : w = fun q => c q.1 * z q := by
    funext q
    simp [hwdef, hcdef, ReciprocityTheory.AnForm.R.affCoord, div_eq_inv_mul]
  have hzero : ∀ h ∈ ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) p, eval w h = 0 :=
    (ReciprocityTheory.AnForm.R.mem_conePts_iff_chartIdeal hPh p z hp).1 ((mem_mcPts_iff_conePts_pC _ _).1 hz)
  have hrank := GlobalTheory.CompanionTheory.Ar.PB.SmoothMan.card_le_finrank_jacSpanAt K ι Ω y n hP hsm p hy w hzero

  let Dc : ((Σ k, ι k) → ℂ) →ₗ[ℂ] ((Σ k, ι k) → ℂ) :=
    LinearMap.pi fun q => c q.1 • LinearMap.proj q
  have hDc : ∀ v q, Dc v q = c q.1 * v q := fun v q => by simp [Dc]
  have hDinj : Function.Injective Dc := by
    refine (injective_iff_map_eq_zero Dc).2 fun v hv => ?_
    funext q
    have := congrFun hv q
    rw [hDc] at this
    simpa [hc q.1] using this

  have hstep : ∀ v ∈ T, pC (mCoordIdeal y) ≤ tanIdeal w (Dc v) := by
    intro v hv
    have hz1 : pC (mCoordIdeal y) ≤ tanIdeal z v := by
      rw [pC, Ideal.span_le]
      rintro _ ⟨g, hg, rfl⟩
      exact ⟨hz.2 g hg, hT v hv g hg⟩
    obtain ⟨S, hS, hPS⟩ := hPh
    have hsub : S ⊆ (pC (mCoordIdeal y) : Set _) := by
      rw [hPS]
      exact Ideal.subset_span
    rw [hPS, Ideal.span_le]
    intro f hfS
    obtain ⟨a, ha⟩ := hS f hfS
    have hfP := hsub hfS
    refine ⟨hzero f (Ideal.mem_sup_left hfP), ?_⟩
    have h3 := sum_pderiv_smul_of_multiHomog ha c z v
    rw [(hz1 hfP).2, mul_zero, ← hwc] at h3
    simpa only [hDc] using h3
  have hchart : ∀ v ∈ T, (∀ k, v ⟨k, p k⟩ = 0) →
      ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) p ≤ tanIdeal w (Dc v) := by
    intro v hv hv0
    refine sup_le (hstep v hv) ?_
    rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    refine ⟨hzero _ (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)), ?_⟩
    have hd : ∀ i, eval w (pderiv i (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ)) =
        if i = ⟨k, p k⟩ then 1 else 0 := by
      intro i
      by_cases hi : i = ⟨k, p k⟩
      · subst hi
        simp
      · rw [if_neg hi]
        simp [pderiv_X_of_ne (Ne.symm hi)]
    simp only [hd, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hDc, hv0 k, mul_zero]

  let Ψ : T →ₗ[ℂ] (K → ℂ) := (LinearMap.pi fun k => LinearMap.proj ⟨k, p k⟩) ∘ₗ T.subtype
  have hΨ : ∀ (v : T) k, Ψ v k = (v : (Σ k, ι k) → ℂ) ⟨k, p k⟩ := fun v k => rfl
  have hker : Module.finrank ℂ (LinearMap.ker Ψ) +
      Module.finrank ℂ (ReciprocityTheory.AnForm.R.jacSpanAt
        (ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) p) w) ≤ Fintype.card (Σ k, ι k) := by
    refine finrank_add_le_of_perp (N := ↥(LinearMap.ker Ψ)) _
      (Dc ∘ₗ T.subtype ∘ₗ (LinearMap.ker Ψ).subtype) ?_ ?_
    · exact hDinj.comp (T.injective_subtype.comp (Submodule.injective_subtype _))
    · intro g hg x
      have hxT : ((x : T) : (Σ k, ι k) → ℂ) ∈ T := (x : T).2
      have hx0 : ∀ k, ((x : T) : (Σ k, ι k) → ℂ) ⟨k, p k⟩ = 0 := fun k => by
        have := congrFun (LinearMap.mem_ker.1 x.2) k
        simpa [hΨ] using this
      have hle := hchart _ hxT hx0
      set u := Dc ((x : T) : (Σ k, ι k) → ℂ) with hu
      let ev : ((Σ k, ι k) → ℂ) →ₗ[ℂ] ℂ :=
        { toFun := fun g => ∑ q, g q * u q
          map_add' := fun a b => by simp [add_mul, Finset.sum_add_distrib]
          map_smul' := fun a b => by simp [Finset.mul_sum, mul_assoc] }
      have hJ : ReciprocityTheory.AnForm.R.jacSpanAt
          (ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) p) w ≤ LinearMap.ker ev := by
        rw [ReciprocityTheory.AnForm.R.jacSpanAt, Submodule.span_le]
        rintro _ ⟨h, hh, rfl⟩
        exact (hle hh).2
      exact hJ hg
  have hrn := LinearMap.finrank_range_add_finrank_ker Ψ
  have hrg : Module.finrank ℂ (LinearMap.range Ψ) ≤ Fintype.card K := by
    have := Submodule.finrank_le (LinearMap.range Ψ)
    simpa using this
  omega

def coneTan {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (z : (Σ k, ι k) → ℂ) : Submodule ℂ ((Σ k, ι k) → ℂ) where
  carrier := {v | IsConeTangent (Int.castRingHom ℂ) P z v}
  add_mem' := by
    intro a b ha hb f hf
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, ha f hf, hb f hf, add_zero]
  zero_mem' := by
    intro f _
    simp
  smul_mem' := by
    intro c a ha f hf
    have h := ha f hf
    simp only [Pi.smul_apply, smul_eq_mul]
    calc ∑ i, eval z (pderiv i (map (Int.castRingHom ℂ) f)) * (c * a i)
        = c * ∑ i, eval z (pderiv i (map (Int.castRingHom ℂ) f)) * a i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = 0 := by rw [h, mul_zero]

/- English proof (translation)
Establish `hMH : IsMultiHomogIdeal (mCoordIdeal D.y)` using `D.arith.2.1.2.1`. Take `⟨W, hWo, hzW, F, hFd, hF⟩` from `projHoloLocal II Ψ K ι Ω E D M e he z hz hze`. Take `⟨U, hUo, hxU, σ, hσ, hσh⟩` from `M.sections (M.proj z)`. Use `set W₀ : Set (Fin D.n → ℂ) := e.target ∩ e.symm ⁻¹' U with hW₀def`. Use `set g : (Fin D.n → ℂ) → (Σ k, ι k) → ℂ := fun u => σ (e.symm u) with hgdef`.

Establish `hW₀o : IsOpen W₀` using `e.isOpen_inter_preimage_symm hUo`. Establish `hg : AnalyticOnNhd ℂ g W₀`. Introduce `u hu`. Use `analyticAt_pi_iff.2 fun p => ?_` and prove the remaining obligations. Take `⟨j, hj⟩` from `M.atlas.cover (e.symm u)`.

Establish `h1 : AnalyticAt ℂ (M.atlas.chart j ∘ e.symm) u` using `(he j).2 u ⟨hu.1, hj⟩`. Establish `h2 : AnalyticAt ℂ ((fun y => σ y p) ∘ (M.atlas.chart j).symm) (M.atlas.chart j (e.symm u))` using `hσh p j _ ⟨(M.atlas.chart j).map_source hj, by`. Simplify using `only [Set.mem_preimage, (M.atlas.chart j).left_inv hj]`. Conclude with `hu.2⟩`. Use `(AnalyticAt.comp (g := (fun y => σ y p) ∘ (M.atlas.chart j).symm) (f := M.atlas.chart j ∘ e.symm) h2 h1).congr ?_` and prove the remaining obligations.

Use `filter_upwards [(e.continuousAt_symm hu.1).preimage_mem_nhds ((M.atlas.chart j).open_source.mem_nhds hj)] with u' hu'`. Simplify using `only [Function.comp, (M.atlas.chart j).left_inv hu']`. Establish `hgmem : ∀ u ∈ W₀, g u ∈ mcPts (mCoordIdeal D.y) ∧ M.proj (g u) = e.symm u` using `fun u hu => hσ _ hu.2`. Use `set u₀ : Fin D.n → ℂ := e (M.proj z) with hu₀def`. Establish `hsym : e.symm u₀ = M.proj z` using `e.left_inv hze`.

Establish `hu₀ : u₀ ∈ W₀` using `⟨e.map_source hze, by simp only [Set.mem_preimage, hsym]; exact hxU⟩`. Take `⟨c₀, hc₀, hzc⟩` from `(M.fibre _ (hgmem u₀ hu₀).1 _ hz).1 (by rw [(hgmem u₀ hu₀).2, hsym])`. Use `set T : Set (K → ℂ) := {c | ∀ k, c k ≠ 0} with hTdef`. Establish `hTo : IsOpen T`. Establish `: T = ⋂ k, (fun c : K → ℂ => c k) ⁻¹' {0}ᶜ` using `by ext c; simp [hTdef]`.

Rewrite using `[this]`. Conclude with `isOpen_iInter_of_finite fun k => isOpen_compl_singleton.preimage (continuous_apply k)`. Use `set Φ : (Fin D.n → ℂ) × (K → ℂ) → (Σ k, ι k) → ℂ := fun q => torusSmul q.2 (g q.1) with hΦdef`. Establish `hΦ : AnalyticOnNhd ℂ Φ (W₀ ×ˢ T)`. Introduce `q hq`.

Use `analyticAt_pi_iff.2 fun p => ?_` and prove the remaining obligations. Establish `ha : AnalyticAt ℂ (fun q : (Fin D.n → ℂ) × (K → ℂ) => q.2 p.1) q` using `((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) p.1).analyticAt _).comp analyticAt_snd`. Establish `hb : AnalyticAt ℂ (fun q : (Fin D.n → ℂ) × (K → ℂ) => g q.1 p) q` using `(analyticAt_pi_iff.1 (hg q.1 hq.1) p).comp analyticAt_fst`. Conclude with `ha.mul hb`. Use `set q₀ : (Fin D.n → ℂ) × (K → ℂ) := (u₀, c₀) with hq₀def`.

Establish `hq₀ : q₀ ∈ W₀ ×ˢ T` using `⟨hu₀, hc₀⟩`. Establish `hΦ₀ : Φ q₀ = z` using `hzc.symm`. Establish `hΦmem : ∀ q ∈ W₀ ×ˢ T, Φ q ∈ mcPts (mCoordIdeal D.y)` using `fun q hq => mcPts_smul hMH q.2 hq.2 (hgmem q.1 hq.1).1`. Establish `hΦproj : ∀ q ∈ W₀ ×ˢ T, M.proj (Φ q) = e.symm q.1` using `fun q hq => (((M.fibre _ (hgmem q.1 hq.1).1 _ (hΦmem q hq)).2 ⟨q.2, hq.2, rfl⟩).symm).trans (hgmem q.1 hq.1).2`. Use `set L := fderiv ℂ Φ q₀ with hLdef`.

Establish `hL : HasFDerivAt Φ L q₀` using `(hΦ q₀ hq₀).differentiableAt.hasFDerivAt`. Establish `hline : ∀ a : (Fin D.n → ℂ) × (K → ℂ), HasDerivAt (fun s : ℂ => q₀ + s • a) a 0` using `fun a => by`. Simplify using `using ((hasDerivAt_id (0 : ℂ)).smul_const a).const_add q₀`. Establish `hδ : ∀ a, HasDerivAt (fun s : ℂ => Φ (q₀ + s • a)) (L a) 0` using `fun a => hL.comp_hasDerivAt_of_eq (0 : ℂ) (hline a) (by simp)`. Establish `hev : ∀ a : (Fin D.n → ℂ) × (K → ℂ), ∀ᶠ s in 𝓝 (0 : ℂ), q₀ + s • a ∈ W₀ ×ˢ T` using `fun a => by`.

Establish `h` using `(hline a).continuousAt.preimage_mem_nhds ((hW₀o.prod hTo).mem_nhds (by simpa using hq₀))`. Conclude with `h`. Establish `hval : ∀ a : (Fin D.n → ℂ) × (K → ℂ), Φ (q₀ + (0 : ℂ) • a) = z` using `fun a => by simp [hΦ₀]`. Establish `htan : ∀ a, L a ∈ coneTan (mCoordIdeal D.y) z`. Introduce `a f hf`.

Establish `hder` using `hasDerivAt_eval_comp (map (Int.castRingHom ℂ) f) (hδ a)`. Rewrite `hder` using `[hval a]`. Establish `hzero : (fun s : ℂ => eval (Φ (q₀ + s • a)) (map (Int.castRingHom ℂ) f)) =ᶠ[𝓝 0] fun _ => (0 : ℂ)` using `by filter_upwards [hev a] with s hs`. Conclude with `(hΦmem _ hs).2 f hf`. Conclude with `hder.unique ((hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq hzero)`.

Establish `hFz : HasFDerivAt F (fderiv ℂ F z) z` using `(hFd.differentiableAt (hWo.mem_nhds hzW)).hasFDerivAt`. Establish `hFL : ∀ a, fderiv ℂ F z (L a) = a.1`. Introduce `a`. Establish `hWδ : ∀ᶠ s in 𝓝 (0 : ℂ), Φ (q₀ + s • a) ∈ W` using `(hδ a).continuousAt.preimage_mem_nhds (hWo.mem_nhds (by simpa [hΦ₀] using hzW))`. Establish `h1 : HasDerivAt (fun s : ℂ => F (Φ (q₀ + s • a))) (fderiv ℂ F z (L a)) 0` using `hFz.comp_hasDerivAt_of_eq (0 : ℂ) (hδ a) (hval a).symm`.

Establish `h2 : HasDerivAt (fun s : ℂ => (q₀ + s • a).1) a.1 0` using `(ContinuousLinearMap.fst ℂ (Fin D.n → ℂ) (K → ℂ)).hasFDerivAt.comp_hasDerivAt (0 : ℂ) (hline a)`. Use `h1.unique (h2.congr_of_eventuallyEq ?_)` and prove the remaining obligations. Use `filter_upwards [hev a, hWδ] with s hs hsW`. Rewrite using `[← (hF _ ⟨hsW, hΦmem _ hs⟩).2, hΦproj _ hs]`. Conclude with `e.right_inv hs.1.1`.

Establish `hLb : ∀ b : K → ℂ, L (0, b) = torusSmul b (g u₀)`. Introduce `b`. Establish `h1` using `hδ (0, b)`. Establish `h2 : HasDerivAt (fun s : ℂ => Φ (q₀ + s • ((0 : Fin D.n → ℂ), b))) (torusSmul b (g u₀)) 0`. Use `hasDerivAt_pi.2 fun p => ?_` and prove the remaining obligations.

Establish `h` using `(((hasDerivAt_id (0 : ℂ)).mul_const (b p.1)).const_add (c₀ p.1)).mul_const (g u₀ p)`. Simplify `h` using `[hΦdef, hq₀def, torusSmul]`. Conclude with `h1.unique h2`. Establish `hinj : Function.Injective L`. Use `(injective_iff_map_eq_zero L).2 fun a ha => ?_` and prove the remaining obligations.

Establish `h1 : a.1 = 0` using `by rw [← hFL a, ha, map_zero]`. Take `⟨a1, b⟩` from `a`. Take `rfl : a1 = 0` from `h1`. Establish `h2` using `hLb b`. Rewrite `h2` using `[ha]`.

Use `Prod.ext rfl (funext fun k => ?_)` and prove the remaining obligations. Take `⟨i, hi⟩` from `(hgmem u₀ hu₀).1.1 k`. Establish `h3` using `congrFun h2 ⟨k, i⟩`. Simplify `h3.symm` using `[torusSmul, hi]`. Set `Ll : ((Fin D.n → ℂ) × (K → ℂ)) →ₗ[ℂ] ((Σ k, ι k) → ℂ)` to `L.toLinearMap`.

Establish `hle : LinearMap.range Ll ≤ coneTan (mCoordIdeal D.y) z`. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `htan a`. Establish `hdim : Module.finrank ℂ (coneTan (mCoordIdeal D.y) z) ≤ Module.finrank ℂ (LinearMap.range Ll)`. Rewrite using `[LinearMap.finrank_range_of_inj (show Function.Injective Ll from hinj)]`.

Use `finrank_coneTangent_le K ι Ω D.y D.n D.arith D.smoothGeneric z hz (coneTan (mCoordIdeal D.y) z) (fun v hv => hv)` as an intermediate fact. Simplify `this` using `[Module.finrank_prod]`. Establish `heq` using `Submodule.eq_of_le_of_finrank_le hle hdim`. Establish `hwT : w ∈ coneTan (mCoordIdeal D.y) z` using `hw`. Rewrite `hwT` using `[← heq]`.

Take `⟨a, rfl⟩` from `hwT`. Use `⟨fun s => Φ (q₀ + s • a), hval a, hδ a, ?_, ?_⟩` and prove the remaining obligations. Establish `hl : AnalyticAt ℂ (fun s : ℂ => q₀ + s • a) 0` using `analyticAt_const.add (analyticAt_id.smul analyticAt_const)`. Conclude with `(hΦ _ (by simpa using hq₀)).comp_of_eq hl (by simp)`. Use `filter_upwards [hev a] with s hs`.

Conclude with `hΦmem _ hs`.
-/
theorem coneTangent_disc {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (M : XModel D)
    (e : OpenPartialHomeomorph M.Xc (Fin D.n → ℂ)) (he : IsCompatChart M.atlas e)
    (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts (mCoordIdeal D.y)) (hze : M.proj z ∈ e.source)
    (w : (Σ k, ι k) → ℂ) (hw : IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal D.y) z w) :
    ∃ γ : ℂ → (Σ k, ι k) → ℂ, γ 0 = z ∧ HasDerivAt γ w 0 ∧ AnalyticAt ℂ γ 0 ∧
      ∀ᶠ s in 𝓝 (0 : ℂ), γ s ∈ mcPts (mCoordIdeal D.y) := by
  classical
  have hMH : IsMultiHomogIdeal (mCoordIdeal D.y) := D.arith.2.1.2.1
  obtain ⟨W, hWo, hzW, F, hFd, hF⟩ := projHoloLocal II Ψ K ι Ω E D M e he z hz hze
  obtain ⟨U, hUo, hxU, σ, hσ, hσh⟩ := M.sections (M.proj z)

  set W₀ : Set (Fin D.n → ℂ) := e.target ∩ e.symm ⁻¹' U with hW₀def
  set g : (Fin D.n → ℂ) → (Σ k, ι k) → ℂ := fun u => σ (e.symm u) with hgdef
  have hW₀o : IsOpen W₀ := e.isOpen_inter_preimage_symm hUo
  have hg : AnalyticOnNhd ℂ g W₀ := by
    intro u hu
    refine analyticAt_pi_iff.2 fun p => ?_
    obtain ⟨j, hj⟩ := M.atlas.cover (e.symm u)
    have h1 : AnalyticAt ℂ (M.atlas.chart j ∘ e.symm) u := (he j).2 u ⟨hu.1, hj⟩
    have h2 : AnalyticAt ℂ ((fun y => σ y p) ∘ (M.atlas.chart j).symm) (M.atlas.chart j (e.symm u)) :=
      hσh p j _ ⟨(M.atlas.chart j).map_source hj, by
        simp only [Set.mem_preimage, (M.atlas.chart j).left_inv hj]; exact hu.2⟩
    refine (AnalyticAt.comp (g := (fun y => σ y p) ∘ (M.atlas.chart j).symm)
      (f := M.atlas.chart j ∘ e.symm) h2 h1).congr ?_
    filter_upwards [(e.continuousAt_symm hu.1).preimage_mem_nhds
      ((M.atlas.chart j).open_source.mem_nhds hj)] with u' hu'
    simp only [Function.comp, (M.atlas.chart j).left_inv hu']
  have hgmem : ∀ u ∈ W₀, g u ∈ mcPts (mCoordIdeal D.y) ∧ M.proj (g u) = e.symm u := fun u hu => hσ _ hu.2
  set u₀ : Fin D.n → ℂ := e (M.proj z) with hu₀def
  have hsym : e.symm u₀ = M.proj z := e.left_inv hze
  have hu₀ : u₀ ∈ W₀ := ⟨e.map_source hze, by simp only [Set.mem_preimage, hsym]; exact hxU⟩
  obtain ⟨c₀, hc₀, hzc⟩ := (M.fibre _ (hgmem u₀ hu₀).1 _ hz).1 (by rw [(hgmem u₀ hu₀).2, hsym])

  set T : Set (K → ℂ) := {c | ∀ k, c k ≠ 0} with hTdef
  have hTo : IsOpen T := by
    have : T = ⋂ k, (fun c : K → ℂ => c k) ⁻¹' {0}ᶜ := by ext c; simp [hTdef]
    rw [this]
    exact isOpen_iInter_of_finite fun k => isOpen_compl_singleton.preimage (continuous_apply k)
  set Φ : (Fin D.n → ℂ) × (K → ℂ) → (Σ k, ι k) → ℂ := fun q => torusSmul q.2 (g q.1) with hΦdef
  have hΦ : AnalyticOnNhd ℂ Φ (W₀ ×ˢ T) := by
    intro q hq
    refine analyticAt_pi_iff.2 fun p => ?_
    have ha : AnalyticAt ℂ (fun q : (Fin D.n → ℂ) × (K → ℂ) => q.2 p.1) q :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) p.1).analyticAt _).comp analyticAt_snd
    have hb : AnalyticAt ℂ (fun q : (Fin D.n → ℂ) × (K → ℂ) => g q.1 p) q :=
      (analyticAt_pi_iff.1 (hg q.1 hq.1) p).comp analyticAt_fst
    exact ha.mul hb
  set q₀ : (Fin D.n → ℂ) × (K → ℂ) := (u₀, c₀) with hq₀def
  have hq₀ : q₀ ∈ W₀ ×ˢ T := ⟨hu₀, hc₀⟩
  have hΦ₀ : Φ q₀ = z := hzc.symm
  have hΦmem : ∀ q ∈ W₀ ×ˢ T, Φ q ∈ mcPts (mCoordIdeal D.y) := fun q hq =>
    mcPts_smul hMH q.2 hq.2 (hgmem q.1 hq.1).1
  have hΦproj : ∀ q ∈ W₀ ×ˢ T, M.proj (Φ q) = e.symm q.1 := fun q hq =>
    (((M.fibre _ (hgmem q.1 hq.1).1 _ (hΦmem q hq)).2 ⟨q.2, hq.2, rfl⟩).symm).trans (hgmem q.1 hq.1).2
  set L := fderiv ℂ Φ q₀ with hLdef
  have hL : HasFDerivAt Φ L q₀ := (hΦ q₀ hq₀).differentiableAt.hasFDerivAt

  have hline : ∀ a : (Fin D.n → ℂ) × (K → ℂ), HasDerivAt (fun s : ℂ => q₀ + s • a) a 0 := fun a => by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const a).const_add q₀
  have hδ : ∀ a, HasDerivAt (fun s : ℂ => Φ (q₀ + s • a)) (L a) 0 := fun a =>
    hL.comp_hasDerivAt_of_eq (0 : ℂ) (hline a) (by simp)
  have hev : ∀ a : (Fin D.n → ℂ) × (K → ℂ), ∀ᶠ s in 𝓝 (0 : ℂ), q₀ + s • a ∈ W₀ ×ˢ T := fun a => by
    have h := (hline a).continuousAt.preimage_mem_nhds
      ((hW₀o.prod hTo).mem_nhds (by simpa using hq₀))
    exact h
  have hval : ∀ a : (Fin D.n → ℂ) × (K → ℂ), Φ (q₀ + (0 : ℂ) • a) = z := fun a => by simp [hΦ₀]

  have htan : ∀ a, L a ∈ coneTan (mCoordIdeal D.y) z := by
    intro a f hf
    have hder := hasDerivAt_eval_comp (map (Int.castRingHom ℂ) f) (hδ a)
    rw [hval a] at hder
    have hzero : (fun s : ℂ => eval (Φ (q₀ + s • a)) (map (Int.castRingHom ℂ) f)) =ᶠ[𝓝 0]
        fun _ => (0 : ℂ) := by
      filter_upwards [hev a] with s hs
      exact (hΦmem _ hs).2 f hf
    exact hder.unique ((hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq hzero)

  have hFz : HasFDerivAt F (fderiv ℂ F z) z := (hFd.differentiableAt (hWo.mem_nhds hzW)).hasFDerivAt
  have hFL : ∀ a, fderiv ℂ F z (L a) = a.1 := by
    intro a
    have hWδ : ∀ᶠ s in 𝓝 (0 : ℂ), Φ (q₀ + s • a) ∈ W :=
      (hδ a).continuousAt.preimage_mem_nhds (hWo.mem_nhds (by simpa [hΦ₀] using hzW))
    have h1 : HasDerivAt (fun s : ℂ => F (Φ (q₀ + s • a))) (fderiv ℂ F z (L a)) 0 :=
      hFz.comp_hasDerivAt_of_eq (0 : ℂ) (hδ a) (hval a).symm
    have h2 : HasDerivAt (fun s : ℂ => (q₀ + s • a).1) a.1 0 :=
      (ContinuousLinearMap.fst ℂ (Fin D.n → ℂ) (K → ℂ)).hasFDerivAt.comp_hasDerivAt (0 : ℂ) (hline a)
    refine h1.unique (h2.congr_of_eventuallyEq ?_)
    filter_upwards [hev a, hWδ] with s hs hsW
    rw [← (hF _ ⟨hsW, hΦmem _ hs⟩).2, hΦproj _ hs]
    exact e.right_inv hs.1.1
  have hLb : ∀ b : K → ℂ, L (0, b) = torusSmul b (g u₀) := by
    intro b
    have h1 := hδ (0, b)
    have h2 : HasDerivAt (fun s : ℂ => Φ (q₀ + s • ((0 : Fin D.n → ℂ), b))) (torusSmul b (g u₀)) 0 := by
      refine hasDerivAt_pi.2 fun p => ?_
      have h := (((hasDerivAt_id (0 : ℂ)).mul_const (b p.1)).const_add (c₀ p.1)).mul_const (g u₀ p)
      simpa [hΦdef, hq₀def, torusSmul] using h
    exact h1.unique h2
  have hinj : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).2 fun a ha => ?_
    have h1 : a.1 = 0 := by rw [← hFL a, ha, map_zero]
    obtain ⟨a1, b⟩ := a
    obtain rfl : a1 = 0 := h1
    have h2 := hLb b
    rw [ha] at h2
    refine Prod.ext rfl (funext fun k => ?_)
    obtain ⟨i, hi⟩ := (hgmem u₀ hu₀).1.1 k
    have h3 := congrFun h2 ⟨k, i⟩
    simpa [torusSmul, hi] using h3.symm

  let Ll : ((Fin D.n → ℂ) × (K → ℂ)) →ₗ[ℂ] ((Σ k, ι k) → ℂ) := L.toLinearMap
  have hle : LinearMap.range Ll ≤ coneTan (mCoordIdeal D.y) z := by
    rintro _ ⟨a, rfl⟩
    exact htan a
  have hdim : Module.finrank ℂ (coneTan (mCoordIdeal D.y) z) ≤
      Module.finrank ℂ (LinearMap.range Ll) := by
    rw [LinearMap.finrank_range_of_inj (show Function.Injective Ll from hinj)]
    have := finrank_coneTangent_le K ι Ω D.y D.n D.arith D.smoothGeneric z hz
      (coneTan (mCoordIdeal D.y) z) (fun v hv => hv)
    simpa [Module.finrank_prod] using this
  have heq := Submodule.eq_of_le_of_finrank_le hle hdim
  have hwT : w ∈ coneTan (mCoordIdeal D.y) z := hw
  rw [← heq] at hwT
  obtain ⟨a, rfl⟩ := hwT
  refine ⟨fun s => Φ (q₀ + s • a), hval a, hδ a, ?_, ?_⟩
  · have hl : AnalyticAt ℂ (fun s : ℂ => q₀ + s • a) 0 :=
      analyticAt_const.add (analyticAt_id.smul analyticAt_const)
    exact (hΦ _ (by simpa using hq₀)).comp_of_eq hl (by simp)
  · filter_upwards [hev a] with s hs
    exact hΦmem _ hs

open NbarLeviChartReg in

/- English proof (translation)
Establish `hProj : ProjChartHolo.Statement` using `projChartHolo`. Establish `hRef : RefChartDisc.Statement` using `RefChartDisc.proof hProj`. Establish `hE : HermExtend.Statement` using `HermExtend.proof`. Establish `hP : ProjSmoothAlong.Statement` using `ProjSmoothAlong.proof HoloInjDerivInj.proof localOrbitChart`. Introduce `II Ψ _ _ K _ ι _ Ω _ _ E _ _ D H M S _ B p q t hsm z hz w hw k hk`.

Establish `hsrc0 : M.proj z ∈ (S.R.chart k).source` using `S.R.mid_subset_source k hk`. Take `⟨γ, hγ0, hγd, hγa, hγm⟩` from `coneTangent_disc D M (S.R.chart k) (S.R.compat k) z hz hsrc0 w hw`. Substitute `hγ0` using the available equality. Establish `hsrc : M.proj (γ 0) ∈ (S.R.chart k).source` using `hsrc0`. Establish `hχ` using `hProj II Ψ K ι Ω E D M (S.R.chart k) (S.R.compat k) γ hγa hγm hsrc`.

Take `⟨G, hGa, hGe⟩` from `hRef II Ψ K ι Ω E D H M S k γ hγa hγm hsrc`. Use `⟨deriv (fun s => S.R.chart k (M.proj (γ s))) 0, ⟨γ, rfl, hγd, ?_, hχ.differentiableAt.hasDerivAt⟩, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hγa.eventually_analyticAt, hγm] with s hs1 hs2`. Conclude with `⟨hs1.differentiableAt, hs2⟩`. Take `⟨hNs, hNe⟩` from `regNbarQ_smooth_eq hE hP D H M S B p q t hsm`.

Establish `hSB : ∀ p' ∈ D.SB B, p' ∈ D.S` using `fun p' hp' => (Finset.mem_filter.1 hp').1`. Establish `hex : ∀ p' ∈ D.SB B, ∃ T : ((Σ k, ι k) → ℂ) → ℂ, AnalyticAt ℂ T (γ 0) ∧ T (γ 0) ≠ 0 ∧ ∀ᶠ y in 𝓝 (γ 0), y ∈ mcPts (mCoordIdeal D.y) → D.vertFactor p' y = ‖T y‖` using `fun p' hp' => vertFactor_local D (hSB p' hp') hz`. Use `choose! T hTa hT0 hTe using hex`. Establish `hTta : AnalyticAt ℂ (fun y => ∏ p' ∈ D.SB B, T p' y) (γ 0)` using `(D.SB B).analyticAt_fun_prod hTa`. Establish `hTt0 : (∏ p' ∈ D.SB B, T p' (γ 0)) ≠ 0` using `Finset.prod_ne_zero_iff.2 hT0`.

Establish `hΓa : AnalyticAt ℂ (fun u : Fin 1 → ℂ => γ (u 0)) 0` using `analyticAt_disc hγa`. Establish `hΓd : fderiv ℂ (fun u : Fin 1 → ℂ => γ (u 0)) 0 (fun _ => 1) = w` using `fderiv_disc hγd`. Establish `hχ1 : AnalyticAt ℂ (fun u : Fin 1 → ℂ => S.R.chart k (M.proj (γ (u 0)))) 0` using `analyticAt_disc hχ`. Establish `hχd : fderiv ℂ (fun u : Fin 1 → ℂ => S.R.chart k (M.proj (γ (u 0)))) 0 (fun _ => 1) = deriv (fun s => S.R.chart k (M.proj (γ s))) 0` using `fderiv_disc hχ.differentiableAt.hasDerivAt`. Establish `hG1 : AnalyticAt ℂ (fun u : Fin 1 → ℂ => G (u 0)) 0` using `analyticAt_disc hGa`.

Establish `hO : {y : (Σ k, ι k) → ℂ | ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0} ∈ 𝓝 (γ 0)` using `MuRegSmooth.isOpen_blocks.mem_nhds hz.1`. Establish `hlogN : ContDiffAt ℝ 2 (fun y => Real.log ((regNbarQ H M S B p q t).h y)) (γ 0)` using `((hNs.contDiffAt hO).of_le (WithTop.coe_le_coe.2 le_top)).log ((regNbarQ H M S B p q t).pos _ hz.1).ne'`. Establish `hlogA : ContDiffAt ℝ 2 (fun y => Real.log (D.A'.h y)) (γ 0)` using `((D.A'_pos.1.contDiffAt hO).of_le (WithTop.coe_le_coe.2 le_top)).log (D.A'.pos _ hz.1).ne'`. Establish `hx0 : S.R.chart k (M.proj (γ 0)) ∈ (S.R.chart k).target` using `(S.R.chart k).map_source hsrc`. Establish `hcf : ContDiffAt ℝ 2 (S.R.chartFun (S.regWeight t) k) (S.R.chart k (M.proj (γ 0)))`.

Establish `hq : ContDiffAt ℝ 2 (S.R.q k) (S.R.chart k (M.proj (γ 0)))` using `((S.R.q_smooth k).contDiffAt ((S.R.chart k).open_target.mem_nhds hx0)).of_le (WithTop.coe_le_coe.2 le_top)`. Establish `hφ : ContDiffAt ℝ 2 (S.regWeight t ∘ (S.R.chart k).symm) (S.R.chart k (M.proj (γ 0)))` using `((ReciprocityTheory.AnForm.M.PLAux.contDiffOn_compat (S.R.compat k) isOpen_univ hsm).contDiffAt (by simpa using (S.R.chart k).open_target.mem_nhds hx0)).of_le (WithTop.coe_le_coe.2 le_top)`. Conclude with `hq.add hφ`. Establish `hγz : Tendsto γ (𝓝 0) (𝓝 (γ 0))` using `hγa.continuousAt.tendsto`. Establish `hcont : Tendsto (fun s => M.proj (γ s)) (𝓝 0) (𝓝 (M.proj (γ 0)))` using `(M.cont (γ 0) hz).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hγz, hγm⟩)`.

Establish `hsrcE : ∀ᶠ s in 𝓝 (0 : ℂ), M.proj (γ s) ∈ (S.R.chart k).source` using `hcont ((S.R.chart k).open_source.mem_nhds hsrc)`. Establish `hTE : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ p' ∈ D.SB B, γ s ∈ mcPts (mCoordIdeal D.y) → D.vertFactor p' (γ s) = ‖T p' (γ s)‖` using `hγz.eventually ((Filter.eventually_all_finset _).2 hTe)`. Establish `hE0 : ∀ᶠ s in 𝓝 (0 : ℂ), Real.log ((regNbarQ H M S B p q t).h (γ s)) = (q : ℝ) * (S.R.chartFun (S.regWeight t) k (S.R.chart k (M.proj (γ s))) + (-1) * (G s).re) + (q : ℝ) * Real.log ‖∏ p' ∈ D.SB B, T p' (γ s)‖ + (p : ℝ) * Real.log (D.A'.h (γ s))` using `by filter_upwards [hγm, hGe, hsrcE, hTE] with s hsm' hsG hss hsT`. Establish `hvf : ∏ p' ∈ D.SB B, D.vertFactor p' (γ s) = ‖∏ p' ∈ D.SB B, T p' (γ s)‖`. Rewrite using `[norm_prod]`.

Conclude with `Finset.prod_congr rfl fun p' hp' => hsT p' hp' hsm'`. Establish `hv0 : 0 < ∏ p' ∈ D.SB B, D.vertFactor p' (γ s)` using `Finset.prod_pos fun p' hp' => VertFactorPos.proof II Ψ K ι Ω E D p' (hSB p' hp') _ hsm'`. Establish `href` using `S.ref.pos _ hsm'.1`. Establish `hA` using `D.A'.pos _ hsm'.1`. Establish `hX : (S.ref.h (γ s) * Real.exp (S.regWeight t (M.proj (γ s)))) ^ q ≠ 0` using `(pow_pos (mul_pos href (Real.exp_pos _)) q).ne'`.

Establish `hY : (∏ p' ∈ D.SB B, D.vertFactor p' (γ s)) ^ q ≠ 0` using `(pow_pos hv0 q).ne'`. Establish `hZ : D.A'.h (γ s) ^ p ≠ 0` using `(pow_pos hA p).ne'`. Rewrite using `[hNe _ hsm', Real.log_mul (mul_ne_zero hX hY) hZ, Real.log_mul hX hY, Real.log_pow, Real.log_pow, Real.log_pow, Real.log_mul href.ne' (Real.exp_pos _).ne', Real.log_exp, hvf, hsG]`. Simplify using `only [Regular.PotentialCharts.chartFun, (S.R.chart k).left_inv hss]`. Expand and normalize the polynomial expressions, which then agree.

Use `set A1 : (Fin 1 → ℂ) → ℝ := fun u => S.R.chartFun (S.regWeight t) k (S.R.chart k (M.proj (γ (u 0)))) with hA1def`. Use `set R1 : (Fin 1 → ℂ) → ℝ := fun u => (G (u 0)).re with hR1def`. Use `set L2 : (Fin 1 → ℂ) → ℝ := fun u => Real.log ‖∏ p' ∈ D.SB B, T p' (γ (u 0))‖ with hL2def`. Use `set L3 : (Fin 1 → ℂ) → ℝ := fun u => Real.log (D.A'.h (γ (u 0))) with hL3def`. Establish `hEv : (fun y => Real.log ((regNbarQ H M S B p q t).h y)) ∘ (fun u : Fin 1 → ℂ => γ (u 0)) =ᶠ[𝓝 0] fun u => (q : ℝ) * (A1 u + (-1) * R1 u) + (q : ℝ) * L2 u + (p : ℝ) * L3 u`.

Establish `ht : Tendsto (fun u : Fin 1 → ℂ => u 0) (𝓝 0) (𝓝 0)`. Simplify using `using (continuous_apply (0 : Fin 1)).tendsto (0 : Fin 1 → ℂ)`. Conclude with `ht.eventually hE0`. Establish `hlevL : levi (fun y => Real.log ((regNbarQ H M S B p q t).h y)) (γ 0) w = levi ((fun y => Real.log ((regNbarQ H M S B p q t).h y)) ∘ (fun u : Fin 1 → ℂ => γ (u 0))) 0 (fun _ => 1)`. Establish `h` using `levi_comp (fun _ => (1 : ℂ)) hΓa hlogN`.

Rewrite `h` using `[hΓd]`. Conclude with `h.symm`. Establish `hA1c : ContDiffAt ℝ 2 A1 0` using `hcf.comp (0 : Fin 1 → ℂ) (hχ1.restrictScalars.contDiffAt (n := 2))`. Establish `hA1l : levi A1 0 (fun _ => 1) = levi (S.R.chartFun (S.regWeight t) k) (S.R.chart k (M.proj (γ 0))) (deriv (fun s => S.R.chart k (M.proj (γ s))) 0)`. Establish `h` using `levi_comp (φ := S.R.chartFun (S.regWeight t) k) (fun _ => (1 : ℂ)) hχ1 hcf`.

Rewrite `h` using `[hχd]`. Conclude with `h`. Establish `hR1c : ContDiffAt ℝ 2 R1 0`. Establish `h` using `(Complex.reCLM.contDiff (n := 2)).contDiffAt.comp (0 : Fin 1 → ℂ) (hG1.restrictScalars.contDiffAt (n := 2))`. Use `h using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `u`. Simplify using `[hR1def]`. Establish `hR1l : levi R1 0 (fun _ => 1) = 0` using `levi_re_analytic hG1 _`. Establish `hL2` using `Inter.RegularizedCurvature.log_norm_pluriharmonic (T := fun u : Fin 1 → ℂ => ∏ p' ∈ D.SB B, T p' (γ (u 0))) (hTta.comp_of_eq hΓa rfl) hTt0 (fun _ => 1)`. Establish `hL2c : ContDiffAt ℝ 2 L2 0` using `hL2.1`.

Establish `hL2l : levi L2 0 (fun _ => 1) = 0` using `hL2.2`. Establish `hL3c : ContDiffAt ℝ 2 L3 0` using `hlogA.comp (0 : Fin 1 → ℂ) (hΓa.restrictScalars.contDiffAt (n := 2))`. Establish `hL3l : levi L3 0 (fun _ => 1) = levi (fun y => Real.log (D.A'.h y)) (γ 0) w`. Establish `h` using `levi_comp (fun _ => (1 : ℂ)) hΓa hlogA`. Rewrite `h` using `[hΓd]`.

Conclude with `h`. Establish `hf1 : ContDiffAt ℝ 2 (fun u => A1 u + (-1) * R1 u) 0` using `hA1c.add (contDiffAt_const.mul hR1c)`. Establish `hq1 : ContDiffAt ℝ 2 (fun u => (q : ℝ) * (A1 u + (-1) * R1 u)) 0` using `contDiffAt_const.mul hf1`. Establish `hq12 : ContDiffAt ℝ 2 (fun u => (q : ℝ) * (A1 u + (-1) * R1 u) + (q : ℝ) * L2 u) 0` using `hq1.add (contDiffAt_const.mul hL2c)`. Rewrite using `[hlevL, levi_congr hEv, levi_add_smul (p : ℝ) hq12 hL3c, levi_add_smul (q : ℝ) hq1 hL2c, levi_const_mul (q : ℝ) hf1, levi_add_smul (-1) hA1c hR1c, hA1l, hR1l, hL2l, hL3l]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem nbarLeviChartReg : NbarLeviChartReg.Statement := by
  have hProj : ProjChartHolo.Statement := projChartHolo
  have hRef : RefChartDisc.Statement := RefChartDisc.proof hProj
  have hE : HermExtend.Statement := HermExtend.proof
  have hP : ProjSmoothAlong.Statement := ProjSmoothAlong.proof HoloInjDerivInj.proof localOrbitChart
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D H M S _ B p q t hsm z hz w hw k hk
  have hsrc0 : M.proj z ∈ (S.R.chart k).source := S.R.mid_subset_source k hk
  obtain ⟨γ, hγ0, hγd, hγa, hγm⟩ := coneTangent_disc D M (S.R.chart k) (S.R.compat k) z hz hsrc0 w hw
  subst hγ0
  have hsrc : M.proj (γ 0) ∈ (S.R.chart k).source := hsrc0
  have hχ := hProj II Ψ K ι Ω E D M (S.R.chart k) (S.R.compat k) γ hγa hγm hsrc
  obtain ⟨G, hGa, hGe⟩ := hRef II Ψ K ι Ω E D H M S k γ hγa hγm hsrc
  refine ⟨deriv (fun s => S.R.chart k (M.proj (γ s))) 0,
    ⟨γ, rfl, hγd, ?_, hχ.differentiableAt.hasDerivAt⟩, ?_⟩
  · filter_upwards [hγa.eventually_analyticAt, hγm] with s hs1 hs2
    exact ⟨hs1.differentiableAt, hs2⟩
  obtain ⟨hNs, hNe⟩ := regNbarQ_smooth_eq hE hP D H M S B p q t hsm
  have hSB : ∀ p' ∈ D.SB B, p' ∈ D.S := fun p' hp' => (Finset.mem_filter.1 hp').1
  have hex : ∀ p' ∈ D.SB B, ∃ T : ((Σ k, ι k) → ℂ) → ℂ, AnalyticAt ℂ T (γ 0) ∧ T (γ 0) ≠ 0 ∧
      ∀ᶠ y in 𝓝 (γ 0), y ∈ mcPts (mCoordIdeal D.y) → D.vertFactor p' y = ‖T y‖ :=
    fun p' hp' => vertFactor_local D (hSB p' hp') hz
  choose! T hTa hT0 hTe using hex
  have hTta : AnalyticAt ℂ (fun y => ∏ p' ∈ D.SB B, T p' y) (γ 0) := (D.SB B).analyticAt_fun_prod hTa
  have hTt0 : (∏ p' ∈ D.SB B, T p' (γ 0)) ≠ 0 := Finset.prod_ne_zero_iff.2 hT0
  have hΓa : AnalyticAt ℂ (fun u : Fin 1 → ℂ => γ (u 0)) 0 := analyticAt_disc hγa
  have hΓd : fderiv ℂ (fun u : Fin 1 → ℂ => γ (u 0)) 0 (fun _ => 1) = w := fderiv_disc hγd
  have hχ1 : AnalyticAt ℂ (fun u : Fin 1 → ℂ => S.R.chart k (M.proj (γ (u 0)))) 0 := analyticAt_disc hχ
  have hχd : fderiv ℂ (fun u : Fin 1 → ℂ => S.R.chart k (M.proj (γ (u 0)))) 0 (fun _ => 1) =
      deriv (fun s => S.R.chart k (M.proj (γ s))) 0 := fderiv_disc hχ.differentiableAt.hasDerivAt
  have hG1 : AnalyticAt ℂ (fun u : Fin 1 → ℂ => G (u 0)) 0 := analyticAt_disc hGa
  have hO : {y : (Σ k, ι k) → ℂ | ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0} ∈ 𝓝 (γ 0) := MuRegSmooth.isOpen_blocks.mem_nhds hz.1
  have hlogN : ContDiffAt ℝ 2 (fun y => Real.log ((regNbarQ H M S B p q t).h y)) (γ 0) :=
    ((hNs.contDiffAt hO).of_le (WithTop.coe_le_coe.2 le_top)).log ((regNbarQ H M S B p q t).pos _ hz.1).ne'
  have hlogA : ContDiffAt ℝ 2 (fun y => Real.log (D.A'.h y)) (γ 0) :=
    ((D.A'_pos.1.contDiffAt hO).of_le (WithTop.coe_le_coe.2 le_top)).log (D.A'.pos _ hz.1).ne'
  have hx0 : S.R.chart k (M.proj (γ 0)) ∈ (S.R.chart k).target := (S.R.chart k).map_source hsrc
  have hcf : ContDiffAt ℝ 2 (S.R.chartFun (S.regWeight t) k) (S.R.chart k (M.proj (γ 0))) := by
    have hq : ContDiffAt ℝ 2 (S.R.q k) (S.R.chart k (M.proj (γ 0))) :=
      ((S.R.q_smooth k).contDiffAt ((S.R.chart k).open_target.mem_nhds hx0)).of_le (WithTop.coe_le_coe.2 le_top)
    have hφ : ContDiffAt ℝ 2 (S.regWeight t ∘ (S.R.chart k).symm) (S.R.chart k (M.proj (γ 0))) :=
      ((ReciprocityTheory.AnForm.M.PLAux.contDiffOn_compat (S.R.compat k) isOpen_univ hsm).contDiffAt
        (by simpa using (S.R.chart k).open_target.mem_nhds hx0)).of_le (WithTop.coe_le_coe.2 le_top)
    exact hq.add hφ

  have hγz : Tendsto γ (𝓝 0) (𝓝 (γ 0)) := hγa.continuousAt.tendsto
  have hcont : Tendsto (fun s => M.proj (γ s)) (𝓝 0) (𝓝 (M.proj (γ 0))) :=
    (M.cont (γ 0) hz).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hγz, hγm⟩)
  have hsrcE : ∀ᶠ s in 𝓝 (0 : ℂ), M.proj (γ s) ∈ (S.R.chart k).source :=
    hcont ((S.R.chart k).open_source.mem_nhds hsrc)
  have hTE : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ p' ∈ D.SB B, γ s ∈ mcPts (mCoordIdeal D.y) →
      D.vertFactor p' (γ s) = ‖T p' (γ s)‖ :=
    hγz.eventually ((Filter.eventually_all_finset _).2 hTe)
  have hE0 : ∀ᶠ s in 𝓝 (0 : ℂ), Real.log ((regNbarQ H M S B p q t).h (γ s)) =
      (q : ℝ) * (S.R.chartFun (S.regWeight t) k (S.R.chart k (M.proj (γ s))) + (-1) * (G s).re) +
        (q : ℝ) * Real.log ‖∏ p' ∈ D.SB B, T p' (γ s)‖ + (p : ℝ) * Real.log (D.A'.h (γ s)) := by
    filter_upwards [hγm, hGe, hsrcE, hTE] with s hsm' hsG hss hsT
    have hvf : ∏ p' ∈ D.SB B, D.vertFactor p' (γ s) = ‖∏ p' ∈ D.SB B, T p' (γ s)‖ := by
      rw [norm_prod]
      exact Finset.prod_congr rfl fun p' hp' => hsT p' hp' hsm'
    have hv0 : 0 < ∏ p' ∈ D.SB B, D.vertFactor p' (γ s) := Finset.prod_pos fun p' hp' =>
      VertFactorPos.proof II Ψ K ι Ω E D p' (hSB p' hp') _ hsm'
    have href := S.ref.pos _ hsm'.1
    have hA := D.A'.pos _ hsm'.1
    have hX : (S.ref.h (γ s) * Real.exp (S.regWeight t (M.proj (γ s)))) ^ q ≠ 0 :=
      (pow_pos (mul_pos href (Real.exp_pos _)) q).ne'
    have hY : (∏ p' ∈ D.SB B, D.vertFactor p' (γ s)) ^ q ≠ 0 := (pow_pos hv0 q).ne'
    have hZ : D.A'.h (γ s) ^ p ≠ 0 := (pow_pos hA p).ne'
    rw [hNe _ hsm', Real.log_mul (mul_ne_zero hX hY) hZ, Real.log_mul hX hY, Real.log_pow, Real.log_pow,
      Real.log_pow, Real.log_mul href.ne' (Real.exp_pos _).ne', Real.log_exp, hvf, hsG]
    simp only [Regular.PotentialCharts.chartFun, (S.R.chart k).left_inv hss]
    ring

  set A1 : (Fin 1 → ℂ) → ℝ := fun u => S.R.chartFun (S.regWeight t) k (S.R.chart k (M.proj (γ (u 0))))
    with hA1def
  set R1 : (Fin 1 → ℂ) → ℝ := fun u => (G (u 0)).re with hR1def
  set L2 : (Fin 1 → ℂ) → ℝ := fun u => Real.log ‖∏ p' ∈ D.SB B, T p' (γ (u 0))‖ with hL2def
  set L3 : (Fin 1 → ℂ) → ℝ := fun u => Real.log (D.A'.h (γ (u 0))) with hL3def
  have hEv : (fun y => Real.log ((regNbarQ H M S B p q t).h y)) ∘ (fun u : Fin 1 → ℂ => γ (u 0)) =ᶠ[𝓝 0]
      fun u => (q : ℝ) * (A1 u + (-1) * R1 u) + (q : ℝ) * L2 u + (p : ℝ) * L3 u := by
    have ht : Tendsto (fun u : Fin 1 → ℂ => u 0) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_apply (0 : Fin 1)).tendsto (0 : Fin 1 → ℂ)
    exact ht.eventually hE0
  have hlevL : levi (fun y => Real.log ((regNbarQ H M S B p q t).h y)) (γ 0) w =
      levi ((fun y => Real.log ((regNbarQ H M S B p q t).h y)) ∘ (fun u : Fin 1 → ℂ => γ (u 0))) 0
        (fun _ => 1) := by
    have h := levi_comp (fun _ => (1 : ℂ)) hΓa hlogN
    rw [hΓd] at h
    exact h.symm
  have hA1c : ContDiffAt ℝ 2 A1 0 := hcf.comp (0 : Fin 1 → ℂ) (hχ1.restrictScalars.contDiffAt (n := 2))
  have hA1l : levi A1 0 (fun _ => 1) = levi (S.R.chartFun (S.regWeight t) k) (S.R.chart k (M.proj (γ 0)))
      (deriv (fun s => S.R.chart k (M.proj (γ s))) 0) := by
    have h := levi_comp (φ := S.R.chartFun (S.regWeight t) k) (fun _ => (1 : ℂ)) hχ1 hcf
    rw [hχd] at h
    exact h
  have hR1c : ContDiffAt ℝ 2 R1 0 := by
    have h := (Complex.reCLM.contDiff (n := 2)).contDiffAt.comp (0 : Fin 1 → ℂ)
      (hG1.restrictScalars.contDiffAt (n := 2))
    convert h using 1
    funext u
    simp [hR1def]
  have hR1l : levi R1 0 (fun _ => 1) = 0 := levi_re_analytic hG1 _
  have hL2 := Inter.RegularizedCurvature.log_norm_pluriharmonic (T := fun u : Fin 1 → ℂ => ∏ p' ∈ D.SB B, T p' (γ (u 0)))
    (hTta.comp_of_eq hΓa rfl) hTt0 (fun _ => 1)
  have hL2c : ContDiffAt ℝ 2 L2 0 := hL2.1
  have hL2l : levi L2 0 (fun _ => 1) = 0 := hL2.2
  have hL3c : ContDiffAt ℝ 2 L3 0 := hlogA.comp (0 : Fin 1 → ℂ) (hΓa.restrictScalars.contDiffAt (n := 2))
  have hL3l : levi L3 0 (fun _ => 1) = levi (fun y => Real.log (D.A'.h y)) (γ 0) w := by
    have h := levi_comp (fun _ => (1 : ℂ)) hΓa hlogA
    rw [hΓd] at h
    exact h
  have hf1 : ContDiffAt ℝ 2 (fun u => A1 u + (-1) * R1 u) 0 := hA1c.add (contDiffAt_const.mul hR1c)
  have hq1 : ContDiffAt ℝ 2 (fun u => (q : ℝ) * (A1 u + (-1) * R1 u)) 0 := contDiffAt_const.mul hf1
  have hq12 : ContDiffAt ℝ 2 (fun u => (q : ℝ) * (A1 u + (-1) * R1 u) + (q : ℝ) * L2 u) 0 :=
    hq1.add (contDiffAt_const.mul hL2c)
  rw [hlevL, levi_congr hEv, levi_add_smul (p : ℝ) hq12 hL3c, levi_add_smul (q : ℝ) hq1 hL2c,
    levi_const_mul (q : ℝ) hf1, levi_add_smul (-1) hA1c hR1c, hA1l, hR1l, hL2l, hL3l]
  ring

end GlobalTheory.CompanionTheory.Ar.Giv
