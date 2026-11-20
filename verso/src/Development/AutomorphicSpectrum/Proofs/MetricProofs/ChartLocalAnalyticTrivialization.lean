import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AnChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConeTangentLiftInChartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

/- English proof (translation)
Use `set L := fderiv ℂ Φ e₀ with hL`. Establish `hLi : LinearMap.ker (L : E →ₗ[ℂ] A) = ⊥` using `LinearMap.ker_eq_bot'.mpr hinj`. Take `⟨p, hp⟩` from `(L : E →ₗ[ℂ] A).exists_leftInverse_of_injective hLi`. Set `π : A →L[ℂ] E` to `LinearMap.toContinuousLinearMap p`. Establish `hπ : ∀ e, π (L e) = e` using `fun e => LinearMap.congr_fun hp e`.

Set `h : E → E` to `fun e => π (Φ e)`. Establish `hh : HasStrictFDerivAt h ((ContinuousLinearEquiv.refl ℂ E : E ≃L[ℂ] E) : E →L[ℂ] E) e₀`. Establish `h1` using `π.hasStrictFDerivAt.comp e₀ hΦ.hasStrictFDerivAt`. Use `h1.congr_fderiv ?_` and prove the remaining obligations. Use extensionality with `e`.

Simplify using `[hπ, ← hL]`. Set `Φ₁` to `hh.toOpenPartialHomeomorph h`. Establish `hΦ₁ : ∀ e, Φ₁ e = π (Φ e)` using `fun e => rfl`. Establish `hs₁ : e₀ ∈ Φ₁.source` using `hh.mem_toOpenPartialHomeomorph_source`. Establish `han₁ : AnalyticAt ℂ Φ₁ e₀` using `(π.analyticAt _).comp hΦ`.

Establish `hsymm : AnalyticAt ℂ Φ₁.symm (Φ₁ e₀)` using `Φ₁.analyticAt_symm' (i := ContinuousLinearEquiv.refl ℂ E) hs₁ han₁ hh.hasFDerivAt.fderiv`. Establish `hback : Φ₁.symm (Φ₁ e₀) = e₀` using `Φ₁.left_inv hs₁`. Set `M : A →L[ℂ] B × E` to `(fderiv ℂ G (Φ e₀)).prod π`. Establish `hMi : LinearMap.ker (M : A →ₗ[ℂ] B × E) = ⊥`. Use `LinearMap.ker_eq_bot'.mpr fun w hw => ?_` and prove the remaining obligations.

Establish `h1 : fderiv ℂ G (Φ e₀) w = 0` using `congrArg Prod.fst hw`. Establish `h2 : π w = 0` using `congrArg Prod.snd hw`. Take `⟨e, rfl⟩` from `hker w h1`. Rewrite `h2` using `[hπ]`. Rewrite using `[h2, map_zero]`.

Take `⟨q, hq⟩` from `(M : A →ₗ[ℂ] B × E).exists_leftInverse_of_injective hMi`. Set `R : B × E →L[ℂ] A` to `LinearMap.toContinuousLinearMap q`. Establish `hR : ∀ w, R (M w) = w` using `fun w => LinearMap.congr_fun hq w`. Set `Ξ : A → A` to `fun z => R (G z, π z)`. Establish `hΞ : HasStrictFDerivAt Ξ ((ContinuousLinearEquiv.refl ℂ A : A ≃L[ℂ] A) : A →L[ℂ] A) (Φ e₀)`.

Establish `h1` using `R.hasStrictFDerivAt.comp (Φ e₀) (hG.hasStrictFDerivAt.prodMk π.hasStrictFDerivAt)`. Use `h1.congr_fderiv ?_` and prove the remaining obligations. Use extensionality with `w`. Conclude with `hR w`. Set `Φ₂` to `hΞ.toOpenPartialHomeomorph Ξ`.

Establish `hs₂ : Φ e₀ ∈ Φ₂.source` using `hΞ.mem_toOpenPartialHomeomorph_source`. Establish `hN : ∀ᶠ e in 𝓝 e₀, e ∈ U ∧ G (Φ e) = 0 ∧ Φ e ∈ Φ₂.source` using `(Filter.eventually_of_mem hU fun _ h => h).and (hzero.and (hΦ.continuousAt.eventually_mem (Φ₂.open_source.mem_nhds hs₂)))`. Establish `hc₁ : ContinuousAt Φ₁.symm (Φ₁ e₀)` using `hsymm.continuousAt`. Establish `hN' : ∀ᶠ x in 𝓝 (Φ₁ e₀), Φ₁.symm x ∈ U ∧ G (Φ (Φ₁.symm x)) = 0 ∧ Φ (Φ₁.symm x) ∈ Φ₂.source`. Use `hc₁.tendsto.eventually (by rw [hback]; exact hN)` as an intermediate fact.

Conclude with `this`. Establish `ht₁ : Φ₁ e₀ ∈ Φ₁.target` using `Φ₁.map_source hs₁`. Establish `hP : ∀ᶠ x in 𝓝 (Φ₁ e₀), (Φ₁.symm x ∈ U ∧ G (Φ (Φ₁.symm x)) = 0 ∧ Φ (Φ₁.symm x) ∈ Φ₂.source) ∧ x ∈ Φ₁.target ∧ AnalyticAt ℂ Φ₁.symm x` using `hN'.and ((Φ₁.open_target.mem_nhds ht₁ |> Filter.eventually_of_mem <| fun _ h => h).and hsymm.eventually_analyticAt)`. Establish `hπc : Tendsto π (𝓝 (Φ e₀)) (𝓝 (Φ₁ e₀))` using `π.continuous.tendsto _`. Establish `hQ : ∀ᶠ z in 𝓝 (Φ e₀), ((Φ₁.symm (π z) ∈ U ∧ G (Φ (Φ₁.symm (π z))) = 0 ∧ Φ (Φ₁.symm (π z)) ∈ Φ₂.source) ∧ π z ∈ Φ₁.target ∧ AnalyticAt ℂ Φ₁.symm (π z)) ∧ z ∈ Φ₂.source` using `(hπc.eventually hP).and (Φ₂.open_source.mem_nhds hs₂ |> Filter.eventually_of_mem <| fun _ h => h)`.

Take `⟨V, hVs, hVo, hV0⟩` from `mem_nhds_iff.mp hQ`. Use `⟨V, fun z => Φ₁.symm (π z), hVo, hV0, ?_, hback, ?_⟩` and prove the remaining obligations. Introduce `z hz`. Conclude with `AnalyticAt.comp (f := fun z => π z) (hVs hz).1.2.2 (π.analyticAt z)`. Introduce `z hz hGz`.

Take `⟨⟨⟨hU', hG', hsrc⟩, htgt, -⟩, hzs⟩` from `hVs hz`. Use `⟨hU', ?_⟩` and prove the remaining obligations. Establish `h1 : π (Φ (Φ₁.symm (π z))) = π z` using `Φ₁.right_inv htgt`. Use `Φ₂.injOn hzs hsrc ?_` and prove the remaining obligations. Use `show R (G z, π z) = R (G _, π _)`.

Rewrite using `[hGz, hG', h1]`.
-/
theorem exists_analytic_param {A B E : Type} [NormedAddCommGroup A] [NormedSpace ℂ A] [FiniteDimensional ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] [FiniteDimensional ℂ B]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {Φ : E → A} {G : A → B} {e₀ : E}
    (hΦ : AnalyticAt ℂ Φ e₀) (hG : AnalyticAt ℂ G (Φ e₀))
    (hinj : ∀ e, fderiv ℂ Φ e₀ e = 0 → e = 0)
    (hker : ∀ w, fderiv ℂ G (Φ e₀) w = 0 → ∃ e, w = fderiv ℂ Φ e₀ e)
    (hzero : ∀ᶠ e in 𝓝 e₀, G (Φ e) = 0) {U : Set E} (hU : U ∈ 𝓝 e₀) :
    ∃ (V : Set A) (S : A → E), IsOpen V ∧ Φ e₀ ∈ V ∧ AnalyticOnNhd ℂ S V ∧ S (Φ e₀) = e₀ ∧
      ∀ z ∈ V, G z = 0 → S z ∈ U ∧ z = Φ (S z) := by
  set L := fderiv ℂ Φ e₀ with hL
  have hLi : LinearMap.ker (L : E →ₗ[ℂ] A) = ⊥ := LinearMap.ker_eq_bot'.mpr hinj
  obtain ⟨p, hp⟩ := (L : E →ₗ[ℂ] A).exists_leftInverse_of_injective hLi
  let π : A →L[ℂ] E := LinearMap.toContinuousLinearMap p
  have hπ : ∀ e, π (L e) = e := fun e => LinearMap.congr_fun hp e

  let h : E → E := fun e => π (Φ e)
  have hh : HasStrictFDerivAt h ((ContinuousLinearEquiv.refl ℂ E : E ≃L[ℂ] E) : E →L[ℂ] E) e₀ := by
    have h1 := π.hasStrictFDerivAt.comp e₀ hΦ.hasStrictFDerivAt
    refine h1.congr_fderiv ?_
    ext e
    simp [hπ, ← hL]
  let Φ₁ := hh.toOpenPartialHomeomorph h
  have hΦ₁ : ∀ e, Φ₁ e = π (Φ e) := fun e => rfl
  have hs₁ : e₀ ∈ Φ₁.source := hh.mem_toOpenPartialHomeomorph_source
  have han₁ : AnalyticAt ℂ Φ₁ e₀ := (π.analyticAt _).comp hΦ
  have hsymm : AnalyticAt ℂ Φ₁.symm (Φ₁ e₀) :=
    Φ₁.analyticAt_symm' (i := ContinuousLinearEquiv.refl ℂ E) hs₁ han₁ hh.hasFDerivAt.fderiv
  have hback : Φ₁.symm (Φ₁ e₀) = e₀ := Φ₁.left_inv hs₁

  let M : A →L[ℂ] B × E := (fderiv ℂ G (Φ e₀)).prod π
  have hMi : LinearMap.ker (M : A →ₗ[ℂ] B × E) = ⊥ := by
    refine LinearMap.ker_eq_bot'.mpr fun w hw => ?_
    have h1 : fderiv ℂ G (Φ e₀) w = 0 := congrArg Prod.fst hw
    have h2 : π w = 0 := congrArg Prod.snd hw
    obtain ⟨e, rfl⟩ := hker w h1
    rw [hπ] at h2
    rw [h2, map_zero]
  obtain ⟨q, hq⟩ := (M : A →ₗ[ℂ] B × E).exists_leftInverse_of_injective hMi
  let R : B × E →L[ℂ] A := LinearMap.toContinuousLinearMap q
  have hR : ∀ w, R (M w) = w := fun w => LinearMap.congr_fun hq w
  let Ξ : A → A := fun z => R (G z, π z)
  have hΞ : HasStrictFDerivAt Ξ ((ContinuousLinearEquiv.refl ℂ A : A ≃L[ℂ] A) : A →L[ℂ] A) (Φ e₀) := by
    have h1 := R.hasStrictFDerivAt.comp (Φ e₀) (hG.hasStrictFDerivAt.prodMk π.hasStrictFDerivAt)
    refine h1.congr_fderiv ?_
    ext w
    exact hR w
  let Φ₂ := hΞ.toOpenPartialHomeomorph Ξ
  have hs₂ : Φ e₀ ∈ Φ₂.source := hΞ.mem_toOpenPartialHomeomorph_source

  have hN : ∀ᶠ e in 𝓝 e₀, e ∈ U ∧ G (Φ e) = 0 ∧ Φ e ∈ Φ₂.source :=
    (Filter.eventually_of_mem hU fun _ h => h).and (hzero.and
      (hΦ.continuousAt.eventually_mem (Φ₂.open_source.mem_nhds hs₂)))
  have hc₁ : ContinuousAt Φ₁.symm (Φ₁ e₀) := hsymm.continuousAt
  have hN' : ∀ᶠ x in 𝓝 (Φ₁ e₀), Φ₁.symm x ∈ U ∧ G (Φ (Φ₁.symm x)) = 0 ∧ Φ (Φ₁.symm x) ∈ Φ₂.source := by
    have := hc₁.tendsto.eventually (by rw [hback]; exact hN)
    exact this
  have ht₁ : Φ₁ e₀ ∈ Φ₁.target := Φ₁.map_source hs₁
  have hP : ∀ᶠ x in 𝓝 (Φ₁ e₀), (Φ₁.symm x ∈ U ∧ G (Φ (Φ₁.symm x)) = 0 ∧ Φ (Φ₁.symm x) ∈ Φ₂.source) ∧
      x ∈ Φ₁.target ∧ AnalyticAt ℂ Φ₁.symm x :=
    hN'.and ((Φ₁.open_target.mem_nhds ht₁ |> Filter.eventually_of_mem <| fun _ h => h).and hsymm.eventually_analyticAt)
  have hπc : Tendsto π (𝓝 (Φ e₀)) (𝓝 (Φ₁ e₀)) := π.continuous.tendsto _
  have hQ : ∀ᶠ z in 𝓝 (Φ e₀), ((Φ₁.symm (π z) ∈ U ∧ G (Φ (Φ₁.symm (π z))) = 0 ∧ Φ (Φ₁.symm (π z)) ∈ Φ₂.source) ∧
      π z ∈ Φ₁.target ∧ AnalyticAt ℂ Φ₁.symm (π z)) ∧ z ∈ Φ₂.source :=
    (hπc.eventually hP).and (Φ₂.open_source.mem_nhds hs₂ |> Filter.eventually_of_mem <| fun _ h => h)
  obtain ⟨V, hVs, hVo, hV0⟩ := mem_nhds_iff.mp hQ
  refine ⟨V, fun z => Φ₁.symm (π z), hVo, hV0, ?_, hback, ?_⟩
  · intro z hz
    exact AnalyticAt.comp (f := fun z => π z) (hVs hz).1.2.2 (π.analyticAt z)
  · intro z hz hGz
    obtain ⟨⟨⟨hU', hG', hsrc⟩, htgt, -⟩, hzs⟩ := hVs hz
    refine ⟨hU', ?_⟩
    have h1 : π (Φ (Φ₁.symm (π z))) = π z := Φ₁.right_inv htgt
    refine Φ₂.injOn hzs hsrc ?_
    show R (G z, π z) = R (G _, π _)
    rw [hGz, hG', h1]

open MvPolynomial in

/- English proof (translation)
Use `set z₀ := χ.γ t₀ with hz₀`. Set `σ : ℤ →+* ℂ` to `Int.castRingHom ℂ`. Set `ell : MRing J → Module.Dual ℂ ((Σ k, J k) → ℂ)` to `fun f => ∑ i, eval z₀ (pderiv i (map σ f)) • LinearMap.proj i`. Establish `hell : ∀ f w, ell f w = ∑ i, eval z₀ (pderiv i (map σ f)) * w i` using `fun f w => by`. Simplify using `[ell, LinearMap.sum_apply]`.

Take `⟨s, hsub, hspan⟩` from `(Submodule.fg_span_iff_fg_span_finset_subset (ell '' (P : Set (MRing J)))).1 (IsNoetherian.noetherian (Submodule.span ℂ (ell '' (P : Set (MRing J)))))`. Establish `hch : ∀ l : s, ∃ f ∈ P, ell f = l.1` using `fun l => by`. Take `⟨f, hf, h⟩` from `hsub l.2`. Conclude with `⟨f, hf, h⟩`. Use `choose f hfP hfl using hch`.

Set `g : s → MvPolynomial (Σ k, J k) ℂ` to `fun l => map σ (f l)`. Set `G : ((Σ k, J k) → ℂ) → s → ℂ` to `fun z l => eval z (g l)`. Set `Φ : (K → ℂ) × (Fin n → ℂ) → (Σ k, J k) → ℂ` to `fun e => torusSmul e.1 (χ.γ e.2)`. Set `e₀ : (K → ℂ) × (Fin n → ℂ)` to `(1, t₀)`. Establish `hΦ₀ : Φ e₀ = z₀`.

Use function extensionality and compare the values at `p`. Simplify using `[Φ, e₀, torusSmul, hz₀]`. Establish `hγ : AnalyticAt ℂ χ.γ t₀` using `χ.analytic t₀ ht₀`. Establish `hΦan : AnalyticAt ℂ Φ e₀`. Use `AnalyticAt.pi fun p => ?_` and prove the remaining obligations.

Establish `h1 : AnalyticAt ℂ (fun e : (K → ℂ) × (Fin n → ℂ) => e.1 p.1) e₀` using `((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) p.1).comp (ContinuousLinearMap.fst ℂ (K → ℂ) (Fin n → ℂ))).analyticAt e₀`. Establish `h2 : AnalyticAt ℂ (fun e : (K → ℂ) × (Fin n → ℂ) => χ.γ e.2) e₀` using `AnalyticAt.comp (f := fun e : (K → ℂ) × (Fin n → ℂ) => e.2) hγ ((ContinuousLinearMap.snd ℂ (K → ℂ) (Fin n → ℂ)).analyticAt e₀)`. Establish `h3 : AnalyticAt ℂ (fun e : (K → ℂ) × (Fin n → ℂ) => χ.γ e.2 p) e₀` using `((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) p).analyticAt _).comp h2`. Conclude with `h1.mul h3`. Establish `hGan : AnalyticAt ℂ G (Φ e₀)`.

Use `AnalyticAt.pi fun l => ?_` and prove the remaining obligations. Conclude with `AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℂ) (g l) _ (Set.mem_univ _)`. Establish `hdΦ : ∀ c u, fderiv ℂ Φ e₀ (c, u) = fderiv ℂ χ.γ t₀ u + torusSmul c z₀`. Establish `hγd` using `hγ.differentiableAt.hasFDerivAt`. Establish `hD : HasFDerivAt Φ (ContinuousLinearMap.pi fun p : (Σ k, J k) => (1 : ℂ) • ((ContinuousLinearMap.proj (R` using `ℂ) (φ := fun _ : (Σ k, J k) => ℂ) p).comp ((fderiv ℂ χ.γ t₀).comp (ContinuousLinearMap.snd ℂ (K → ℂ) (Fin n → ℂ)))) + z₀ p • ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) p.1).comp (ContinuousLinearMap.fst ℂ (K → ℂ) (Fin n → ℂ)))) e₀ := by`.

Use `hasFDerivAt_pi.2 fun p => ?_` and prove the remaining obligations. Establish `h1 : HasFDerivAt (fun e : (K → ℂ) × (Fin n → ℂ) => e.1 p.1) ((ContinuousLinearMap.proj (R` using `ℂ) (φ := fun _ : K => ℂ) p.1).comp (ContinuousLinearMap.fst ℂ (K → ℂ) (Fin n → ℂ))) e₀ := ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) p.1).comp (ContinuousLinearMap.fst ℂ (K → ℂ) (Fin n → ℂ))).hasFDerivAt`. Establish `h2 : HasFDerivAt (fun e : (K → ℂ) × (Fin n → ℂ) => χ.γ e.2) ((fderiv ℂ χ.γ t₀).comp (ContinuousLinearMap.snd ℂ (K → ℂ) (Fin n → ℂ))) e₀` using `HasFDerivAt.comp e₀ (f := fun e : (K → ℂ) × (Fin n → ℂ) => e.2) hγd (ContinuousLinearMap.snd ℂ (K → ℂ) (Fin n → ℂ)).hasFDerivAt`. Establish `h3 : HasFDerivAt (fun e : (K → ℂ) × (Fin n → ℂ) => χ.γ e.2 p) ((ContinuousLinearMap.proj (R` using `ℂ) (φ := fun _ : (Σ k, J k) => ℂ) p).comp ((fderiv ℂ χ.γ t₀).comp (ContinuousLinearMap.snd ℂ (K → ℂ) (Fin n → ℂ)))) e₀ := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) p).hasFDerivAt.comp e₀ h2`. Use `(h1.mul h3).congr_fderiv ?_` and prove the remaining obligations.

Simplify using `[e₀, hz₀]`. Introduce `c u`. Rewrite using `[hD.fderiv]`. Use function extensionality and compare the values at `p`. Simplify using `[torusSmul, mul_comm]`.

Establish `hdG : ∀ w l, fderiv ℂ G (Φ e₀) w l = ell (f l) w`. Establish `hD : HasFDerivAt G (ContinuousLinearMap.pi fun l : s => ∑ i, eval (Φ e₀) (pderiv i (g l)) • ContinuousLinearMap.proj (R` using `ℂ) (φ := fun _ : (Σ k, J k) => ℂ) i) (Φ e₀) := hasFDerivAt_pi.2 fun l => hasFDerivAt_eval (g l) (Φ e₀)`. Introduce `w l`. Rewrite using `[hD.fderiv, hell, hΦ₀]`. Simplify using `[g]`.

Establish `hinj : ∀ e, fderiv ℂ Φ e₀ e = 0 → e = 0`. Introduce and unpack `⟨c, u⟩ h`. Rewrite `h` using `[hdΦ]`. Establish `hu : u = 0`. Use `χ.immersion t₀ ht₀ u ⟨fun k => - c k, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `p`. Use `congrFun h p` as an intermediate fact. Simplify using `only [Pi.add_apply, Pi.zero_apply, torusSmul] at this ⊢`. Rewrite using `[← hz₀]`. Take the linear combination `this`.

Substitute `hu` using the available equality. Establish `hc : c = 0`. Use function extensionality and compare the values at `k`. Take `⟨i, hi⟩` from `(χ.mem t₀ ht₀).1 k`. Use `congrFun h ⟨k, i⟩` as an intermediate fact.

Simplify using `only [map_zero, Pi.add_apply, Pi.zero_apply, zero_add, torusSmul] at this`. Conclude with `(mul_eq_zero.mp this).resolve_right hi`. Simplify using `[hc]`. Establish `hker : ∀ w, fderiv ℂ G (Φ e₀) w = 0 → ∃ e, w = fderiv ℂ Φ e₀ e`. Introduce `w hw`.

Establish `hs0 : ∀ l ∈ Submodule.span ℂ (s : Set (Module.Dual ℂ ((Σ k, J k) → ℂ))), l w = 0`. Introduce `l hl`. Proceed by induction on `hl using Submodule.span_induction with`. Consider the case `mem x hx`. Use `congrFun hw ⟨x, hx⟩` as an intermediate fact.

Rewrite `this` using `[hdG, hfl]`. Conclude with `this`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => simp [hx, hy]`. Consider the case `smul a x _ hx => simp [hx]`.

Establish `htv : IsConeTangent (Int.castRingHom ℂ) P z₀ w`. Introduce `q hq`. Establish `: ell q ∈ Submodule.span ℂ (s : Set (Module.Dual ℂ ((Σ k, J k) → ℂ)))`. Rewrite using `[← hspan]`. Conclude with `Submodule.subset_span ⟨q, hq, rfl⟩`.

Establish `h0` using `hs0 _ this`. Rewrite `h0` using `[hell]`. Conclude with `h0`. Take `⟨u, c, hv⟩` from `htan w htv`. Conclude with `⟨(c, u), by rw [hdΦ, hv]⟩`.

Establish `hopen : ∀ᶠ e : (K → ℂ) × (Fin n → ℂ) in 𝓝 e₀, (∀ k, e.1 k ≠ 0) ∧ e.2 ∈ Metric.ball (0 : Fin n → ℂ) 1`. Use `Filter.Eventually.and (eventually_all.2 fun k => ?_) ?_` and prove the remaining obligations. Establish `hc : ContinuousAt (fun e : (K → ℂ) × (Fin n → ℂ) => e.1 k) e₀` using `by fun_prop`. Conclude with `hc.eventually_ne (by simp [e₀])`. Establish `hc : ContinuousAt (fun e : (K → ℂ) × (Fin n → ℂ) => e.2) e₀` using `by fun_prop`.

Conclude with `hc.eventually_mem (Metric.isOpen_ball.mem_nhds ht₀)`. Establish `hzero : ∀ᶠ e in 𝓝 e₀, G (Φ e) = 0` using `by filter_upwards [hopen] with e he`. Use function extensionality and compare the values at `l`. Conclude with `(mcPts_smul hP e.1 he.1 (χ.mem e.2 he.2)).2 (f l) (hfP l)`. Take `⟨V, S, hVo, hV0, hSan, hS0, hS⟩` from `exists_analytic_param hΦan hGan hinj hker hzero hopen`.

Rewrite `hV0`, `hS0` using `[hΦ₀]`. Use `⟨V, fun z => (S z).2, hVo, hV0, ?_, by simp [hS0, e₀], ?_⟩` and prove the remaining obligations. Introduce `z hz`. Conclude with `((ContinuousLinearMap.snd ℂ (K → ℂ) (Fin n → ℂ)).analyticAt _).comp (hSan z hz)`. Introduce and unpack `z ⟨hzV, hzP⟩`.

Establish `hGz : G z = 0`. Use function extensionality and compare the values at `l`. Conclude with `hzP.2 (f l) (hfP l)`. Take `⟨hU, hz⟩` from `hS z hzV hGz`. Conclude with `⟨hU.2, (S z).1, hU.1, hz⟩`.
-/
theorem exists_chart_inverse {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {P : Ideal (MRing J)}
    (hP : IsMultiHomogIdeal P) {n : ℕ} {Bd : Set ((Σ k, J k) → ℂ)} (χ : SncChart P n Bd) {t₀ : Fin n → ℂ}
    (ht₀ : t₀ ∈ Metric.ball (0 : Fin n → ℂ) 1)
    (htan : ∀ v, IsConeTangent (Int.castRingHom ℂ) P (χ.γ t₀) v →
      ∃ (u : Fin n → ℂ) (c : K → ℂ), v = fderiv ℂ χ.γ t₀ u + torusSmul c (χ.γ t₀)) :
    ∃ (V : Set ((Σ k, J k) → ℂ)) (T : ((Σ k, J k) → ℂ) → Fin n → ℂ), IsOpen V ∧ χ.γ t₀ ∈ V ∧
      AnalyticOnNhd ℂ T V ∧ T (χ.γ t₀) = t₀ ∧ ∀ z ∈ V ∩ mcPts P, T z ∈ Metric.ball 0 1 ∧
        ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z = torusSmul c (χ.γ (T z)) := by
  classical
  set z₀ := χ.γ t₀ with hz₀
  let σ : ℤ →+* ℂ := Int.castRingHom ℂ

  let ell : MRing J → Module.Dual ℂ ((Σ k, J k) → ℂ) := fun f =>
    ∑ i, eval z₀ (pderiv i (map σ f)) • LinearMap.proj i
  have hell : ∀ f w, ell f w = ∑ i, eval z₀ (pderiv i (map σ f)) * w i := fun f w => by
    simp [ell, LinearMap.sum_apply]
  obtain ⟨s, hsub, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (ell '' (P : Set (MRing J)))).1
    (IsNoetherian.noetherian (Submodule.span ℂ (ell '' (P : Set (MRing J)))))
  have hch : ∀ l : s, ∃ f ∈ P, ell f = l.1 := fun l => by
    obtain ⟨f, hf, h⟩ := hsub l.2
    exact ⟨f, hf, h⟩
  choose f hfP hfl using hch
  let g : s → MvPolynomial (Σ k, J k) ℂ := fun l => map σ (f l)
  let G : ((Σ k, J k) → ℂ) → s → ℂ := fun z l => eval z (g l)
  let Φ : (K → ℂ) × (Fin n → ℂ) → (Σ k, J k) → ℂ := fun e => torusSmul e.1 (χ.γ e.2)
  let e₀ : (K → ℂ) × (Fin n → ℂ) := (1, t₀)
  have hΦ₀ : Φ e₀ = z₀ := by
    funext p
    simp [Φ, e₀, torusSmul, hz₀]
  have hγ : AnalyticAt ℂ χ.γ t₀ := χ.analytic t₀ ht₀
  have hΦan : AnalyticAt ℂ Φ e₀ := by
    refine AnalyticAt.pi fun p => ?_
    have h1 : AnalyticAt ℂ (fun e : (K → ℂ) × (Fin n → ℂ) => e.1 p.1) e₀ :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) p.1).comp
        (ContinuousLinearMap.fst ℂ (K → ℂ) (Fin n → ℂ))).analyticAt e₀
    have h2 : AnalyticAt ℂ (fun e : (K → ℂ) × (Fin n → ℂ) => χ.γ e.2) e₀ :=
      AnalyticAt.comp (f := fun e : (K → ℂ) × (Fin n → ℂ) => e.2) hγ
        ((ContinuousLinearMap.snd ℂ (K → ℂ) (Fin n → ℂ)).analyticAt e₀)
    have h3 : AnalyticAt ℂ (fun e : (K → ℂ) × (Fin n → ℂ) => χ.γ e.2 p) e₀ :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) p).analyticAt _).comp h2
    exact h1.mul h3
  have hGan : AnalyticAt ℂ G (Φ e₀) := by
    refine AnalyticAt.pi fun l => ?_
    exact AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℂ) (g l) _ (Set.mem_univ _)

  have hdΦ : ∀ c u, fderiv ℂ Φ e₀ (c, u) = fderiv ℂ χ.γ t₀ u + torusSmul c z₀ := by
    have hγd := hγ.differentiableAt.hasFDerivAt
    have hD : HasFDerivAt Φ (ContinuousLinearMap.pi fun p : (Σ k, J k) =>
        (1 : ℂ) • ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) p).comp
            ((fderiv ℂ χ.γ t₀).comp (ContinuousLinearMap.snd ℂ (K → ℂ) (Fin n → ℂ)))) +
          z₀ p • ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) p.1).comp
            (ContinuousLinearMap.fst ℂ (K → ℂ) (Fin n → ℂ)))) e₀ := by
      refine hasFDerivAt_pi.2 fun p => ?_
      have h1 : HasFDerivAt (fun e : (K → ℂ) × (Fin n → ℂ) => e.1 p.1)
          ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) p.1).comp
            (ContinuousLinearMap.fst ℂ (K → ℂ) (Fin n → ℂ))) e₀ :=
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) p.1).comp
            (ContinuousLinearMap.fst ℂ (K → ℂ) (Fin n → ℂ))).hasFDerivAt
      have h2 : HasFDerivAt (fun e : (K → ℂ) × (Fin n → ℂ) => χ.γ e.2)
          ((fderiv ℂ χ.γ t₀).comp (ContinuousLinearMap.snd ℂ (K → ℂ) (Fin n → ℂ))) e₀ :=
        HasFDerivAt.comp e₀ (f := fun e : (K → ℂ) × (Fin n → ℂ) => e.2) hγd
          (ContinuousLinearMap.snd ℂ (K → ℂ) (Fin n → ℂ)).hasFDerivAt
      have h3 : HasFDerivAt (fun e : (K → ℂ) × (Fin n → ℂ) => χ.γ e.2 p)
          ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) p).comp
            ((fderiv ℂ χ.γ t₀).comp (ContinuousLinearMap.snd ℂ (K → ℂ) (Fin n → ℂ)))) e₀ :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) p).hasFDerivAt.comp e₀ h2
      refine (h1.mul h3).congr_fderiv ?_
      simp [e₀, hz₀]
    intro c u
    rw [hD.fderiv]
    funext p
    simp [torusSmul, mul_comm]

  have hdG : ∀ w l, fderiv ℂ G (Φ e₀) w l = ell (f l) w := by
    have hD : HasFDerivAt G (ContinuousLinearMap.pi fun l : s =>
        ∑ i, eval (Φ e₀) (pderiv i (g l)) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) i)
        (Φ e₀) := hasFDerivAt_pi.2 fun l => hasFDerivAt_eval (g l) (Φ e₀)
    intro w l
    rw [hD.fderiv, hell, hΦ₀]
    simp [g]
  have hinj : ∀ e, fderiv ℂ Φ e₀ e = 0 → e = 0 := by
    rintro ⟨c, u⟩ h
    rw [hdΦ] at h
    have hu : u = 0 := by
      refine χ.immersion t₀ ht₀ u ⟨fun k => - c k, ?_⟩
      funext p
      have := congrFun h p
      simp only [Pi.add_apply, Pi.zero_apply, torusSmul] at this ⊢
      rw [← hz₀]
      linear_combination this
    subst hu
    have hc : c = 0 := by
      funext k
      obtain ⟨i, hi⟩ := (χ.mem t₀ ht₀).1 k
      have := congrFun h ⟨k, i⟩
      simp only [map_zero, Pi.add_apply, Pi.zero_apply, zero_add, torusSmul] at this
      exact (mul_eq_zero.mp this).resolve_right hi
    simp [hc]
  have hker : ∀ w, fderiv ℂ G (Φ e₀) w = 0 → ∃ e, w = fderiv ℂ Φ e₀ e := by
    intro w hw
    have hs0 : ∀ l ∈ Submodule.span ℂ (s : Set (Module.Dual ℂ ((Σ k, J k) → ℂ))), l w = 0 := by
      intro l hl
      induction hl using Submodule.span_induction with
      | mem x hx =>
        have := congrFun hw ⟨x, hx⟩
        rw [hdG, hfl] at this
        exact this
      | zero => simp
      | add x y _ _ hx hy => simp [hx, hy]
      | smul a x _ hx => simp [hx]
    have htv : IsConeTangent (Int.castRingHom ℂ) P z₀ w := by
      intro q hq
      have : ell q ∈ Submodule.span ℂ (s : Set (Module.Dual ℂ ((Σ k, J k) → ℂ))) := by
        rw [← hspan]
        exact Submodule.subset_span ⟨q, hq, rfl⟩
      have h0 := hs0 _ this
      rw [hell] at h0
      exact h0
    obtain ⟨u, c, hv⟩ := htan w htv
    exact ⟨(c, u), by rw [hdΦ, hv]⟩
  have hopen : ∀ᶠ e : (K → ℂ) × (Fin n → ℂ) in 𝓝 e₀, (∀ k, e.1 k ≠ 0) ∧ e.2 ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
    refine Filter.Eventually.and (eventually_all.2 fun k => ?_) ?_
    · have hc : ContinuousAt (fun e : (K → ℂ) × (Fin n → ℂ) => e.1 k) e₀ := by fun_prop
      exact hc.eventually_ne (by simp [e₀])
    · have hc : ContinuousAt (fun e : (K → ℂ) × (Fin n → ℂ) => e.2) e₀ := by fun_prop
      exact hc.eventually_mem (Metric.isOpen_ball.mem_nhds ht₀)
  have hzero : ∀ᶠ e in 𝓝 e₀, G (Φ e) = 0 := by
    filter_upwards [hopen] with e he
    funext l
    exact (mcPts_smul hP e.1 he.1 (χ.mem e.2 he.2)).2 (f l) (hfP l)
  obtain ⟨V, S, hVo, hV0, hSan, hS0, hS⟩ := exists_analytic_param hΦan hGan hinj hker hzero hopen
  rw [hΦ₀] at hV0 hS0
  refine ⟨V, fun z => (S z).2, hVo, hV0, ?_, by simp [hS0, e₀], ?_⟩
  · intro z hz
    exact ((ContinuousLinearMap.snd ℂ (K → ℂ) (Fin n → ℂ)).analyticAt _).comp (hSan z hz)
  · rintro z ⟨hzV, hzP⟩
    have hGz : G z = 0 := by
      funext l
      exact hzP.2 (f l) (hfP l)
    obtain ⟨hU, hz⟩ := hS z hzV hGz
    exact ⟨hU.2, (S z).1, hU.1, hz⟩

/- English proof (translation)
Introduce `K _ J _ II Ψ _ Ω _ _ W _ _ D a t₀ ht₀`. Conclude with `exists_chart_inverse D.arith.2.1.2.1 (D.chart a) ht₀ (GlobalTheory.T.cone_tangent_lift_in_chart K J II Ψ Ω W D a t₀ ht₀)`.
-/
theorem chart_torus_open : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (a : Fin D.nCharts), ∀ t₀ ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1, ∃ (V : Set ((Σ k, J k) → ℂ)) (T : ((Σ k, J k) → ℂ) → Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ), IsOpen V ∧ (D.chart a).γ t₀ ∈ V ∧ AnalyticOnNhd ℂ T V ∧ T ((D.chart a).γ t₀) = t₀ ∧ ∀ z ∈ V ∩ mcPts (mCoordIdeal D.y), T z ∈ Metric.ball 0 1 ∧ ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z = torusSmul c ((D.chart a).γ (T z)) := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D a t₀ ht₀
  exact exists_chart_inverse D.arith.2.1.2.1 (D.chart a) ht₀
    (GlobalTheory.T.cone_tangent_lift_in_chart K J II Ψ Ω W D a t₀ ht₀)

end GlobalTheory.CompanionTheory.Ar.Cusp
