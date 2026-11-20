import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergThetaIntegralPoleRapidKernelSpanStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedThetaIntegralEqMulSchurEulerProductStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasProdLocalRankinSelbergFactorSelfOfEulerProducStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableCompInfGLProd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MspanLeBddForms
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup
  Formalism.L2.Host GlobalTheory.JSW
open scoped ENNReal nonZeroDivisors ComplexConjugate

noncomputable section

namespace GlobalTheory.RSPole

open GlobalTheory.CuspRep.CuspidalL2GL in

/- English proof (translation)
Introduce `E _ _ _ a`. Use `haveI := CuspidalL2GL.locallyCompactSpace_GA E a`. Use `haveI := CuspidalL2GL.t2Space_GA E a`. Use `haveI := CuspidalL2GL.secondCountableTopology_GA E a`. Use `haveI : DiscreteTopology (ratGL E a).range := GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E a`.

Take `⟨𝓕, -, -, h𝓕⟩` from `GlobalTheory.exists_isFundamentalDomain_subgroup (ratGL E a).range`. Take `⟨𝓕', -, -, h𝓕'⟩` from `GlobalTheory.exists_isFundamentalDomain_subgroup (latticeGL E a)`. Conclude with `⟨Measure.haar, inferInstance, 𝓕, 𝓕', h𝓕 _, h𝓕' _⟩`.
-/
theorem exists_haar_fundamentalDomains : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ),
    ∃ (μ : Measure (GA E a)) (_ : μ.IsHaarMeasure) (𝓕 𝓕' : Set (GA E a)),
      IsFundamentalDomain (ratGL E a).range 𝓕 μ ∧ IsFundamentalDomain (latticeGL E a) 𝓕' μ := by
  intro E _ _ _ a
  haveI := CuspidalL2GL.locallyCompactSpace_GA E a
  haveI := CuspidalL2GL.t2Space_GA E a
  haveI := CuspidalL2GL.secondCountableTopology_GA E a
  haveI : DiscreteTopology (ratGL E a).range := GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E a
  obtain ⟨𝓕, -, -, h𝓕⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (ratGL E a).range
  obtain ⟨𝓕', -, -, h𝓕'⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (latticeGL E a)
  exact ⟨Measure.haar, inferInstance, 𝓕, 𝓕', h𝓕 _, h𝓕' _⟩

open GlobalTheory.Petersson GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep.CuspidalL2GL in

/- English proof (translation)
Establish `hR : φ.1 ∈ GlobalTheory.JSW.rspan π₀`. Break down `hφ with h | h` into its components or cases. Conclude with `GlobalTheory.JSW.mem_rspan h`. Rewrite using `[GlobalTheory.JSW.rspan_eq_mspanR]`. Conclude with `h`.

Establish `h1 : φ.1 ≠ 0` using `fun e => h0 (Subtype.ext e)`. Establish `hb : φ.1 ∈ bddForms E a ω` using `(GlobalTheory.JSW.rspan_bdd_pet_eq_zero μ hω hωc (ψ := 0) (zero_mem _) (fun _ _ => by simp [pet, descend]) hR).1`. Take `⟨r, hr, e⟩` from `pet_self_pos μ hω hb h1`. Rewrite using `[← (pet_eq_setIntegral hω hb hb h𝓕).2, e]`. Conclude with `hr.ne'` after adjusting the coercions.
-/
theorem setIntegral_mul_conj_ne_zero_rapid {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    (π₀ : CuspSub E a) (ω : HChar E) (hω : ω.IsUnitary) (hωc : π₀.HasCentChar ω) (φ : Sm E a)
    (hφ : φ ∈ π₀.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π₀) (h0 : φ ≠ 0) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (𝓕' : Set (GA E a)) (h𝓕 : IsFundamentalDomain (latticeGL E a) 𝓕' μ) :
    ∫ g in 𝓕', φ.1 g * starRingEnd ℂ (φ.1 g) ∂μ ≠ 0 := by
  have hR : φ.1 ∈ GlobalTheory.JSW.rspan π₀ := by
    rcases hφ with h | h
    · exact GlobalTheory.JSW.mem_rspan h
    · rw [GlobalTheory.JSW.rspan_eq_mspanR]; exact h
  have h1 : φ.1 ≠ 0 := fun e => h0 (Subtype.ext e)
  have hb : φ.1 ∈ bddForms E a ω :=
    (GlobalTheory.JSW.rspan_bdd_pet_eq_zero μ hω hωc (ψ := 0) (zero_mem _) (fun _ _ => by simp [pet, descend]) hR).1
  obtain ⟨r, hr, e⟩ := pet_self_pos μ hω hb h1
  rw [← (pet_eq_setIntegral hω hb hb h𝓕).2, e]
  exact_mod_cast hr.ne'

/- English proof (translation)
Introduce `E _ _ _ a π ha hπ T hT`. Take `⟨α, ℓ, Φ, J, η, π₀, ω, φ, hα, hπ₀, hω, hωc, hφ, hφ0, hΦc, hΦs, hΦr, hΦpos, hΦ0, hZ⟩` from `GlobalTheory.T.unfolded_theta_integral_eq_mul_schur_euler_product E a π ha hπ T hT`. Use `set q : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → ℕ := fun w => Ideal.absNorm w.1.asIdeal with hqdef`. Establish `hq : ∀ w, 2 ≤ q w` using `fun w => HeightOneSpectrum.one_lt_absNorm w.1`. Take `⟨μ, hμ, 𝓕, 𝓕', h𝓕, h𝓕'⟩` from `exists_haar_fundamentalDomains E a`.

Take `⟨H, hHc, hH1, hZH'⟩` from `hZ μ 𝓕 h𝓕`. Establish `hZH : ∀ x : ℝ, 1 < x → _` using `fun x hx => (hZH' x hx).2`. Establish `hHpos : ∀ x : ℝ, 1 < x → 0 < H x` using `fun x hx => (hZH' x hx).1`. Use `set D : ℝ → ℝ := fun x => (eulD q (fun w i => ((α w i : ℂˣ) : ℂ)) x).toReal with hDdef`. Take `⟨hprod, hcont⟩` from `GlobalTheory.T.hasProd_localRankinSelbergFactor_self_of_eulerProduct _ q a α hq fun x hx => (hZH x hx).1`.

Use `⟨D, fun x hx => ?_, hcont, ?_⟩` and prove the remaining obligations. Establish `e : (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => locL (Ideal.absNorm w.1.asIdeal) (sat π w.1) ((sat π w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) = fun w => locL (q w) (Finset.univ.val.map (α w)) ((Finset.univ.val.map (α w)).map (Units.map (starRingEnd ℂ).toM …`. Use function extensionality and compare the values at `w`. Rewrite using `[hα w]`. Rewrite using `[e]`.

Conclude with `hprod x hx`. Take `⟨c, hc0, hlim⟩` from `GlobalTheory.T.rankinSelberg_theta_integral_pole_rapid_kernel_span E a ℓ Φ hΦc hΦs hΦr J η μ 𝓕 𝓕' h𝓕 h𝓕'`. Establish `hc : c ≠ 0` using `hc0 hΦpos hΦ0`. Establish `hT2` using `(hlim π₀ π₀ ω hω hωc hωc φ φ hφ hφ).2`. Establish `hP` using `setIntegral_mul_conj_ne_zero_rapid π₀ ω hω hωc φ hφ hφ0 μ 𝓕' h𝓕'`.

Use `set P := ∫ g in 𝓕', φ.1 g * starRingEnd ℂ (φ.1 g) ∂μ`. Establish `hH : Tendsto (fun x : ℝ => ((H x : ℝ) : ℂ)) (𝓝[>] 1) (𝓝 ((H 1 : ℝ) : ℂ))` using `(Complex.continuous_ofReal.tendsto _).comp hHc`. Establish `hH0 : ((H 1 : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 hH1.ne'`. Establish `hdiv` using `hT2.div hH hH0`. Establish `hev : ∀ᶠ x in 𝓝[>] (1 : ℝ), ((x - 1 : ℝ) : ℂ) * thetaZ μ 𝓕 ℓ φ.1 φ.1 Φ J η x / ((H x : ℝ) : ℂ) = (((x - 1) * D x : ℝ) : ℂ)` using `by filter_upwards [self_mem_nhdsWithin] with x hx`.

Rewrite using `[(hZH x hx).2]`. Establish `: ((H x : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 (hHpos x hx).ne'`. Simplify using `only [hDdef]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Establish `hlim2 : Tendsto (fun x : ℝ => (((x - 1) * D x : ℝ) : ℂ)) (𝓝[>] 1) (𝓝 (c * P / ((H 1 : ℝ) : ℂ)))` using `(hdiv.congr' hev)`. Establish `hre` using `(Complex.continuous_re.tendsto _).comp hlim2`. Establish `him` using `(Complex.continuous_im.tendsto _).comp hlim2`. Simplify using `only [Function.comp_def, Complex.ofReal_re, Complex.ofReal_im] at hre him`. Establish `him0 : (c * P / ((H 1 : ℝ) : ℂ)).im = 0` using `tendsto_nhds_unique tendsto_const_nhds him |>.symm`.

Establish `hne : c * P / ((H 1 : ℝ) : ℂ) ≠ 0` using `div_ne_zero (mul_ne_zero hc hP) hH0`. Establish `hnn : 0 ≤ (c * P / ((H 1 : ℝ) : ℂ)).re`. Use `ge_of_tendsto hre ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with x hx`. Establish `hx' : (1 : ℝ) < x` using `hx`.

Establish `h1` using `(hprod x hx').2`. Conclude with `mul_nonneg (by linarith) (by linarith)`. Use `⟨_, lt_of_le_of_ne hnn fun h0 => hne (Complex.ext h0.symm him0), hre⟩` and prove the remaining obligations.
-/
theorem rs_pole_conj : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CG E a), 1 ≤ a → π.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T π → ∃ L : ℝ → ℝ, (∀ x : ℝ, 1 < x → HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => locL (Ideal.absNorm w.1.asIdeal) (sat π w.1) ((sat π w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (L x : ℂ) ∧ 1 ≤ L x) ∧ ContinuousOn L (Set.Ioi 1) ∧ ∃ c : ℝ, 0 < c ∧ Tendsto (fun x => (x - 1) * L x) (𝓝[>] 1) (𝓝 c) := by
  intro E _ _ _ a π ha hπ T hT
  obtain ⟨α, ℓ, Φ, J, η, π₀, ω, φ, hα, hπ₀, hω, hωc, hφ, hφ0, hΦc, hΦs, hΦr, hΦpos, hΦ0, hZ⟩ := GlobalTheory.T.unfolded_theta_integral_eq_mul_schur_euler_product E a π ha hπ T hT
  set q : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → ℕ := fun w => Ideal.absNorm w.1.asIdeal with hqdef
  have hq : ∀ w, 2 ≤ q w := fun w => HeightOneSpectrum.one_lt_absNorm w.1
  obtain ⟨μ, hμ, 𝓕, 𝓕', h𝓕, h𝓕'⟩ := exists_haar_fundamentalDomains E a
  obtain ⟨H, hHc, hH1, hZH'⟩ := hZ μ 𝓕 h𝓕
  have hZH : ∀ x : ℝ, 1 < x → _ := fun x hx => (hZH' x hx).2
  have hHpos : ∀ x : ℝ, 1 < x → 0 < H x := fun x hx => (hZH' x hx).1
  set D : ℝ → ℝ := fun x => (eulD q (fun w i => ((α w i : ℂˣ) : ℂ)) x).toReal with hDdef
  obtain ⟨hprod, hcont⟩ := GlobalTheory.T.hasProd_localRankinSelbergFactor_self_of_eulerProduct _ q a α hq fun x hx => (hZH x hx).1
  refine ⟨D, fun x hx => ?_, hcont, ?_⟩
  · have e : (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => locL (Ideal.absNorm w.1.asIdeal) (sat π w.1)
        ((sat π w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) = fun w => locL (q w)
        (Finset.univ.val.map (α w)) ((Finset.univ.val.map (α w)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) := by
      funext w; rw [hα w]
    rw [e]
    exact hprod x hx
  · obtain ⟨c, hc0, hlim⟩ := GlobalTheory.T.rankinSelberg_theta_integral_pole_rapid_kernel_span E a ℓ Φ hΦc hΦs hΦr J η μ 𝓕 𝓕' h𝓕 h𝓕'
    have hc : c ≠ 0 := hc0 hΦpos hΦ0
    have hT2 := (hlim π₀ π₀ ω hω hωc hωc φ φ hφ hφ).2
    have hP := setIntegral_mul_conj_ne_zero_rapid π₀ ω hω hωc φ hφ hφ0 μ 𝓕' h𝓕'
    set P := ∫ g in 𝓕', φ.1 g * starRingEnd ℂ (φ.1 g) ∂μ
    have hH : Tendsto (fun x : ℝ => ((H x : ℝ) : ℂ)) (𝓝[>] 1) (𝓝 ((H 1 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp hHc
    have hH0 : ((H 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hH1.ne'
    have hdiv := hT2.div hH hH0
    have hev : ∀ᶠ x in 𝓝[>] (1 : ℝ), ((x - 1 : ℝ) : ℂ) * thetaZ μ 𝓕 ℓ φ.1 φ.1 Φ J η x / ((H x : ℝ) : ℂ) =
        (((x - 1) * D x : ℝ) : ℂ) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      rw [(hZH x hx).2]
      have : ((H x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hHpos x hx).ne'
      simp only [hDdef]
      push_cast
      field_simp
    have hlim2 : Tendsto (fun x : ℝ => (((x - 1) * D x : ℝ) : ℂ)) (𝓝[>] 1) (𝓝 (c * P / ((H 1 : ℝ) : ℂ))) :=
      (hdiv.congr' hev)
    have hre := (Complex.continuous_re.tendsto _).comp hlim2
    have him := (Complex.continuous_im.tendsto _).comp hlim2
    simp only [Function.comp_def, Complex.ofReal_re, Complex.ofReal_im] at hre him
    have him0 : (c * P / ((H 1 : ℝ) : ℂ)).im = 0 := tendsto_nhds_unique tendsto_const_nhds him |>.symm
    have hne : c * P / ((H 1 : ℝ) : ℂ) ≠ 0 := div_ne_zero (mul_ne_zero hc hP) hH0
    have hnn : 0 ≤ (c * P / ((H 1 : ℝ) : ℂ)).re := by
      refine ge_of_tendsto hre ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx' : (1 : ℝ) < x := hx
      have h1 := (hprod x hx').2
      exact mul_nonneg (by linarith) (by linarith)
    refine ⟨_, lt_of_le_of_ne hnn fun h0 => hne (Complex.ext h0.symm him0), hre⟩

end GlobalTheory.RSPole
