import Mathlib
import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHeckeLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open IsDedekindDomain NumberField IdeleGroup Topology Filter
open scoped GroundTheory.LocalField.Abstract

noncomputable section

namespace DirichletHecke

open _root_.GroundTheory.Global.Cyclotomic GroundTheory.LocalField.Abstract RationalSymbol

/- English proof (translation)
Rewrite using `[Ideal.absNorm_span_singleton, ← map_natCast (algebraMap ℤ (𝓞 ℚ)) m, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one, Int.natAbs_natCast]`.
-/
theorem absNorm_span_natCast (m : ℕ) : Ideal.absNorm (Ideal.span {(m : 𝓞 ℚ)}) = m := by
  rw [Ideal.absNorm_span_singleton, ← map_natCast (algebraMap ℤ (𝓞 ℚ)) m, Algebra.norm_algebraMap,
    NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one, Int.natAbs_natCast]

/- English proof (translation)
Take `⟨k, hk⟩` from `(IsPrincipalIdealRing.principal (I.map Rat.ringOfIntegersEquiv)).principal`. Use `⟨k.natAbs, ?_⟩` and prove the remaining obligations. Establish `hI : I = (I.map Rat.ringOfIntegersEquiv).map Rat.ringOfIntegersEquiv.symm` using `(Ideal.map_of_equiv _).symm`. Rewrite using `[hI, hk, Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton, show Rat.ringOfIntegersEquiv.symm k = (k : 𝓞 ℚ) from eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) k]`. Break down `Int.natAbs_eq k with h | h` into its components or cases.

Rewrite using `[h, Int.cast_natCast, Int.natAbs_natCast]`. Rewrite using `[h, Int.natAbs_neg, Int.natAbs_natCast, Int.cast_neg, Int.cast_natCast, Ideal.span_singleton_neg]`.
-/
theorem exists_eq_span_natCast (I : Ideal (𝓞 ℚ)) : ∃ m : ℕ, I = Ideal.span {(m : 𝓞 ℚ)} := by
  obtain ⟨k, hk⟩ := (IsPrincipalIdealRing.principal (I.map Rat.ringOfIntegersEquiv)).principal
  refine ⟨k.natAbs, ?_⟩
  have hI : I = (I.map Rat.ringOfIntegersEquiv).map Rat.ringOfIntegersEquiv.symm :=
    (Ideal.map_of_equiv _).symm
  rw [hI, hk, Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton,
    show Rat.ringOfIntegersEquiv.symm k = (k : 𝓞 ℚ) from
      eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) k]
  rcases Int.natAbs_eq k with h | h
  · rw [h, Int.cast_natCast, Int.natAbs_natCast]
  · rw [h, Int.natAbs_neg, Int.natAbs_natCast, Int.cast_neg, Int.cast_natCast, Ideal.span_singleton_neg]

/- English proof (translation)
Take `⟨m, rfl⟩` from `exists_eq_span_natCast I`. Rewrite `h` using `[absNorm_span_natCast]`. Rewrite using `[h]`.
-/
theorem eq_span_of_absNorm_eq {I : Ideal (𝓞 ℚ)} {n : ℕ} (h : Ideal.absNorm I = n) :
    I = Ideal.span {(n : 𝓞 ℚ)} := by
  obtain ⟨m, rfl⟩ := exists_eq_span_natCast I
  rw [absNorm_span_natCast] at h
  rw [h]

/- English proof (translation)
Rewrite using `[asIdeal_eq_span, absNorm_span_natCast]`.
-/
theorem absNorm_asIdeal (v : HeightOneSpectrum (𝓞 ℚ)) : Ideal.absNorm v.asIdeal = prime v := by
  rw [asIdeal_eq_span, absNorm_span_natCast]

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

/- English proof (translation)
Distinguish the cases in `hv : prime v ∣ N`. Rewrite using `[(heckeCharacter χ).coeff_asIdeal_of_dvd (dvd_conductor_of_dvd χ hχ hv)]`. Use `(MulChar.map_nonunit χ fun hu ↦ ?_).symm` and prove the remaining obligations. Rewrite `hu` using `[ZMod.isUnit_iff_coprime]`. Conclude with `(Nat.Prime.coprime_iff_not_dvd Fact.out).1 hu hv`.

Rewrite using `[(heckeCharacter χ).coeff_asIdeal_of_not_dvd (not_dvd_conductor_of_not_dvd χ hv)]`. Conclude with `coe_idealCharacter_primeIdealUnit χ hv`.
-/
theorem coeff_asIdeal (hχ : χ.IsPrimitive) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (heckeCharacter χ).coeff v.asIdeal = χ (prime v) := by
  by_cases hv : prime v ∣ N
  · rw [(heckeCharacter χ).coeff_asIdeal_of_dvd (dvd_conductor_of_dvd χ hχ hv)]
    refine (MulChar.map_nonunit χ fun hu ↦ ?_).symm
    rw [ZMod.isUnit_iff_coprime] at hu
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).1 hu hv
  · rw [(heckeCharacter χ).coeff_asIdeal_of_not_dvd (not_dvd_conductor_of_not_dvd χ hv)]
    exact coe_idealCharacter_primeIdealUnit χ hv

/- English proof (translation)
Proceed by induction on `n using Nat.recOnMul with`. Consider the case `zero => exact absurd rfl hn`. Consider the case `one => rw [Nat.cast_one, Ideal.span_singleton_one, (heckeCharacter χ).coeff_top, Nat.cast_one, map_one]`. Consider the case `prime p hp`. Establish `hv : prime (placeOf ⟨p, hp⟩) = p` using `prime_placeOf ⟨p, hp⟩`.

Establish `h` using `coeff_asIdeal χ hχ (placeOf ⟨p, hp⟩)`. Rewrite `h` using `[asIdeal_eq_span, hv]`. Conclude with `h`. Consider the case `mul a b ha hb`. Establish `ha0 : a ≠ 0` using `left_ne_zero_of_mul hn`.

Establish `hb0 : b ≠ 0` using `right_ne_zero_of_mul hn`. Rewrite using `[Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton, (heckeCharacter χ).coeff_mul, ha ha0, hb hb0, Nat.cast_mul, map_mul]`.
-/
theorem coeff_span_natCast (hχ : χ.IsPrimitive) {n : ℕ} (hn : n ≠ 0) :
    (heckeCharacter χ).coeff (Ideal.span {(n : 𝓞 ℚ)}) = χ n := by
  induction n using Nat.recOnMul with
  | zero => exact absurd rfl hn
  | one => rw [Nat.cast_one, Ideal.span_singleton_one, (heckeCharacter χ).coeff_top, Nat.cast_one, map_one]
  | prime p hp =>
    have hv : prime (placeOf ⟨p, hp⟩) = p := prime_placeOf ⟨p, hp⟩
    have h := coeff_asIdeal χ hχ (placeOf ⟨p, hp⟩)
    rw [asIdeal_eq_span, hv] at h
    exact h
  | mul a b ha hb =>
    have ha0 : a ≠ 0 := left_ne_zero_of_mul hn
    have hb0 : b ≠ 0 := right_ne_zero_of_mul hn
    rw [Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton, (heckeCharacter χ).coeff_mul, ha ha0,
      hb hb0, Nat.cast_mul, map_mul]

/- English proof (translation)
Rewrite using `[HeckeCharacter.LCoeff, tsum_eq_single (⟨Ideal.span {(n : 𝓞 ℚ)}, absNorm_span_natCast n⟩ : {I : Ideal (𝓞 ℚ) // Ideal.absNorm I = n}) fun I hI ↦ absurd (Subtype.ext (eq_span_of_absNorm_eq I.2)) hI]`. Conclude with `coeff_span_natCast χ hχ hn`.
-/
theorem LCoeff_eq (hχ : χ.IsPrimitive) {n : ℕ} (hn : n ≠ 0) : (heckeCharacter χ).LCoeff n = χ n := by
  rw [HeckeCharacter.LCoeff, tsum_eq_single (⟨Ideal.span {(n : 𝓞 ℚ)}, absNorm_span_natCast n⟩ :
      {I : Ideal (𝓞 ℚ) // Ideal.absNorm I = n}) fun I hI ↦
      absurd (Subtype.ext (eq_span_of_absNorm_eq I.2)) hI]
  exact coeff_span_natCast χ hχ hn

/- English proof (translation)
Rewrite using `[DirichletCharacter.LFunction_eq_LSeries χ hs, HeckeCharacter.LFunction]`. Conclude with `LSeries_congr (fun hn ↦ LCoeff_eq χ hχ hn) s`.
-/
theorem LFunction_heckeCharacter (hχ : χ.IsPrimitive) {s : ℂ} (hs : 1 < s.re) :
    (heckeCharacter χ).LFunction s = DirichletCharacter.LFunction χ s := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs, HeckeCharacter.LFunction]
  exact LSeries_congr (fun hn ↦ LCoeff_eq χ hχ hn) s

/- English proof (translation)
Rewrite using `[← LFunction_heckeCharacter χ hχ hs]`. Use `(heckeCharacter χ).LFunction_hasProd_all hs using 3 with v` and compare the differences between its conclusion and the goal. Rewrite using `[coeff_asIdeal χ hχ v, absNorm_asIdeal]`.
-/
theorem hasProd_eulerFactor (hχ : χ.IsPrimitive) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : HeightOneSpectrum (𝓞 ℚ) ↦ (1 - χ (prime v) * (prime v : ℂ) ^ (-s))⁻¹)
      (DirichletCharacter.LFunction χ s) := by
  rw [← LFunction_heckeCharacter χ hχ hs]
  convert (heckeCharacter χ).LFunction_hasProd_all hs using 3 with v
  rw [coeff_asIdeal χ hχ v, absNorm_asIdeal]

/- English proof (translation)
Use `(hH.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hD.analyticOnNhd hU) hpc h2 ?_` and prove the remaining obligations. Establish `hopen : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ)` using `(isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)`. Use `filter_upwards [hopen] with s hs`. Rewrite using `[HeckeCharacter.continuedLFunction_eq _ hs, LFunction_heckeCharacter χ hχ hs]`.
-/
theorem eqOn_continuedLFunction (hχ : χ.IsPrimitive) {U : Set ℂ} (hU : IsOpen U)
    (hpc : IsPreconnected U) (h2 : (2 : ℂ) ∈ U)
    (hH : DifferentiableOn ℂ (heckeCharacter χ).continuedLFunction U)
    (hD : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) U) :
    Set.EqOn (heckeCharacter χ).continuedLFunction (DirichletCharacter.LFunction χ) U := by
  refine (hH.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hD.analyticOnNhd hU) hpc h2 ?_
  have hopen : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [hopen] with s hs
  rw [HeckeCharacter.continuedLFunction_eq _ hs, LFunction_heckeCharacter χ hχ hs]

/- English proof (translation)
The claim follows from `(hS.isPathConnected_compl_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)).isConnected.isPreconnected`.
-/
theorem isPreconnected_compl_of_countable {S : Set ℂ} (hS : S.Countable) : IsPreconnected Sᶜ :=
  (hS.isPathConnected_compl_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)).isConnected.isPreconnected

/- English proof (translation)
Distinguish the cases in `hτ : ∃ τ : ℝ, ∀ x : IdeleGroup ℚ, ((heckeCharacter χ).toIdele x : ℂ) = ((ideleModule ℚ x : ℝ) : ℂ) ^ ((τ : ℂ) * Complex.I)`. Take `⟨τ, hτ⟩` from `hτ set s0 : ℂ := 1 - (τ : ℂ) * Complex.I with hs0`. Establish `hU : IsOpen ({1, s0} : Set ℂ)ᶜ` using `(Set.toFinite _).isClosed.isOpen_compl`. Establish `h2 : (2 : ℂ) ∈ ({1, s0} : Set ℂ)ᶜ`. Simplify using `only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]`.

Use `⟨by norm_num, fun h ↦ ?_⟩` and prove the remaining obligations. Use `congrArg Complex.re h` as an intermediate fact. Simplify using `[hs0] at this`. Establish `heq` using `eqOn_continuedLFunction χ hχ hU (isPreconnected_compl_of_countable (Set.toFinite _).countable) h2 ((HeckeCharacter.differentiableOn_continuedLFunction_of_forall hτ).mono fun z hz ↦ by`. Simplify using `only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz ⊢`.

Conclude with `hz.2)`. Use the proof step `(fun z hz ↦ (DirichletCharacter.differentiableAt_LFunction χ z (Or.inl (by`. Simplify using `only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz`. Conclude with `hz.1))).differentiableWithinAt)`. Establish `hnhds : ({1, s0} : Set ℂ)ᶜ ∈ 𝓝[≠] s0`.

Distinguish the cases in `h1 : s0 = 1`. Rewrite using `[h1, Set.pair_eq_singleton]`. Conclude with `self_mem_nhdsWithin`. Establish `hA : ({1} : Set ℂ)ᶜ ∈ 𝓝[≠] s0` using `nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds (show s0 ∈ ({1} : Set ℂ)ᶜ from h1)) filter_upwards [hA, self_mem_nhdsWithin] with z hz1 hz2`. Simplify using `only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz1 hz2 ⊢`.

Conclude with `⟨hz1, hz2⟩`. Establish `key : s0 = 1 ∧ χ = 1`. Assume the negation of the conclusion as `hne`. Establish `hd : s0 ≠ 1 ∨ χ ≠ 1` using `by tauto`. Establish `hDs0 : ContinuousAt (DirichletCharacter.LFunction χ) s0` using `(DirichletCharacter.differentiableAt_LFunction χ s0 hd).continuousAt`.

Establish `h0 : Tendsto (fun z ↦ (z - s0) * DirichletCharacter.LFunction χ z) (𝓝[≠] s0) (𝓝 0)`. Establish `hc : ContinuousAt (fun z ↦ (z - s0) * DirichletCharacter.LFunction χ z) s0` using `(continuousAt_id.sub continuousAt_const).mul hDs0`. Use `hc.tendsto.mono_left (nhdsWithin_le_nhds (s := ({s0} : Set ℂ)ᶜ))` as an intermediate fact. Simplify using `using this`. Establish `hR` using `HeckeCharacter.tendsto_sub_mul_continuedLFunction_of_forall hτ`.

Establish `hev : (fun z ↦ (z - s0) * (heckeCharacter χ).continuedLFunction z) =ᶠ[𝓝[≠] s0] (fun z ↦ (z - s0) * DirichletCharacter.LFunction χ z)` using `by filter_upwards [hnhds] with z hz`. Rewrite using `[heq hz]`. Conclude with `HeckeCharacter.residue_continuedLFunction_ne_zero (tendsto_nhds_unique (hR.congr' hev) h0)`. Take `⟨hs01, hχ1⟩` from `key`. Establish `hs1 : s ≠ 1` using `hs.resolve_right (not_not.2 hχ1)`.

Use `heq ?_` and prove the remaining obligations. Simplify using `only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]`. Conclude with `⟨hs1, hs01 ▸ hs1⟩`. Establish `hH` using `(HeckeCharacter.differentiable_continuedLFunction _ hτ).differentiableOn (s := Set.univ)`. Distinguish the cases in `hχ1 : χ = 1`.

Establish `hs1 : s ≠ 1` using `hs.resolve_right (not_not.2 hχ1)`. Use `eqOn_continuedLFunction χ hχ isOpen_compl_singleton (isPreconnected_compl_of_countable (Set.countable_singleton 1)) (by norm_num) (hH.mono (Set.subset_univ _)) (fun z hz ↦ (DirichletCharacter.differentiableAt_LFunction χ z (Or.inl hz)).differentiableWithinAt) hs1` and prove the remaining obligations. Conclude with `eqOn_continuedLFunction χ hχ isOpen_univ isPreconnected_univ (Set.mem_univ _) hH (DirichletCharacter.differentiable_LFunction hχ1).differentiableOn (Set.mem_univ s)`.
-/
theorem continuedLFunction_heckeCharacter (hχ : χ.IsPrimitive) {s : ℂ} (hs : s ≠ 1 ∨ χ ≠ 1) :
    (heckeCharacter χ).continuedLFunction s = DirichletCharacter.LFunction χ s := by
  by_cases hτ : ∃ τ : ℝ, ∀ x : IdeleGroup ℚ,
      ((heckeCharacter χ).toIdele x : ℂ) = ((ideleModule ℚ x : ℝ) : ℂ) ^ ((τ : ℂ) * Complex.I)
  · obtain ⟨τ, hτ⟩ := hτ
    set s0 : ℂ := 1 - (τ : ℂ) * Complex.I with hs0
    have hU : IsOpen ({1, s0} : Set ℂ)ᶜ := (Set.toFinite _).isClosed.isOpen_compl
    have h2 : (2 : ℂ) ∈ ({1, s0} : Set ℂ)ᶜ := by
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      refine ⟨by norm_num, fun h ↦ ?_⟩
      have := congrArg Complex.re h
      simp [hs0] at this
    have heq := eqOn_continuedLFunction χ hχ hU
      (isPreconnected_compl_of_countable (Set.toFinite _).countable) h2
      ((HeckeCharacter.differentiableOn_continuedLFunction_of_forall hτ).mono fun z hz ↦ by
        simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz ⊢
        exact hz.2)
      (fun z hz ↦ (DirichletCharacter.differentiableAt_LFunction χ z (Or.inl (by
        simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz
        exact hz.1))).differentiableWithinAt)
    have hnhds : ({1, s0} : Set ℂ)ᶜ ∈ 𝓝[≠] s0 := by
      by_cases h1 : s0 = 1
      · rw [h1, Set.pair_eq_singleton]
        exact self_mem_nhdsWithin
      · have hA : ({1} : Set ℂ)ᶜ ∈ 𝓝[≠] s0 :=
          nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds (show s0 ∈ ({1} : Set ℂ)ᶜ from h1))
        filter_upwards [hA, self_mem_nhdsWithin] with z hz1 hz2
        simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz1 hz2 ⊢
        exact ⟨hz1, hz2⟩
    have key : s0 = 1 ∧ χ = 1 := by
      by_contra hne
      have hd : s0 ≠ 1 ∨ χ ≠ 1 := by tauto
      have hDs0 : ContinuousAt (DirichletCharacter.LFunction χ) s0 :=
        (DirichletCharacter.differentiableAt_LFunction χ s0 hd).continuousAt
      have h0 : Tendsto (fun z ↦ (z - s0) * DirichletCharacter.LFunction χ z) (𝓝[≠] s0) (𝓝 0) := by
        have hc : ContinuousAt (fun z ↦ (z - s0) * DirichletCharacter.LFunction χ z) s0 :=
          (continuousAt_id.sub continuousAt_const).mul hDs0
        have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := ({s0} : Set ℂ)ᶜ))
        simpa using this
      have hR := HeckeCharacter.tendsto_sub_mul_continuedLFunction_of_forall hτ
      have hev : (fun z ↦ (z - s0) * (heckeCharacter χ).continuedLFunction z) =ᶠ[𝓝[≠] s0]
          (fun z ↦ (z - s0) * DirichletCharacter.LFunction χ z) := by
        filter_upwards [hnhds] with z hz
        rw [heq hz]
      exact HeckeCharacter.residue_continuedLFunction_ne_zero (tendsto_nhds_unique (hR.congr' hev) h0)
    obtain ⟨hs01, hχ1⟩ := key
    have hs1 : s ≠ 1 := hs.resolve_right (not_not.2 hχ1)
    refine heq ?_
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hs1, hs01 ▸ hs1⟩
  · have hH := (HeckeCharacter.differentiable_continuedLFunction _ hτ).differentiableOn (s := Set.univ)
    by_cases hχ1 : χ = 1
    · have hs1 : s ≠ 1 := hs.resolve_right (not_not.2 hχ1)
      refine eqOn_continuedLFunction χ hχ isOpen_compl_singleton
        (isPreconnected_compl_of_countable (Set.countable_singleton 1)) (by norm_num)
        (hH.mono (Set.subset_univ _))
        (fun z hz ↦ (DirichletCharacter.differentiableAt_LFunction χ z (Or.inl hz)).differentiableWithinAt)
        hs1
    · exact eqOn_continuedLFunction χ hχ isOpen_univ isPreconnected_univ (Set.mem_univ _) hH
        (DirichletCharacter.differentiable_LFunction hχ1).differentiableOn (Set.mem_univ s)

end DirichletHecke

end

end GroundTheory.Global
