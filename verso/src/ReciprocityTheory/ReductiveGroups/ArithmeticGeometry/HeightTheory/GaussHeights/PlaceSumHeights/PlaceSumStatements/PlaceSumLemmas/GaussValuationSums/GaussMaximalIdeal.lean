import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.LaTIsPrime

namespace PI.HtPlacesSumWork

open NumberField IsLocalRing ReciprocityTheory.ChartRestriction.G.T0

variable {K : Type} [Field K] [NumberField K] (D N : ℕ)
  (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h' : (MvPolynomial.C s : ReciprocityTheory.ChartRestriction.G.T0.OT K D N) ∈ Ideal.map (MvPolynomial.C : 𝓞 K →+* ReciprocityTheory.ChartRestriction.G.T0.OT K D N) la.asIdeal` using `h`. Establish `h0` using `(MvPolynomial.mem_map_C_iff.mp h') 0`. Simplify using `using h0`.

Introduce `h`. Conclude with `Ideal.mem_map_of_mem _ h`.
-/
theorem gauss_C_mem_iff (s : 𝓞 K) :
    (MvPolynomial.C s : OT K D N) ∈ laT D N la ↔ s ∈ la.asIdeal := by
  constructor
  · intro h
    have h' : (MvPolynomial.C s : ReciprocityTheory.ChartRestriction.G.T0.OT K D N) ∈
        Ideal.map (MvPolynomial.C : 𝓞 K →+* ReciprocityTheory.ChartRestriction.G.T0.OT K D N) la.asIdeal := h
    have h0 := (MvPolynomial.mem_map_C_iff.mp h') 0
    simpa using h0
  · intro h
    exact Ideal.mem_map_of_mem _ h

/- English proof (translation)
Establish `hp0 : la.asIdeal ≠ ⊥` using `la.ne_bot`. Establish `hp1 : la.asIdeal ≠ ⊤` using `la.isPrime.ne_top`. Establish `hlt : la.asIdeal ^ 2 < la.asIdeal`. Use `Ideal.pow_right_strictAnti la.asIdeal hp0 hp1 (show 1 < 2 by norm_num)` as an intermediate fact. Simplify using `using this`.

Take `⟨π, hπ, hπ2⟩` from `SetLike.exists_of_lt hlt`. Establish `hπ0 : π ≠ 0`. Introduce and unpack `rfl`. Conclude with `hπ2 (Ideal.zero_mem _)`. Take `⟨J, hJ⟩ : la.asIdeal ∣ Ideal.span {π}` from `Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hπ)`.

Establish `hJp : ¬ J ≤ la.asIdeal`. Introduce `hle`. Apply `hπ2` to reduce the goal to its premises. Establish `h1 : π ∈ la.asIdeal * J`. Rewrite using `[← hJ]`.

Conclude with `Ideal.mem_span_singleton_self π`. Establish `h2 : la.asIdeal * J ≤ la.asIdeal ^ 2`. Rewrite using `[pow_two]`. Conclude with `Ideal.mul_mono_right hle`. Conclude with `h2 h1`.

Take `⟨s, hsJ, hsp⟩` from `SetLike.not_le_iff_exists.mp hJp`. Use `⟨π, hπ, hπ0, s, hsp, fun a ha => ?_⟩` and prove the remaining obligations. Establish `hmem : a * s ∈ Ideal.span {π}`. Rewrite using `[hJ]`. Conclude with `Ideal.mul_mem_mul ha hsJ`.

Take `⟨b, hb⟩` from `Ideal.mem_span_singleton'.mp hmem`. Conclude with `⟨b, by rw [mul_comm s a, ← hb, mul_comm]⟩`.
-/
theorem gauss_unif : ∃ π ∈ la.asIdeal, π ≠ 0 ∧ ∃ s ∉ la.asIdeal,
    ∀ a ∈ la.asIdeal, ∃ b, s * a = π * b := by
  have hp0 : la.asIdeal ≠ ⊥ := la.ne_bot
  have hp1 : la.asIdeal ≠ ⊤ := la.isPrime.ne_top
  have hlt : la.asIdeal ^ 2 < la.asIdeal := by
    have := Ideal.pow_right_strictAnti la.asIdeal hp0 hp1 (show 1 < 2 by norm_num)
    simpa using this
  obtain ⟨π, hπ, hπ2⟩ := SetLike.exists_of_lt hlt
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact hπ2 (Ideal.zero_mem _)
  obtain ⟨J, hJ⟩ : la.asIdeal ∣ Ideal.span {π} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hπ)
  have hJp : ¬ J ≤ la.asIdeal := by
    intro hle
    apply hπ2
    have h1 : π ∈ la.asIdeal * J := by
      rw [← hJ]; exact Ideal.mem_span_singleton_self π
    have h2 : la.asIdeal * J ≤ la.asIdeal ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mono_right hle
    exact h2 h1
  obtain ⟨s, hsJ, hsp⟩ := SetLike.not_le_iff_exists.mp hJp
  refine ⟨π, hπ, hπ0, s, hsp, fun a ha => ?_⟩
  have hmem : a * s ∈ Ideal.span {π} := by
    rw [hJ]; exact Ideal.mul_mem_mul ha hsJ
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hmem
  exact ⟨b, by rw [mul_comm s a, ← hb, mul_comm]⟩

/- English proof (translation)
The claim follows from `IsLocalization.injective (M := (ReciprocityTheory.ChartRestriction.G.T0.laT D N la).primeCompl) (S := ReciprocityTheory.ChartRestriction.G.T0.Op D N la) (Ideal.primeCompl_le_nonZeroDivisors _)`.
-/
theorem gauss_inj : Function.Injective (algebraMap (OT K D N) (Op D N la)) :=
  IsLocalization.injective (M := (ReciprocityTheory.ChartRestriction.G.T0.laT D N la).primeCompl)
    (S := ReciprocityTheory.ChartRestriction.G.T0.Op D N la) (Ideal.primeCompl_le_nonZeroDivisors _)

/- English proof (translation)
Rewrite using `[← Localization.AtPrime.map_eq_maximalIdeal (I := ReciprocityTheory.ChartRestriction.G.T0.laT D N la)]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Ideal.map_le_iff_le_comap] show Ideal.map (MvPolynomial.C : 𝓞 K →+* ReciprocityTheory.ChartRestriction.G.T0.OT K D N) la.asIdeal ≤ _`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `a ha`.

Rewrite using `[Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_span_singleton']`. Take `⟨b, hb⟩` from `h a ha`. Establish `hsP : (MvPolynomial.C s : ReciprocityTheory.ChartRestriction.G.T0.OT K D N) ∈ (ReciprocityTheory.ChartRestriction.G.T0.laT D N la).primeCompl` using `fun hm => hs ((gauss_C_mem_iff D N la s).mp hm)`. Take `⟨u, hu⟩` from `IsLocalization.map_units (S := ReciprocityTheory.ChartRestriction.G.T0.Op D N la) (⟨_, hsP⟩ : (ReciprocityTheory.ChartRestriction.G.T0.laT D N la).primeCompl)`. Establish `key` using `congrArg (fun t => algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N) (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) (MvPolynomial.C t)) hb`.

Simplify using `only [map_mul] at key`. Establish `hu' : (u : ReciprocityTheory.ChartRestriction.G.T0.Op D N la) = algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N) (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) (MvPolynomial.C s)` using `hu`. Use `⟨(↑u⁻¹ : ReciprocityTheory.ChartRestriction.G.T0.Op D N la) * algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N) (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) (MvPolynomial.C b), ?_⟩` and prove the remaining obligations. Use `symm`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← mul_assoc, Units.inv_mul, one_mul]`. Use `_ = _ := by rw [hu', key]; ring`. Rewrite using `[Ideal.span_singleton_le_iff_mem]`. Conclude with `Ideal.mem_map_of_mem _ ((gauss_C_mem_iff D N la π).mpr hπ)`.
-/
theorem gauss_maximalIdeal {π : 𝓞 K} (hπ : π ∈ la.asIdeal) {s : 𝓞 K} (hs : s ∉ la.asIdeal)
    (h : ∀ a ∈ la.asIdeal, ∃ b, s * a = π * b) :
    maximalIdeal (Op D N la) =
      Ideal.span {algebraMap (OT K D N) (Op D N la) (MvPolynomial.C π)} := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal (I := ReciprocityTheory.ChartRestriction.G.T0.laT D N la)]
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    show Ideal.map (MvPolynomial.C : 𝓞 K →+* ReciprocityTheory.ChartRestriction.G.T0.OT K D N) la.asIdeal ≤ _
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_span_singleton']
    obtain ⟨b, hb⟩ := h a ha
    have hsP : (MvPolynomial.C s : ReciprocityTheory.ChartRestriction.G.T0.OT K D N) ∈ (ReciprocityTheory.ChartRestriction.G.T0.laT D N la).primeCompl :=
      fun hm => hs ((gauss_C_mem_iff D N la s).mp hm)
    obtain ⟨u, hu⟩ := IsLocalization.map_units (S := ReciprocityTheory.ChartRestriction.G.T0.Op D N la)
      (⟨_, hsP⟩ : (ReciprocityTheory.ChartRestriction.G.T0.laT D N la).primeCompl)
    have key := congrArg (fun t => algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N)
      (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) (MvPolynomial.C t)) hb
    simp only [map_mul] at key
    have hu' : (u : ReciprocityTheory.ChartRestriction.G.T0.Op D N la) = algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N)
        (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) (MvPolynomial.C s) := hu
    refine ⟨(↑u⁻¹ : ReciprocityTheory.ChartRestriction.G.T0.Op D N la) * algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N)
      (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) (MvPolynomial.C b), ?_⟩
    symm
    calc algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N) (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) (MvPolynomial.C a)
        = (↑u⁻¹ : ReciprocityTheory.ChartRestriction.G.T0.Op D N la) * ((u : ReciprocityTheory.ChartRestriction.G.T0.Op D N la) *
          algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N) (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) (MvPolynomial.C a)) := by
          rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = _ := by rw [hu', key]; ring
  · rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_map_of_mem _ ((gauss_C_mem_iff D N la π).mpr hπ)

/- English proof (translation)
Take `⟨π, hπ, hπ0, s, hs, h⟩` from `gauss_unif la`. Establish `hmax` using `gauss_maximalIdeal D N la hπ hs h`. Establish `: IsDomain (ReciprocityTheory.ChartRestriction.G.T0.Op D N la)` using `IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors _)`. Establish `: IsNoetherianRing (ReciprocityTheory.ChartRestriction.G.T0.Op D N la)` using `IsLocalization.isNoetherianRing (ReciprocityTheory.ChartRestriction.G.T0.laT D N la).primeCompl _ inferInstance`. Establish `hne : algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N) (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) (MvPolynomial.C π) ≠ 0`.

Introduce `h0`. Apply `hπ0` to reduce the goal to its premises. Establish `h1` using `gauss_inj D N la (h0.trans (map_zero _).symm)`. Simplify using `using h1`. Establish `hnf : ¬ IsField (ReciprocityTheory.ChartRestriction.G.T0.Op D N la)`.

Introduce `hF`. Establish `hmem : algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N) (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) (MvPolynomial.C π) ∈ maximalIdeal (ReciprocityTheory.ChartRestriction.G.T0.Op D N la)`. Rewrite using `[hmax]`. Conclude with `Ideal.mem_span_singleton_self _`. Take `⟨y, hy⟩` from `hF.mul_inv_cancel hne`.

Conclude with `(IsLocalRing.mem_maximalIdeal _).mp hmem (isUnit_iff_exists_inv.mpr ⟨y, hy⟩)`. Establish `hprin : (maximalIdeal (ReciprocityTheory.ChartRestriction.G.T0.Op D N la)).IsPrincipal` using `⟨⟨_, hmax⟩⟩`. Conclude with `((IsDiscreteValuationRing.TFAE (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) hnf).out 0 4).mpr hprin`.
-/
theorem gauss_dvr : IsDiscreteValuationRing (Op D N la) := by
  obtain ⟨π, hπ, hπ0, s, hs, h⟩ := gauss_unif la
  have hmax := gauss_maximalIdeal D N la hπ hs h
  have : IsDomain (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors _)
  have : IsNoetherianRing (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) :=
    IsLocalization.isNoetherianRing (ReciprocityTheory.ChartRestriction.G.T0.laT D N la).primeCompl _ inferInstance
  have hne : algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N) (ReciprocityTheory.ChartRestriction.G.T0.Op D N la)
      (MvPolynomial.C π) ≠ 0 := by
    intro h0
    apply hπ0
    have h1 := gauss_inj D N la (h0.trans (map_zero _).symm)
    simpa using h1
  have hnf : ¬ IsField (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) := by
    intro hF
    have hmem : algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N) (ReciprocityTheory.ChartRestriction.G.T0.Op D N la)
        (MvPolynomial.C π) ∈ maximalIdeal (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) := by
      rw [hmax]; exact Ideal.mem_span_singleton_self _
    obtain ⟨y, hy⟩ := hF.mul_inv_cancel hne
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem (isUnit_iff_exists_inv.mpr ⟨y, hy⟩)
  have hprin : (maximalIdeal (ReciprocityTheory.ChartRestriction.G.T0.Op D N la)).IsPrincipal := ⟨⟨_, hmax⟩⟩
  exact ((IsDiscreteValuationRing.TFAE (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) hnf).out 0 4).mpr hprin

/- English proof (translation)
Rewrite using `[ReciprocityTheory.ChartRestriction.G.T0.OpToKT, IsLocalization.lift_eq, RingHom.comp_apply]`.
-/
theorem gauss_lift (x : OT K D N) :
    OpToKT D N la (algebraMap (OT K D N) (Op D N la) x) =
      algebraMap (KTp K D N) (KTf K D N) (OTtoKT K D N x) := by
  rw [ReciprocityTheory.ChartRestriction.G.T0.OpToKT, IsLocalization.lift_eq, RingHom.comp_apply]

/- English proof (translation)
Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K)) (p.support.image fun v => p.coeff v)`. Establish `hint_r : ∀ v ∈ p.support, ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = (b : 𝓞 K) • p.coeff v`. Introduce `v hv`. Conclude with `RingHom.mem_rangeS.mp (hb _ (Finset.mem_image_of_mem _ hv))`. Use `choose! g hg using hint_r`.

Use `⟨∑ v ∈ p.support, MvPolynomial.monomial v (g v), b, nonZeroDivisors.coe_ne_zero b, ?_⟩` and prove the remaining obligations. Rewrite using `[ReciprocityTheory.ChartRestriction.G.T0.OTtoKT, map_sum, MvPolynomial.map_C]`. Use `conv_rhs => rw [p.as_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun v hv => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.map_monomial, MvPolynomial.C_mul_monomial, hg v hv, Algebra.smul_def]`.
-/
theorem gauss_clear (p : KTp K D N) :
    ∃ x : OT K D N, ∃ n : 𝓞 K, n ≠ 0 ∧
      OTtoKT K D N x = OTtoKT K D N (MvPolynomial.C n) * p := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
    (p.support.image fun v => p.coeff v)
  have hint_r : ∀ v ∈ p.support, ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = (b : 𝓞 K) • p.coeff v := by
    intro v hv
    exact RingHom.mem_rangeS.mp (hb _ (Finset.mem_image_of_mem _ hv))
  choose! g hg using hint_r
  refine ⟨∑ v ∈ p.support, MvPolynomial.monomial v (g v), b, nonZeroDivisors.coe_ne_zero b, ?_⟩
  rw [ReciprocityTheory.ChartRestriction.G.T0.OTtoKT, map_sum, MvPolynomial.map_C]
  conv_rhs => rw [p.as_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [MvPolynomial.map_monomial, MvPolynomial.C_mul_monomial, hg v hv, Algebra.smul_def]

/- English proof (translation)
Use `letI := (ReciprocityTheory.ChartRestriction.G.T0.OpToKT D N la).toAlgebra`. Establish `: IsDomain (ReciprocityTheory.ChartRestriction.G.T0.Op D N la)` using `IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors _)`. Establish `intInj : Function.Injective (ReciprocityTheory.ChartRestriction.G.T0.OTtoKT K D N)` using `MvPolynomial.map_injective _ (IsFractionRing.injective (𝓞 K) K)`. Establish `fracInj : Function.Injective (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N))` using `IsFractionRing.injective (ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N)`. Establish `hCinj : ∀ k : 𝓞 K, k ≠ 0 → (MvPolynomial.C k : ReciprocityTheory.ChartRestriction.G.T0.OT K D N) ≠ 0` using `fun k hk hC => hk (by simpa using hC)`.

Establish `hfinj : Function.Injective (ReciprocityTheory.ChartRestriction.G.T0.OpToKT D N la)`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨⟨a, t⟩, rfl⟩` from `IsLocalization.mk'_surjective (ReciprocityTheory.ChartRestriction.G.T0.laT D N la).primeCompl x`. Establish `h1` using `congrArg (ReciprocityTheory.ChartRestriction.G.T0.OpToKT D N la) (IsLocalization.mk'_spec (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) a t)`.

Rewrite `h1` using `[map_mul, hx, zero_mul, gauss_lift]`. Establish `ha : a = 0`. Apply `intInj` to reduce the goal to its premises. Apply `fracInj` to reduce the goal to its premises. Rewrite using `[map_zero, map_zero]`.

Conclude with `h1.symm`. Substitute `ha` using the available equality. Use `show IsLocalization.mk' (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) (0 : ReciprocityTheory.ChartRestriction.G.T0.OT K D N) t = 0`. Rewrite using `[IsLocalization.mk'_zero]`. Use `⟨fun y => ?_, fun z => ?_, fun {x y} hxy => ?_⟩` and prove the remaining obligations.

Apply `isUnit_iff_ne_zero.mpr` to reduce the goal to its premises. Introduce `h0`. Conclude with `nonZeroDivisors.coe_ne_zero y (hfinj (h0.trans (map_zero _).symm))`. Take `⟨P, Q, hQ, rfl⟩` from `IsFractionRing.div_surjective (A := ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) z`. Take `⟨a, n, hn, ha⟩` from `gauss_clear D N P`.

Take `⟨b, m, hm, hb⟩` from `gauss_clear D N Q`. Establish `hQ0 : Q ≠ 0` using `nonZeroDivisors.ne_zero hQ`. Establish `hQ' : algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) Q ≠ 0` using `fun h0 => hQ0 (fracInj (h0.trans (map_zero _).symm))`. Establish `hb0 : b ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hb` using `[map_zero]`. Establish `hc : ReciprocityTheory.ChartRestriction.G.T0.OTtoKT K D N (MvPolynomial.C m) = 0`. Break down `mul_eq_zero.mp hb.symm with hc | hc` into its components or cases. Conclude with `hc`. Conclude with `absurd hc hQ0`.

Conclude with `hCinj m hm (intInj (hc.trans (map_zero _).symm))`. Establish `hden : algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N) (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) (b * MvPolynomial.C n) ∈ nonZeroDivisors (ReciprocityTheory.ChartRestriction.G.T0.Op D N la)` using `mem_nonZeroDivisors_of_ne_zero fun h0 => (mul_ne_zero hb0 (hCinj n hn)) (gauss_inj D N la (h0.trans (map_zero _).symm))`. Use `⟨⟨algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N) (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) (a * MvPolynomial.C m), ⟨_, hden⟩⟩, ?_⟩` and prove the remaining obligations. Use `show algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) P / algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) Q * ReciprocityTheory.ChartRestriction.G. …`. Rewrite using `[gauss_lift, gauss_lift]`.

Simplify using `only [map_mul, ha, hb]`. Rewrite using `[div_mul_eq_mul_div, div_eq_iff hQ']`. Expand and normalize the polynomial expressions, which then agree. Conclude with `⟨1, by rw [hfinj hxy]⟩`.
-/
theorem gauss_frac :
    letI := (OpToKT D N la).toAlgebra
    IsFractionRing (Op D N la) (KTf K D N) := by
  letI := (ReciprocityTheory.ChartRestriction.G.T0.OpToKT D N la).toAlgebra
  have : IsDomain (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors _)
  have intInj : Function.Injective (ReciprocityTheory.ChartRestriction.G.T0.OTtoKT K D N) :=
    MvPolynomial.map_injective _ (IsFractionRing.injective (𝓞 K) K)
  have fracInj : Function.Injective (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N)) :=
    IsFractionRing.injective (ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N)
  have hCinj : ∀ k : 𝓞 K, k ≠ 0 → (MvPolynomial.C k : ReciprocityTheory.ChartRestriction.G.T0.OT K D N) ≠ 0 :=
    fun k hk hC => hk (by simpa using hC)
  have hfinj : Function.Injective (ReciprocityTheory.ChartRestriction.G.T0.OpToKT D N la) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective (ReciprocityTheory.ChartRestriction.G.T0.laT D N la).primeCompl x
    have h1 := congrArg (ReciprocityTheory.ChartRestriction.G.T0.OpToKT D N la)
      (IsLocalization.mk'_spec (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) a t)
    rw [map_mul, hx, zero_mul, gauss_lift] at h1
    have ha : a = 0 := by
      apply intInj
      apply fracInj
      rw [map_zero, map_zero]
      exact h1.symm
    subst ha
    show IsLocalization.mk' (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) (0 : ReciprocityTheory.ChartRestriction.G.T0.OT K D N) t = 0
    rw [IsLocalization.mk'_zero]
  refine ⟨fun y => ?_, fun z => ?_, fun {x y} hxy => ?_⟩
  · apply isUnit_iff_ne_zero.mpr
    intro h0
    exact nonZeroDivisors.coe_ne_zero y (hfinj (h0.trans (map_zero _).symm))
  · obtain ⟨P, Q, hQ, rfl⟩ := IsFractionRing.div_surjective (A := ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) z
    obtain ⟨a, n, hn, ha⟩ := gauss_clear D N P
    obtain ⟨b, m, hm, hb⟩ := gauss_clear D N Q
    have hQ0 : Q ≠ 0 := nonZeroDivisors.ne_zero hQ
    have hQ' : algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) Q ≠ 0 :=
      fun h0 => hQ0 (fracInj (h0.trans (map_zero _).symm))
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [map_zero] at hb
      have hc : ReciprocityTheory.ChartRestriction.G.T0.OTtoKT K D N (MvPolynomial.C m) = 0 := by
        rcases mul_eq_zero.mp hb.symm with hc | hc
        · exact hc
        · exact absurd hc hQ0
      exact hCinj m hm (intInj (hc.trans (map_zero _).symm))
    have hden : algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N) (ReciprocityTheory.ChartRestriction.G.T0.Op D N la)
        (b * MvPolynomial.C n) ∈ nonZeroDivisors (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) :=
      mem_nonZeroDivisors_of_ne_zero fun h0 => (mul_ne_zero hb0 (hCinj n hn))
        (gauss_inj D N la (h0.trans (map_zero _).symm))
    refine ⟨⟨algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N) (ReciprocityTheory.ChartRestriction.G.T0.Op D N la)
      (a * MvPolynomial.C m), ⟨_, hden⟩⟩, ?_⟩
    show algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) P /
        algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) Q *
        ReciprocityTheory.ChartRestriction.G.T0.OpToKT D N la (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N)
          (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) (b * MvPolynomial.C n)) =
      ReciprocityTheory.ChartRestriction.G.T0.OpToKT D N la (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N)
          (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) (a * MvPolynomial.C m))
    rw [gauss_lift, gauss_lift]
    simp only [map_mul, ha, hb]
    rw [div_mul_eq_mul_div, div_eq_iff hQ']
    ring
  · exact ⟨1, by rw [hfinj hxy]⟩

end PI.HtPlacesSumWork
