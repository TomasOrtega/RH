import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.LaTIsPrime

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField IsLocalRing

/- English proof (translation)
Use `set P := laT D N la with hP`. Establish `hp0 : la.asIdeal ≠ ⊥` using `la.ne_bot`. Establish `hp1 : la.asIdeal ≠ ⊤` using `la.isPrime.ne_top`. Choose the witnesses or unpack the hypotheses as in `⟨π, hπp, hπ2⟩ : ∃ π ∈ la.asIdeal, π ∉ la.asIdeal ^ 2 := by`. Establish `hlt : la.asIdeal ^ 2 < la.asIdeal ^ 1` using `Ideal.pow_right_strictAnti la.asIdeal hp0 hp1 (by norm_num : 1 < 2)`.

Rewrite `hlt` using `[pow_one]`. Take `⟨x, hx, hx2⟩` from `SetLike.exists_of_lt hlt`. Conclude with `⟨x, hx, hx2⟩`. Establish `hmemP : ∀ t : 𝓞 K, MvPolynomial.C t ∈ P ↔ t ∈ la.asIdeal`. Introduce `t`.

Rewrite using `[hP, laT, MvPolynomial.mem_map_C_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Simplify using `using h 0`. Introduce `h m`.

Rewrite using `[MvPolynomial.coeff_C]`. Use `split_ifs`. Conclude with `h`. Conclude with `zero_mem _`. Establish `hdiv : ∀ a ∈ la.asIdeal, ∃ t c : 𝓞 K, t ∉ la.asIdeal ∧ t * a = π * c`.

Introduce `a ha`. Establish `hle : Ideal.span {π} ≤ la.asIdeal` using `(Ideal.span_singleton_le_iff_mem _).mpr hπp`. Take `⟨J, hJ⟩` from `Ideal.dvd_iff_le.mpr hle`. Establish `hJp : ¬ J ≤ la.asIdeal`. Introduce `hJle`.

Apply `hπ2` to reduce the goal to its premises. Establish `hsq : Ideal.span {π} ≤ la.asIdeal ^ 2`. Rewrite using `[hJ, pow_two]`. Conclude with `Ideal.mul_mono_right hJle`. Conclude with `hsq (Ideal.mem_span_singleton_self π)`.

Take `⟨t, htJ, htp⟩` from `SetLike.not_le_iff_exists.mp hJp`. Establish `hta : t * a ∈ Ideal.span {π}`. Rewrite using `[hJ, mul_comm t a]`. Conclude with `Ideal.mul_mem_mul ha htJ`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.mp hta`.

Conclude with `⟨t, c, htp, by rw [← hc, mul_comm]⟩`. Use `haveI : IsNoetherianRing (Op D N la) := IsLocalization.isNoetherianRing P.primeCompl (Op D N la) inferInstance`. Set `f : 𝓞 K →+* Op D N la` to `(algebraMap (OT K D N) (Op D N la)).comp MvPolynomial.C`. Establish `hmax : IsLocalRing.maximalIdeal (Op D N la) = Ideal.map f la.asIdeal`. Establish `e : Ideal.map f la.asIdeal = Ideal.map (algebraMap (OT K D N) (Op D N la)) (laT D N la)` using `(Ideal.map_map (MvPolynomial.C : 𝓞 K →+* OT K D N) (algebraMap (OT K D N) (Op D N la))).symm`.

Rewrite using `[e]`. Conclude with `(Localization.AtPrime.map_eq_maximalIdeal).symm`. Establish `hπm : IsLocalRing.maximalIdeal (Op D N la) = Ideal.span {f π}`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[hmax, Ideal.map_le_iff_le_comap]`.

Introduce `a ha`. Rewrite using `[Ideal.mem_comap]`. Take `⟨t, c, htp, htc⟩` from `hdiv a ha`. Establish `hu : IsUnit (f t)` using `(IsLocalization.AtPrime.isUnit_to_map_iff (Op D N la) P (MvPolynomial.C t)).mpr (fun h => htp ((hmemP t).mp h))`. Take `⟨u, hu'⟩` from `hu`.

Rewrite using `[Ideal.mem_span_singleton']`. Use `⟨↑u⁻¹ * f c, ?_⟩` and prove the remaining obligations. Establish `hfm : f t * f a = f π * f c` using `by rw [← map_mul, ← map_mul, htc]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff, hmax]`.

Conclude with `Ideal.mem_map_of_mem f hπp`. Establish `hnf : ¬ IsField (Op D N la)`. Introduce `hF`. Establish `hb` using `IsLocalRing.isField_iff_maximalIdeal_eq.mp hF`. Rewrite `hb` using `[hπm, Ideal.span_singleton_eq_bot]`.

Establish `hπ0 : π ≠ 0` using `fun h => hπ2 (h ▸ zero_mem _)`. Establish `hinj : Function.Injective (algebraMap (OT K D N) (Op D N la))` using `IsLocalization.injective (Op D N la) (Ideal.primeCompl_le_nonZeroDivisors P)`. Conclude with `hπ0 (MvPolynomial.C_injective _ _ ((hinj (hb.trans (map_zero _).symm)).trans (map_zero _).symm))`. Establish `hprin : (IsLocalRing.maximalIdeal (Op D N la)).IsPrincipal` using `⟨⟨f π, hπm⟩⟩`. Conclude with `((IsDiscreteValuationRing.TFAE (Op D N la) hnf).out 0 4).mpr hprin`.
-/
theorem Op_isDVR {K : Type} [Field K] [NumberField K] (D N : ℕ)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : IsDiscreteValuationRing (Op D N la) := by
  classical
  set P := laT D N la with hP
  have hp0 : la.asIdeal ≠ ⊥ := la.ne_bot
  have hp1 : la.asIdeal ≠ ⊤ := la.isPrime.ne_top

  obtain ⟨π, hπp, hπ2⟩ : ∃ π ∈ la.asIdeal, π ∉ la.asIdeal ^ 2 := by
    have hlt : la.asIdeal ^ 2 < la.asIdeal ^ 1 :=
      Ideal.pow_right_strictAnti la.asIdeal hp0 hp1 (by norm_num : 1 < 2)
    rw [pow_one] at hlt
    obtain ⟨x, hx, hx2⟩ := SetLike.exists_of_lt hlt
    exact ⟨x, hx, hx2⟩
  have hmemP : ∀ t : 𝓞 K, MvPolynomial.C t ∈ P ↔ t ∈ la.asIdeal := by
    intro t
    rw [hP, laT, MvPolynomial.mem_map_C_iff]
    constructor
    · intro h
      simpa using h 0
    · intro h m
      rw [MvPolynomial.coeff_C]
      split_ifs
      · exact h
      · exact zero_mem _

  have hdiv : ∀ a ∈ la.asIdeal, ∃ t c : 𝓞 K, t ∉ la.asIdeal ∧ t * a = π * c := by
    intro a ha
    have hle : Ideal.span {π} ≤ la.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr hπp
    obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hle
    have hJp : ¬ J ≤ la.asIdeal := by
      intro hJle
      apply hπ2
      have hsq : Ideal.span {π} ≤ la.asIdeal ^ 2 := by
        rw [hJ, pow_two]
        exact Ideal.mul_mono_right hJle
      exact hsq (Ideal.mem_span_singleton_self π)
    obtain ⟨t, htJ, htp⟩ := SetLike.not_le_iff_exists.mp hJp
    have hta : t * a ∈ Ideal.span {π} := by
      rw [hJ, mul_comm t a]
      exact Ideal.mul_mem_mul ha htJ
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hta
    exact ⟨t, c, htp, by rw [← hc, mul_comm]⟩
  haveI : IsNoetherianRing (Op D N la) :=
    IsLocalization.isNoetherianRing P.primeCompl (Op D N la) inferInstance
  let f : 𝓞 K →+* Op D N la := (algebraMap (OT K D N) (Op D N la)).comp MvPolynomial.C
  have hmax : IsLocalRing.maximalIdeal (Op D N la) = Ideal.map f la.asIdeal := by
    have e : Ideal.map f la.asIdeal =
        Ideal.map (algebraMap (OT K D N) (Op D N la)) (laT D N la) :=
      (Ideal.map_map (MvPolynomial.C : 𝓞 K →+* OT K D N) (algebraMap (OT K D N) (Op D N la))).symm
    rw [e]
    exact (Localization.AtPrime.map_eq_maximalIdeal).symm
  have hπm : IsLocalRing.maximalIdeal (Op D N la) = Ideal.span {f π} := by
    apply le_antisymm
    · rw [hmax, Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap]
      obtain ⟨t, c, htp, htc⟩ := hdiv a ha
      have hu : IsUnit (f t) :=
        (IsLocalization.AtPrime.isUnit_to_map_iff (Op D N la) P (MvPolynomial.C t)).mpr
          (fun h => htp ((hmemP t).mp h))
      obtain ⟨u, hu'⟩ := hu
      rw [Ideal.mem_span_singleton']
      refine ⟨↑u⁻¹ * f c, ?_⟩
      have hfm : f t * f a = f π * f c := by rw [← map_mul, ← map_mul, htc]
      calc ↑u⁻¹ * f c * f π = ↑u⁻¹ * (f π * f c) := by ring
        _ = ↑u⁻¹ * (f t * f a) := by rw [hfm]
        _ = f a := by rw [← hu', ← mul_assoc, Units.inv_mul, one_mul]
    · rw [Ideal.span_le, Set.singleton_subset_iff, hmax]
      exact Ideal.mem_map_of_mem f hπp
  have hnf : ¬ IsField (Op D N la) := by
    intro hF
    have hb := IsLocalRing.isField_iff_maximalIdeal_eq.mp hF
    rw [hπm, Ideal.span_singleton_eq_bot] at hb
    have hπ0 : π ≠ 0 := fun h => hπ2 (h ▸ zero_mem _)
    have hinj : Function.Injective (algebraMap (OT K D N) (Op D N la)) :=
      IsLocalization.injective (Op D N la) (Ideal.primeCompl_le_nonZeroDivisors P)
    exact hπ0 (MvPolynomial.C_injective _ _ ((hinj (hb.trans (map_zero _).symm)).trans
      (map_zero _).symm))
  have hprin : (IsLocalRing.maximalIdeal (Op D N la)).IsPrincipal := ⟨⟨f π, hπm⟩⟩
  exact ((IsDiscreteValuationRing.TFAE (Op D N la) hnf).out 0 4).mpr hprin

end ReciprocityTheory.ChartRestriction.G.T0
