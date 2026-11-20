import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.DimensionQuotientBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.PrimeAvoidanceFibre

namespace ReciprocityTheory.ChartRestriction.G.T0.DiscreteValuationPoint

open IsLocalRing

/- English proof (translation)
Conclude with `(IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.1`.
-/
private theorem irreducible_mem_maximalIdeal {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ) : ϖ ∈ maximalIdeal O := by
  exact (IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.1

/- English proof (translation)
Introduce `h`. Establish `h1 : x • (1 : B) = x • (0 : B)` using `by simp [Algebra.smul_def, h]`. Conclude with `one_ne_zero ((Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B) (mem_nonZeroDivisors_of_ne_zero hx)) h1)`.
-/
private theorem algebraMap_ne_zero_of_flat' {O B : Type} [CommRing O] [IsDomain O] [CommRing B] [IsDomain B]
    [Algebra O B] [Module.Flat O B] {x : O} (hx : x ≠ 0) : algebraMap O B x ≠ 0 := by
  intro h
  have h1 : x • (1 : B) = x • (0 : B) := by simp [Algebra.smul_def, h]
  exact one_ne_zero ((Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B)
    (mem_nonZeroDivisors_of_ne_zero hx)) h1)

/- English proof (translation)
Rewrite using `[RingHom.injective_iff_ker_eq_bot]`. Assume the negation of the conclusion as `hne`. Establish `hmax : (RingHom.ker (algebraMap O T)).IsMaximal`. Conclude with `Ideal.IsPrime.isMaximal (RingHom.ker_isPrime (algebraMap O T)) hne`. Establish `hk : RingHom.ker (algebraMap O T) = maximalIdeal O` using `IsLocalRing.eq_maximalIdeal hmax`.

Apply `h` to reduce the goal to its premises. Rewrite using `[← RingHom.mem_ker, hk]`. Conclude with `irreducible_mem_maximalIdeal hϖ`.
-/
private theorem algebraMap_injective_of_uniformizer_ne_zero {O T : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing T] [IsDomain T] [Algebra O T] {ϖ : O} (hϖ : Irreducible ϖ)
    (h : algebraMap O T ϖ ≠ 0) : Function.Injective (algebraMap O T) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hne
  have hmax : (RingHom.ker (algebraMap O T)).IsMaximal := by
    exact Ideal.IsPrime.isMaximal (RingHom.ker_isPrime (algebraMap O T)) hne
  have hk : RingHom.ker (algebraMap O T) = maximalIdeal O := IsLocalRing.eq_maximalIdeal hmax
  apply h
  rw [← RingHom.mem_ker, hk]
  exact irreducible_mem_maximalIdeal hϖ

/- English proof (translation)
Establish `hle : Submonoid.powers s ≤ nonZeroDivisors R` using `powers_le_nonZeroDivisors_of_noZeroDivisors hs`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `IsLocalization.isDomain_localization hle`. Conclude with `IsLocalization.isNoetherianRing (Submonoid.powers s) (Localization.Away s) inferInstance`. Establish `h1 : Algebra.FiniteType R (Localization.Away s)` using `by infer_instance`.

Conclude with `Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType O R) h1`. Conclude with `IsLocalization.injective (Localization.Away s) hle`.
-/
private theorem localization_away_domain_noetherian_finiteType {O R : Type} [CommRing O] [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Algebra O R] [Algebra.FiniteType O R] (s : R) (hs : s ≠ 0) :
    IsDomain (Localization.Away s) ∧ IsNoetherianRing (Localization.Away s) ∧
      Algebra.FiniteType O (Localization.Away s) ∧
      Function.Injective (algebraMap R (Localization.Away s)) := by
  have hle : Submonoid.powers s ≤ nonZeroDivisors R :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact IsLocalization.isDomain_localization hle
  · exact IsLocalization.isNoetherianRing (Submonoid.powers s) (Localization.Away s) inferInstance
  · have h1 : Algebra.FiniteType R (Localization.Away s) := by
      infer_instance
    exact Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType O R) h1
  · exact IsLocalization.injective (Localization.Away s) hle

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨y, a, ha, rfl⟩`. Use `isUnit_iff_ne_zero.2 ?_` and prove the remaining obligations. Introduce `h`. Apply `nonZeroDivisors.ne_zero ha` to reduce the goal to its premises.

Apply `hinj` to reduce the goal to its premises. Apply `IsFractionRing.injective T (FractionRing T)` to reduce the goal to its premises. Simplify using `using h`. Introduce `z`. Take `⟨⟨a, b⟩, hab⟩` from `IsLocalization.surj (nonZeroDivisors T) z`.

Simplify using `only at hab`. Establish `hb0 : (b : T) ≠ 0` using `nonZeroDivisors.ne_zero b.2`. Establish `hc : (Ideal.span {(b : T)}).comap (algebraMap O T) ≠ ⊥`. Conclude with `Ideal.comap_ne_bot_of_integral_mem hb0 (Ideal.mem_span_singleton_self (b : T)) (Algebra.IsIntegral.isIntegral (b : T))`. Take `⟨c, hcmem, hc0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hc`.

Rewrite `hcmem` using `[Ideal.mem_comap, Ideal.mem_span_singleton']`. Take `⟨d, hd⟩` from `hcmem`. Use `⟨⟨a * d, ⟨algebraMap O T c, c, mem_nonZeroDivisors_of_ne_zero hc0, rfl⟩⟩, ?_⟩` and prove the remaining obligations. Use `show z * algebraMap T (FractionRing T) (algebraMap O T c) = algebraMap T (FractionRing T) (a * d)`. Rewrite using `[← hd, map_mul, map_mul, mul_comm (algebraMap T (FractionRing T) d), ← mul_assoc, hab]`.

Introduce `x y h`. Conclude with `⟨1, by simpa using IsFractionRing.injective T (FractionRing T) h⟩`.
-/
private theorem isLocalization_fractionRing_of_isIntegral {O T : Type} [CommRing O] [IsDomain O] [CommRing T] [IsDomain T]
    [Algebra O T] [Algebra.IsIntegral O T] (hinj : Function.Injective (algebraMap O T)) :
    IsLocalization (Algebra.algebraMapSubmonoid T (nonZeroDivisors O)) (FractionRing T) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, a, ha, rfl⟩
    refine isUnit_iff_ne_zero.2 ?_
    intro h
    apply nonZeroDivisors.ne_zero ha
    apply hinj
    apply IsFractionRing.injective T (FractionRing T)
    simpa using h
  · intro z
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors T) z
    dsimp only at hab
    have hb0 : (b : T) ≠ 0 := nonZeroDivisors.ne_zero b.2
    have hc : (Ideal.span {(b : T)}).comap (algebraMap O T) ≠ ⊥ := by
      exact Ideal.comap_ne_bot_of_integral_mem hb0 (Ideal.mem_span_singleton_self (b : T))
        (Algebra.IsIntegral.isIntegral (b : T))
    obtain ⟨c, hcmem, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
    rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hcmem
    obtain ⟨d, hd⟩ := hcmem
    refine ⟨⟨a * d, ⟨algebraMap O T c, c, mem_nonZeroDivisors_of_ne_zero hc0, rfl⟩⟩, ?_⟩
    show z * algebraMap T (FractionRing T) (algebraMap O T c) = algebraMap T (FractionRing T) (a * d)
    rw [← hd, map_mul, map_mul, mul_comm (algebraMap T (FractionRing T) d), ← mul_assoc, hab]
  · intro x y h
    exact ⟨1, by simpa using IsFractionRing.injective T (FractionRing T) h⟩

/- English proof (translation)
Use `haveI : NoZeroSMulDivisors O (FractionRing T) := by`. Establish `hi : Function.Injective (algebraMap O (FractionRing T))`. Rewrite using `[IsScalarTower.algebraMap_eq O T (FractionRing T)]`. Conclude with `(IsFractionRing.injective T (FractionRing T)).comp hinj`. Conclude with `⟨fun {c x} h => by`.

Rewrite `h` using `[Algebra.smul_def, mul_eq_zero]`. Conclude with `h.imp_left (fun h' => hi (h'.trans (map_zero _).symm))⟩`. Use `letI : Algebra (FractionRing O) (FractionRing T) := FractionRing.liftAlgebra O (FractionRing T)`. Use `haveI : IsScalarTower O (FractionRing O) (FractionRing T) := FractionRing.isScalarTower_liftAlgebra O (FractionRing T)`. Use `haveI : IsLocalization (Algebra.algebraMapSubmonoid T (nonZeroDivisors O)) (FractionRing T) := isLocalization_fractionRing_of_isIntegral hinj`.

Use `haveI : FiniteDimensional (FractionRing O) (FractionRing T) := Module.Finite.of_isLocalization O T (Rₚ := FractionRing O) (Sₚ := FractionRing T) (nonZeroDivisors O)`. Use `haveI : CharZero (FractionRing O) := by infer_instance`. Use `haveI : Algebra.IsSeparable (FractionRing O) (FractionRing T) := by infer_instance`. Use `haveI : IsDedekindDomain (integralClosure O (FractionRing T)) := by infer_instance`. Use `haveI : Module.Finite O (integralClosure O (FractionRing T)) := by`.

Conclude with `IsIntegralClosure.finite O (FractionRing O) (FractionRing T) (integralClosure O (FractionRing T))`. Use `⟨integralClosure O (FractionRing T), inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, (IsScalarTower.toAlgHom O T (FractionRing T)).codRestrict _ ?_, ?_⟩` and prove the remaining obligations. Introduce `t`. Conclude with `(Algebra.IsIntegral.isIntegral t).map (IsScalarTower.toAlgHom O T (FractionRing T))`. Introduce `a b h`.

Conclude with `IsFractionRing.injective T (FractionRing T) (congrArg Subtype.val h)`.
-/
private theorem exists_dedekind_embedding_of_finite {O T : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CharZero O] [CommRing T] [IsDomain T] [Algebra O T] [Module.Finite O T]
    (hinj : Function.Injective (algebraMap O T)) :
    ∃ (C : Type) (_ : CommRing C) (_ : IsDomain C) (_ : IsDedekindDomain C) (_ : Algebra O C)
      (_ : Module.Finite O C) (ψ : T →ₐ[O] C), Function.Injective ψ := by
  classical
  haveI : NoZeroSMulDivisors O (FractionRing T) := by
    have hi : Function.Injective (algebraMap O (FractionRing T)) := by
      rw [IsScalarTower.algebraMap_eq O T (FractionRing T)]
      exact (IsFractionRing.injective T (FractionRing T)).comp hinj
    exact ⟨fun {c x} h => by
      rw [Algebra.smul_def, mul_eq_zero] at h
      exact h.imp_left (fun h' => hi (h'.trans (map_zero _).symm))⟩
  letI : Algebra (FractionRing O) (FractionRing T) := FractionRing.liftAlgebra O (FractionRing T)
  haveI : IsScalarTower O (FractionRing O) (FractionRing T) :=
    FractionRing.isScalarTower_liftAlgebra O (FractionRing T)
  haveI : IsLocalization (Algebra.algebraMapSubmonoid T (nonZeroDivisors O)) (FractionRing T) :=
    isLocalization_fractionRing_of_isIntegral hinj
  haveI : FiniteDimensional (FractionRing O) (FractionRing T) :=
    Module.Finite.of_isLocalization O T (Rₚ := FractionRing O) (Sₚ := FractionRing T)
      (nonZeroDivisors O)
  haveI : CharZero (FractionRing O) := by
    infer_instance
  haveI : Algebra.IsSeparable (FractionRing O) (FractionRing T) := by
    infer_instance
  haveI : IsDedekindDomain (integralClosure O (FractionRing T)) := by
    infer_instance
  haveI : Module.Finite O (integralClosure O (FractionRing T)) := by
    exact IsIntegralClosure.finite O (FractionRing O) (FractionRing T)
      (integralClosure O (FractionRing T))
  refine ⟨integralClosure O (FractionRing T), inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance,
    (IsScalarTower.toAlgHom O T (FractionRing T)).codRestrict _ ?_, ?_⟩
  · intro t
    exact (Algebra.IsIntegral.isIntegral t).map (IsScalarTower.toAlgHom O T (FractionRing T))
  · intro a b h
    exact IsFractionRing.injective T (FractionRing T) (congrArg Subtype.val h)

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `hϖm : ϖ ∈ maximalIdeal O` using `irreducible_mem_maximalIdeal hϖ`. Establish `hϖ0 : algebraMap O C ϖ ≠ 0` using `fun h => hϖ.ne_zero (hinj (h.trans (map_zero _).symm))`. Take `⟨N, hNmax⟩` from `Ideal.exists_maximal C`. Use `haveI := hNmax`.

Establish `hϖN : algebraMap O C ϖ ∈ N`. Establish `hc : (N.comap (algebraMap O C)).IsMaximal`. Conclude with `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal N`. Rewrite using `[← Ideal.mem_comap, IsLocalRing.eq_maximalIdeal hc]`. Conclude with `hϖm`.

Establish `hch : ∀ P : Ideal C, P.IsPrime → ⊥ ≤ P → P ≤ N → algebraMap O C ϖ ∈ P → P = N`. Introduce `P hP _ hPN hϖP`. Establish `hP0 : P ≠ ⊥` using `fun h => hϖ0 (by rw [h] at hϖP; exact (Submodule.mem_bot C).1 hϖP)`. Conclude with `(Ideal.IsPrime.isMaximal hP hP0).eq_of_le hNmax.ne_top hPN`. Take `⟨s, hsN, hs⟩` from `ReciprocityTheory.ChartRestriction.G.T0.PrimeAvoidanceFibre.avoid N ⊥ (algebraMap O C ϖ) hch`.

Establish `hs0 : s ≠ 0` using `fun h => hsN (h ▸ N.zero_mem)`. Use `haveI : Algebra.FiniteType O C := by infer_instance`. Take `⟨hVd, hVn, hVf, hVi⟩` from `localization_away_domain_noetherian_finiteType (O := O) s hs0`. Establish `hϖV : algebraMap O (Localization.Away s) ϖ = algebraMap C (Localization.Away s) (algebraMap O C ϖ)` using `IsScalarTower.algebraMap_apply O C _ ϖ`. Establish `key : ∀ P : Ideal (Localization.Away s), P.IsPrime → algebraMap O (Localization.Away s) ϖ ∈ P → P = Ideal.map (algebraMap C (Localization.Away s)) N`.

Introduce `P hP hϖP`. Use `haveI := hP`. Establish `hQ : P.comap (algebraMap C (Localization.Away s)) = N`. Apply `hs` to reduce the goal to its premises. Use `infer_instance`.

Conclude with `bot_le`. Rewrite using `[Ideal.mem_comap, ← hϖV]`. Conclude with `hϖP`. Introduce `h`. Rewrite `h` using `[Ideal.mem_comap]`.

Conclude with `hP.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit s))`. Rewrite using `[← hQ]`. Rewrite using `[IsLocalization.map_comap (Submonoid.powers s)]`. Establish `hdisj : Disjoint (Submonoid.powers s : Set C) (N : Set C)`. Rewrite using `[Set.disjoint_left]`.

Introduce and unpack `x ⟨n, rfl⟩ hx`. Conclude with `hsN (hNmax.isPrime.mem_of_pow_mem n hx)`. Establish `hP0 : (Ideal.map (algebraMap C (Localization.Away s)) N).IsPrime`. Conclude with `IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers s) _ N hNmax.isPrime hdisj`. Establish `hϖmem : algebraMap O (Localization.Away s) ϖ ∈ Ideal.map (algebraMap C (Localization.Away s)) N`.

Rewrite using `[hϖV]`. Conclude with `Ideal.mem_map_of_mem _ hϖN`. Use `haveI : Module.Finite O (Localization.Away s) := by`. Use `ReciprocityTheory.ChartRestriction.G.T0.PrimeAvoidanceFibre.finite_of_fibre ϖ hϖ ⟨_, hP0, hϖmem⟩ ?_` and prove the remaining obligations. Introduce `P P' hP hP' h1 h2`.

Rewrite using `[key P hP h1, key P' hP' h2]`. Establish `hinjV : Function.Injective (algebraMap O (Localization.Away s))`. Rewrite using `[IsScalarTower.algebraMap_eq O C (Localization.Away s)]`. Conclude with `hVi.comp hinj`. Establish `hnz : ∀ P : Ideal (Localization.Away s), P.IsPrime → P ≠ ⊥ → algebraMap O (Localization.Away s) ϖ ∈ P`.

Introduce `P hP hP0'`. Use `haveI := hP`. Establish `hc : P.comap (algebraMap O (Localization.Away s)) ≠ ⊥`. Take `⟨x, hxP, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hP0'`. Conclude with `Ideal.comap_ne_bot_of_integral_mem hx0 hxP (Algebra.IsIntegral.isIntegral x)`.

Establish `hm` using `IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal inferInstance hc)`. Rewrite using `[← Ideal.mem_comap, hm]`. Conclude with `hϖm`. Establish `hdvr : IsDiscreteValuationRing (Localization.Away s)` using `by haveI : IsDedekindDomain (Localization.Away s) := by`. Conclude with `IsLocalization.isDedekindDomain C (powers_le_nonZeroDivisors_of_noZeroDivisors hs0) _`.

Establish `hfin : {I : Ideal (Localization.Away s) | I.IsPrime}.Finite`. Apply `((Set.finite_singleton (Ideal.map (algebraMap C (Localization.Away s)) N)).insert ⊥).subset` to reduce the goal to its premises. Introduce `P hP`. Distinguish the cases in `h : P = ⊥`. Conclude with `Or.inl h`.

Conclude with `Or.inr (key P hP (hnz P hP h))`. Use `haveI : IsPrincipalIdealRing (Localization.Away s) := IsPrincipalIdealRing.of_finite_primes hfin`. Rewrite using `[IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime]`. Use `⟨inferInstance, _, ⟨?_, hP0⟩, ?_⟩` and prove the remaining obligations. Introduce `h`.

Rewrite `hϖmem` using `[h, Ideal.mem_bot]`. Conclude with `hϖ.ne_zero (hinjV (hϖmem.trans (map_zero _).symm))`. Introduce and unpack `P ⟨hP0', hP⟩`. Conclude with `key P hP (hnz P hP hP0')`. Conclude with `⟨Localization.Away s, inferInstance, hVd, hdvr, inferInstance, inferInstance, IsScalarTower.toAlgHom O C (Localization.Away s), hVi⟩`.
-/
private theorem exists_dvr_embedding_of_dedekind {O C : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O]
    [CommRing C] [IsDomain C] [IsDedekindDomain C] [Algebra O C] [Module.Finite O C]
    (hinj : Function.Injective (algebraMap O C)) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra O V)
      (_ : Module.Finite O V) (φ : C →ₐ[O] V), Function.Injective φ := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖm : ϖ ∈ maximalIdeal O := irreducible_mem_maximalIdeal hϖ
  have hϖ0 : algebraMap O C ϖ ≠ 0 := fun h => hϖ.ne_zero (hinj (h.trans (map_zero _).symm))
  obtain ⟨N, hNmax⟩ := Ideal.exists_maximal C
  haveI := hNmax
  have hϖN : algebraMap O C ϖ ∈ N := by
    have hc : (N.comap (algebraMap O C)).IsMaximal := by
      exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal N
    rw [← Ideal.mem_comap, IsLocalRing.eq_maximalIdeal hc]
    exact hϖm
  have hch : ∀ P : Ideal C, P.IsPrime → ⊥ ≤ P → P ≤ N → algebraMap O C ϖ ∈ P → P = N := by
    intro P hP _ hPN hϖP
    have hP0 : P ≠ ⊥ := fun h => hϖ0 (by rw [h] at hϖP; exact (Submodule.mem_bot C).1 hϖP)
    exact (Ideal.IsPrime.isMaximal hP hP0).eq_of_le hNmax.ne_top hPN
  obtain ⟨s, hsN, hs⟩ := ReciprocityTheory.ChartRestriction.G.T0.PrimeAvoidanceFibre.avoid N ⊥ (algebraMap O C ϖ) hch
  have hs0 : s ≠ 0 := fun h => hsN (h ▸ N.zero_mem)
  haveI : Algebra.FiniteType O C := by
    infer_instance
  obtain ⟨hVd, hVn, hVf, hVi⟩ := localization_away_domain_noetherian_finiteType (O := O) s hs0
  have hϖV : algebraMap O (Localization.Away s) ϖ =
      algebraMap C (Localization.Away s) (algebraMap O C ϖ) :=
    IsScalarTower.algebraMap_apply O C _ ϖ
  have key : ∀ P : Ideal (Localization.Away s), P.IsPrime →
      algebraMap O (Localization.Away s) ϖ ∈ P →
      P = Ideal.map (algebraMap C (Localization.Away s)) N := by
    intro P hP hϖP
    haveI := hP
    have hQ : P.comap (algebraMap C (Localization.Away s)) = N := by
      apply hs
      · infer_instance
      · exact bot_le
      · rw [Ideal.mem_comap, ← hϖV]
        exact hϖP
      · intro h
        rw [Ideal.mem_comap] at h
        exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit s))
    rw [← hQ]
    rw [IsLocalization.map_comap (Submonoid.powers s)]
  have hdisj : Disjoint (Submonoid.powers s : Set C) (N : Set C) := by
    rw [Set.disjoint_left]
    rintro x ⟨n, rfl⟩ hx
    exact hsN (hNmax.isPrime.mem_of_pow_mem n hx)
  have hP0 : (Ideal.map (algebraMap C (Localization.Away s)) N).IsPrime := by
    exact IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers s) _ N hNmax.isPrime hdisj
  have hϖmem : algebraMap O (Localization.Away s) ϖ ∈ Ideal.map (algebraMap C (Localization.Away s)) N := by
    rw [hϖV]
    exact Ideal.mem_map_of_mem _ hϖN
  haveI : Module.Finite O (Localization.Away s) := by
    refine ReciprocityTheory.ChartRestriction.G.T0.PrimeAvoidanceFibre.finite_of_fibre ϖ hϖ ⟨_, hP0, hϖmem⟩ ?_
    intro P P' hP hP' h1 h2
    rw [key P hP h1, key P' hP' h2]
  have hinjV : Function.Injective (algebraMap O (Localization.Away s)) := by
    rw [IsScalarTower.algebraMap_eq O C (Localization.Away s)]
    exact hVi.comp hinj
  have hnz : ∀ P : Ideal (Localization.Away s), P.IsPrime → P ≠ ⊥ →
      algebraMap O (Localization.Away s) ϖ ∈ P := by
    intro P hP hP0'
    haveI := hP
    have hc : P.comap (algebraMap O (Localization.Away s)) ≠ ⊥ := by
      obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0'
      exact Ideal.comap_ne_bot_of_integral_mem hx0 hxP (Algebra.IsIntegral.isIntegral x)
    have hm := IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal inferInstance hc)
    rw [← Ideal.mem_comap, hm]
    exact hϖm
  have hdvr : IsDiscreteValuationRing (Localization.Away s) := by
    haveI : IsDedekindDomain (Localization.Away s) := by
      exact IsLocalization.isDedekindDomain C (powers_le_nonZeroDivisors_of_noZeroDivisors hs0) _
    have hfin : {I : Ideal (Localization.Away s) | I.IsPrime}.Finite := by
      apply ((Set.finite_singleton (Ideal.map (algebraMap C (Localization.Away s)) N)).insert ⊥).subset
      intro P hP
      by_cases h : P = ⊥
      · exact Or.inl h
      · exact Or.inr (key P hP (hnz P hP h))
    haveI : IsPrincipalIdealRing (Localization.Away s) := IsPrincipalIdealRing.of_finite_primes hfin
    rw [IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime]
    refine ⟨inferInstance, _, ⟨?_, hP0⟩, ?_⟩
    · intro h
      rw [h, Ideal.mem_bot] at hϖmem
      exact hϖ.ne_zero (hinjV (hϖmem.trans (map_zero _).symm))
    · rintro P ⟨hP0', hP⟩
      exact key P hP (hnz P hP hP0')
  exact ⟨Localization.Away s, inferInstance, hVd, hdvr, inferInstance, inferInstance,
    IsScalarTower.toAlgHom O C (Localization.Away s), hVi⟩

/- English proof (translation)
Use `haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing O B`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `hϖm : ϖ ∈ maximalIdeal O` using `irreducible_mem_maximalIdeal hϖ`. Establish `hw0 : algebraMap O B ϖ ≠ 0` using `algebraMap_ne_zero_of_flat' hϖ.ne_zero`. Take `⟨M, hMmax, hMle⟩` from `Ideal.exists_le_maximal _ hsp`.

Use `haveI := hMmax`. Establish `hwM : algebraMap O B ϖ ∈ M` using `hMle (Ideal.mem_map_of_mem _ hϖm)`. Take `⟨q, hqp, hqM, heq, hwq, hch⟩` from `ReciprocityTheory.ChartRestriction.G.T0.DimensionQuotientBound.local_step M (algebraMap O B ϖ) e hwM hw0 he`. Take `⟨s, hsM, hs⟩` from `ReciprocityTheory.ChartRestriction.G.T0.PrimeAvoidanceFibre.avoid M q (algebraMap O B ϖ) hch`. Use `haveI := hqp`.

Establish `hsq : s ∉ q` using `fun h => hsM (hqM h)`. Establish `hsb : Ideal.Quotient.mk q s ≠ 0` using `fun h => hsq (Ideal.Quotient.eq_zero_iff_mem.1 h)`. Use `haveI : Algebra.FiniteType O (B ⧸ q) := by infer_instance`. Take `⟨hTd, hTn, hTf, hTi⟩` from `localization_away_domain_noetherian_finiteType (O := O) (Ideal.Quotient.mk q s) hsb`. Establish `hϖT : algebraMap O (Localization.Away (Ideal.Quotient.mk q s)) ϖ = algebraMap (B ⧸ q) (Localization.Away (Ideal.Quotient.mk q s)) (Ideal.Quotient.mk q (algebraMap O B ϖ))`.

Rewrite using `[IsScalarTower.algebraMap_apply O (B ⧸ q) (Localization.Away (Ideal.Quotient.mk q s))]`. Both sides reduce to the same expression. Establish `key : ∀ P : Ideal (Localization.Away (Ideal.Quotient.mk q s)), P.IsPrime → algebraMap O (Localization.Away (Ideal.Quotient.mk q s)) ϖ ∈ P → P = Ideal.map (algebraMap (B ⧸ q) (Localization.Away (Ideal.Quotient.mk q s))) (Ideal.map (Ideal.Quotient.mk q) M)`. Introduce `P hP hϖP`. Use `haveI := hP`.

Establish `hQ : (P.comap (algebraMap (B ⧸ q) (Localization.Away (Ideal.Quotient.mk q s)))).comap (Ideal.Quotient.mk q) = M`. Apply `hs` to reduce the goal to its premises. Use `infer_instance`. Introduce `x hx`. Rewrite using `[Ideal.mem_comap, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]`.

Conclude with `P.zero_mem`. Rewrite using `[Ideal.mem_comap, Ideal.mem_comap, ← hϖT]`. Conclude with `hϖP`. Introduce `h`. Rewrite `h` using `[Ideal.mem_comap, Ideal.mem_comap]`.

Conclude with `hP.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit _))`. Rewrite using `[← hQ, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]`. Rewrite using `[IsLocalization.map_comap (Submonoid.powers (Ideal.Quotient.mk q s))]`. Establish `hdisj : Disjoint (Submonoid.powers (Ideal.Quotient.mk q s) : Set (B ⧸ q)) (Ideal.map (Ideal.Quotient.mk q) M : Set (B ⧸ q))`. Rewrite using `[Set.disjoint_left]`.

Introduce and unpack `x ⟨n, rfl⟩ hx`. Simplify using `only at hx`. Rewrite `hx` using `[← map_pow]`. Apply `hsM` to reduce the goal to its premises. Apply `hMmax.isPrime.mem_of_pow_mem n` to reduce the goal to its premises.

Conclude with `(Ideal.mem_quotient_iff_mem hqM).1 hx`. Establish `hMq : (Ideal.map (Ideal.Quotient.mk q) M).IsPrime`. Conclude with `Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hqM)`. Establish `hP0 : (Ideal.map (algebraMap (B ⧸ q) (Localization.Away (Ideal.Quotient.mk q s))) (Ideal.map (Ideal.Quotient.mk q) M)).IsPrime`. Conclude with `IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (Ideal.Quotient.mk q s)) _ _ hMq hdisj`.

Use `haveI : Module.Finite O (Localization.Away (Ideal.Quotient.mk q s)) := by`. Use `ReciprocityTheory.ChartRestriction.G.T0.PrimeAvoidanceFibre.finite_of_fibre ϖ hϖ ⟨_, hP0, ?_⟩ ?_` and prove the remaining obligations. Rewrite using `[hϖT]`. Conclude with `Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hwM)`. Introduce `P P' hP hP' h1 h2`.

Rewrite using `[key P hP h1, key P' hP' h2]`. Use `⟨Localization.Away (Ideal.Quotient.mk q s), inferInstance, hTd, inferInstance, inferInstance, (IsScalarTower.toAlgHom O (B ⧸ q) (Localization.Away (Ideal.Quotient.mk q s))).comp (Ideal.Quotient.mkₐ O q), ?_, ?_⟩` and prove the remaining obligations. Apply `algebraMap_injective_of_uniformizer_ne_zero hϖ` to reduce the goal to its premises. Rewrite using `[hϖT]`. Introduce `h`.

Apply `hwq` to reduce the goal to its premises. Apply `Ideal.Quotient.eq_zero_iff_mem.1` to reduce the goal to its premises. Apply `hTi` to reduce the goal to its premises. Rewrite using `[h, map_zero]`. Introduce `h`.

Apply `heq` to reduce the goal to its premises. Apply `Ideal.Quotient.eq_zero_iff_mem.1` to reduce the goal to its premises. Apply `hTi` to reduce the goal to its premises. Rewrite using `[map_zero]`. Conclude with `h`.
-/
private theorem exists_finite_domain_quotient_ne_zero {O B : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O]
    [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B] [Module.Flat O B]
    (hsp : Ideal.map (algebraMap O B) (maximalIdeal O) ≠ ⊤) (e : B) (he : e ≠ 0) :
    ∃ (T : Type) (_ : CommRing T) (_ : IsDomain T) (_ : Algebra O T) (_ : Module.Finite O T)
      (g : B →ₐ[O] T), Function.Injective (algebraMap O T) ∧ g e ≠ 0 := by
  classical
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing O B
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖm : ϖ ∈ maximalIdeal O := irreducible_mem_maximalIdeal hϖ
  have hw0 : algebraMap O B ϖ ≠ 0 := algebraMap_ne_zero_of_flat' hϖ.ne_zero
  obtain ⟨M, hMmax, hMle⟩ := Ideal.exists_le_maximal _ hsp
  haveI := hMmax
  have hwM : algebraMap O B ϖ ∈ M := hMle (Ideal.mem_map_of_mem _ hϖm)
  obtain ⟨q, hqp, hqM, heq, hwq, hch⟩ :=
    ReciprocityTheory.ChartRestriction.G.T0.DimensionQuotientBound.local_step M (algebraMap O B ϖ) e hwM hw0 he
  obtain ⟨s, hsM, hs⟩ := ReciprocityTheory.ChartRestriction.G.T0.PrimeAvoidanceFibre.avoid M q (algebraMap O B ϖ) hch
  haveI := hqp
  have hsq : s ∉ q := fun h => hsM (hqM h)
  have hsb : Ideal.Quotient.mk q s ≠ 0 := fun h => hsq (Ideal.Quotient.eq_zero_iff_mem.1 h)
  haveI : Algebra.FiniteType O (B ⧸ q) := by
    infer_instance
  obtain ⟨hTd, hTn, hTf, hTi⟩ := localization_away_domain_noetherian_finiteType (O := O) (Ideal.Quotient.mk q s) hsb
  have hϖT : algebraMap O (Localization.Away (Ideal.Quotient.mk q s)) ϖ =
      algebraMap (B ⧸ q) (Localization.Away (Ideal.Quotient.mk q s))
        (Ideal.Quotient.mk q (algebraMap O B ϖ)) := by
    rw [IsScalarTower.algebraMap_apply O (B ⧸ q) (Localization.Away (Ideal.Quotient.mk q s))]
    rfl
  have key : ∀ P : Ideal (Localization.Away (Ideal.Quotient.mk q s)), P.IsPrime →
      algebraMap O (Localization.Away (Ideal.Quotient.mk q s)) ϖ ∈ P →
      P = Ideal.map (algebraMap (B ⧸ q) (Localization.Away (Ideal.Quotient.mk q s)))
        (Ideal.map (Ideal.Quotient.mk q) M) := by
    intro P hP hϖP
    haveI := hP
    have hQ : (P.comap (algebraMap (B ⧸ q) (Localization.Away (Ideal.Quotient.mk q s)))).comap
        (Ideal.Quotient.mk q) = M := by
      apply hs
      · infer_instance
      · intro x hx
        rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
        exact P.zero_mem
      · rw [Ideal.mem_comap, Ideal.mem_comap, ← hϖT]
        exact hϖP
      · intro h
        rw [Ideal.mem_comap, Ideal.mem_comap] at h
        exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit _))
    rw [← hQ, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    rw [IsLocalization.map_comap (Submonoid.powers (Ideal.Quotient.mk q s))]
  have hdisj : Disjoint (Submonoid.powers (Ideal.Quotient.mk q s) : Set (B ⧸ q))
      (Ideal.map (Ideal.Quotient.mk q) M : Set (B ⧸ q)) := by
    rw [Set.disjoint_left]
    rintro x ⟨n, rfl⟩ hx
    dsimp only at hx
    rw [← map_pow] at hx
    apply hsM
    apply hMmax.isPrime.mem_of_pow_mem n
    exact (Ideal.mem_quotient_iff_mem hqM).1 hx
  have hMq : (Ideal.map (Ideal.Quotient.mk q) M).IsPrime := by
    exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hqM)
  have hP0 : (Ideal.map (algebraMap (B ⧸ q) (Localization.Away (Ideal.Quotient.mk q s)))
      (Ideal.map (Ideal.Quotient.mk q) M)).IsPrime := by
    exact IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (Ideal.Quotient.mk q s))
      _ _ hMq hdisj
  haveI : Module.Finite O (Localization.Away (Ideal.Quotient.mk q s)) := by
    refine ReciprocityTheory.ChartRestriction.G.T0.PrimeAvoidanceFibre.finite_of_fibre ϖ hϖ ⟨_, hP0, ?_⟩ ?_
    · rw [hϖT]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hwM)
    · intro P P' hP hP' h1 h2
      rw [key P hP h1, key P' hP' h2]
  refine ⟨Localization.Away (Ideal.Quotient.mk q s), inferInstance, hTd, inferInstance,
    inferInstance, (IsScalarTower.toAlgHom O (B ⧸ q)
      (Localization.Away (Ideal.Quotient.mk q s))).comp (Ideal.Quotient.mkₐ O q), ?_, ?_⟩
  · apply algebraMap_injective_of_uniformizer_ne_zero hϖ
    rw [hϖT]
    intro h
    apply hwq
    apply Ideal.Quotient.eq_zero_iff_mem.1
    apply hTi
    rw [h, map_zero]
  · intro h
    apply heq
    apply Ideal.Quotient.eq_zero_iff_mem.1
    apply hTi
    rw [map_zero]
    exact h

/- English proof (translation)
Take `⟨T, iT1, iT2, familyTheoremThreeBound, iT4, g, hTinj, hge⟩` from `exists_finite_domain_quotient_ne_zero hsp e he`. Take `⟨C, indexCFirst, indexCSecond, iC3, iC4, iC5, ψ, hψ⟩` from `exists_dedekind_embedding_of_finite (O := O) (T := T) hTinj`. Establish `hCinj : Function.Injective (algebraMap O C)`. Introduce `a b h`. Apply `hTinj` to reduce the goal to its premises.

Apply `hψ` to reduce the goal to its premises. Rewrite using `[ψ.commutes, ψ.commutes]`. Conclude with `h`. Take `⟨V, indexVFirst, indexVSecond, indexVThird, indexVFourth, iV5, φ, hφ⟩` from `exists_dvr_embedding_of_dedekind (O := O) (C := C) hCinj`. Use `⟨V, indexVFirst, indexVSecond, indexVThird, indexVFourth, iV5, (φ.comp ψ).comp g, ?_⟩` and prove the remaining obligations.

Introduce `h`. Apply `hge` to reduce the goal to its premises. Apply `hψ` to reduce the goal to its premises. Apply `hφ` to reduce the goal to its premises. Rewrite using `[map_zero, map_zero]`.

Conclude with `h`.
-/
theorem exists_dvr_point_flat_algebra {O B : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B] [Module.Flat O B]
    (hsp : Ideal.map (algebraMap O B) (maximalIdeal O) ≠ ⊤) (e : B) (he : e ≠ 0) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra O V)
      (_ : Module.Finite O V) (φ : B →ₐ[O] V), φ e ≠ 0 := by
  obtain ⟨T, iT1, iT2, familyTheoremThreeBound, iT4, g, hTinj, hge⟩ := exists_finite_domain_quotient_ne_zero hsp e he
  obtain ⟨C, indexCFirst, indexCSecond, iC3, iC4, iC5, ψ, hψ⟩ := exists_dedekind_embedding_of_finite (O := O) (T := T) hTinj
  have hCinj : Function.Injective (algebraMap O C) := by
    intro a b h
    apply hTinj
    apply hψ
    rw [ψ.commutes, ψ.commutes]
    exact h
  obtain ⟨V, indexVFirst, indexVSecond, indexVThird, indexVFourth, iV5, φ, hφ⟩ := exists_dvr_embedding_of_dedekind (O := O) (C := C) hCinj
  refine ⟨V, indexVFirst, indexVSecond, indexVThird, indexVFourth, iV5, (φ.comp ψ).comp g, ?_⟩
  intro h
  apply hge
  apply hψ
  apply hφ
  rw [map_zero, map_zero]
  exact h

end ReciprocityTheory.ChartRestriction.G.T0.DiscreteValuationPoint
