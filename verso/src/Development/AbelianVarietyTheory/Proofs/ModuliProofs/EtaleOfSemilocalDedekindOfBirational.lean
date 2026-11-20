import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEquivalenceFiniteEtaleBaseChangeResidueField

namespace GlobalTheory

section
open Polynomial IsLocalRing

/- English proof (translation)
Use `set q := (maximalIdeal S).comap (algebraMap B S) with hq_def`. Establish `hqp : q.IsPrime` using `Ideal.comap_isPrime _ _`. Establish `hmem : ∀ y : B, y ∈ q ↔ ¬ IsUnit (algebraMap B S y)` using `fun y => by`. Rewrite using `[hq_def, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs_mem, hsq⟩ : ∃ s : B, (∀ P : Ideal B, P.IsMaximal → P ≠ q → s ∈ P) ∧ s ∉ q := by`.

Set `T : Finset (MaximalSpectrum B)` to `(Set.toFinite {m : MaximalSpectrum B | m.asIdeal ≠ q}).toFinset`. Establish `hT : ¬ T.inf (fun m => m.asIdeal) ≤ q`. Introduce `hle`. Take `⟨m, hmT, hmq⟩` from `hqp.inf_le'.mp hle`. Simplify using `only [T, Set.Finite.mem_toFinset] at hmT`.

Conclude with `hmT (m.isMaximal.eq_of_le hqp.ne_top hmq)`. Take `⟨s, hsT, hsq⟩` from `SetLike.not_le_iff_exists.mp hT`. Use `⟨s, fun P hP hPq => ?_, hsq⟩` and prove the remaining obligations. Establish `hPT : (⟨P, hP⟩ : MaximalSpectrum B) ∈ T` using `by simpa [T] using hPq`. Conclude with `Finset.inf_le (f := fun m : MaximalSpectrum B => m.asIdeal) hPT hsT`.

Establish `hsu : IsUnit (algebraMap B S s)`. Assume the negation of the conclusion as `h`. Conclude with `hsq ((hmem s).mpr h)`. Establish `key : ∀ x : S, ∃ a t : B, t ∉ q ∧ x * algebraMap B S t = algebraMap B S a`. Introduce `x`.

Take `⟨a, b, hb, hx⟩` from `hfr x`. Establish `hb' : algebraMap B S b ≠ 0` using `fun h => hb (hinj (by rw [h, map_zero]))`. Establish `hdvr` using `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hq (Localization.AtPrime q)`. Establish `hBq : Function.Injective (algebraMap B (Localization.AtPrime q))` using `IsLocalization.injective _ q.primeCompl_le_nonZeroDivisors`. Take `⟨c, hc | hc⟩` from `ValuationRing.cond (algebraMap B (Localization.AtPrime q) a) (algebraMap B (Localization.AtPrime q) b)`.

Take `⟨⟨a', t⟩, hct⟩` from `IsLocalization.surj q.primeCompl c`. Establish `h1 : a * a' = b * t` using `hBq (by simp only [map_mul]; rw [← hct, ← hc]; ring)`. Establish `h2 : x * algebraMap B S a' = algebraMap B S t`. Apply `mul_left_cancel₀ hb'` to reduce the goal to its premises. Establish `h3` using `congrArg (algebraMap B S) h1`.

Simplify using `only [map_mul] at h3`. Rewrite `h3` using `[← hx]`. Take the linear combination `h3`. Use `⟨t, a', ?_, h2⟩` and prove the remaining obligations. Introduce `ha'`.

Establish `ht : IsUnit (algebraMap B S t)`. Assume the negation of the conclusion as `h`. Conclude with `t.2 ((hmem t).mpr h)`. Rewrite `ht` using `[← h2]`. Conclude with `(hmem a').mp ha' (isUnit_of_mul_isUnit_right ht)`.

Take `⟨⟨a', t⟩, hct⟩` from `IsLocalization.surj q.primeCompl c`. Establish `h1 : b * a' = a * t` using `hBq (by simp only [map_mul]; rw [← hct, ← hc]; ring)`. Use `⟨a', t, t.2, ?_⟩` and prove the remaining obligations. Apply `mul_left_cancel₀ hb'` to reduce the goal to its premises. Establish `h3` using `congrArg (algebraMap B S) h1`.

Simplify using `only [map_mul] at h3`. Rewrite `h3` using `[← hx]`. Take the linear combination `-h3`. Establish `hsurj : ∀ x : S, ∃ y : B × Submonoid.powers s, x * algebraMap B S y.2 = algebraMap B S y.1`. Introduce `x`.

Take `⟨a, t, htq, hxt⟩` from `key x`. Establish `ht0 : t ≠ 0`. Introduce and unpack `rfl`. Conclude with `htq q.zero_mem`. Establish `hrad : s ∈ (Ideal.span {t}).radical`.

Rewrite using `[Ideal.radical_eq_sInf, Submodule.mem_sInf]`. Introduce and unpack `P ⟨hP, hPp⟩`. Establish `htP : t ∈ P` using `hP (Ideal.mem_span_singleton_self t)`. Establish `hPne : P ≠ ⊥` using `fun h => ht0 (by rwa [h, Ideal.mem_bot] at htP)`. Conclude with `hs_mem P (Ring.DimensionLEOne.maximalOfPrime hPne hPp) (fun h => htq (h ▸ htP))`.

Take `⟨n, hn⟩` from `hrad`. Take `⟨u, hu⟩` from `Ideal.mem_span_singleton'.mp hn`. Use `⟨⟨a * u, ⟨s ^ n, n, rfl⟩⟩, ?_⟩` and prove the remaining obligations. Use `show x * algebraMap B S (s ^ n) = algebraMap B S (a * u)`. Rewrite using `[← hu, map_mul, map_mul]`.

Take the linear combination `(algebraMap B S u) * hxt`. Establish `hloc : IsLocalization.Away s S` using `(isLocalization_iff (Submonoid.powers s) S).mpr ⟨fun y => by`. Take `⟨_, n, rfl⟩` from `y`. Simplify using `using hsu.pow n,`. Use the proof step `hsurj, fun {x y} h => ⟨1, by rw [hinj h]⟩⟩`.

Conclude with `Algebra.Etale.of_isLocalizationAway s`.
-/
theorem etale_of_semilocal_dedekind_of_birational (B S : Type*) [CommRing B] [IsDedekindDomain B]
    [Finite (MaximalSpectrum B)] [CommRing S] [IsDomain S] [IsLocalRing S] [Algebra B S]
    (hinj : Function.Injective (algebraMap B S))
    (hq : (maximalIdeal S).comap (algebraMap B S) ≠ ⊥)
    (hfr : ∀ x : S, ∃ a b : B, b ≠ 0 ∧ x * algebraMap B S b = algebraMap B S a) :
    Algebra.Etale B S := by
  classical
  set q := (maximalIdeal S).comap (algebraMap B S) with hq_def
  have hqp : q.IsPrime := Ideal.comap_isPrime _ _
  have hmem : ∀ y : B, y ∈ q ↔ ¬ IsUnit (algebraMap B S y) := fun y => by
    rw [hq_def, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  obtain ⟨s, hs_mem, hsq⟩ : ∃ s : B, (∀ P : Ideal B, P.IsMaximal → P ≠ q → s ∈ P) ∧ s ∉ q := by
    let T : Finset (MaximalSpectrum B) :=
      (Set.toFinite {m : MaximalSpectrum B | m.asIdeal ≠ q}).toFinset
    have hT : ¬ T.inf (fun m => m.asIdeal) ≤ q := by
      intro hle
      obtain ⟨m, hmT, hmq⟩ := hqp.inf_le'.mp hle
      simp only [T, Set.Finite.mem_toFinset] at hmT
      exact hmT (m.isMaximal.eq_of_le hqp.ne_top hmq)
    obtain ⟨s, hsT, hsq⟩ := SetLike.not_le_iff_exists.mp hT
    refine ⟨s, fun P hP hPq => ?_, hsq⟩
    have hPT : (⟨P, hP⟩ : MaximalSpectrum B) ∈ T := by simpa [T] using hPq
    exact Finset.inf_le (f := fun m : MaximalSpectrum B => m.asIdeal) hPT hsT
  have hsu : IsUnit (algebraMap B S s) := by
    by_contra h
    exact hsq ((hmem s).mpr h)
  have key : ∀ x : S, ∃ a t : B, t ∉ q ∧ x * algebraMap B S t = algebraMap B S a := by
    intro x
    obtain ⟨a, b, hb, hx⟩ := hfr x
    have hb' : algebraMap B S b ≠ 0 := fun h => hb (hinj (by rw [h, map_zero]))
    have hdvr := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hq
      (Localization.AtPrime q)
    have hBq : Function.Injective (algebraMap B (Localization.AtPrime q)) :=
      IsLocalization.injective _ q.primeCompl_le_nonZeroDivisors
    obtain ⟨c, hc | hc⟩ := ValuationRing.cond (algebraMap B (Localization.AtPrime q) a)
      (algebraMap B (Localization.AtPrime q) b)
    · obtain ⟨⟨a', t⟩, hct⟩ := IsLocalization.surj q.primeCompl c
      have h1 : a * a' = b * t := hBq (by simp only [map_mul]; rw [← hct, ← hc]; ring)
      have h2 : x * algebraMap B S a' = algebraMap B S t := by
        apply mul_left_cancel₀ hb'
        have h3 := congrArg (algebraMap B S) h1
        simp only [map_mul] at h3
        rw [← hx] at h3
        linear_combination h3
      refine ⟨t, a', ?_, h2⟩
      intro ha'
      have ht : IsUnit (algebraMap B S t) := by
        by_contra h
        exact t.2 ((hmem t).mpr h)
      rw [← h2] at ht
      exact (hmem a').mp ha' (isUnit_of_mul_isUnit_right ht)
    · obtain ⟨⟨a', t⟩, hct⟩ := IsLocalization.surj q.primeCompl c
      have h1 : b * a' = a * t := hBq (by simp only [map_mul]; rw [← hct, ← hc]; ring)
      refine ⟨a', t, t.2, ?_⟩
      apply mul_left_cancel₀ hb'
      have h3 := congrArg (algebraMap B S) h1
      simp only [map_mul] at h3
      rw [← hx] at h3
      linear_combination -h3
  have hsurj : ∀ x : S, ∃ y : B × Submonoid.powers s,
      x * algebraMap B S y.2 = algebraMap B S y.1 := by
    intro x
    obtain ⟨a, t, htq, hxt⟩ := key x
    have ht0 : t ≠ 0 := by
      rintro rfl
      exact htq q.zero_mem
    have hrad : s ∈ (Ideal.span {t}).radical := by
      rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
      rintro P ⟨hP, hPp⟩
      have htP : t ∈ P := hP (Ideal.mem_span_singleton_self t)
      have hPne : P ≠ ⊥ := fun h => ht0 (by rwa [h, Ideal.mem_bot] at htP)
      exact hs_mem P (Ring.DimensionLEOne.maximalOfPrime hPne hPp) (fun h => htq (h ▸ htP))
    obtain ⟨n, hn⟩ := hrad
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hn
    refine ⟨⟨a * u, ⟨s ^ n, n, rfl⟩⟩, ?_⟩
    show x * algebraMap B S (s ^ n) = algebraMap B S (a * u)
    rw [← hu, map_mul, map_mul]
    linear_combination (algebraMap B S u) * hxt
  have hloc : IsLocalization.Away s S := (isLocalization_iff (Submonoid.powers s) S).mpr
    ⟨fun y => by
      obtain ⟨_, n, rfl⟩ := y
      simpa using hsu.pow n,
     hsurj, fun {x y} h => ⟨1, by rw [hinj h]⟩⟩
  exact Algebra.Etale.of_isLocalizationAway s

/- English proof (translation)
Establish `hI : IsIntegral O z` using `⟨X ^ N - C 1, monic_X_pow_sub_C 1 hN.ne', by simp [hz]⟩`. Use `⟨hI, ?_⟩` and prove the remaining obligations. Establish `: FaithfulSMul O S` using `(faithfulSMul_iff_algebraMap_injective O S).mpr hinj`. Establish `hfm : (minpoly O z).Monic` using `minpoly.monic hI`. Take `⟨h, hgh⟩ : minpoly O z ∣ X ^ N - C 1` from `minpoly.isIntegrallyClosed_dvd hI (by simp [hz])`.

Establish `hpoly : X * derivative (X ^ N - C (1 : O)) = C (N : O) * (X ^ N - C 1) + C (N : O)`. Take `⟨n, rfl⟩ : ∃ n, N = n + 1` from `⟨N - 1, by omega⟩`. Simplify using `only [derivative_sub, derivative_X_pow, Nat.add_sub_cancel, map_one, derivative_one, sub_zero]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hg0 : AdjoinRoot.mk (minpoly O z) (X ^ N - C 1) = 0`. Rewrite using `[hgh, AdjoinRoot.mk_eq_zero]`. Conclude with `dvd_mul_right _ _`. Establish `hd : AdjoinRoot.mk (minpoly O z) (derivative (X ^ N - C (1 : O))) = AdjoinRoot.mk (minpoly O z) (derivative (minpoly O z)) * AdjoinRoot.mk (minpoly O z) h`. Rewrite using `[hgh, derivative_mul, map_add, map_mul, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero]`.

Establish `h1` using `congrArg (AdjoinRoot.mk (minpoly O z)) hpoly`. Rewrite `h1` using `[map_mul, hd, map_add, map_mul, hg0, mul_zero, zero_add]`. Establish `hu' : IsUnit (AdjoinRoot.mk (minpoly O z) (C (N : O)))`. Rewrite using `[AdjoinRoot.mk_C]`. Conclude with `hu.map _`.

Rewrite `hu'` using `[← h1]`. Establish `hunit` using `isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_right hu')`. Use `etale_adjoinRoot_of_isUnit_derivative hfm hunit` as an intermediate fact. Conclude with `Algebra.Etale.of_equiv (minpoly.equivAdjoin hI)`.
-/
theorem etale_adjoin_root_of_unity (O S : Type*) [CommRing O] [IsDomain O] [IsIntegrallyClosed O]
    [CommRing S] [IsDomain S] [Algebra O S] (hinj : Function.Injective (algebraMap O S))
    {N : ℕ} (hN : 0 < N) (hu : IsUnit (N : O)) {z : S} (hz : z ^ N = 1) :
    IsIntegral O z ∧ Algebra.Etale O (Algebra.adjoin O {z}) := by
  have hI : IsIntegral O z := ⟨X ^ N - C 1, monic_X_pow_sub_C 1 hN.ne', by simp [hz]⟩
  refine ⟨hI, ?_⟩
  have : FaithfulSMul O S := (faithfulSMul_iff_algebraMap_injective O S).mpr hinj
  have hfm : (minpoly O z).Monic := minpoly.monic hI
  obtain ⟨h, hgh⟩ : minpoly O z ∣ X ^ N - C 1 :=
    minpoly.isIntegrallyClosed_dvd hI (by simp [hz])
  have hpoly : X * derivative (X ^ N - C (1 : O)) = C (N : O) * (X ^ N - C 1) + C (N : O) := by
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    simp only [derivative_sub, derivative_X_pow, Nat.add_sub_cancel, map_one, derivative_one,
      sub_zero]
    push_cast
    ring
  have hg0 : AdjoinRoot.mk (minpoly O z) (X ^ N - C 1) = 0 := by
    rw [hgh, AdjoinRoot.mk_eq_zero]; exact dvd_mul_right _ _
  have hd : AdjoinRoot.mk (minpoly O z) (derivative (X ^ N - C (1 : O))) =
      AdjoinRoot.mk (minpoly O z) (derivative (minpoly O z)) * AdjoinRoot.mk (minpoly O z) h := by
    rw [hgh, derivative_mul, map_add, map_mul, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero]
  have h1 := congrArg (AdjoinRoot.mk (minpoly O z)) hpoly
  rw [map_mul, hd, map_add, map_mul, hg0, mul_zero, zero_add] at h1
  have hu' : IsUnit (AdjoinRoot.mk (minpoly O z) (C (N : O))) := by
    rw [AdjoinRoot.mk_C]; exact hu.map _
  rw [← h1] at hu'
  have hunit := isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_right hu')
  have := etale_adjoinRoot_of_isUnit_derivative hfm hunit
  exact Algebra.Etale.of_equiv (minpoly.equivAdjoin hI)

/- English proof (translation)
Take `⟨hI, hA⟩` from `etale_adjoin_root_of_unity O S hinj hN hu hz`. Establish `: FaithfulSMul O S` using `(faithfulSMul_iff_algebraMap_injective O S).mpr hinj`. Establish `hfin : Module.Finite O (Algebra.adjoin O {z})` using `(Algebra.adjoin.powerBasis' hI).finite`. Establish `hnoeth : IsNoetherianRing (Algebra.adjoin O {z})` using `IsNoetherianRing.of_finite O (Algebra.adjoin O {z})`. Establish `hdim : Ring.DimensionLEOne (Algebra.adjoin O {z})` using `Ring.DimensionLEOne.of_isIntegral O (Algebra.adjoin O {z})`.

Establish `hic : IsIntegrallyClosed (Algebra.adjoin O {z})` using `IsIntegrallyClosed.of_localization_maximal fun p _ _ => (isDomain_and_isIntegrallyClosed_atPrime_of_etale O p (Localization.AtPrime p)).2`. Establish `: IsDedekindRing (Algebra.adjoin O {z})` using `{ toIsNoetherian := hnoeth, toDimensionLEOne := hdim, toIsIntegralClosure := hic }`. Establish `hmax : Finite (MaximalSpectrum (Algebra.adjoin O {z}))`. Establish `hf : ((maximalIdeal O).primesOver (Algebra.adjoin O {z})).Finite` using `Algebra.QuasiFinite.finite_primesOver _`. Use `hf.to_subtype` as an intermediate fact.

Use `Finite.of_injective (fun m : MaximalSpectrum (Algebra.adjoin O {z}) => (⟨m.asIdeal, m.isMaximal.isPrime, ?_⟩ : (maximalIdeal O).primesOver (Algebra.adjoin O {z}))) (fun m m' h => MaximalSpectrum.ext (congrArg Subtype.val h))` and prove the remaining obligations. Use `m.isMaximal` as an intermediate fact. Conclude with `⟨(IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := O) m.asIdeal)).symm⟩`. Establish `hq : (maximalIdeal S).comap (algebraMap (Algebra.adjoin O {z}) S) ≠ ⊥`. Introduce `h`.

Establish `hmem : algebraMap O (Algebra.adjoin O {z}) π ∈ (maximalIdeal S).comap (algebraMap (Algebra.adjoin O {z}) S)`. Rewrite using `[Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]`. Conclude with `hπ'`. Rewrite `hmem` using `[h, Ideal.mem_bot]`. Conclude with `hπ (hinj (by rw [IsScalarTower.algebraMap_apply O (Algebra.adjoin O {z}) S, hmem, map_zero, map_zero]))`.

Establish `hfr' : ∀ x : S, ∃ a b : Algebra.adjoin O {z}, b ≠ 0 ∧ x * algebraMap (Algebra.adjoin O {z}) S b = algebraMap (Algebra.adjoin O {z}) S a`. Introduce `x`. Take `⟨a, ha, b, hb, hb0, hx⟩` from `hfr x`. Conclude with `⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hb0 (by simpa using congrArg Subtype.val h), hx⟩`. Establish `hAS : Algebra.Etale (Algebra.adjoin O {z}) S` using `etale_of_semilocal_dedekind_of_birational (Algebra.adjoin O {z}) S (fun x y h => Subtype.ext h) hq hfr'`.

Conclude with `Algebra.Etale.comp O (Algebra.adjoin O {z}) S`.
-/
theorem etale_of_birational_adjoin_root_of_unity (O S : Type*) [CommRing O] [IsDedekindDomain O]
    [IsLocalRing O] [CommRing S] [IsDomain S] [IsLocalRing S] [Algebra O S]
    (hinj : Function.Injective (algebraMap O S))
    {N : ℕ} (hN : 0 < N) (hu : IsUnit (N : O)) {z : S} (hz : z ^ N = 1)
    (π : O) (hπ : π ≠ 0) (hπ' : algebraMap O S π ∈ maximalIdeal S)
    (hfr : ∀ x : S, ∃ a ∈ Algebra.adjoin O {z}, ∃ b ∈ Algebra.adjoin O {z}, b ≠ 0 ∧ x * b = a) :
    Algebra.Etale O S := by
  classical
  obtain ⟨hI, hA⟩ := etale_adjoin_root_of_unity O S hinj hN hu hz
  have : FaithfulSMul O S := (faithfulSMul_iff_algebraMap_injective O S).mpr hinj
  have hfin : Module.Finite O (Algebra.adjoin O {z}) := (Algebra.adjoin.powerBasis' hI).finite
  have hnoeth : IsNoetherianRing (Algebra.adjoin O {z}) :=
    IsNoetherianRing.of_finite O (Algebra.adjoin O {z})
  have hdim : Ring.DimensionLEOne (Algebra.adjoin O {z}) :=
    Ring.DimensionLEOne.of_isIntegral O (Algebra.adjoin O {z})
  have hic : IsIntegrallyClosed (Algebra.adjoin O {z}) :=
    IsIntegrallyClosed.of_localization_maximal fun p _ _ =>
      (isDomain_and_isIntegrallyClosed_atPrime_of_etale O p (Localization.AtPrime p)).2
  have : IsDedekindRing (Algebra.adjoin O {z}) :=
    { toIsNoetherian := hnoeth, toDimensionLEOne := hdim, toIsIntegralClosure := hic }
  have hmax : Finite (MaximalSpectrum (Algebra.adjoin O {z})) := by
    have hf : ((maximalIdeal O).primesOver (Algebra.adjoin O {z})).Finite :=
      Algebra.QuasiFinite.finite_primesOver _
    have := hf.to_subtype
    refine Finite.of_injective (fun m : MaximalSpectrum (Algebra.adjoin O {z}) =>
      (⟨m.asIdeal, m.isMaximal.isPrime, ?_⟩ : (maximalIdeal O).primesOver (Algebra.adjoin O {z})))
      (fun m m' h => MaximalSpectrum.ext (congrArg Subtype.val h))
    have := m.isMaximal
    exact ⟨(IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := O) m.asIdeal)).symm⟩
  have hq : (maximalIdeal S).comap (algebraMap (Algebra.adjoin O {z}) S) ≠ ⊥ := by
    intro h
    have hmem : algebraMap O (Algebra.adjoin O {z}) π ∈
        (maximalIdeal S).comap (algebraMap (Algebra.adjoin O {z}) S) := by
      rw [Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]
      exact hπ'
    rw [h, Ideal.mem_bot] at hmem
    exact hπ (hinj (by rw [IsScalarTower.algebraMap_apply O (Algebra.adjoin O {z}) S, hmem,
      map_zero, map_zero]))
  have hfr' : ∀ x : S, ∃ a b : Algebra.adjoin O {z}, b ≠ 0 ∧
      x * algebraMap (Algebra.adjoin O {z}) S b = algebraMap (Algebra.adjoin O {z}) S a := by
    intro x
    obtain ⟨a, ha, b, hb, hb0, hx⟩ := hfr x
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hb0 (by simpa using congrArg Subtype.val h), hx⟩
  have hAS : Algebra.Etale (Algebra.adjoin O {z}) S :=
    etale_of_semilocal_dedekind_of_birational (Algebra.adjoin O {z}) S
      (fun x y h => Subtype.ext h) hq hfr'
  exact Algebra.Etale.comp O (Algebra.adjoin O {z}) S

end

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Models

/- English proof (translation)
Take `⟨-, -, -, hloc⟩` from `CoeffRings.coeff_isDedFrac E H l c`. Take `⟨⟨⟨_, hdd⟩, -, hfrac⟩, hunit, -⟩` from `hloc p W hp hW`. Set `_ : Algebra (c.V W) (c₁.V W)` to `b.toAlgebra`. Unfold `spMap`. Rewrite using `[HasRingHomProperty.Spec_iff (P := @Etale), CommRingCat.hom_ofHom]`.

Express the relevant statement in the definitionally equal form `Algebra.Etale (c.V W) (c₁.V W)`. Set `ι₀ : c.V W →+* ℂ` to `c.F.val.toRingHom.comp (c.V W).subtype`. Set `ι₁ : c₁.V W →+* ℂ` to `c₁.F.val.toRingHom.comp (c₁.V W).subtype`. Establish `hι₀ : Function.Injective ι₀` using `fun x y h => Subtype.ext (Subtype.ext h)`. Establish `hι₁ : Function.Injective ι₁` using `fun x y h => Subtype.ext (Subtype.ext h)`.

Establish `hbι : ∀ x, ι₁ (algebraMap (c.V W) (c₁.V W) x) = ι₀ x` using `hb`. Establish `hinj : Function.Injective (algebraMap (c.V W) (c₁.V W))` using `fun x y h => hι₀ (by rw [← hbι, ← hbι, h])`. Establish `hζF : zeta N ∈ c₁.F`. Rewrite using `[hF]`. Conclude with `(le_sup_right : IntermediateField.adjoin ℚ {zeta N} ≤ c.F ⊔ IntermediateField.adjoin ℚ {zeta N}) (IntermediateField.mem_adjoin_simple_self ℚ (zeta N))`.

Establish `hζW : (⟨zeta N, hζF⟩ : c₁.F) ∈ c₁.V W` using `ValuationSubring.mem_comap.mpr (CoeffRings.mem_of_isIntegral W (CoeffRings.isIntegral_int_zeta hN))`. Set `z : c₁.V W` to `⟨⟨zeta N, hζF⟩, hζW⟩`. Establish `hzι : ι₁ z = zeta N` using `rfl`. Establish `hz : z ^ N = 1` using `hι₁ (by`. Rewrite using `[map_pow, map_one, hzι]`.

Conclude with `(Complex.isPrimitiveRoot_exp N hN.ne').pow_eq_one)`. Establish `hπ : ((p : ℕ) : c.V W) ≠ 0` using `fun h => hp.ne_zero (by`. Establish `h1` using `congrArg ι₀ h`. Rewrite `h1` using `[map_natCast, map_zero]`. Conclude with `h1)` after adjusting the coercions.

Establish `hπ' : algebraMap (c.V W) (c₁.V W) (p : c.V W) ∈ IsLocalRing.maximalIdeal (c₁.V W)`. Rewrite using `[map_natCast, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce and unpack `⟨u, hu⟩`. Break down `(ValuationSubring.mem_nonunits_iff_or W).mp hW with h0 | hinv` into its components or cases. Conclude with `hp.ne_zero (by exact_mod_cast h0)`.

Apply `hinv` to reduce the goal to its premises. Establish `h1 : ι₁ ↑u * ι₁ ↑u⁻¹ = 1` using `by rw [← map_mul, Units.mul_inv, map_one]`. Rewrite `h1` using `[hu, map_natCast]`. Rewrite using `[← eq_inv_of_mul_eq_one_right h1]`. Conclude with `ValuationSubring.mem_comap.mp (↑u⁻¹ : c₁.V W).2`.

Set `A'` to `Algebra.adjoin (c.V W) {z}`. Set `P : ℂ → Prop` to `fun y => ∃ d : c.V W, d ≠ 0 ∧ ∃ a ∈ A', ι₁ a = ι₀ d * y`. Establish `hPF : ∀ y ∈ c.F, P y`. Introduce `y hy`. Take `⟨⟨a, d⟩, had⟩` from `@IsLocalization.surj _ _ _ _ _ (c.V W).subtype.toAlgebra hfrac ⟨y, hy⟩`.

Establish `had' : y * ι₀ d = ι₀ a` using `congrArg (fun t : c.F => (t : ℂ)) had`. Use `⟨d, nonZeroDivisors.coe_ne_zero d, algebraMap (c.V W) (c₁.V W) a, Subalgebra.algebraMap_mem _ _, ?_⟩` and prove the remaining obligations. Rewrite using `[hbι, ← had', mul_comm]`. Establish `hadd : ∀ y₁ y₂, P y₁ → P y₂ → P (y₁ + y₂)`. Introduce and unpack `y₁ y₂ ⟨d₁, hd₁, a₁, ha₁, e₁⟩ ⟨d₂, hd₂, a₂, ha₂, e₂⟩`.

Use `⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, algebraMap (c.V W) (c₁.V W) d₂ * a₁ + algebraMap (c.V W) (c₁.V W) d₁ * a₂, A'.add_mem (A'.mul_mem (A'.algebraMap_mem _) ha₁) (A'.mul_mem (A'.algebraMap_mem _) ha₂), ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_mul, map_mul, hbι, hbι, e₁, e₂, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hmul : ∀ y₁ y₂, P y₁ → P y₂ → P (y₁ * y₂)`. Introduce and unpack `y₁ y₂ ⟨d₁, hd₁, a₁, ha₁, e₁⟩ ⟨d₂, hd₂, a₂, ha₂, e₂⟩`.

Use `⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, a₁ * a₂, A'.mul_mem ha₁ ha₂, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, e₁, e₂, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Set `T : Subalgebra ℚ ℂ` to `{ carrier := {y | P y} mul_mem' := fun {y₁ y₂} h₁ h₂ => hmul y₁ y₂ h₁ h₂ add_mem' := fun {y₁ y₂} h₁ h₂ => hadd y₁ y₂ h₁ h₂ algebraMap_mem' := fun r => hPF _ (c.F.algebraMap_mem r) }`. Establish `hle : c₁.F.toSubalgebra ≤ T`.

Use `c.fin` as an intermediate fact. Rewrite using `[hF, IntermediateField.sup_toSubalgebra_of_left]`. Use `sup_le (fun y hy => hPF y hy) ?_` and prove the remaining obligations. Rewrite using `[IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (CoeffRings.isIntegral_int_zeta hN).tower_top.isAlgebraic]`. Use `Algebra.adjoin_le (Set.singleton_subset_iff.mpr ?_)` and prove the remaining obligations.

Conclude with `⟨1, one_ne_zero, z, Algebra.subset_adjoin rfl, by rw [map_one, one_mul]; exact hzι⟩`. Establish `hfr : ∀ x : c₁.V W, ∃ a ∈ A', ∃ b' ∈ A', b' ≠ 0 ∧ x * b' = a`. Introduce `x`. Take `⟨d, hd, a, ha, e⟩` from `hle (x : c₁.F).2`. Use `⟨a, ha, algebraMap (c.V W) (c₁.V W) d, A'.algebraMap_mem d, fun h => hd (hinj (by rw [h, map_zero])), hι₁ ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, hbι, e]`. Conclude with `mul_comm _ _`. Conclude with `etale_of_birational_adjoin_root_of_unity (c.V W) (c₁.V W) hinj hN (hunit N hNp) hz (p : c.V W) hπ hπ' hfr`.
-/
theorem etale_coeff_adjoin_zeta (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (l l₁ : Level H) (c : Coeff l) (c₁ : Coeff l₁) (p N : ℕ) (W : ValuationSubring ℂ)
    (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (hNp : N.Coprime p) (hN : 0 < N)
    (hF : c₁.F = c.F ⊔ IntermediateField.adjoin ℚ {zeta N}) (b : c.V W →+* c₁.V W)
    (hb : IsIncl b) : Etale (spMap b) := by
  classical
  obtain ⟨-, -, -, hloc⟩ := CoeffRings.coeff_isDedFrac E H l c
  obtain ⟨⟨⟨_, hdd⟩, -, hfrac⟩, hunit, -⟩ := hloc p W hp hW
  let _ : Algebra (c.V W) (c₁.V W) := b.toAlgebra
  unfold spMap
  rw [HasRingHomProperty.Spec_iff (P := @Etale), CommRingCat.hom_ofHom]
  change Algebra.Etale (c.V W) (c₁.V W)
  let ι₀ : c.V W →+* ℂ := c.F.val.toRingHom.comp (c.V W).subtype
  let ι₁ : c₁.V W →+* ℂ := c₁.F.val.toRingHom.comp (c₁.V W).subtype
  have hι₀ : Function.Injective ι₀ := fun x y h => Subtype.ext (Subtype.ext h)
  have hι₁ : Function.Injective ι₁ := fun x y h => Subtype.ext (Subtype.ext h)
  have hbι : ∀ x, ι₁ (algebraMap (c.V W) (c₁.V W) x) = ι₀ x := hb
  have hinj : Function.Injective (algebraMap (c.V W) (c₁.V W)) := fun x y h =>
    hι₀ (by rw [← hbι, ← hbι, h])
  have hζF : zeta N ∈ c₁.F := by
    rw [hF]
    exact (le_sup_right : IntermediateField.adjoin ℚ {zeta N} ≤ c.F ⊔ IntermediateField.adjoin ℚ {zeta N})
      (IntermediateField.mem_adjoin_simple_self ℚ (zeta N))
  have hζW : (⟨zeta N, hζF⟩ : c₁.F) ∈ c₁.V W :=
    ValuationSubring.mem_comap.mpr (CoeffRings.mem_of_isIntegral W (CoeffRings.isIntegral_int_zeta hN))
  let z : c₁.V W := ⟨⟨zeta N, hζF⟩, hζW⟩
  have hzι : ι₁ z = zeta N := rfl
  have hz : z ^ N = 1 := hι₁ (by
    rw [map_pow, map_one, hzι]
    exact (Complex.isPrimitiveRoot_exp N hN.ne').pow_eq_one)
  have hπ : ((p : ℕ) : c.V W) ≠ 0 := fun h => hp.ne_zero (by
    have h1 := congrArg ι₀ h
    rw [map_natCast, map_zero] at h1
    exact_mod_cast h1)
  have hπ' : algebraMap (c.V W) (c₁.V W) (p : c.V W) ∈ IsLocalRing.maximalIdeal (c₁.V W) := by
    rw [map_natCast, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    rcases (ValuationSubring.mem_nonunits_iff_or W).mp hW with h0 | hinv
    · exact hp.ne_zero (by exact_mod_cast h0)
    · apply hinv
      have h1 : ι₁ ↑u * ι₁ ↑u⁻¹ = 1 := by rw [← map_mul, Units.mul_inv, map_one]
      rw [hu, map_natCast] at h1
      rw [← eq_inv_of_mul_eq_one_right h1]
      exact ValuationSubring.mem_comap.mp (↑u⁻¹ : c₁.V W).2
  let A' := Algebra.adjoin (c.V W) {z}
  let P : ℂ → Prop := fun y => ∃ d : c.V W, d ≠ 0 ∧ ∃ a ∈ A', ι₁ a = ι₀ d * y
  have hPF : ∀ y ∈ c.F, P y := by
    intro y hy
    obtain ⟨⟨a, d⟩, had⟩ :=
      @IsLocalization.surj _ _ _ _ _ (c.V W).subtype.toAlgebra hfrac ⟨y, hy⟩
    have had' : y * ι₀ d = ι₀ a := congrArg (fun t : c.F => (t : ℂ)) had
    refine ⟨d, nonZeroDivisors.coe_ne_zero d, algebraMap (c.V W) (c₁.V W) a,
      Subalgebra.algebraMap_mem _ _, ?_⟩
    rw [hbι, ← had', mul_comm]
  have hadd : ∀ y₁ y₂, P y₁ → P y₂ → P (y₁ + y₂) := by
    rintro y₁ y₂ ⟨d₁, hd₁, a₁, ha₁, e₁⟩ ⟨d₂, hd₂, a₂, ha₂, e₂⟩
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂,
      algebraMap (c.V W) (c₁.V W) d₂ * a₁ + algebraMap (c.V W) (c₁.V W) d₁ * a₂,
      A'.add_mem (A'.mul_mem (A'.algebraMap_mem _) ha₁) (A'.mul_mem (A'.algebraMap_mem _) ha₂), ?_⟩
    rw [map_add, map_mul, map_mul, hbι, hbι, e₁, e₂, map_mul]
    ring
  have hmul : ∀ y₁ y₂, P y₁ → P y₂ → P (y₁ * y₂) := by
    rintro y₁ y₂ ⟨d₁, hd₁, a₁, ha₁, e₁⟩ ⟨d₂, hd₂, a₂, ha₂, e₂⟩
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, a₁ * a₂, A'.mul_mem ha₁ ha₂, ?_⟩
    rw [map_mul, e₁, e₂, map_mul]
    ring
  let T : Subalgebra ℚ ℂ :=
    { carrier := {y | P y}
      mul_mem' := fun {y₁ y₂} h₁ h₂ => hmul y₁ y₂ h₁ h₂
      add_mem' := fun {y₁ y₂} h₁ h₂ => hadd y₁ y₂ h₁ h₂
      algebraMap_mem' := fun r => hPF _ (c.F.algebraMap_mem r) }
  have hle : c₁.F.toSubalgebra ≤ T := by
    have := c.fin
    rw [hF, IntermediateField.sup_toSubalgebra_of_left]
    refine sup_le (fun y hy => hPF y hy) ?_
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (CoeffRings.isIntegral_int_zeta hN).tower_top.isAlgebraic]
    refine Algebra.adjoin_le (Set.singleton_subset_iff.mpr ?_)
    exact ⟨1, one_ne_zero, z, Algebra.subset_adjoin rfl, by rw [map_one, one_mul]; exact hzι⟩
  have hfr : ∀ x : c₁.V W, ∃ a ∈ A', ∃ b' ∈ A', b' ≠ 0 ∧ x * b' = a := by
    intro x
    obtain ⟨d, hd, a, ha, e⟩ := hle (x : c₁.F).2
    refine ⟨a, ha, algebraMap (c.V W) (c₁.V W) d, A'.algebraMap_mem d,
      fun h => hd (hinj (by rw [h, map_zero])), hι₁ ?_⟩
    rw [map_mul, hbι, e]
    exact mul_comm _ _
  exact etale_of_birational_adjoin_root_of_unity (c.V W) (c₁.V W) hinj hN (hunit N hNp) hz
    (p : c.V W) hπ hπ' hfr

end GlobalTheory
