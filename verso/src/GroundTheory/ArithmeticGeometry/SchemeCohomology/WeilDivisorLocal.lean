import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.WeilDivisor
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory AlgebraicGeometry IsDedekindDomain TopologicalSpace Topology

universe u

class IsLocallyFactorial (X : Scheme.{u}) : Prop where
  ufm_stalk : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)

variable {X : Scheme.{u}}

instance (priority := 100) IsLocallyFactorial.isNormalScheme [IsIntegral X]
    [IsLocallyFactorial X] : IsNormalScheme X where
  isDomain_stalk _ := inferInstance
  isIntegrallyClosed_stalk x := by
    have := IsLocallyFactorial.ufm_stalk (X := X) x
    infer_instance

namespace PrimeDivisor

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]

/- English proof (translation)
Simplify using `[ord]`.
-/
lemma ord_zero (x : PrimeDivisor X) : x.ord 0 = 0 := by
  simp [ord]

/- English proof (translation)
Use `x.isDedekindDomain_stalk` as an intermediate fact. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Conclude with `x.maximalIdeal_ne_bot (by rw [ha, Ideal.span_singleton_eq_bot])`. Simplify using `only [ord, valuation]`.

Rewrite using `[HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_singleton _ ha0 ha]`. Simplify using the standard rewrite rules.
-/
lemma ord_algebraMap_of_maximalIdeal_eq (x : PrimeDivisor X) {a : X.presheaf.stalk x.point}
    (ha : IsLocalRing.maximalIdeal (X.presheaf.stalk x.point) = Ideal.span {a}) :
    x.ord (algebraMap _ X.functionField a) = 1 := by
  have := x.isDedekindDomain_stalk
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact x.maximalIdeal_ne_bot (by rw [ha, Ideal.span_singleton_eq_bot])
  simp only [ord, valuation]
  rw [HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_singleton _ ha0 ha]
  simp

omit [IsLocallyNoetherian X] [IsNormalScheme X] in

/- English proof (translation)
Use `x.dimensionLEOne_stalk` as an intermediate fact. Establish `hmax : w.asIdeal.IsMaximal` using `Ring.DimensionLEOne.maximalOfPrime w.ne_bot w.isPrime`. Use `ext1`. Conclude with `IsLocalRing.eq_maximalIdeal hmax`.
-/
lemma heightOneSpectrum_eq (x : PrimeDivisor X)
    (w : HeightOneSpectrum (X.presheaf.stalk x.point)) : w = x.heightOneSpectrum := by
  have := x.dimensionLEOne_stalk
  have hmax : w.asIdeal.IsMaximal := Ring.DimensionLEOne.maximalOfPrime w.ne_bot w.isPrime
  ext1
  exact IsLocalRing.eq_maximalIdeal hmax

/- English proof (translation)
Use `x.isDedekindDomain_stalk` as an intermediate fact. Establish `hv0 : x.valuation f ≠ 0` using `(Valuation.ne_zero_iff _).mpr hf`. Establish `key : 0 ≤ x.ord f ↔ x.valuation f ≤ 1`. Simplify using `only [ord, Left.nonneg_neg_iff]`. Rewrite using `[WithZero.log_le_iff_le_exp hv0]`.

Simplify using the standard rewrite rules. Rewrite using `[key]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Apply `HeightOneSpectrum.mem_integers_of_valuation_le_one` to reduce the goal to its premises.

Introduce `w`. Rewrite using `[x.heightOneSpectrum_eq w]`. Conclude with `h`. Introduce and unpack `⟨a, rfl⟩`. Simplify using `only [valuation]`.

Rewrite using `[HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `HeightOneSpectrum.intValuation_le_one _ _`.
-/
lemma ord_nonneg_iff (x : PrimeDivisor X) {f : X.functionField} (hf : f ≠ 0) :
    0 ≤ x.ord f ↔ f ∈ (algebraMap (X.presheaf.stalk x.point) X.functionField).range := by
  have := x.isDedekindDomain_stalk
  have hv0 : x.valuation f ≠ 0 := (Valuation.ne_zero_iff _).mpr hf
  have key : 0 ≤ x.ord f ↔ x.valuation f ≤ 1 := by
    simp only [ord, Left.nonneg_neg_iff]
    rw [WithZero.log_le_iff_le_exp hv0]
    simp
  rw [key]
  constructor
  · intro h
    apply HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro w
    rw [x.heightOneSpectrum_eq w]
    exact h
  · rintro ⟨a, rfl⟩
    simp only [valuation]
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_le_one _ _

end PrimeDivisor

section Algebra

variable {A : Type*} [CommRing A] [IsDomain A] (p : Ideal A) [p.IsPrime]

/- English proof (translation)
Establish `hdisj : ∀ q' : Ideal A, q' ≤ p → Disjoint (p.primeCompl : Set A) (q' : Set A)` using `fun q' h => Set.disjoint_left.mpr fun x hx hq' => hx (h hq')`. Establish `hQ : (q.map (algebraMap A S)).IsPrime` using `IsLocalization.isPrime_of_isPrime_disjoint p.primeCompl S q ‹_› (hdisj q hqp)`. Establish `hQc : (q.map (algebraMap A S)).under A = q` using `IsLocalization.under_map_of_isPrime_disjoint p.primeCompl S ‹q.IsPrime› (hdisj q hqp)`. Establish `hQh : (q.map (algebraMap A S)).height = 1`. Rewrite using `[IsLocalization.height_map_of_disjoint p.primeCompl q (hdisj q hqp), hq]`.

Take `⟨π, hπ⟩` from `(UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hQh).principal`. Take `⟨⟨a, s⟩, rfl⟩` from `IsLocalization.mk'_surjective p.primeCompl π`. Establish `hQa : q.map (algebraMap A S) = Ideal.span {algebraMap A S a}` using `by dsimp only at hπ`. Rewrite using `[hπ]`. Express the relevant statement in the definitionally equal form `Ideal.span {IsLocalization.mk' S a s} = _`.

Rewrite using `[IsLocalization.mk'_eq_mul_mk'_one, Ideal.span_singleton_mul_right_unit ((IsLocalization.AtPrime.isUnit_mk'_iff S p 1 s).mpr p.primeCompl.one_mem)]`. Establish `hinj : Function.Injective (algebraMap A S)` using `IsLocalization.injective S p.primeCompl_le_nonZeroDivisors`. Use `⟨a, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hQc, Ideal.under, Ideal.mem_comap, hQa]`. Conclude with `Ideal.mem_span_singleton_self _`.

Introduce `b hb`. Establish `hbQ : algebraMap A S b ∈ q.map (algebraMap A S)` using `Ideal.mem_map_of_mem _ hb`. Rewrite `hbQ` using `[hQa, Ideal.mem_span_singleton']`. Take `⟨z, hz⟩` from `hbQ`. Take `⟨⟨c, t⟩, rfl⟩` from `IsLocalization.mk'_surjective p.primeCompl z`.

Use `⟨c, t, t.2, hinj ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, ← hz, mul_comm (IsLocalization.mk' S c t), mul_assoc, IsLocalization.mk'_spec, mul_comm]`. Introduce `q' hq' hq'p hq'h haq'`. Establish `hQ' : (q'.map (algebraMap A S)).IsPrime` using `IsLocalization.isPrime_of_isPrime_disjoint p.primeCompl S q' hq' (hdisj q' hq'p)`. Establish `hQ'h : (q'.map (algebraMap A S)).height = 1`.

Rewrite using `[IsLocalization.height_map_of_disjoint p.primeCompl q' (hdisj q' hq'p), hq'h]`. Establish `hle : q.map (algebraMap A S) ≤ q'.map (algebraMap A S)`. Rewrite using `[hQa, Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `Ideal.mem_map_of_mem _ haq'`. Establish `: (q.map (algebraMap A S)).FiniteHeight`.

Simplify using `[Ideal.finiteHeight_iff, hQh]`. Establish `heq` using `Ideal.eq_of_le_of_height_le _ hle (by rw [hQh, hQ'h])`. Rewrite using `[← hQc, heq, IsLocalization.under_map_of_isPrime_disjoint p.primeCompl S hq' (hdisj q' hq'p)]`.
-/
theorem exists_local_generator (S : Type*) [CommRing S] [IsDomain S] [Algebra A S]
    [IsLocalization.AtPrime S p] [UniqueFactorizationMonoid S]
    {q : Ideal A} [q.IsPrime] (hqp : q ≤ p) (hq : q.height = 1) :
    ∃ a ∈ q, (∀ b ∈ q, ∃ c : A, ∃ t : A, t ∉ p ∧ b * t = a * c) ∧
      ∀ q' : Ideal A, q'.IsPrime → q' ≤ p → q'.height = 1 → a ∈ q' → q' = q := by
  have hdisj : ∀ q' : Ideal A, q' ≤ p → Disjoint (p.primeCompl : Set A) (q' : Set A) :=
    fun q' h => Set.disjoint_left.mpr fun x hx hq' => hx (h hq')
  have hQ : (q.map (algebraMap A S)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint p.primeCompl S q ‹_› (hdisj q hqp)
  have hQc : (q.map (algebraMap A S)).under A = q :=
    IsLocalization.under_map_of_isPrime_disjoint p.primeCompl S ‹q.IsPrime› (hdisj q hqp)
  have hQh : (q.map (algebraMap A S)).height = 1 := by
    rw [IsLocalization.height_map_of_disjoint p.primeCompl q (hdisj q hqp), hq]
  obtain ⟨π, hπ⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hQh).principal
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl π
  have hQa : q.map (algebraMap A S) = Ideal.span {algebraMap A S a} := by
    dsimp only at hπ
    rw [hπ]
    change Ideal.span {IsLocalization.mk' S a s} = _
    rw [IsLocalization.mk'_eq_mul_mk'_one,
      Ideal.span_singleton_mul_right_unit ((IsLocalization.AtPrime.isUnit_mk'_iff S p 1 s).mpr
        p.primeCompl.one_mem)]
  have hinj : Function.Injective (algebraMap A S) :=
    IsLocalization.injective S p.primeCompl_le_nonZeroDivisors
  refine ⟨a, ?_, ?_, ?_⟩
  · rw [← hQc, Ideal.under, Ideal.mem_comap, hQa]
    exact Ideal.mem_span_singleton_self _
  · intro b hb
    have hbQ : algebraMap A S b ∈ q.map (algebraMap A S) := Ideal.mem_map_of_mem _ hb
    rw [hQa, Ideal.mem_span_singleton'] at hbQ
    obtain ⟨z, hz⟩ := hbQ
    obtain ⟨⟨c, t⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
    refine ⟨c, t, t.2, hinj ?_⟩
    rw [map_mul, map_mul, ← hz, mul_comm (IsLocalization.mk' S c t), mul_assoc,
      IsLocalization.mk'_spec, mul_comm]
  · intro q' hq' hq'p hq'h haq'
    have hQ' : (q'.map (algebraMap A S)).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint p.primeCompl S q' hq' (hdisj q' hq'p)
    have hQ'h : (q'.map (algebraMap A S)).height = 1 := by
      rw [IsLocalization.height_map_of_disjoint p.primeCompl q' (hdisj q' hq'p), hq'h]
    have hle : q.map (algebraMap A S) ≤ q'.map (algebraMap A S) := by
      rw [hQa, Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem _ haq'
    have : (q.map (algebraMap A S)).FiniteHeight := by
      simp [Ideal.finiteHeight_iff, hQh]
    have heq := Ideal.eq_of_le_of_height_le _ hle (by rw [hQh, hQ'h])
    rw [← hQc, heq, IsLocalization.under_map_of_isPrime_disjoint p.primeCompl S hq'
      (hdisj q' hq'p)]

end Algebra

section Hartogs

/- English proof (translation)
Take `⟨a, c, hac, rfl⟩` from `IsFractionRing.exists_reduced_fraction R f`. Distinguish the cases in `hc : IsUnit (c : R)`. Use `⟨a * ↑hc.unit⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_comm, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul, mul_assoc, Units.inv_mul_eq_one.mpr hc.unit_spec.symm, mul_one]`. Take `⟨π, hπirr, hπc⟩` from `WfDvdMonoid.exists_irreducible_factor hc (nonZeroDivisors.ne_zero c.2)`.

Establish `hπ : Prime π` using `UniqueFactorizationMonoid.irreducible_iff_prime.mp hπirr`. Take `⟨b, t, hπt, hft⟩` from `h π hπ`. Establish `key : a * t = b * c`. Apply `IsFractionRing.injective R K` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, ← hft, mul_comm (IsLocalization.mk' K a c), mul_assoc, IsLocalization.mk'_spec, mul_comm]`.

Establish `hπa : π ∣ a`. Establish `: π ∣ a * t` using `key ▸ dvd_mul_of_dvd_right hπc b`. Conclude with `(hπ.dvd_or_dvd this).resolve_right hπt`. Conclude with `absurd (hac hπa hπc) hπ.not_isUnit`.
-/
theorem mem_range_of_forall_prime (R : Type*) [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (f : K) (h : ∀ π : R, Prime π → ∃ b t : R, ¬ π ∣ t ∧ f * algebraMap R K t = algebraMap R K b) :
    f ∈ (algebraMap R K).range := by
  obtain ⟨a, c, hac, rfl⟩ := IsFractionRing.exists_reduced_fraction R f
  by_cases hc : IsUnit (c : R)
  · refine ⟨a * ↑hc.unit⁻¹, ?_⟩
    rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul, mul_assoc, Units.inv_mul_eq_one.mpr
      hc.unit_spec.symm, mul_one]
  · obtain ⟨π, hπirr, hπc⟩ :=
      WfDvdMonoid.exists_irreducible_factor hc (nonZeroDivisors.ne_zero c.2)
    have hπ : Prime π := UniqueFactorizationMonoid.irreducible_iff_prime.mp hπirr
    obtain ⟨b, t, hπt, hft⟩ := h π hπ
    have key : a * t = b * c := by
      apply IsFractionRing.injective R K
      rw [map_mul, map_mul, ← hft, mul_comm (IsLocalization.mk' K a c), mul_assoc,
        IsLocalization.mk'_spec, mul_comm]
    have hπa : π ∣ a := by
      have : π ∣ a * t := key ▸ dvd_mul_of_dvd_right hπc b
      exact (hπ.dvd_or_dvd this).resolve_right hπt
    exact absurd (hac hπa hπc) hπ.not_isUnit

/- English proof (translation)
Establish `hprime : (Ideal.span {π}).IsPrime` using `(Ideal.span_singleton_prime hπ.ne_zero).mpr hπ`. Apply `le_antisymm` to reduce the goal to its premises. Apply `Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {π})` to reduce the goal to its premises. Rewrite using `[Ideal.minimalPrimes_eq_subsingleton_self]`. Both sides reduce to the same expression.

Rewrite using `[Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hπ.ne_zero`.
-/
lemma height_span_prime {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] {π : R}
    (hπ : Prime π) : (Ideal.span {π}).height = 1 := by
  have hprime : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
  apply le_antisymm
  · apply Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {π})
    rw [Ideal.minimalPrimes_eq_subsingleton_self]
    rfl
  · rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot,
      Ideal.span_singleton_eq_bot]
    exact hπ.ne_zero

end Hartogs

section Affine

variable {U : X.Opens} (hU : IsAffineOpen U)

include hU in

/- English proof (translation)
Rewrite using `[← SetLike.mem_coe, ← hU.range_fromSpec]`. Conclude with `⟨q, rfl⟩`.
-/
lemma affine_fromSpec_mem (q : Spec Γ(X, U)) : hU.fromSpec q ∈ U := by
  rw [← SetLike.mem_coe, ← hU.range_fromSpec]
  exact ⟨q, rfl⟩

/- English proof (translation)
Rewrite using `[hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff]`. Conclude with `(PrimeSpectrum.le_iff_specializes q q').symm`.
-/
lemma affine_fromSpec_specializes_iff (q q' : Spec Γ(X, U)) :
    hU.fromSpec q ⤳ hU.fromSpec q' ↔ q.asIdeal ≤ q'.asIdeal := by
  rw [hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff]
  exact (PrimeSpectrum.le_iff_specializes q q').symm

/- English proof (translation)
The claim follows from `hU.fromSpec.isOpenEmbedding.injective`.
-/
lemma affine_fromSpec_injective : Function.Injective hU.fromSpec :=
  hU.fromSpec.isOpenEmbedding.injective

/- English proof (translation)
Take `⟨z, hz⟩` from `Z`. Express the relevant statement in the definitionally equal form `hU.fromSpec q = z at hq`. Substitute `hq` using the available equality. Establish `: q.asIdeal.IsPrime` using `PrimeSpectrum.isPrime q`. Set `_` to `TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec q, affine_fromSpec_mem hU q⟩`.

Establish `: IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec q)) q.asIdeal` using `hU.isLocalization_stalk' q (affine_fromSpec_mem hU q)`. Establish `h` using `IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal (X.presheaf.stalk (hU.fromSpec q))`. Rewrite `h` using `[hz]`. Conclude with `h.symm` after adjusting the coercions.
-/
lemma affine_height_eq_one (Z : PrimeDivisor X) (q : Spec Γ(X, U))
    (hq : hU.fromSpec q = Z.point) : q.asIdeal.height = 1 := by
  obtain ⟨z, hz⟩ := Z
  change hU.fromSpec q = z at hq
  subst hq
  have : q.asIdeal.IsPrime := PrimeSpectrum.isPrime q
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec q, affine_fromSpec_mem hU q⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec q)) q.asIdeal :=
    hU.isLocalization_stalk' q (affine_fromSpec_mem hU q)
  have h := IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal (X.presheaf.stalk (hU.fromSpec q))
  rw [hz] at h
  exact_mod_cast h.symm

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]

/- English proof (translation)
Take `⟨z, hz⟩` from `Z`. Express the relevant statement in the definitionally equal form `hU.fromSpec q = z at hq`. Substitute `hq` using the available equality. Establish `: q.asIdeal.IsPrime` using `PrimeSpectrum.isPrime q`. Set `_` to `TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec q, affine_fromSpec_mem hU q⟩`.

Establish `: IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec q)) q.asIdeal` using `hU.isLocalization_stalk' q (affine_fromSpec_mem hU q)`. Rewrite using `[← Scheme.algebraMap_germ_eq_germToFunctionField X (affine_fromSpec_mem hU q)]`. Apply `PrimeDivisor.ord_algebraMap_of_maximalIdeal_eq ⟨hU.fromSpec q, hz⟩` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `IsLocalRing.maximalIdeal (X.presheaf.stalk (hU.fromSpec q)) = Ideal.span {algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec q)) a}`. Rewrite using `[← IsLocalization.AtPrime.map_eq_maximalIdeal q.asIdeal]`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `b hb`. Take `⟨c, t, ht, hbt⟩` from `hgen b hb`. Rewrite using `[Ideal.mem_comap, Ideal.mem_span_singleton]`.

Establish `hu : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec q)) t)` using `(IsLocalization.AtPrime.isUnit_to_map_iff _ q.asIdeal t).mpr ht`. Use `⟨algebraMap _ _ c * ↑hu.unit⁻¹, ?_⟩` and prove the remaining obligations. Establish `h2` using `congrArg (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec q))) hbt`. Rewrite `h2` using `[map_mul, map_mul]`. Rewrite using `[← mul_assoc, ← h2, mul_assoc, IsUnit.mul_val_inv, mul_one]`.

Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `Ideal.mem_map_of_mem _ ha`.
-/
lemma affine_ord_eq_one (Z : PrimeDivisor X) (q : Spec Γ(X, U))
    (hq : hU.fromSpec q = Z.point) [Nonempty U] {a : Γ(X, U)} (ha : a ∈ q.asIdeal)
    (hgen : ∀ b ∈ q.asIdeal, ∃ c t : Γ(X, U), t ∉ q.asIdeal ∧ b * t = a * c) :
    Z.ord (X.germToFunctionField U a) = 1 := by
  obtain ⟨z, hz⟩ := Z
  change hU.fromSpec q = z at hq
  subst hq
  have : q.asIdeal.IsPrime := PrimeSpectrum.isPrime q
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec q, affine_fromSpec_mem hU q⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec q)) q.asIdeal :=
    hU.isLocalization_stalk' q (affine_fromSpec_mem hU q)
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField X (affine_fromSpec_mem hU q)]
  apply PrimeDivisor.ord_algebraMap_of_maximalIdeal_eq ⟨hU.fromSpec q, hz⟩
  change IsLocalRing.maximalIdeal (X.presheaf.stalk (hU.fromSpec q)) =
    Ideal.span {algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec q)) a}
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q.asIdeal]
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro b hb
    obtain ⟨c, t, ht, hbt⟩ := hgen b hb
    rw [Ideal.mem_comap, Ideal.mem_span_singleton]
    have hu : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec q)) t) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff _ q.asIdeal t).mpr ht
    refine ⟨algebraMap _ _ c * ↑hu.unit⁻¹, ?_⟩
    have h2 := congrArg (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec q))) hbt
    rw [map_mul, map_mul] at h2
    rw [← mul_assoc, ← h2, mul_assoc, IsUnit.mul_val_inv, mul_one]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ ha

/- English proof (translation)
Take `⟨z, hz⟩` from `Z`. Express the relevant statement in the definitionally equal form `hU.fromSpec q = z at hq`. Substitute `hq` using the available equality. Establish `: q.asIdeal.IsPrime` using `PrimeSpectrum.isPrime q`. Set `_` to `TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec q, affine_fromSpec_mem hU q⟩`.

Establish `: IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec q)) q.asIdeal` using `hU.isLocalization_stalk' q (affine_fromSpec_mem hU q)`. Rewrite using `[← Scheme.algebraMap_germ_eq_germToFunctionField X (affine_fromSpec_mem hU q)]`. Conclude with `PrimeDivisor.ord_algebraMap_of_isUnit ⟨hU.fromSpec q, hz⟩ ((IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk (hU.fromSpec q)) q.asIdeal a).mpr ha)`.
-/
lemma affine_ord_eq_zero (Z : PrimeDivisor X) (q : Spec Γ(X, U))
    (hq : hU.fromSpec q = Z.point) [Nonempty U] {a : Γ(X, U)} (ha : a ∉ q.asIdeal) :
    Z.ord (X.germToFunctionField U a) = 0 := by
  obtain ⟨z, hz⟩ := Z
  change hU.fromSpec q = z at hq
  subst hq
  have : q.asIdeal.IsPrime := PrimeSpectrum.isPrime q
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec q, affine_fromSpec_mem hU q⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec q)) q.asIdeal :=
    hU.isLocalization_stalk' q (affine_fromSpec_mem hU q)
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField X (affine_fromSpec_mem hU q)]
  exact PrimeDivisor.ord_algebraMap_of_isUnit ⟨hU.fromSpec q, hz⟩
    ((IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk (hU.fromSpec q)) q.asIdeal
      a).mpr ha)

end Affine

section Uniformizer

variable [IsIntegral X] [IsLocallyNoetherian X] [IsLocallyFactorial X]

/- English proof (translation)
Take `⟨_, ⟨U, hU, rfl⟩, hxU, -⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ`. Establish `hne : Nonempty U` using `⟨⟨x, hxU⟩⟩`. Use `set p := hU.primeIdealOf ⟨x, hxU⟩`. Establish `hpx : hU.fromSpec p = x` using `hU.fromSpec_primeIdealOf ⟨x, hxU⟩`. Establish `hmem : ∀ Z : PrimeDivisor X, Z.point ⤳ x → Z.point ∈ U` using `fun Z hZ => hZ.mem_open U.isOpen hxU`.

Establish `hq : ∀ Z : PrimeDivisor X, ∀ hZ : Z.point ⤳ x, hU.fromSpec (hU.primeIdealOf ⟨Z.point, hmem Z hZ⟩) = Z.point` using `fun Z hZ => hU.fromSpec_primeIdealOf ⟨Z.point, hmem Z hZ⟩`. Establish `hle : ∀ Z : PrimeDivisor X, ∀ hZ : Z.point ⤳ x, (hU.primeIdealOf ⟨Z.point, hmem Z hZ⟩).asIdeal ≤ p.asIdeal` using `fun Z hZ => (affine_fromSpec_specializes_iff hU _ p).mp (by rw [hq Z hZ, hpx]; exact hZ)`. Establish `: p.asIdeal.IsPrime` using `PrimeSpectrum.isPrime p`. Set `_` to `TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec p, affine_fromSpec_mem hU p⟩`. Establish `: IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec p)) p.asIdeal` using `hU.isLocalization_stalk' p (affine_fromSpec_mem hU p)`.

Use `IsLocallyFactorial.ufm_stalk (X := X) (hU.fromSpec p)` as an intermediate fact. Take `⟨a, haq, hgen, huniq⟩` from `exists_local_generator p.asIdeal (X.presheaf.stalk (hU.fromSpec p)) (hle Y hYx) (affine_height_eq_one hU Y _ (hq Y hYx))`. Use `⟨U, hne, a, hxU, ?_, ?_⟩` and prove the remaining obligations. Use `affine_ord_eq_one hU Y _ (hq Y hYx) haq fun b hb => ?_` and prove the remaining obligations. Take `⟨c, t, ht, hbt⟩` from `hgen b hb`.

Conclude with `⟨c, t, fun h => ht (hle Y hYx h), hbt⟩`. Introduce `Z hZx hZY`. Use `affine_ord_eq_zero hU Z _ (hq Z hZx) fun haZ => hZY ?_` and prove the remaining obligations. Establish `h` using `huniq _ inferInstance (hle Z hZx) (affine_height_eq_one hU Z _ (hq Z hZx)) haZ`. Establish `h2 : hU.primeIdealOf ⟨Z.point, hmem Z hZx⟩ = hU.primeIdealOf ⟨Y.point, hmem Y hYx⟩` using `PrimeSpectrum.ext h`.

Apply `PrimeDivisor.point_injective` to reduce the goal to its premises. Rewrite using `[← hq Z hZx, ← hq Y hYx, h2]`.
-/
theorem exists_local_uniformizer (x : X) (Y : PrimeDivisor X) (hYx : Y.point ⤳ x) :
    ∃ (U : X.Opens) (_ : Nonempty U) (a : Γ(X, U)), x ∈ U ∧
      Y.ord (X.germToFunctionField U a) = 1 ∧
      ∀ Z : PrimeDivisor X, Z.point ⤳ x → Z ≠ Y → Z.ord (X.germToFunctionField U a) = 0 := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hne : Nonempty U := ⟨⟨x, hxU⟩⟩
  set p := hU.primeIdealOf ⟨x, hxU⟩
  have hpx : hU.fromSpec p = x := hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  have hmem : ∀ Z : PrimeDivisor X, Z.point ⤳ x → Z.point ∈ U :=
    fun Z hZ => hZ.mem_open U.isOpen hxU
  have hq : ∀ Z : PrimeDivisor X, ∀ hZ : Z.point ⤳ x,
      hU.fromSpec (hU.primeIdealOf ⟨Z.point, hmem Z hZ⟩) = Z.point :=
    fun Z hZ => hU.fromSpec_primeIdealOf ⟨Z.point, hmem Z hZ⟩
  have hle : ∀ Z : PrimeDivisor X, ∀ hZ : Z.point ⤳ x,
      (hU.primeIdealOf ⟨Z.point, hmem Z hZ⟩).asIdeal ≤ p.asIdeal := fun Z hZ =>
    (affine_fromSpec_specializes_iff hU _ p).mp (by rw [hq Z hZ, hpx]; exact hZ)
  have : p.asIdeal.IsPrime := PrimeSpectrum.isPrime p
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec p, affine_fromSpec_mem hU p⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec p)) p.asIdeal :=
    hU.isLocalization_stalk' p (affine_fromSpec_mem hU p)
  have := IsLocallyFactorial.ufm_stalk (X := X) (hU.fromSpec p)
  obtain ⟨a, haq, hgen, huniq⟩ := exists_local_generator p.asIdeal
    (X.presheaf.stalk (hU.fromSpec p)) (hle Y hYx)
    (affine_height_eq_one hU Y _ (hq Y hYx))
  refine ⟨U, hne, a, hxU, ?_, ?_⟩
  · refine affine_ord_eq_one hU Y _ (hq Y hYx) haq fun b hb => ?_
    obtain ⟨c, t, ht, hbt⟩ := hgen b hb
    exact ⟨c, t, fun h => ht (hle Y hYx h), hbt⟩
  · intro Z hZx hZY
    refine affine_ord_eq_zero hU Z _ (hq Z hZx) fun haZ => hZY ?_
    have h := huniq _ inferInstance (hle Z hZx) (affine_height_eq_one hU Z _ (hq Z hZx)) haZ
    have h2 : hU.primeIdealOf ⟨Z.point, hmem Z hZx⟩ = hU.primeIdealOf ⟨Y.point, hmem Y hYx⟩ :=
      PrimeSpectrum.ext h
    apply PrimeDivisor.point_injective
    rw [← hq Z hZx, ← hq Y hYx, h2]

end Uniformizer

section LocallyPrincipal

variable [IsIntegral X] [IsNoetherian X] [IsLocallyFactorial X]

/- English proof (translation)
Establish `H : ∀ Y : PrimeDivisor X, ∃ u : (X.functionField)ˣ, Y.point ⤳ x → Y.ord (u : X.functionField) = 1 ∧ ∀ Z : PrimeDivisor X, Z.point ⤳ x → Z ≠ Y → Z.ord (u : X.functionField) = 0`. Introduce `Y`. Distinguish the cases in `hY : Y.point ⤳ x`. Take `⟨U, hU, a, -, h1, h0⟩` from `exists_local_uniformizer x Y hY`. Establish `ha : X.germToFunctionField U a ≠ 0`.

Introduce `h`. Rewrite `h1` using `[h, PrimeDivisor.ord_zero]`. Conclude with `zero_ne_one h1`. Conclude with `⟨Units.mk0 _ ha, fun _ => ⟨h1, h0⟩⟩`. Conclude with `⟨1, fun h => absurd h hY⟩`.

Use `choose u hu using H`. Use `set S : Finset (PrimeDivisor X) := D.support.filter (fun Y => Y.point ⤳ x)`. Use `set g : (X.functionField)ˣ := ∏ Y ∈ S, u Y ^ D Y`. Establish `hdiv : ∀ Z : PrimeDivisor X, Z.point ⤳ x → principalDivisor (Additive.ofMul g) Z = D Z`. Introduce `Z hZ`.

Establish `hsum : principalDivisor (Additive.ofMul g) = ∑ Y ∈ S, D Y • principalDivisor (Additive.ofMul (u Y))`. Simplify using `only [g, ofMul_prod, ofMul_zpow, map_sum, map_zsmul]`. Rewrite using `[hsum, Finset.sum_apply']`. Simplify using `only [Finsupp.smul_apply, smul_eq_mul, principalDivisor_apply]`. Distinguish the cases in `hZS : Z ∈ S`.

Rewrite using `[Finset.sum_eq_single Z]`. Rewrite using `[((hu Z) hZ).1, mul_one]`. Introduce `Y hY hYZ`. Establish `hYx : Y.point ⤳ x` using `(Finset.mem_filter.mp hY).2`. Rewrite using `[((hu Y) hYx).2 Z hZ (Ne.symm hYZ), mul_zero]`.

Conclude with `fun h => absurd hZS h`. Establish `hDZ : D Z = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hZS (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hne, hZ⟩)`. Rewrite using `[hDZ]`.

Use `Finset.sum_eq_zero fun Y hY => ?_` and prove the remaining obligations. Establish `hYx : Y.point ⤳ x` using `(Finset.mem_filter.mp hY).2`. Establish `hYZ : Z ≠ Y` using `fun h => hZS (h ▸ hY)`. Rewrite using `[((hu Y) hYx).2 Z hZ hYZ, mul_zero]`. Use `set T : Finset (PrimeDivisor X) := (D.support ∪ (principalDivisor (Additive.ofMul g)).support).filter (fun Z => ¬ Z.point ⤳ x)`.

Establish `hT : IsClosed (⋃ Z ∈ T, closure {Z.point})` using `isClosed_biUnion_finset fun _ _ => isClosed_closure`. Use `⟨⟨(⋃ Z ∈ T, closure {Z.point})ᶜ, hT.isOpen_compl⟩, g, ?_, ?_⟩` and prove the remaining obligations. Use `show x ∈ (⋃ Z ∈ T, closure {Z.point})ᶜ`. Simplify using `only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]`. Introduce `Z hZ hxZ`.

Conclude with `(Finset.mem_filter.mp hZ).2 (specializes_iff_mem_closure.mpr hxZ)`. Introduce `Z hZV`. Distinguish the cases in `hZx : Z.point ⤳ x`. Conclude with `hdiv Z hZx`. Establish `hZT : Z ∉ T`.

Introduce `hZT`. Establish `: Z.point ∈ (⋃ Z ∈ T, closure {Z.point})` using `Set.mem_biUnion hZT (subset_closure rfl)`. Conclude with `hZV this`. Simplify using `only [T, Finset.mem_filter, Finset.mem_union, Finsupp.mem_support_iff, not_and, not_not] at hZT`. Distinguish the cases in `h1 : D Z = 0`.

Rewrite using `[h1]`. Assume the negation of the conclusion as `h2`. Conclude with `hZx (hZT (Or.inr h2))`. Conclude with `absurd (hZT (Or.inl h1)) hZx`.
-/
theorem WeilDivisor.exists_local_equation (D : WeilDivisor X) (x : X) :
    ∃ (V : X.Opens) (g : (X.functionField)ˣ), x ∈ V ∧
      ∀ Z : PrimeDivisor X, Z.point ∈ V → principalDivisor (Additive.ofMul g) Z = D Z := by
  classical
  have H : ∀ Y : PrimeDivisor X, ∃ u : (X.functionField)ˣ, Y.point ⤳ x →
      Y.ord (u : X.functionField) = 1 ∧
      ∀ Z : PrimeDivisor X, Z.point ⤳ x → Z ≠ Y → Z.ord (u : X.functionField) = 0 := by
    intro Y
    by_cases hY : Y.point ⤳ x
    · obtain ⟨U, hU, a, -, h1, h0⟩ := exists_local_uniformizer x Y hY
      have ha : X.germToFunctionField U a ≠ 0 := by
        intro h
        rw [h, PrimeDivisor.ord_zero] at h1
        exact zero_ne_one h1
      exact ⟨Units.mk0 _ ha, fun _ => ⟨h1, h0⟩⟩
    · exact ⟨1, fun h => absurd h hY⟩
  choose u hu using H
  set S : Finset (PrimeDivisor X) := D.support.filter (fun Y => Y.point ⤳ x)
  set g : (X.functionField)ˣ := ∏ Y ∈ S, u Y ^ D Y
  have hdiv : ∀ Z : PrimeDivisor X, Z.point ⤳ x → principalDivisor (Additive.ofMul g) Z = D Z := by
    intro Z hZ
    have hsum : principalDivisor (Additive.ofMul g) =
        ∑ Y ∈ S, D Y • principalDivisor (Additive.ofMul (u Y)) := by
      simp only [g, ofMul_prod, ofMul_zpow, map_sum, map_zsmul]
    rw [hsum, Finset.sum_apply']
    simp only [Finsupp.smul_apply, smul_eq_mul, principalDivisor_apply]
    by_cases hZS : Z ∈ S
    · rw [Finset.sum_eq_single Z]
      · rw [((hu Z) hZ).1, mul_one]
      · intro Y hY hYZ
        have hYx : Y.point ⤳ x := (Finset.mem_filter.mp hY).2
        rw [((hu Y) hYx).2 Z hZ (Ne.symm hYZ), mul_zero]
      · exact fun h => absurd hZS h
    · have hDZ : D Z = 0 := by
        by_contra hne
        exact hZS (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hne, hZ⟩)
      rw [hDZ]
      refine Finset.sum_eq_zero fun Y hY => ?_
      have hYx : Y.point ⤳ x := (Finset.mem_filter.mp hY).2
      have hYZ : Z ≠ Y := fun h => hZS (h ▸ hY)
      rw [((hu Y) hYx).2 Z hZ hYZ, mul_zero]
  set T : Finset (PrimeDivisor X) :=
    (D.support ∪ (principalDivisor (Additive.ofMul g)).support).filter (fun Z => ¬ Z.point ⤳ x)
  have hT : IsClosed (⋃ Z ∈ T, closure {Z.point}) :=
    isClosed_biUnion_finset fun _ _ => isClosed_closure
  refine ⟨⟨(⋃ Z ∈ T, closure {Z.point})ᶜ, hT.isOpen_compl⟩, g, ?_, ?_⟩
  · show x ∈ (⋃ Z ∈ T, closure {Z.point})ᶜ
    simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    intro Z hZ hxZ
    exact (Finset.mem_filter.mp hZ).2 (specializes_iff_mem_closure.mpr hxZ)
  · intro Z hZV
    by_cases hZx : Z.point ⤳ x
    · exact hdiv Z hZx
    · have hZT : Z ∉ T := by
        intro hZT
        have : Z.point ∈ (⋃ Z ∈ T, closure {Z.point}) :=
          Set.mem_biUnion hZT (subset_closure rfl)
        exact hZV this
      simp only [T, Finset.mem_filter, Finset.mem_union, Finsupp.mem_support_iff, not_and,
        not_not] at hZT
      by_cases h1 : D Z = 0
      · rw [h1]
        by_contra h2
        exact hZx (hZT (Or.inr h2))
      · exact absurd (hZT (Or.inl h1)) hZx

end LocallyPrincipal

section Regular

variable [IsIntegral X] [IsLocallyNoetherian X] [IsLocallyFactorial X]

/- English proof (translation)
Distinguish the cases in `hf0 : f = 0`. Conclude with `⟨0, by simp [hf0]⟩`. Take `⟨_, ⟨U, hU, rfl⟩, hxU, -⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ`. Establish `hne : Nonempty U` using `⟨⟨x, hxU⟩⟩`. Take `⟨p, rfl⟩ : ∃ p, hU.fromSpec p = x` from `⟨_, hU.fromSpec_primeIdealOf ⟨x, hxU⟩⟩`.

Establish `: p.asIdeal.IsPrime` using `PrimeSpectrum.isPrime p`. Set `_` to `TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec p, affine_fromSpec_mem hU p⟩`. Establish `: IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec p)) p.asIdeal` using `hU.isLocalization_stalk' p (affine_fromSpec_mem hU p)`. Use `IsLocallyFactorial.ufm_stalk (X := X) (hU.fromSpec p)` as an intermediate fact. Apply `mem_range_of_forall_prime` to reduce the goal to its premises.

Introduce `π hπ`. Establish `hQ : (Ideal.span {π}).IsPrime` using `(Ideal.span_singleton_prime hπ.ne_zero).mpr hπ`. Use `set q : Spec Γ(X, U) := ⟨(Ideal.span {π}).comap (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec p))), Ideal.comap_isPrime _ _⟩`. Establish `hqp : q.asIdeal ≤ p.asIdeal`. Rewrite using `[← IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk (hU.fromSpec p)) p.asIdeal]`.

Apply `Ideal.comap_mono` to reduce the goal to its premises. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `(IsLocalRing.mem_maximalIdeal π).mpr hπ.not_isUnit`. Establish `hqh : q.asIdeal.height = 1`. Express the relevant statement in the definitionally equal form `(Ideal.under Γ(X, U) (Ideal.span {π})).height = 1`.

Rewrite using `[IsLocalization.height_under p.asIdeal.primeCompl, height_span_prime hπ]`. Establish `hzx : hU.fromSpec q ⤳ hU.fromSpec p` using `(affine_fromSpec_specializes_iff hU q p).mpr hqp`. Establish `: q.asIdeal.IsPrime` using `PrimeSpectrum.isPrime q`. Set `_` to `TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec q, affine_fromSpec_mem hU q⟩`. Establish `hlocq : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec q)) q.asIdeal` using `hU.isLocalization_stalk' q (affine_fromSpec_mem hU q)`.

Establish `hdim : ringKrullDim (X.presheaf.stalk (hU.fromSpec q)) = 1`. Rewrite using `[IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal, hqh]`. Both sides reduce to the same expression. Set `Z : PrimeDivisor X` to `⟨hU.fromSpec q, hdim⟩`. Establish `hmem : f ∈ (algebraMap (X.presheaf.stalk (hU.fromSpec q)) X.functionField).range` using `(Z.ord_nonneg_iff hf0).mp (h Z hzx)`.

Take `⟨w, hw⟩` from `hmem`. Take `⟨⟨b', t'⟩, rfl⟩` from `IsLocalization.mk'_surjective q.asIdeal.primeCompl w`. Establish `hcompat : ∀ (y : Spec Γ(X, U)) (a : Γ(X, U)),`. Use `letI := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, affine_fromSpec_mem hU y⟩`. Use `algebraMap (X.presheaf.stalk (hU.fromSpec y)) X.functionField (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) a) = X.germToFunctionField U a :=`.

Use `fun y a => Scheme.algebraMap_germ_eq_germToFunctionField X (affine_fromSpec_mem hU y) a`. Establish `hft : f * X.germToFunctionField U t' = X.germToFunctionField U b'`. Rewrite using `[← hw, ← hcompat q t', ← hcompat q b', ← map_mul]`. Use `congr 1`. Conclude with `IsLocalization.mk'_spec _ _ _`.

Use `⟨algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec p)) b', algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec p)) t', ?_, ?_⟩` and prove the remaining obligations. Introduce `hdvd`. Apply `t'.2` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec p)) t' ∈ Ideal.span {π}`. Conclude with `Ideal.mem_span_singleton.mpr hdvd`.

Rewrite using `[hcompat p t', hcompat p b', hft]`.
-/
theorem mem_range_stalk_of_ord_nonneg (x : X) (f : X.functionField)
    (h : ∀ Z : PrimeDivisor X, Z.point ⤳ x → 0 ≤ Z.ord f) :
    f ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  by_cases hf0 : f = 0
  · exact ⟨0, by simp [hf0]⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hne : Nonempty U := ⟨⟨x, hxU⟩⟩
  obtain ⟨p, rfl⟩ : ∃ p, hU.fromSpec p = x := ⟨_, hU.fromSpec_primeIdealOf ⟨x, hxU⟩⟩
  have : p.asIdeal.IsPrime := PrimeSpectrum.isPrime p
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec p, affine_fromSpec_mem hU p⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec p)) p.asIdeal :=
    hU.isLocalization_stalk' p (affine_fromSpec_mem hU p)
  have := IsLocallyFactorial.ufm_stalk (X := X) (hU.fromSpec p)
  apply mem_range_of_forall_prime
  intro π hπ
  have hQ : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
  set q : Spec Γ(X, U) := ⟨(Ideal.span {π}).comap (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec p))), Ideal.comap_isPrime _ _⟩
  have hqp : q.asIdeal ≤ p.asIdeal := by
    rw [← IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk (hU.fromSpec p)) p.asIdeal]
    apply Ideal.comap_mono
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact (IsLocalRing.mem_maximalIdeal π).mpr hπ.not_isUnit
  have hqh : q.asIdeal.height = 1 := by
    change (Ideal.under Γ(X, U) (Ideal.span {π})).height = 1
    rw [IsLocalization.height_under p.asIdeal.primeCompl, height_span_prime hπ]
  have hzx : hU.fromSpec q ⤳ hU.fromSpec p := (affine_fromSpec_specializes_iff hU q p).mpr hqp
  have : q.asIdeal.IsPrime := PrimeSpectrum.isPrime q
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec q, affine_fromSpec_mem hU q⟩
  have hlocq : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec q)) q.asIdeal :=
    hU.isLocalization_stalk' q (affine_fromSpec_mem hU q)
  have hdim : ringKrullDim (X.presheaf.stalk (hU.fromSpec q)) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal, hqh]
    rfl
  let Z : PrimeDivisor X := ⟨hU.fromSpec q, hdim⟩
  have hmem : f ∈ (algebraMap (X.presheaf.stalk (hU.fromSpec q)) X.functionField).range :=
    (Z.ord_nonneg_iff hf0).mp (h Z hzx)
  obtain ⟨w, hw⟩ := hmem
  obtain ⟨⟨b', t'⟩, rfl⟩ := IsLocalization.mk'_surjective q.asIdeal.primeCompl w
  have hcompat : ∀ (y : Spec Γ(X, U)) (a : Γ(X, U)),
      letI := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, affine_fromSpec_mem hU y⟩
      algebraMap (X.presheaf.stalk (hU.fromSpec y)) X.functionField
        (algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) a) = X.germToFunctionField U a :=
    fun y a => Scheme.algebraMap_germ_eq_germToFunctionField X (affine_fromSpec_mem hU y) a
  have hft : f * X.germToFunctionField U t' = X.germToFunctionField U b' := by
    rw [← hw, ← hcompat q t', ← hcompat q b', ← map_mul]
    congr 1
    exact IsLocalization.mk'_spec _ _ _
  refine ⟨algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec p)) b',
    algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec p)) t', ?_, ?_⟩
  · intro hdvd
    apply t'.2
    change algebraMap Γ(X, U) (X.presheaf.stalk (hU.fromSpec p)) t' ∈ Ideal.span {π}
    exact Ideal.mem_span_singleton.mpr hdvd
  · rw [hcompat p t', hcompat p b', hft]

end Regular

section Regular

variable [IsIntegral X] [IsLocallyNoetherian X] [IsLocallyFactorial X]

/- English proof (translation)
Establish `hloc : ∀ x : V, ∃ (W : X.Opens) (hxW : x.1 ∈ W), W ≤ V ∧ ∃ s : Γ(X, W), X.germToFunctionField W (h` using `⟨⟨x.1, hxW⟩⟩) s = f := by`. Introduce `x`. Take `⟨w, hw⟩` from `mem_range_stalk_of_ord_nonneg x.1 f (fun Z hZ => h Z (hZ.mem_open V.isOpen x.2))`. Take `⟨W, hxW, g, hg⟩` from `X.presheaf.exists_germ_eq w`. Use `⟨W ⊓ V, ⟨hxW, x.2⟩, inf_le_right, X.presheaf.map (homOfLE inf_le_left).op g, ?_⟩` and prove the remaining obligations.

Establish `: Nonempty W` using `⟨⟨x.1, hxW⟩⟩`. Rewrite using `[← hw, ← hg, Scheme.algebraMap_germ_eq_germToFunctionField]`. Simplify using the standard rewrite rules. Use `choose W hxW hWV s hs using hloc`. Establish `hcompat : TopCat.Presheaf.IsCompatible X.sheaf.obj W s`.

Introduce `i j`. Establish `hne : ((W i : Set X) ∩ W j).Nonempty` using `nonempty_preirreducible_inter (W i).isOpen (W j).isOpen ⟨_, hxW i⟩ ⟨_, hxW j⟩`. Take `⟨y, hy⟩` from `hne`. Establish `: Nonempty (W i ⊓ W j : X.Opens)` using `⟨⟨y, hy⟩⟩`. Establish `: Nonempty (W i)` using `⟨⟨_, hxW i⟩⟩`.

Establish `: Nonempty (W j)` using `⟨⟨_, hxW j⟩⟩`. Apply `Scheme.germToFunctionField_injective X (W i ⊓ W j)` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `X.germToFunctionField (W i ⊓ W j) (X.presheaf.map (homOfLE inf_le_left).op (s i)) = X.germToFunctionField (W i ⊓ W j) (X.presheaf.map (homOfLE inf_le_right).op (s j))`. Simplify using `[hs]`. Take `⟨t, ht, -⟩` from `X.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hWV i)) (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW _⟩) s hcompat`.

Use `⟨t, ?_⟩` and prove the remaining obligations. Take `⟨i⟩` from `‹Nonempty V›`. Establish `: Nonempty (W i)` using `⟨⟨_, hxW i⟩⟩`. Rewrite using `[← hs i, ← ht i]`. Express the relevant statement in the definitionally equal form `_ = X.germToFunctionField (W i) (X.presheaf.map (homOfLE (hWV i)).op t)`.

Conclude with `(TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm`.
-/
theorem exists_section_of_ord_nonneg (V : X.Opens) [Nonempty V] (f : X.functionField)
    (h : ∀ Z : PrimeDivisor X, Z.point ∈ V → 0 ≤ Z.ord f) :
    ∃ s : Γ(X, V), X.germToFunctionField V s = f := by
  have hloc : ∀ x : V, ∃ (W : X.Opens) (hxW : x.1 ∈ W), W ≤ V ∧
      ∃ s : Γ(X, W), X.germToFunctionField W (h := ⟨⟨x.1, hxW⟩⟩) s = f := by
    intro x
    obtain ⟨w, hw⟩ := mem_range_stalk_of_ord_nonneg x.1 f
      (fun Z hZ => h Z (hZ.mem_open V.isOpen x.2))
    obtain ⟨W, hxW, g, hg⟩ := X.presheaf.exists_germ_eq w
    refine ⟨W ⊓ V, ⟨hxW, x.2⟩, inf_le_right, X.presheaf.map (homOfLE inf_le_left).op g, ?_⟩
    have : Nonempty W := ⟨⟨x.1, hxW⟩⟩
    rw [← hw, ← hg, Scheme.algebraMap_germ_eq_germToFunctionField]
    simp
  choose W hxW hWV s hs using hloc
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.obj W s := by
    intro i j
    have hne : ((W i : Set X) ∩ W j).Nonempty :=
      nonempty_preirreducible_inter (W i).isOpen (W j).isOpen ⟨_, hxW i⟩ ⟨_, hxW j⟩
    obtain ⟨y, hy⟩ := hne
    have : Nonempty (W i ⊓ W j : X.Opens) := ⟨⟨y, hy⟩⟩
    have : Nonempty (W i) := ⟨⟨_, hxW i⟩⟩
    have : Nonempty (W j) := ⟨⟨_, hxW j⟩⟩
    apply Scheme.germToFunctionField_injective X (W i ⊓ W j)
    change X.germToFunctionField (W i ⊓ W j) (X.presheaf.map (homOfLE inf_le_left).op (s i)) =
      X.germToFunctionField (W i ⊓ W j) (X.presheaf.map (homOfLE inf_le_right).op (s j))
    simp [hs]
  obtain ⟨t, ht, -⟩ := X.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hWV i))
    (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW _⟩) s hcompat
  refine ⟨t, ?_⟩
  obtain ⟨i⟩ := ‹Nonempty V›
  have : Nonempty (W i) := ⟨⟨_, hxW i⟩⟩
  rw [← hs i, ← ht i]
  change _ = X.germToFunctionField (W i) (X.presheaf.map (homOfLE (hWV i)).op t)
  exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm

end Regular

end GroundTheory.Arith.SchemeCoh
