import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.StatementsIntegralPointAlgebraic
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.NormLeOneIffIsIntegralElemOfEquiv
import GroundTheory.GlobalFields.LocalFieldAtPlace
import GroundTheory.GlobalFields.CompletionAtPlace
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel

noncomputable section

namespace IntegralPointOfAlgebraicDomain

section FractionField

variable {F : Type*} [Field F] [NumberField F] {S : Type*} [CommRing S]
  [Algebra (𝓞 F) S] {K : Type*} [Field K] [Algebra S K] [IsFractionRing S K] [Algebra F K]

/- English proof (translation)
Take `⟨s, hs⟩` from `Algebra.FiniteType.out (R := 𝓞 F) (A := S)`. Set `f : S →ₐ[𝓞 F] K` to `{ algebraMap S K with commutes' := fun r ↦ by`. Rewrite using `[IsScalarTower.algebraMap_apply (𝓞 F) F K]`. Conclude with `(hc r).symm }`. Use `set t : Set K := f '' (s : Set S)`.

Establish `hinj : Function.Injective (algebraMap (𝓞 F) F)` using `IsFractionRing.injective _ _`. Establish `hint : ∀ x ∈ t, IsIntegral F x`. Introduce and unpack `_ ⟨x, -, rfl⟩`. Conclude with `(((Algebra.IsAlgebraic.isAlgebraic (R := 𝓞 F) x).algHom f).extendScalars hinj).isIntegral`. Establish `: Finite t` using `(s.finite_toSet.image _).to_subtype`.

Establish `hfin` using `IntermediateField.finiteDimensional_adjoin hint`. Use `set E := IntermediateField.adjoin F t`. Establish `hS : ∀ x : S, algebraMap S K x ∈ E`. Establish `hle : (⊤ : Subalgebra (𝓞 F) S) ≤ (E.toSubalgebra.restrictScalars (𝓞 F)).comap f`. Rewrite using `[← hs]`.

Conclude with `Algebra.adjoin_le fun x hx ↦ IntermediateField.subset_adjoin F t ⟨x, hx, rfl⟩`. Conclude with `fun x ↦ hle Algebra.mem_top`. Establish `hE : E = ⊤`. Use `eq_top_iff.2 fun z _ ↦ ?_` and prove the remaining obligations. Take `⟨a, b, -, rfl⟩` from `IsFractionRing.div_surjective (A := S) z`.

Conclude with `E.div_mem (hS a) (hS b)`. Rewrite `hfin` using `[hE]`. Conclude with `(IntermediateField.topEquiv (F := F) (E := K)).toLinearEquiv.finiteDimensional`.
-/
theorem finiteDimensional_of_isFractionRing [Algebra.FiniteType (𝓞 F) S]
    [Algebra.IsAlgebraic (𝓞 F) S]
    (hc : ∀ r : 𝓞 F, algebraMap F K (algebraMap (𝓞 F) F r) = algebraMap S K (algebraMap (𝓞 F) S r)) :
    FiniteDimensional F K := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := 𝓞 F) (A := S)
  let f : S →ₐ[𝓞 F] K :=
    { algebraMap S K with
      commutes' := fun r ↦ by
        rw [IsScalarTower.algebraMap_apply (𝓞 F) F K]
        exact (hc r).symm }
  set t : Set K := f '' (s : Set S)
  have hinj : Function.Injective (algebraMap (𝓞 F) F) := IsFractionRing.injective _ _
  have hint : ∀ x ∈ t, IsIntegral F x := by
    rintro _ ⟨x, -, rfl⟩
    exact (((Algebra.IsAlgebraic.isAlgebraic (R := 𝓞 F) x).algHom f).extendScalars hinj).isIntegral
  have : Finite t := (s.finite_toSet.image _).to_subtype
  have hfin := IntermediateField.finiteDimensional_adjoin hint
  set E := IntermediateField.adjoin F t
  have hS : ∀ x : S, algebraMap S K x ∈ E := by
    have hle : (⊤ : Subalgebra (𝓞 F) S) ≤ (E.toSubalgebra.restrictScalars (𝓞 F)).comap f := by
      rw [← hs]
      exact Algebra.adjoin_le fun x hx ↦ IntermediateField.subset_adjoin F t ⟨x, hx, rfl⟩
    exact fun x ↦ hle Algebra.mem_top
  have hE : E = ⊤ := by
    refine eq_top_iff.2 fun z _ ↦ ?_
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := S) z
    exact E.div_mem (hS a) (hS b)
  rw [hE] at hfin
  exact (IntermediateField.topEquiv (F := F) (E := K)).toLinearEquiv.finiteDimensional

end FractionField

section Place

variable {K : Type*} [Field K] {S : Type*} [CommRing S]
  [Algebra S K] [IsFractionRing S K] (M : Ideal S) [M.IsMaximal]

/- English proof (translation)
Set `e : S →+* (algebraMap S K).range` to `(algebraMap S K).rangeRestrict`. Establish `he : Function.Bijective e` using `⟨fun a b h ↦ IsFractionRing.injective S K (congrArg Subtype.val h), (algebraMap S K).rangeRestrict_surjective⟩`. Establish `hI : M.map e ≠ ⊤`. Introduce `h`. Establish `h'` using `congrArg (Ideal.comap e) h`.

Rewrite `h'` using `[Ideal.comap_map_of_bijective e he, Ideal.comap_top]`. Conclude with `(‹M.IsMaximal›).ne_top h'`. Take `⟨B, hAB, hB⟩` from `Ideal.image_subset_nonunits_valuationSubring (M.map e) hI`. Use `⟨B, fun s ↦ hAB (RingHom.mem_range.2 ⟨s, rfl⟩), fun s hs ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[← ValuationSubring.mem_nonunits_iff]`.

Conclude with `hB ⟨e s, Ideal.mem_map_of_mem e hs, rfl⟩`.
-/
theorem exists_valuationSubring :
    ∃ B : ValuationSubring K, (∀ s : S, algebraMap S K s ∈ B) ∧
      ∀ s ∈ M, B.valuation (algebraMap S K s) < 1 := by
  let e : S →+* (algebraMap S K).range := (algebraMap S K).rangeRestrict
  have he : Function.Bijective e :=
    ⟨fun a b h ↦ IsFractionRing.injective S K (congrArg Subtype.val h),
      (algebraMap S K).rangeRestrict_surjective⟩
  have hI : M.map e ≠ ⊤ := by
    intro h
    have h' := congrArg (Ideal.comap e) h
    rw [Ideal.comap_map_of_bijective e he, Ideal.comap_top] at h'
    exact (‹M.IsMaximal›).ne_top h'
  obtain ⟨B, hAB, hB⟩ := Ideal.image_subset_nonunits_valuationSubring (M.map e) hI
  refine ⟨B, fun s ↦ hAB (RingHom.mem_range.2 ⟨s, rfl⟩), fun s hs ↦ ?_⟩
  rw [← ValuationSubring.mem_nonunits_iff]
  exact hB ⟨e s, Ideal.mem_map_of_mem e hs, rfl⟩

/- English proof (translation)
Establish `h : IsIntegral B (algebraMap (𝓞 K) K x)` using `(RingOfIntegers.isIntegral_coe x).tower_top`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.1 h`. Rewrite using `[← hy]`. Conclude with `y.2`.
-/
theorem algebraMap_ringOfIntegers_mem [NumberField K] (B : ValuationSubring K) (x : 𝓞 K) :
    algebraMap (𝓞 K) K x ∈ B := by
  have h : IsIntegral B (algebraMap (𝓞 K) K x) := (RingOfIntegers.isIntegral_coe x).tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [← hy]
  exact y.2

/- English proof (translation)
Take `⟨B, hSB, hMB⟩` from `exists_valuationSubring (K := K) M`. Establish `hO : ∀ x : 𝓞 K, B.valuation (algebraMap (𝓞 K) K x) ≤ 1` using `fun x ↦ (B.valuation_le_one_iff _).2 (algebraMap_ringOfIntegers_mem B x)`. Set `φ : 𝓞 K →+* B` to `(algebraMap (𝓞 K) K).codRestrict B (algebraMap_ringOfIntegers_mem B)`. Set `P : Ideal (𝓞 K)` to `(IsLocalRing.maximalIdeal B).comap φ`. Establish `hP : ∀ x : 𝓞 K, x ∈ P ↔ B.valuation (algebraMap (𝓞 K) K x) < 1` using `fun x ↦ B.valuation_lt_one_iff (φ x)`.

Establish `hne : P ≠ ⊥`. Introduce `h`. Establish `hx : x₀ ∈ P` using `(hP x₀).2 (h₀ ▸ hMB s₀ hs₀)`. Rewrite `hx` using `[h, Ideal.mem_bot]`. Conclude with `hx₀ hx`.

Set `w : HeightOneSpectrum (𝓞 K)` to `⟨P, Ideal.comap_isPrime φ _, hne⟩`. Establish `key : ∀ z : K, w.valuation K z ≤ 1 → B.valuation z ≤ 1 ∧ (w.valuation K z < 1 → B.valuation z < 1)`. Introduce `z hz`. Take `⟨n, d, hnd⟩` from `w.exists_primeCompl_mul_eq_of_integer z hz`. Establish `hd : B.valuation (algebraMap (𝓞 K) K d) = 1` using `le_antisymm (hO d) (not_lt.1 fun h ↦ d.2 ((hP d).2 h))`.

Establish `hzn : B.valuation z = B.valuation (algebraMap (𝓞 K) K n)`. Rewrite using `[← hnd, map_mul, hd, mul_one]`. Use `⟨hzn ▸ hO n, fun hlt ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[hzn, ← hP n]`. Express the relevant statement in the definitionally equal form `n ∈ w.asIdeal`.

Rewrite using `[← w.valuation_lt_one_iff_mem (K := K)]`. Express the relevant statement in the definitionally equal form `w.valuation K (algebraMap (𝓞 K) K n) < 1`. Rewrite using `[← hnd, map_mul, w.valuation_eq_one_iff_notMem.2 d.2, mul_one]`. Conclude with `hlt`. Use `⟨w, fun s ↦ ?_, fun s hs ↦ ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_le]`. Establish `hx0 : algebraMap S K s ≠ 0`. Introduce `hx`. Rewrite `h` using `[hx, map_zero]`.

Conclude with `not_lt.2 zero_le (h.trans' zero_lt_one)`. Establish `h1` using `((w.valuation K).one_lt_val_iff hx0).1 h`. Establish `h2` using `(key _ h1.le).2 h1`. Establish `h3` using `(B.valuation.one_lt_val_iff hx0).2 h2`. Conclude with `not_lt.2 ((B.valuation_le_one_iff _).2 (hSB s)) h3`.

Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_lt]`. Establish `hx0 : algebraMap S K s ≠ 0`. Introduce `hx`. Rewrite `h` using `[hx, map_zero]`.

Conclude with `not_le.2 zero_lt_one h`. Establish `h1` using `((w.valuation K).one_le_val_iff hx0).1 h`. Establish `h2` using `(key _ h1).1`. Establish `h3` using `(B.valuation.one_le_val_iff hx0).2 h2`. Conclude with `not_lt.2 h3 (hMB s hs)`.
-/
theorem exists_place [NumberField K] (x₀ : 𝓞 K) (hx₀ : x₀ ≠ 0) (s₀ : S) (hs₀ : s₀ ∈ M)
    (h₀ : algebraMap S K s₀ = algebraMap (𝓞 K) K x₀) :
    ∃ w : HeightOneSpectrum (𝓞 K), (∀ s : S, w.valuation K (algebraMap S K s) ≤ 1) ∧
      ∀ s ∈ M, w.valuation K (algebraMap S K s) < 1 := by
  obtain ⟨B, hSB, hMB⟩ := exists_valuationSubring (K := K) M
  have hO : ∀ x : 𝓞 K, B.valuation (algebraMap (𝓞 K) K x) ≤ 1 := fun x ↦
    (B.valuation_le_one_iff _).2 (algebraMap_ringOfIntegers_mem B x)
  let φ : 𝓞 K →+* B := (algebraMap (𝓞 K) K).codRestrict B (algebraMap_ringOfIntegers_mem B)
  let P : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal B).comap φ
  have hP : ∀ x : 𝓞 K, x ∈ P ↔ B.valuation (algebraMap (𝓞 K) K x) < 1 := fun x ↦
    B.valuation_lt_one_iff (φ x)
  have hne : P ≠ ⊥ := by
    intro h
    have hx : x₀ ∈ P := (hP x₀).2 (h₀ ▸ hMB s₀ hs₀)
    rw [h, Ideal.mem_bot] at hx
    exact hx₀ hx
  let w : HeightOneSpectrum (𝓞 K) := ⟨P, Ideal.comap_isPrime φ _, hne⟩
  have key : ∀ z : K, w.valuation K z ≤ 1 →
      B.valuation z ≤ 1 ∧ (w.valuation K z < 1 → B.valuation z < 1) := by
    intro z hz
    obtain ⟨n, d, hnd⟩ := w.exists_primeCompl_mul_eq_of_integer z hz
    have hd : B.valuation (algebraMap (𝓞 K) K d) = 1 :=
      le_antisymm (hO d) (not_lt.1 fun h ↦ d.2 ((hP d).2 h))
    have hzn : B.valuation z = B.valuation (algebraMap (𝓞 K) K n) := by
      rw [← hnd, map_mul, hd, mul_one]
    refine ⟨hzn ▸ hO n, fun hlt ↦ ?_⟩
    rw [hzn, ← hP n]
    change n ∈ w.asIdeal
    rw [← w.valuation_lt_one_iff_mem (K := K)]
    change w.valuation K (algebraMap (𝓞 K) K n) < 1
    rw [← hnd, map_mul,
      w.valuation_eq_one_iff_notMem.2 d.2, mul_one]
    exact hlt
  refine ⟨w, fun s ↦ ?_, fun s hs ↦ ?_⟩
  · by_contra h
    rw [not_le] at h
    have hx0 : algebraMap S K s ≠ 0 := by
      intro hx
      rw [hx, map_zero] at h
      exact not_lt.2 zero_le (h.trans' zero_lt_one)
    have h1 := ((w.valuation K).one_lt_val_iff hx0).1 h
    have h2 := (key _ h1.le).2 h1
    have h3 := (B.valuation.one_lt_val_iff hx0).2 h2
    exact not_lt.2 ((B.valuation_le_one_iff _).2 (hSB s)) h3
  · by_contra h
    rw [not_lt] at h
    have hx0 : algebraMap S K s ≠ 0 := by
      intro hx
      rw [hx, map_zero] at h
      exact not_le.2 zero_lt_one h
    have h1 := ((w.valuation K).one_le_val_iff hx0).1 h
    have h2 := (key _ h1).1
    have h3 := (B.valuation.one_le_val_iff hx0).2 h2
    exact not_lt.2 h3 (hMB s hs)

end Place

section Completion

open GroundTheory.Global GroundTheory.Global.AdicLiesOver

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) [w.asIdeal.LiesOver v.asIdeal]

/- English proof (translation)
Set `φ : v.adicCompletionIntegers F ≃+* 𝒪[v.adicCompletion F]` to `RingEquiv.subringCongr (Subring.ext fun x ↦ (mem_valuationInteger_iff v x).symm)`. Establish `h : completionIntegersTo F v (w.adicCompletion K) = (algebraMap 𝒪[v.adicCompletion F] (w.adicCompletion K)).comp (φ : _ →+* _)` using `rfl`. Rewrite using `[h, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB.isIntegralElem_comp_ringEquiv]`. Express the relevant statement in the definitionally equal form `IsIntegral 𝒪[v.adicCompletion F] z ↔ _`. Rewrite using `[← mem_adicCompletionIntegers, ← mem_valuationInteger_iff]`.

Conclude with `⟨mem_integer_of_isIntegral v w, isIntegral_of_mem_integer v w⟩`.
-/
theorem isIntegralElem_iff_valued_le_one (z : w.adicCompletion K) :
    (completionIntegersTo F v (w.adicCompletion K)).IsIntegralElem z ↔ Valued.v z ≤ 1 := by
  let φ : v.adicCompletionIntegers F ≃+* 𝒪[v.adicCompletion F] :=
    RingEquiv.subringCongr (Subring.ext fun x ↦ (mem_valuationInteger_iff v x).symm)
  have h : completionIntegersTo F v (w.adicCompletion K) =
      (algebraMap 𝒪[v.adicCompletion F] (w.adicCompletion K)).comp (φ : _ →+* _) := rfl
  rw [h, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB.isIntegralElem_comp_ringEquiv]
  change IsIntegral 𝒪[v.adicCompletion F] z ↔ _
  rw [← mem_adicCompletionIntegers, ← mem_valuationInteger_iff]
  exact ⟨mem_integer_of_isIntegral v w, isIntegral_of_mem_integer v w⟩

end Completion

open GroundTheory.Global GroundTheory.Global.AdicLiesOver in

/- English proof (translation)
Introduce `F _ _ S _ _ _ _ v M ⟨hinj, halg, hM, hMv⟩`. Set `K` to `FractionRing S`. Establish `hg : Function.Injective ((algebraMap S K).comp (algebraMap (𝓞 F) S))` using `(IsFractionRing.injective S K).comp hinj`. Set `_ : Algebra F K` to `(IsFractionRing.lift hg).toAlgebra`. Establish `hc : ∀ r : 𝓞 F, algebraMap F K (algebraMap (𝓞 F) F r) = algebraMap S K (algebraMap (𝓞 F) S r)` using `fun r ↦ IsFractionRing.lift_algebraMap hg r`.

Establish `: FiniteDimensional F K` using `finiteDimensional_of_isFractionRing (S := S) hc`. Establish `: NumberField K` using `NumberField.of_module_finite F K`. Establish `hOK : ∀ r : 𝓞 F, algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) r) = algebraMap S K (algebraMap (𝓞 F) S r)` using `fun r ↦ hc r`. Take `⟨p, hpv, hp0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot`. Establish `hpM : algebraMap (𝓞 F) S p ∈ M`.

Rewrite using `[← Ideal.mem_comap, hMv]`. Conclude with `hpv`. Establish `hx0 : algebraMap (𝓞 F) (𝓞 K) p ≠ 0`. Introduce `h`. Establish `h'` using `hOK p`.

Rewrite `h'` using `[h, map_zero]`. Conclude with `hp0 ((map_eq_zero_iff _ hg).1 h'.symm)`. Take `⟨w, hw1, hw2⟩` from `exists_place M _ hx0 _ hpM (hOK p).symm`. Establish `: w.asIdeal.LiesOver v.asIdeal`. Establish `hle : v.asIdeal ≤ w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 K))` using `fun r hr ↦ by`.

Rewrite using `[Ideal.mem_comap, ← w.valuation_lt_one_iff_mem (K := K)]`. Express the relevant statement in the definitionally equal form `w.valuation K (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) r)) < 1`. Rewrite using `[hOK r]`. Conclude with `hw2 _ (by rw [← Ideal.mem_comap, hMv]; exact hr)`. Conclude with `⟨v.isMaximal.eq_of_le (Ideal.comap_isPrime _ w.asIdeal).ne_top hle⟩`.

Establish `hval : ∀ x : K, Valued.v (algebraMap K (w.adicCompletion K) x) = w.valuation K x` using `fun x ↦ valuedAdicCompletion_eq_valuation' w x`. Establish `hunit : ∀ a ∉ M, w.valuation K (algebraMap S K a) = 1`. Introduce `a ha`. Take `⟨b, m, hm, hbm⟩` from `hM.exists_inv ha`. Use `le_antisymm (hw1 a) (not_lt.1 fun hlt ↦ ?_)` and prove the remaining obligations.

Establish `h1 : w.valuation K (algebraMap S K (b * a)) < 1`. Rewrite using `[map_mul, map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left zero_le (hw1 b)) hlt`. Establish `h2` using `(w.valuation K).map_add_lt h1 (hw2 m hm)`. Rewrite `h2` using `[← map_add, hbm, map_one, map_one]`.

Conclude with `lt_irrefl _ h2`. Establish `hyinj : Function.Injective ((algebraMap K (w.adicCompletion K)).comp (algebraMap S K))` using `(algebraMap K (w.adicCompletion K)).injective.comp (IsFractionRing.injective S K)`. Use `⟨w.adicCompletion K, inferInstance, inferInstance, finite_adicCompletion v w, (algebraMap K (w.adicCompletion K)).comp (algebraMap S K), ?_, hyinj, ?_, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `r`. Simplify using `only [RingHom.comp_apply]`.

Rewrite using `[← hc r, AdicLiesOver.algebraMap_eq, adicCompletionMap_algebraMap]`. Introduce `a`. Rewrite using `[isIntegralElem_iff_valued_le_one v w, RingHom.comp_apply, hval]`. Conclude with `hw1 a`. Introduce `a ha`.

Establish `ha0 : a ≠ 0` using `fun h0 ↦ ha (h0 ▸ M.zero_mem)`. Establish `hy : (algebraMap K (w.adicCompletion K)).comp (algebraMap S K) a ≠ 0` using `(map_ne_zero_iff _ hyinj).2 ha0`. Use `⟨((algebraMap K (w.adicCompletion K)).comp (algebraMap S K) a)⁻¹, inv_mul_cancel₀ hy, ?_⟩` and prove the remaining obligations. Rewrite using `[isIntegralElem_iff_valued_le_one v w, map_inv₀, RingHom.comp_apply, hval, hunit a ha, inv_one]`. Introduce `a ha b hb hint`.

Rewrite `hint` using `[isIntegralElem_iff_valued_le_one v w]`. Establish `h` using `congrArg Valued.v hb`. Rewrite `h` using `[map_mul, map_one, RingHom.comp_apply, hval]`. Establish `h'` using `(mul_le_of_le_one_left zero_le hint).trans_lt (hw2 a ha)`. Rewrite `h'` using `[h]`.

Conclude with `lt_irrefl _ h'`.
-/
theorem proof : IntegralPointOfAlgebraicDomain.Statement := by
  intro F _ _ S _ _ _ _ v M ⟨hinj, halg, hM, hMv⟩
  let K := FractionRing S
  have hg : Function.Injective ((algebraMap S K).comp (algebraMap (𝓞 F) S)) :=
    (IsFractionRing.injective S K).comp hinj
  let _ : Algebra F K := (IsFractionRing.lift hg).toAlgebra
  have hc : ∀ r : 𝓞 F,
      algebraMap F K (algebraMap (𝓞 F) F r) = algebraMap S K (algebraMap (𝓞 F) S r) :=
    fun r ↦ IsFractionRing.lift_algebraMap hg r
  have : FiniteDimensional F K := finiteDimensional_of_isFractionRing (S := S) hc
  have : NumberField K := NumberField.of_module_finite F K
  have hOK : ∀ r : 𝓞 F, algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) r) =
      algebraMap S K (algebraMap (𝓞 F) S r) := fun r ↦ hc r
  obtain ⟨p, hpv, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hpM : algebraMap (𝓞 F) S p ∈ M := by
    rw [← Ideal.mem_comap, hMv]
    exact hpv
  have hx0 : algebraMap (𝓞 F) (𝓞 K) p ≠ 0 := by
    intro h
    have h' := hOK p
    rw [h, map_zero] at h'
    exact hp0 ((map_eq_zero_iff _ hg).1 h'.symm)
  obtain ⟨w, hw1, hw2⟩ := exists_place M _ hx0 _ hpM (hOK p).symm
  have : w.asIdeal.LiesOver v.asIdeal := by
    have hle : v.asIdeal ≤ w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 K)) := fun r hr ↦ by
      rw [Ideal.mem_comap, ← w.valuation_lt_one_iff_mem (K := K)]
      change w.valuation K (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) r)) < 1
      rw [hOK r]
      exact hw2 _ (by rw [← Ideal.mem_comap, hMv]; exact hr)
    exact ⟨v.isMaximal.eq_of_le (Ideal.comap_isPrime _ w.asIdeal).ne_top hle⟩
  have hval : ∀ x : K, Valued.v (algebraMap K (w.adicCompletion K) x) = w.valuation K x :=
    fun x ↦ valuedAdicCompletion_eq_valuation' w x
  have hunit : ∀ a ∉ M, w.valuation K (algebraMap S K a) = 1 := by
    intro a ha
    obtain ⟨b, m, hm, hbm⟩ := hM.exists_inv ha
    refine le_antisymm (hw1 a) (not_lt.1 fun hlt ↦ ?_)
    have h1 : w.valuation K (algebraMap S K (b * a)) < 1 := by
      rw [map_mul, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le (hw1 b)) hlt
    have h2 := (w.valuation K).map_add_lt h1 (hw2 m hm)
    rw [← map_add, hbm, map_one, map_one] at h2
    exact lt_irrefl _ h2
  have hyinj : Function.Injective ((algebraMap K (w.adicCompletion K)).comp (algebraMap S K)) :=
    (algebraMap K (w.adicCompletion K)).injective.comp (IsFractionRing.injective S K)
  refine ⟨w.adicCompletion K, inferInstance, inferInstance, finite_adicCompletion v w,
    (algebraMap K (w.adicCompletion K)).comp (algebraMap S K), ?_, hyinj, ?_, ?_, ?_⟩
  · ext r
    simp only [RingHom.comp_apply]
    rw [← hc r, AdicLiesOver.algebraMap_eq, adicCompletionMap_algebraMap]
  · intro a
    rw [isIntegralElem_iff_valued_le_one v w, RingHom.comp_apply, hval]
    exact hw1 a
  · intro a ha
    have ha0 : a ≠ 0 := fun h0 ↦ ha (h0 ▸ M.zero_mem)
    have hy : (algebraMap K (w.adicCompletion K)).comp (algebraMap S K) a ≠ 0 :=
      (map_ne_zero_iff _ hyinj).2 ha0
    refine ⟨((algebraMap K (w.adicCompletion K)).comp (algebraMap S K) a)⁻¹, inv_mul_cancel₀ hy, ?_⟩
    rw [isIntegralElem_iff_valued_le_one v w, map_inv₀, RingHom.comp_apply, hval, hunit a ha,
      inv_one]
  · intro a ha b hb hint
    rw [isIntegralElem_iff_valued_le_one v w] at hint
    have h := congrArg Valued.v hb
    rw [map_mul, map_one, RingHom.comp_apply, hval] at h
    have h' := (mul_le_of_le_one_left zero_le hint).trans_lt (hw2 a ha)
    rw [h] at h'
    exact lt_irrefl _ h'

end IntegralPointOfAlgebraicDomain

end

end GroundTheory.Heights₂.Heights.FourB
