import Mathlib
import GroundTheory.FunctionField.PlaceSum

namespace GroundTheory.FunctionField

open IsDedekindDomain IsLocalRing

open scoped WithZero

namespace Place

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

section General

variable (B : Type*) [CommRing B] [IsDedekindDomain B] [Algebra B K] [IsFractionRing B K]
  (hk : ∀ c : k, algebraMap k K c ∈ (algebraMap B K).range)

noncomputable abbrev ofHeightOneSpectrum (P : HeightOneSpectrum B) : Place k K where
  ring := HeightOneSpectrum.valuationSubringAtPrime K P
  ne_top := by
    intro htop
    obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer K
    have hle := HeightOneSpectrum.valuationSubringAtPrime_le_valuation (K := K) (v := P)
    have hmem : π⁻¹ ∈ (P.valuation K).valuationSubring := hle (htop ▸ ValuationSubring.mem_top _)
    rw [Valuation.mem_valuationSubring_iff, map_inv₀, hπ, ← WithZero.exp_neg, ← WithZero.exp_zero,
      WithZero.exp_le_exp] at hmem
    omega
  algebraMap_mem c := by
    obtain ⟨b, hb⟩ := hk c
    rw [← hb]
    exact Subalgebra.algebraMap_mem
      (Localization.subalgebra.ofField K _ P.asIdeal.primeCompl_le_nonZeroDivisors) b

/- English proof (translation)
The claim follows from `Subalgebra.algebraMap_mem (Localization.subalgebra.ofField K _ P.asIdeal.primeCompl_le_nonZeroDivisors) b`.
-/
theorem algebraMap_mem_ofHeightOneSpectrum (P : HeightOneSpectrum B) (b : B) :
    algebraMap B K b ∈ (ofHeightOneSpectrum B hk P).ring :=
  Subalgebra.algebraMap_mem (Localization.subalgebra.ofField K _ P.asIdeal.primeCompl_le_nonZeroDivisors) b

noncomputable def centerHom (v : Place k K) (hv : ∀ b : B, algebraMap B K b ∈ v.ring) : B →+* v.ring :=
  RingHom.codRestrict (algebraMap B K) v.ring hv

noncomputable def center (v : Place k K) (hv : ∀ b : B, algebraMap B K b ∈ v.ring) :
    HeightOneSpectrum B where
  asIdeal := (maximalIdeal v.ring).comap (centerHom B v hv)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h0
    apply v.ne_top
    have hunit : ∀ b : B, b ≠ 0 → v.ring.valuation (algebraMap B K b) = 1 := by
      intro b hb
      refine le_antisymm ((v.ring.valuation_le_one_iff _).2 (hv b)) (not_lt.1 fun hlt => hb ?_)
      have hmem : centerHom B v hv b ∈ maximalIdeal v.ring := (v.ring.valuation_lt_one_iff _).2 hlt
      have : b ∈ (maximalIdeal v.ring).comap (centerHom B v hv) := hmem
      rw [h0] at this
      exact this
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := B) x
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    rw [← v.ring.valuation_le_one_iff, map_div₀, hunit s hs0, div_one]
    exact (v.ring.valuation_le_one_iff _).2 (hv a)

variable [IsFunctionField k K]

/- English proof (translation)
Use `Place.eq_of_le fun x hx => ?_` and prove the remaining obligations. Take `⟨a, s, hs, rfl⟩` from `hx`. Establish `hs' : centerHom B v hv s ∉ maximalIdeal v.ring` using `hs`. Establish `hs1 : v.ring.valuation (algebraMap B K s) = 1` using `le_antisymm ((v.ring.valuation_le_one_iff _).2 (hv s)) (not_lt.1 fun hlt => hs' ((v.ring.valuation_lt_one_iff _).2 hlt))`. Establish `hsinv : (algebraMap B K s)⁻¹ ∈ v.ring`.

Rewrite using `[← v.ring.valuation_le_one_iff, map_inv₀, hs1, inv_one]`. Conclude with `mul_mem (hv a) hsinv`.
-/
theorem ofHeightOneSpectrum_center (v : Place k K) (hv : ∀ b : B, algebraMap B K b ∈ v.ring) :
    ofHeightOneSpectrum B hk (center B v hv) = v := by
  refine Place.eq_of_le fun x hx => ?_
  obtain ⟨a, s, hs, rfl⟩ := hx
  have hs' : centerHom B v hv s ∉ maximalIdeal v.ring := hs
  have hs1 : v.ring.valuation (algebraMap B K s) = 1 :=
    le_antisymm ((v.ring.valuation_le_one_iff _).2 (hv s)) (not_lt.1 fun hlt =>
      hs' ((v.ring.valuation_lt_one_iff _).2 hlt))
  have hsinv : (algebraMap B K s)⁻¹ ∈ v.ring := by
    rw [← v.ring.valuation_le_one_iff, map_inv₀, hs1, inv_one]
  exact mul_mem (hv a) hsinv

omit [IsFunctionField k K] in
/- English proof (translation)
Use extensionality with `b`. Express the relevant statement in the definitionally equal form `centerHom B _ _ b ∈ maximalIdeal (ofHeightOneSpectrum B hk P).ring ↔ b ∈ P.asIdeal`. Rewrite using `[ValuationSubring.valuation_lt_one_iff]`. Express the relevant statement in the definitionally equal form `(ofHeightOneSpectrum B hk P).ring.valuation (algebraMap B K b) < 1 ↔ b ∈ P.asIdeal`. Establish `hbmem` using `algebraMap_mem_ofHeightOneSpectrum B hk P b`.

Prove the components needed by the constructor for the conclusion. Introduce `hb`. Assume the negation of the conclusion as `hbP`. Establish `hinv : (algebraMap B K b)⁻¹ ∈ (ofHeightOneSpectrum B hk P).ring` using `⟨1, b, hbP, by simp⟩`. Establish `hb0 : algebraMap B K b ≠ 0`.

Introduce `h0`. Rewrite `hinv` using `[h0, inv_zero]`. Apply `hbP` to reduce the goal to its premises. Establish `: b = 0` using `IsFractionRing.injective B K (h0.trans (map_zero _).symm)`. Rewrite using `[this]`.

Conclude with `P.asIdeal.zero_mem`. Establish `h1` using `(ofHeightOneSpectrum B hk P).ring.valuation_le_one_iff _ |>.2 hinv`. Rewrite `h1` using `[map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hb0))]`. Conclude with `absurd hb (not_lt.2 h1)`. Introduce `hbP`.

Assume the negation of the conclusion as `hb`. Establish `hb1 : (ofHeightOneSpectrum B hk P).ring.valuation (algebraMap B K b) = 1` using `le_antisymm ((ofHeightOneSpectrum B hk P).ring.valuation_le_one_iff _ |>.2 hbmem) (not_lt.1 hb)`. Establish `hb0 : algebraMap B K b ≠ 0`. Introduce `h0`. Rewrite `hb1` using `[h0, map_zero]`.

Conclude with `zero_ne_one hb1`. Establish `hinv : (algebraMap B K b)⁻¹ ∈ (ofHeightOneSpectrum B hk P).ring`. Rewrite using `[← ValuationSubring.valuation_le_one_iff, map_inv₀, hb1, inv_one]`. Establish `hle` using `HeightOneSpectrum.valuationSubringAtPrime_le_valuation (K := K) (v := P)`. Establish `h1 : P.valuation K (algebraMap B K b)⁻¹ ≤ 1` using `hle hinv`.

Establish `h2 : P.valuation K (algebraMap B K b) < 1` using `(P.valuation_lt_one_iff_mem (K := K) b).2 hbP`. Rewrite `h1` using `[map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hb0))]`. Conclude with `absurd h2 (not_lt.2 h1)`.
-/
theorem center_ofHeightOneSpectrum (P : HeightOneSpectrum B) :
    center B (ofHeightOneSpectrum B hk P) (algebraMap_mem_ofHeightOneSpectrum B hk P) = P := by
  ext b
  change centerHom B _ _ b ∈ maximalIdeal (ofHeightOneSpectrum B hk P).ring ↔ b ∈ P.asIdeal
  rw [ValuationSubring.valuation_lt_one_iff]
  change (ofHeightOneSpectrum B hk P).ring.valuation (algebraMap B K b) < 1 ↔ b ∈ P.asIdeal
  have hbmem := algebraMap_mem_ofHeightOneSpectrum B hk P b
  constructor
  · intro hb
    by_contra hbP
    have hinv : (algebraMap B K b)⁻¹ ∈ (ofHeightOneSpectrum B hk P).ring :=
      ⟨1, b, hbP, by simp⟩
    have hb0 : algebraMap B K b ≠ 0 := by
      intro h0
      rw [h0, inv_zero] at hinv
      apply hbP
      have : b = 0 := IsFractionRing.injective B K (h0.trans (map_zero _).symm)
      rw [this]
      exact P.asIdeal.zero_mem
    have h1 := (ofHeightOneSpectrum B hk P).ring.valuation_le_one_iff _ |>.2 hinv
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hb0))] at h1
    exact absurd hb (not_lt.2 h1)
  · intro hbP
    by_contra hb
    have hb1 : (ofHeightOneSpectrum B hk P).ring.valuation (algebraMap B K b) = 1 :=
      le_antisymm ((ofHeightOneSpectrum B hk P).ring.valuation_le_one_iff _ |>.2 hbmem)
        (not_lt.1 hb)
    have hb0 : algebraMap B K b ≠ 0 := by
      intro h0; rw [h0, map_zero] at hb1; exact zero_ne_one hb1
    have hinv : (algebraMap B K b)⁻¹ ∈ (ofHeightOneSpectrum B hk P).ring := by
      rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, hb1, inv_one]
    have hle := HeightOneSpectrum.valuationSubringAtPrime_le_valuation (K := K) (v := P)
    have h1 : P.valuation K (algebraMap B K b)⁻¹ ≤ 1 := hle hinv
    have h2 : P.valuation K (algebraMap B K b) < 1 := (P.valuation_lt_one_iff_mem (K := K) b).2 hbP
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hb0))] at h1
    exact absurd h2 (not_lt.2 h1)

noncomputable def equivHeightOneSpectrum :
    {v : Place k K // ∀ b : B, algebraMap B K b ∈ v.ring} ≃ HeightOneSpectrum B where
  toFun v := center B v.1 v.2
  invFun P := ⟨ofHeightOneSpectrum B hk P, algebraMap_mem_ofHeightOneSpectrum B hk P⟩
  left_inv v := Subtype.ext (ofHeightOneSpectrum_center B hk v.1 v.2)
  right_inv P := center_ofHeightOneSpectrum B hk P

/- English proof (translation)
Use `valuation_eq_of_isEquiv ?_ (ofHeightOneSpectrum B hk P).valuation_surjective (HeightOneSpectrum.valuation_surjective K P)` and prove the remaining obligations. Use `Valuation.isEquiv_iff_val_le_one.2 fun {x} => ?_` and prove the remaining obligations. Rewrite using `[Place.valuation_le_one_iff]`. Establish `hle` using `HeightOneSpectrum.valuationSubringAtPrime_le_valuation (K := K) (v := P)`. Set `Q : Place k K` to `{ ring := (P.valuation K).valuationSubring ne_top := (ofHeightOneSpectrum B hk P).ne_top ∘ fun htop => by`.

Apply `le_antisymm le_top` to reduce the goal to its premises. Introduce `y _`. Take `⟨π, hπ⟩` from `P.valuation_exists_uniformizer K`. Establish `hmem : π⁻¹ ∈ (P.valuation K).valuationSubring` using `htop ▸ ValuationSubring.mem_top _`. Rewrite `hmem` using `[Valuation.mem_valuationSubring_iff, map_inv₀, hπ, ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp]`.

Use linear arithmetic over natural numbers and integers. Use `algebraMap_mem := fun c => hle ((ofHeightOneSpectrum B hk P).algebraMap_mem c) }`. Establish `heq : ofHeightOneSpectrum B hk P = Q` using `Place.eq_of_le hle`. Prove the components needed by the constructor for the conclusion. Conclude with `fun hx => hle hx`.

Introduce `hx`. Establish `hxQ : x ∈ Q.ring` using `hx`. Rewrite `hxQ` using `[← heq]`. Conclude with `hxQ`.
-/
theorem valuation_ofHeightOneSpectrum (P : HeightOneSpectrum B) :
    (ofHeightOneSpectrum B hk P).valuation = P.valuation K := by
  refine valuation_eq_of_isEquiv ?_ (ofHeightOneSpectrum B hk P).valuation_surjective
    (HeightOneSpectrum.valuation_surjective K P)
  refine Valuation.isEquiv_iff_val_le_one.2 fun {x} => ?_
  rw [Place.valuation_le_one_iff]
  have hle := HeightOneSpectrum.valuationSubringAtPrime_le_valuation (K := K) (v := P)
  let Q : Place k K :=
    { ring := (P.valuation K).valuationSubring
      ne_top := (ofHeightOneSpectrum B hk P).ne_top ∘ fun htop => by
        apply le_antisymm le_top
        intro y _
        obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer K
        have hmem : π⁻¹ ∈ (P.valuation K).valuationSubring := htop ▸ ValuationSubring.mem_top _
        rw [Valuation.mem_valuationSubring_iff, map_inv₀, hπ, ← WithZero.exp_neg,
          ← WithZero.exp_zero, WithZero.exp_le_exp] at hmem
        omega
      algebraMap_mem := fun c => hle ((ofHeightOneSpectrum B hk P).algebraMap_mem c) }
  have heq : ofHeightOneSpectrum B hk P = Q := Place.eq_of_le hle
  constructor
  · exact fun hx => hle hx
  · intro hx
    have hxQ : x ∈ Q.ring := hx
    rw [← heq] at hxQ
    exact hxQ

end General

section RatFunc

open scoped Polynomial

omit [Algebra k K] in

/- English proof (translation)
Establish `: Algebra.Transcendental k K` using `(trdeg_ne_zero_iff (R := k) (A := K)).1 (by rw [h]; exact one_ne_zero)`. Take `⟨x, hx⟩` from `Algebra.Transcendental.transcendental (R := k) (A := K)`. Establish `hbx : IsTranscendenceBasis k ((↑) : ({x} : Set K) → K)` using `AlgebraicIndependent.isTranscendenceBasis_of_trdeg_le_of_finite ((algebraicIndependent_singleton_iff (⟨x, rfl⟩ : ({x} : Set K))).2 hx) (by rw [h, Cardinal.mk_singleton])`. Establish `halg` using `hbx.isAlgebraic_field`. Rewrite `halg` using `[Subtype.range_coe]`.

Establish `: Algebra.EssFiniteType (IntermediateField.adjoin k {x}) K` using `Algebra.EssFiniteType.of_comp k _ K`. Conclude with `⟨⟨x, hx, Algebra.finite_of_essFiniteType_of_isAlgebraic⟩⟩`.
-/
theorem _root_.GroundTheory.FunctionField.IsFunctionField.of_trdeg_eq_one [Algebra k K]
    [Algebra.EssFiniteType k K] (h : Algebra.trdeg k K = 1) : IsFunctionField k K := by
  have : Algebra.Transcendental k K :=
    (trdeg_ne_zero_iff (R := k) (A := K)).1 (by rw [h]; exact one_ne_zero)
  obtain ⟨x, hx⟩ := Algebra.Transcendental.transcendental (R := k) (A := K)
  have hbx : IsTranscendenceBasis k ((↑) : ({x} : Set K) → K) :=
    AlgebraicIndependent.isTranscendenceBasis_of_trdeg_le_of_finite
      ((algebraicIndependent_singleton_iff (⟨x, rfl⟩ : ({x} : Set K))).2 hx)
      (by rw [h, Cardinal.mk_singleton])
  have halg := hbx.isAlgebraic_field
  rw [Subtype.range_coe] at halg
  have : Algebra.EssFiniteType (IntermediateField.adjoin k {x}) K :=
    Algebra.EssFiniteType.of_comp k _ K
  exact ⟨⟨x, hx, Algebra.finite_of_essFiniteType_of_isAlgebraic⟩⟩

omit [Algebra k K] in
/- English proof (translation)
Establish `: Algebra.EssFiniteType k[X] (RatFunc k)` using `.of_isLocalization _ (nonZeroDivisors k[X])`. Conclude with `.comp k k[X] (RatFunc k)`.
-/
theorem _root_.GroundTheory.FunctionField.essFiniteType_ratFunc : Algebra.EssFiniteType k (RatFunc k) := by
  have : Algebra.EssFiniteType k[X] (RatFunc k) :=
    .of_isLocalization _ (nonZeroDivisors k[X])
  exact .comp k k[X] (RatFunc k)

omit [Algebra k K] in

instance _root_.GroundTheory.FunctionField.isFunctionField_ratFunc : IsFunctionField k (RatFunc k) := by
  have := essFiniteType_ratFunc (k := k)
  apply IsFunctionField.of_trdeg_eq_one
  have : Algebra.IsAlgebraic k[X] (RatFunc k) := IsLocalization.isAlgebraic _ (nonZeroDivisors k[X])
  have h := trdeg_add_eq k k[X] (A := RatFunc k)
  rw [Polynomial.trdeg_of_isDomain, trdeg_eq_zero, add_zero] at h
  exact h.symm

omit [Algebra k K] in

/- English proof (translation)
Use `essFiniteType_ratFunc (k := k)` as an intermediate fact. Establish `: Algebra.EssFiniteType k K` using `.comp k (RatFunc k) K`. Apply `IsFunctionField.of_trdeg_eq_one` to reduce the goal to its premises. Establish `h` using `lift_trdeg_add_eq k (RatFunc k) K`. Rewrite `h` using `[trdeg_eq_one (k := k) (K := RatFunc k), trdeg_eq_zero, Cardinal.lift_zero, add_zero, Cardinal.lift_one]`.

Conclude with `(Cardinal.lift_eq_one.1 h.symm)`.
-/
theorem _root_.GroundTheory.FunctionField.IsFunctionField.of_functionField [Algebra k K]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K] :
    IsFunctionField k K := by
  have := essFiniteType_ratFunc (k := k)
  have : Algebra.EssFiniteType k K := .comp k (RatFunc k) K
  apply IsFunctionField.of_trdeg_eq_one
  have h := lift_trdeg_add_eq k (RatFunc k) K
  rw [trdeg_eq_one (k := k) (K := RatFunc k), trdeg_eq_zero, Cardinal.lift_zero, add_zero,
    Cardinal.lift_one] at h
  exact (Cardinal.lift_eq_one.1 h.symm)

end RatFunc

section RingOfIntegers

open scoped Polynomial

variable [IsFunctionField k K] [Algebra k[X] K] [Algebra (RatFunc k) K]
  [IsScalarTower k[X] (RatFunc k) K] [IsScalarTower k k[X] K] [FunctionField k K]

omit [IsFunctionField k K] [Algebra (RatFunc k) K] [IsScalarTower k[X] (RatFunc k) K]
  [FunctionField k K] in
/- English proof (translation)
Establish `h : algebraMap k[X] K p = Polynomial.aeval (algebraMap k[X] K Polynomial.X) p`. Rewrite using `[Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left_apply]`. Rewrite using `[h, ← v.ring.valuation_le_one_iff]`. Conclude with `v.valuation_aeval_le_one hv p`.
-/
theorem algebraMap_polynomial_mem (v : Place k K) (hv : algebraMap k[X] K Polynomial.X ∈ v.ring)
    (p : k[X]) : algebraMap k[X] K p ∈ v.ring := by
  have h : algebraMap k[X] K p = Polynomial.aeval (algebraMap k[X] K Polynomial.X) p := by
    rw [Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left_apply]
  rw [h, ← v.ring.valuation_le_one_iff]
  exact v.valuation_aeval_le_one hv p

omit [IsFunctionField k K] [Algebra (RatFunc k) K] [IsScalarTower k[X] (RatFunc k) K]
  [FunctionField k K] in

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hX : IsIntegral k[X] (algebraMap k[X] K Polynomial.X)` using `isIntegral_algebraMap`. Use `h (IsIntegralClosure.mk' (FunctionField.ringOfIntegers k K) _ hX)` as an intermediate fact. Rewrite `this` using `[IsIntegralClosure.algebraMap_mk']`. Then use the resulting hypothesis.

Introduce `hv b`. Set `: Algebra k[X] v.ring` to `(RingHom.codRestrict (algebraMap k[X] K) v.ring (v.algebraMap_polynomial_mem hv)).toAlgebra`. Establish `: IsScalarTower k[X] v.ring K` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `hb : IsIntegral k[X] (algebraMap (FunctionField.ringOfIntegers k K) K b)` using `(IsIntegralClosure.isIntegral k[X] K b).map (IsScalarTower.toAlgHom k[X] (FunctionField.ringOfIntegers k K) K)`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.1 (hb.tower_top (A := v.ring))`.

Rewrite using `[← hy]`. Conclude with `y.2`.
-/
theorem forall_mem_ringOfIntegers_iff (v : Place k K) :
    (∀ b : FunctionField.ringOfIntegers k K, algebraMap _ K b ∈ v.ring) ↔
      algebraMap k[X] K Polynomial.X ∈ v.ring := by
  constructor
  · intro h
    have hX : IsIntegral k[X] (algebraMap k[X] K Polynomial.X) := isIntegral_algebraMap
    have := h (IsIntegralClosure.mk' (FunctionField.ringOfIntegers k K) _ hX)
    rwa [IsIntegralClosure.algebraMap_mk'] at this
  · intro hv b
    let : Algebra k[X] v.ring :=
      (RingHom.codRestrict (algebraMap k[X] K) v.ring (v.algebraMap_polynomial_mem hv)).toAlgebra
    have : IsScalarTower k[X] v.ring K := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hb : IsIntegral k[X] (algebraMap (FunctionField.ringOfIntegers k K) K b) :=
      (IsIntegralClosure.isIntegral k[X] K b).map
        (IsScalarTower.toAlgHom k[X] (FunctionField.ringOfIntegers k K) K)
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hb.tower_top (A := v.ring))
    rw [← hy]
    exact y.2

omit [IsFunctionField k K] [Algebra (RatFunc k) K] [IsScalarTower k[X] (RatFunc k) K]
  [FunctionField k K] in
/- English proof (translation)
Establish `hc : IsIntegral k[X] (algebraMap k[X] K (Polynomial.C c))` using `isIntegral_algebraMap`. Use `⟨IsIntegralClosure.mk' (FunctionField.ringOfIntegers k K) _ hc, ?_⟩` and prove the remaining obligations. Rewrite using `[IsIntegralClosure.algebraMap_mk', ← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]`.
-/
theorem algebraMap_mem_range_ringOfIntegers (c : k) :
    algebraMap k K c ∈ (algebraMap (FunctionField.ringOfIntegers k K) K).range := by
  have hc : IsIntegral k[X] (algebraMap k[X] K (Polynomial.C c)) := isIntegral_algebraMap
  refine ⟨IsIntegralClosure.mk' (FunctionField.ringOfIntegers k K) _ hc, ?_⟩
  rw [IsIntegralClosure.algebraMap_mk', ← Polynomial.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply]

noncomputable def equivHeightOneSpectrumRingOfIntegers [Algebra.IsSeparable (RatFunc k) K] :
    {v : Place k K // algebraMap k[X] K Polynomial.X ∈ v.ring} ≃
      HeightOneSpectrum (FunctionField.ringOfIntegers k K) :=
  (Equiv.subtypeEquivRight fun v => (forall_mem_ringOfIntegers_iff v).symm).trans
    (equivHeightOneSpectrum _ algebraMap_mem_range_ringOfIntegers)

end RingOfIntegers

section Separating

open scoped IntermediateField.algebraAdjoinAdjoin

omit [Algebra k K] in

/- English proof (translation)
Use `IsPrincipalIdealRing.of_surjective (Polynomial.aeval (R := k) (⟨t, Algebra.self_mem_adjoin_singleton k t⟩ : Algebra.adjoin k {t})) ?_` and prove the remaining obligations. Introduce and unpack `⟨y, hy⟩`. Rewrite `hy` using `[Algebra.adjoin_singleton_eq_range_aeval]`. Take `⟨p, rfl⟩` from `(AlgHom.mem_range _).1 hy`. Conclude with `⟨p, Subtype.ext (Polynomial.aeval_subalgebra_coe p _ _)⟩`.
-/
theorem isPrincipalIdealRing_adjoin [Algebra k K] (t : K) :
    IsPrincipalIdealRing (Algebra.adjoin k {t}) := by
  refine IsPrincipalIdealRing.of_surjective
    (Polynomial.aeval (R := k) (⟨t, Algebra.self_mem_adjoin_singleton k t⟩ : Algebra.adjoin k {t})) ?_
  rintro ⟨y, hy⟩
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
  obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).1 hy
  exact ⟨p, Subtype.ext (Polynomial.aeval_subalgebra_coe p _ _)⟩

variable [IsFunctionField k K] (t : K) [Algebra.IsSeparable (IntermediateField.adjoin k {t}) K]

/- English proof (translation)
Introduce `ht`. Establish `: FiniteDimensional k (IntermediateField.adjoin k {t})` using `IntermediateField.adjoin.finiteDimensional ht.isIntegral`. Establish `: Algebra.IsAlgebraic k (IntermediateField.adjoin k {t})` using `Algebra.IsAlgebraic.of_finite _ _`. Establish `: Algebra.IsAlgebraic k K` using `Algebra.IsAlgebraic.trans k (IntermediateField.adjoin k {t}) K`. Establish `h` using `trdeg_eq_one (k := k) (K := K)`.

Rewrite `h` using `[trdeg_eq_zero]`. Conclude with `zero_ne_one h`.
-/
theorem transcendental_of_isSeparable : Transcendental k t := by
  intro ht
  have : FiniteDimensional k (IntermediateField.adjoin k {t}) :=
    IntermediateField.adjoin.finiteDimensional ht.isIntegral
  have : Algebra.IsAlgebraic k (IntermediateField.adjoin k {t}) := Algebra.IsAlgebraic.of_finite _ _
  have : Algebra.IsAlgebraic k K := Algebra.IsAlgebraic.trans k (IntermediateField.adjoin k {t}) K
  have h := trdeg_eq_one (k := k) (K := K)
  rw [trdeg_eq_zero] at h
  exact zero_ne_one h

/- English proof (translation)
Use `isPrincipalIdealRing_adjoin (k := k) t` as an intermediate fact. Use `finiteDimensional_adjoin (transcendental_of_isSeparable (k := k) t)` as an intermediate fact. Conclude with `IsIntegralClosure.isDedekindDomain (Algebra.adjoin k {t}) (IntermediateField.adjoin k {t}) K _`.
-/
theorem isDedekindDomain_closure_adjoin :
    IsDedekindDomain (integralClosure (Algebra.adjoin k {t}) K) := by
  have := isPrincipalIdealRing_adjoin (k := k) t
  have := finiteDimensional_adjoin (transcendental_of_isSeparable (k := k) t)
  exact IsIntegralClosure.isDedekindDomain (Algebra.adjoin k {t}) (IntermediateField.adjoin k {t}) K _

/- English proof (translation)
Use `finiteDimensional_adjoin (transcendental_of_isSeparable (k := k) t)` as an intermediate fact. Conclude with `integralClosure.isFractionRing_of_finite_extension (A := Algebra.adjoin k {t}) (IntermediateField.adjoin k {t}) K`.
-/
theorem isFractionRing_closure_adjoin :
    IsFractionRing (integralClosure (Algebra.adjoin k {t}) K) K := by
  have := finiteDimensional_adjoin (transcendental_of_isSeparable (k := k) t)
  exact integralClosure.isFractionRing_of_finite_extension (A := Algebra.adjoin k {t})
    (IntermediateField.adjoin k {t}) K

attribute [local instance] isDedekindDomain_closure_adjoin isFractionRing_closure_adjoin

omit [IsFunctionField k K] [Algebra.IsSeparable (IntermediateField.adjoin k {t}) K] in

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hint : IsIntegral (Algebra.adjoin k {t}) t` using `isIntegral_algebraMap (R := Algebra.adjoin k {t}) (A := K) (x := ⟨t, Algebra.self_mem_adjoin_singleton k t⟩)`. Conclude with `h ⟨t, hint⟩`. Introduce `hv b`.

Establish `hA : ∀ a : Algebra.adjoin k {t}, (a : K) ∈ v.ring`. Introduce and unpack `⟨y, hy⟩`. Rewrite `hy` using `[Algebra.adjoin_singleton_eq_range_aeval]`. Take `⟨p, rfl⟩` from `(AlgHom.mem_range _).1 hy`. Rewrite using `[← v.ring.valuation_le_one_iff]`.

Conclude with `v.valuation_aeval_le_one hv p`. Set `: Algebra (Algebra.adjoin k {t}) v.ring` to `(RingHom.codRestrict (algebraMap (Algebra.adjoin k {t}) K) v.ring hA).toAlgebra`. Establish `: IsScalarTower (Algebra.adjoin k {t}) v.ring K` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `hb : IsIntegral (Algebra.adjoin k {t}) (b : K)` using `b.2`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.1 (hb.tower_top (A := v.ring))`.

Use `show (b : K) ∈ v.ring`. Rewrite using `[← hy]`. Conclude with `y.2`.
-/
theorem forall_mem_closure_adjoin_iff (v : Place k K) :
    (∀ b : integralClosure (Algebra.adjoin k {t}) K, algebraMap _ K b ∈ v.ring) ↔ t ∈ v.ring := by
  constructor
  · intro h
    have hint : IsIntegral (Algebra.adjoin k {t}) t :=
      isIntegral_algebraMap (R := Algebra.adjoin k {t}) (A := K)
        (x := ⟨t, Algebra.self_mem_adjoin_singleton k t⟩)
    exact h ⟨t, hint⟩
  · intro hv b
    have hA : ∀ a : Algebra.adjoin k {t}, (a : K) ∈ v.ring := by
      rintro ⟨y, hy⟩
      rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
      obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).1 hy
      rw [← v.ring.valuation_le_one_iff]
      exact v.valuation_aeval_le_one hv p
    let : Algebra (Algebra.adjoin k {t}) v.ring :=
      (RingHom.codRestrict (algebraMap (Algebra.adjoin k {t}) K) v.ring hA).toAlgebra
    have : IsScalarTower (Algebra.adjoin k {t}) v.ring K := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hb : IsIntegral (Algebra.adjoin k {t}) (b : K) := b.2
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hb.tower_top (A := v.ring))
    show (b : K) ∈ v.ring
    rw [← hy]
    exact y.2

omit [IsFunctionField k K] [Algebra.IsSeparable (IntermediateField.adjoin k {t}) K] in
/- English proof (translation)
Establish `hc : IsIntegral (Algebra.adjoin k {t}) (algebraMap k K c)` using `isIntegral_algebraMap (R := Algebra.adjoin k {t}) (A := K) (x := ⟨algebraMap k K c, Subalgebra.algebraMap_mem _ c⟩)`. Conclude with `⟨⟨algebraMap k K c, hc⟩, rfl⟩`.
-/
theorem algebraMap_mem_range_closure_adjoin (c : k) :
    algebraMap k K c ∈ (algebraMap (integralClosure (Algebra.adjoin k {t}) K) K).range := by
  have hc : IsIntegral (Algebra.adjoin k {t}) (algebraMap k K c) :=
    isIntegral_algebraMap (R := Algebra.adjoin k {t}) (A := K)
      (x := ⟨algebraMap k K c, Subalgebra.algebraMap_mem _ c⟩)
  exact ⟨⟨algebraMap k K c, hc⟩, rfl⟩

noncomputable def equivOfSeparating :
    {v : Place k K // t ∈ v.ring} ≃ HeightOneSpectrum (integralClosure (Algebra.adjoin k {t}) K) :=
  (Equiv.subtypeEquivRight fun v => (forall_mem_closure_adjoin_iff t v).symm).trans
    (equivHeightOneSpectrum _ (algebraMap_mem_range_closure_adjoin t))

omit [IsFunctionField k K] [Algebra.IsSeparable (IntermediateField.adjoin k {t}) K] in
/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[IntermediateField.adjoin_simple_le_iff]`. Conclude with `inv_mem (IntermediateField.mem_adjoin_simple_self k t)`. Rewrite using `[IntermediateField.adjoin_simple_le_iff]`. Use `inv_mem (IntermediateField.mem_adjoin_simple_self k t⁻¹)` as an intermediate fact.

Rewrite `this` using `[inv_inv]`. Then use the resulting hypothesis.
-/
theorem adjoin_inv_eq : IntermediateField.adjoin k {t⁻¹} = IntermediateField.adjoin k {t} := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self k t)
  · rw [IntermediateField.adjoin_simple_le_iff]
    have := inv_mem (IntermediateField.mem_adjoin_simple_self k t⁻¹)
    rwa [inv_inv] at this

omit [IsFunctionField k K] in

/- English proof (translation)
Rewrite using `[adjoin_inv_eq]`. Use `infer_instance`.
-/
theorem isSeparable_adjoin_inv : Algebra.IsSeparable (IntermediateField.adjoin k {t⁻¹}) K := by
  rw [adjoin_inv_eq]
  infer_instance

noncomputable def equivZerosOfSeparating :
    {v : Place k K // v.ring.valuation t < 1} ≃
      {P : HeightOneSpectrum (integralClosure (Algebra.adjoin k {t}) K) //
        (⟨t, isIntegral_algebraMap (R := Algebra.adjoin k {t}) (A := K)
          (x := ⟨t, Algebra.self_mem_adjoin_singleton k t⟩)⟩ :
            integralClosure (Algebra.adjoin k {t}) K) ∈ P.asIdeal} :=
  let e₁ : {v : Place k K // v.ring.valuation t < 1} ≃
      {w : {v : Place k K // t ∈ v.ring} // w.1.ring.valuation t < 1} :=
    { toFun v := ⟨⟨v.1, (v.1.ring.valuation_le_one_iff t).1 v.2.le⟩, v.2⟩
      invFun w := ⟨w.1.1, w.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  e₁.trans (Equiv.subtypeEquiv (equivOfSeparating t) fun w => by
    change _ ↔ centerHom _ w.1 _ _ ∈ maximalIdeal w.1.ring
    rw [ValuationSubring.valuation_lt_one_iff]
    rfl)

end Separating

end Place

end GroundTheory.FunctionField
