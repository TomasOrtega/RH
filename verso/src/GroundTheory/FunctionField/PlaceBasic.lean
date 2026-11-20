import Mathlib
import GroundTheory.FunctionField.PlaceDefs

namespace GroundTheory.FunctionField

open Polynomial

namespace Place

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/- English proof (translation)
Establish `hx' : IsIntegral v.ring x` using `hx.tower_top`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hx'`. Rewrite using `[← hy]`. Conclude with `y.2`.
-/
theorem mem_ring_of_isIntegral (v : Place k K) {x : K} (hx : IsIntegral k x) : x ∈ v.ring := by
  have hx' : IsIntegral v.ring x := hx.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hx'
  rw [← hy]
  exact y.2

/- English proof (translation)
The claim follows from `v.mem_ring_of_isIntegral hx.isIntegral`.
-/
theorem mem_ring_of_isAlgebraic (v : Place k K) {x : K} (hx : IsAlgebraic k x) : x ∈ v.ring :=
  v.mem_ring_of_isIntegral hx.isIntegral

/- English proof (translation)
Establish `h1` using `(v.ring.valuation_le_one_iff x).2 (v.mem_ring_of_isAlgebraic hx)`. Establish `h2` using `(v.ring.valuation_le_one_iff x⁻¹).2 (v.mem_ring_of_isAlgebraic (IsAlgebraic.inv_iff.2 hx))`. Rewrite `h2` using `[map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx0))]`. Conclude with `le_antisymm h1 h2`.
-/
theorem valuation_eq_one_of_isAlgebraic (v : Place k K) {x : K} (hx : IsAlgebraic k x)
    (hx0 : x ≠ 0) : v.ring.valuation x = 1 := by
  have h1 := (v.ring.valuation_le_one_iff x).2 (v.mem_ring_of_isAlgebraic hx)
  have h2 := (v.ring.valuation_le_one_iff x⁻¹).2
    (v.mem_ring_of_isAlgebraic (IsAlgebraic.inv_iff.2 hx))
  rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx0))] at h2
  exact le_antisymm h1 h2

/- English proof (translation)
Establish `h` using `v.valuation_eq_one_of_isAlgebraic hx hx0`. Rewrite `h` using `[← v.valuation_isEquiv.eq_one_iff_eq_one]`. Rewrite using `[ord, h, WithZero.log_one, neg_zero]`.
-/
theorem ord_eq_zero_of_isAlgebraic [IsFunctionField k K] (v : Place k K) {x : K}
    (hx : IsAlgebraic k x) (hx0 : x ≠ 0) : v.ord x = 0 := by
  have h := v.valuation_eq_one_of_isAlgebraic hx hx0
  rw [← v.valuation_isEquiv.eq_one_iff_eq_one] at h
  rw [ord, h, WithZero.log_one, neg_zero]

/- English proof (translation)
Set `A : Subring K` to `(Algebra.adjoin k {x}).toSubring`. Establish `hxA : x ∈ A` using `Algebra.self_mem_adjoin_singleton k x`. Set `I : Ideal A` to `Ideal.span {⟨x, hxA⟩}`. Establish `hI : I ≠ ⊤`. Introduce `htop`.

Rewrite `htop` using `[Ideal.span_singleton_eq_top]`. Take `⟨y, hy⟩` from `htop.exists_right_inv`. Establish `hyA : (y : K) ∈ Algebra.adjoin k {x}` using `y.2`. Rewrite `hyA` using `[Algebra.adjoin_singleton_eq_range_aeval]`. Take `⟨p, hp⟩` from `hyA`.

Establish `hxy : x * (y : K) = 1` using `congrArg Subtype.val hy`. Apply `hx` to reduce the goal to its premises. Use `⟨X * p - 1, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Establish `h0` using `congrArg (fun q : k[X] => q.coeff 0) h`.

Simplify using `at h0`. Establish `hp' : aeval x p = (y : K)` using `hp`. Rewrite using `[map_sub, map_mul, aeval_X, map_one, hp', hxy, sub_self]`. Take `⟨B, hAB, hIB⟩` from `Ideal.image_subset_nonunits_valuationSubring I hI`. Establish `hxB : x ∈ B.nonunits` using `hIB ⟨⟨x, hxA⟩, Ideal.subset_span rfl, rfl⟩`.

Use `⟨⟨B, ?_, ?_⟩, B.mem_nonunits_iff.1 hxB⟩` and prove the remaining obligations. Introduce `htop`. Break down `B.mem_nonunits_iff_or.1 hxB with h | h` into its components or cases. Conclude with `hx (h ▸ isAlgebraic_zero)`. Conclude with `h (htop ▸ ValuationSubring.mem_top x⁻¹)`.

Introduce `c`. Conclude with `hAB (Subalgebra.algebraMap_mem (Algebra.adjoin k {x}) c)`.
-/
theorem exists_valuation_lt_one_of_transcendental {x : K} (hx : Transcendental k x) :
    ∃ v : Place k K, v.ring.valuation x < 1 := by
  let A : Subring K := (Algebra.adjoin k {x}).toSubring
  have hxA : x ∈ A := Algebra.self_mem_adjoin_singleton k x
  let I : Ideal A := Ideal.span {⟨x, hxA⟩}
  have hI : I ≠ ⊤ := by
    intro htop
    rw [Ideal.span_singleton_eq_top] at htop
    obtain ⟨y, hy⟩ := htop.exists_right_inv
    have hyA : (y : K) ∈ Algebra.adjoin k {x} := y.2
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hyA
    obtain ⟨p, hp⟩ := hyA
    have hxy : x * (y : K) = 1 := congrArg Subtype.val hy
    apply hx
    refine ⟨X * p - 1, ?_, ?_⟩
    · intro h
      have h0 := congrArg (fun q : k[X] => q.coeff 0) h
      simp at h0
    · have hp' : aeval x p = (y : K) := hp
      rw [map_sub, map_mul, aeval_X, map_one, hp', hxy, sub_self]
  obtain ⟨B, hAB, hIB⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  have hxB : x ∈ B.nonunits := hIB ⟨⟨x, hxA⟩, Ideal.subset_span rfl, rfl⟩
  refine ⟨⟨B, ?_, ?_⟩, B.mem_nonunits_iff.1 hxB⟩
  · intro htop
    rcases B.mem_nonunits_iff_or.1 hxB with h | h
    · exact hx (h ▸ isAlgebraic_zero)
    · exact h (htop ▸ ValuationSubring.mem_top x⁻¹)
  · intro c
    exact hAB (Subalgebra.algebraMap_mem (Algebra.adjoin k {x}) c)

/- English proof (translation)
Establish `hx' : Transcendental k x⁻¹` using `fun h => hx (by simpa using IsAlgebraic.inv_iff.2 h)`. Take `⟨v, hv⟩` from `exists_valuation_lt_one_of_transcendental hx'`. Use `⟨v, fun hmem => ?_⟩` and prove the remaining obligations. Establish `hx0 : x ≠ 0` using `fun h => hx (h ▸ isAlgebraic_zero)`. Establish `h1` using `(v.ring.valuation_le_one_iff x).2 hmem`.

Rewrite `hv` using `[map_inv₀, inv_lt_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx0))]`. Conclude with `absurd h1 (not_le.2 hv)`.
-/
theorem exists_not_mem_of_transcendental {x : K} (hx : Transcendental k x) :
    ∃ v : Place k K, x ∉ v.ring := by
  have hx' : Transcendental k x⁻¹ := fun h => hx (by simpa using IsAlgebraic.inv_iff.2 h)
  obtain ⟨v, hv⟩ := exists_valuation_lt_one_of_transcendental hx'
  refine ⟨v, fun hmem => ?_⟩
  have hx0 : x ≠ 0 := fun h => hx (h ▸ isAlgebraic_zero)
  have h1 := (v.ring.valuation_le_one_iff x).2 hmem
  rw [map_inv₀, inv_lt_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx0))] at hv
  exact absurd h1 (not_le.2 hv)

/- English proof (translation)
Use `⟨fun hx v => v.mem_ring_of_isAlgebraic hx, fun h => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hx`. Take `⟨v, hv⟩` from `exists_not_mem_of_transcendental hx`. Conclude with `hv (h v)`.
-/
theorem isAlgebraic_iff_forall_mem {x : K} : IsAlgebraic k x ↔ ∀ v : Place k K, x ∈ v.ring := by
  refine ⟨fun hx v => v.mem_ring_of_isAlgebraic hx, fun h => ?_⟩
  by_contra hx
  obtain ⟨v, hv⟩ := exists_not_mem_of_transcendental hx
  exact hv (h v)

/- English proof (translation)
Take `⟨x, hx, -⟩` from `IsFunctionField.exists_transcendental_finiteDimensional (k := k) (K := K)`. Take `⟨v, -⟩` from `exists_valuation_lt_one_of_transcendental hx`. Conclude with `⟨v⟩`.
-/
theorem nonempty [IsFunctionField k K] : Nonempty (Place k K) := by
  obtain ⟨x, hx, -⟩ := IsFunctionField.exists_transcendental_finiteDimensional (k := k) (K := K)
  obtain ⟨v, -⟩ := exists_valuation_lt_one_of_transcendental hx
  exact ⟨v⟩

/- English proof (translation)
Use `ext1`. Establish `key : ∀ (P : Ideal v.ring) [P.IsPrime], v.ring.ofPrime P = w.ring → v.ring = w.ring`. Introduce `P hP hPw`. Break down `eq_or_ne P ⊥ with h0 | h0` into its components or cases. Substitute `h0` using the available equality.

Rewrite `hPw` using `[ValuationSubring.ofPrime_bot]`. Conclude with `absurd hPw.symm w.ne_top`. Establish `hmax : P.IsMaximal` using `Ideal.IsPrime.isMaximal hP h0`. Establish `hm` using `IsLocalRing.eq_maximalIdeal hmax`. Substitute `hm` using the available equality.

Rewrite `hPw` using `[ValuationSubring.ofPrime_top]`. Conclude with `hPw`. Conclude with `key _ (v.ring.ofPrime_idealOfLE w.ring h)`.
-/
theorem eq_of_le [IsFunctionField k K] {v w : Place k K} (h : v.ring ≤ w.ring) : v = w := by
  ext1
  have key : ∀ (P : Ideal v.ring) [P.IsPrime], v.ring.ofPrime P = w.ring → v.ring = w.ring := by
    intro P hP hPw
    rcases eq_or_ne P ⊥ with h0 | h0
    · subst h0
      rw [ValuationSubring.ofPrime_bot] at hPw
      exact absurd hPw.symm w.ne_top
    · have hmax : P.IsMaximal := Ideal.IsPrime.isMaximal hP h0
      have hm := IsLocalRing.eq_maximalIdeal hmax
      subst hm
      rw [ValuationSubring.ofPrime_top] at hPw
      exact hPw
  exact key _ (v.ring.ofPrime_idealOfLE w.ring h)

noncomputable def algebraicClosureToResidueField (v : Place k K) :
    algebraicClosure k K →ₐ[k] v.ResidueField where
  toRingHom := (IsLocalRing.residue v.ring).comp
    (RingHom.codRestrict ((algebraicClosure k K).val : algebraicClosure k K →+* K) v.ring
      fun y => show (y : K) ∈ v.ring from v.mem_ring_of_isAlgebraic (mem_algebraicClosure_iff.1 y.2))
  commutes' _ := rfl

/- English proof (translation)
The claim follows from `v.algebraicClosureToResidueField.toRingHom.injective`.
-/
theorem algebraicClosureToResidueField_injective (v : Place k K) :
    Function.Injective v.algebraicClosureToResidueField :=
  v.algebraicClosureToResidueField.toRingHom.injective

instance [IsFunctionField k K] : FiniteDimensional k (algebraicClosure k K) := by
  obtain ⟨v⟩ := Place.nonempty (k := k) (K := K)
  exact FiniteDimensional.of_injective v.algebraicClosureToResidueField.toLinearMap
    v.algebraicClosureToResidueField_injective

end Place

end GroundTheory.FunctionField
