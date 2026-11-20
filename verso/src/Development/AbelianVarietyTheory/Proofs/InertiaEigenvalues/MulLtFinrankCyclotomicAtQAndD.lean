import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.UsedConclusionOfUsedInputs
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.CycDegRam

open Formalism Formalism.BasicNotions NumberField IsDedekindDomain Polynomial UniqueFactorizationMonoid

/- English proof (translation)
Use `haveI : Fact l.Prime := ⟨hl⟩`. Use `haveI : NeZero l := ⟨hl.ne_zero⟩`. Use `set L := CyclotomicField l E`. Use `set k := Module.finrank E L with hk`. Establish `hkpos : 0 < k` using `Module.finrank_pos`.

Establish `hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta l E L) l` using `IsCyclotomicExtension.zeta_spec l E L`. Set `z : 𝓞 L` to `⟨IsCyclotomicExtension.zeta l E L, hζ.isIntegral hl.pos⟩`. Establish `hz : IsPrimitiveRoot z l` using `IsPrimitiveRoot.of_map_of_injective (f := algebraMap (𝓞 L) L) hζ RingOfIntegers.coe_injective`. Establish `hprod : ∏ μ ∈ primitiveRoots l (𝓞 L), (1 - μ) = (l : 𝓞 L)`. Establish `h` using `Polynomial.eval_one_cyclotomic_prime (R := 𝓞 L) (p := l)`.

Rewrite `h` using `[Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hz, Polynomial.eval_prod]`. Simplify using `using h`. Establish `hassoc : ∀ μ ∈ primitiveRoots l (𝓞 L), Associated (1 - z) (1 - μ)`. Introduce `μ hμ`. Establish `hμ' : IsPrimitiveRoot μ l` using `(mem_primitiveRoots hl.pos).1 hμ`.

Take `⟨a, -, ha⟩` from `hz.eq_pow_of_pow_eq_one hμ'.pow_eq_one`. Take `⟨b, -, hb⟩` from `hμ'.eq_pow_of_pow_eq_one hz.pow_eq_one`. Use `associated_of_dvd_dvd ?_ ?_` and prove the remaining obligations. Rewrite using `[← ha]`. Simplify using `using sub_dvd_pow_sub_pow (1 : 𝓞 L) z a`.

Rewrite using `[← hb]`. Simplify using `using sub_dvd_pow_sub_pow (1 : 𝓞 L) μ b`. Establish `hA : Associated ((1 - z) ^ (l - 1)) (l : 𝓞 L)`. Rewrite using `[← hprod]`. Use `Associated.prod (primitiveRoots l (𝓞 L)) (fun _ => 1 - z) (fun μ => 1 - μ) hassoc` as an intermediate fact.

Rewrite `this` using `[Finset.prod_const, hz.card_primitiveRoots, Nat.totient_prime hl]`. Then use the resulting hypothesis. Use `set n : 𝓞 E := RingOfIntegers.norm E (1 - z)`. Establish `hB : Associated (n ^ (l - 1)) ((l : 𝓞 E) ^ k)`. Use `hA.map (RingOfIntegers.norm E)` as an intermediate fact. Rewrite `this` using `[map_pow]`.

Establish `hl' : (l : 𝓞 L) = algebraMap (𝓞 E) (𝓞 L) (l : 𝓞 E)` using `(map_natCast _ _).symm`. Rewrite `this` using `[hl', RingOfIntegers.norm_algebraMap]`. Then use the resulting hypothesis. Establish `hI : (Ideal.span {n}) ^ (l - 1) = (Ideal.span {(l : 𝓞 E)}) ^ k`. Rewrite using `[Ideal.span_singleton_pow, Ideal.span_singleton_pow]`. Conclude with `Ideal.span_singleton_eq_span_singleton.2 hB`.

Establish `hmaxZ : (Ideal.span {(l : ℤ)}).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible`. Establish `hinj : Function.Injective (algebraMap ℤ (𝓞 E))` using `(algebraMap ℤ (𝓞 E)).injective_int`. Establish `hker : RingHom.ker (algebraMap ℤ (𝓞 E)) ≤ Ideal.span {(l : ℤ)}`. Rewrite using `[(RingHom.injective_iff_ker_eq_bot _).1 hinj]`. Conclude with `bot_le`.

Take `⟨Q, hQmax, hQ⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (Ideal.span {(l : ℤ)}) hker`. Establish `hlZ : (l : ℤ) ≠ 0` using `by exact_mod_cast hl.ne_zero`. Establish `hQ0 : Q ≠ ⊥`. Introduce and unpack `rfl`. Establish `h1 : (l : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 E)) (⊥ : Ideal (𝓞 E))`.

Rewrite using `[hQ]`. Conclude with `Ideal.mem_span_singleton_self _`. Rewrite `h1` using `[Ideal.mem_comap, Ideal.mem_bot, map_natCast]`. Conclude with `hl.ne_zero (by exact_mod_cast h1)`. Set `v : HeightOneSpectrum (𝓞 E)` to `⟨Q, hQmax.isPrime, hQ0⟩`.

Establish `hv : v ∈ placesOver E l` using `by show (l : 𝓞 E) ∈ Q`. Establish `h1 : (l : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 E)) Q`. Rewrite using `[hQ]`. Conclude with `Ideal.mem_span_singleton_self _`. Rewrite `h1` using `[Ideal.mem_comap, map_natCast]`. Then use the resulting hypothesis.

Establish `hram2 : Q.ramificationIdx ℤ = 2` using `hram v hv`. Use `haveI : Q.LiesOver (Ideal.span {(l : ℤ)}) := ⟨hQ.symm⟩`. Establish `hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(l : ℤ)}) = Ideal.span {(l : 𝓞 E)}`. Rewrite using `[Ideal.map_span, Set.image_singleton, map_natCast]`. Establish `hne : Ideal.span {(l : 𝓞 E)} ≠ ⊥`.

Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hl.ne_zero` after adjusting the coercions. Establish `hc` using `Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count (Ideal.span {(l : ℤ)}) Q (by rw [hmap]; exact hne)`. Rewrite `hc` using `[hram2, hmap]`. Establish `h1` using `congrArg (fun I => Multiset.count Q (normalizedFactors I)) hI`.

Simplify using `only [normalizedFactors_pow, Multiset.count_nsmul] at h1`. Rewrite `h1` using `[← hc]`. Break down `Nat.eq_zero_or_pos (Multiset.count Q (normalizedFactors (Ideal.span {n}))) with h0 | hpos` into its components or cases. Rewrite `h1` using `[h0]`. Use linear arithmetic over natural numbers and integers.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem sub_one_le_two_mul_finrank (E : Type) [Field E] [NumberField E] (l : ℕ) (hl : l.Prime)
    (hram : ∀ v ∈ placesOver E l, v.asIdeal.ramificationIdx ℤ = 2) :
    l - 1 ≤ 2 * Module.finrank E (CyclotomicField l E) := by
  classical
  haveI : Fact l.Prime := ⟨hl⟩
  haveI : NeZero l := ⟨hl.ne_zero⟩
  set L := CyclotomicField l E
  set k := Module.finrank E L with hk
  have hkpos : 0 < k := Module.finrank_pos
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta l E L) l := IsCyclotomicExtension.zeta_spec l E L
  let z : 𝓞 L := ⟨IsCyclotomicExtension.zeta l E L, hζ.isIntegral hl.pos⟩
  have hz : IsPrimitiveRoot z l :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap (𝓞 L) L) hζ RingOfIntegers.coe_injective
  have hprod : ∏ μ ∈ primitiveRoots l (𝓞 L), (1 - μ) = (l : 𝓞 L) := by
    have h := Polynomial.eval_one_cyclotomic_prime (R := 𝓞 L) (p := l)
    rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hz, Polynomial.eval_prod] at h
    simpa using h
  have hassoc : ∀ μ ∈ primitiveRoots l (𝓞 L), Associated (1 - z) (1 - μ) := by
    intro μ hμ
    have hμ' : IsPrimitiveRoot μ l := (mem_primitiveRoots hl.pos).1 hμ
    obtain ⟨a, -, ha⟩ := hz.eq_pow_of_pow_eq_one hμ'.pow_eq_one
    obtain ⟨b, -, hb⟩ := hμ'.eq_pow_of_pow_eq_one hz.pow_eq_one
    refine associated_of_dvd_dvd ?_ ?_
    · rw [← ha]; simpa using sub_dvd_pow_sub_pow (1 : 𝓞 L) z a
    · rw [← hb]; simpa using sub_dvd_pow_sub_pow (1 : 𝓞 L) μ b
  have hA : Associated ((1 - z) ^ (l - 1)) (l : 𝓞 L) := by
    rw [← hprod]
    have := Associated.prod (primitiveRoots l (𝓞 L)) (fun _ => 1 - z) (fun μ => 1 - μ) hassoc
    rwa [Finset.prod_const, hz.card_primitiveRoots, Nat.totient_prime hl] at this
  set n : 𝓞 E := RingOfIntegers.norm E (1 - z)
  have hB : Associated (n ^ (l - 1)) ((l : 𝓞 E) ^ k) := by
    have := hA.map (RingOfIntegers.norm E)
    rw [map_pow] at this
    have hl' : (l : 𝓞 L) = algebraMap (𝓞 E) (𝓞 L) (l : 𝓞 E) := (map_natCast _ _).symm
    rwa [hl', RingOfIntegers.norm_algebraMap] at this
  have hI : (Ideal.span {n}) ^ (l - 1) = (Ideal.span {(l : 𝓞 E)}) ^ k := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow]
    exact Ideal.span_singleton_eq_span_singleton.2 hB

  have hmaxZ : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible
  have hinj : Function.Injective (algebraMap ℤ (𝓞 E)) := (algebraMap ℤ (𝓞 E)).injective_int
  have hker : RingHom.ker (algebraMap ℤ (𝓞 E)) ≤ Ideal.span {(l : ℤ)} := by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (Ideal.span {(l : ℤ)}) hker
  have hlZ : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    have h1 : (l : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 E)) (⊥ : Ideal (𝓞 E)) := by
      rw [hQ]; exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap, Ideal.mem_bot, map_natCast] at h1
    exact hl.ne_zero (by exact_mod_cast h1)
  let v : HeightOneSpectrum (𝓞 E) := ⟨Q, hQmax.isPrime, hQ0⟩
  have hv : v ∈ placesOver E l := by
    show (l : 𝓞 E) ∈ Q
    have h1 : (l : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 E)) Q := by
      rw [hQ]; exact Ideal.mem_span_singleton_self _
    rwa [Ideal.mem_comap, map_natCast] at h1
  have hram2 : Q.ramificationIdx ℤ = 2 := hram v hv
  haveI : Q.LiesOver (Ideal.span {(l : ℤ)}) := ⟨hQ.symm⟩
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(l : ℤ)}) = Ideal.span {(l : 𝓞 E)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hne : Ideal.span {(l : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hl.ne_zero
  have hc := Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
    (Ideal.span {(l : ℤ)}) Q (by rw [hmap]; exact hne)
  rw [hram2, hmap] at hc
  have h1 := congrArg (fun I => Multiset.count Q (normalizedFactors I)) hI
  simp only [normalizedFactors_pow, Multiset.count_nsmul] at h1
  rw [← hc] at h1
  rcases Nat.eq_zero_or_pos (Multiset.count Q (normalizedFactors (Ideal.span {n}))) with h0 | hpos
  · rw [h0] at h1; omega
  · calc l - 1 ≤ (l - 1) * Multiset.count Q (normalizedFactors (Ideal.span {n})) :=
          Nat.le_mul_of_pos_right _ hpos
      _ = 2 * k := by rw [h1, mul_comm]

end GlobalTheory.CycDegRam

namespace GlobalTheory.CycDegRam

/- English proof (translation)
Introduce `D h1 i hi`. Establish `hmem : D.nd.l i ∈ ({D.host.q, D.host.d} : Finset ℕ)`. Apply the tactic sequence `rcases hi with h | h <;> simp [h]`. Establish `hprime : (D.nd.l i).Prime`. Apply the tactic sequence `rcases hi with h | h <;> rw [h]`.

Conclude with `D.host.hyp.1`. Conclude with `D.host.hyp.2.1`. Establish `hbig : 4 * D.R.t * D.R.r + 1 < D.nd.l i`. Apply the tactic sequence `rcases hi with h | h <;> rw [h]`. Conclude with `D.host.qd_big.1`.

Conclude with `D.host.qd_big.2`. Establish `key` using `sub_one_le_two_mul_finrank D.host.E (D.nd.l i) hprime (fun v hv => ((h1 _ hmem).2 v hv).1)`. Establish `h4 : 4 * D.R.t * D.R.r = 4 * (D.R.t * D.R.r)` using `by ring`. Use linear arithmetic over natural numbers and integers.
-/
theorem tr_lt_finrank_cyclotomic : ∀ (D : D7), EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc,
    (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) →
    D.R.t * D.R.r < Module.finrank D.host.E (CyclotomicField (D.nd.l i) D.host.E) := by
  intro D h1 i hi
  have hmem : D.nd.l i ∈ ({D.host.q, D.host.d} : Finset ℕ) := by
    rcases hi with h | h <;> simp [h]
  have hprime : (D.nd.l i).Prime := by
    rcases hi with h | h <;> rw [h]
    · exact D.host.hyp.1
    · exact D.host.hyp.2.1
  have hbig : 4 * D.R.t * D.R.r + 1 < D.nd.l i := by
    rcases hi with h | h <;> rw [h]
    · exact D.host.qd_big.1
    · exact D.host.qd_big.2
  have key := sub_one_le_two_mul_finrank D.host.E (D.nd.l i) hprime
    (fun v hv => ((h1 _ hmem).2 v hv).1)
  have h4 : 4 * D.R.t * D.R.r = 4 * (D.R.t * D.R.r) := by ring
  omega

/- English proof (translation)
The claim follows from `tr_lt_finrank_cyclotomic`.
-/
example : ∀ (D : D7), EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → D.R.t * D.R.r < Module.finrank D.host.E (CyclotomicField (D.nd.l i) D.host.E) := tr_lt_finrank_cyclotomic

end GlobalTheory.CycDegRam
