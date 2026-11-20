import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeElementCongruentStatement
import Formalism.LocalRingCardinality.ConjSqrtMinusD
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem.NormPrime

/- English proof (translation)
Establish `h` using `Algebra.norm_eq_prod_embeddings ℚ ℂ x`. Establish `hne : φ.toRatAlgHom ≠ (ComplexEmbedding.conjugate φ).toRatAlgHom`. Introduce `he`. Establish `hc` using `IsTotallyComplex.isComplex (InfinitePlace.mk φ)`. Apply `InfinitePlace.isComplex_mk_iff.mp hc` to reduce the goal to its premises.

Rewrite using `[ComplexEmbedding.isReal_iff]`. Use extensionality with `y`. Conclude with `(congrArg (fun f : K →ₐ[ℚ] ℂ => f y) he).symm`. Establish `hu : (Finset.univ : Finset (K →ₐ[ℚ] ℂ)) = {φ.toRatAlgHom, (ComplexEmbedding.conjugate φ).toRatAlgHom}`. Use `symm`.

Apply `Finset.eq_univ_of_card` to reduce the goal to its premises. Rewrite using `[Finset.card_pair hne, AlgHom.card, h2]`. Rewrite `h` using `[hu, Finset.prod_pair hne]`. Conclude with `h`.
-/
theorem norm_eq_mul_conj {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    (h2 : Module.finrank ℚ K = 2) (φ : K →+* ℂ) (x : K) :
    ((Algebra.norm ℚ x : ℚ) : ℂ) = φ x * starRingEnd ℂ (φ x) := by
  classical
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  have hne : φ.toRatAlgHom ≠ (ComplexEmbedding.conjugate φ).toRatAlgHom := by
    intro he
    have hc := IsTotallyComplex.isComplex (InfinitePlace.mk φ)
    apply InfinitePlace.isComplex_mk_iff.mp hc
    rw [ComplexEmbedding.isReal_iff]
    ext y
    exact (congrArg (fun f : K →ₐ[ℚ] ℂ => f y) he).symm
  have hu : (Finset.univ : Finset (K →ₐ[ℚ] ℂ)) =
      {φ.toRatAlgHom, (ComplexEmbedding.conjugate φ).toRatAlgHom} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hne, AlgHom.card, h2]
  rw [hu, Finset.prod_pair hne] at h
  exact h

variable {R : Ranks}

/- English proof (translation)
The claim follows from `IntermediateField.mem_adjoin_simple_self ℚ _`.
-/
theorem sqrtMinusD_mem (H : Host R) : H.sqrtMinusD ∈ H.K :=
  IntermediateField.mem_adjoin_simple_self ℚ _

/- English proof (translation)
The claim follows from `Formalism.FrobeniusOrbits.SplitK.finrank_K H.hyp.2.1.pos H.sqrtMinusD_sq`.
-/
theorem finrank_K (H : Host R) : Module.finrank ℚ H.K = 2 :=
  Formalism.FrobeniusOrbits.SplitK.finrank_K H.hyp.2.1.pos H.sqrtMinusD_sq

/- English proof (translation)
Use `⟨fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[← InfinitePlace.not_isReal_iff_isComplex]`. Introduce `hw`. Use `set b : H.K := ⟨H.sqrtMinusD, sqrtMinusD_mem H⟩`. Establish `hb : b ^ 2 = -(H.d : H.K)`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify `H.sqrtMinusD_sq` using `[b]`. Establish `h1` using `congrArg (InfinitePlace.embedding_of_isReal hw) hb`. Rewrite `h1` using `[map_pow, map_neg, map_natCast]`. Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast H.hyp.2.1.pos`.

Use polynomial arithmetic with `[sq_nonneg (InfinitePlace.embedding_of_isReal hw b)]`.
-/
theorem isTotallyComplex_K (H : Host R) : IsTotallyComplex H.K := by
  refine ⟨fun w => ?_⟩
  rw [← InfinitePlace.not_isReal_iff_isComplex]
  intro hw
  set b : H.K := ⟨H.sqrtMinusD, sqrtMinusD_mem H⟩
  have hb : b ^ 2 = -(H.d : H.K) := by
    apply Subtype.ext
    simpa [b] using H.sqrtMinusD_sq
  have h1 := congrArg (InfinitePlace.embedding_of_isReal hw) hb
  rw [map_pow, map_neg, map_natCast] at h1
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
  nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hw b)]

/- English proof (translation)
Use `isTotallyComplex_K H` as an intermediate fact. Apply `H.φ₀.injective` to reduce the goal to its premises. Establish `h1 : H.φ₀ (H.conj (x : H.E)) = starRingEnd ℂ (H.φ₀ (x : H.E))` using `H.toHostAx.conjE_apply _ _`. Rewrite using `[map_mul, h1, map_ratCast, norm_eq_mul_conj (finrank_K H) (H.φ₀.comp (algebraMap H.K H.E)) x]`. Both sides reduce to the same expression.
-/
theorem norm_K (H : Host R) (x : H.K) :
    (x : H.E) * H.conj (x : H.E) = ((Algebra.norm ℚ x : ℚ) : H.E) := by
  have := isTotallyComplex_K H
  apply H.φ₀.injective
  have h1 : H.φ₀ (H.conj (x : H.E)) = starRingEnd ℂ (H.φ₀ (x : H.E)) :=
    H.toHostAx.conjE_apply _ _
  rw [map_mul, h1, map_ratCast,
    norm_eq_mul_conj (finrank_K H) (H.φ₀.comp (algebraMap H.K H.E)) x]
  rfl

/- English proof (translation)
Establish `hM' : (M : E) ≠ 0` using `by exact_mod_cast hM`. Establish `hM'' : (M : ℚ) ≠ 0` using `by exact_mod_cast hM`. Establish `e : y = algebraMap ℚ E ((n : ℚ) / M)`. Rewrite using `[map_div₀, map_intCast, map_natCast, h]`. Clear the denominators using the available nonvanishing facts.

Rewrite `hy` using `[e, isIntegral_algebraMap_iff (algebraMap ℚ E).injective]`. Take `⟨k, hk⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hy`. Use `⟨k, ?_⟩` and prove the remaining obligations. Establish `: (n : ℚ) = M * k`. Establish `hk' : (k : ℚ) = n / M` using `by simpa using hk`.

Rewrite using `[hk']`. Clear the denominators using the available nonvanishing facts. Conclude with `this` after adjusting the coercions.
-/
theorem dvd_of_eq_mul_integral {E : Type} [Field E] [NumberField E] {M : ℕ} (hM : M ≠ 0) {n : ℤ} {y : E}
    (hy : IsIntegral ℤ y) (h : (n : E) = M * y) : (M : ℤ) ∣ n := by
  have hM' : (M : E) ≠ 0 := by exact_mod_cast hM
  have hM'' : (M : ℚ) ≠ 0 := by exact_mod_cast hM
  have e : y = algebraMap ℚ E ((n : ℚ) / M) := by
    rw [map_div₀, map_intCast, map_natCast, h]; field_simp
  rw [e, isIntegral_algebraMap_iff (algebraMap ℚ E).injective] at hy
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.mp hy
  refine ⟨k, ?_⟩
  have : (n : ℚ) = M * k := by
    have hk' : (k : ℚ) = n / M := by simpa using hk
    rw [hk']; field_simp
  exact_mod_cast this

/- English proof (translation)
Introduce `R H M a N hM haM`. Use `isTotallyComplex_K H` as an intermediate fact. Take `⟨π, p, hp, hN, hn, hc⟩` from `GlobalTheory.T.exists_prime_element_congruent H.K (finrank_K H) M hM (a : 𝓞 H.K) (Nat.Coprime.cast haM) N`. Take `⟨x, hx⟩` from `Ideal.mem_span_singleton'.mp hc`. Establish `hπ : ((algebraMap (𝓞 H.K) (𝓞 H.E) π : 𝓞 H.E) : H.E) = ((π : H.K) : H.E)` using `rfl`.

Establish `hnorm : ((π : H.K) : H.E) * H.conj ((π : H.K) : H.E) = (p : H.E)`. Rewrite using `[norm_K, ← Algebra.coe_norm_int, hn]`. Simplify using the standard rewrite rules. Establish `hx' : algebraMap (𝓞 H.K) (𝓞 H.E) x * (M : 𝓞 H.E) = algebraMap (𝓞 H.K) (𝓞 H.E) π - (a : 𝓞 H.E)`. Use `congrArg (algebraMap (𝓞 H.K) (𝓞 H.E)) hx` as an intermediate fact.

Rewrite `this` using `[map_mul, map_sub, map_natCast, map_natCast]`. Then use the resulting hypothesis. Use `⟨algebraMap (𝓞 H.K) (𝓞 H.E) π, p, hp, hN, ?_, ?_, Ideal.mem_span_singleton'.mpr ⟨_, hx'⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hπ]`. Conclude with `(π : H.K).2`. Rewrite using `[hπ]`.

Conclude with `hnorm`. Use `set y : 𝓞 H.E := algebraMap (𝓞 H.K) (𝓞 H.E) x`. Establish `hy : IsIntegral ℤ (y : H.E)` using `y.isIntegral_coe`. Establish `hcy : IsIntegral ℤ (H.conj (y : H.E))` using `hy.map (H.conj.toAlgHom.restrictScalars ℤ)`. Establish `e : ((π : H.K) : H.E) = a + M * (y : H.E)`.

Use `congrArg (algebraMap (𝓞 H.E) H.E) hx'` as an intermediate fact. Rewrite `this` using `[map_mul, map_sub, map_natCast, map_natCast]`. Rewrite using `[← hπ]`. Take the linear combination `-this`. Rewrite `hnorm` using `[e, map_add, map_mul, map_natCast, map_natCast]`.

Establish `hd : (M : ℤ) ∣ (p : ℤ) - (a : ℤ) ^ 2`. Apply `dvd_of_eq_mul_integral (E := H.E) hM (y := a * (y : H.E) + a * H.conj (y : H.E) + M * ((y : H.E) * H.conj (y : H.E)))` to reduce the goal to its premises. Establish `ha : IsIntegral ℤ (a : H.E)`. Simplify using `using (isIntegral_algebraMap (R := ℤ) (A := H.E) (x := (a : ℤ)))`. Establish `hMi : IsIntegral ℤ (M : H.E)`.

Simplify using `using (isIntegral_algebraMap (R := ℤ) (A := H.E) (x := (M : ℤ)))`. Conclude with `((ha.mul hy).add (ha.mul hcy)).add (hMi.mul (hy.mul hcy))`. Use `push_cast`. Take the linear combination `-hnorm`. Apply `Nat.ModEq.symm` to reduce the goal to its premises.

Rewrite using `[Nat.modEq_iff_dvd]`. Conclude with `hd` after adjusting the coercions.
-/
theorem exists_norm_prime : ∀ (R : Ranks) (H : Host R) (M a N : ℕ), M ≠ 0 → Nat.Coprime a M →
    ∃ (π : 𝓞 H.E) (p : ℕ), p.Prime ∧ N < p ∧ (π : H.E) ∈ H.K ∧
      (π : H.E) * H.conj (π : H.E) = (p : H.E) ∧ π - (a : 𝓞 H.E) ∈ Ideal.span {(M : 𝓞 H.E)} ∧
      p ≡ a ^ 2 [MOD M] := by
  intro R H M a N hM haM
  have := isTotallyComplex_K H
  obtain ⟨π, p, hp, hN, hn, hc⟩ := GlobalTheory.T.exists_prime_element_congruent H.K (finrank_K H) M hM (a : 𝓞 H.K)
    (Nat.Coprime.cast haM) N
  obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.mp hc
  have hπ : ((algebraMap (𝓞 H.K) (𝓞 H.E) π : 𝓞 H.E) : H.E) = ((π : H.K) : H.E) := rfl
  have hnorm : ((π : H.K) : H.E) * H.conj ((π : H.K) : H.E) = (p : H.E) := by
    rw [norm_K, ← Algebra.coe_norm_int, hn]
    simp
  have hx' : algebraMap (𝓞 H.K) (𝓞 H.E) x * (M : 𝓞 H.E) =
      algebraMap (𝓞 H.K) (𝓞 H.E) π - (a : 𝓞 H.E) := by
    have := congrArg (algebraMap (𝓞 H.K) (𝓞 H.E)) hx
    rwa [map_mul, map_sub, map_natCast, map_natCast] at this
  refine ⟨algebraMap (𝓞 H.K) (𝓞 H.E) π, p, hp, hN, ?_, ?_, Ideal.mem_span_singleton'.mpr ⟨_, hx'⟩, ?_⟩
  · rw [hπ]; exact (π : H.K).2
  · rw [hπ]; exact hnorm
  · set y : 𝓞 H.E := algebraMap (𝓞 H.K) (𝓞 H.E) x
    have hy : IsIntegral ℤ (y : H.E) := y.isIntegral_coe
    have hcy : IsIntegral ℤ (H.conj (y : H.E)) := hy.map (H.conj.toAlgHom.restrictScalars ℤ)
    have e : ((π : H.K) : H.E) = a + M * (y : H.E) := by
      have := congrArg (algebraMap (𝓞 H.E) H.E) hx'
      rw [map_mul, map_sub, map_natCast, map_natCast] at this
      rw [← hπ]
      linear_combination -this
    rw [e, map_add, map_mul, map_natCast, map_natCast] at hnorm
    have hd : (M : ℤ) ∣ (p : ℤ) - (a : ℤ) ^ 2 := by
      apply dvd_of_eq_mul_integral (E := H.E) hM
        (y := a * (y : H.E) + a * H.conj (y : H.E) + M * ((y : H.E) * H.conj (y : H.E)))
      · have ha : IsIntegral ℤ (a : H.E) := by
          simpa using (isIntegral_algebraMap (R := ℤ) (A := H.E) (x := (a : ℤ)))
        have hMi : IsIntegral ℤ (M : H.E) := by
          simpa using (isIntegral_algebraMap (R := ℤ) (A := H.E) (x := (M : ℤ)))
        exact ((ha.mul hy).add (ha.mul hcy)).add (hMi.mul (hy.mul hcy))
      · push_cast
        linear_combination -hnorm
    apply Nat.ModEq.symm
    rw [Nat.modEq_iff_dvd]
    exact_mod_cast hd

end GlobalTheory.Mem.NormPrime
