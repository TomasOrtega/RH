import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfinitelyManyPrimesInRayClassStatement
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Formalism.LocalRingCardinality.ConjSqrtMinusD
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK

section
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder

namespace GlobalTheory.Mem.ImaginaryQuadraticNorm

/- English proof (translation)
Take `⟨φ⟩ : Nonempty (K →+* ℂ)` from `inferInstance`. Establish `hne : ComplexEmbedding.conjugate φ ≠ φ`. Introduce `h`. Conclude with `IsTotallyComplex.complexEmbedding_not_isReal φ (ComplexEmbedding.isReal_iff.2 h)`. Establish `hcard : Fintype.card (K →+* ℂ) = 2` using `by rw [Embeddings.card, h2]`.

Establish `huniv : (Finset.univ : Finset (K →+* ℂ)) = {ComplexEmbedding.conjugate φ, φ}`. Use `symm`. Apply `Finset.eq_univ_of_card` to reduce the goal to its premises. Rewrite using `[Finset.card_pair hne, hcard]`. Establish `h1` using `Algebra.norm_eq_prod_embeddings ℚ ℂ (x : K)`.

Rewrite `h1` using `[← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun f => f (x : K)) (fun σ => σ (x : K)) (fun _ => by simp [RingHom.equivRatAlgHom_apply]), huniv, Finset.prod_pair hne, ComplexEmbedding.conjugate_coe_eq, mul_comm, Complex.mul_conj, ← Algebra.coe_norm_int]`. Establish `h3 : ((Algebra.norm ℤ x : ℤ) : ℝ) = Complex.normSq (φ x)`. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[← h1]`. Simplify using the standard rewrite rules.

Establish `h4 : (0 : ℝ) ≤ ((Algebra.norm ℤ x : ℤ) : ℝ)` using `h3 ▸ Complex.normSq_nonneg _`. Conclude with `h4` after adjusting the coercions.
-/
theorem norm_nonneg_of_imag_quadratic (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (h2 : Module.finrank ℚ K = 2) (x : 𝓞 K) : 0 ≤ Algebra.norm ℤ x := by
  classical
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hne : ComplexEmbedding.conjugate φ ≠ φ := by
    intro h
    exact IsTotallyComplex.complexEmbedding_not_isReal φ (ComplexEmbedding.isReal_iff.2 h)
  have hcard : Fintype.card (K →+* ℂ) = 2 := by rw [Embeddings.card, h2]
  have huniv : (Finset.univ : Finset (K →+* ℂ)) = {ComplexEmbedding.conjugate φ, φ} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hne, hcard]
  have h1 := Algebra.norm_eq_prod_embeddings ℚ ℂ (x : K)
  rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun f => f (x : K)) (fun σ => σ (x : K))
    (fun _ => by simp [RingHom.equivRatAlgHom_apply]), huniv, Finset.prod_pair hne,
    ComplexEmbedding.conjugate_coe_eq, mul_comm, Complex.mul_conj, ← Algebra.coe_norm_int] at h1
  have h3 : ((Algebra.norm ℤ x : ℤ) : ℝ) = Complex.normSq (φ x) := by
    apply Complex.ofReal_injective
    rw [← h1]; simp
  have h4 : (0 : ℝ) ≤ ((Algebra.norm ℤ x : ℤ) : ℝ) := h3 ▸ Complex.normSq_nonneg _
  exact_mod_cast h4

/- English proof (translation)
Take `⟨D⟩` from `nonempty_rayData_of_ne_zero K M (by omega)`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Establish `hu : IsUnit ((M : ℕ) : 𝓞 K)` using `isCoprime_zero_left.1 ha`. Establish `h1` using `hu.map (Algebra.norm ℤ)`.

Establish `h3 : Algebra.norm ℤ ((M : ℕ) : 𝓞 K) = (M : ℤ) ^ 2`. Use `Algebra.norm_algebraMap (R := ℤ) (S := 𝓞 K) (M : ℤ)` as an intermediate fact. Rewrite `this` using `[RingOfIntegers.rank, h2]`. Simplify using `using this`. Rewrite `h1` using `[h3, isUnit_pow_iff two_ne_zero, Int.isUnit_iff]`.

Use linear arithmetic over natural numbers and integers. Establish `hac : IsCoprime (Ideal.span {a}) (Ideal.span {(M : 𝓞 K)})` using `(Ideal.isCoprime_span_singleton_iff _ _).2 ha`. Take `⟨v, hc, hp, hN⟩` from `GlobalTheory.T.infinitely_many_primes_in_ray_class K h2 M hM D (D.cls (Ideal.span {a})) N`. Take `⟨x, y, hx0, hy0, hx, hy, hxy⟩` from `(D.cls_eq _ _ v.2 hac v.1.ne_bot (by simpa using ha0)).1 hc`. Rewrite `hxy` using `[Ideal.span_singleton_mul_span_singleton]`.

Establish `hdvd : x ∣ y * a`. Rewrite using `[← Ideal.mem_span_singleton]`. Establish `: y * a ∈ Ideal.span {x} * v.1.asIdeal`. Rewrite using `[hxy]`. Conclude with `Ideal.mem_span_singleton_self _`.

Conclude with `Ideal.mul_le_left this`. Take `⟨π, hπ⟩` from `hdvd`. Establish `hv : v.1.asIdeal = Ideal.span {π}`. Rewrite `hxy` using `[hπ, ← Ideal.span_singleton_mul_span_singleton]`. Conclude with `mul_left_cancel₀ (by simpa using hx0) hxy`.

Use `⟨π, Ideal.absNorm v.1.asIdeal, hp, hN, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hv, Ideal.absNorm_span_singleton, Int.natAbs_of_nonneg (norm_nonneg_of_imag_quadratic K h2 π)]`. Establish `: π - a = (y - 1) * a - (x - 1) * π` using `by linear_combination -hπ`. Rewrite using `[this]`. Conclude with `Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hy) (Ideal.mul_mem_right _ _ hx)`.
-/
theorem exists_prime_norm_of_two_le (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (h2 : Module.finrank ℚ K = 2) (M : ℕ) (hM : 2 ≤ M) (a : 𝓞 K) (ha : IsCoprime a (M : 𝓞 K)) (N : ℕ) :
    ∃ (π : 𝓞 K) (p : ℕ), p.Prime ∧ N < p ∧ Algebra.norm ℤ π = p ∧ π - a ∈ Ideal.span {(M : 𝓞 K)} := by
  obtain ⟨D⟩ := nonempty_rayData_of_ne_zero K M (by omega)
  have ha0 : a ≠ 0 := by
    rintro rfl
    have hu : IsUnit ((M : ℕ) : 𝓞 K) := isCoprime_zero_left.1 ha
    have h1 := hu.map (Algebra.norm ℤ)
    have h3 : Algebra.norm ℤ ((M : ℕ) : 𝓞 K) = (M : ℤ) ^ 2 := by
      have := Algebra.norm_algebraMap (R := ℤ) (S := 𝓞 K) (M : ℤ)
      rw [RingOfIntegers.rank, h2] at this
      simpa using this
    rw [h3, isUnit_pow_iff two_ne_zero, Int.isUnit_iff] at h1
    omega
  have hac : IsCoprime (Ideal.span {a}) (Ideal.span {(M : 𝓞 K)}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).2 ha
  obtain ⟨v, hc, hp, hN⟩ := GlobalTheory.T.infinitely_many_primes_in_ray_class K h2 M hM D (D.cls (Ideal.span {a})) N
  obtain ⟨x, y, hx0, hy0, hx, hy, hxy⟩ := (D.cls_eq _ _ v.2 hac v.1.ne_bot
    (by simpa using ha0)).1 hc
  rw [Ideal.span_singleton_mul_span_singleton] at hxy
  have hdvd : x ∣ y * a := by
    rw [← Ideal.mem_span_singleton]
    have : y * a ∈ Ideal.span {x} * v.1.asIdeal := by
      rw [hxy]; exact Ideal.mem_span_singleton_self _
    exact Ideal.mul_le_left this
  obtain ⟨π, hπ⟩ := hdvd
  have hv : v.1.asIdeal = Ideal.span {π} := by
    rw [hπ, ← Ideal.span_singleton_mul_span_singleton] at hxy
    exact mul_left_cancel₀ (by simpa using hx0) hxy
  refine ⟨π, Ideal.absNorm v.1.asIdeal, hp, hN, ?_, ?_⟩
  · rw [hv, Ideal.absNorm_span_singleton, Int.natAbs_of_nonneg (norm_nonneg_of_imag_quadratic K h2 π)]
  · have : π - a = (y - 1) * a - (x - 1) * π := by linear_combination -hπ
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hy) (Ideal.mul_mem_right _ _ hx)

/- English proof (translation)
Introduce `K _ _ _ h2 M hM a ha N`. Break down `Nat.lt_or_ge M 2 with h | h` into its components or cases. Take `rfl : M = 1` from `by omega`. Take `⟨π, p, hp, hN, hn, -⟩` from `exists_prime_norm_of_two_le K h2 2 le_rfl 1 isCoprime_one_left N`. Conclude with `⟨π, p, hp, hN, hn, by simp⟩`.

Conclude with `exists_prime_norm_of_two_le K h2 M h a ha N`.
-/
theorem exists_prime_norm : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (M : ℕ), M ≠ 0 → ∀ (a : 𝓞 K), IsCoprime a (M : 𝓞 K) → ∀ N : ℕ, ∃ (π : 𝓞 K) (p : ℕ), p.Prime ∧ N < p ∧ Algebra.norm ℤ π = p ∧ π - a ∈ Ideal.span {(M : 𝓞 K)} := by
  intro K _ _ _ h2 M hM a ha N
  rcases Nat.lt_or_ge M 2 with h | h
  · obtain rfl : M = 1 := by omega
    obtain ⟨π, p, hp, hN, hn, -⟩ := exists_prime_norm_of_two_le K h2 2 le_rfl 1 isCoprime_one_left N
    exact ⟨π, p, hp, hN, hn, by simp⟩
  · exact exists_prime_norm_of_two_le K h2 M h a ha N

end GlobalTheory.Mem.ImaginaryQuadraticNorm

end

section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem.ImaginaryQuadraticNorm

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
Introduce `R H M a N hM haM`. Use `isTotallyComplex_K H` as an intermediate fact. Take `⟨π, p, hp, hN, hn, hc⟩` from `exists_prime_norm H.K (finrank_K H) M hM (a : 𝓞 H.K) (Nat.Coprime.cast haM) N`. Take `⟨x, hx⟩` from `Ideal.mem_span_singleton'.mp hc`. Establish `hπ : ((algebraMap (𝓞 H.K) (𝓞 H.E) π : 𝓞 H.E) : H.E) = ((π : H.K) : H.E)` using `rfl`.

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
  obtain ⟨π, p, hp, hN, hn, hc⟩ := exists_prime_norm H.K (finrank_K H) M hM (a : 𝓞 H.K)
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

end GlobalTheory.Mem.ImaginaryQuadraticNorm

end
