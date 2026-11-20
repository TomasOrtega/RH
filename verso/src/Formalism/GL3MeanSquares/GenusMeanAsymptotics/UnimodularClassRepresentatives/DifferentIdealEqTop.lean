import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CovolumeIntegerLatticeEq
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSqAbsNormOfInert

open NumberField Module Polynomial

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

/- English proof (translation)
Take `⟨hTC, hconj, -⟩` from `hK`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Take `⟨w⟩ : Nonempty (NumberField.InfinitePlace K)` from `inferInstance`. Establish `hc` using `hTC.isComplex w`.

Rewrite `hc` using `[NumberField.InfinitePlace.isComplex_iff]`. Apply `hc` to reduce the goal to its premises. Rewrite using `[NumberField.ComplexEmbedding.isReal_iff]`. Use extensionality with `a`. Rewrite using `[NumberField.ComplexEmbedding.conjugate_coe_eq, ← hconj, h]`.
-/
theorem exists_star_ne (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) : ∃ a : K, star a ≠ a := by
  obtain ⟨hTC, hconj, -⟩ := hK
  by_contra h
  push_neg at h
  obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace K) := inferInstance
  have hc := hTC.isComplex w
  rw [NumberField.InfinitePlace.isComplex_iff] at hc
  apply hc
  rw [NumberField.ComplexEmbedding.isReal_iff]
  ext a
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq, ← hconj, h]

/- English proof (translation)
The claim follows from `(hF _).2 ⟨u, rfl⟩`.
-/
theorem star_algebraMap (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) (u : F) :
    star (algebraMap F K u) = algebraMap F K u :=
  (hF _).2 ⟨u, rfl⟩

/- English proof (translation)
Establish `hb : a - star a ≠ 0` using `sub_ne_zero.mpr (Ne.symm ha)`. Take `⟨w, hw⟩ : ∃ w : K, w * (a - star a) = x - star x` from `⟨(x - star x) / (a - star a), div_mul_cancel₀ _ hb⟩`. Establish `hsw : star w = w`. Establish `h1` using `congrArg star hw`. Rewrite `h1` using `[star_mul', star_sub, star_sub, star_star, star_star]`.

Apply `mul_right_cancel₀ hb` to reduce the goal to its premises. Take the linear combination `-h1 - hw`. Take `⟨v, hv⟩` from `(hF w).1 hsw`. Establish `hz : star (x - w * a) = x - w * a`. Rewrite using `[star_sub, star_mul', hsw]`.

Take the linear combination `hw`. Take `⟨u, hu⟩` from `(hF _).1 hz`. Conclude with `⟨u, v, by rw [hu, hv]; ring⟩`.
-/
theorem exists_decomp (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) {a : K}
    (ha : star a ≠ a) (x : K) : ∃ u v : F, x = algebraMap F K u + algebraMap F K v * a := by
  have hb : a - star a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  obtain ⟨w, hw⟩ : ∃ w : K, w * (a - star a) = x - star x :=
    ⟨(x - star x) / (a - star a), div_mul_cancel₀ _ hb⟩
  have hsw : star w = w := by
    have h1 := congrArg star hw
    rw [star_mul', star_sub, star_sub, star_star, star_star] at h1
    apply mul_right_cancel₀ hb
    linear_combination -h1 - hw
  obtain ⟨v, hv⟩ := (hF w).1 hsw
  have hz : star (x - w * a) = x - w * a := by
    rw [star_sub, star_mul', hsw]
    linear_combination hw
  obtain ⟨u, hu⟩ := (hF _).1 hz
  exact ⟨u, v, by rw [hu, hv]; ring⟩

/- English proof (translation)
Take `⟨a, ha⟩` from `exists_star_ne hK`. Establish `hli : LinearIndependent F ![(1 : K), a]`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`. Distinguish the cases in `ht : t = 0`.

Substitute `ht` using the available equality. Simplify using `only [zero_smul, add_zero] at hst`. Conclude with `⟨(smul_eq_zero.mp hst).resolve_right one_ne_zero, rfl⟩`. It suffices to derive a contradiction. Apply `ha` to reduce the goal to its premises.

Establish `htK : algebraMap F K t ≠ 0` using `(_root_.map_ne_zero _).mpr ht`. Establish `hA : a = algebraMap F K (-s / t)`. Rewrite `hst` using `[Algebra.smul_def, Algebra.smul_def, mul_one]`. Rewrite using `[map_div₀, map_neg, eq_div_iff htK]`. Take the linear combination `hst`.

Conclude with `(hF a).2 ⟨_, hA.symm⟩`. Establish `hsp : ⊤ ≤ Submodule.span F (Set.range ![(1 : K), a])`. Introduce `x _`. Take `⟨u, v, rfl⟩` from `exists_decomp hF ha x`. Apply `Submodule.add_mem` to reduce the goal to its premises.

Rewrite using `[Algebra.algebraMap_eq_smul_one]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, by simp⟩)`. Rewrite using `[← Algebra.smul_def]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, by simp⟩)`. Rewrite using `[Module.finrank_eq_card_basis (Basis.mk hli hsp)]`.

Simplify using the standard rewrite rules.
-/
theorem finrank_eq_two (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) : finrank F K = 2 := by
  obtain ⟨a, ha⟩ := exists_star_ne hK
  have hli : LinearIndependent F ![(1 : K), a] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right one_ne_zero, rfl⟩
    · exfalso
      apply ha
      have htK : algebraMap F K t ≠ 0 := (_root_.map_ne_zero _).mpr ht
      have hA : a = algebraMap F K (-s / t) := by
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
        rw [map_div₀, map_neg, eq_div_iff htK]
        linear_combination hst
      exact (hF a).2 ⟨_, hA.symm⟩
  have hsp : ⊤ ≤ Submodule.span F (Set.range ![(1 : K), a]) := by
    intro x _
    obtain ⟨u, v, rfl⟩ := exists_decomp hF ha x
    apply Submodule.add_mem
    · rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, by simp⟩)
    · rw [← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, by simp⟩)
  rw [Module.finrank_eq_card_basis (Basis.mk hli hsp)]
  simp

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce `x _`. Take `⟨u, v, rfl⟩` from `exists_decomp hF ha x`. Conclude with `Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ u) (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ v) (Algebra.subset_adjoin (Set.mem_singleton a)))`.
-/
theorem adjoin_eq_top (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) {a : K}
    (ha : star a ≠ a) : Algebra.adjoin F {a} = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨u, v, rfl⟩ := exists_decomp hF ha x
  exact Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ u)
    (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ v) (Algebra.subset_adjoin (Set.mem_singleton a)))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_algebraMap (z : 𝓞 F) :
    algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) z) = algebraMap F K (algebraMap (𝓞 F) F z) := by
  rfl

/- English proof (translation)
Take `⟨u, hu⟩` from `(hF _).1 hy`. Establish `hint : IsIntegral ℤ u`. Establish `h1 : IsIntegral ℤ (algebraMap F K u)`. Rewrite using `[hu]`. Conclude with `RingOfIntegers.isIntegral_coe y`.

Conclude with `(isIntegral_algebraMap_iff (algebraMap F K).injective).mp h1`. Use `⟨⟨u, hint⟩, ?_⟩` and prove the remaining obligations. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Conclude with `(coe_algebraMap (F := F) (K := K) ⟨u, hint⟩).trans hu`.
-/
theorem exists_int_of_star_eq (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K))
    (y : 𝓞 K) (hy : star (algebraMap (𝓞 K) K y) = algebraMap (𝓞 K) K y) :
    ∃ z : 𝓞 F, algebraMap (𝓞 F) (𝓞 K) z = y := by
  obtain ⟨u, hu⟩ := (hF _).1 hy
  have hint : IsIntegral ℤ u := by
    have h1 : IsIntegral ℤ (algebraMap F K u) := by
      rw [hu]; exact RingOfIntegers.isIntegral_coe y
    exact (isIntegral_algebraMap_iff (algebraMap F K).injective).mp h1
  refine ⟨⟨u, hint⟩, ?_⟩
  apply RingOfIntegers.ext
  exact (coe_algebraMap (F := F) (K := K) ⟨u, hint⟩).trans hu

/- English proof (translation)
Take `⟨-, hconj, -⟩` from `hK`. Use `⟨fun w => ?_⟩` and prove the remaining obligations. Take `⟨v, rfl⟩` from `NumberField.InfinitePlace.comap_surjective (k := F) (K := K) w`. Apply the tactic sequence `try dsimp only`. Rewrite using `[← NumberField.InfinitePlace.mk_embedding v, NumberField.InfinitePlace.comap_mk]`.

Assume the negation of the conclusion as `h`. Rewrite `h` using `[NumberField.InfinitePlace.not_isReal_iff_isComplex, NumberField.InfinitePlace.isComplex_mk_iff]`. Apply `h` to reduce the goal to its premises. Rewrite using `[NumberField.ComplexEmbedding.isReal_iff]`. Use extensionality with `u`.

Rewrite using `[NumberField.ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, ← hconj, star_algebraMap hF]`.
-/
theorem isTotallyReal (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) : IsTotallyReal F := by
  obtain ⟨-, hconj, -⟩ := hK
  refine ⟨fun w => ?_⟩
  obtain ⟨v, rfl⟩ := NumberField.InfinitePlace.comap_surjective (k := F) (K := K) w
  try dsimp only
  rw [← NumberField.InfinitePlace.mk_embedding v, NumberField.InfinitePlace.comap_mk]
  by_contra h
  rw [NumberField.InfinitePlace.not_isReal_iff_isComplex, NumberField.InfinitePlace.isComplex_mk_iff] at h
  apply h
  rw [NumberField.ComplexEmbedding.isReal_iff]
  ext u
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, ← hconj, star_algebraMap hF]

/- English proof (translation)
Establish `ht' : star (algebraMap (𝓞 K) K t) = algebraMap (𝓞 K) K θ` using `by rw [ht, star_star]`. Take `⟨s, hs⟩` from `exists_int_of_star_eq hF (θ + t) (by rw [map_add, star_add, ht', ← ht, add_comm])`. Take `⟨p, hp⟩` from `exists_int_of_star_eq hF (θ * t) (by rw [map_mul, star_mul', ht', ← ht, mul_comm])`. Take `⟨q, hq⟩ : ∃ q : Polynomial (𝓞 F), q = X ^ 2 - C s * X + C p` from `⟨_, rfl⟩`. Establish `hqdeg : q.natDegree = 2` using `by rw [hq]; compute_degree!`.

Establish `hqm : q.Monic` using `by rw [hq]; monicity!`. Establish `hroot : aeval θ q = 0`. Rewrite using `[hq]`. Simplify using `only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, hs, hp]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hint : IsIntegral (𝓞 F) θ` using `by first`. Consider the case `exact Algebra.IsIntegral.isIntegral θ`. Consider the case `exact IsIntegral.tower_top (A := 𝓞 F) (RingOfIntegers.isIntegral θ)`. Consider the case `exact (Algebra.IsIntegral.isIntegral (R := ℤ) θ).tower_top`. Establish `hdvd : minpoly (𝓞 F) θ ∣ q` using `minpoly.isIntegrallyClosed_dvd hint hroot`.

Establish `hdeg2 : 2 ≤ (minpoly (𝓞 F) θ).natDegree`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `h1 : (minpoly (𝓞 F) θ).natDegree = 1`. Use `minpoly.natDegree_pos hint` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hd1 : (minpoly (𝓞 F) θ).degree = 1`. Rewrite using `[Polynomial.degree_eq_natDegree (minpoly.ne_zero hint), h1]`. Both sides reduce to the same expression. Establish `hr : θ ∈ (algebraMap (𝓞 F) (𝓞 K)).range` using `by first`.

Consider the case `exact minpoly.mem_range_of_degree_eq_one (𝓞 F) θ hd1`. Consider the case `exact minpoly.mem_range_of_degree_eq_one hd1`. Consider the case `exact minpoly.mem_range_of_degree_eq_one (𝓞 F) hd1`. Take `⟨z, hz⟩` from `hr`. Apply `hne` to reduce the goal to its premises.

Apply `RingOfIntegers.ext` to reduce the goal to its premises. Establish `hfx : star (algebraMap (𝓞 K) K θ) = algebraMap (𝓞 K) K θ`. Rewrite using `[← hz, coe_algebraMap]`. Conclude with `star_algebraMap hF _`. Conclude with `(ht.trans hfx).symm`.

Establish `heq : q = minpoly (𝓞 F) θ` using `Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hqm hdvd (by rw [hqdeg]; exact hdeg2)`. Rewrite using `[← heq, hq]`. Simplify using `only [derivative_add, derivative_sub, derivative_mul, derivative_X_pow, derivative_C, derivative_X, zero_mul, mul_one, zero_add, add_zero, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, map_natCast, hs]`. Use `first`. Consider the case `ring`.

Consider the case `(norm_num; ring)`. Consider the case `norm_num`. Consider the case `(push_cast; ring)`.
-/
theorem minpoly_eq (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) (θ t : 𝓞 K)
    (ht : algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K θ)) (hne : θ ≠ t) :
    aeval θ (derivative (minpoly (𝓞 F) θ)) = θ - t := by
  have ht' : star (algebraMap (𝓞 K) K t) = algebraMap (𝓞 K) K θ := by rw [ht, star_star]
  obtain ⟨s, hs⟩ := exists_int_of_star_eq hF (θ + t) (by rw [map_add, star_add, ht', ← ht, add_comm])
  obtain ⟨p, hp⟩ := exists_int_of_star_eq hF (θ * t) (by rw [map_mul, star_mul', ht', ← ht, mul_comm])
  obtain ⟨q, hq⟩ : ∃ q : Polynomial (𝓞 F), q = X ^ 2 - C s * X + C p := ⟨_, rfl⟩
  have hqdeg : q.natDegree = 2 := by rw [hq]; compute_degree!
  have hqm : q.Monic := by rw [hq]; monicity!
  have hroot : aeval θ q = 0 := by
    rw [hq]
    simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, hs, hp]
    ring
  have hint : IsIntegral (𝓞 F) θ := by
    first
      | exact Algebra.IsIntegral.isIntegral θ
      | exact IsIntegral.tower_top (A := 𝓞 F) (RingOfIntegers.isIntegral θ)
      | exact (Algebra.IsIntegral.isIntegral (R := ℤ) θ).tower_top
  have hdvd : minpoly (𝓞 F) θ ∣ q := minpoly.isIntegrallyClosed_dvd hint hroot
  have hdeg2 : 2 ≤ (minpoly (𝓞 F) θ).natDegree := by
    by_contra hlt
    push_neg at hlt
    have h1 : (minpoly (𝓞 F) θ).natDegree = 1 := by
      have := minpoly.natDegree_pos hint
      omega
    have hd1 : (minpoly (𝓞 F) θ).degree = 1 := by
      rw [Polynomial.degree_eq_natDegree (minpoly.ne_zero hint), h1]
      rfl
    have hr : θ ∈ (algebraMap (𝓞 F) (𝓞 K)).range := by
      first
        | exact minpoly.mem_range_of_degree_eq_one (𝓞 F) θ hd1
        | exact minpoly.mem_range_of_degree_eq_one hd1
        | exact minpoly.mem_range_of_degree_eq_one (𝓞 F) hd1
    obtain ⟨z, hz⟩ := hr
    apply hne
    apply RingOfIntegers.ext
    have hfx : star (algebraMap (𝓞 K) K θ) = algebraMap (𝓞 K) K θ := by
      rw [← hz, coe_algebraMap]
      exact star_algebraMap hF _
    exact (ht.trans hfx).symm
  have heq : q = minpoly (𝓞 F) θ :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hqm hdvd (by rw [hqdeg]; exact hdeg2)
  rw [← heq, hq]
  simp only [derivative_add, derivative_sub, derivative_mul, derivative_X_pow, derivative_C,
    derivative_X, zero_mul, mul_one, zero_add, add_zero, map_add, map_sub, map_mul, map_pow,
    aeval_X, aeval_C, map_natCast, hs]
  first
    | ring
    | (norm_num; ring)
    | norm_num
    | (push_cast; ring)

/- English proof (translation)
Take `⟨-, -, hmax⟩` from `hK`. Assume the negation of the conclusion as `hne`. Take `⟨P, hP, hle⟩` from `Ideal.exists_le_maximal _ hne`. Take `⟨θ, t, ht, hθt⟩` from `hmax P hP`. Establish `hne' : θ ≠ t` using `fun h => hθt (by rw [h, sub_self]; exact P.zero_mem)`.

Establish `hstar : star (algebraMap (𝓞 K) K θ) ≠ algebraMap (𝓞 K) K θ`. Rewrite using `[← ht]`. Conclude with `fun h => hne' (RingOfIntegers.ext h.symm)`. Apply `hθt` to reduce the goal to its premises. Apply `hle` to reduce the goal to its premises.

Rewrite using `[← minpoly_eq hF θ t ht hne']`. Conclude with `aeval_derivative_mem_differentIdeal (A := 𝓞 F) (K := F) (L := K) θ (adjoin_eq_top hF hstar)`.
-/
theorem differentIdeal_eq_top (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) :
    differentIdeal (𝓞 F) (𝓞 K) = ⊤ := by
  obtain ⟨-, -, hmax⟩ := hK
  by_contra hne
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨θ, t, ht, hθt⟩ := hmax P hP
  have hne' : θ ≠ t := fun h => hθt (by rw [h, sub_self]; exact P.zero_mem)
  have hstar : star (algebraMap (𝓞 K) K θ) ≠ algebraMap (𝓞 K) K θ := by
    rw [← ht]; exact fun h => hne' (RingOfIntegers.ext h.symm)
  apply hθt
  apply hle
  rw [← minpoly_eq hF θ t ht hne']
  exact aeval_derivative_mem_differentIdeal (A := 𝓞 F) (K := F) (L := K) θ (adjoin_eq_top hF hstar)

/- English proof (translation)
Rewrite using `[natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) K (𝓞 K), differentIdeal_eq_top hK hF, Ideal.absNorm_top, one_mul, finrank_eq_two hK hF]`.
-/
theorem natAbs_discr (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) :
    (discr K).natAbs = (discr F).natAbs ^ 2 := by
  rw [natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) K (𝓞 K),
    differentIdeal_eq_top hK hF, Ideal.absNorm_top, one_mul, finrank_eq_two hK hF]

/- English proof (translation)
Use `haveI := isTotallyReal hK hF`. Use `first`. Consider the case `exact NumberField.discr_pos_of_isTotallyReal F`. Consider the case `(have h := NumberField.sign_discr F`. Rewrite `h` using `[IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero]`.

Conclude with `Int.sign_eq_one_iff_pos.mp h)`.
-/
theorem discr_pos (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) : 0 < discr F := by
  haveI := isTotallyReal hK hF
  first
    | exact NumberField.discr_pos_of_isTotallyReal F
    | (have h := NumberField.sign_discr F
       rw [IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero] at h
       exact Int.sign_eq_one_iff_pos.mp h)

end Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation

namespace Formalism.HermitianLattices.Ext.L3

/- English proof (translation)
Introduce `K F _ _ _ _ _ _ hK hF`. Establish `hpos` using `QuadraticExtensionConjugation.discr_pos hK hF`. Establish `h1` using `QuadraticExtensionConjugation.natAbs_discr hK hF`. Establish `hTC : IsTotallyComplex K`. Take `⟨h, -, -⟩` from `hK`.

Conclude with `h`. Establish `hA : |(discr K : ℝ)| = (discr F : ℝ) ^ 2`. Establish `h2` using `congrArg (fun n : ℕ => (n : ℝ)) h1`. Simplify using `only [Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs] at h2`. Rewrite using `[h2, sq_abs]`.

Establish `hdeg : finrank ℚ F = Formalism.HermitianLatticesTheory.fDeg K`. Establish `e1` using `NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K`. Establish `e2` using `Module.finrank_mul_finrank ℚ F K`. Establish `e3` using `NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := K)`. Establish `e4 : NumberField.InfinitePlace.nrRealPlaces K = 0` using `by first`.

Consider the case `exact NumberField.IsTotallyComplex.nrRealPlaces_eq_zero`. Consider the case `exact IsTotallyComplex.nrRealPlaces_eq_zero`. Consider the case `exact NumberField.InfinitePlace.nrRealPlaces_eq_zero_iff.mpr hTC`. Consider the case `exact NumberField.nrRealPlaces_eq_zero_iff.mpr hTC`. Consider the case `(haveI : IsEmpty {w : NumberField.InfinitePlace K // w.IsReal} := ⟨fun w => (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr (hTC.isComplex w.1)) w.2⟩`.

Simplify using `[NumberField.InfinitePlace.nrRealPlaces])`. Consider the case `(unfold NumberField.InfinitePlace.nrRealPlaces`. Rewrite using `[Fintype.card_eq_zero_iff]`. Conclude with `⟨fun w => (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr (hTC.isComplex w.1)) w.2⟩)`. Rewrite `e2` using `[QuadraticExtensionConjugation.finrank_eq_two hK hF]`.

Unfold `Formalism.HermitianLatticesTheory.fDeg`. Use linear arithmetic over natural numbers and integers. Use `⟨hA, hdeg, ?_⟩` and prove the remaining obligations. Establish `hF0 : (0 : ℝ) < discr F` using `by exact_mod_cast hpos`. Establish `hd : 0 < Formalism.HermitianLatticesTheory.fDeg K`.

Unfold `Formalism.HermitianLatticesTheory.fDeg`. Conclude with `Fintype.card_pos`. Establish `hd0 : ((Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ) ≠ 0` using `by exact_mod_cast hd.ne'`. Unfold `Formalism.HermitianLatticesTheory.vInv`. Rewrite using `[show ∀ x : ℝ, 2 * (x / 2) = x from fun x => by ring, hA, ← Real.rpow_natCast (discr F : ℝ) 2, ← Real.rpow_mul hF0.le, ← Real.rpow_natCast _ (Formalism.HermitianLatticesTheory.fDeg K), ← Real.rpow_mul hF0.le]`.

Use `conv_lhs => rw [← Real.rpow_one (discr F : ℝ)]`. Use `congr 1`. Use `first`. Consider the case `(push_cast; field_simp)`. Consider the case `(push_cast; field_simp; ring)`.

Consider the case `field_simp`. Consider the case `(field_simp; ring)`.
-/
theorem discrTower : DiscrTower := by
  intro K F _ _ _ _ _ _ hK hF
  have hpos := QuadraticExtensionConjugation.discr_pos hK hF
  have h1 := QuadraticExtensionConjugation.natAbs_discr hK hF
  have hTC : IsTotallyComplex K := by
    obtain ⟨h, -, -⟩ := hK
    exact h
  have hA : |(discr K : ℝ)| = (discr F : ℝ) ^ 2 := by
    have h2 := congrArg (fun n : ℕ => (n : ℝ)) h1
    simp only [Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs] at h2
    rw [h2, sq_abs]
  have hdeg : finrank ℚ F = Formalism.HermitianLatticesTheory.fDeg K := by
    have e1 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
    have e2 := Module.finrank_mul_finrank ℚ F K
    have e3 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := K)
    have e4 : NumberField.InfinitePlace.nrRealPlaces K = 0 := by
      first
        | exact NumberField.IsTotallyComplex.nrRealPlaces_eq_zero
        | exact IsTotallyComplex.nrRealPlaces_eq_zero
        | exact NumberField.InfinitePlace.nrRealPlaces_eq_zero_iff.mpr hTC
        | exact NumberField.nrRealPlaces_eq_zero_iff.mpr hTC
        | (haveI : IsEmpty {w : NumberField.InfinitePlace K // w.IsReal} :=
             ⟨fun w => (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr (hTC.isComplex w.1)) w.2⟩
           simp [NumberField.InfinitePlace.nrRealPlaces])
        | (unfold NumberField.InfinitePlace.nrRealPlaces
           rw [Fintype.card_eq_zero_iff]
           exact ⟨fun w => (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr (hTC.isComplex w.1)) w.2⟩)
    rw [QuadraticExtensionConjugation.finrank_eq_two hK hF] at e2
    unfold Formalism.HermitianLatticesTheory.fDeg
    omega
  refine ⟨hA, hdeg, ?_⟩
  have hF0 : (0 : ℝ) < discr F := by exact_mod_cast hpos
  have hd : 0 < Formalism.HermitianLatticesTheory.fDeg K := by
    unfold Formalism.HermitianLatticesTheory.fDeg
    exact Fintype.card_pos
  have hd0 : ((Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  unfold Formalism.HermitianLatticesTheory.vInv
  rw [show ∀ x : ℝ, 2 * (x / 2) = x from fun x => by ring, hA, ← Real.rpow_natCast (discr F : ℝ) 2,
    ← Real.rpow_mul hF0.le, ← Real.rpow_natCast _ (Formalism.HermitianLatticesTheory.fDeg K), ← Real.rpow_mul hF0.le]
  conv_lhs => rw [← Real.rpow_one (discr F : ℝ)]
  congr 1
  first
    | (push_cast; field_simp)
    | (push_cast; field_simp; ring)
    | field_simp
    | (field_simp; ring)

end Formalism.HermitianLattices.Ext.L3
