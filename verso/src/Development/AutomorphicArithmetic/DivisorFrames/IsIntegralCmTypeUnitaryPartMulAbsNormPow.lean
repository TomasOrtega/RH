import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.CharProd

open NumberField IsDedekindDomain

/- English proof (translation)
Establish `hbk : ∀ k : ℕ, b ^ k * b⁻¹ ^ k = 1` using `fun k => by rw [← mul_pow, mul_inv_cancel₀ hb0, one_pow]`. Establish `hak : ∀ k : ℕ, a ^ k * a⁻¹ ^ k = 1` using `fun k => by rw [← mul_pow, mul_inv_cancel₀ ha0, one_pow]`. Take `⟨k, rfl | rfl⟩` from `Int.eq_nat_or_neg n`. Simplify using `only [Int.natAbs_natCast] at hn`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hn`.

Establish `e : (a / b) ^ (k : ℤ) * (a * b) ^ (k + d) = a ^ (k + k + d) * b ^ d * (b ^ k * b⁻¹ ^ k)`. Rewrite using `[zpow_natCast, div_eq_mul_inv]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, hbk, mul_one]`. Conclude with `(ha.pow _).mul (hb.pow _)`.

Simplify using `only [Int.natAbs_neg, Int.natAbs_natCast] at hn`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hn`. Establish `e : (a / b) ^ (-(k : ℤ)) * (a * b) ^ (k + d) = a ^ d * b ^ (k + k + d) * (a ^ k * a⁻¹ ^ k)`. Rewrite using `[zpow_neg, ← inv_zpow, inv_div, zpow_natCast, div_eq_mul_inv]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, hak, mul_one]`. Conclude with `(ha.pow _).mul (hb.pow _)`.
-/
private lemma isIntegral_pow_div_mul_pow (a b : ℂ) (ha : IsIntegral ℤ a) (hb : IsIntegral ℤ b) (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) (n : ℤ) (M : ℕ) (hn : n.natAbs ≤ M) :
    IsIntegral ℤ ((a / b) ^ n * (a * b) ^ M) := by
  have hbk : ∀ k : ℕ, b ^ k * b⁻¹ ^ k = 1 := fun k => by rw [← mul_pow, mul_inv_cancel₀ hb0, one_pow]
  have hak : ∀ k : ℕ, a ^ k * a⁻¹ ^ k = 1 := fun k => by rw [← mul_pow, mul_inv_cancel₀ ha0, one_pow]
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simp only [Int.natAbs_natCast] at hn
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
    have e : (a / b) ^ (k : ℤ) * (a * b) ^ (k + d) = a ^ (k + k + d) * b ^ d * (b ^ k * b⁻¹ ^ k) := by
      rw [zpow_natCast, div_eq_mul_inv]
      ring
    rw [e, hbk, mul_one]
    exact (ha.pow _).mul (hb.pow _)
  · simp only [Int.natAbs_neg, Int.natAbs_natCast] at hn
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
    have e : (a / b) ^ (-(k : ℤ)) * (a * b) ^ (k + d) = a ^ d * b ^ (k + k + d) * (a ^ k * a⁻¹ ^ k) := by
      rw [zpow_neg, ← inv_zpow, inv_div, zpow_natCast, div_eq_mul_inv]
      ring
    rw [e, hak, mul_one]
    exact (ha.pow _).mul (hb.pow _)

/- English proof (translation)
Establish `hn : ((‖a‖ : ℝ) : ℂ) ≠ 0`. Rewrite using `[Ne, Complex.ofReal_eq_zero, norm_eq_zero]`. Conclude with `ha0`. Establish `hc : (starRingEnd ℂ) a ≠ 0` using `(map_ne_zero _).mpr ha0`. Rewrite using `[div_pow, ← Complex.mul_conj' a]`.

Clear the denominators using the available nonvanishing facts.
-/
private lemma div_abs_sq_eq_div_conj (a : ℂ) (ha0 : a ≠ 0) :
    (a / ((‖a‖ : ℝ) : ℂ)) ^ 2 = a / (starRingEnd ℂ) a := by
  have hn : ((‖a‖ : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero, norm_eq_zero]
    exact ha0
  have hc : (starRingEnd ℂ) a ≠ 0 := (map_ne_zero _).mpr ha0
  rw [div_pow, ← Complex.mul_conj' a]
  field_simp

/- English proof (translation)
Establish `h1' : P.intValuation a = WithZero.exp (-(h : ℤ))`. Rewrite using `[← HeightOneSpectrum.valuation_of_algebraMap (K := E)]`. Conclude with `h1`. Establish `h2' : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → Q.intValuation a = 1`. Introduce `Q hQ`.

Rewrite using `[← HeightOneSpectrum.valuation_of_algebraMap (K := E)]`. Conclude with `h2 Q hQ`. Take `⟨J, hJ⟩` from `(P.intValuation_le_pow_iff_dvd a h).mp h1'.le`. Rewrite using `[hJ]`. It suffices to establish `hJt : J = ⊤ by rw [hJt, Ideal.mul_top]`.

Assume the negation of the conclusion as `hne`. Take `⟨M, hM, hJM⟩` from `Ideal.exists_le_maximal J hne`. Establish `hspan0 : Ideal.span {a} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `ha`.

Establish `hJ0 : J ≠ ⊥`. Introduce and unpack `rfl`. Rewrite `hJ` using `[Ideal.mul_bot]`. Conclude with `hspan0 hJ`. Establish `hM0 : M ≠ ⊥` using `fun hb => hJ0 (le_bot_iff.mp (hb ▸ hJM))`.

Set `Q : HeightOneSpectrum (𝓞 E)` to `⟨M, hM.isPrime, hM0⟩`. Establish `hQJ : Q.asIdeal ∣ J` using `Ideal.dvd_iff_le.mpr hJM`. Distinguish the cases in `hQP : Q = P`. Establish `hPJ : P.asIdeal ∣ J` using `hQP ▸ hQJ`. Establish `hdvd : P.asIdeal ^ (h + 1) ∣ Ideal.span {a}`.

Rewrite using `[hJ, pow_succ]`. Conclude with `mul_dvd_mul_left _ hPJ`. Establish `hv` using `(P.intValuation_le_pow_iff_dvd a (h + 1)).mpr hdvd`. Rewrite `hv` using `[h1', WithZero.exp_le_exp]`. Move the coercions through the operations in `at hv`.

Use linear arithmetic over natural numbers and integers. Establish `hlt : Q.intValuation a < 1`. Rewrite using `[Q.intValuation_lt_one_iff_dvd, hJ]`. Conclude with `dvd_mul_of_dvd_right hQJ _`. Rewrite `hlt` using `[h2' Q hQP]`.

Conclude with `lt_irrefl _ hlt`.
-/
private lemma span_eq_pow_of_valuation_supported_at (E : Type) [Field E] [NumberField E]
    (P : HeightOneSpectrum (𝓞 E)) (h : ℕ) (a : 𝓞 E) (ha : a ≠ 0)
    (h1 : P.valuation E (a : E) = WithZero.exp (-(h : ℤ)))
    (h2 : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → Q.valuation E (a : E) = 1) :
    Ideal.span {a} = P.asIdeal ^ h := by
  have h1' : P.intValuation a = WithZero.exp (-(h : ℤ)) := by
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := E)]
    exact h1
  have h2' : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → Q.intValuation a = 1 := by
    intro Q hQ
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := E)]
    exact h2 Q hQ
  obtain ⟨J, hJ⟩ := (P.intValuation_le_pow_iff_dvd a h).mp h1'.le
  rw [hJ]
  suffices hJt : J = ⊤ by rw [hJt, Ideal.mul_top]
  by_contra hne
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hne
  have hspan0 : Ideal.span {a} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact ha
  have hJ0 : J ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot] at hJ
    exact hspan0 hJ
  have hM0 : M ≠ ⊥ := fun hb => hJ0 (le_bot_iff.mp (hb ▸ hJM))
  let Q : HeightOneSpectrum (𝓞 E) := ⟨M, hM.isPrime, hM0⟩
  have hQJ : Q.asIdeal ∣ J := Ideal.dvd_iff_le.mpr hJM
  by_cases hQP : Q = P
  · have hPJ : P.asIdeal ∣ J := hQP ▸ hQJ
    have hdvd : P.asIdeal ^ (h + 1) ∣ Ideal.span {a} := by
      rw [hJ, pow_succ]
      exact mul_dvd_mul_left _ hPJ
    have hv := (P.intValuation_le_pow_iff_dvd a (h + 1)).mpr hdvd
    rw [h1', WithZero.exp_le_exp] at hv
    push_cast at hv
    omega
  · have hlt : Q.intValuation a < 1 := by
      rw [Q.intValuation_lt_one_iff_dvd, hJ]
      exact dvd_mul_of_dvd_right hQJ _
    rw [h2' Q hQP] at hlt
    exact lt_irrefl _ hlt

/- English proof (translation)
Rewrite using `[Ideal.absNorm_span_singleton]`. Establish `h1 : ((((Algebra.norm ℤ) a).natAbs : ℕ) : ℂ) ^ 2 = (((Algebra.norm ℤ a : ℤ)) : ℂ) ^ 2`. Rewrite using `[← Int.cast_natCast, ← Int.cast_pow, Int.natAbs_sq, Int.cast_pow]`. Rewrite using `[h1]`. Use `congr 1`.

Establish `h2 : (((Algebra.norm ℤ a : ℤ)) : ℂ) = algebraMap ℚ ℂ (Algebra.norm ℚ (a : E))`. Rewrite using `[← Algebra.coe_norm_int]`. Simplify using the standard rewrite rules. Rewrite using `[h2, Algebra.norm_eq_prod_embeddings ℚ ℂ]`. Conclude with `Fintype.prod_equiv (RingHom.equivRatAlgHom (R := E) (S := ℂ)).symm _ _ (fun σ => rfl)`.
-/
private lemma absNorm_span_sq_eq_prod_embeddings_sq (E : Type) [Field E] [NumberField E] (a : 𝓞 E) :
    ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℂ) ^ 2 = (∏ σ : E →+* ℂ, σ (a : E)) ^ 2 := by
  rw [Ideal.absNorm_span_singleton]
  have h1 : ((((Algebra.norm ℤ) a).natAbs : ℕ) : ℂ) ^ 2 = (((Algebra.norm ℤ a : ℤ)) : ℂ) ^ 2 := by
    rw [← Int.cast_natCast, ← Int.cast_pow, Int.natAbs_sq, Int.cast_pow]
  rw [h1]
  congr 1
  have h2 : (((Algebra.norm ℤ a : ℤ)) : ℂ) = algebraMap ℚ ℂ (Algebra.norm ℚ (a : E)) := by
    rw [← Algebra.coe_norm_int]
    simp
  rw [h2, Algebra.norm_eq_prod_embeddings ℚ ℂ]
  exact Fintype.prod_equiv (RingHom.equivRatAlgHom (R := E) (S := ℂ)).symm _ _ (fun σ => rfl)

/- English proof (translation)
Introduce `E _ _ I _ φ hinj n M hn P h z hP hQ`. Establish `hle : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E (z : E) ≤ 1`. Introduce `v`. Distinguish the cases in `hv : v = P`. Substitute `hv` using the available equality.

Rewrite using `[hP, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hQ v hv]`. Take `⟨a, ha⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one E (z : E) hle`. Establish `hza : (z : E) = (a : E)` using `ha.symm`.

Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Rewrite `ha` using `[map_zero]`. Conclude with `z.ne_zero ha.symm`. Establish `hspan` using `span_eq_pow_of_valuation_supported_at E P h a ha0 (by rw [← hza]; exact hP) (fun Q hQP => by rw [← hza]; exact hQ Q hQP)`.

Establish `hnorm : ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (2 * h) = (∏ σ : E →+* ℂ, σ (a : E)) ^ 2`. Rewrite using `[← absNorm_span_sq_eq_prod_embeddings_sq E a, hspan, map_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `haE : (a : E) ≠ 0` using `hza ▸ z.ne_zero`.

Establish `hint : ∀ σ : E →+* ℂ, IsIntegral ℤ (σ (a : E))` using `fun σ => (RingOfIntegers.isIntegral_coe a).map σ.toIntAlgHom`. Establish `hw0 : ∀ i, φ i (a : E) ≠ 0` using `fun i => (map_ne_zero _).mpr haE`. Establish `hwc0 : ∀ i, (starRingEnd ℂ) (φ i (a : E)) ≠ 0` using `fun i => (map_ne_zero _).mpr (hw0 i)`. Establish `hzp : ∀ (x : ℂ) (k : ℤ), (x ^ k) ^ 2 = (x ^ 2) ^ k` using `fun x k => by`. Rewrite using `[← zpow_natCast, ← zpow_natCast x, ← zpow_mul, ← zpow_mul, mul_comm]`.

Rewrite using `[hza]`. Apply `IsIntegral.of_pow (n := 2) two_pos` to reduce the goal to its premises. Establish `e1 : ((∏ i, (φ i (a : E) / ((‖φ i (a : E)‖ : ℝ) : ℂ)) ^ n i) * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (h * M)) ^ 2 = (∏ i, (φ i (a : E) / (starRingEnd ℂ) (φ i (a : E))) ^ n i) * ((∏ σ : E →+* ℂ, σ (a : E)) ^ 2) ^ M`. Rewrite using `[mul_pow, ← Finset.prod_pow, ← hnorm]`. Use `congr 1`.

Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[hzp, div_abs_sq_eq_div_conj _ (hw0 i)]`. Expand and normalize the polynomial expressions, which then agree. Set `e : I ⊕ I ↪ (E →+* ℂ)` to `⟨Sum.elim φ (fun i => ComplexEmbedding.conjugate (φ i)), hinj⟩`.

Establish `hsplit : ∏ σ : E →+* ℂ, σ (a : E) = (∏ i, φ i (a : E) * (starRingEnd ℂ) (φ i (a : E))) * ∏ σ ∈ Finset.univ \ Finset.univ.map e, σ (a : E)`. Rewrite using `[← Finset.prod_sdiff (Finset.subset_univ (Finset.univ.map e)), Finset.prod_map, Fintype.prod_sum_type, ← Finset.prod_mul_distrib, mul_comm]`. Both sides reduce to the same expression. Rewrite using `[e1, hsplit]`. Establish `e2 : (∏ i, (φ i (a : E) / (starRingEnd ℂ) (φ i (a : E))) ^ n i) * (((∏ i, φ i (a : E) * (starRingEnd ℂ) (φ i (a : E))) * ∏ σ ∈ Finset.univ \ Finset.univ.map e, σ (a : E)) ^ 2) ^ M = (∏ i, (φ i (a : E) / (starRingEnd ℂ) (φ i (a : E))) ^ n i * (φ i (a : E) * (starRingEnd ℂ) (φ i (a …`.

Simplify using `only [Finset.prod_mul_distrib, Finset.prod_pow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`. Apply `IsIntegral.mul` to reduce the goal to its premises. Apply `IsIntegral.prod` to reduce the goal to its premises.

Introduce `i _`. Conclude with `isIntegral_pow_div_mul_pow _ _ (hint (φ i)) (hint (ComplexEmbedding.conjugate (φ i))) (hw0 i) (hwc0 i) (n i) (2 * M) (by have := hn i; omega)`. Apply `IsIntegral.pow` to reduce the goal to its premises. Apply `IsIntegral.prod` to reduce the goal to its premises. Introduce `σ _`.

Conclude with `hint σ`.
-/
theorem UpperTheory.isIntegral_cmType_unitaryPart_mul_absNorm_pow :
    ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), Function.Injective (Sum.elim φ fun i => ComplexEmbedding.conjugate (φ i)) → ∀ (n : I → ℤ) (M : ℕ), (∀ i, (n i).natAbs ≤ M) → ∀ (P : HeightOneSpectrum (𝓞 E)) (h : ℕ) (z : Eˣ), P.valuation E (z : E) = WithZero.exp (-(h : ℤ)) → (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → Q.valuation E (z : E) = 1) → IsIntegral ℤ ((∏ i, (φ i (z : E) / ((‖φ i (z : E)‖ : ℝ) : ℂ)) ^ n i) * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (h * M)) := by
  intro E _ _ I _ φ hinj n M hn P h z hP hQ
  classical
  have hle : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E (z : E) ≤ 1 := by
    intro v
    by_cases hv : v = P
    · subst hv
      rw [hP, ← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    · rw [hQ v hv]
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E (z : E) hle
  have hza : (z : E) = (a : E) := ha.symm
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact z.ne_zero ha.symm
  have hspan := span_eq_pow_of_valuation_supported_at E P h a ha0 (by rw [← hza]; exact hP) (fun Q hQP => by rw [← hza]; exact hQ Q hQP)
  have hnorm : ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (2 * h) = (∏ σ : E →+* ℂ, σ (a : E)) ^ 2 := by
    rw [← absNorm_span_sq_eq_prod_embeddings_sq E a, hspan, map_pow]
    push_cast
    ring
  have haE : (a : E) ≠ 0 := hza ▸ z.ne_zero
  have hint : ∀ σ : E →+* ℂ, IsIntegral ℤ (σ (a : E)) := fun σ =>
    (RingOfIntegers.isIntegral_coe a).map σ.toIntAlgHom
  have hw0 : ∀ i, φ i (a : E) ≠ 0 := fun i => (map_ne_zero _).mpr haE
  have hwc0 : ∀ i, (starRingEnd ℂ) (φ i (a : E)) ≠ 0 := fun i => (map_ne_zero _).mpr (hw0 i)
  have hzp : ∀ (x : ℂ) (k : ℤ), (x ^ k) ^ 2 = (x ^ 2) ^ k := fun x k => by
    rw [← zpow_natCast, ← zpow_natCast x, ← zpow_mul, ← zpow_mul, mul_comm]
  rw [hza]
  apply IsIntegral.of_pow (n := 2) two_pos
  have e1 : ((∏ i, (φ i (a : E) / ((‖φ i (a : E)‖ : ℝ) : ℂ)) ^ n i) * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (h * M)) ^ 2
      = (∏ i, (φ i (a : E) / (starRingEnd ℂ) (φ i (a : E))) ^ n i) * ((∏ σ : E →+* ℂ, σ (a : E)) ^ 2) ^ M := by
    rw [mul_pow, ← Finset.prod_pow, ← hnorm]
    congr 1
    · apply Finset.prod_congr rfl
      intro i _
      rw [hzp, div_abs_sq_eq_div_conj _ (hw0 i)]
    · ring
  let e : I ⊕ I ↪ (E →+* ℂ) := ⟨Sum.elim φ (fun i => ComplexEmbedding.conjugate (φ i)), hinj⟩
  have hsplit : ∏ σ : E →+* ℂ, σ (a : E)
      = (∏ i, φ i (a : E) * (starRingEnd ℂ) (φ i (a : E))) * ∏ σ ∈ Finset.univ \ Finset.univ.map e, σ (a : E) := by
    rw [← Finset.prod_sdiff (Finset.subset_univ (Finset.univ.map e)), Finset.prod_map, Fintype.prod_sum_type,
      ← Finset.prod_mul_distrib, mul_comm]
    rfl
  rw [e1, hsplit]
  have e2 : (∏ i, (φ i (a : E) / (starRingEnd ℂ) (φ i (a : E))) ^ n i) *
      (((∏ i, φ i (a : E) * (starRingEnd ℂ) (φ i (a : E))) * ∏ σ ∈ Finset.univ \ Finset.univ.map e, σ (a : E)) ^ 2) ^ M
      = (∏ i, (φ i (a : E) / (starRingEnd ℂ) (φ i (a : E))) ^ n i * (φ i (a : E) * (starRingEnd ℂ) (φ i (a : E))) ^ (2 * M))
        * (∏ σ ∈ Finset.univ \ Finset.univ.map e, σ (a : E)) ^ (2 * M) := by
    simp only [Finset.prod_mul_distrib, Finset.prod_pow]
    ring
  rw [e2]
  apply IsIntegral.mul
  · apply IsIntegral.prod
    intro i _
    exact isIntegral_pow_div_mul_pow _ _ (hint (φ i)) (hint (ComplexEmbedding.conjugate (φ i))) (hw0 i) (hwc0 i) (n i) (2 * M)
      (by have := hn i; omega)
  · apply IsIntegral.pow
    apply IsIntegral.prod
    intro σ _
    exact hint σ
