import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementC
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementK
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedSubfieldCriterionStatement

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM NumberField

noncomputable section

namespace GlobalTheory.NfKur

variable {M : Type} [Field M] [NumberField M] {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `hx : IsIntegral ℤ (φ (a : M))`. Use `map_isIntegral_int φ a.isIntegral_coe` and compare the differences between its conclusion and the goal. Conclude with `Subsingleton.elim _ _`. Establish `h1 : IsIntegral (NormedField.valuation (K` using `ℂ_[l])).integer (φ (a : M)) := hx.tower_top`. Establish `h2` using `(Valuation.integer.integers (NormedField.valuation (K := ℂ_[l]))).mem_of_integral h1`.

Establish `h3 : ‖φ (a : M)‖₊ ≤ 1` using `h2`. Conclude with `h3` after adjusting the coercions.
-/
theorem norm_int_le (φ : M →+* ℂ_[l]) (a : 𝓞 M) : ‖φ (a : M)‖ ≤ 1 := by
  have hx : IsIntegral ℤ (φ (a : M)) := by
    convert map_isIntegral_int φ a.isIntegral_coe; exact Subsingleton.elim _ _
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[l])).integer (φ (a : M)) := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[l]))).mem_of_integral h1
  have h3 : ‖φ (a : M)‖₊ ≤ 1 := h2
  exact_mod_cast h3

def primeAt (φ : M →+* ℂ_[l]) : Ideal (𝓞 M) where
  carrier := {a | ‖φ (a : M)‖ < 1}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  smul_mem' := fun c {a} ha => by
    simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, norm_mul] at ha ⊢
    exact mul_lt_one_of_nonneg_of_lt_one_right (norm_int_le φ c) (norm_nonneg _) ha

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_primeAt (φ : M →+* ℂ_[l]) (a : 𝓞 M) : a ∈ primeAt φ ↔ ‖φ (a : M)‖ < 1 := Iff.rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => le_antisymm (norm_int_le φ a) (not_lt.1 h), fun h h' => absurd h (ne_of_lt h')⟩`.
-/
theorem notMem_primeAt (φ : M →+* ℂ_[l]) (a : 𝓞 M) : a ∉ primeAt φ ↔ ‖φ (a : M)‖ = 1 :=
  ⟨fun h => le_antisymm (norm_int_le φ a) (not_lt.1 h), fun h h' => absurd h (ne_of_lt h')⟩

instance primeAt_isPrime (φ : M →+* ℂ_[l]) : (primeAt φ).IsPrime := by
  refine ⟨(Ideal.ne_top_iff_one _).2 ((notMem_primeAt φ 1).2 (by simp)), fun {a b} hab => ?_⟩
  by_contra hc
  rw [not_or, notMem_primeAt, notMem_primeAt] at hc
  exact (notMem_primeAt φ (a * b)).2 (by simp [hc.1, hc.2]) hab

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem norm_l (φ : M →+* ℂ_[l]) : ‖φ ((l : 𝓞 M) : M)‖ = ‖(l : ℂ_[l])‖ := by simp

/- English proof (translation)
Establish `: (l : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] (l : ℚ_[l])` using `by simp`. Rewrite using `[this, norm_algebraMap']`. Conclude with `Padic.norm_p_lt_one`.
-/
theorem norm_l_lt_one : ‖(l : ℂ_[l])‖ < 1 := by
  have : (l : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] (l : ℚ_[l]) := by simp
  rw [this, norm_algebraMap']
  exact Padic.norm_p_lt_one

/- English proof (translation)
Rewrite using `[mem_primeAt, norm_l]`. Conclude with `norm_l_lt_one`.
-/
theorem l_mem_primeAt (φ : M →+* ℂ_[l]) : (l : 𝓞 M) ∈ primeAt φ := by
  rw [mem_primeAt, norm_l]; exact norm_l_lt_one

/- English proof (translation)
Introduce `h` and use `by have h1 := l_mem_primeAt φ rw [h, Ideal.mem_bot] at h1 exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h1)`.
-/
theorem primeAt_ne_bot (φ : M →+* ℂ_[l]) : primeAt φ ≠ ⊥ := fun h => by
  have h1 := l_mem_primeAt φ
  rw [h, Ideal.mem_bot] at h1
  exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h1)

/- English proof (translation)
Take `⟨n, d, h | h⟩` from `(⟨primeAt φ, inferInstance, primeAt_ne_bot φ⟩ : IsDedekindDomain.HeightOneSpectrum (𝓞 M)).exists_primeCompl_mul_eq_or_mul_eq (K := M) x`. Conclude with `⟨d, n, (notMem_primeAt φ _).1 d.2, by rw [mul_comm]; exact h⟩`. Use `⟨n, d, le_antisymm (norm_int_le φ n) ?_, by rw [mul_comm]; exact h⟩` and prove the remaining obligations. Establish `h1 : ‖φ x‖ * ‖φ (n : M)‖ = 1`. Rewrite using `[← norm_mul, ← map_mul, ← (notMem_primeAt φ _).1 d.2]`.

Conclude with `congrArg (fun y => ‖φ y‖) h`. Use polynomial arithmetic with `[norm_nonneg (φ (n : M)), norm_nonneg (φ x)]`.
-/
theorem exists_denom (φ : M →+* ℂ_[l]) (x : M) (hx : ‖φ x‖ ≤ 1) :
    ∃ s n : 𝓞 M, ‖φ (s : M)‖ = 1 ∧ (s : M) * x = n := by
  obtain ⟨n, d, h | h⟩ := (⟨primeAt φ, inferInstance, primeAt_ne_bot φ⟩ :
    IsDedekindDomain.HeightOneSpectrum (𝓞 M)).exists_primeCompl_mul_eq_or_mul_eq (K := M) x
  · exact ⟨d, n, (notMem_primeAt φ _).1 d.2, by rw [mul_comm]; exact h⟩
  · refine ⟨n, d, le_antisymm (norm_int_le φ n) ?_, by rw [mul_comm]; exact h⟩
    have h1 : ‖φ x‖ * ‖φ (n : M)‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← (notMem_primeAt φ _).1 d.2]
      exact congrArg (fun y => ‖φ y‖) h
    nlinarith [norm_nonneg (φ (n : M)), norm_nonneg (φ x)]

/- English proof (translation)
Establish `hle : Ideal.span {a} ≤ P` using `(Ideal.span_singleton_le_iff_mem _).2 ha`. Take `⟨J, hJ⟩` from `(Ideal.dvd_iff_le).2 hle`. Establish `hJP : ¬ J ≤ P`. Introduce `h`. Apply `hP` to reduce the goal to its premises.

Establish `h1 : a ∈ P * J` using `hJ ▸ Ideal.mem_span_singleton_self a`. Rewrite using `[pow_two]`. Conclude with `Ideal.mul_mono_right h h1`. Take `⟨s, hsJ, hsP⟩` from `SetLike.not_le_iff_exists.1 hJP`. Use `⟨s, hsP, fun b hb => ?_⟩` and prove the remaining obligations.

Establish `: s * b ∈ Ideal.span {a}`. Rewrite using `[hJ, mul_comm s b]`. Conclude with `Ideal.mul_mem_mul hb hsJ`. Conclude with `Ideal.mem_span_singleton.1 this`.
-/
theorem exists_mul_dvd_of_notMem_sq {R : Type} [CommRing R] [IsDedekindDomain R] (P : Ideal R) (a : R)
    (ha : a ∈ P) (hP : a ∉ P ^ 2) : ∃ s : R, s ∉ P ∧ ∀ b ∈ P, a ∣ s * b := by
  have hle : Ideal.span {a} ≤ P := (Ideal.span_singleton_le_iff_mem _).2 ha
  obtain ⟨J, hJ⟩ := (Ideal.dvd_iff_le).2 hle
  have hJP : ¬ J ≤ P := by
    intro h
    apply hP
    have h1 : a ∈ P * J := hJ ▸ Ideal.mem_span_singleton_self a
    rw [pow_two]
    exact Ideal.mul_mono_right h h1
  obtain ⟨s, hsJ, hsP⟩ := SetLike.not_le_iff_exists.1 hJP
  refine ⟨s, hsP, fun b hb => ?_⟩
  have : s * b ∈ Ideal.span {a} := by
    rw [hJ, mul_comm s b]; exact Ideal.mul_mem_mul hb hsJ
  exact Ideal.mem_span_singleton.1 this

/- English proof (translation)
Take `⟨t, n, ht, hn⟩` from `exists_denom φ x hx.le`. Establish `hnx : ‖φ (n : M)‖ = ‖φ x‖` using `by rw [← hn, map_mul, norm_mul, ht, one_mul]`. Take `⟨s, hs, hdvd⟩` from `exists_mul_dvd_of_notMem_sq _ _ (l_mem_primeAt φ) hP`. Take `⟨c, hc⟩` from `hdvd n ((mem_primeAt φ n).2 (hnx ▸ hx))`. Establish `hs1` using `(notMem_primeAt φ s).1 hs`.

Establish `h1 : ‖φ (n : M)‖ = ‖(l : ℂ_[l])‖ * ‖φ (c : M)‖`. Use `congrArg (fun y : 𝓞 M => ‖φ (y : M)‖) hc` as an intermediate fact. Simplify using `only [map_mul, norm_mul, hs1, one_mul] at this`. Rewrite using `[this]`. Simplify using the standard rewrite rules.

Rewrite using `[← hnx, h1]`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) (norm_int_le φ c)`.
-/
theorem norm_le_of_lt_one (φ : M →+* ℂ_[l]) (hP : (l : 𝓞 M) ∉ primeAt φ ^ 2) (x : M) (hx : ‖φ x‖ < 1) :
    ‖φ x‖ ≤ ‖(l : ℂ_[l])‖ := by
  obtain ⟨t, n, ht, hn⟩ := exists_denom φ x hx.le
  have hnx : ‖φ (n : M)‖ = ‖φ x‖ := by rw [← hn, map_mul, norm_mul, ht, one_mul]
  obtain ⟨s, hs, hdvd⟩ := exists_mul_dvd_of_notMem_sq _ _ (l_mem_primeAt φ) hP
  obtain ⟨c, hc⟩ := hdvd n ((mem_primeAt φ n).2 (hnx ▸ hx))
  have hs1 := (notMem_primeAt φ s).1 hs
  have h1 : ‖φ (n : M)‖ = ‖(l : ℂ_[l])‖ * ‖φ (c : M)‖ := by
    have := congrArg (fun y : 𝓞 M => ‖φ (y : M)‖) hc
    simp only [map_mul, norm_mul, hs1, one_mul] at this
    rw [this]; simp
  rw [← hnx, h1]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_int_le φ c)

/- English proof (translation)
Use `haveI : P.IsMaximal := hP.isMaximal h0`. Use `letI : Field (𝓞 M ⧸ P) := Ideal.Quotient.field P`. Use `haveI : Finite (𝓞 M ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P h0`. Use `letI : Fintype (𝓞 M ⧸ P) := Fintype.ofFinite _`. Establish `hl0 : (l : 𝓞 M ⧸ P) = 0`.

Rewrite using `[← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hl`. Use `haveI : CharP (𝓞 M ⧸ P) l := (CharP.charP_iff_prime_eq_zero Fact.out).2 hl0`. Take `⟨N, -, hN⟩` from `FiniteField.card (𝓞 M ⧸ P) l`. Use `⟨N, N.pos, fun s n hs => ?_⟩` and prove the remaining obligations.

Establish `hs0 : Ideal.Quotient.mk P s ≠ 0` using `fun h => hs (Ideal.Quotient.eq_zero_iff_mem.1 h)`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_pow, map_pow, ← hN, FiniteField.pow_card, FiniteField.pow_card_sub_one_eq_one _ hs0, one_mul, sub_self]`.
-/
theorem exists_pow_mem (P : Ideal (𝓞 M)) [hP : P.IsPrime] (h0 : P ≠ ⊥) (hl : (l : 𝓞 M) ∈ P) :
    ∃ N : ℕ, 0 < N ∧ ∀ s n : 𝓞 M, s ∉ P → n ^ (l ^ N) - s ^ (l ^ N - 1) * n ∈ P := by
  classical
  haveI : P.IsMaximal := hP.isMaximal h0
  letI : Field (𝓞 M ⧸ P) := Ideal.Quotient.field P
  haveI : Finite (𝓞 M ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P h0
  letI : Fintype (𝓞 M ⧸ P) := Fintype.ofFinite _
  have hl0 : (l : 𝓞 M ⧸ P) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]; exact hl
  haveI : CharP (𝓞 M ⧸ P) l := (CharP.charP_iff_prime_eq_zero Fact.out).2 hl0
  obtain ⟨N, -, hN⟩ := FiniteField.card (𝓞 M ⧸ P) l
  refine ⟨N, N.pos, fun s n hs => ?_⟩
  have hs0 : Ideal.Quotient.mk P s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.1 h)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_pow, map_pow, ← hN, FiniteField.pow_card,
    FiniteField.pow_card_sub_one_eq_one _ hs0, one_mul, sub_self]

/- English proof (translation)
Take `⟨N, hN, h⟩` from `exists_pow_mem (primeAt φ) (primeAt_ne_bot φ) (l_mem_primeAt φ)`. Use `⟨N, hN, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨s, n, hs, hn⟩` from `exists_denom φ x hx`. Establish `h1` using `(mem_primeAt φ _).1 (h s n ((notMem_primeAt φ s).2 hs))`. Establish `hq : l ^ N ≠ 0` using `pow_ne_zero _ (Fact.out : l.Prime).ne_zero`.

Establish `hn' : φ (n : M) = φ (s : M) * φ x` using `by rw [← hn, map_mul]`. Establish `h2 : φ ((n ^ (l ^ N) - s ^ (l ^ N - 1) * n : 𝓞 M) : M) = φ (s : M) ^ (l ^ N) * (φ x ^ (l ^ N) - φ x)`. Establish `h3 : φ ((n ^ (l ^ N) - s ^ (l ^ N - 1) * n : 𝓞 M) : M) = φ (n : M) ^ (l ^ N) - φ (s : M) ^ (l ^ N - 1) * φ (n : M)` using `by simp`. Rewrite using `[h3, hn', ← mul_assoc, pow_sub_one_mul hq, mul_pow, mul_sub]`. Rewrite `h1` using `[h2, norm_mul, norm_pow, hs, one_pow, one_mul]`. Then use the resulting hypothesis.
-/
theorem exists_norm_pow_sub (φ : M →+* ℂ_[l]) :
    ∃ N : ℕ, 0 < N ∧ ∀ x : M, ‖φ x‖ ≤ 1 → ‖φ x ^ (l ^ N) - φ x‖ < 1 := by
  obtain ⟨N, hN, h⟩ := exists_pow_mem (primeAt φ) (primeAt_ne_bot φ) (l_mem_primeAt φ)
  refine ⟨N, hN, fun x hx => ?_⟩
  obtain ⟨s, n, hs, hn⟩ := exists_denom φ x hx
  have h1 := (mem_primeAt φ _).1 (h s n ((notMem_primeAt φ s).2 hs))
  have hq : l ^ N ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have hn' : φ (n : M) = φ (s : M) * φ x := by rw [← hn, map_mul]
  have h2 : φ ((n ^ (l ^ N) - s ^ (l ^ N - 1) * n : 𝓞 M) : M)
      = φ (s : M) ^ (l ^ N) * (φ x ^ (l ^ N) - φ x) := by
    have h3 : φ ((n ^ (l ^ N) - s ^ (l ^ N - 1) * n : 𝓞 M) : M)
        = φ (n : M) ^ (l ^ N) - φ (s : M) ^ (l ^ N - 1) * φ (n : M) := by simp
    rw [h3, hn', ← mul_assoc, pow_sub_one_mul hq, mul_pow, mul_sub]
  rwa [h2, norm_mul, norm_pow, hs, one_pow, one_mul] at h1

/- English proof (translation)
Introduce `M _ _ l _ hM φ x`. Take `⟨N, hN, h⟩` from `exists_norm_pow_sub φ`. Establish `hP` using `hM (primeAt φ) inferInstance (l_mem_primeAt φ)`. Use `GlobalTheory.T.unramified_subfield_criterion l φ.fieldRange N hN ?_ ?_ (φ.mem_fieldRange_self x)` and prove the remaining obligations. Introduce and unpack `_ ⟨y, rfl⟩ hy`.

Conclude with `norm_le_of_lt_one φ hP y hy`. Introduce and unpack `_ ⟨y, rfl⟩ hy`. Conclude with `h y hy`.
-/
theorem map_mem_Kur : ∀ (M : Type) [Field M] [NumberField M] (l : ℕ) [Fact l.Prime],
    (∀ P : Ideal (𝓞 M), P.IsPrime → (l : 𝓞 M) ∈ P → (l : 𝓞 M) ∉ P ^ 2) →
      ∀ (φ : M →+* ℂ_[l]) (x : M), φ x ∈ MaximalUnramifiedExtension l := by
  intro M _ _ l _ hM φ x
  obtain ⟨N, hN, h⟩ := exists_norm_pow_sub φ
  have hP := hM (primeAt φ) inferInstance (l_mem_primeAt φ)
  refine GlobalTheory.T.unramified_subfield_criterion l φ.fieldRange N hN ?_ ?_ (φ.mem_fieldRange_self x)
  · rintro _ ⟨y, rfl⟩ hy
    exact norm_le_of_lt_one φ hP y hy
  · rintro _ ⟨y, rfl⟩ hy
    exact h y hy

end GlobalTheory.NfKur
