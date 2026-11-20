import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeMemHeightOneSpectrum

open NumberField IsDedekindDomain

namespace GlobalTheory.Mem.FewPrimes

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Establish `h1 : ∏ v ∈ s, v.asIdeal ∣ I` using `Finset.prod_dvd_of_coprime (fun a _ b _ hab => HeightOneSpectrum.isCoprime_of_ne _ _ hab) h`. Rewrite using `[← map_prod]`. Conclude with `map_dvd _ h1`.
-/
theorem prod_absNorm_dvd (s : Finset (HeightOneSpectrum (𝓞 K))) (I : Ideal (𝓞 K))
    (h : ∀ v ∈ s, v.asIdeal ∣ I) :
    ∏ v ∈ s, Ideal.absNorm v.asIdeal ∣ Ideal.absNorm I := by
  have h1 : ∏ v ∈ s, v.asIdeal ∣ I :=
    Finset.prod_dvd_of_coprime
      (fun a _ b _ hab => HeightOneSpectrum.isCoprime_of_ne _ _ hab) h
  rw [← map_prod]
  exact map_dvd _ h1

/- English proof (translation)
Establish `h` using `Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊X⌋₊`. Establish `h2` using `h.preimage (f := fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal) (fun a _ b _ hab => HeightOneSpectrum.ext hab)`. Use `h2.subset ?_` and prove the remaining obligations. Introduce `v hv`. Conclude with `Nat.le_floor hv`.
-/
theorem finite_absNorm_le (X : ℝ) :
    {v : HeightOneSpectrum (𝓞 K) | (Ideal.absNorm v.asIdeal : ℝ) ≤ X}.Finite := by
  have h := Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊X⌋₊
  have h2 := h.preimage (f := fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal)
    (fun a _ b _ hab => HeightOneSpectrum.ext hab)
  refine h2.subset ?_
  intro v hv
  exact Nat.le_floor hv

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.PrimeInHeightOneSpectrum.target`. Consider the case `exact _root_.GlobalTheory.PrimeInHeightOneSpectrum.target`. Consider the case `(apply _root_.GlobalTheory.PrimeInHeightOneSpectrum.target <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.PrimeInHeightOneSpectrum.target <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.PrimeInHeightOneSpectrum.target <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.PrimeInHeightOneSpectrum.target ..)`.
-/
theorem exists_prime_mem (v : HeightOneSpectrum (𝓞 K)) :
    ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ v.asIdeal := by
  first
  | exact @_root_.GlobalTheory.PrimeInHeightOneSpectrum.target
  | exact _root_.GlobalTheory.PrimeInHeightOneSpectrum.target
  | (apply _root_.GlobalTheory.PrimeInHeightOneSpectrum.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimeInHeightOneSpectrum.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimeInHeightOneSpectrum.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimeInHeightOneSpectrum.target ..)

/- English proof (translation)
Take `⟨p, hp, hm⟩` from `exists_prime_mem v`. Establish `hd : v.asIdeal ∣ Ideal.span {(p : 𝓞 K)}` using `Ideal.dvd_span_singleton.2 hm`. Establish `hN : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ 2`. Rewrite using `[Ideal.absNorm_span_natCast, RingOfIntegers.rank, hK]`. Establish `h1` using `NumberField.HeightOneSpectrum.one_lt_absNorm v`.

Establish `h2 : Ideal.absNorm v.asIdeal ∣ p ^ 2` using `hN ▸ map_dvd _ hd`. Take `⟨i, hi, he⟩` from `(Nat.dvd_prime_pow hp).1 h2`. Establish `h3 : Ideal.absNorm v.asIdeal = p ^ 2` using `by interval_cases i`. Rewrite `he` using `[pow_zero]`. Conclude with `absurd he h1.ne'`.

Rewrite `he` using `[pow_one]`. Conclude with `absurd (he ▸ hp) hv`. Conclude with `he`. Use `⟨p, hp, ?_, h3⟩` and prove the remaining obligations. Take `⟨J, hJ⟩` from `hd`.

Establish `h4 : Ideal.absNorm J = 1`. Establish `h5` using `hN`. Rewrite `h5` using `[hJ, map_mul, h3]`. Conclude with `Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) (by rw [h5, mul_one])`. Rewrite `h4` using `[Ideal.absNorm_eq_one_iff]`.

Rewrite using `[hJ, h4, Ideal.mul_top]`.
-/
theorem exists_eq_span (hK : Module.finrank ℚ K = 2) (v : HeightOneSpectrum (𝓞 K))
    (hv : ¬ (Ideal.absNorm v.asIdeal).Prime) :
    ∃ p : ℕ, p.Prime ∧ v.asIdeal = Ideal.span {(p : 𝓞 K)} ∧ Ideal.absNorm v.asIdeal = p ^ 2 := by
  obtain ⟨p, hp, hm⟩ := exists_prime_mem v
  have hd : v.asIdeal ∣ Ideal.span {(p : 𝓞 K)} := Ideal.dvd_span_singleton.2 hm
  have hN : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, hK]
  have h1 := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have h2 : Ideal.absNorm v.asIdeal ∣ p ^ 2 := hN ▸ map_dvd _ hd
  obtain ⟨i, hi, he⟩ := (Nat.dvd_prime_pow hp).1 h2
  have h3 : Ideal.absNorm v.asIdeal = p ^ 2 := by
    interval_cases i
    · rw [pow_zero] at he; exact absurd he h1.ne'
    · rw [pow_one] at he; exact absurd (he ▸ hp) hv
    · exact he
  refine ⟨p, hp, ?_, h3⟩
  obtain ⟨J, hJ⟩ := hd
  have h4 : Ideal.absNorm J = 1 := by
    have h5 := hN
    rw [hJ, map_mul, h3] at h5
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) (by rw [h5, mul_one])
  rw [Ideal.absNorm_eq_one_iff] at h4
  rw [hJ, h4, Ideal.mul_top]

/- English proof (translation)
Establish `h : {v : HeightOneSpectrum (𝓞 K) | (Ideal.absNorm v.asIdeal : ℝ) ≤ X ∧ ¬ (Ideal.absNorm v.asIdeal).Prime}.ncard ≤ ((Finset.Icc 1 ⌊Real.sqrt X⌋₊ : Finset ℕ) : Set ℕ).ncard`. Use `Set.ncard_le_ncard_of_injOn (fun v => Nat.sqrt (Ideal.absNorm v.asIdeal)) ?_ ?_ (Finset.finite_toSet _)` and prove the remaining obligations. Introduce and unpack `v ⟨hX, hv⟩`. Take `⟨p, hp, -, h3⟩` from `exists_eq_span hK v hv`. Rewrite `hX` using `[h3]`.

Simplify using `only [h3, Nat.sqrt_eq', Finset.coe_Icc, Set.mem_Icc]`. Use `⟨hp.pos, Nat.le_floor ?_⟩` and prove the remaining obligations. Apply `Real.le_sqrt_of_sq_le` to reduce the goal to its premises. Conclude with `hX` after adjusting the coercions. Introduce and unpack `v ⟨-, hv⟩ w ⟨-, hw⟩ hvw`.

Take `⟨p, hp, e1, h3⟩` from `exists_eq_span hK v hv`. Take `⟨q, hq, e2, h4⟩` from `exists_eq_span hK w hw`. Simplify using `only [h3, h4, Nat.sqrt_eq'] at hvw`. Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Rewrite using `[e1, e2, hvw]`.

Rewrite `h` using `[Set.ncard_coe_finset, Nat.card_Icc, Nat.add_sub_cancel]`. Conclude with `le_trans (by exact_mod_cast h) (Nat.floor_le (Real.sqrt_nonneg X))`.
-/
theorem ncard_not_prime_le (hK : Module.finrank ℚ K = 2) (X : ℝ) :
    ({v : HeightOneSpectrum (𝓞 K) | (Ideal.absNorm v.asIdeal : ℝ) ≤ X ∧
      ¬ (Ideal.absNorm v.asIdeal).Prime}.ncard : ℝ) ≤ Real.sqrt X := by
  have h : {v : HeightOneSpectrum (𝓞 K) | (Ideal.absNorm v.asIdeal : ℝ) ≤ X ∧
      ¬ (Ideal.absNorm v.asIdeal).Prime}.ncard ≤
      ((Finset.Icc 1 ⌊Real.sqrt X⌋₊ : Finset ℕ) : Set ℕ).ncard := by
    refine Set.ncard_le_ncard_of_injOn (fun v => Nat.sqrt (Ideal.absNorm v.asIdeal)) ?_ ?_
      (Finset.finite_toSet _)
    · rintro v ⟨hX, hv⟩
      obtain ⟨p, hp, -, h3⟩ := exists_eq_span hK v hv
      rw [h3] at hX
      simp only [h3, Nat.sqrt_eq', Finset.coe_Icc, Set.mem_Icc]
      refine ⟨hp.pos, Nat.le_floor ?_⟩
      apply Real.le_sqrt_of_sq_le
      exact_mod_cast hX
    · rintro v ⟨-, hv⟩ w ⟨-, hw⟩ hvw
      obtain ⟨p, hp, e1, h3⟩ := exists_eq_span hK v hv
      obtain ⟨q, hq, e2, h4⟩ := exists_eq_span hK w hw
      simp only [h3, h4, Nat.sqrt_eq'] at hvw
      apply HeightOneSpectrum.ext
      rw [e1, e2, hvw]
  rw [Set.ncard_coe_finset, Nat.card_Icc, Nat.add_sub_cancel] at h
  exact le_trans (by exact_mod_cast h) (Nat.floor_le (Real.sqrt_nonneg X))

/- English proof (translation)
Establish `hf : {v : HeightOneSpectrum (𝓞 K) | Ideal.absNorm v.asIdeal = p}.Finite` using `(finite_absNorm_le (K := K) p).subset (fun v hv => by`. Establish `hv' : Ideal.absNorm v.asIdeal = p` using `hv`. Use `show (Ideal.absNorm v.asIdeal : ℝ) ≤ p`. Rewrite using `[hv'])`. Establish `h` using `prod_absNorm_dvd hf.toFinset (Ideal.span {(p : 𝓞 K)}) (fun v hv => by`.

Establish `hv' : Ideal.absNorm v.asIdeal = p` using `by simpa using hv`. Rewrite using `[Ideal.dvd_span_singleton, ← hv']`. Conclude with `Ideal.absNorm_mem _)`. Rewrite `h` using `[Ideal.absNorm_span_natCast, RingOfIntegers.rank, hK, Finset.prod_congr rfl (g := fun _ => p) (fun v hv => by simpa using hv), Finset.prod_const]`. Rewrite using `[Set.ncard_eq_toFinset_card _ hf]`.

Conclude with `(Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h`.
-/
theorem ncard_absNorm_eq_le (hK : Module.finrank ℚ K = 2) (p : ℕ) (hp : p.Prime) :
    {v : HeightOneSpectrum (𝓞 K) | Ideal.absNorm v.asIdeal = p}.ncard ≤ 2 := by
  have hf : {v : HeightOneSpectrum (𝓞 K) | Ideal.absNorm v.asIdeal = p}.Finite :=
    (finite_absNorm_le (K := K) p).subset (fun v hv => by
      have hv' : Ideal.absNorm v.asIdeal = p := hv
      show (Ideal.absNorm v.asIdeal : ℝ) ≤ p
      rw [hv'])
  have h := prod_absNorm_dvd hf.toFinset (Ideal.span {(p : 𝓞 K)}) (fun v hv => by
    have hv' : Ideal.absNorm v.asIdeal = p := by simpa using hv
    rw [Ideal.dvd_span_singleton, ← hv']
    exact Ideal.absNorm_mem _)
  rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, hK,
    Finset.prod_congr rfl (g := fun _ => p) (fun v hv => by simpa using hv),
    Finset.prod_const] at h
  rw [Set.ncard_eq_toFinset_card _ hf]
  exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h

/- English proof (translation)
Establish `hf : {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ 𝔮}.Finite` using `Ideal.finite_factors hq`. Establish `hN : Ideal.absNorm 𝔮 ≠ 0` using `fun h => hq (Ideal.absNorm_eq_zero_iff.1 h)`. Establish `h` using `Nat.le_of_dvd (Nat.pos_of_ne_zero hN) (prod_absNorm_dvd hf.toFinset 𝔮 (fun v hv => by simpa using hv))`. Establish `h2 : 2 ^ hf.toFinset.card ≤ Ideal.absNorm 𝔮` using `le_trans (Finset.pow_card_le_prod _ _ _ (fun v _ => NumberField.HeightOneSpectrum.one_lt_absNorm v)) h`. Rewrite using `[Set.ncard_eq_toFinset_card _ hf]`.

Establish `h3 : (2 : ℝ) ^ hf.toFinset.card ≤ 4 * Ideal.absNorm 𝔮`. Establish `: ((2 ^ hf.toFinset.card : ℕ) : ℝ) ≤ Ideal.absNorm 𝔮` using `by exact_mod_cast h2`. Move the coercions through the operations in `at this`. Establish `h0 : (0 : ℝ) ≤ Ideal.absNorm 𝔮` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h4` using `Real.log_le_log (by positivity) h3`. Rewrite `h4` using `[Real.log_pow]`. Establish `h5` using `Real.log_two_gt_d9`. Establish `h6 : (0 : ℝ) ≤ hf.toFinset.card` using `Nat.cast_nonneg _`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem ncard_dvd_le (𝔮 : Ideal (𝓞 K)) (hq : 𝔮 ≠ ⊥) :
    ({v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ 𝔮}.ncard : ℝ) ≤
      3 * Real.log (4 * Ideal.absNorm 𝔮) := by
  have hf : {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ 𝔮}.Finite := Ideal.finite_factors hq
  have hN : Ideal.absNorm 𝔮 ≠ 0 := fun h => hq (Ideal.absNorm_eq_zero_iff.1 h)
  have h := Nat.le_of_dvd (Nat.pos_of_ne_zero hN)
    (prod_absNorm_dvd hf.toFinset 𝔮 (fun v hv => by simpa using hv))
  have h2 : 2 ^ hf.toFinset.card ≤ Ideal.absNorm 𝔮 :=
    le_trans (Finset.pow_card_le_prod _ _ _
      (fun v _ => NumberField.HeightOneSpectrum.one_lt_absNorm v)) h
  rw [Set.ncard_eq_toFinset_card _ hf]
  have h3 : (2 : ℝ) ^ hf.toFinset.card ≤ 4 * Ideal.absNorm 𝔮 := by
    have : ((2 ^ hf.toFinset.card : ℕ) : ℝ) ≤ Ideal.absNorm 𝔮 := by exact_mod_cast h2
    push_cast at this
    have h0 : (0 : ℝ) ≤ Ideal.absNorm 𝔮 := Nat.cast_nonneg _
    linarith
  have h4 := Real.log_le_log (by positivity) h3
  rw [Real.log_pow] at h4
  have h5 := Real.log_two_gt_d9
  have h6 : (0 : ℝ) ≤ hf.toFinset.card := Nat.cast_nonneg _
  nlinarith

/- English proof (translation)
Introduce `_ _ _ _ hK` and use `⟨fun X _ => ⟨finite_absNorm_le X, ncard_not_prime_le hK X⟩, ncard_absNorm_eq_le hK, ncard_dvd_le⟩`.
-/
theorem few_primes : ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K → Module.finrank ℚ K = 2 → (∀ X : ℝ, 1 ≤ X → {v : HeightOneSpectrum (𝓞 K) | (Ideal.absNorm v.asIdeal : ℝ) ≤ X}.Finite ∧ ({v : HeightOneSpectrum (𝓞 K) | (Ideal.absNorm v.asIdeal : ℝ) ≤ X ∧ ¬ (Ideal.absNorm v.asIdeal).Prime}.ncard : ℝ) ≤ Real.sqrt X) ∧ (∀ p : ℕ, p.Prime → {v : HeightOneSpectrum (𝓞 K) | Ideal.absNorm v.asIdeal = p}.ncard ≤ 2) ∧ ∀ 𝔮 : Ideal (𝓞 K), 𝔮 ≠ ⊥ → ({v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ 𝔮}.ncard : ℝ) ≤ 3 * Real.log (4 * Ideal.absNorm 𝔮) :=
  fun _ _ _ _ hK => ⟨fun X _ => ⟨finite_absNorm_le X, ncard_not_prime_le hK X⟩,
    ncard_absNorm_eq_le hK, ncard_dvd_le⟩

end GlobalTheory.Mem.FewPrimes
