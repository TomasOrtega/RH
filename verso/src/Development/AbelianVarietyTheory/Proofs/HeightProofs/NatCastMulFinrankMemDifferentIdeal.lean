import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz

set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize Pointwise
open scoped IntermediateField nonZeroDivisors

namespace GlobalTheory.DifferentBound

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

/- English proof (translation)
Apply `FaithfulSMul.algebraMap_injective (𝓞 L) L` to reduce the goal to its premises. Rewrite using `[← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 K) K L, Algebra.algebraMap_intTrace (L := L), trace_eq_sum_automorphisms, map_sum]`. Both sides reduce to the same expression.
-/
theorem algebraMap_intTrace_eq_sum (x : 𝓞 L) :
    algebraMap (𝓞 K) (𝓞 L) (Algebra.intTrace (𝓞 K) (𝓞 L) x) = ∑ σ : L ≃ₐ[K] L, σ • x := by
  apply FaithfulSMul.algebraMap_injective (𝓞 L) L
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 K) K L,
    Algebra.algebraMap_intTrace (L := L), trace_eq_sum_automorphisms, map_sum]
  rfl

/- English proof (translation)
Establish `hp : P.under (𝓞 K) ≠ ⊥` using `mt Ideal.eq_bot_of_comap_eq_bot hP`. Use `Ideal.IsPrime.isMaximal inferInstance hP` as an intermediate fact. Establish `: IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L)` using `IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L`. Establish `hcard` using `Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) (P.under (𝓞 K)) P`. Rewrite `hcard` using `[Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 K)) P (L ≃ₐ[K] L)]`.

Establish `hb : P.inertia (L ≃ₐ[K] L) = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `σ hσ`. Conclude with `h σ hσ`. Rewrite `hcard` using `[hb, Subgroup.card_bot]`.

Rewrite using `[not_dvd_differentIdeal_iff]`. Conclude with `Ideal.ramificationIdx_eq_one_iff.1 hcard.symm`.
-/
theorem not_dvd_of_inertia (P : Ideal (𝓞 L)) [P.IsPrime] (hP : P ≠ ⊥)
    (h : ∀ σ : L ≃ₐ[K] L, (∀ x : 𝓞 L, σ • x - x ∈ P) → σ = 1) :
    ¬ P ∣ differentIdeal (𝓞 K) (𝓞 L) := by
  have hp : P.under (𝓞 K) ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hP
  have := Ideal.IsPrime.isMaximal inferInstance hP
  have : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) (P.under (𝓞 K)) P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 K)) P (L ≃ₐ[K] L)] at hcard
  have hb : P.inertia (L ≃ₐ[K] L) = ⊥ := by
    rw [eq_bot_iff]
    intro σ hσ
    exact h σ hσ
  rw [hb, Subgroup.card_bot] at hcard
  rw [not_dvd_differentIdeal_iff]
  exact Ideal.ramificationIdx_eq_one_iff.1 hcard.symm

/- English proof (translation)
Establish `hco : IsCoprime (P ^ m) Q` using `(Ideal.isCoprime_iff_sup_eq.2 hPQ).pow_left`. Take `⟨a, ha, x, hx, hax⟩` from `Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 (Ideal.isCoprime_iff_sup_eq.1 hco))`. Use `not_dvd_differentIdeal_of_intTrace_not_mem (𝓞 K) (p := Ideal.span {((n * Module.finrank K L : ℕ) : 𝓞 K)}) (P ^ m) Q ?_ x hx ?_` and prove the remaining obligations. Rewrite using `[Ideal.map_span, Set.image_singleton, map_natCast, h]`. Introduce `htr`.

Establish `hle : Ideal.span {((n * Module.finrank K L : ℕ) : 𝓞 L)} ≤ P ^ m` using `h ▸ Ideal.mul_le_left`. Establish `h1 : ∑ σ : L ≃ₐ[K] L, σ • x ∈ P ^ m`. Rewrite using `[← algebraMap_intTrace_eq_sum]`. Apply `hle` to reduce the goal to its premises. Use `Ideal.mem_map_of_mem (algebraMap (𝓞 K) (𝓞 L)) htr` as an intermediate fact.

Rewrite `this` using `[Ideal.map_span, Set.image_singleton, map_natCast]`. Then use the resulting hypothesis. Use `set S := MulAction.stabilizer (L ≃ₐ[K] L) P`. Establish `h2 : ∀ σ : L ≃ₐ[K] L, σ • x - (if σ ∈ S then 1 else 0) ∈ P ^ m`. Introduce `σ`. Use `split_ifs with hσ`.

Establish `h3 : σ • a ∈ σ • P ^ m` using `Ideal.smul_mem_pointwise_smul σ a _ ha`. Rewrite `h3` using `[smul_pow', MulAction.mem_stabilizer_iff.1 hσ]`. Establish `h4 : σ • x - 1 = -(σ • a)`. Rewrite using `[← smul_one σ, ← hax, smul_add]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h4]`. Conclude with `neg_mem h3`. Rewrite using `[sub_zero]`. Establish `h3 : σ • x ∈ σ • Q` using `Ideal.smul_mem_pointwise_smul σ x _ hx`. Establish `h4 : σ • Ideal.span {((n * Module.finrank K L : ℕ) : 𝓞 L)} = Ideal.span {((n * Module.finrank K L : ℕ) : 𝓞 L)}`.

Rewrite using `[Ideal.pointwise_smul_def, Ideal.map_span, Set.image_singleton, map_natCast]`. Establish `h5 : P ^ m ∣ (σ • P) ^ m * σ • Q`. Rewrite using `[← smul_pow', ← smul_mul', ← h, h4]`. Conclude with `Ideal.dvd_iff_le.2 hle`. Establish `hM : (σ • P).IsMaximal`.

Rewrite using `[Ideal.pointwise_smul_def]`. Conclude with `Ideal.map_isMaximal_of_equiv (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ)`. Establish `h6 : IsCoprime P (σ • P)` using `Ideal.isCoprime_iff_sup_eq.2 (hP.coprime_of_ne hM fun e => hσ (MulAction.mem_stabilizer_iff.2 e.symm))`. Conclude with `Ideal.dvd_iff_le.1 ((h6.pow).dvd_of_dvd_mul_left h5) h3`. Establish `h7 : ((Nat.card S : ℕ) : 𝓞 L) ∈ P ^ m`.

Establish `h8` using `sub_mem h1 (Ideal.sum_mem _ fun σ (_ : σ ∈ Finset.univ) => h2 σ)`. Rewrite `h8` using `[Finset.sum_sub_distrib, sub_sub_cancel, Finset.sum_boole]`. Rewrite using `[Nat.card_eq_fintype_card, Fintype.card_subtype]` and apply the resulting hypothesis. Establish `h9 : ((Module.finrank K L : ℕ) : 𝓞 L) ∈ P ^ m`. Take `⟨c, hc⟩` from `S.card_subgroup_dvd_card`.

Rewrite using `[← IsGalois.card_aut_eq_finrank, hc, Nat.cast_mul]`. Conclude with `Ideal.mul_mem_right _ _ h7`. Establish `h10 : P ^ m * P ∣ P ^ m * Q`. Rewrite using `[← h, Ideal.dvd_span_singleton, Nat.cast_mul, mul_comm (n : 𝓞 L)]`. Conclude with `Ideal.mul_mem_mul h9 hnP`.

Establish `h0 : P ^ m ≠ 0`. Introduce `e`. Rewrite `h` using `[e, zero_mul, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]`. Conclude with `(Nat.mul_pos hn Module.finrank_pos).ne' h`. Establish `h11` using `Ideal.dvd_iff_le.1 ((mul_dvd_mul_iff_left h0).1 h10)`.

Conclude with `hP.ne_top (by rw [← hPQ, sup_eq_left.2 h11])`.
-/
theorem not_pow_dvd (n : ℕ) (hn : 0 < n) (P Q : Ideal (𝓞 L)) [hP : P.IsMaximal] (m : ℕ) (hnP : (n : 𝓞 L) ∈ P)
    (hPQ : P ⊔ Q = ⊤) (h : Ideal.span {((n * Module.finrank K L : ℕ) : 𝓞 L)} = P ^ m * Q) :
    ¬ P ^ m ∣ differentIdeal (𝓞 K) (𝓞 L) := by
  classical
  have hco : IsCoprime (P ^ m) Q := (Ideal.isCoprime_iff_sup_eq.2 hPQ).pow_left
  obtain ⟨a, ha, x, hx, hax⟩ := Submodule.mem_sup.1
    ((Ideal.eq_top_iff_one _).1 (Ideal.isCoprime_iff_sup_eq.1 hco))
  refine not_dvd_differentIdeal_of_intTrace_not_mem (𝓞 K)
    (p := Ideal.span {((n * Module.finrank K L : ℕ) : 𝓞 K)}) (P ^ m) Q ?_ x hx ?_
  · rw [Ideal.map_span, Set.image_singleton, map_natCast, h]
  intro htr
  have hle : Ideal.span {((n * Module.finrank K L : ℕ) : 𝓞 L)} ≤ P ^ m := h ▸ Ideal.mul_le_left
  have h1 : ∑ σ : L ≃ₐ[K] L, σ • x ∈ P ^ m := by
    rw [← algebraMap_intTrace_eq_sum]
    apply hle
    have := Ideal.mem_map_of_mem (algebraMap (𝓞 K) (𝓞 L)) htr
    rwa [Ideal.map_span, Set.image_singleton, map_natCast] at this
  set S := MulAction.stabilizer (L ≃ₐ[K] L) P
  have h2 : ∀ σ : L ≃ₐ[K] L, σ • x - (if σ ∈ S then 1 else 0) ∈ P ^ m := by
    intro σ
    split_ifs with hσ
    · have h3 : σ • a ∈ σ • P ^ m := Ideal.smul_mem_pointwise_smul σ a _ ha
      rw [smul_pow', MulAction.mem_stabilizer_iff.1 hσ] at h3
      have h4 : σ • x - 1 = -(σ • a) := by
        rw [← smul_one σ, ← hax, smul_add]; ring
      rw [h4]
      exact neg_mem h3
    · rw [sub_zero]
      have h3 : σ • x ∈ σ • Q := Ideal.smul_mem_pointwise_smul σ x _ hx
      have h4 : σ • Ideal.span {((n * Module.finrank K L : ℕ) : 𝓞 L)} =
          Ideal.span {((n * Module.finrank K L : ℕ) : 𝓞 L)} := by
        rw [Ideal.pointwise_smul_def, Ideal.map_span, Set.image_singleton, map_natCast]
      have h5 : P ^ m ∣ (σ • P) ^ m * σ • Q := by
        rw [← smul_pow', ← smul_mul', ← h, h4]
        exact Ideal.dvd_iff_le.2 hle
      have hM : (σ • P).IsMaximal := by
        rw [Ideal.pointwise_smul_def]
        exact Ideal.map_isMaximal_of_equiv (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ)
      have h6 : IsCoprime P (σ • P) :=
        Ideal.isCoprime_iff_sup_eq.2 (hP.coprime_of_ne hM fun e => hσ (MulAction.mem_stabilizer_iff.2 e.symm))
      exact Ideal.dvd_iff_le.1 ((h6.pow).dvd_of_dvd_mul_left h5) h3
  have h7 : ((Nat.card S : ℕ) : 𝓞 L) ∈ P ^ m := by
    have h8 := sub_mem h1 (Ideal.sum_mem _ fun σ (_ : σ ∈ Finset.univ) => h2 σ)
    rw [Finset.sum_sub_distrib, sub_sub_cancel, Finset.sum_boole] at h8
    rwa [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h9 : ((Module.finrank K L : ℕ) : 𝓞 L) ∈ P ^ m := by
    obtain ⟨c, hc⟩ := S.card_subgroup_dvd_card
    rw [← IsGalois.card_aut_eq_finrank, hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ h7
  have h10 : P ^ m * P ∣ P ^ m * Q := by
    rw [← h, Ideal.dvd_span_singleton, Nat.cast_mul, mul_comm (n : 𝓞 L)]
    exact Ideal.mul_mem_mul h9 hnP
  have h0 : P ^ m ≠ 0 := by
    intro e
    rw [e, zero_mul, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] at h
    exact (Nat.mul_pos hn Module.finrank_pos).ne' h
  have h11 := Ideal.dvd_iff_le.1 ((mul_dvd_mul_iff_left h0).1 h10)
  exact hP.ne_top (by rw [← hPQ, sup_eq_left.2 h11])

omit K L in

/- English proof (translation)
Introduce `K L _ _ _ _ _ _ n hn hu`. Establish `hD0 : differentIdeal (𝓞 K) (𝓞 L) ≠ 0` using `differentIdeal_ne_bot`. Establish `hI : Ideal.span {((n * Module.finrank K L : ℕ) : 𝓞 L)} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]`. Conclude with `(Nat.mul_pos hn Module.finrank_pos).ne'`.

Rewrite using `[← Ideal.dvd_span_singleton, UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hD0]`. Introduce `P hP`. Establish `hPp : P.IsPrime` using `Ideal.isPrime_of_prime hP`. Establish `hP0 : P ≠ ⊥` using `hP.ne_zero`. Establish `hPm` using `hPp.isMaximal hP0`.

Distinguish the cases in `hnP : (n : 𝓞 L) ∈ P`. Take `⟨Q, hPQ, h⟩` from `Ideal.eq_prime_pow_mul_coprime hI P`. Establish `h1` using `not_pow_dvd K L n hn P Q _ hnP hPQ h`. Conclude with `(emultiplicity_lt_iff_not_dvd.2 h1).le.trans (le_emultiplicity_of_pow_dvd ⟨Q, h⟩)`. Establish `hp : P.under (𝓞 K) ≠ ⊥` using `mt Ideal.eq_bot_of_comap_eq_bot hP0`.

Establish `h1` using `hu ⟨P.under (𝓞 K), inferInstance, hp⟩ (fun e => hnP (by simpa using Ideal.mem_comap.1 e))`. Establish `h2` using `not_dvd_of_inertia K L P hP0 fun σ hσ => h1 σ ⟨P, hPp, ⟨rfl⟩, hσ⟩`. Rewrite using `[emultiplicity_eq_zero.2 h2]`. Conclude with `zero_le`.
-/
theorem natCast_mul_finrank_mem_differentIdeal :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (n : ℕ), 0 < n →
      (∀ 𝔭 : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∉ 𝔭.asIdeal → GlobalTheory.NT.UnramIn L 𝔭) →
      ((n * Module.finrank K L : ℕ) : 𝓞 L) ∈ differentIdeal (𝓞 K) (𝓞 L) := by
  intro K L _ _ _ _ _ _ n hn hu
  classical
  have hD0 : differentIdeal (𝓞 K) (𝓞 L) ≠ 0 := differentIdeal_ne_bot
  have hI : Ideal.span {((n * Module.finrank K L : ℕ) : 𝓞 L)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact (Nat.mul_pos hn Module.finrank_pos).ne'
  rw [← Ideal.dvd_span_singleton, UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hD0]
  intro P hP
  have hPp : P.IsPrime := Ideal.isPrime_of_prime hP
  have hP0 : P ≠ ⊥ := hP.ne_zero
  have hPm := hPp.isMaximal hP0
  by_cases hnP : (n : 𝓞 L) ∈ P
  · obtain ⟨Q, hPQ, h⟩ := Ideal.eq_prime_pow_mul_coprime hI P
    have h1 := not_pow_dvd K L n hn P Q _ hnP hPQ h
    exact (emultiplicity_lt_iff_not_dvd.2 h1).le.trans (le_emultiplicity_of_pow_dvd ⟨Q, h⟩)
  · have hp : P.under (𝓞 K) ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hP0
    have h1 := hu ⟨P.under (𝓞 K), inferInstance, hp⟩ (fun e => hnP (by simpa using Ideal.mem_comap.1 e))
    have h2 := not_dvd_of_inertia K L P hP0 fun σ hσ => h1 σ ⟨P, hPp, ⟨rfl⟩, hσ⟩
    rw [emultiplicity_eq_zero.2 h2]
    exact zero_le

end GlobalTheory.DifferentBound
