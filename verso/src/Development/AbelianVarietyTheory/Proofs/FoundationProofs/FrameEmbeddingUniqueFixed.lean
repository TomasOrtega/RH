import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdxEqRelIndex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsNormCmPrimeInertPrimeSignStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimeDvdMem

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise

namespace GlobalTheory.InertParity.FiniteOrder

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.PrimeDivisorMembership.exists_prime_dvd_mem`. Consider the case `exact _root_.GlobalTheory.PrimeDivisorMembership.exists_prime_dvd_mem`. Consider the case `(apply _root_.GlobalTheory.PrimeDivisorMembership.exists_prime_dvd_mem <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.PrimeDivisorMembership.exists_prime_dvd_mem <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.PrimeDivisorMembership.exists_prime_dvd_mem <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.PrimeDivisorMembership.exists_prime_dvd_mem ..)`.
-/
theorem exists_prime_mem {R : Type*} [CommRing R] (P : Ideal R) (hP : P.IsPrime) (n : ℕ) (hn : n ≠ 0)
    (h : (n : R) ∈ P) : ∃ q : ℕ, q.Prime ∧ q ∣ n ∧ (q : R) ∈ P := by
  first
  | exact @_root_.GlobalTheory.PrimeDivisorMembership.exists_prime_dvd_mem
  | exact _root_.GlobalTheory.PrimeDivisorMembership.exists_prime_dvd_mem
  | (apply _root_.GlobalTheory.PrimeDivisorMembership.exists_prime_dvd_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimeDivisorMembership.exists_prime_dvd_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimeDivisorMembership.exists_prime_dvd_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimeDivisorMembership.exists_prime_dvd_mem ..)

/- English proof (translation)
Take `⟨P, hP, ⟨e⟩⟩` from `(isSimpleModule_iff_quot_maximal (R := 𝓞 D.host.E) (M := S)).1 ‹_›`. Establish `hc : Nat.card S = Ideal.absNorm P`. Rewrite using `[Nat.card_congr e.toEquiv, Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Establish `h0 : Ideal.absNorm P ≠ 0` using `hc ▸ Nat.card_pos.ne'`. Take `⟨h1, h2, h3⟩` from `GlobalTheory.T.absNorm_cmPrime_inertPrime_sign D P hP`.

Rewrite using `[hc]`. Use `⟨h1, fun h => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hs : D.host.conj • P = P`. Conclude with `(h2 hs).1`. Take `⟨q, hq, hd, hm⟩` from `exists_prime_mem P hP.isPrime _ h0 (Ideal.absNorm_mem P)`.

Conclude with `absurd (h q hq hd) ((h3 hs).2 q hq hm)`.
-/
theorem simple_case (D : D7) (S : Type) [AddCommGroup S] [Module (𝓞 D.host.E) S] [Finite S]
    [IsSimpleModule (𝓞 D.host.E) S] :
    Ev D (Nat.card S) ∧ ((∀ q : ℕ, q.Prime → q ∣ Nat.card S → InertQ D q) → sgn D (Nat.card S) = -1) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := (isSimpleModule_iff_quot_maximal (R := 𝓞 D.host.E) (M := S)).1 ‹_›
  have hc : Nat.card S = Ideal.absNorm P := by
    rw [Nat.card_congr e.toEquiv, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have h0 : Ideal.absNorm P ≠ 0 := hc ▸ Nat.card_pos.ne'
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.absNorm_cmPrime_inertPrime_sign D P hP
  rw [hc]
  refine ⟨h1, fun h => ?_⟩
  by_cases hs : D.host.conj • P = P
  · exact (h2 hs).1
  · obtain ⟨q, hq, hd, hm⟩ := exists_prime_mem P hP.isPrime _ h0 (Ideal.absNorm_mem P)
    exact absurd (h q hq hd) ((h3 hs).2 q hq hm)

/- English proof (translation)
Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `M _ _ _ hn`. Break down `subsingleton_or_nontrivial M with hM | hM` into its components or cases. Establish `h1 : Nat.card M = 1` using `Nat.card_of_subsingleton (0 : M)`.

Rewrite using `[h1, Module.length_eq_zero]`. Conclude with `⟨Ev.one, fun _ => by simp [sgn_one]⟩`. Choose the witnesses or unpack the hypotheses as in `⟨N, hN⟩ : ∃ N : Submodule (𝓞 D.host.E) M, IsCoatom N := by`. Break down `eq_top_or_exists_le_coatom (⊥ : Submodule (𝓞 D.host.E) M) with h | ⟨N, hN, -⟩` into its components or cases. Conclude with `absurd h bot_ne_top`.

Conclude with `⟨N, hN⟩`. Use `haveI : Finite (M ⧸ N) := Finite.of_surjective _ N.mkQ_surjective`. Use `haveI : IsSimpleModule (𝓞 D.host.E) (M ⧸ N) := isSimpleModule_iff_isCoatom.2 hN`. Use `haveI : Nontrivial (M ⧸ N) := IsSimpleModule.nontrivial (𝓞 D.host.E) (M ⧸ N)`. Establish `hc : Nat.card M = Nat.card N * Nat.card (M ⧸ N)` using `Submodule.card_eq_card_quotient_mul_card N`.

Establish `hq : 1 < Nat.card (M ⧸ N)` using `Finite.one_lt_card`. Establish `hp : 0 < Nat.card N` using `Nat.card_pos`. Take `⟨a1, a2⟩` from `ih (Nat.card N) (by rw [← hn, hc]; exact lt_mul_of_one_lt_right hp hq) N rfl`. Take `⟨b1, b2⟩` from `simple_case D (M ⧸ N)`. Establish `hl : Module.length (𝓞 D.host.E) M = Module.length (𝓞 D.host.E) N + Module.length (𝓞 D.host.E) (M ⧸ N)` using `Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective (LinearMap.exact_subtype_mkQ N)`.

Establish `hfin : Module.length (𝓞 D.host.E) N ≠ ⊤` using `Module.length_ne_top`. Rewrite using `[hl, Module.length_eq_one (R := 𝓞 D.host.E) (M := M ⧸ N), ENat.toNat_add hfin (by simp), hc]`. Use `⟨a1.mul b1 hp.ne' (by omega), fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[sgn_mul a1 b1 hp.ne' (by omega), a2 fun q hq hd => h q hq (hd.mul_right _), b2 fun q hq hd => h q hq (hd.mul_left _), pow_add]`. Simplify using the standard rewrite rules.
-/
theorem card_parity_sign_length_of_eq (D : D7) (n : ℕ) : ∀ (M : Type) [AddCommGroup M] [Module (𝓞 D.host.E) M] [Finite M],
    Nat.card M = n → Ev D (Nat.card M) ∧ ((∀ q : ℕ, q.Prime → q ∣ Nat.card M → InertQ D q) →
      sgn D (Nat.card M) = (-1 : ℂ) ^ (Module.length (𝓞 D.host.E) M).toNat) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M _ _ _ hn
    rcases subsingleton_or_nontrivial M with hM | hM
    · have h1 : Nat.card M = 1 := Nat.card_of_subsingleton (0 : M)
      rw [h1, Module.length_eq_zero]
      exact ⟨Ev.one, fun _ => by simp [sgn_one]⟩
    · obtain ⟨N, hN⟩ : ∃ N : Submodule (𝓞 D.host.E) M, IsCoatom N := by
        rcases eq_top_or_exists_le_coatom (⊥ : Submodule (𝓞 D.host.E) M) with h | ⟨N, hN, -⟩
        · exact absurd h bot_ne_top
        · exact ⟨N, hN⟩
      haveI : Finite (M ⧸ N) := Finite.of_surjective _ N.mkQ_surjective
      haveI : IsSimpleModule (𝓞 D.host.E) (M ⧸ N) := isSimpleModule_iff_isCoatom.2 hN
      haveI : Nontrivial (M ⧸ N) := IsSimpleModule.nontrivial (𝓞 D.host.E) (M ⧸ N)
      have hc : Nat.card M = Nat.card N * Nat.card (M ⧸ N) := Submodule.card_eq_card_quotient_mul_card N
      have hq : 1 < Nat.card (M ⧸ N) := Finite.one_lt_card
      have hp : 0 < Nat.card N := Nat.card_pos
      obtain ⟨a1, a2⟩ := ih (Nat.card N) (by rw [← hn, hc]; exact lt_mul_of_one_lt_right hp hq) N rfl
      obtain ⟨b1, b2⟩ := simple_case D (M ⧸ N)
      have hl : Module.length (𝓞 D.host.E) M =
          Module.length (𝓞 D.host.E) N + Module.length (𝓞 D.host.E) (M ⧸ N) :=
        Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
          (LinearMap.exact_subtype_mkQ N)
      have hfin : Module.length (𝓞 D.host.E) N ≠ ⊤ := Module.length_ne_top
      rw [hl, Module.length_eq_one (R := 𝓞 D.host.E) (M := M ⧸ N), ENat.toNat_add hfin (by simp), hc]
      refine ⟨a1.mul b1 hp.ne' (by omega), fun h => ?_⟩
      rw [sgn_mul a1 b1 hp.ne' (by omega), a2 fun q hq hd => h q hq (hd.mul_right _),
        b2 fun q hq hd => h q hq (hd.mul_left _), pow_add]
      simp

/- English proof (translation)
Introduce `D M _ _ _` and use `card_parity_sign_length_of_eq D _ M rfl`.
-/
theorem ev_card_and_sgn_card : ∀ (D : D7) (M : Type) [AddCommGroup M] [Module (𝓞 D.host.E) M] [Finite M], Ev D (Nat.card M) ∧ ((∀ q : ℕ, q.Prime → q ∣ Nat.card M → InertQ D q) → sgn D (Nat.card M) = (-1 : ℂ) ^ (Module.length (𝓞 D.host.E) M).toNat) :=
  fun D M _ _ _ => card_parity_sign_length_of_eq D _ M rfl

end GlobalTheory.InertParity.FiniteOrder
