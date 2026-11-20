import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemUnitOff

open Formalism.BasicNotions Classical NumberField IsDedekindDomain Matrix GlobalTheory.LvT GlobalTheory.LvT.Inh
open Formalism.MainNotions.product_first_zeroth_parts (Ow ten blk CSpan IntSpan wSh)
open Formalism.L2.Col (conjPrime₂ PosStar hStd UF Sp)

namespace GlobalTheory.LvT.Inh.ResFin

/- English proof (translation)
Establish `h : ∀ p : Nat.Primes, ∃ la : HeightOneSpectrum (𝓞 K), la.asIdeal.comap (algebraMap ℤ (𝓞 K)) = Ideal.span {((p : ℕ) : ℤ)}` using `fun p => by haveI : Fact (p : ℕ).Prime := ⟨p.2⟩ haveI : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p`. Take `⟨M, hM, hc⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) (Ideal.span {((p : ℕ) : ℤ)}) (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap ℤ (𝓞 K)).injective_int]; exact bot_le)`. Conclude with `⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩, hc⟩`. Use `choose f hf using h`. Use `Infinite.of_injective f fun p q hpq => ?_` and prove the remaining obligations.

Establish `e : Ideal.span {((p : ℕ) : ℤ)} = Ideal.span {((q : ℕ) : ℤ)}` using `by rw [← hf p, ← hf q, hpq]`. Use `Int.associated_iff_natAbs.1 (Ideal.span_singleton_eq_span_singleton.1 e)` as an intermediate fact. Conclude with `Subtype.ext (by simpa using this)`.
-/
theorem infinite_places (K : Type) [Field K] [NumberField K] : Infinite (HeightOneSpectrum (𝓞 K)) := by
  have h : ∀ p : Nat.Primes, ∃ la : HeightOneSpectrum (𝓞 K), la.asIdeal.comap (algebraMap ℤ (𝓞 K)) =
      Ideal.span {((p : ℕ) : ℤ)} := fun p => by
    haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
    haveI : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
    obtain ⟨M, hM, hc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) (Ideal.span {((p : ℕ) : ℤ)})
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap ℤ (𝓞 K)).injective_int]; exact bot_le)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩, hc⟩
  choose f hf using h
  refine Infinite.of_injective f fun p q hpq => ?_
  have e : Ideal.span {((p : ℕ) : ℤ)} = Ideal.span {((q : ℕ) : ℤ)} := by rw [← hf p, ← hf q, hpq]
  have := Int.associated_iff_natAbs.1 (Ideal.span_singleton_eq_span_singleton.1 e)
  exact Subtype.ext (by simpa using this)

/- English proof (translation)
Set `ι : 𝓞 K →+* (Q.valuation K).valuationSubring` to `(algebraMap (𝓞 K) K).codRestrict (Q.valuation K).valuationSubring fun a => Q.valuation_le_one a`. Establish `key : ∀ x : (Q.valuation K).valuationSubring, IsLocalRing.residue _ x = 0 ↔ Q.valuation K (x : K) < 1` using `fun x => by`. Rewrite using `[IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]`. Set `φ : 𝓞 K ⧸ Q.asIdeal →+* IsLocalRing.ResidueField (Q.valuation K).valuationSubring` to `Ideal.Quotient.lift Q.asIdeal ((IsLocalRing.residue _).comp ι) fun a ha => by`. Rewrite using `[RingHom.comp_apply, key]`.

Conclude with `(Q.valuation_lt_one_iff_mem (K := K) a).2 ha`. Use `haveI : Finite (𝓞 K ⧸ Q.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ Q.ne_bot`. Use `Finite.of_surjective φ fun y => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `IsLocalRing.residue_surjective y`. Take `⟨a, ha⟩` from `Q.exists_valuation_sub_lt_of_integer (K := K) x.2 1`.

Use `⟨Ideal.Quotient.mk _ a, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `IsLocalRing.residue _ (ι a) = _`. Rewrite using `[← sub_eq_zero, ← map_sub, key]`. Conclude with `ha`.
-/
theorem finite_residue {K : Type} [Field K] [NumberField K] (Q : HeightOneSpectrum (𝓞 K)) :
    Finite (IsLocalRing.ResidueField (Q.valuation K).valuationSubring) := by
  let ι : 𝓞 K →+* (Q.valuation K).valuationSubring :=
    (algebraMap (𝓞 K) K).codRestrict (Q.valuation K).valuationSubring fun a => Q.valuation_le_one a
  have key : ∀ x : (Q.valuation K).valuationSubring,
      IsLocalRing.residue _ x = 0 ↔ Q.valuation K (x : K) < 1 := fun x => by
    rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
  let φ : 𝓞 K ⧸ Q.asIdeal →+* IsLocalRing.ResidueField (Q.valuation K).valuationSubring :=
    Ideal.Quotient.lift Q.asIdeal ((IsLocalRing.residue _).comp ι) fun a ha => by
      rw [RingHom.comp_apply, key]
      exact (Q.valuation_lt_one_iff_mem (K := K) a).2 ha
  haveI : Finite (𝓞 K ⧸ Q.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ Q.ne_bot
  refine Finite.of_surjective φ fun y => ?_
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨a, ha⟩ := Q.exists_valuation_sub_lt_of_integer (K := K) x.2 1
  refine ⟨Ideal.Quotient.mk _ a, ?_⟩
  change IsLocalRing.residue _ (ι a) = _
  rw [← sub_eq_zero, ← map_sub, key]
  exact ha

def redHom {K k ι : Type} [Field K] [CommRing k] [Fintype ι] [DecidableEq ι] (O : Subring K) (φ : O →+* k)
    (G : Subgroup (GL ι K)) (hG : ∀ g ∈ G, IntGL O g) : G →* Matrix ι ι k where
  toFun g := Matrix.of fun a b => φ ⟨((g : GL ι K) : Matrix ι ι K) a b, (hG g g.2 a b).1⟩
  map_one' := by
    ext a b
    simp only [Matrix.of_apply, Matrix.one_apply, OneMemClass.coe_one, Units.val_one]
    split_ifs
    · exact map_one φ
    · exact map_zero φ
  map_mul' g h := by
    ext a b
    simp only [Matrix.of_apply, Matrix.mul_apply, ← map_mul, ← map_sum]
    congr 1
    apply Subtype.ext
    simp [Matrix.mul_apply]

end GlobalTheory.LvT.Inh.ResFin
