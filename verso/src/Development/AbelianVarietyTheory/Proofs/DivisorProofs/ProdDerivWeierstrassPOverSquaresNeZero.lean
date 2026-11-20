import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

noncomputable section

namespace GlobalTheory.CMModel.SqNe

/- English proof (translation)
Establish `h1` using `neg_mem (h.mul _ h.ker)`. Rewrite `h1` using `[← mul_assoc, ← sq, sqrtNegNat_sq, neg_mul, neg_neg]`. Conclude with `h1`.
-/
theorem natMul_mem {p : ℕ} {F : IntermediateField ℚ ℂ} {L : PeriodPair} {t : ℂ} (h : Datum p F L t) :
    (p : ℂ) * t ∈ L.lattice := by
  have h1 := neg_mem (h.mul _ h.ker)
  rw [← mul_assoc, ← sq, sqrtNegNat_sq, neg_mul, neg_neg] at h1
  exact h1

/- English proof (translation)
Introduce `hm` and use `by have h1 := natMul_mem h obtain ⟨a, b, e⟩ := Nat.isCoprime_iff_coprime.2 hn have e' : (a : ℂ) * n + b * p = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → ℂ) e have := add_mem (zsmul_mem hm a) (zsmul_mem h1 b) rw [zsmul_eq_mul, zsmul_eq_mul, ← mul_assoc, ← mul_assoc, ← add_mul …`.
-/
theorem mul_notMem {p : ℕ} {F : IntermediateField ℚ ℂ} {L : PeriodPair} {t : ℂ} (h : Datum p F L t)
    {n : ℕ} (hn : Nat.Coprime n p) : (n : ℂ) * t ∉ L.lattice := fun hm => by
  have h1 := natMul_mem h
  obtain ⟨a, b, e⟩ := Nat.isCoprime_iff_coprime.2 hn
  have e' : (a : ℂ) * n + b * p = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → ℂ) e
  have := add_mem (zsmul_mem hm a) (zsmul_mem h1 b)
  rw [zsmul_eq_mul, zsmul_eq_mul, ← mul_assoc, ← mul_assoc, ← add_mul, e', one_mul] at this
  exact h.notMem this

/- English proof (translation)
The claim follows from `((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => k.2.1 ((ZMod.natCast_eq_zero_iff _ _).2 h)).symm`.
-/
theorem coprime_sq {p : ℕ} (hp : p.Prime) (k : Sq p) : Nat.Coprime (k.1 : ℕ) p :=
  ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => k.2.1 ((ZMod.natCast_eq_zero_iff _ _).2 h)).symm

/- English proof (translation)
Introduce `p F L t hp h4 h3 h`. Establish `h2 : p ≠ 2` using `by omega`. Use `⟨fun k => ⟨mul_notMem h (coprime_sq hp k), ?_⟩, ?_⟩` and prove the remaining obligations. Use `zsmul_mem (natMul_mem h) (k.1 : ℕ)` as an intermediate fact. Rewrite `this` using `[zsmul_eq_mul]`.

Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[sqPt]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `Finset.prod_ne_zero_iff.2 fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[Ne, GlobalTheory.derivWeierstrassP_eq_zero_iff L (show sqPt p t k ∉ L.lattice from mul_notMem h (coprime_sq hp k))]`. Use `mul_notMem h (Nat.Coprime.mul_left ((Nat.coprime_primes Nat.prime_two hp).2 h2.symm) (coprime_sq hp k))` as an intermediate fact. Introduce `hm`. Apply `this` to reduce the goal to its premises. Use `hm using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[sqPt]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sqPt_and_sqProd_ne_zero : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ),
    p.Prime → p % 4 = 3 → 3 < p → Datum p F L t →
      (∀ k : Sq p, sqPt p t k ∉ L.lattice ∧ (p : ℂ) * sqPt p t k ∈ L.lattice) ∧ sqProd p L t ≠ 0 := by
  intro p F L t hp h4 h3 h
  have h2 : p ≠ 2 := by omega
  refine ⟨fun k => ⟨mul_notMem h (coprime_sq hp k), ?_⟩, ?_⟩
  · have := zsmul_mem (natMul_mem h) (k.1 : ℕ)
    rw [zsmul_eq_mul] at this
    convert this using 1
    rw [sqPt]; push_cast; ring
  · refine Finset.prod_ne_zero_iff.2 fun k _ => ?_
    rw [Ne, GlobalTheory.derivWeierstrassP_eq_zero_iff L (show sqPt p t k ∉ L.lattice from mul_notMem h (coprime_sq hp k))]
    have := mul_notMem h (Nat.Coprime.mul_left ((Nat.coprime_primes Nat.prime_two hp).2 h2.symm)
      (coprime_sq hp k))
    intro hm
    apply this
    convert hm using 1
    rw [sqPt]; push_cast; ring

end GlobalTheory.CMModel.SqNe
