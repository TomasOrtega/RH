import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqrtNegPrimeKernelCyclicStatement
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

open GlobalTheory.ConjPoint PeriodPair in

/- English proof (translation)
Introduce `p F L t hp h4 h3 hD σ hσ`. Establish `h₂ : L.g₂ = σ L.g₂` using `(hσ _ hD.g₂_mem).symm`. Establish `h₃ : L.g₃ = σ L.g₃` using `(hσ _ hD.g₃_mem).symm`. Take `⟨s, -, hc⟩` from `exists_conjEquiv h₂ h₃`. Take `⟨t', ht'⟩` from `latticePoint_surjective L (s (latticePoint L t))`.

Establish `hct : IsConj L L σ t t'` using `(hc _ _).2 ht'.symm`. Establish `ht'n : t' ∉ L.lattice`. Break down `hct with h | h` into its components or cases. Conclude with `(hD.notMem h.1).elim`. Conclude with `h.2.1`.

Establish `hsq : (σ (sqrtNegNat p)) ^ 2 = (sqrtNegNat p) ^ 2`. Rewrite using `[← map_pow, sqrtNegNat_sq, map_neg, map_natCast]`. Establish `hm` using `IsConj.mul h₂ h₃ hD.mul hct`. Establish `hker : σ (sqrtNegNat p) * t' ∈ L.lattice`. Break down `hm with h | h` into its components or cases.

Conclude with `h.2`. Conclude with `(h.1 hD.ker).elim`. Establish `hker' : sqrtNegNat p * t' ∈ L.lattice`. Break down `sq_eq_sq_iff_eq_or_eq_neg.mp hsq with e | e` into its components or cases. Rewrite `hker` using `[e]`. Then use the resulting hypothesis.

Rewrite `hker` using `[e, neg_mul]`. Simplify using `using neg_mem hker`. Take `⟨-, hz, -⟩` from `GlobalTheory.T.sqrtNegPrime_kernel_cyclic p F L t hp h4 h3 hD`. Take `⟨c, hcp, hcl⟩` from `hz t' hker'`. Use `⟨c, fun hdvd => ?_, fun k => ?_⟩` and prove the remaining obligations.

Establish `hc0 : c = 0` using `Nat.eq_zero_of_dvd_of_lt hdvd hcp`. Substitute `hc0` using the available equality. Conclude with `ht'n (by simpa using hcl)`. Establish `hk` using `IsConj.mul h₂ h₃ (α := (k : ℂ)) (fun l hl => by rw [← nsmul_eq_mul]; exact nsmul_mem hl k) hct`. Rewrite `hk` using `[map_natCast]`.

Establish `h0 : IsConj L L σ 0 ((k : ℂ) * ((c : ℂ) * t) - (k : ℂ) * t')` using `by left`. Use `⟨zero_mem _, ?_⟩` and prove the remaining obligations. Establish `: (k : ℂ) * ((c : ℂ) * t) - (k : ℂ) * t' = -((k : ℂ) * (t' - (c : ℂ) * t))` using `by ring`. Rewrite using `[this, ← nsmul_eq_mul]`. Conclude with `neg_mem (nsmul_mem hcl k)`.

Use `IsConj.add h₂ h₃ hk h0` as an intermediate fact. Simplify using `using this`.
-/
theorem exists_conj_kernel_mul : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → ∀ σ : ℂ ≃+* ℂ, (∀ x ∈ F, σ x = x) → ∃ c : ℕ, ¬ p ∣ c ∧ ∀ k : ℕ, GlobalTheory.ConjPoint.IsConj L L σ ((k : ℂ) * t) ((k : ℂ) * ((c : ℂ) * t)) := by
  intro p F L t hp h4 h3 hD σ hσ
  have h₂ : L.g₂ = σ L.g₂ := (hσ _ hD.g₂_mem).symm
  have h₃ : L.g₃ = σ L.g₃ := (hσ _ hD.g₃_mem).symm
  obtain ⟨s, -, hc⟩ := exists_conjEquiv h₂ h₃
  obtain ⟨t', ht'⟩ := latticePoint_surjective L (s (latticePoint L t))
  have hct : IsConj L L σ t t' := (hc _ _).2 ht'.symm
  have ht'n : t' ∉ L.lattice := by
    rcases hct with h | h
    · exact (hD.notMem h.1).elim
    · exact h.2.1

  have hsq : (σ (sqrtNegNat p)) ^ 2 = (sqrtNegNat p) ^ 2 := by
    rw [← map_pow, sqrtNegNat_sq, map_neg, map_natCast]
  have hm := IsConj.mul h₂ h₃ hD.mul hct
  have hker : σ (sqrtNegNat p) * t' ∈ L.lattice := by
    rcases hm with h | h
    · exact h.2
    · exact (h.1 hD.ker).elim
  have hker' : sqrtNegNat p * t' ∈ L.lattice := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with e | e
    · rwa [e] at hker
    · rw [e, neg_mul] at hker
      simpa using neg_mem hker
  obtain ⟨-, hz, -⟩ := GlobalTheory.T.sqrtNegPrime_kernel_cyclic p F L t hp h4 h3 hD
  obtain ⟨c, hcp, hcl⟩ := hz t' hker'
  refine ⟨c, fun hdvd => ?_, fun k => ?_⟩
  · have hc0 : c = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hcp
    subst hc0
    exact ht'n (by simpa using hcl)
  · have hk := IsConj.mul h₂ h₃ (α := (k : ℂ))
      (fun l hl => by rw [← nsmul_eq_mul]; exact nsmul_mem hl k) hct
    rw [map_natCast] at hk
    have h0 : IsConj L L σ 0 ((k : ℂ) * ((c : ℂ) * t) - (k : ℂ) * t') := by
      left
      refine ⟨zero_mem _, ?_⟩
      have : (k : ℂ) * ((c : ℂ) * t) - (k : ℂ) * t' = -((k : ℂ) * (t' - (c : ℂ) * t)) := by ring
      rw [this, ← nsmul_eq_mul]
      exact neg_mem (nsmul_mem hcl k)
    have := IsConj.add h₂ h₃ hk h0
    simpa using this

end GlobalTheory.CMModel
