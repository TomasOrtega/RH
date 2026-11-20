import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqAddPrimeOddModThreeValuationOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableKerRepsAddSubStatement
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

/- English proof (translation)
Establish `ha : ∀ ω ∈ L.lattice, (a : ℂ) * ω ∈ L.lattice` using `fun ω hω => by`. Use `L.lattice.smul_mem a hω` as an intermediate fact. Rewrite `this` using `[zsmul_eq_mul]`. Then use the resulting hypothesis. Use `⟨fun ω hω => ?_, fun ω hω => ?_⟩` and prove the remaining obligations. Rewrite using `[add_mul]`.

Conclude with `add_mem (ha ω hω) (h ω hω)`. Rewrite using `[sub_mul]`. Conclude with `sub_mem (ha ω hω) (h ω hω)`.
-/
theorem mulStable_intCast_add_sub (L : PeriodPair) (s : ℂ) (a : ℤ) (h : MulStable L s) :
    MulStable L (a + s) ∧ MulStable L (a - s) := by
  have ha : ∀ ω ∈ L.lattice, (a : ℂ) * ω ∈ L.lattice := fun ω hω => by
    have := L.lattice.smul_mem a hω
    rwa [zsmul_eq_mul] at this
  refine ⟨fun ω hω => ?_, fun ω hω => ?_⟩
  · rw [add_mul]; exact add_mem (ha ω hω) (h ω hω)
  · rw [sub_mul]; exact sub_mem (ha ω hω) (h ω hω)

/- English proof (translation)
Establish `h : √(p : ℝ) * √(p : ℝ) = p` using `Real.mul_self_sqrt (Nat.cast_nonneg p)`. Apply the tactic sequence `constructor <;> simp [sqrtNegNat, Complex.normSq_apply, h, sq]`.
-/
theorem normSq_natCast_add_sub_sqrtNegNat (p a : ℕ) :
    Complex.normSq (((a : ℤ) : ℂ) + sqrtNegNat p) = ((a ^ 2 + p : ℕ) : ℝ) ∧
      Complex.normSq (((a : ℤ) : ℂ) - sqrtNegNat p) = ((a ^ 2 + p : ℕ) : ℝ) := by
  have h : √(p : ℝ) * √(p : ℝ) = p := Real.mul_self_sqrt (Nat.cast_nonneg p)
  constructor <;> simp [sqrtNegNat, Complex.normSq_apply, h, sq]

/- English proof (translation)
Introduce `p F L t hp _ h3 hD V`. Take `⟨a, N, hN, hodd, hmod, hv⟩` from `GlobalTheory.T.exists_sq_add_prime_odd_mod_three_valuation_one p V hp h3`. Take `⟨hs, hs'⟩` from `mulStable_intCast_add_sub L (sqrtNegNat p) (a : ℤ) hD.mul`. Take `⟨hn, hn'⟩` from `normSq_natCast_add_sub_sqrtNegNat p a`. Rewrite `hn`, `hn'` using `[← hN]`.

Establish `hN0 : (N : ℝ) ≠ 0`. Establish `: N ≠ 0` using `by omega`. Conclude with `this` after adjusting the coercions. Establish `h0 : ((a : ℤ) : ℂ) + sqrtNegNat p ≠ 0` using `fun h => hN0 (by rw [← hn, h, map_zero])`. Establish `h0' : ((a : ℤ) : ℂ) - sqrtNegNat p ≠ 0` using `fun h => hN0 (by rw [← hn', h, map_zero])`.

Take `⟨S, hS⟩` from `kerRepsExist L _ h0 hs`. Take `⟨S', hS'⟩` from `kerRepsExist L _ h0' hs'`. Establish `hc` using `kerRepsCard L _ S h0 hs hS`. Establish `hc'` using `kerRepsCard L _ S' h0' hs' hS'`. Rewrite `hc` using `[hn]`.

Rewrite `hc'` using `[hn']`. Establish `hc1 : S.card + 1 = N` using `by exact_mod_cast hc`. Establish `hc1' : S'.card + 1 = N` using `by exact_mod_cast hc'`. Establish `hfac : (N : ℂ) = (((a : ℤ) : ℂ) - sqrtNegNat p) * (((a : ℤ) : ℂ) + sqrtNegNat p)`. Use `sqrtNegNat_sq p` as an intermediate fact.

Rewrite using `[hN]`. Use `push_cast`. Take the linear combination `this`. Use `⟨N, S ⊕ S', inferInstance, Sum.elim (fun t : S => (t : ℂ)) (fun t : S' => (t : ℂ)), hodd, hmod, hv, ?_, GlobalTheory.T.stable_sum_elim_of_isKerReps_add_sub_sqrtNegNat p F L a S S' hD.g₂_mem hD.g₃_mem hD.mul hS hS', ?_⟩` and prove the remaining obligations. Rewrite using `[Fintype.card_sum, Fintype.card_coe, Fintype.card_coe]`.

Use linear arithmetic over natural numbers and integers. Introduce and unpack `(⟨x, hx⟩ | ⟨x, hx⟩)`. Use `⟨(hS.1 x hx).2, ?_⟩ show (N : ℂ) * x ∈ _` and prove the remaining obligations. Rewrite using `[hfac, mul_assoc]`. Conclude with `hs' _ (hS.1 x hx).1`.

Use `⟨(hS'.1 x hx).2, ?_⟩ show (N : ℂ) * x ∈ _` and prove the remaining obligations. Rewrite using `[hfac, mul_comm (_ - _), mul_assoc]`. Conclude with `hs _ (hS'.1 x hx).1`.
-/
theorem exists_stable_family_ker : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → ∀ V : ValuationSubring ℂ, ∃ (N : ℕ) (ι : Type) (_ : Fintype ι) (T : ι → ℂ), Odd N ∧ N % 3 = 2 ∧ V.valuation (N : ℂ) = 1 ∧ Fintype.card ι = 2 * (N - 1) ∧ Stable L F T ∧ ∀ i, T i ∉ L.lattice ∧ (N : ℂ) * T i ∈ L.lattice := by
  intro p F L t hp _ h3 hD V
  obtain ⟨a, N, hN, hodd, hmod, hv⟩ := GlobalTheory.T.exists_sq_add_prime_odd_mod_three_valuation_one p V hp h3
  obtain ⟨hs, hs'⟩ := mulStable_intCast_add_sub L (sqrtNegNat p) (a : ℤ) hD.mul
  obtain ⟨hn, hn'⟩ := normSq_natCast_add_sub_sqrtNegNat p a
  rw [← hN] at hn hn'
  have hN0 : (N : ℝ) ≠ 0 := by
    have : N ≠ 0 := by omega
    exact_mod_cast this
  have h0 : ((a : ℤ) : ℂ) + sqrtNegNat p ≠ 0 := fun h => hN0 (by rw [← hn, h, map_zero])
  have h0' : ((a : ℤ) : ℂ) - sqrtNegNat p ≠ 0 := fun h => hN0 (by rw [← hn', h, map_zero])
  obtain ⟨S, hS⟩ := kerRepsExist L _ h0 hs
  obtain ⟨S', hS'⟩ := kerRepsExist L _ h0' hs'
  have hc := kerRepsCard L _ S h0 hs hS
  have hc' := kerRepsCard L _ S' h0' hs' hS'
  rw [hn] at hc
  rw [hn'] at hc'
  have hc1 : S.card + 1 = N := by exact_mod_cast hc
  have hc1' : S'.card + 1 = N := by exact_mod_cast hc'
  have hfac : (N : ℂ) = (((a : ℤ) : ℂ) - sqrtNegNat p) * (((a : ℤ) : ℂ) + sqrtNegNat p) := by
    have := sqrtNegNat_sq p
    rw [hN]; push_cast
    linear_combination this
  refine ⟨N, S ⊕ S', inferInstance, Sum.elim (fun t : S => (t : ℂ)) (fun t : S' => (t : ℂ)), hodd, hmod, hv,
    ?_, GlobalTheory.T.stable_sum_elim_of_isKerReps_add_sub_sqrtNegNat p F L a S S' hD.g₂_mem hD.g₃_mem hD.mul hS hS', ?_⟩
  · rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe]; omega
  · rintro (⟨x, hx⟩ | ⟨x, hx⟩)
    · refine ⟨(hS.1 x hx).2, ?_⟩
      show (N : ℂ) * x ∈ _
      rw [hfac, mul_assoc]
      exact hs' _ (hS.1 x hx).1
    · refine ⟨(hS'.1 x hx).2, ?_⟩
      show (N : ℂ) * x ∈ _
      rw [hfac, mul_comm (_ - _), mul_assoc]
      exact hs _ (hS'.1 x hx).1

end GlobalTheory.CMModel
