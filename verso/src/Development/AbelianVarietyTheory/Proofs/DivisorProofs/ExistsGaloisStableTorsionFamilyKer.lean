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
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem normSq_natCast_add_sub_sqrtNegNat (p a : ℕ) :
    Complex.normSq (((a : ℤ) : ℂ) + sqrtNegNat p) = ((a ^ 2 + p : ℕ) : ℝ) ∧
      Complex.normSq (((a : ℤ) : ℂ) - sqrtNegNat p) = ((a ^ 2 + p : ℕ) : ℝ) := by
  have h : √(p : ℝ) * √(p : ℝ) = p := Real.mul_self_sqrt (Nat.cast_nonneg p)
  constructor <;> simp [sqrtNegNat, Complex.normSq_apply, h, sq]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Move the embeddings inside the algebraic operations. Take a linear combination of the given relations to obtain the conclusion. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
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
