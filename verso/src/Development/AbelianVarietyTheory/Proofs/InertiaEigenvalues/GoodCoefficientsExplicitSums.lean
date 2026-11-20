import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientRingIntegersCompactAdicPropertiesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components.

Supply the required witnesses or components.
-/
theorem adicSpan_smul_top_mem_iff {O : Type} [CommRing O] (ϖ : O) (n : ℕ) (x : O) :
    x ∈ (Ideal.span {ϖ}) ^ n • (⊤ : Submodule O O) ↔ ∃ b : O, x = ϖ ^ n * b := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨a, mul_comm _ _⟩
  · rintro ⟨b, rfl⟩; exact ⟨b, mul_comm _ _⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem adicComplete_explicit_sums {O : Type} [CommRing O] (ϖ : O)
    [h : IsAdicComplete (Ideal.span {ϖ}) O] :
    (∀ x : ℕ → O, ∃ a : O, ∀ n : ℕ, ∃ b : O, a - ∑ j ∈ Finset.range n, ϖ ^ j * x j = ϖ ^ n * b) ∧
    (∀ a : O, (∀ n : ℕ, ∃ b : O, a = ϖ ^ n * b) → a = 0) := by
  refine ⟨fun x => ?_, fun a ha => ?_⟩
  · obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {ϖ}) (M := O)
      (fun n => ∑ j ∈ Finset.range n, ϖ ^ j * x j) (by
        intro m n hmn
        rw [SModEq.sub_mem, adicSpan_smul_top_mem_iff]
        refine ⟨-∑ j ∈ Finset.Ico m n, ϖ ^ (j - m) * x j, ?_⟩
        rw [← Finset.sum_range_add_sum_Ico _ hmn, mul_neg, Finset.mul_sum]
        have : ∑ j ∈ Finset.Ico m n, ϖ ^ m * (ϖ ^ (j - m) * x j)
            = ∑ j ∈ Finset.Ico m n, ϖ ^ j * x j := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' (Finset.mem_Ico.mp hj).1]
        rw [this]; ring)
    refine ⟨L, fun n => ?_⟩
    have h1 := (SModEq.sub_mem.mp (hL n))
    rw [adicSpan_smul_top_mem_iff] at h1
    obtain ⟨b, hb⟩ := h1
    exact ⟨-b, by rw [mul_neg, ← hb]; ring⟩
  · refine IsHausdorff.haus' (I := Ideal.span {ϖ}) a fun n => ?_
    rw [SModEq.zero, adicSpan_smul_top_mem_iff]
    exact ha n

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem goodO_coeff_explicit_sums : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O →
    (∀ x : ℕ → O, ∃ a : O, ∀ n : ℕ, ∃ b : O,
      a - ∑ j ∈ Finset.range n, ((l : ℕ) : O) ^ j * x j = ((l : ℕ) : O) ^ n * b) ∧
    (∀ a : O, (∀ n : ℕ, ∃ b : O, a = ((l : ℕ) : O) ^ n * b) → a = 0) := by
  intro l _ LL _ _ _ O _ _ hG
  have hc := (GlobalTheory.T.coefficient_ring_integers_compact_adic_properties l LL O hG).2.2.2
  exact adicComplete_explicit_sums (h := hc) ((l : ℕ) : O)

end GlobalTheory
