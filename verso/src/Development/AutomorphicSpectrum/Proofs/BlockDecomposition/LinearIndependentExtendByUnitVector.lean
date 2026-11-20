import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureData
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpenStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂.VecFree

variable {K : Type} [CommRing K] {M n : ℕ}

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem sum_vec_zero (α : K) (c : Fin n → K) (X : Fin n → Fin M → K) (g : Fin (n + 1) → K) :
    (∑ a, g a • (vec α c X : Fin (n + 1) → Fin (M + 1) → K) a) 0
      = g 0 * α + ∑ j : Fin n, g j.succ * c j := by
  rw [Finset.sum_apply, Fin.sum_univ_succ]
  simp [vec]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem sum_vec_succ (α : K) (c : Fin n → K) (X : Fin n → Fin M → K) (g : Fin (n + 1) → K)
    (i : Fin M) :
    (∑ a, g a • (vec α c X : Fin (n + 1) → Fin (M + 1) → K) a) i.succ
      = (∑ j : Fin n, g j.succ • X j) i := by
  rw [Finset.sum_apply, Fin.sum_univ_succ, Finset.sum_apply]
  simp [vec]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem linearIndependent_vec_iff (K : Type) [CommRing K] (M n : ℕ) (α : K) (hα : IsUnit α)
    (c : Fin n → K) (X : Fin n → Fin M → K) :
    LinearIndependent K (vec α c X : Fin (n + 1) → Fin (M + 1) → K) ↔ LinearIndependent K X := by
  rw [Fintype.linearIndependent_iff, Fintype.linearIndependent_iff]
  constructor
  · intro h w hw j
    obtain ⟨β, hβ⟩ := hα.exists_left_inv
    have key := h (Fin.cons (-(∑ j : Fin n, w j * c j) * β) w) (by
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · rw [sum_vec_zero]
        simp only [Fin.cons_zero, Fin.cons_succ, Pi.zero_apply]
        rw [mul_assoc, hβ]
        ring
      · rw [sum_vec_succ]
        simp only [Fin.cons_succ, Pi.zero_apply]
        rw [hw]
        rfl) j.succ
    simpa using key
  · intro h w hw
    have hs : ∀ j : Fin n, w j.succ = 0 := by
      refine h (fun j => w j.succ) ?_
      funext i
      have := congrFun hw i.succ
      rwa [sum_vec_succ] at this
    have h0 : w 0 = 0 := by
      have := congrFun hw 0
      rw [sum_vec_zero] at this
      simp only [hs, zero_mul, Finset.sum_const_zero, add_zero, Pi.zero_apply] at this
      exact (hα.mul_left_eq_zero).1 this
    intro a
    refine Fin.cases h0 hs a

end GlobalTheory.CompanionTheory.SW.PiLocalization₂.VecFree
