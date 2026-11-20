import Mathlib
open Polynomial

namespace GlobalTheory

/- English proof (translation)
Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem finiteField_exists_generator_minpoly (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [Finite K]
    [Algebra (ZMod l) K] :
    ∃ (a : K) (p : (ZMod l)[X]), p.Monic ∧ Irreducible p ∧ aeval a p = 0 ∧
      aeval a (derivative p) ≠ 0 ∧ (∀ y : K, ∃ q : (ZMod l)[X], aeval a q = y) ∧
      Nat.card K = l ^ p.natDegree := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : FiniteDimensional (ZMod l) K := Module.Finite.of_finite
  let pb := Field.powerBasisOfFiniteOfSeparable (ZMod l) K
  refine ⟨pb.gen, minpoly (ZMod l) pb.gen, minpoly.monic pb.isIntegral_gen,
    minpoly.irreducible pb.isIntegral_gen, minpoly.aeval _ _, ?_, ?_, ?_⟩
  · exact (Algebra.IsSeparable.isSeparable (ZMod l) pb.gen).aeval_derivative_ne_zero
      (minpoly.aeval _ _)
  · intro y
    obtain ⟨q, -, hq⟩ := pb.exists_eq_aeval y
    exact ⟨q, hq.symm⟩
  · rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod l) (V := K), ZMod.card, pb.natDegree_minpoly,
      pb.finrank]

end GlobalTheory
