import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveEtaleCohomologicalDimensionLeOnStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologySpecTwistIndependentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerVanishingStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Consider separately whether the proposition holds or fails. Establish an intermediate fact.

Substitute using the available equality. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities.

Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem acyc_polynomial_of_isAlgClosed : ∀ (q : ℕ) [NeZero q] (K : Type) [Field K] [IsAlgClosed K],
    IsUnit (q : K) → Acyc q (sp (Polynomial K)) := by
  intro q _ K _ _ hq n i hn
  have hqA : IsUnit (q : Polynomial K) := by
    simpa using hq.map (Polynomial.C : K →+* Polynomial K)
  by_cases h2 : 2 ≤ n
  · exact GlobalTheory.T.smooth_affine_curve_etale_cohomologicalDimension_le_one q K (Polynomial K) hq n i h2
  · have hn1 : n = 1 := by omega
    subst hn1
    have hζ : ∃ ζ : Polynomial K, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
      have hdeg : (Polynomial.cyclotomic q K).degree ≠ 0 := by
        rw [Polynomial.degree_cyclotomic]
        have := Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))
        exact_mod_cast this.ne'
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdeg
      refine ⟨Polynomial.C z, ?_⟩
      have hz' : Polynomial.aeval z (Polynomial.cyclotomic q ℤ) = 0 := by
        rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
        exact hz
      have hC : Polynomial.C z = algebraMap K (Polynomial K) z := rfl
      rw [hC, Polynomial.aeval_algebraMap_apply, hz', map_zero]
    obtain ⟨e⟩ := GlobalTheory.T.tateTwistCohomology_spec_twist_independent q (Polynomial K) hqA hζ 1 i 1
    have hs : Subsingleton (Ht q (sp (Polynomial K)) 1 1) := by
      refine GlobalTheory.T.kummer_etale_vanishing q (Polynomial K) hqA ?_ ?_
      · intro u
        obtain ⟨r, hr, hru⟩ := Polynomial.isUnit_iff.1 u.isUnit
        obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq r (Nat.pos_of_ne_zero (NeZero.ne q))
        have hv0 : v ≠ 0 := by
          rintro rfl
          rw [zero_pow (NeZero.ne q)] at hv
          exact hr.ne_zero hv.symm
        refine ⟨Units.map (Polynomial.C : K →+* Polynomial K).toMonoidHom (Units.mk0 v hv0), ?_⟩
        ext
        simp [← hru, ← hv]
      · intro c _
        exact Subsingleton.elim _ _
    exact e.toEquiv.subsingleton

end GlobalTheory.EtC
