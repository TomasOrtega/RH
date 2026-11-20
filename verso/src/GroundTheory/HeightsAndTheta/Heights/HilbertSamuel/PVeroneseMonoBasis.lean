import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsVeroneseChiParts
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseGenDeg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CSandwichStE
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open scoped Pointwise

noncomputable section

namespace VeroneseMonoBasis

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem sec_x_eq (D n : ℕ) : sec ℤ (Veronese.x D) n = sec ℤ (Veronese.t D) (2 * n) := by
  rw [SectionsRank.sec_eq_span, SectionsRank.sec_eq_span, VeroneseGenDeg.range_alt, ← pow_mul]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem mono_mem_sec (D n : ℕ) (k : Fin (Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).card) :
    (∏ i, Veronese.t D i ^ adtEnum D (2 * n) k i) ∈ sec ℤ (Veronese.x D) n := by
  rw [sec_x_eq]
  refine Submodule.mem_map.mpr ⟨monoZ (adtEnum D (2 * n) k),
    (mem_homogeneousSubmodule _ _).mpr (monoZ_isHomogeneous (adtEnum_sum D (2 * n) k)), ?_⟩
  rw [AlgHom.toLinearMap_apply, aeval_monoZ]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem linearIndependent_mono (D N : ℕ) :
    LinearIndependent ℤ (fun k : Fin (Finset.Nat.antidiagonalTuple (D + 1) N).card =>
      ∏ i, Veronese.t D i ^ adtEnum D N k i) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro u hu l
  set p : MvPolynomial (Fin (D + 1)) ℤ := ∑ k, u k • monoZ (adtEnum D N k) with hp
  have hpa : aeval (Veronese.t D) p = aeval (Veronese.t D) (0 : MvPolynomial (Fin (D + 1)) ℤ) := by
    rw [hp, map_sum, map_zero, ← hu]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, aeval_monoZ]
  have hp0 := VeroneseGenDeg.aeval_t_injective D hpa
  have hc := congrArg (coeff (Finsupp.equivFunOnFinite.symm (adtEnum D N l))) hp0
  rw [hp, coeff_sum, coeff_zero, Finset.sum_eq_single l (fun k _ hkl => ?_) (by simp)] at hc
  · rwa [coeff_smul, monoZ, coeff_monomial, if_pos rfl, smul_eq_mul, mul_one] at hc
  · rw [coeff_smul, monoZ, coeff_monomial, if_neg, smul_zero]
    intro hE
    exact hkl (adtEnum_injective D N (by simpa using hE))

end VeroneseMonoBasis

open VeroneseMonoBasis in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem VeroneseMonoBasis.proof : VeroneseMonoBasis.Statement := by
  intro D n
  have hex : ∀ k : Fin (Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).card,
      ∃ f : MvPolynomial (Ix (Veronese.Idx D)) ℤ, f.IsHomogeneous n ∧
        aeval (Veronese.x D) f = ∏ i, Veronese.t D i ^ adtEnum D (2 * n) k i := fun k => by
    obtain ⟨f, hf, hfx⟩ := Submodule.mem_map.mp (mono_mem_sec D n k)
    exact ⟨f, (mem_homogeneousSubmodule _ _).mp hf, hfx⟩
  choose f hf hfx using hex
  have hb : ∀ k, aeval (Veronese.x D) (map (Int.castRingHom ℚ) (f k)) =
      ∏ i, Veronese.t D i ^ adtEnum D (2 * n) k i := fun k => by
    rw [aeval_map_intQ, hfx]
  refine ⟨fun k => map (Int.castRingHom ℚ) (f k), ⟨fun k => ⟨f k, hf k, rfl⟩, ?_, ?_⟩, hb⟩
  · simp only [hb]
    exact linearIndependent_mono D (2 * n)
  · simp only [hb]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact mono_mem_sec D n k
    · rw [sec_x_eq]
      rintro _ ⟨g, hg, rfl⟩
      rw [AlgHom.toLinearMap_apply, aeval_eq_sum_adt _ ((mem_homogeneousSubmodule _ _).mp hg)]
      refine Submodule.sum_mem _ fun a ha => ?_
      have hai : adtEnum D (2 * n) ((Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).equivFin ⟨a, ha⟩) = a := by
        simp [adtEnum]
      rw [← zsmul_eq_mul, ← hai]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
