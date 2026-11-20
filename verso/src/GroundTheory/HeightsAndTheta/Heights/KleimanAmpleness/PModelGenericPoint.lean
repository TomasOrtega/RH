import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreSide
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiProjPrimeMIdealOverGraph
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver)

noncomputable section

namespace ModelGenericPoint

variable {O : Type} [CommRing O] {K : Type} {ι : K → Type} (P : Ideal (NumbersDVR.MRing ι O))

def genPt : (Σ k, ι k) → FractionRing (NumbersDVR.MRing ι O ⧸ P) :=
  fun p => algebraMap (NumbersDVR.MRing ι O ⧸ P) _ (Ideal.Quotient.mk P (X p))

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression.
-/
theorem aeval_genPt (g : NumbersDVR.MRing ι O) :
    aeval (genPt P) g = algebraMap (NumbersDVR.MRing ι O ⧸ P)
      (FractionRing (NumbersDVR.MRing ι O ⧸ P)) (Ideal.Quotient.mk P g) := by
  have h : (aeval (genPt P) : NumbersDVR.MRing ι O →ₐ[O] FractionRing (NumbersDVR.MRing ι O ⧸ P)) =
      (IsScalarTower.toAlgHom O (NumbersDVR.MRing ι O ⧸ P)
        (FractionRing (NumbersDVR.MRing ι O ⧸ P))).comp (Ideal.Quotient.mkₐ O P) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [genPt]
  rw [h]
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem aeval_genPt_eq_zero (g : NumbersDVR.MRing ι O) : aeval (genPt P) g = 0 ↔ g ∈ P := by
  rw [aeval_genPt, map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem genPt_ne_zero (p : Σ k, ι k) : genPt P p ≠ 0 ↔ (X p : NumbersDVR.MRing ι O) ∉ P := by
  rw [Ne, ← aeval_genPt_eq_zero, aeval_X]

/- English proof (translation)
By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mIdealOver_genPt [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] [P.IsPrime]
    (hP : NumbersDVR.IsMultiHomogIdeal P) : mIdealOver O (genPt P) = P := by
  ext f
  constructor
  · intro hf
    have hc : ∀ b : K → ℕ, weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f ∈ P := by
      intro b
      rw [← aeval_genPt_eq_zero, ← coeff_mConeMapOver, RingHom.mem_ker.mp hf, coeff_zero]
    rw [← sum_weightedHomogeneousComponent (NumbersDVR.blockWeight ι) f,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
    exact Ideal.sum_mem _ fun b _ => hc b
  · intro hf
    refine RingHom.mem_ker.mpr ?_
    ext m
    rw [coeff_zero]
    have h := coeff_mConeMapOver (S := O) (genPt P) (⇑m) f
    rw [Finsupp.equivFunOnFinite_symm_coe] at h
    rw [h, aeval_genPt_eq_zero]
    exact hP f hf _

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem algebraMap_injective (h : P.comap (C : O →+* NumbersDVR.MRing ι O) = ⊥) :
    Function.Injective (algebraMap O (FractionRing (NumbersDVR.MRing ι O ⧸ P))) := by
  have h0 : Function.Injective (algebraMap O (NumbersDVR.MRing ι O ⧸ P)) := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have hc' : Ideal.Quotient.mk P (C c) = 0 := by
      exact hc
    have hmem : c ∈ P.comap (C : O →+* NumbersDVR.MRing ι O) :=
      Ideal.mem_comap.mpr (Ideal.Quotient.eq_zero_iff_mem.mp hc')
    rw [h] at hmem
    exact hmem
  rw [IsScalarTower.algebraMap_eq O (NumbersDVR.MRing ι O ⧸ P)]
  exact (IsFractionRing.injective (NumbersDVR.MRing ι O ⧸ P)
    (FractionRing (NumbersDVR.MRing ι O ⧸ P))).comp h0

end ModelGenericPoint

open ModelGenericPoint in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem ModelGenericPoint.proof : ModelGenericPoint.Statement := by
  intro O _ _ _ K _ _ ι _ P d hP
  have := hP.multiProj.isPrime
  have hinj := algebraMap_injective P hP.noTorsion
  let alg : Algebra (FractionRing O) (FractionRing (NumbersDVR.MRing ι O ⧸ P)) :=
    (IsFractionRing.lift hinj).toAlgebra
  refine ⟨FractionRing (NumbersDVR.MRing ι O ⧸ P), inferInstance, inferInstance, alg, ?_, genPt P,
    mIdealOver_genPt P hP.multiProj.multiHomog, fun k => ?_⟩
  · exact IsScalarTower.of_algebraMap_eq fun c => (IsFractionRing.lift_algebraMap hinj c).symm
  · obtain ⟨i, hi⟩ := hP.multiProj.relevant k
    exact ⟨i, (genPt_ne_zero P _).mpr hi⟩

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
