import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelPointOfPlace
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StModelLocalizationMaximalPoint
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalizationAtPrimeQuotient
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartLocalOrder
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Introduce a local definition for the expression.

By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Substitute using the available equality. Simplify to obtain the desired conclusion from the available facts.

Fix the arbitrary inputs or assume the hypotheses. Substitute using the available equality. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem NormalModelPointOfPlace.proof (hLoc : NormalisationModelLocalization.Statement)
    (hMax : ModelLocalizationMaximalPoint.Statement) (hAt : LocalizationAtPrimeQuotient.Statement.{0}) :
    NormalModelPointOfPlace.Statement := by
  intro n J q M hJ P
  obtain ⟨e, he⟩ := hLoc n J q M hJ
  obtain ⟨P', hP'def⟩ : ∃ P' : @Ideal (Localization (normalModelSubmonoid M q)) CommSemiring.toSemiring,
      P' = P.asIdeal.comap (e.symm : Localization (normalModelSubmonoid M q) →+* curveNormalisation J q) :=
    ⟨_, rfl⟩
  have hP' : P'.IsMaximal := by
    rw [hP'def]
    exact Ideal.comap_isMaximal_of_surjective _ e.symm.surjective
  have hPp : P'.IsPrime := by
    rw [hP'def]
    infer_instance
  obtain ⟨w, hw, hq, hcomap⟩ := hMax n J q M P' hP'
  obtain ⟨eAt, heAt⟩ := hAt (MvPolynomial (Fin n ⊕ Fin M.m) ℂ) M.ideal (normalModelSubmonoid M q) P'
    (RingHom.ker (eval w : MvPolynomial (Fin n ⊕ Fin M.m) ℂ →+* ℂ)) hcomap
  let eP : Localization.AtPrime P.asIdeal ≃+* Localization.AtPrime P' :=
    IsLocalization.ringEquivOfRingEquiv (M := P.asIdeal.primeCompl) (T := P'.primeCompl)
      (Localization.AtPrime P.asIdeal) (Localization.AtPrime P') e (by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          subst hP'def
          show e.symm (e x) ∉ P.asIdeal
          simpa using hx
        · intro hy
          subst hP'def
          exact ⟨e.symm y, hy, by simp⟩)
  refine ⟨w, hw, hq, fun f ↦ ?_⟩
  rw [← ord_ringEquiv (eP.trans eAt)]
  congr 1
  rw [RingEquiv.trans_apply, IsLocalization.ringEquivOfRingEquiv_eq, he, heAt]
  rfl

end

end GroundTheory.Heights₂.Heights
