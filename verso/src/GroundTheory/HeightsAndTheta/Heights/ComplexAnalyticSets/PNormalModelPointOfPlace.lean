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
Introduce `n J q M hJ P`. Take `⟨e, he⟩` from `hLoc n J q M hJ`. Take `⟨P', hP'def⟩ : ∃ P' : @Ideal (Localization (normalModelSubmonoid M q)) CommSemiring.toSemiring, P' = P.asIdeal.comap (e.symm : Localization (normalModelSubmonoid M q) →+* curveNormalisation J q)` from `⟨_, rfl⟩`. Establish `hP' : P'.IsMaximal`. Rewrite using `[hP'def]`.

Conclude with `Ideal.comap_isMaximal_of_surjective _ e.symm.surjective`. Establish `hPp : P'.IsPrime`. Rewrite using `[hP'def]`. Use `infer_instance`. Take `⟨w, hw, hq, hcomap⟩` from `hMax n J q M P' hP'`.

Take `⟨eAt, heAt⟩` from `hAt (MvPolynomial (Fin n ⊕ Fin M.m) ℂ) M.ideal (normalModelSubmonoid M q) P' (RingHom.ker (eval w : MvPolynomial (Fin n ⊕ Fin M.m) ℂ →+* ℂ)) hcomap`. Set `eP : Localization.AtPrime P.asIdeal ≃+* Localization.AtPrime P'` to `IsLocalization.ringEquivOfRingEquiv (M := P.asIdeal.primeCompl) (T := P'.primeCompl) (Localization.AtPrime P.asIdeal) (Localization.AtPrime P') e (by`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`.

Substitute `hP'def` using the available equality. Use `show e.symm (e x) ∉ P.asIdeal`. Simplify using `using hx`. Introduce `hy`. Substitute `hP'def` using the available equality.

Conclude with `⟨e.symm y, hy, by simp⟩)`. Use `⟨w, hw, hq, fun f ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[← ord_ringEquiv (eP.trans eAt)]`. Use `congr 1`. Rewrite using `[RingEquiv.trans_apply, IsLocalization.ringEquivOfRingEquiv_eq, he, heAt]`.

Both sides reduce to the same expression.
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
