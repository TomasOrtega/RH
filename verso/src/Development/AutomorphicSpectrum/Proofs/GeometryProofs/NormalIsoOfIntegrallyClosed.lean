import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Supply the required witnesses or components.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem NormAt.isoAt_of_integrallyClosed : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X) (p : Cpt ξ),
    NormAt ξ' f (RingHom.id Ω) p → (∀ a : Ω, IsIntegral (regAt ξ p) a → a ∈ regAt ξ p) →
      IsoAt ξ' f (RingHom.id Ω) p := by
  intro X Ω _ ξ X' ξ' f p hN hp
  have e : (integralClosure ((regAt ξ p).map (RingHom.id Ω)) Ω).toSubring = regAt ξ p := by
    rw [Subring.map_id]
    ext a
    exact ⟨hp a, fun ha => isIntegral_algebraMap (x := (⟨a, ha⟩ : regAt ξ p))⟩
  have loc : IsLocalRing (integralClosure ((regAt ξ p).map (RingHom.id Ω)) Ω).toSubring := by
    rw [e]
    exact NormAt.isLocalRing_regAt p
  have hr : ∀ q : Cpt ξ', f q.1 = p.1 →
      regAt ξ' q = (integralClosure ((regAt ξ p).map (RingHom.id Ω)) Ω).toSubring := fun q hq => by
    obtain ⟨P, hP, h⟩ := hN.exists_max q hq
    exact h.trans (NormAt.ofPrime_of_isLocalRing _ P hP)
  refine ⟨?_, fun q hq => ?_, hN.dom⟩
  · obtain ⟨q, hq, hu⟩ := hN.existsUnique _ (IsLocalRing.maximalIdeal.isMaximal _)
    exact ⟨q, hq.1, fun q' hq' => hu q' ⟨hq', (hr q' hq').trans
      (NormAt.ofPrime_of_isLocalRing _ _ (IsLocalRing.maximalIdeal.isMaximal _)).symm⟩⟩
  · rw [hr q hq, e, Subring.map_id]

end GlobalTheory.CompanionTheory.Ar
