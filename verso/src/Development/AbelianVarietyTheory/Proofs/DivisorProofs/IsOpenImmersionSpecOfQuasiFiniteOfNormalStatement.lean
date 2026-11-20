import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionSpecOfQuasiFiniteOfNormal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsOpenImmersionSpecOfQuasiFiniteOfNormal.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.isOpenImmersion_specMap_of_quasiFinite_of_normal : ∀ {A B : Type} [CommRing A] [CommRing B] [IsDomain B] [IsNoetherianRing A] (φ : A →+* B), (∀ (𝔭 : Ideal A) [𝔭.IsPrime], IsDomain (Localization.AtPrime 𝔭) ∧ IsIntegrallyClosed (Localization.AtPrime 𝔭)) → φ.FiniteType → LocallyQuasiFinite (Spec.map (CommRingCat.ofHom φ)) → (∃ V : (Spec (CommRingCat.of B)).Opens, Nonempty V ∧ IsOpenImmersion (V.ι ≫ Spec.map (CommRingCat.ofHom φ))) → IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)) := by
  first | exact @GlobalTheory.isOpenImmersion_spec_of_quasiFinite_of_normal | exact GlobalTheory.isOpenImmersion_spec_of_quasiFinite_of_normal | (intros; apply GlobalTheory.isOpenImmersion_spec_of_quasiFinite_of_normal <;> assumption)
