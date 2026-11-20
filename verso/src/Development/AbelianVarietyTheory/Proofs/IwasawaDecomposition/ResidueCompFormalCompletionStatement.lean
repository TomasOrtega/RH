import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueCompFormalCompletion
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FResidueCompFormalCompletion.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.residue_comp_formal_completion : ∀ (A B R : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [CommRing B] [IsDomain B] [IsLocalRing B] [CommRing R] [IsDomain R] [IsLocalRing R] (f : A →+* B) (g : A →+* R), IsNoetherianRing A → IsNoetherianRing R → Algebra.EssFiniteType ℤ B → IsLocalHom f → Function.Injective f → (∀ b : B, ∃ a s : A, f s ≠ 0 ∧ f s * b = f a) → IsLocalHom g → GlobalTheory.Toroidal.IsEtaleCompletion g → ((IsLocalRing.residue R).comp g).FormallyUnramified → ∃ (C : Type) (_ : CommRing C) (_ : IsDomain C) (_ : IsLocalRing C) (φ : R →+* C) (ψ : B →+* C), IsNoetherianRing C ∧ IsLocalHom φ ∧ Function.Injective φ ∧ IsLocalHom ψ ∧ Function.Injective ψ ∧ ψ.Flat ∧ (IsLocalRing.maximalIdeal B).map ψ = IsLocalRing.maximalIdeal C ∧ ((IsLocalRing.residue C).comp ψ).Finite ∧ ((IsLocalRing.residue C).comp ψ).FormallyUnramified ∧ ψ.comp f = φ.comp g := by
  first | exact @GlobalTheory.LocalChart.exists_localised_base_change | exact GlobalTheory.LocalChart.exists_localised_base_change | (intros; apply GlobalTheory.LocalChart.exists_localised_base_change <;> assumption)
