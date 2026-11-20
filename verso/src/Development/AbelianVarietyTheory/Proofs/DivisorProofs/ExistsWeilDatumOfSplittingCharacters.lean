import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTildeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTwistHeckeCharactersStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilExist

variable {D : D7}

/- English proof (translation)
Use `⟨?_, fun x => ?_⟩` and prove the remaining obligations. Establish `: (((η ^ n)⁻¹ * χ : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => (η x ^ n)⁻¹ * χ x`. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules. Rewrite using `[this]`.

Conclude with `((hη.1.pow n).inv).mul hχ.1`. Establish `h1` using `hχ.2 x`. Establish `h2` using `hη.2 x`. Simplify using `only [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, h1, h2, one_pow, inv_one, mul_one]`.
-/
theorem isHeckeChar_div_pow {χ η : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hη : IsHeckeChar D η) (n : ℕ) :
    IsHeckeChar D ((η ^ n)⁻¹ * χ) := by
  refine ⟨?_, fun x => ?_⟩
  · have : (((η ^ n)⁻¹ * χ : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => (η x ^ n)⁻¹ * χ x := by
      funext x; simp
    rw [this]
    exact ((hη.1.pow n).inv).mul hχ.1
  · have h1 := hχ.2 x
    have h2 := hη.2 x
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, h1, h2, one_pow, inv_one, mul_one]

/- English proof (translation)
Use `⟨hχ.1, fun e he a => ?_⟩` and prove the remaining obligations. Establish `h1` using `hχ.2 e he a`. Establish `h2` using `hη.2 e he a`. Simplify using `only [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, h1, h2, pow_one, pow_zero, inv_mul_cancel]`.
-/
theorem resEta_div_pow {χ η : (AE D)ˣ →* Circle} {n : ℕ} (hχ : ResEta D χ n) (hη : ResEta D η 1) :
    ResEta D ((η ^ n)⁻¹ * χ) 0 := by
  refine ⟨hχ.1, fun e he a => ?_⟩
  have h1 := hχ.2 e he a
  have h2 := hη.2 e he a
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, h1, h2, pow_one, pow_zero, inv_mul_cancel]

/- English proof (translation)
Introduce `D ψ hψ S T χS χT ⟨η, hη⟩ hS hT rS rT`. Take `⟨θ, hθ⟩` from `hψ.2.1`. Take `⟨om, hom, -⟩` from `GlobalTheory.T.exists_weilDatum_powers_unramifiedEtaTilde D ψ hψ S T θ hθ _ _ (GlobalTheory.PlaceModel.isSelfDualC_latFrame S) (GlobalTheory.PlaceModel.isSelfDualC_latFrame T) η hη`. Take `⟨om', hom', -⟩` from `GlobalTheory.T.exists_weilDatum_twist_heckeCharacters D ψ hψ S T _ _ ((η ^ S.rank)⁻¹ * χS) ((η ^ T.rank)⁻¹ * χT) om hom (isHeckeChar_div_pow hS hη.1 _) (isHeckeChar_div_pow hT hη.1 _) (resEta_div_pow rS hη.2.2.1) (resEta_div_pow rT hη.2.2.1)`. Rewrite `hom'` using `[mul_inv_cancel_left, mul_inv_cancel_left]`.

Conclude with `⟨om', hom'⟩`.
-/
theorem exists_isWeilDatumO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), (∃ η, IsEtaTilde D η) → IsHeckeChar D χS → IsHeckeChar D χT → ResEta D χS S.rank → ResEta D χT T.rank → ∃ om, IsWeilDatumO ψ S T χS χT om := by
  intro D ψ hψ S T χS χT ⟨η, hη⟩ hS hT rS rT
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨om, hom, -⟩ := GlobalTheory.T.exists_weilDatum_powers_unramifiedEtaTilde D ψ hψ S T θ hθ _ _ (GlobalTheory.PlaceModel.isSelfDualC_latFrame S) (GlobalTheory.PlaceModel.isSelfDualC_latFrame T) η hη
  obtain ⟨om', hom', -⟩ := GlobalTheory.T.exists_weilDatum_twist_heckeCharacters D ψ hψ S T _ _ ((η ^ S.rank)⁻¹ * χS) ((η ^ T.rank)⁻¹ * χT) om hom
    (isHeckeChar_div_pow hS hη.1 _) (isHeckeChar_div_pow hT hη.1 _)
    (resEta_div_pow rS hη.2.2.1) (resEta_div_pow rT hη.2.2.1)
  rw [mul_inv_cancel_left, mul_inv_cancel_left] at hom'
  exact ⟨om', hom'⟩

end GlobalTheory.WeilExist
