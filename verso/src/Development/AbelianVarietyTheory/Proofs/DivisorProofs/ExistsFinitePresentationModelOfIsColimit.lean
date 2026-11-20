import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZModTorsorIff
open CategoryTheory Limits TensorProduct

namespace GlobalTheory.FpDescent

/- English proof (translation)
Introduce `J _ _ F c hc D _ _ hD`. Establish `hc'` using `isColimitOfPreserves (forget _) hc`. Set `P` to `Algebra.Presentation.ofFinitePresentation c.pt D`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, P.coeffs ⊆ Set.range (c.ι.app j).hom := by`. Establish `hfin` using `P.finite_coeffs`.

Use `choose jx x hx using fun y : c.pt ↦ Types.jointly_surjective_of_isColimit hc' y`. Take `⟨j, hj⟩` from `IsFiltered.sup_objs_exists (hfin.toFinset.image jx)`. Use `⟨j, fun y hy ↦ ?_⟩` and prove the remaining obligations. Take `⟨f⟩` from `hj (Finset.mem_image_of_mem jx (hfin.mem_toFinset.mpr hy))`. Use `⟨F.map f (x y), ?_⟩` and prove the remaining obligations.

Establish `h1` using `hx y`. Establish `h2` using `congr(($(c.w f)).hom (x y))`. Simplify using `only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2`. Rewrite using `[h2]`. Conclude with `h1`.

Use `letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra`. Use `letI : Algebra (F.obj j) D := ((algebraMap c.pt D).comp (c.ι.app j).hom).toAlgebra`. Use `haveI : IsScalarTower (F.obj j) c.pt D := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)`. Use `haveI : P.HasCoeffs (F.obj j) := ⟨hj⟩`. Conclude with `⟨j, P.ModelOfHasCoeffs (F.obj j), inferInstance, inferInstance, inferInstance, ⟨P.tensorModelOfHasCoeffsEquiv (F.obj j)⟩⟩`.
-/
theorem exists_finitePresentation_model_of_isColimit :
    ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (D : Type) [CommRing D] [Algebra c.pt D], Algebra.FinitePresentation c.pt D →
    ∃ (j : J) (A : Type) (_ : CommRing A) (_ : Algebra (F.obj j) A)
      (_ : Algebra.FinitePresentation (F.obj j) A),
      letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      Nonempty (c.pt ⊗[F.obj j] A ≃ₐ[c.pt] D) := by
  intro J _ _ F c hc D _ _ hD
  classical
  have hc' := isColimitOfPreserves (forget _) hc
  let P := Algebra.Presentation.ofFinitePresentation c.pt D
  obtain ⟨j, hj⟩ : ∃ j, P.coeffs ⊆ Set.range (c.ι.app j).hom := by
    have hfin := P.finite_coeffs
    choose jx x hx using fun y : c.pt ↦ Types.jointly_surjective_of_isColimit hc' y
    obtain ⟨j, hj⟩ := IsFiltered.sup_objs_exists (hfin.toFinset.image jx)
    refine ⟨j, fun y hy ↦ ?_⟩
    obtain ⟨f⟩ := hj (Finset.mem_image_of_mem jx (hfin.mem_toFinset.mpr hy))
    refine ⟨F.map f (x y), ?_⟩
    have h1 := hx y
    have h2 := congr(($(c.w f)).hom (x y))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2
    rw [h2]
    exact h1
  letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  letI : Algebra (F.obj j) D := ((algebraMap c.pt D).comp (c.ι.app j).hom).toAlgebra
  haveI : IsScalarTower (F.obj j) c.pt D := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  haveI : P.HasCoeffs (F.obj j) := ⟨hj⟩
  exact ⟨j, P.ModelOfHasCoeffs (F.obj j), inferInstance, inferInstance, inferInstance,
    ⟨P.tensorModelOfHasCoeffsEquiv (F.obj j)⟩⟩

end GlobalTheory.FpDescent
