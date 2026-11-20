import Development.EtaleCohomology.EtaleSheaves.IECompPf

noncomputable section
open CategoryTheory Limits Cardinal

namespace LateralTheory.E.UnderFAPf

def FP (X : CommRingCat.{0}) : ObjectProperty (Under X) := fun S => S.hom.hom.FinitePresentation

def model (X : CommRingCat.{0}) (i : Σ n : ℕ, Ideal (MvPolynomial (Fin n) X)) : Under X :=
  Under.mk (CommRingCat.ofHom (algebraMap X (MvPolynomial (Fin i.1) X ⧸ i.2)))

/- English proof (translation)
Use `⟨⟨.ofObj (model X), inferInstance, fun S hS => ?_⟩⟩` and prove the remaining obligations. Set `_ : Algebra X S.right` to `S.hom.hom.toAlgebra`. Establish `hS' : Algebra.FinitePresentation X S.right` using `hS`. Take `⟨n, f, hf, -⟩` from `hS'.out`. Set `e` to `Ideal.quotientKerAlgEquivOfSurjective hf`.

Use `⟨_, ⟨⟨n, RingHom.ker f⟩⟩, ⟨(Under.isoMk e.toRingEquiv.toCommRingCatIso ?_).symm⟩⟩` and prove the remaining obligations. Use extensionality with `x`. Conclude with `e.commutes x`.
-/
theorem fpSmall (X : CommRingCat.{0}) : ObjectProperty.EssentiallySmall.{0} (FP X) := by
  refine ⟨⟨.ofObj (model X), inferInstance, fun S hS => ?_⟩⟩
  let _ : Algebra X S.right := S.hom.hom.toAlgebra
  have hS' : Algebra.FinitePresentation X S.right := hS
  obtain ⟨n, f, hf, -⟩ := hS'.out
  let e := Ideal.quotientKerAlgEquivOfSurjective hf
  refine ⟨_, ⟨⟨n, RingHom.ker f⟩⟩, ⟨(Under.isoMk e.toRingEquiv.toCommRingCatIso ?_).symm⟩⟩
  ext x
  exact e.commutes x

attribute [local instance] fact_isRegular_aleph0

/- English proof (translation)
Introduce `S hS`. Establish `h` using `CommRingCat.isFinitelyPresentable_under X S hS`. Conclude with `h`.
-/
theorem fp_le (X : CommRingCat.{0}) : FP X ≤ isCardinalPresentable (Under X) (ℵ₀ : Cardinal.{0}) := by
  intro S hS
  have h := CommRingCat.isFinitelyPresentable_under X S hS
  exact h

def FPColim : Prop := ∀ (X : CommRingCat.{0}) (S : Under X),
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J), (FP X).colimitsOfShape J S

/- English proof (translation)
Introduce `X`. Use `fpSmall X` as an intermediate fact. Establish `hg : (FP X).IsCardinalFilteredGenerator (ℵ₀ : Cardinal.{0})` using `{ le_isCardinalPresentable := fp_le X exists_colimitsOfShape := fun S => by`. Take `⟨J, _, _, h⟩` from `hC X S`. Use `⟨J, inferInstance, ?_, h⟩` and prove the remaining obligations.

Rewrite using `[isCardinalFiltered_aleph0_iff]`. Use `infer_instance }`. Conclude with `{ toHasCardinalFilteredGenerator := hg.hasCardinalFilteredGenerator }`.
-/
theorem UnderFA_of (hC : FPColim) : LateralTheory.E.IECompPf.UnderFA := by
  intro X
  have := fpSmall X
  have hg : (FP X).IsCardinalFilteredGenerator (ℵ₀ : Cardinal.{0}) :=
    { le_isCardinalPresentable := fp_le X
      exists_colimitsOfShape := fun S => by
        obtain ⟨J, _, _, h⟩ := hC X S
        refine ⟨J, inferInstance, ?_, h⟩
        rw [isCardinalFiltered_aleph0_iff]; infer_instance }
  exact { toHasCardinalFilteredGenerator := hg.hasCardinalFilteredGenerator }

end LateralTheory.E.UnderFAPf
