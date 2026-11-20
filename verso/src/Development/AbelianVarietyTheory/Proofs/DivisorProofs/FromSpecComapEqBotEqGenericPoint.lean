import Mathlib
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `X Y _ π V hV hW P hP h`. Establish `e` using `IsAffineOpen.SpecMap_appLE_fromSpec π hV hW le_rfl`. Establish `e2 : π (hW.fromSpec ⟨P, hP⟩) = hV.fromSpec (Spec.map (π.appLE V (π ⁻¹ᵁ V) le_rfl) ⟨P, hP⟩)`. Use `congrArg (fun f : Spec Γ(Y, π ⁻¹ᵁ V) ⟶ X => f (⟨P, hP⟩ : PrimeSpectrum Γ(Y, π ⁻¹ᵁ V))) e` as an intermediate fact. Conclude with `this.symm`.

Use `set q : Spec Γ(X, V) := Spec.map (π.appLE V (π ⁻¹ᵁ V) le_rfl) ⟨P, hP⟩ with hqdef`. Establish `hq : q.asIdeal = ⊥`. Rewrite using `[← h, Scheme.Hom.app_eq_appLE]`. Both sides reduce to the same expression. Establish `hne : Nonempty V` using `⟨⟨hV.fromSpec q, hV.range_fromSpec.subset ⟨q, rfl⟩⟩⟩`.

Establish `hgen : q = genericPoint (Spec Γ(X, V))`. Rewrite using `[genericPoint_eq_bot_of_affine]`. Conclude with `PrimeSpectrum.ext hq`. Rewrite using `[e2, hgen, genericPoint_eq_of_isOpenImmersion]`.
-/
theorem fromSpec_prime_comap_bot_lies_over_genericPoint :
    ∀ (X Y : Scheme.{0}) [IsIntegral X] (π : Y ⟶ X) (V : X.Opens), IsAffineOpen V →
      ∀ (hW : IsAffineOpen (π ⁻¹ᵁ V)) (P : Ideal Γ(Y, π ⁻¹ᵁ V)) (hP : P.IsPrime),
        P.comap (π.app V).hom = ⊥ → π (hW.fromSpec ⟨P, hP⟩) = genericPoint X := by
  intro X Y _ π V hV hW P hP h
  have e := IsAffineOpen.SpecMap_appLE_fromSpec π hV hW le_rfl
  have e2 : π (hW.fromSpec ⟨P, hP⟩) =
      hV.fromSpec (Spec.map (π.appLE V (π ⁻¹ᵁ V) le_rfl) ⟨P, hP⟩) := by
    have := congrArg (fun f : Spec Γ(Y, π ⁻¹ᵁ V) ⟶ X => f (⟨P, hP⟩ : PrimeSpectrum Γ(Y, π ⁻¹ᵁ V))) e
    exact this.symm
  set q : Spec Γ(X, V) := Spec.map (π.appLE V (π ⁻¹ᵁ V) le_rfl) ⟨P, hP⟩ with hqdef
  have hq : q.asIdeal = ⊥ := by
    rw [← h, Scheme.Hom.app_eq_appLE]
    rfl
  have hne : Nonempty V := ⟨⟨hV.fromSpec q, hV.range_fromSpec.subset ⟨q, rfl⟩⟩⟩
  have hgen : q = genericPoint (Spec Γ(X, V)) := by
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext hq
  rw [e2, hgen, genericPoint_eq_of_isOpenImmersion]

end GlobalTheory
