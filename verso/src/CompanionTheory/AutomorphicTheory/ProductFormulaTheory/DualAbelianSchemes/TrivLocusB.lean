import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsClosedSubschemeLocallyTrivialProductLineBu
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.DualAbelianSchemes.TrivLocusA

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace CompanionTheory.PfDual

open GlobalTheory.TrivSubscheme in

/- English proof (translation)
Introduce `S A Y _ hB hY F hF`. Establish `h₀ : IsPullback (pullback.fst A.hom Y.hom) (snd A Y).left A.hom Y.hom` using `IsPullback.of_hasPullback A.hom Y.hom`. Take `⟨I, hI⟩` from `exists_idealSheaf (LocTrivOver (snd A Y).left F) LocTrivOver.comp locTrivOver_of_affine (fun U => by haveI : IsNoetherianRing Γ(Y.left, U) := IsLocallyNoetherian.component_noetherian U`. Set `t : Spec (CommRingCat.of Γ(Y.left, U)) ⟶ S` to `U.2.fromSpec ≫ Y.hom`. Establish `h₁ : IsPullback (pullback.fst A.hom t) (pullback.snd A.hom t) A.hom (U.2.fromSpec ≫ Y.hom)` using `IsPullback.of_hasPullback _ _`.

Set `φ` to `h₀.lift _ _ (h₁.w.trans (Category.assoc _ _ _).symm)`. Establish `h₂ : IsPullback φ (pullback.snd A.hom t) (snd A Y).left U.2.fromSpec` using `IsPullback.of_right (by rw [h₀.lift_fst]; exact h₁) (h₀.lift_snd _ _ _) h₀`. Take `⟨I, hI⟩` from `exists_ideal_locTriv_noeth Γ(Y.left, U) ((Over.pullback t).obj A) (CubeGen.isAb_baseChange hB t) (F.pull φ) (LB.isLB_pull hF φ)`. Use `⟨I, fun S g => ?_⟩` and prove the remaining obligations. Establish `h₃` using `IsPullback.of_hasPullback (pullback.snd A.hom t) (Spec.map g)`.

Rewrite using `[← hI S g.hom _ _ _ h₃, locTrivOver_iff (h₃.paste_horiz h₂)]`. Use `forall_congr' fun y => exists_congr fun V => and_congr_right fun _ => ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc]`. Conclude with `((triv_pull_iff _ _ _).trans (triv_pull_iff _ _ _)).symm)`. Use `⟨Over.mk (I.subschemeι ≫ Y.hom), Over.homMk I.subschemeι rfl, inferInstanceAs (IsClosedImmersion I.subschemeι), fun T' x => ?_⟩` and prove the remaining obligations.

Establish `h₄ : IsPullback (A ◁ x).left (snd A T').left (snd A Y).left x.left`. Use `IsPullback.of_right ?_ (Over.whiskerLeft_left_snd x) h₀` and prove the remaining obligations. Rewrite using `[Over.whiskerLeft_left_fst, Over.w x]`. Conclude with `IsPullback.of_hasPullback A.hom T'.hom`. Simplify using `only [triv_pull_iff]`.

Rewrite using `[← locTrivOver_iff h₄, hI]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h' : I.subschemeι.ker ≤ x.left.ker` using `by rwa [Scheme.IdealSheafData.ker_subschemeι]`. Use `⟨Over.homMk (IsClosedImmersion.lift I.subschemeι x.left h') ?_, ?_⟩` and prove the remaining obligations.

Conclude with `(IsClosedImmersion.lift_fac_assoc _ _ _ _).trans (Over.w x)`. Conclude with `Over.OverMorphism.ext (IsClosedImmersion.lift_fac _ _ _)`. Introduce and unpack `⟨y, rfl⟩`. Conclude with `I.ker_subschemeι.ge.trans (Scheme.Hom.le_ker_comp y.left I.subschemeι)`.
-/
theorem exists_closed_locTriv_noeth : ∀ (S : Scheme.{0}) (A Y : Over S) [GrpObj A], IsAbelianScheme A → IsLocallyNoetherian Y.left → ∀ F : LB (A ⊗ Y).left, F.IsLB → ∃ (H : Over S) (j : H ⟶ Y), IsClosedImmersion j.left ∧ ∀ (T' : Over S) (x : T' ⟶ Y), (∀ p : T'.left, ∃ U : T'.left.Opens, p ∈ U ∧ Triv ((F.pull (A ◁ x).left).pull ((snd A T').left ⁻¹ᵁ U).ι)) ↔ ∃ y : T' ⟶ H, y ≫ j = x := by
  intro S A Y _ hB hY F hF
  have h₀ : IsPullback (pullback.fst A.hom Y.hom) (snd A Y).left A.hom Y.hom :=
    IsPullback.of_hasPullback A.hom Y.hom
  obtain ⟨I, hI⟩ := exists_idealSheaf (LocTrivOver (snd A Y).left F) LocTrivOver.comp locTrivOver_of_affine
    (fun U => by
      haveI : IsNoetherianRing Γ(Y.left, U) := IsLocallyNoetherian.component_noetherian U
      let t : Spec (CommRingCat.of Γ(Y.left, U)) ⟶ S := U.2.fromSpec ≫ Y.hom
      have h₁ : IsPullback (pullback.fst A.hom t) (pullback.snd A.hom t) A.hom (U.2.fromSpec ≫ Y.hom) :=
        IsPullback.of_hasPullback _ _
      let φ := h₀.lift _ _ (h₁.w.trans (Category.assoc _ _ _).symm)
      have h₂ : IsPullback φ (pullback.snd A.hom t) (snd A Y).left U.2.fromSpec :=
        IsPullback.of_right (by rw [h₀.lift_fst]; exact h₁) (h₀.lift_snd _ _ _) h₀
      obtain ⟨I, hI⟩ := exists_ideal_locTriv_noeth Γ(Y.left, U) ((Over.pullback t).obj A)
        (CubeGen.isAb_baseChange hB t) (F.pull φ) (LB.isLB_pull hF φ)
      refine ⟨I, fun S g => ?_⟩
      have h₃ := IsPullback.of_hasPullback (pullback.snd A.hom t) (Spec.map g)
      rw [← hI S g.hom _ _ _ h₃, locTrivOver_iff (h₃.paste_horiz h₂)]
      refine forall_congr' fun y => exists_congr fun V => and_congr_right fun _ => ?_
      rw [← Category.assoc]
      exact ((triv_pull_iff _ _ _).trans (triv_pull_iff _ _ _)).symm)
  refine ⟨Over.mk (I.subschemeι ≫ Y.hom), Over.homMk I.subschemeι rfl,
    inferInstanceAs (IsClosedImmersion I.subschemeι), fun T' x => ?_⟩
  have h₄ : IsPullback (A ◁ x).left (snd A T').left (snd A Y).left x.left := by
    refine IsPullback.of_right ?_ (Over.whiskerLeft_left_snd x) h₀
    rw [Over.whiskerLeft_left_fst, Over.w x]
    exact IsPullback.of_hasPullback A.hom T'.hom
  simp only [triv_pull_iff]
  rw [← locTrivOver_iff h₄, hI]
  constructor
  · intro h
    have h' : I.subschemeι.ker ≤ x.left.ker := by rwa [Scheme.IdealSheafData.ker_subschemeι]
    refine ⟨Over.homMk (IsClosedImmersion.lift I.subschemeι x.left h') ?_, ?_⟩
    · exact (IsClosedImmersion.lift_fac_assoc _ _ _ _).trans (Over.w x)
    · exact Over.OverMorphism.ext (IsClosedImmersion.lift_fac _ _ _)
  · rintro ⟨y, rfl⟩
    exact I.ker_subschemeι.ge.trans (Scheme.Hom.le_ker_comp y.left I.subschemeι)

end CompanionTheory.PfDual
