import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyTorusExtensionOfIsGt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.QuasiCompactIffLocallyOfFinitePresentation
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GrpObjOfDenseOpen

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SplitExtComm

/- English proof (translation)
Use `ExtUnique.flat_tensorObj A A` as an intermediate fact. Establish `key : ∀ (T : Over S') (t : Over.mk (T.hom ≫ f) ⟶ A ⊗ A), t ≫ (β_ A A).hom ≫ μ[A] = t ≫ μ[A]` using `fun T t => by`. Take `⟨x, hx⟩` from `GrpDense.pushPt_surjective h.1 T (t ≫ fst _ _)`. Take `⟨y, hy⟩` from `GrpDense.pushPt_surjective h.1 T (t ≫ snd _ _)`. Take `rfl : t = lift (pushPt h.1.w x) (pushPt h.1.w y)` from `CartesianMonoidalCategory.hom_ext _ _ (by rw [lift_fst, hx]) (by rw [lift_snd, hy])`.

Rewrite using `[lift_braiding_hom_assoc]`. Conclude with `Over.OverMorphism.ext ((h.2 T y x _ _ rfl rfl).trans ((congrArg (fun z => z.left ≫ φ) (_root_.mul_comm y x)).trans (h.2 T x y _ _ rfl rfl).symm))`. Use `⟨ExtUnique.over_hom_ext_of_isPullback (IsPullback.of_hasPullback (A ⊗ A).hom f) ?_⟩` and prove the remaining obligations. Conclude with `congrArg (fun z => z.left) (key (Over.mk (pullback.snd (A ⊗ A).hom f)) (Over.homMk (pullback.fst (A ⊗ A).hom f) (by simpa using pullback.condition)))`.
-/
theorem isCommMonObj_of_dominant {S S' : Scheme.{0}} {f : S' ⟶ S} [QuasiCompact f]
    [IsSchemeTheoreticallyDominant f] {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
    [Flat A.hom] [IsSeparated A.hom] {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ)
    [IsCommMonObj A'] : IsCommMonObj A := by
  have := ExtUnique.flat_tensorObj A A
  have key : ∀ (T : Over S') (t : Over.mk (T.hom ≫ f) ⟶ A ⊗ A),
      t ≫ (β_ A A).hom ≫ μ[A] = t ≫ μ[A] := fun T t => by
    obtain ⟨x, hx⟩ := GrpDense.pushPt_surjective h.1 T (t ≫ fst _ _)
    obtain ⟨y, hy⟩ := GrpDense.pushPt_surjective h.1 T (t ≫ snd _ _)
    obtain rfl : t = lift (pushPt h.1.w x) (pushPt h.1.w y) :=
      CartesianMonoidalCategory.hom_ext _ _ (by rw [lift_fst, hx]) (by rw [lift_snd, hy])
    rw [lift_braiding_hom_assoc]
    exact Over.OverMorphism.ext ((h.2 T y x _ _ rfl rfl).trans
      ((congrArg (fun z => z.left ≫ φ) (_root_.mul_comm y x)).trans (h.2 T x y _ _ rfl rfl).symm))
  refine ⟨ExtUnique.over_hom_ext_of_isPullback (IsPullback.of_hasPullback (A ⊗ A).hom f) ?_⟩
  exact congrArg (fun z => z.left) (key (Over.mk (pullback.snd (A ⊗ A).hom f))
    (Over.homMk (pullback.fst (A ⊗ A).hom f) (by simpa using pullback.condition)))

/- English proof (translation)
Take `⟨hs, -⟩` from `UnitRigidity.smooth_geometricallyConnected_of_isGt E G h`. Take `⟨d⟩` from `h`. Use `d.q_affine` as an intermediate fact. Use `E.isAbelian.proper` as an intermediate fact. Establish `: IsSeparated G.hom`.

Rewrite using `[← Over.w d.q]`. Use `infer_instance`. Set `f : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of O)` to `Spec.map (CommRingCat.ofHom (algebraMap O C))`. Establish `: IsSchemeTheoreticallyDominant f` using `ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ hinj`. Take `⟨T⟩` from `nonempty_torusExtension_of_isGt _ _ (GtBaseChange.isGt_extBC f E G d)`.

Use `SemiAbelianCompare.isCommMonObj_of_torusExtension T` as an intermediate fact. Conclude with `isCommMonObj_of_dominant (isGrpPullback_pullback G f)`.
-/
theorem isCommMonObj_of_isGt {O C : Type} [CommRing O] [Field C] [Algebra O C]
    (hinj : Function.Injective (algebraMap O C)) (E : SplitExt (Spec (CommRingCat.of O)))
    (G : Over (Spec (CommRingCat.of O))) [GrpObj G] (h : E.IsGt G) : IsCommMonObj G := by
  obtain ⟨hs, -⟩ := UnitRigidity.smooth_geometricallyConnected_of_isGt E G h
  obtain ⟨d⟩ := h
  have := d.q_affine
  have := E.isAbelian.proper
  have : IsSeparated G.hom := by
    rw [← Over.w d.q]
    infer_instance
  let f : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of O) :=
    Spec.map (CommRingCat.ofHom (algebraMap O C))
  have : IsSchemeTheoreticallyDominant f :=
    ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ hinj
  obtain ⟨T⟩ := nonempty_torusExtension_of_isGt _ _ (GtBaseChange.isGt_extBC f E G d)
  have := SemiAbelianCompare.isCommMonObj_of_torusExtension T
  exact isCommMonObj_of_dominant (isGrpPullback_pullback G f)

end GlobalTheory.SplitExtComm
