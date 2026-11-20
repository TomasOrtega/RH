import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsClosedSubschemeLocallyTrivialProductLineBu
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorRigidifiedLocallyTrivialStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.AffineTrivLocus

/- English proof (translation)
Introduce `R _ A _ L₀ N hA hL₀ hamp hN hrig`. Establish `hproj : GlobalTheory.AbLaw.IsProjBy A.hom` using `(GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral (Sp R) A L₀ hA hL₀ hamp R (𝟙 _) A.left (𝟙 _) A.hom (IsPullback.id_horiz A.hom)).1`. Set `T0 : Over (Sp R)` to `Over.mk (𝟙 _)`. Establish `h₀ : IsPullback (pullback.snd T0.hom A.hom) (fst T0 A).left A.hom T0.hom` using `(IsPullback.of_hasPullback T0.hom A.hom).flip`. Take `⟨F, hFd⟩ : ∃ F : LB (T0 ⊗ A).left, F = N.pull (pullback.snd T0.hom A.hom)` from `⟨_, rfl⟩`.

Establish `hF : F.IsLB` using `hFd ▸ LB.isLB_pull hN _`. Take `⟨H, j, hj, hH⟩` from `GlobalTheory.TrivSubscheme.exists_closed_locTriv GlobalTheory.SemiRigid.globalFns R T0 A hA hproj F hF`. Use `⟨H.left, j.left, hj, ?_⟩` and prove the remaining obligations. Introduce `T t A' _ φ' hφ`. Set `T' : Over (Sp R)` to `Over.mk t`.

Set `x : T' ⟶ T0` to `Over.homMk t (Category.comp_id t)`. Establish `hR : (∃ y : T' ⟶ H, y ≫ j = x) ↔ ∃ z : T ⟶ H.left, z ≫ j.left = t`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy⟩`. Conclude with `⟨y.left, congrArg (fun g => g.left) hy⟩`.

Introduce and unpack `⟨z, hz⟩`. Use `⟨Over.homMk z ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `z ≫ H.hom = t`. Rewrite using `[← Over.w j]`. Express the relevant statement in the definitionally equal form `z ≫ j.left ≫ 𝟙 _ = t`.

Rewrite using `[Category.comp_id, hz]`. Conclude with `Over.OverMorphism.ext hz`. Rewrite using `[← hR, ← hH T' x]`. Establish `h₄ : IsPullback (x ▷ A).left (fst T' A).left (fst T0 A).left x.left`. Use `IsPullback.of_right ?_ (Over.whiskerRight_left_fst x) h₀` and prove the remaining obligations.

Rewrite using `[Over.whiskerRight_left_snd, Over.w]`. Conclude with `(IsPullback.of_hasPullback T'.hom A.hom).flip`. Establish `hw : φ' ≫ A.hom = (A'.hom ≫ t) ≫ T0.hom`. Rewrite using `[hφ.1.w]`. Conclude with `(Category.comp_id _).symm`.

Set `φ'' : A'.left ⟶ (T0 ⊗ A).left` to `h₀.lift φ' (A'.hom ≫ t) hw`. Establish `hsq : IsPullback φ'' A'.hom (fst T0 A).left t`. Use `IsPullback.of_right (h₁₂ := pullback.snd T0.hom A.hom) (h₂₂ := T0.hom) ?_ (h₀.lift_snd _ _ _) h₀` and prove the remaining obligations. Rewrite using `[h₀.lift_fst]`. Conclude with `(Category.comp_id t).symm ▸ hφ.1`.

Establish `e₁ : (∀ p : T'.left, ∃ U : T'.left.Opens, p ∈ U ∧ GlobalTheory.AbLaw.Triv ((F.pull (x ▷ A).left).pull ((fst T' A).left ⁻¹ᵁ U).ι)) ↔ GlobalTheory.TrivSubscheme.LocTrivOver (fst T0 A).left F T'.left x.left`. Rewrite using `[GlobalTheory.TrivSubscheme.locTrivOver_iff h₄]`. Conclude with `forall_congr' fun p => exists_congr fun U => and_congr_right fun _ => GlobalTheory.TrivSubscheme.triv_pull_iff _ _ _`. Rewrite using `[e₁]`. Use `show _ ↔ GlobalTheory.TrivSubscheme.LocTrivOver (fst T0 A).left F T t`.

Rewrite using `[GlobalTheory.TrivSubscheme.locTrivOver_iff hsq]`. Establish `hA' : IsAbelianScheme A'` using `GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hφ`. Prove the components needed by the constructor for the conclusion. Introduce `ht τ`. Use `⟨⊤, trivial, ?_⟩` and prove the remaining obligations.

Rewrite using `[hFd, GlobalTheory.TrivSubscheme.triv_pull_iff, Category.assoc, h₀.lift_fst]`. Conclude with `GlobalTheory.AbLaw.CubeOpen.triv_comp _ rfl ht`. Introduce `h`. Use `GlobalTheory.T.exists_generator_rigidified_locally_trivial T A' (N.pull φ') hA' (LB.isLB_pull hN φ') (GlobalTheory.PolBaseChange.rigidified_pull hφ hrig) fun τ => ?_` and prove the remaining obligations. Take `⟨V, hV, ht⟩` from `h τ`.

Use `⟨V, hV, ?_⟩` and prove the remaining obligations. Rewrite `ht` using `[hFd, GlobalTheory.TrivSubscheme.triv_pull_iff, Category.assoc, h₀.lift_fst]`. Conclude with `(GlobalTheory.TrivSubscheme.triv_pull_iff _ _ _).2 ht`.
-/
theorem exists_closed_triv : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (L₀ N : LB A.left), IsAbelianScheme A → L₀.IsLB → Out.RelAmple A L₀ → N.IsLB → Out.Rigidified A N → ∃ (Z : Scheme.{0}) (i : Z ⟶ Sp R), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ Sp R) (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left), IsGrpPullback A' A t φ' → ((∃ s : (N.pull φ').Gen, s.IsGen) ↔ ∃ z : T ⟶ Z, z ≫ i = t) := by
  intro R _ A _ L₀ N hA hL₀ hamp hN hrig
  have hproj : GlobalTheory.AbLaw.IsProjBy A.hom :=
    (GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral (Sp R) A L₀ hA hL₀ hamp R (𝟙 _)
      A.left (𝟙 _) A.hom (IsPullback.id_horiz A.hom)).1
  let T0 : Over (Sp R) := Over.mk (𝟙 _)
  have h₀ : IsPullback (pullback.snd T0.hom A.hom) (fst T0 A).left A.hom T0.hom :=
    (IsPullback.of_hasPullback T0.hom A.hom).flip
  obtain ⟨F, hFd⟩ : ∃ F : LB (T0 ⊗ A).left, F = N.pull (pullback.snd T0.hom A.hom) := ⟨_, rfl⟩
  have hF : F.IsLB := hFd ▸ LB.isLB_pull hN _
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.TrivSubscheme.exists_closed_locTriv GlobalTheory.SemiRigid.globalFns R T0 A hA hproj F hF
  refine ⟨H.left, j.left, hj, ?_⟩
  intro T t A' _ φ' hφ
  let T' : Over (Sp R) := Over.mk t
  let x : T' ⟶ T0 := Over.homMk t (Category.comp_id t)
  have hR : (∃ y : T' ⟶ H, y ≫ j = x) ↔ ∃ z : T ⟶ H.left, z ≫ j.left = t := by
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y.left, congrArg (fun g => g.left) hy⟩
    · rintro ⟨z, hz⟩
      refine ⟨Over.homMk z ?_, ?_⟩
      · change z ≫ H.hom = t
        rw [← Over.w j]
        change z ≫ j.left ≫ 𝟙 _ = t
        rw [Category.comp_id, hz]
      · exact Over.OverMorphism.ext hz
  rw [← hR, ← hH T' x]
  have h₄ : IsPullback (x ▷ A).left (fst T' A).left (fst T0 A).left x.left := by
    refine IsPullback.of_right ?_ (Over.whiskerRight_left_fst x) h₀
    rw [Over.whiskerRight_left_snd, Over.w]
    exact (IsPullback.of_hasPullback T'.hom A.hom).flip
  have hw : φ' ≫ A.hom = (A'.hom ≫ t) ≫ T0.hom := by
    rw [hφ.1.w]; exact (Category.comp_id _).symm
  let φ'' : A'.left ⟶ (T0 ⊗ A).left := h₀.lift φ' (A'.hom ≫ t) hw
  have hsq : IsPullback φ'' A'.hom (fst T0 A).left t := by
    refine IsPullback.of_right (h₁₂ := pullback.snd T0.hom A.hom) (h₂₂ := T0.hom) ?_ (h₀.lift_snd _ _ _) h₀
    rw [h₀.lift_fst]
    exact (Category.comp_id t).symm ▸ hφ.1
  have e₁ : (∀ p : T'.left, ∃ U : T'.left.Opens, p ∈ U ∧
      GlobalTheory.AbLaw.Triv ((F.pull (x ▷ A).left).pull ((fst T' A).left ⁻¹ᵁ U).ι)) ↔
      GlobalTheory.TrivSubscheme.LocTrivOver (fst T0 A).left F T'.left x.left := by
    rw [GlobalTheory.TrivSubscheme.locTrivOver_iff h₄]
    exact forall_congr' fun p => exists_congr fun U => and_congr_right fun _ =>
      GlobalTheory.TrivSubscheme.triv_pull_iff _ _ _
  rw [e₁]
  show _ ↔ GlobalTheory.TrivSubscheme.LocTrivOver (fst T0 A).left F T t
  rw [GlobalTheory.TrivSubscheme.locTrivOver_iff hsq]
  have hA' : IsAbelianScheme A' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hφ
  constructor
  · intro ht τ
    refine ⟨⊤, trivial, ?_⟩
    rw [hFd, GlobalTheory.TrivSubscheme.triv_pull_iff, Category.assoc, h₀.lift_fst]
    exact GlobalTheory.AbLaw.CubeOpen.triv_comp _ rfl ht
  · intro h
    refine GlobalTheory.T.exists_generator_rigidified_locally_trivial T A' (N.pull φ') hA' (LB.isLB_pull hN φ') (GlobalTheory.PolBaseChange.rigidified_pull hφ hrig)
      fun τ => ?_
    obtain ⟨V, hV, ht⟩ := h τ
    refine ⟨V, hV, ?_⟩
    rw [hFd, GlobalTheory.TrivSubscheme.triv_pull_iff, Category.assoc, h₀.lift_fst] at ht
    exact (GlobalTheory.TrivSubscheme.triv_pull_iff _ _ _).2 ht

end GlobalTheory.AffineTrivLocus
