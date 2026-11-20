import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseOfDenseP
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjectiveRepresentationPullbackCoordinates
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordBcScaleUnique
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.NearBuild

def chartPullCompOfPullPull {X Y Z : Scheme.{0}} (M : LB X) (π : Y ⟶ X) (φ : Z ⟶ Y) :
    ChartPull (M.pull (φ ≫ π)) ((M.pull π).pull φ) (𝟙 Z) where
  idx j := fun _ => j
  le j := RepBC.le₂ M π φ j
  g y j j' hj hj' := by
    have h := RepBC.le₂ M π φ j hj
    have h' := RepBC.le₂ M π φ j' hj'
    refine (gm_pull_g M (φ ≫ π) (𝟙 Z) y j j' hj hj').trans (Eq.symm ?_)
    refine (gm_pull_g (M.pull π) φ (𝟙 Z) y (fun _ => j) (fun _ => j') h h').trans ?_
    exact gm_pull_g M π (𝟙 Z ≫ φ) y j j' (mem_pull.1 h) (mem_pull.1 h')

/- English proof (translation)
Assemble the required witnesses or components as `⟨LBIso.chartPull (chartPullId A) (chartPullCompOfPullPull M π φ), LBIso.chartPull (chartPullId A) (chartPullLinComb M π (fun _ : PUnit => φ) (fun _ => φ ≫ π) (fun _ => 1) (𝟙 Z) fun _ => (Category.id_comp _).symm)⟩`.
-/
theorem lbIso_pullPull_iff {X Y Z : Scheme.{0}} (A : LB Z) (M : LB X) (π : Y ⟶ X) (φ : Z ⟶ Y) :
    LBIso A ((M.pull π).pull φ) ↔ LBIso A (M.pull (φ ≫ π)) :=
  ⟨LBIso.chartPull (chartPullId A) (chartPullCompOfPullPull M π φ),
    LBIso.chartPull (chartPullId A) (chartPullLinComb M π (fun _ : PUnit => φ) (fun _ => φ ≫ π) (fun _ => 1) (𝟙 Z)
      fun _ => (Category.id_comp _).symm)⟩

/- English proof (translation)
Introduce `o _ g N' J b Mat κ R _ β v m Z M th sc R' _ ρ Z' π hp ⟨⟨I, p, hrep, hco⟩, hflat, hfib⟩`. Take `⟨th', hrep', hc⟩` from `RepBC.projRep_baseChange R R' _ ρ I _ _ _ _ π M th hrep hp`. Establish `hw : ∀ h, (spMap ρ ≫ (sc h).left) ≫ Z.hom = 𝟙 _ ≫ spMap ρ` using `fun h => by`. Rewrite using `[Category.assoc, Over.w (sc h), Category.id_comp]`. Conclude with `Category.comp_id _`.

Set `sc' : Ix g (N' ^ 2) → (Out.baseOver (Sp R') ⟶ Z')` to `fun h => Over.homMk (hp.lift (spMap ρ ≫ (sc h).left) (𝟙 _) (hw h)) (hp.lift_snd _ _ _)`. Establish `hsc : ∀ h, (sc' h).left ≫ π = spMap ρ ≫ (sc h).left` using `fun h => hp.lift_fst _ _ _`. Establish `hsc' : ∀ h, (sc' h).left ≫ Z'.hom = 𝟙 _` using `fun h => hp.lift_snd _ _ _`. Use `⟨th', sc', ⟨⟨_, fun h a => ρ (p h a), hrep', fun h => (hc _ _ _).2 ?_⟩, MorphismProperty.of_isPullback (P := @Flat) hp hflat, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hsc]`.

Conclude with `Coord.baseChange (hco h) ρ`. Introduce `K _ _ x s t ht`. Take `⟨φ, h1, ⟨σ, hσ, h2⟩, h3, h4⟩` from `hfib K (x.comp ρ) s t ((good_comp _ _ _).1 ht)`. Establish `hw' : φ ≫ Z.hom = (t.A.hom ≫ spMap x) ≫ spMap ρ`. Rewrite using `[h1.w, NearBuild.spMap_comp, Category.assoc]`.

Establish `e1 : hp.lift φ _ hw' ≫ π = φ` using `hp.lift_fst _ _ _`. Establish `e2 : hp.lift φ _ hw' ≫ Z'.hom = t.A.hom ≫ spMap x` using `hp.lift_snd _ _ _`. Generalize the expression as in `hp.lift φ _ hw' = φ' at e1 e2`. Substitute `e1` using the available equality. Use `⟨φ', IsPullback.of_right (by rw [← NearBuild.spMap_comp]; exact h1) e2 hp, ⟨σ, hσ, fun T _ y w => ?_⟩, (lbIso_pullPull_iff _ _ _ _).2 h3, fun h => ?_⟩` and prove the remaining obligations.

Rewrite using `[h2 T y w, hc, Category.assoc, Category.assoc]`. Apply `hp.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, h4, NearBuild.spMap_comp] erw [Category.assoc, Category.assoc, hsc]`. Rewrite using `[Category.assoc, e2, ← Category.assoc, Over.w (t.lab h ^ N')] erw [Category.assoc, hsc', Category.id_comp]`. Introduce and unpack `K _ x s t φ ⟨h1, ⟨σ, hσ, h2⟩, h3, h4⟩`.

Use `⟨by rw [NearBuild.spMap_comp]; exact h1.paste_horiz hp, ⟨σ, hσ, fun T _ y w => ?_⟩, (lbIso_pullPull_iff _ _ _ _).1 h3, fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[h2 T y w, hc, Category.assoc, Category.assoc]`. Rewrite using `[← Category.assoc, h4, NearBuild.spMap_comp] erw [Category.assoc, Category.assoc, hsc]`.
-/
theorem fam_baseChange : ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (R : Type) [CommRing R] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (m : ℕ) (Z : Over (Sp R)) (M : LB Z.left) (th : Ix g (N' ^ 2) → M.Sec) (sc : Ix g (N' ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (R' : Type) [CommRing R'] (ρ : R →+* R') (Z' : Over (Sp R')) (π : Z'.left ⟶ Z.left), IsPullback π Z'.hom Z.hom (spMap ρ) → Fam b Mat κ β v m M th sc → ∃ (th' : Ix g (N' ^ 2) → (M.pull π).Sec) (sc' : Ix g (N' ^ 2) → (Out.baseOver (Sp R') ⟶ Z')), Fam b Mat κ (ρ.comp β) (fun a => ρ (v a)) m (M.pull π) th' sc' ∧ ∀ (K : Type) [Field K] (x : R' →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (φ : t.A.left ⟶ Z'.left), Fib m (M.pull π) th' sc' x t φ → Fib m M th sc (x.comp ρ) t (φ ≫ π) := by
  intro o _ g N' J b Mat κ R _ β v m Z M th sc R' _ ρ Z' π hp ⟨⟨I, p, hrep, hco⟩, hflat, hfib⟩
  obtain ⟨th', hrep', hc⟩ := RepBC.projRep_baseChange R R' _ ρ I _ _ _ _ π M th hrep hp
  have hw : ∀ h, (spMap ρ ≫ (sc h).left) ≫ Z.hom = 𝟙 _ ≫ spMap ρ := fun h => by
    rw [Category.assoc, Over.w (sc h), Category.id_comp]
    exact Category.comp_id _
  let sc' : Ix g (N' ^ 2) → (Out.baseOver (Sp R') ⟶ Z') := fun h =>
    Over.homMk (hp.lift (spMap ρ ≫ (sc h).left) (𝟙 _) (hw h)) (hp.lift_snd _ _ _)
  have hsc : ∀ h, (sc' h).left ≫ π = spMap ρ ≫ (sc h).left := fun h => hp.lift_fst _ _ _
  have hsc' : ∀ h, (sc' h).left ≫ Z'.hom = 𝟙 _ := fun h => hp.lift_snd _ _ _
  refine ⟨th', sc', ⟨⟨_, fun h a => ρ (p h a), hrep', fun h => (hc _ _ _).2 ?_⟩,
    MorphismProperty.of_isPullback (P := @Flat) hp hflat, ?_⟩, ?_⟩
  · rw [hsc]
    exact Coord.baseChange (hco h) ρ
  · intro K _ _ x s t ht
    obtain ⟨φ, h1, ⟨σ, hσ, h2⟩, h3, h4⟩ := hfib K (x.comp ρ) s t ((good_comp _ _ _).1 ht)
    have hw' : φ ≫ Z.hom = (t.A.hom ≫ spMap x) ≫ spMap ρ := by
      rw [h1.w, NearBuild.spMap_comp, Category.assoc]
    have e1 : hp.lift φ _ hw' ≫ π = φ := hp.lift_fst _ _ _
    have e2 : hp.lift φ _ hw' ≫ Z'.hom = t.A.hom ≫ spMap x := hp.lift_snd _ _ _
    generalize hp.lift φ _ hw' = φ' at e1 e2
    subst e1
    refine ⟨φ', IsPullback.of_right (by rw [← NearBuild.spMap_comp]; exact h1) e2 hp, ⟨σ, hσ, fun T _ y w => ?_⟩,
      (lbIso_pullPull_iff _ _ _ _).2 h3, fun h => ?_⟩
    · rw [h2 T y w, hc, Category.assoc, Category.assoc]
    · apply hp.hom_ext
      · rw [Category.assoc, h4, NearBuild.spMap_comp]
        erw [Category.assoc, Category.assoc, hsc]
      · rw [Category.assoc, e2, ← Category.assoc, Over.w (t.lab h ^ N')]
        erw [Category.assoc, hsc', Category.id_comp]
  · rintro K _ x s t φ ⟨h1, ⟨σ, hσ, h2⟩, h3, h4⟩
    refine ⟨by rw [NearBuild.spMap_comp]; exact h1.paste_horiz hp, ⟨σ, hσ, fun T _ y w => ?_⟩,
      (lbIso_pullPull_iff _ _ _ _).1 h3, fun h => ?_⟩
    · rw [h2 T y w, hc, Category.assoc, Category.assoc]
    · rw [← Category.assoc, h4, NearBuild.spMap_comp]
      erw [Category.assoc, Category.assoc, hsc]

end GlobalTheory.ZM.NearBuild
end
