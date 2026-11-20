import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

/- English proof (translation)
Introduce `p f hp κ _ _ φ hφ A A' _ _ ψ hpull h`. Take `⟨hpb, hmul⟩` from `hpull`. Establish `hκ : ((p : ℕ) : Γ(Sp κ, ⊤)) = 0`. Establish `e` using `congrArg (Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom (CharP.cast_eq_zero κ p)`. Rewrite `e` using `[map_natCast, map_zero]`.

Conclude with `e`. Establish `hfrκ : GlobalTheory.SS.FrobField.absFrob (Sp κ) p f hp hκ = spMap φ` using `GlobalTheory.SS.FrobField.absFrob_spec κ p f hp hκ φ hφ`. Establish `hsq : GlobalTheory.SS.FrobField.absFrob A.left p f hp h ≫ A.hom = A.hom ≫ spMap φ`. Rewrite using `[GlobalTheory.SS.FrobField.absFrob_nat A.hom p f hp h hκ, hfrκ]`. Set `F : A ⟶ A'` to `Over.homMk (hpb.lift (GlobalTheory.SS.FrobField.absFrob A.left p f hp h) A.hom hsq) (hpb.lift_snd _ _ _)`.

Establish `hFψ : F.left ≫ ψ = GlobalTheory.SS.FrobField.absFrob A.left p f hp h` using `hpb.lift_fst _ _ _`. Establish `hTz : ∀ T : Over (Sp κ), ((p : ℕ) : Γ(T.left, ⊤)) = 0` using `fun T => GlobalTheory.SS.FrobField.cast_zero_of_hom T.hom hκ`. Establish `key : ∀ (T : Over (Sp κ)) (x : T ⟶ A), (x ≫ F).left ≫ ψ = GlobalTheory.SS.FrobField.absFrob T.left p f hp (hTz T) ≫ x.left`. Introduce `T x`. Rewrite using `[Over.comp_left, Category.assoc, hFψ]`.

Conclude with `(GlobalTheory.SS.FrobField.absFrob_nat x.left p f hp (hTz T) h).symm`. Set `Fr : ∀ T : Over (Sp κ), Over.mk (T.hom ≫ spMap φ) ⟶ T` to `fun T => Over.homMk (GlobalTheory.SS.FrobField.absFrob T.left p f hp (hTz T)) (by`. Simplify using `only [Over.mk_hom]`. Rewrite using `[GlobalTheory.SS.FrobField.absFrob_nat T.hom p f hp (hTz T) hκ, hfrκ])`. Use `haveI hF : IsMonHom F := by`.

Apply `isMonHom_of_mul F` to reduce the goal to its premises. Introduce `T x y`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `hpb.hom_ext` to reduce the goal to its premises. Rewrite using `[← hmul T (x ≫ F) (y ≫ F) (Fr T ≫ x) (Fr T ≫ y) (by rw [key]; rfl) (by rw [key]; rfl), ← MonObj.comp_mul, key, Over.comp_left]`.

Both sides reduce to the same expression. Rewrite using `[Over.w, Over.w]`. Use `⟨F, hF, hFψ, fun T g => ?_⟩` and prove the remaining obligations. Establish `hone : (1 : T ⟶ A').left ≫ ψ = GlobalTheory.SS.FrobField.absFrob T.left p f hp (hTz T) ≫ (1 : T ⟶ A).left`. Rewrite using `[← MonObj.one_comp (X := T) F, key]`.

Prove the components needed by the constructor for the conclusion. Introduce `hg h'`. Establish `e` using `congrArg (fun k => k.left ≫ ψ) hg`. Rewrite `e` using `[key, hone]`. Conclude with `e`.

Introduce `hk`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `hpb.hom_ext` to reduce the goal to its premises. Rewrite using `[key, hone]`. Conclude with `hk (hTz T)`.

Rewrite using `[Over.w, Over.w]`.
-/
theorem UpperTheory.Gal.crystallineComparison.Mod.frobHom_of :
    FrobHom := by
  intro p f hp κ _ _ φ hφ A A' _ _ ψ hpull h
  obtain ⟨hpb, hmul⟩ := hpull
  have hκ : ((p : ℕ) : Γ(Sp κ, ⊤)) = 0 := by
    have e := congrArg (Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom (CharP.cast_eq_zero κ p)
    rw [map_natCast, map_zero] at e
    exact e
  have hfrκ : GlobalTheory.SS.FrobField.absFrob (Sp κ) p f hp hκ = spMap φ :=
    GlobalTheory.SS.FrobField.absFrob_spec κ p f hp hκ φ hφ
  have hsq : GlobalTheory.SS.FrobField.absFrob A.left p f hp h ≫ A.hom = A.hom ≫ spMap φ := by
    rw [GlobalTheory.SS.FrobField.absFrob_nat A.hom p f hp h hκ, hfrκ]
  let F : A ⟶ A' := Over.homMk (hpb.lift (GlobalTheory.SS.FrobField.absFrob A.left p f hp h) A.hom hsq)
    (hpb.lift_snd _ _ _)
  have hFψ : F.left ≫ ψ = GlobalTheory.SS.FrobField.absFrob A.left p f hp h := hpb.lift_fst _ _ _
  have hTz : ∀ T : Over (Sp κ), ((p : ℕ) : Γ(T.left, ⊤)) = 0 := fun T =>
    GlobalTheory.SS.FrobField.cast_zero_of_hom T.hom hκ
  have key : ∀ (T : Over (Sp κ)) (x : T ⟶ A),
      (x ≫ F).left ≫ ψ = GlobalTheory.SS.FrobField.absFrob T.left p f hp (hTz T) ≫ x.left := by
    intro T x
    rw [Over.comp_left, Category.assoc, hFψ]
    exact (GlobalTheory.SS.FrobField.absFrob_nat x.left p f hp (hTz T) h).symm
  let Fr : ∀ T : Over (Sp κ), Over.mk (T.hom ≫ spMap φ) ⟶ T := fun T =>
    Over.homMk (GlobalTheory.SS.FrobField.absFrob T.left p f hp (hTz T)) (by
      simp only [Over.mk_hom]
      rw [GlobalTheory.SS.FrobField.absFrob_nat T.hom p f hp (hTz T) hκ, hfrκ])
  haveI hF : IsMonHom F := by
    apply isMonHom_of_mul F
    intro T x y
    apply Over.OverMorphism.ext
    apply hpb.hom_ext
    · rw [← hmul T (x ≫ F) (y ≫ F) (Fr T ≫ x) (Fr T ≫ y) (by rw [key]; rfl) (by rw [key]; rfl),
        ← MonObj.comp_mul, key, Over.comp_left]
      rfl
    · rw [Over.w, Over.w]
  refine ⟨F, hF, hFψ, fun T g => ?_⟩
  have hone : (1 : T ⟶ A').left ≫ ψ = GlobalTheory.SS.FrobField.absFrob T.left p f hp (hTz T) ≫ (1 : T ⟶ A).left := by
    rw [← MonObj.one_comp (X := T) F, key]
  constructor
  · intro hg h'
    have e := congrArg (fun k => k.left ≫ ψ) hg
    rw [key, hone] at e
    exact e
  · intro hk
    apply Over.OverMorphism.ext
    apply hpb.hom_ext
    · rw [key, hone]
      exact hk (hTz T)
    · rw [Over.w, Over.w]
