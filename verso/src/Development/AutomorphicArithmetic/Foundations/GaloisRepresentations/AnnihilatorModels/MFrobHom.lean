import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
