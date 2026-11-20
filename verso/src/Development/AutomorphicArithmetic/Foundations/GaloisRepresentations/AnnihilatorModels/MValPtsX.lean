import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Introduce a local definition for the expression. Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.crystallineComparison.Mod.valPtsX_of :
    ValPtsX := by
  intro S K h hp V _ _ _ z
  have : IsProper h := hp
  constructor
  · intro g g' hg hg' e
    have c : CommSq (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) ≫ g)
        (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) h z :=
      ⟨by rw [Category.assoc, hg]⟩
    let Q : ValuativeCommSq h := ⟨V, FractionRing V, _, z, c⟩
    have hs : Subsingleton Q.commSq.LiftStruct := IsSeparated.valuativeCriterion h Q
    let l₁ : Q.commSq.LiftStruct := ⟨g, rfl, hg⟩
    let l₂ : Q.commSq.LiftStruct := ⟨g', e.symm, hg'⟩
    exact congrArg CommSq.LiftStruct.l (Subsingleton.elim l₁ l₂)
  · intro g hg
    have c : CommSq g (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) h z := ⟨hg⟩
    let Q : ValuativeCommSq h := ⟨V, FractionRing V, g, z, c⟩
    have hu : (ValuativeCriterion.Existence ⊓ @QuasiCompact) h := by
      rw [← UniversallyClosed.eq_valuativeCriterion]
      infer_instance
    obtain ⟨l, h₁, h₂⟩ := (hu.1 Q).exists_lift
    exact ⟨l, h₂, h₁⟩
