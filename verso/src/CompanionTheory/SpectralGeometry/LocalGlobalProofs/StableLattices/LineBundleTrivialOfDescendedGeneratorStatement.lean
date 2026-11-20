import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LineBundleTrivialOfDescendedGenerator
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FlatDescentOfUnitsStatement
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.FnDesc.triv_of_invariant_gen` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FLineBundleTrivialOfDescendedGenerator.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.line_bundle_trivial_of_descended_generator : ∀ {P Q : Scheme.{0}} (f : P ⟶ Q), Flat f → LocallyOfFinitePresentation f → Surjective f →
    ∀ (D : LB Q), D.IsLB → ∀ (t : LB.Gen (D.pull f)), t.IsGen →
      (∀ (W : Scheme.{0}) (a b : W ⟶ P), a ≫ f = b ≫ f → ∀ (w : W) (i : D.ι), f (a w) ∈ D.U i →
        gm a w ((D.pull f).U fun _ => i) (t.s fun _ => i) = gm b w ((D.pull f).U fun _ => i) (t.s fun _ => i)) →
      Triv D := by
  first | exact @GlobalTheory.CompanionTheory.FnDesc.triv_of_invariant_gen | exact GlobalTheory.CompanionTheory.FnDesc.triv_of_invariant_gen | (intros; apply GlobalTheory.CompanionTheory.FnDesc.triv_of_invariant_gen <;> assumption)
