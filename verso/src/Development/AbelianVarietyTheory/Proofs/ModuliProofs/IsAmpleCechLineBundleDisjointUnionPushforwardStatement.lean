import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAmpleCechLineBundleDisjointUnionPushforward
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFramesOfAmpFrames
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ModelSum.UnionAmple.sumLB_isLB_ampleFam` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FModuliProofs%2FIsAmpleCechLineBundleDisjointUnionPushforward.lean&line=200#L200)
-/
theorem _root_.GlobalTheory.T.isAmpleCechLineBundle_disjointUnion_pushforward : ∀ (Z Z₁ Z₂ : Scheme.{0}) (f₁ : Z₁ ⟶ Z) (f₂ : Z₂ ⟶ Z) [IsOpenImmersion f₁] [IsOpenImmersion f₂] (A₁ : LB Z₁) (A₂ : LB Z₂), IsCompl (Set.range f₁) (Set.range f₂) → A₁.IsLB → A₂.IsLB → AmpleFam A₁ → AmpleFam A₂ → (sumLB (pushLB f₁ A₁) (pushLB f₂ A₂)).IsLB ∧ AmpleFam (sumLB (pushLB f₁ A₁) (pushLB f₂ A₂)) := by
  first | exact @GlobalTheory.ModelSum.UnionAmple.sumLB_isLB_ampleFam | exact GlobalTheory.ModelSum.UnionAmple.sumLB_isLB_ampleFam | (intros; apply GlobalTheory.ModelSum.UnionAmple.sumLB_isLB_ampleFam <;> assumption)
