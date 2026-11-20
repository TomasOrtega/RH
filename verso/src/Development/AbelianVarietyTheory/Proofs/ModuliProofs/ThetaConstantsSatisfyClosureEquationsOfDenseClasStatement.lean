import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaConstantsSatisfyClosureEquationsOfDenseClas
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FModuliProofs%2FThetaConstantsSatisfyClosureEquationsOfDenseClas.lean&line=97#L97)
-/
theorem _root_.GlobalTheory.T.thetaConstants_satisfy_closure_equations_of_dense_class : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g n N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (R : Type) [CommRing R] (β : o →+* R) (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R), 2 ≤ n → n ∣ N' → Odd N' → IsReduced S → Dense (fromSet em C t) → IsOpenImmersion x → x ≫ s = spMap β → t.HasTh x v → InMM n N' (thIdeal em C) β v := by
  first | exact @GlobalTheory.ZM.inMM_of_dense_fromSet | exact GlobalTheory.ZM.inMM_of_dense_fromSet | (intros; apply GlobalTheory.ZM.inMM_of_dense_fromSet <;> assumption)
