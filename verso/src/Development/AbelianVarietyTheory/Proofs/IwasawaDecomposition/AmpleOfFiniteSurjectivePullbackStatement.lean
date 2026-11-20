import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmpleOfFiniteSurjectivePullback
import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FAmpleOfFiniteSurjectivePullback.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.ample_of_finite_surjective_pullback : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X), AlgebraicGeometry.IsNoetherian X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X →
    IsFinite f → Function.Surjective f → ∀ L : ReciprocityTheory.ChartRestriction.G.Semi.LB X, L.IsLB → GlobalTheory.IsAmpleLB (L.pull f) → GlobalTheory.IsAmpleLB L := by
  first | exact @GlobalTheory.NormalDescent.isAmpleLB_of_pull | exact GlobalTheory.NormalDescent.isAmpleLB_of_pull | (intros; apply GlobalTheory.NormalDescent.isAmpleLB_of_pull <;> assumption)
