import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularFunctionsBoundClosePoints
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar Formalism.BasicNotions GlobalTheory.TrueGeo

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HtLocBound.htLoc` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRegularFunctionsBoundClosePoints.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.regular_functions_bound_close_points : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y), Y.ample A.D →
  (∃ (M : Model Y) (L : GlobalTheory.HermLB M.p) (q : ℕ+), A.Induced M L q 0) → (∀ σ, C.mSmooth Y σ A.D (A.m σ)) →
  ∃ (N : ℕ) (f : Fin N → Y.Fn), (∃ U : Y.X.Opens, (U : Set Y.X).Nonempty ∧ ∀ x ∈ U, ∀ i, RegAt x (f i)) ∧
    ∀ (a : ℝ) (b : HeightOneSpectrum (𝓞 F) → ℝ), (Function.support b).Finite →
      ∃ K : ℝ, ∀ x : Y.X, IsClosed ({x} : Set Y.X) → (∀ i, RegAt x (f i)) →
        (∀ (σ : F →+* ℂ) (z : Pts Y σ), under z = x → ∀ i, ‖ratVal (f i) z‖ ≤ a) →
        (∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y), below y.1 = x → ∀ i,
          e.w (valAt y.1 (f i)) ≤ Real.exp (b v)) →
        A.ht x ≤ K := by
  first | exact @GlobalTheory.HtLocBound.htLoc | exact GlobalTheory.HtLocBound.htLoc | (intros; apply GlobalTheory.HtLocBound.htLoc <;> assumption)
