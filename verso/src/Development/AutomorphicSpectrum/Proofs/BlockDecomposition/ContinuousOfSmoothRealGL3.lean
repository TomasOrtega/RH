import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.CasselmanShalikaStandardVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BndIUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrablePowerWeightUnits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization

namespace GlobalTheory.CompanionTheory.GL2Factorization

/- English proof (translation)
Introduce `W hW`. Establish `hc : ContinuousOn (ext W) {m : M3 | (Matrix.of m).det ≠ 0}` using `hW.continuousOn`. Establish `hv : Continuous fun g : GL (Fin 3) ℝ => (Matrix.of.symm g.val : M3)` using `(Units.continuous_val : Continuous fun g : GL (Fin 3) ℝ => (g.val : Matrix (Fin 3) (Fin 3) ℝ))`. Establish `hm : ∀ g : GL (Fin 3) ℝ, (Matrix.of.symm g.val : M3) ∈ {m : M3 | (Matrix.of m).det ≠ 0}`. Introduce `g`.

Establish `: (g.val).det ≠ 0` using `((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero`. Simplify using `using this`. Establish `he : W = fun g => ext W (Matrix.of.symm g.val : M3)`. Use function extensionality and compare the values at `g`. Establish `h : (Matrix.of (Matrix.of.symm g.val : M3)).det ≠ 0` using `hm g`.

Rewrite using `[Ad3.ext, dif_pos h]`. Use `congr 1`. Apply `Units.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Rewrite using `[he]`.

Conclude with `hc.comp_continuous hv hm`.
-/
theorem smoothR_continuous : ∀ W : GL (Fin 3) ℝ → ℂ, SmoothR W → Continuous W := by
  intro W hW
  have hc : ContinuousOn (ext W) {m : M3 | (Matrix.of m).det ≠ 0} := hW.continuousOn
  have hv : Continuous fun g : GL (Fin 3) ℝ => (Matrix.of.symm g.val : M3) :=
    (Units.continuous_val : Continuous fun g : GL (Fin 3) ℝ => (g.val : Matrix (Fin 3) (Fin 3) ℝ))
  have hm : ∀ g : GL (Fin 3) ℝ, (Matrix.of.symm g.val : M3) ∈ {m : M3 | (Matrix.of m).det ≠ 0} := by
    intro g
    have : (g.val).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
    simpa using this
  have he : W = fun g => ext W (Matrix.of.symm g.val : M3) := by
    funext g
    have h : (Matrix.of (Matrix.of.symm g.val : M3)).det ≠ 0 := hm g
    rw [Ad3.ext, dif_pos h]
    congr 1
    apply Units.ext
    simp
  rw [he]
  exact hc.comp_continuous hv hm

end GlobalTheory.CompanionTheory.GL2Factorization
