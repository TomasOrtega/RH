import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckePolyMulCentralIdempotentMulGenericProjector
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvRoots
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCentralGroupAlgebraIdempotentUniversal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ISupEigenspaceEqTopOfAeval
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FHeckePolyMulCentralIdempotentMulGenericProjector.lean&line=92#L92)
-/
theorem _root_.GlobalTheory.T.heckePoly_mul_centralIdempotent_mul_genericProjector : ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (j k : ℕ) (P : PlE D.host), 1 ≤ j → j ≤ D.R.m → 1 ≤ k → k ≤ D.R.r →
    IsSplitPl D.host P → P ∉ In.Sb → phiLop D S In j k P * eLop D S j * piLop D S In.θ j = 0 := by
  first | exact @GlobalTheory.HeightCounting.FormsStep.phiLop_eLop_piLop | exact GlobalTheory.HeightCounting.FormsStep.phiLop_eLop_piLop | (intros; apply GlobalTheory.HeightCounting.FormsStep.phiLop_eLop_piLop <;> assumption)
