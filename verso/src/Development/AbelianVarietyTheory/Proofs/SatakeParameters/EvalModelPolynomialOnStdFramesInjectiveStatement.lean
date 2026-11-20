import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvalModelPolynomialOnStdFramesInjective
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TwV.DelA.eq_zero_of_ev1_eq_zero_on_frames` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FEvalModelPolynomialOnStdFramesInjective.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.evalModelPolynomialOnStdFrames_injective : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (R : XR (X.Pj i) ℂ), (∀ f : Fr1 D n, ev1 X D pos i h R f = 0) → R = 0 := by
  first | exact @GlobalTheory.TwV.DelA.eq_zero_of_ev1_eq_zero_on_frames | exact GlobalTheory.TwV.DelA.eq_zero_of_ev1_eq_zero_on_frames | (intros; apply GlobalTheory.TwV.DelA.eq_zero_of_ev1_eq_zero_on_frames <;> assumption)
