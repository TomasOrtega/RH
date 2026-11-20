import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselBigCellPointVectorEqBessel
import Formalism.HermitianCurvature.StatementTBB
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.vec_bigPt_eq_bessel` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FBesselBigCellPointVectorEqBessel.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.besselBigCellPoint_vector_eq_bessel : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : Fin (P.r + 1) → ℂ), (¬ ((∀ a, c a ≠ 0) ∧ TBB.TTp p < Complex.normSq (c (Fin.last P.r))) → p.V H (TBB.bigPt P.r c) = 0) ∧ (((∀ a, c a ≠ 0) ∧ TBB.TTp p < Complex.normSq (c (Fin.last P.r))) → 0 < TBB.Gp p (TBB.bigPt P.r c) ∧ ∀ γ ∈ B.GV P.k P.r, Zhat P.k P.r p.T.base.z p.T.base.z' γ = D.ptMatN (TBB.bigPt P.r c) (P.r + 1) → D.IsDFrame p.T.base p.ν' p.m₀ γ → γ ∈ B.GPos p.T.base ∧ p.V H (TBB.bigPt P.r c) = B.JF p.T.base H γ) := by
  first | exact @GlobalTheory.vec_bigPt_eq_bessel | exact GlobalTheory.vec_bigPt_eq_bessel | (intros; apply GlobalTheory.vec_bigPt_eq_bessel <;> assumption)
