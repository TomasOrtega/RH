import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalLevelVectorLaws
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mem.Col2.fv_te_laws` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FLevelFunctionalLevelVectorLaws.lean&line=74#L74)
-/
theorem _root_.GlobalTheory.T.levelFunctional_levelVector_laws : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n} {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (T : ℕ), S.Ok → A.Ok T → (∀ P c (x : A.N c.1 (S.rep c)), A.fv P c (Submodule.Quotient.mk x) = A.f c.1 (S.rep c) P x) ∧ (∀ P c, A.fv P c ≠ 0) ∧ ∀ P c, A.te T P c ≠ 0 := by
  first | exact @GlobalTheory.Mem.Col2.fv_te_laws | exact GlobalTheory.Mem.Col2.fv_te_laws | (intros; apply GlobalTheory.Mem.Col2.fv_te_laws <;> assumption)
