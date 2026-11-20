import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexFormsFiniteDimensional
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mem.Col2.GStep.fi_finiteDimensional` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FComplexFormsFiniteDimensional.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.complexForms_finiteDimensional : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n), FOk emb σ → S.Ok → FiniteDimensional ℂ (S.Fi emb σ lam) := by
  first | exact @GlobalTheory.Mem.Col2.GStep.fi_finiteDimensional | exact GlobalTheory.Mem.Col2.GStep.fi_finiteDimensional | (intros; apply GlobalTheory.Mem.Col2.GStep.fi_finiteDimensional <;> assumption)
