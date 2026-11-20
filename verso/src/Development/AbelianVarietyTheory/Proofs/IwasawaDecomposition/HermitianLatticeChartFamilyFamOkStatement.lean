import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianLatticeChartFamilyFamOk
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mem.Col2.fam_ok` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FHermitianLatticeChartFamilyFamOk.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.hermitianLatticeChartFamily_fam_ok : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n), FOk emb σ → S.Ok → (S.fam emb lam).Ok := by
  first | exact @GlobalTheory.Mem.Col2.fam_ok | exact GlobalTheory.Mem.Col2.fam_ok | (intros; apply GlobalTheory.Mem.Col2.fam_ok <;> assumption)
