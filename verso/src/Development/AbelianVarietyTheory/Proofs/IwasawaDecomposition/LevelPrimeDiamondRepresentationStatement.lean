import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDiamondRepresentation
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FLevelPrimeDiamondRepresentation.lean&line=97#L97)
-/
theorem _root_.GlobalTheory.T.levelPrimeDiamond_representation : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks} (I : ChainIn E K ι R) (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R), FOk emb σ → ∀ (hI : I.Ok), J.Ok → J.LawDiaOne emb σ ∧ J.LawDiaMul emb σ := by
  first | exact @GlobalTheory.Mem.Col2.DiaRep.diamond_rep | exact GlobalTheory.Mem.Col2.DiaRep.diamond_rep | (intros; apply GlobalTheory.Mem.Col2.DiaRep.diamond_rep <;> assumption)
