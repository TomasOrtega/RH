import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelFamilyCharacterExponent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsLevelFamilyCharacterExponent.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_levelFamily_character_exponent : ∀ {X : Fields} {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 X.E))} (Λ : LevFam X.E X.K n SG), ∃ m : ℕ, 0 < m ∧ ∀ h, Λ.chr h ^ m = 1 := by
  first | exact @GlobalTheory.Mem.Col2.TopCh.levFam_chr_exp | exact GlobalTheory.Mem.Col2.TopCh.levFam_chr_exp | (intros; apply GlobalTheory.Mem.Col2.TopCh.levFam_chr_exp <;> assumption)
