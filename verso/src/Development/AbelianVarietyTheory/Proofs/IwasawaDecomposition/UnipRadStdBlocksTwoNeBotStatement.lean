import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnipRadStdBlocksTwoNeBot
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FUnipRadStdBlocksTwoNeBot.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.unipRad_stdBlocks_two_ne_bot' : ∀ (R : Type) [CommRing R] [Nontrivial R] (n a b : ℕ) (h : ∑ i, ![a, b] i = n), 0 < a → 0 < b → unipRad R (stdBlocks ![a, b] h) ≠ ⊥ := by
  first | exact @GlobalTheory.unipRad_stdBlocks_two_ne_bot | exact GlobalTheory.unipRad_stdBlocks_two_ne_bot | (intros; apply GlobalTheory.unipRad_stdBlocks_two_ne_bot <;> assumption)
