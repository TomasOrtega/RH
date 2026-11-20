import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlCornerEmbeddingUpperUnitriangularSuperDiagonal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FGlCornerEmbeddingUpperUnitriangularSuperDiagonal.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.glCornerEmbedding_upperUnitriangular_superDiagonalSum : ∀ (R : Type) [CommRing R] (m : ℕ) (u : GL (Fin m) R), u ∈ unipB R (Fin m) → corner u ∈ unipB R (Fin (m + 1)) ∧ superDiag (corner u) = superDiag u := by
  first | exact @GlobalTheory.CornerUnip.corner_unipB_superDiag | exact GlobalTheory.CornerUnip.corner_unipB_superDiag | (intros; apply GlobalTheory.CornerUnip.corner_unipB_superDiag <;> assumption)
