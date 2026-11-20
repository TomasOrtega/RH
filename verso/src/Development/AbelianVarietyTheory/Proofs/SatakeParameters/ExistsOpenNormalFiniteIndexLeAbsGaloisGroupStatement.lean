import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenNormalFiniteIndexLeAbsGaloisGroup
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ArthurClozel
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FExistsOpenNormalFiniteIndexLeAbsGaloisGroup.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.exists_openNormal_finiteIndex_le_absGaloisGroup : ∀ (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω] (U : Subgroup (G F Ω)), IsOpen (U : Set (G F Ω)) → ∃ N : Subgroup (G F Ω), N.Normal ∧ IsOpen (N : Set (G F Ω)) ∧ N.FiniteIndex ∧ N ≤ U := by
  first | exact @GlobalTheory.OpenNormal.exists_open_normal_le | exact GlobalTheory.OpenNormal.exists_open_normal_le | (intros; apply GlobalTheory.OpenNormal.exists_open_normal_le <;> assumption)
