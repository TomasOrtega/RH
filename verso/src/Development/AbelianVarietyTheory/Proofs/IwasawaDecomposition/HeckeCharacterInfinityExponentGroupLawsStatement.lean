import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterInfinityExponentGroupLaws
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FHeckeCharacterInfinityExponentGroupLaws.lean&line=93#L93)
-/
theorem _root_.GlobalTheory.T.heckeCharacter_infinityExponent_group_laws : ∀ D : D7, (∃ C : Subgroup (IdC D), ∀ χ, χ ∈ C ↔ IsHC D χ) ∧ (∀ (χ : IdC D) τ a a', HasInfExp D χ τ a → HasInfExp D χ τ a' → a = a') ∧ ∀ (χ χ' : IdC D) τ a a', HasInfExp D χ τ a → HasInfExp D χ' τ a' → HasInfExp D (χ * χ') τ (a + a') := by
  first | exact @GlobalTheory.Mem.HeckeExp.hecke_exp_laws | exact GlobalTheory.Mem.HeckeExp.hecke_exp_laws | (intros; apply GlobalTheory.Mem.HeckeExp.hecke_exp_laws <;> assumption)
