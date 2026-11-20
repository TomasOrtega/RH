import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigencharacterOfSummandCharZero

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.TP.Sub.cpFacts_holds :
    CpFacts := by
  intro Γ k _ _ a b
  refine ⟨fun r s g => GlobalTheory.EigTwist.charpoly_sumRep r s g, ?_, ?_⟩
  · intro c g
    simp [cp, rk1, Matrix.charpoly, Matrix.charmatrix, Matrix.det_unique]
  · rintro r r' ⟨u, hu⟩ g
    simp only [cp, hu, Units.val_mul]
    rw [Matrix.coe_units_inv]
    exact Matrix.charpoly_units_conj u (r g : Matrix (Fin a) (Fin a) k)
