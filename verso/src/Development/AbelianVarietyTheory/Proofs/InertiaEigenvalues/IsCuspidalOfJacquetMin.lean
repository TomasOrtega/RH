import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.JacMinCusp

open GlobalTheory.SmGL.CuspMax Matrix
open scoped TensorProduct

/- English proof (translation)
Extract witnesses or component facts from the available result. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules.
-/
theorem blk_two_stdSum {a b n : ℕ} (h : a + b = n) (i : Fin n) :
    blk (two (stdSum h)) i = decide (a ≤ (i : ℕ)) := by
  obtain ⟨x, rfl⟩ := (stdSum h).surjective i
  rcases x with x | x
  · rw [← two_false, blk_apply]; simp [x.2]
  · rw [← two_true, blk_apply]; simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem blk_two_stdSum_lt {a b n : ℕ} (h : a + b = n) (i j : Fin n) :
    blk (two (stdSum h)) i < blk (two (stdSum h)) j ↔ (i : ℕ) < a ∧ a ≤ (j : ℕ) := by
  rw [blk_two_stdSum, blk_two_stdSum]
  by_cases h1 : a ≤ (i : ℕ) <;> by_cases h2 : a ≤ (j : ℕ) <;> simp [h1, h2] <;> omega

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem mem_unipRad_two_iff {R : Type} [CommRing R] {a b n : ℕ} (h : a + b = n) {g : GL (Fin n) R} :
    g ∈ unipRad R (two (stdSum h)) ↔ ∀ i j : Fin n, ¬ ((i : ℕ) < a ∧ a ≤ (j : ℕ)) →
      (g : Matrix (Fin n) (Fin n) R) i j = (1 : Matrix (Fin n) (Fin n) R) i j := by
  rw [mem_unipRad_iff_entries]
  simp only [blk_two_stdSum_lt]

end GlobalTheory.JacMinCusp
