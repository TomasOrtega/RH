import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory

/- English proof (translation)
Consider separately whether the proposition holds or fails. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
theorem exists_nontrivial_addChar_eq_of_ne (p : ℕ) [Fact p.Prime] (Pr : Prop) (φ : AddChar (ZMod p) ℂ) (h : Pr → φ ≠ 1) :
    ∃ ψ' : AddChar (ZMod p) ℂ, ψ' ≠ 1 ∧ (Pr → ψ' = φ) := by
  by_cases hP : Pr
  · exact ⟨φ, h hP, fun _ => rfl⟩
  · refine ⟨ZMod.stdAddChar, ?_, fun h' => absurd h' hP⟩
    intro h1
    have hprim := ZMod.isPrimitive_stdAddChar p
    apply hprim (a := 1) one_ne_zero
    rw [AddChar.mulShift_one, h1]

end GlobalTheory
