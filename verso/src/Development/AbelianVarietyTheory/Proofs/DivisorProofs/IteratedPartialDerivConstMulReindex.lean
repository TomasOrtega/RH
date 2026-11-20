import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Treat this case separately. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem iterD_const_mul_reindex : ∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] (e : I ≃ J) (u : List I) (h : (J → ℂ) → ℂ) (A : ℂ) (z : I → ℂ), iterD u (fun z ↦ A * h (fun j ↦ z (e.symm j))) z = A * iterD (u.map e) h (fun j ↦ z (e.symm j)) := by
  intro I J _ _ _ _ e u h A z
  have key : ∀ v : List I, iterD v (fun z ↦ A * h (fun j ↦ z (e.symm j))) =
      fun z ↦ A * iterD (v.map e) h (fun j ↦ z (e.symm j)) := by
    intro v
    induction v with
    | nil => rfl
    | cons i v ih =>
      funext z
      show partialD i (iterD v _) z = A * partialD (e i) (iterD (v.map e) h) _
      rw [ih]
      simp only [partialD, lineDeriv]
      have hpath : (fun t : ℂ ↦ A * iterD (v.map e) h (fun j ↦ (z + t • (Pi.single i 1 : I → ℂ)) (e.symm j))) =
          fun t ↦ A * iterD (v.map e) h ((fun j ↦ z (e.symm j)) + t • (Pi.single (e i) 1 : J → ℂ)) := by
        funext t
        congr 2
        funext j
        simp [Pi.single_apply, Equiv.symm_apply_eq]
      rw [hpath, deriv_const_mul_field]
  exact congrFun (key u) z

end GlobalTheory.HilbFam
