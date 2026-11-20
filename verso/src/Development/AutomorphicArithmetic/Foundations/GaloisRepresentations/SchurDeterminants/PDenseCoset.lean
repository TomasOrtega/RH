import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PairSplit

noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

private def latt {O K ι : Type} [CommRing O] [Field K] (τ : ι → (O →+* K)) (N : O) (k : ℕ) :
    AddSubgroup (ι × Fin k → K) where
  carrier := {x | ∃ β : Fin k → O, x = pt τ (fun s => N * β s)}
  add_mem' := by
    rintro _ _ ⟨β, rfl⟩ ⟨β', rfl⟩
    refine ⟨β + β', ?_⟩
    funext p
    simp [pt, mul_add]
  zero_mem' := by
    refine ⟨0, ?_⟩
    funext p
    simp [pt]
  neg_mem' := by
    rintro _ ⟨β, rfl⟩
    refine ⟨-β, ?_⟩
    funext p
    simp [pt]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem denseCoset_of : DenseSub → SpanTop → DenseOff → DenseCoset := by
  intro hS hT hO O K ι _ _ _ _ τ hτ N hN k a Q hQ
  have hspan : Submodule.span K ((latt τ N k : AddSubgroup (ι × Fin k → K)) : Set (ι × Fin k → K)) = ⊤ :=
    hT O K ι τ hτ N hN k
  have hd := hS K (ι × Fin k) (latt τ N k) (pt τ a) hspan
  have hd2 := hO K (ι × Fin k) _ hd Q hQ
  intro P hP
  apply hd2
  rintro x ⟨hx, hxQ⟩
  obtain ⟨β, hβ⟩ : ∃ β : Fin k → O, x - pt τ a = pt τ (fun s => N * β s) := hx
  have hxe : x = pt τ (fun s => a s + N * β s) := by
    rw [sub_eq_iff_eq_add.mp hβ]
    funext p
    simp [pt, add_comm]
  refine hP x ⟨fun s => a s + N * β s, fun s => ?_, ?_, hxe⟩
  · simp
  · rw [← hxe]
    exact hxQ

end UpperTheory.Gal.Schur
