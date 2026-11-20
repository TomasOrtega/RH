import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusOfPadic

noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Simplify using the standard rewrite rules. Treat this case separately. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

By extensionality, compare the relevant components. Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Treat this case separately. Rewrite the conclusion using the stated equalities.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem frame_psi_eq_phiInv : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ) (ψ : RL p O Λ →+* RL p O Λ) (e : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)), IsPsi ψ → (∀ (i : Fin N) (l : Λ), ∃ t : Fin h → ℤ_[p], e (Pi.single i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l)) = fun j => ofPadic p O (t j)) → ∀ w, e (fun i => ψ (w i)) = fun j => phiInv p O (e w j) := by
  intro p _ O _ _ _ Λ _ _ N h ψ e hψ ht w
  have key : ∀ (i : Fin N) (r : RL p O Λ),
      e (Pi.single i (ψ r)) = fun j => phiInv p O (e (Pi.single i r) j) := by
    intro i r
    induction r using TensorProduct.induction_on with
    | zero => funext j; simp
    | tmul a l =>
      rw [hψ]
      have h1 : ∀ b : Ainf p O, (Pi.single i (b ⊗ₜ[ℤ_[p]] l) : Fin N → RL p O Λ) =
          b • Pi.single i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l) := by
        intro b
        ext k
        rcases eq_or_ne k i with rfl | hk
        · simp [TensorProduct.smul_tmul']
        · simp [hk]
      obtain ⟨t, ht'⟩ := ht i l
      rw [h1 (phiInv p O a), h1 a, map_smul, map_smul, ht']
      funext j
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, PsiPhi.phiInv_ofPadic]
    | add x y hx hy =>
      rw [map_add ψ, Pi.single_add, map_add e, hx, hy, Pi.single_add, map_add e]
      funext j
      simp only [Pi.add_apply, map_add]
  have hw : (fun i => ψ (w i)) = ∑ i, Pi.single i (ψ (w i)) := (Finset.univ_sum_single _).symm
  rw [hw, map_sum]
  conv_rhs => rw [← Finset.univ_sum_single w, map_sum]
  funext j
  simp only [Finset.sum_apply, key, map_sum]

end GlobalTheory.DetInv
