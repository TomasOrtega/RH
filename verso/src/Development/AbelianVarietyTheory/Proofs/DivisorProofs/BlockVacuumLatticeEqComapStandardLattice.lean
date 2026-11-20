import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkLat
import Formalism.LocalToGlobal.InertKernelTheory.StatementAlg
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

namespace GlobalTheory.BaseVacuum

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem gC_xv {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (w : Fin 4 × D.what₂.Tau) :
    B.gC (fun w' => TaylorLogMetric.embT D w'.2 (xv B w w'.1)) = Pi.single w 1 := by
  rw [B.gC_spec]
  funext w'
  simp only [xv, LinearEquiv.apply_symm_apply]
  by_cases h : w' = w
  · subst h; simp
  · simp [h]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem blk_embV_putB (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {n n' : ℕ} (k k' : Fin n' × Fin n)
    (x : Fin 4 → D.host.E) :
    blk D k' (TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) (putB D k x) : TaylorLogMetric.VC D (n * 2) (n' * 2)) =
      if k' = k then (fun w => TaylorLogMetric.embT D w.2 (x w.1)) else (0 : Fin 4 × D.what₂.Tau → ℂ) := by
  funext w
  simp only [blk, TaylorLogMetric.embV, TaylorLogMetric.tor0, putB, Prod.mk.eta, Equiv.symm_apply_apply]
  by_cases h : k' = k
  · simp [h]
  · simp [h]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails.

Establish an intermediate fact. Substitute using the available equality. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
theorem phi_embV_bas {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (n n' : ℕ)
    (j : Fin (TaylorLogMetric.fF D * (n * 2) * (n' * 2))) :
    phi B n n' (TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) (bas B n n' j)) = Pi.single (ixE D n n' j) 1 := by
  funext p
  rw [phi_apply, bas, blk_embV_putB]
  by_cases h : p.1 = (ixE D n n' j).1
  · rw [if_pos h, gC_xv]
    by_cases h2 : p.2 = (ixE D n n' j).2
    · have : p = ixE D n n' j := Prod.ext h h2
      subst this; simp
    · have : p ≠ ixE D n n' j := fun e => h2 (by rw [e])
      simp [h2, this]
  · rw [if_neg h, B.gC.map_zero]
    have : p ≠ ixE D n n' j := fun e => h (by rw [e])
    simp [this]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem laB_eq_comap : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ),
    StandardLatticesGL3.LaB D (TaylorLogMetric.tor0 D cc δ) (bas B n n') =
      (stdLat B.L (Ix D n n')).comap (phi B n n' : TaylorLogMetric.VC D (n * 2) (n' * 2) →ₗ[ℂ] (Ix D n n' → ℂ)).toAddMonoidHom := by
  intro D cc δ B n n'
  apply le_antisymm
  · unfold StandardLatticesGL3.LaB
    rw [AddSubgroup.closure_le]
    rintro z ⟨w, hw, j, rfl⟩
    show phi B n n' (w • TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) (bas B n n' j)) ∈ stdLat B.L (Ix D n n')
    rw [map_smul, phi_embV_bas]
    have hw' : w ∈ B.L.lattice.toAddSubgroup := by rw [B.lat]; exact hw
    simp only [stdLat, AddSubgroup.mem_pi, Set.mem_univ, true_implies]
    intro p
    by_cases h : p = ixE D n n' j
    · subst h; simpa using hw'
    · simp [h]
  · intro x hx
    have hx' : phi B n n' x ∈ stdLat B.L (Ix D n n') := hx
    simp only [stdLat, AddSubgroup.mem_pi, Set.mem_univ, true_implies] at hx'
    have hsum : phi B n n' x = ∑ p, phi B n n' x p • (Pi.single p 1 : Ix D n n' → ℂ) := by
      funext q
      simp [Finset.sum_apply, Pi.single_apply]
    have hsing : ∀ p, (phi B n n').symm (Pi.single p 1) =
        TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) (bas B n n' ((ixE D n n').symm p)) := by
      intro p
      rw [LinearEquiv.symm_apply_eq, phi_embV_bas, Equiv.apply_symm_apply]
    have hxe : x = ∑ p, phi B n n' x p • TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) (bas B n n' ((ixE D n n').symm p)) := by
      conv_lhs => rw [← (phi B n n').symm_apply_apply x, hsum]
      rw [map_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [map_smul, hsing]
    rw [hxe]
    refine AddSubgroup.sum_mem _ fun p _ => AddSubgroup.subset_closure ?_
    refine ⟨phi B n n' x p, ?_, (ixE D n n').symm p, rfl⟩
    have := hx' p
    rw [B.lat] at this
    exact this

end GlobalTheory.BaseVacuum
