import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkLat
import Formalism.LocalToGlobal.InertKernelTheory.StatementAlg
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

noncomputable section
namespace GlobalTheory.BaseVacuum
open scoped BigOperators

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem sum_putB_embT (D : D7) {n n' : ℕ} (k : Fin n' × Fin n) (x : Fin 4 → D.host.E) (τ : D.what₂.Tau)
    (z : TaylorLogMetric.VC D (n * 2) (n' * 2)) :
    (∑ a, ∑ c, z τ a c * (starRingEnd ℂ) (TaylorLogMetric.embT D τ (putB D k x a c)))
      = ∑ b : Fin 4, blk D k z (b, τ) * (starRingEnd ℂ) (emb4 D x (b, τ)) := by
  rw [← Fintype.sum_prod_type' (f := fun a c => z τ a c * (starRingEnd ℂ) (TaylorLogMetric.embT D τ (putB D k x a c)))]
  rw [← (posE n n').sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single k]
  · refine Finset.sum_congr rfl fun b _ => ?_
    simp [putB, blk, emb4]
  · intro k' _ hk'
    refine Finset.sum_eq_zero fun b _ => ?_
    simp [putB, hk']
  · simp

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
theorem blockVacuum_coordinate_eq_coordinateEquiv_numbering (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ)
    (j : Fin (TaylorLogMetric.fF D * (n * 2) * (n' * 2))) (z : TaylorLogMetric.VC D (n * 2) (n' * 2)) :
    StandardLatticesGL3.coordB D (TaylorLogMetric.tor0 D cc δ) (bas B n n') j z = phi B n n' z (ixE D n n' j) := by
  set k := (ixE D n n' j).1
  set w := (ixE D n n' j).2
  have h1 : StandardLatticesGL3.coordB D (TaylorLogMetric.tor0 D cc δ) (bas B n n') j z
      = ∑ w', blk D k z w' * (starRingEnd ℂ) (emb4 D (xv B w) w') := by
    unfold StandardLatticesGL3.coordB
    rw [Fintype.sum_prod_type_right (f := fun w' : Fin 4 × D.what₂.Tau => blk D k z w' * (starRingEnd ℂ) (emb4 D (xv B w) w'))]
    refine Finset.sum_congr rfl fun τ _ => ?_
    exact sum_putB_embT D k (xv B w) τ z
  have hg : B.gC (emb4 D (xv B w)) = Pi.single w 1 := by
    rw [show B.gC (emb4 D (xv B w)) = _ from B.gC_spec (xv B w)]
    funext w'
    simp only [xv, LinearEquiv.apply_symm_apply]
    by_cases h : w' = w
    · subst h; simp
    · simp [Pi.single_apply, h]
  have hA : ((Formalism.L2.Th1.F.area B.L : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Formalism.L2.Th1.F.areaPos_thm B.L).ne'
  have hI := B.isomOK (blk D k z) (emb4 D (xv B w))
  rw [blockFourfold_hOne_eq_hOne] at hI
  change (matH (hOne B.L (Fin 4 × D.what₂.Tau))) (B.gC (blk D k z)) (B.gC (emb4 D (xv B w))) = _ at hI
  rw [matH_hOne, matH_hOne, div_left_inj' hA, hg] at hI
  rw [h1, ← hI, phi_apply]
  simp [Pi.single_apply]
  rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem coordB_bas_eq_phi : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ) (j : Fin (TaylorLogMetric.fF D * (n * 2) * (n' * 2))) (z : TaylorLogMetric.VC D (n * 2) (n' * 2)), StandardLatticesGL3.coordB D (TaylorLogMetric.tor0 D cc δ) (bas B n n') j z = phi B n n' z (ixE D n n' j) :=
  blockVacuum_coordinate_eq_coordinateEquiv_numbering

end GlobalTheory.BaseVacuum
