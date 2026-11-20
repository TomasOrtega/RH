import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkLat
import Formalism.LocalToGlobal.InertKernelTheory.StatementAlg
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

noncomputable section
namespace GlobalTheory.BaseVacuum
open scoped BigOperators

/- English proof (translation)
Rewrite using `[← Fintype.sum_prod_type' (f := fun a c => z τ a c * (starRingEnd ℂ) (TaylorLogMetric.embT D τ (putB D k x a c)))]`. Rewrite using `[← (posE n n').sum_comp]`. Rewrite using `[Fintype.sum_prod_type, Finset.sum_eq_single k]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `[putB, blk, emb4]`.

Introduce `k' _ hk'`. Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations. Simplify using `[putB, hk']`. Simplify using the standard rewrite rules.
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
Use `set k := (ixE D n n' j).1`. Use `set w := (ixE D n n' j).2`. Establish `h1 : StandardLatticesGL3.coordB D (TaylorLogMetric.tor0 D cc δ) (bas B n n') j z = ∑ w', blk D k z w' * (starRingEnd ℂ) (emb4 D (xv B w) w')`. Unfold `StandardLatticesGL3.coordB`. Rewrite using `[Fintype.sum_prod_type_right (f := fun w' : Fin 4 × D.what₂.Tau => blk D k z w' * (starRingEnd ℂ) (emb4 D (xv B w) w'))]`.

Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Conclude with `sum_putB_embT D k (xv B w) τ z`. Establish `hg : B.gC (emb4 D (xv B w)) = Pi.single w 1`. Rewrite using `[show B.gC (emb4 D (xv B w)) = _ from B.gC_spec (xv B w)]`. Use function extensionality and compare the values at `w'`.

Simplify using `only [xv, LinearEquiv.apply_symm_apply]`. Distinguish the cases in `h : w' = w`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, h]`.

Establish `hA : ((Formalism.L2.Th1.F.area B.L : ℝ) : ℂ) ≠ 0`. Conclude with `(Formalism.L2.Th1.F.areaPos_thm B.L).ne'` after adjusting the coercions. Establish `hI` using `B.isomOK (blk D k z) (emb4 D (xv B w))`. Rewrite `hI` using `[blockFourfold_hOne_eq_hOne]`. Express the relevant statement in the definitionally equal form `(matH (hOne B.L (Fin 4 × D.what₂.Tau))) (B.gC (blk D k z)) (B.gC (emb4 D (xv B w))) = _ at hI`.

Rewrite `hI` using `[matH_hOne, matH_hOne, div_left_inj' hA, hg]`. Rewrite using `[h1, ← hI, phi_apply]`. Simplify using `[Pi.single_apply]`. Both sides reduce to the same expression.
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
The claim follows from `blockVacuum_coordinate_eq_coordinateEquiv_numbering`.
-/
theorem coordB_bas_eq_phi : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ) (j : Fin (TaylorLogMetric.fF D * (n * 2) * (n' * 2))) (z : TaylorLogMetric.VC D (n * 2) (n' * 2)), StandardLatticesGL3.coordB D (TaylorLogMetric.tor0 D cc δ) (bas B n n') j z = phi B n n' z (ixE D n n' j) :=
  blockVacuum_coordinate_eq_coordinateEquiv_numbering

end GlobalTheory.BaseVacuum
