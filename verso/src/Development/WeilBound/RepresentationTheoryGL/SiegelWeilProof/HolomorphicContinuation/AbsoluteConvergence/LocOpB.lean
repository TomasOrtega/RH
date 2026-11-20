import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.LocOpA

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal ComplexOrder

namespace PositivityTheory.Rg.Sw.AbsSt.LocOpA

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

/- English proof (translation)
Conclude with `(Matrix.isUnits_det_units (g : GL (Fin n ⊕ Fin n) ℂ)).ne_zero`.
-/
theorem det_mR_ne (g : GR n) : (mR g).det ≠ 0 := by
  exact (Matrix.isUnits_det_units (g : GL (Fin n ⊕ Fin n) ℂ)).ne_zero

/- English proof (translation)
The claim follows from `continuous_pi fun i => continuous_pi fun j => continuous_apply_apply (Sum.inr i) (Sum.inl j)`.
-/
theorem continuous_toBlocks₂₁ : Continuous (fun M : M2 n => M.toBlocks₂₁) := continuous_pi fun i => continuous_pi fun j => continuous_apply_apply (Sum.inr i) (Sum.inl j)

/- English proof (translation)
The claim follows from `continuous_pi fun i => continuous_pi fun j => continuous_apply_apply (Sum.inr i) (Sum.inr j)`.
-/
theorem continuous_toBlocks₂₂ : Continuous (fun M : M2 n => M.toBlocks₂₂) := continuous_pi fun i => continuous_pi fun j => continuous_apply_apply (Sum.inr i) (Sum.inr j)

/- English proof (translation)
Use `show Continuous fun g : GR n => (Complex.I • (mR g).toBlocks₂₁ + (mR g).toBlocks₂₂).det`. Establish `h1 : Continuous fun g : GR n => (mR g).toBlocks₂₁` using `continuous_toBlocks₂₁.comp continuous_mR`. Establish `h2 : Continuous fun g : GR n => (mR g).toBlocks₂₂` using `continuous_toBlocks₂₂.comp continuous_mR`. Conclude with `((continuous_const (y := Complex.I)).smul h1 |>.add h2).matrix_det`.
-/
theorem continuous_det_first_block : Continuous (fun g : GR n => (u1 (mR g)).det) := by
  show Continuous fun g : GR n => (Complex.I • (mR g).toBlocks₂₁ + (mR g).toBlocks₂₂).det
  have h1 : Continuous fun g : GR n => (mR g).toBlocks₂₁ := continuous_toBlocks₂₁.comp continuous_mR
  have h2 : Continuous fun g : GR n => (mR g).toBlocks₂₂ := continuous_toBlocks₂₂.comp continuous_mR
  exact ((continuous_const (y := Complex.I)).smul h1 |>.add h2).matrix_det

/- English proof (translation)
Use `show Continuous fun g : GR n => (-(Complex.I • (mR g).toBlocks₂₁) + (mR g).toBlocks₂₂).det`. Establish `h1 : Continuous fun g : GR n => (mR g).toBlocks₂₁` using `continuous_toBlocks₂₁.comp continuous_mR`. Establish `h2 : Continuous fun g : GR n => (mR g).toBlocks₂₂` using `continuous_toBlocks₂₂.comp continuous_mR`. Conclude with `((continuous_const (y := Complex.I)).smul h1 |>.neg.add h2).matrix_det`.
-/
theorem continuous_det_second_block : Continuous (fun g : GR n => (u2 (mR g)).det) := by
  show Continuous fun g : GR n => (-(Complex.I • (mR g).toBlocks₂₁) + (mR g).toBlocks₂₂).det
  have h1 : Continuous fun g : GR n => (mR g).toBlocks₂₁ := continuous_toBlocks₂₁.comp continuous_mR
  have h2 : Continuous fun g : GR n => (mR g).toBlocks₂₂ := continuous_toBlocks₂₂.comp continuous_mR
  exact ((continuous_const (y := Complex.I)).smul h1 |>.neg.add h2).matrix_det

/- English proof (translation)
Unfold `f0`. Conclude with `mul_ne_zero (zpow_ne_zero _ (det_first_block_ne_zero_group (inG_of g))) (zpow_ne_zero _ (det_second_cayley_block_ne (inG_of g)))`.
-/
theorem local_spherical_function_ne_zero (p q : ℤ) (g : GR n) : f0 p q (mR g) ≠ 0 := by
  unfold f0
  exact mul_ne_zero (zpow_ne_zero _ (det_first_block_ne_zero_group (inG_of g))) (zpow_ne_zero _ (det_second_cayley_block_ne (inG_of g)))

/- English proof (translation)
Unfold `F0`. Conclude with `mul_ne_zero (zpow_ne_zero _ (det_mR_ne g)) (local_spherical_function_ne_zero _ _ g)`.
-/
theorem weight_factor_ne_zero (p q : ℕ) (e : ℤ) (g : GR n) : F0 p q e g ≠ 0 := by
  unfold F0
  exact mul_ne_zero (zpow_ne_zero _ (det_mR_ne g)) (local_spherical_function_ne_zero _ _ g)

/- English proof (translation)
Unfold `F0 f0`. Use `Continuous.mul (Continuous.zpow₀ (Continuous.matrix_det continuous_mR) e (fun g => Or.inl (det_mR_ne g))) ?_` and prove the remaining obligations. Conclude with `Continuous.mul (Continuous.zpow₀ continuous_det_first_block _ (fun g => Or.inl (det_first_block_ne_zero_group (inG_of g)))) (Continuous.zpow₀ continuous_det_second_block _ (fun g => Or.inl (det_second_cayley_block_ne (inG_of g))))`.
-/
theorem continuous_weight_factor (p q : ℕ) (e : ℤ) : Continuous (fun g : GR n => F0 p q e g) := by
  unfold F0 f0
  refine Continuous.mul (Continuous.zpow₀ (Continuous.matrix_det continuous_mR) e (fun g => Or.inl (det_mR_ne g))) ?_
  exact Continuous.mul (Continuous.zpow₀ continuous_det_first_block _ (fun g => Or.inl (det_first_block_ne_zero_group (inG_of g))))
    (Continuous.zpow₀ continuous_det_second_block _ (fun g => Or.inl (det_second_cayley_block_ne (inG_of g))))

/- English proof (translation)
Unfold `hLoc`. Conclude with `inv_pos.2 (pow_pos (norm_pos_iff.2 (det_first_block_ne_zero_group (inG_of g))) 2)`.
-/
theorem hLoc_pos (g : GR n) : 0 < hLoc g := by
  unfold hLoc
  exact inv_pos.2 (pow_pos (norm_pos_iff.2 (det_first_block_ne_zero_group (inG_of g))) 2)

/- English proof (translation)
Unfold `hLoc`. Conclude with `(continuous_det_first_block.norm.pow 2).inv₀ fun g => (pow_pos (norm_pos_iff.2 (det_first_block_ne_zero_group (inG_of g))) 2).ne'`.
-/
theorem continuous_hLoc : Continuous (fun g : GR n => hLoc g) := by
  unfold hLoc
  exact (continuous_det_first_block.norm.pow 2).inv₀ fun g =>
    (pow_pos (norm_pos_iff.2 (det_first_block_ne_zero_group (inG_of g))) 2).ne'

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[toBlocks₂₁]`.
-/
theorem toBlocks₂₁_one : (1 : M2 n).toBlocks₂₁ = 0 := by
  ext i j; simp [toBlocks₂₁]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[toBlocks₂₂, Matrix.one_apply]`.
-/
theorem toBlocks₂₂_one : (1 : M2 n).toBlocks₂₂ = 1 := by
  ext i j; simp [toBlocks₂₂, Matrix.one_apply]

/- English proof (translation)
Establish `h1 : mR (1 : GR n) = 1` using `rfl`. Simplify using `[F0, f0, u1, u2, h1, toBlocks₂₁_one, toBlocks₂₂_one]`.
-/
theorem weight_factor_one (p q : ℕ) (e : ℤ) : F0 p q e (1 : GR n) = 1 := by
  have h1 : mR (1 : GR n) = 1 := rfl
  simp [F0, f0, u1, u2, h1, toBlocks₂₁_one, toBlocks₂₂_one]

def kSet (n : ℕ) : Set (M2 n) := {M | InK M}

/- English proof (translation)
Establish `hcl : IsClosed (kSet n)`. Establish `hc : Continuous fun M : M2 n => Mᴴ` using `continuous_id.matrix_conjTranspose`. Conclude with `(isClosed_eq ((hc.matrix_mul continuous_const).matrix_mul continuous_id) continuous_const).inter (isClosed_eq (hc.matrix_mul continuous_id) continuous_const)`. Establish `hbd : IsCompact (Set.pi Set.univ fun _ : Fin n ⊕ Fin n => Set.pi Set.univ fun _ : Fin n ⊕ Fin n => Metric.closedBall (0 : ℂ) 1)` using `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _`. Use `hbd.of_isClosed_subset hcl ?_` and prove the remaining obligations.

Introduce `M hM i _ j _`. Establish `hu : M ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ` using `Matrix.mem_unitaryGroup_iff'.2 hM.2`. Simplify using `using entry_norm_bound_of_unitary hu i j`.
-/
theorem isCompact_kSet : IsCompact (kSet n) := by
  have hcl : IsClosed (kSet n) := by
    have hc : Continuous fun M : M2 n => Mᴴ := continuous_id.matrix_conjTranspose
    exact (isClosed_eq ((hc.matrix_mul continuous_const).matrix_mul continuous_id) continuous_const).inter
      (isClosed_eq (hc.matrix_mul continuous_id) continuous_const)
  have hbd : IsCompact (Set.pi Set.univ fun _ : Fin n ⊕ Fin n =>
      Set.pi Set.univ fun _ : Fin n ⊕ Fin n => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hbd.of_isClosed_subset hcl ?_
  intro M hM i _ j _
  have hu : M ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ := Matrix.mem_unitaryGroup_iff'.2 hM.2
  simpa using entry_norm_bound_of_unitary hu i j

def kOf (M : kSet n) : KR n := ⟨mkG M.1 M.2.1, M.2⟩

/- English proof (translation)
The claim follows from `Continuous.subtype_mk (continuous_mkG continuous_subtype_val (fun M => M.2.1)) _`.
-/
theorem continuous_kOf : Continuous (kOf (n := n)) :=
  Continuous.subtype_mk (continuous_mkG continuous_subtype_val (fun M => M.2.1)) _

/- English proof (translation)
Introduce `k`. Use `⟨⟨mR (k : GR n), k.2⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises.

Both sides reduce to the same expression.
-/
theorem surj_kOf : Function.Surjective (kOf (n := n)) := by
  intro k
  refine ⟨⟨mR (k : GR n), k.2⟩, ?_⟩
  apply Subtype.ext; apply Subtype.ext; apply Units.ext; rfl

instance instCompactKR : CompactSpace (KR n) := by
  have : CompactSpace (kSet n) := isCompact_iff_compactSpace.1 isCompact_kSet
  exact Function.Surjective.compactSpace continuous_kOf surj_kOf

end PositivityTheory.Rg.Sw.AbsSt.LocOpA
