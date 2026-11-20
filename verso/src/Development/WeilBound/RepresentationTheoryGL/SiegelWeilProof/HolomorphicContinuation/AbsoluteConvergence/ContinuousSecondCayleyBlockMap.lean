import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FarRightAlt

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Far

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem continuous_mR : Continuous (mR : GR n → M2 n) :=
  Units.continuous_val.comp continuous_subtype_val

def KMat (n : ℕ) : Set (M2 n) := {M | Mᴴ * M = 1 ∧ Mᴴ * JJ n * M = JJ n}

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem isCompact_KMat : IsCompact (KMat n) := by
  have hsub : KMat n ⊆ Set.pi univ (fun _ : Fin n ⊕ Fin n => Set.pi univ (fun _ : Fin n ⊕ Fin n => Metric.closedBall (0:ℂ) 1)) := by
    intro M hM
    have hU : M ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ := Matrix.mem_unitaryGroup_iff'.mpr hM.1
    intro i _ j _
    simpa using entry_norm_bound_of_unitary hU i j
  have hc : IsCompact (Set.pi univ (fun _ : Fin n ⊕ Fin n => Set.pi univ (fun _ : Fin n ⊕ Fin n => Metric.closedBall (0:ℂ) 1))) :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall 0 1))
  refine hc.of_isClosed_subset ?_ hsub
  have hA : Continuous fun M : M2 n => Mᴴ * M :=
    continuous_id.matrix_conjTranspose.matrix_mul continuous_id
  have hB : Continuous fun M : M2 n => Mᴴ * JJ n * M :=
    (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id
  exact (isClosed_eq hA continuous_const).inter (isClosed_eq hB continuous_const)

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isCompact_KR : IsCompact ((KR n : Subgroup (GR n)) : Set (GR n)) := by
  let φ : KMat n → GR n := fun M =>
    ⟨⟨M.1, M.1ᴴ, (mul_eq_one_comm).mp M.2.1, M.2.1⟩, M.2.2⟩
  have hφ : Continuous φ :=
    Continuous.subtype_mk (Units.continuous_iff.mpr
      ⟨continuous_subtype_val, continuous_subtype_val.matrix_conjTranspose⟩) _
  have hK : IsCompact (univ : Set (KMat n)) := isCompact_iff_isCompact_univ.mp isCompact_KMat
  have himg : φ '' univ = ((KR n : Subgroup (GR n)) : Set (GR n)) := by
    ext k
    constructor
    · rintro ⟨M, -, rfl⟩
      exact ⟨M.2.2, M.2.1⟩
    · intro hk
      refine ⟨⟨mR k, hk.2, hk.1⟩, trivial, ?_⟩
      apply Subtype.ext
      apply Units.ext
      rfl
  rw [← himg]
  exact hK.image hφ

instance compactSpace_KR_far : CompactSpace (KR n) := isCompact_iff_compactSpace.mp isCompact_KR

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem continuous_first_cayley_block_map : Continuous (fun M : M2 n => u1 M) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [u1, Matrix.add_apply, Matrix.smul_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.of_apply]
  fun_prop

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem continuous_second_cayley_block_map : Continuous (fun M : M2 n => u2 M) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [u2, Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.of_apply]
  fun_prop

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem det_mR_ne (g : GR n) : (mR g).det ≠ 0 := by
  exact ((Matrix.isUnit_iff_isUnit_det _).mp g.1.isUnit).ne_zero

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions.

A detailed English derivation is pending.
-/
theorem continuous_weight_factor (hD : CayleyBlocksInvertible) (p q : ℕ) (e : ℤ) : Continuous (F0 (n := n) p q e) := by
  have hm : Continuous (mR : GR n → M2 n) := continuous_mR
  have hd : Continuous fun g : GR n => (mR g).det := hm.matrix_det
  have h1 : Continuous fun g : GR n => (u1 (mR g)).det := (continuous_first_cayley_block_map.comp hm).matrix_det
  have h2 : Continuous fun g : GR n => (u2 (mR g)).det := (continuous_second_cayley_block_map.comp hm).matrix_det
  unfold F0 f0
  exact (hd.zpow₀ e fun g => Or.inl (det_mR_ne g)).mul
    ((h1.zpow₀ _ fun g => Or.inl (hD n g).1).mul (h2.zpow₀ _ fun g => Or.inl (hD n g).2))

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations.
-/
theorem weight_factor_ne_zero (hD : CayleyBlocksInvertible) (p q : ℕ) (e : ℤ) (g : GR n) : F0 p q e g ≠ 0 := by
  unfold F0 f0
  refine mul_ne_zero (zpow_ne_zero _ (det_mR_ne g)) (mul_ne_zero (zpow_ne_zero _ (hD n g).1) (zpow_ne_zero _ (hD n g).2))

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem hLoc_pos (hD : CayleyBlocksInvertible) (g : GR n) : 0 < hLoc g := by
  unfold hLoc
  exact inv_pos.mpr (pow_pos (norm_pos_iff.mpr (hD n g).1) 2)

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem continuous_hLoc (hD : CayleyBlocksInvertible) : Continuous (hLoc (n := n)) := by
  have h1 : Continuous fun g : GR n => (u1 (mR g)).det := (continuous_first_cayley_block_map.comp continuous_mR).matrix_det
  unfold hLoc
  exact (h1.norm.pow 2).inv₀ fun g => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hD n g).1)

end PositivityTheory.Rg.Sw.AbsSt.Far
