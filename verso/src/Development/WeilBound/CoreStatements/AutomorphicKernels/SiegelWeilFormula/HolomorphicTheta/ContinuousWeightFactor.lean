import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.ContinuousQuad
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.ZOfSurjBdd
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.SphericalSectionUnipotentInvariant

noncomputable section

open Matrix Metric Set Filter Topology
open scoped ComplexOrder

namespace PositivityTheory.SiegelWeilFormula.Holtb

open PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula PositivityTheory.Rg.Sw.HSt.HolTPf

variable {n : ℕ}

def bmap (q : ℕ) (y : GR n) : Matrix (Fin n) (Fin n) ℂ := if q = 0 then zOf y else -(zOf y)ᴴ

def negConj (W : Fin n → Fin n → ℂ) : Fin n → Fin n → ℂ := fun i j => -star (W j i)

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem negConj_eq (W : Fin n → Fin n → ℂ) : negConj W = (-(Matrix.of W)ᴴ : Matrix (Fin n) (Fin n) ℂ) := by
  ext i j; simp [negConj]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem negConj_negConj (W : Fin n → Fin n → ℂ) : negConj (negConj W) = W := by
  ext i j; simp [negConj]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem negConj_mem {W : Fin n → Fin n → ℂ} (hW : W ∈ Dom n) : negConj W ∈ Dom n := by
  rw [negConj_eq]; exact neg_conj_mem' hW

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem norm_negConj_sub (W W' : Fin n → Fin n → ℂ) : ‖negConj W - negConj W'‖ ≤ ‖W - W'‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  have h : (negConj W - negConj W') i j = -star ((W - W') j i) := by
    show -star (W j i) - -star (W' j i) = -star (W j i - W' j i)
    rw [star_sub]; ring
  rw [h, norm_neg, norm_star]
  exact (norm_le_pi_norm ((W - W') j) i).trans (norm_le_pi_norm (W - W') j)

/- English proof (translation)
Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem bmap_local (q : ℕ) (W₀ : Fin n → Fin n → ℂ) (hW₀ : W₀ ∈ Dom n) : ∃ r > 0, closedBall W₀ r ⊆ Dom n ∧
    ∃ S : Set (GR n), IsCompact S ∧ ∀ W ∈ closedBall W₀ r, ∃ y ∈ S, (bmap q y : Fin n → Fin n → ℂ) = W := by
  by_cases hq : q = 0
  · obtain ⟨r, hr, hsub, S, hS, hcov⟩ := zOf_surj_bdd' W₀ hW₀
    refine ⟨r, hr, hsub, S, hS, fun W hW => ?_⟩
    obtain ⟨y, hy, hyW⟩ := hcov W hW
    refine ⟨y, hy, ?_⟩
    unfold bmap
    rw [if_pos hq]
    exact hyW
  · obtain ⟨r, hr, hsub, S, hS, hcov⟩ := zOf_surj_bdd' (negConj W₀) (negConj_mem hW₀)
    have key : ∀ W ∈ closedBall W₀ r, negConj W ∈ closedBall (negConj W₀) r := by
      intro W hW
      rw [mem_closedBall, dist_eq_norm] at hW ⊢
      exact (norm_negConj_sub W W₀).trans hW
    refine ⟨r, hr, fun W hW => ?_, S, hS, fun W hW => ?_⟩
    · have h := negConj_mem (hsub (key W hW))
      rwa [negConj_negConj] at h
    · obtain ⟨y, hy, hyW⟩ := hcov (negConj W) (key W hW)
      refine ⟨y, hy, ?_⟩
      unfold bmap
      rw [if_neg hq, hyW]
      funext i j
      show -star (negConj W j i) = W i j
      simp [negConj]

/- English proof (translation)
Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem bmap_surj (q : ℕ) {W : Fin n → Fin n → ℂ} (hW : W ∈ Dom n) : ∃ y : GR n, (bmap q y : Fin n → Fin n → ℂ) = W := by
  by_cases hq : q = 0
  · obtain ⟨y, hy⟩ := zOf_surj' hW
    refine ⟨y, ?_⟩
    unfold bmap
    rw [if_pos hq]
    exact hy
  · obtain ⟨y, hy⟩ := zOf_surj' (negConj_mem hW)
    refine ⟨y, ?_⟩
    unfold bmap
    rw [if_neg hq, hy]
    funext i j
    show -star (negConj W j i) = W i j
    simp [negConj]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem continuous_mR : Continuous (mR : GR n → M2 n) :=
  Units.continuous_val.comp continuous_subtype_val

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem continuous_toBlocks₂₁ : Continuous fun M : M2 n => M.toBlocks₂₁ :=
  continuous_pi fun i => continuous_pi fun j => (continuous_apply (Sum.inl j)).comp (continuous_apply (Sum.inr i))

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem continuous_toBlocks₂₂ : Continuous fun M : M2 n => M.toBlocks₂₂ :=
  continuous_pi fun i => continuous_pi fun j => (continuous_apply (Sum.inr j)).comp (continuous_apply (Sum.inr i))

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem zpow_cond {a : ℂ} {k : ℤ} (h : a ^ k ≠ 0) : a ≠ 0 ∨ 0 ≤ k := by
  by_contra hc
  push_neg at hc
  obtain ⟨rfl, hk⟩ := hc
  exact h (zero_zpow k (ne_of_lt hk))

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions.

Establish an intermediate fact. Replace the relevant objects with their definitions. Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem continuous_weight_factor (p q : ℕ) (e : ℤ) : Continuous (F0 p q e : GR n → ℂ) := by
  have hd : Continuous fun y : GR n => (mR y).det := continuous_mR.matrix_det
  have hb1 : Continuous fun y : GR n => toBlocks₂₁ (mR y) := continuous_toBlocks₂₁.comp continuous_mR
  have hb2 : Continuous fun y : GR n => toBlocks₂₂ (mR y) := continuous_toBlocks₂₂.comp continuous_mR
  have h1 : Continuous fun y : GR n => (u1 (mR y)).det := by
    unfold u1
    exact (((continuous_const (y := Complex.I)).smul hb1).add hb2).matrix_det
  have h2 : Continuous fun y : GR n => (u2 (mR y)).det := by
    unfold u2
    exact ((((continuous_const (y := Complex.I)).smul hb1).neg).add hb2).matrix_det
  have hne := spherical_section_ne_zero_group (n := n) p q e
  simp only [F0, f0] at hne ⊢
  exact (hd.zpow₀ e fun y => zpow_cond (left_ne_zero_of_mul (hne y))).mul
    ((h1.zpow₀ _ fun y => zpow_cond (left_ne_zero_of_mul (right_ne_zero_of_mul (hne y)))).mul
      (h2.zpow₀ _ fun y => zpow_cond (right_ne_zero_of_mul (right_ne_zero_of_mul (hne y)))))

end PositivityTheory.SiegelWeilFormula.Holtb
