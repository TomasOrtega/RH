import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormMulApplyLeOne
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.UnitGLift

variable {k : Type} [CommRing k] {r : ℕ}

/- English proof (translation)
Simplify using `[full, Matrix.reindex_apply, Matrix.submatrix_apply]`.
-/
theorem full_apply_cc (Y : Gl r k) (a b : Fin r) : full Y (Fin.castSucc a) (Fin.castSucc b) = Y.1 a b := by
  simp [full, Matrix.reindex_apply, Matrix.submatrix_apply]

/- English proof (translation)
Simplify using `[full, Matrix.reindex_apply, Matrix.submatrix_apply]`.
-/
theorem full_apply_cl (Y : Gl r k) (a : Fin r) : full Y (Fin.castSucc a) (Fin.last r) = Y.2.1 a := by
  simp [full, Matrix.reindex_apply, Matrix.submatrix_apply]

/- English proof (translation)
Simplify using `[full, Matrix.reindex_apply, Matrix.submatrix_apply]`.
-/
theorem full_apply_lc (Y : Gl r k) (b : Fin r) : full Y (Fin.last r) (Fin.castSucc b) = Y.2.2.1 b := by
  simp [full, Matrix.reindex_apply, Matrix.submatrix_apply]

/- English proof (translation)
Simplify using `[full, Matrix.reindex_apply, Matrix.submatrix_apply]`.
-/
theorem full_apply_ll (Y : Gl r k) : full Y (Fin.last r) (Fin.last r) = Y.2.2.2 := by
  simp [full, Matrix.reindex_apply, Matrix.submatrix_apply]

end GlobalTheory.JR.UnitGLift

namespace GlobalTheory.JR.UnitGLift

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun i j => ?_, fun i => ?_, fun j => ?_, ?_⟩` and prove the remaining obligations. Simplify `h (Fin.castSucc i) (Fin.castSucc j)` using `[full_apply_cc]`. Simplify `h (Fin.castSucc i) (Fin.last r)` using `[full_apply_cl]`.

Simplify `h (Fin.last r) (Fin.castSucc j)` using `[full_apply_lc]`. Simplify `h (Fin.last r) (Fin.last r)` using `[full_apply_ll]`. Introduce and unpack `⟨h1, h2, h3, h4⟩ i j`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last`.

Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => simpa [full_apply_ll] using h4`. Consider the case `cast j => simpa [full_apply_lc] using h3 j`. Consider the case `cast i`. Proceed by induction on `j using Fin.lastCases with`.

Consider the case `last => simpa [full_apply_cl] using h2 i`. Consider the case `cast j => simpa [full_apply_cc] using h1 i j`.
-/
theorem norm_full_le_one_iff {F : Type} [NormedField F] {r : ℕ} (Z : Gl r F) :
    (∀ i j, ‖full Z i j‖ ≤ 1) ↔
      ((∀ i j, ‖Z.1 i j‖ ≤ 1) ∧ (∀ i, ‖Z.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Z.2.2.1 i‖ ≤ 1) ∧ ‖Z.2.2.2‖ ≤ 1) := by
  constructor
  · intro h
    refine ⟨fun i j => ?_, fun i => ?_, fun j => ?_, ?_⟩
    · simpa [full_apply_cc] using h (Fin.castSucc i) (Fin.castSucc j)
    · simpa [full_apply_cl] using h (Fin.castSucc i) (Fin.last r)
    · simpa [full_apply_lc] using h (Fin.last r) (Fin.castSucc j)
    · simpa [full_apply_ll] using h (Fin.last r) (Fin.last r)
  · rintro ⟨h1, h2, h3, h4⟩ i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simpa [full_apply_ll] using h4
      | cast j => simpa [full_apply_lc] using h3 j
    | cast i =>
      induction j using Fin.lastCases with
      | last => simpa [full_apply_cl] using h2 i
      | cast j => simpa [full_apply_cc] using h1 i j

/- English proof (translation)
Unfold `GlobalTheory.JR.Step.eL`. Distinguish the cases in `h : i = Fin.last r`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, h]`.
-/
theorem norm_eL_le_one {F : Type} [NormedField F] {r : ℕ} (i : Fin (r + 1)) :
    ‖GlobalTheory.JR.Step.eL r F i‖ ≤ 1 := by
  unfold GlobalTheory.JR.Step.eL
  by_cases h : i = Fin.last r
  · subst h; simp
  · simp [Pi.single_apply, h]

/- English proof (translation)
Introduce `F _ r Z μ l hμ`. Establish `hb : ∀ i, ‖(μ • GlobalTheory.JR.Step.eL r F) i‖ ≤ 1` using `fun i => by`. Rewrite using `[Pi.smul_apply, smul_eq_mul, norm_mul]`. Conclude with `mul_le_one₀ hμ (norm_nonneg _) (norm_eL_le_one i)`. Establish `hmem : GlobalTheory.JR.Step.lift Z μ l ∈ {Y : Gl (r + 1) F | (∀ i j, ‖Y.1 i j‖ ≤ 1) ∧ (∀ i, ‖Y.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Y.2.2.1 i‖ ≤ 1) ∧ ‖Y.2.2.2‖ ≤ 1} ↔ (Z ∈ {Y : Gl r F | (∀ i j, ‖Y.1 i j‖ ≤ 1) ∧ (∀ i, ‖Y.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Y.2.2.1 i‖ ≤ 1) ∧ ‖Y.2.2.2‖ ≤ 1} ∧ ‖l‖ ≤ 1)`.

Simplify using `only [Set.mem_setOf_eq, GlobalTheory.JR.Step.lift]`. Rewrite using `[norm_full_le_one_iff]`. Conclude with `⟨fun ⟨h1, _, _, h4⟩ => ⟨h1, h4⟩, fun ⟨h1, h4⟩ => ⟨h1, hb, norm_eL_le_one, h4⟩⟩`. Unfold `unitG`. Distinguish the cases in `hZ : Z ∈ {Y : Gl r F | (∀ i j, ‖Y.1 i j‖ ≤ 1) ∧ (∀ i, ‖Y.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Y.2.2.1 i‖ ≤ 1) ∧ ‖Y.2.2.2‖ ≤ 1}`.

Distinguish the cases in `hl : ‖l‖ ≤ 1`. Rewrite using `[Set.indicator_of_mem (hmem.2 ⟨hZ, hl⟩), Set.indicator_of_mem hZ, if_pos hl]`. Simplify using the standard rewrite rules. Rewrite using `[Set.indicator_of_notMem (fun h => hl (hmem.1 h).2), if_neg hl, zero_mul]`. Rewrite using `[Set.indicator_of_notMem (fun h => hZ (hmem.1 h).1), Set.indicator_of_notMem hZ, mul_zero]`.
-/
theorem unitG_lift : ∀ (F : Type) [NormedField F] (r : ℕ) (Z : Gl r F) (μ l : F), ‖μ‖ ≤ 1 →
    unitG (r + 1) F (GlobalTheory.JR.Step.lift Z μ l) = (if ‖l‖ ≤ 1 then 1 else 0) * unitG r F Z := by
  intro F _ r Z μ l hμ
  have hb : ∀ i, ‖(μ • GlobalTheory.JR.Step.eL r F) i‖ ≤ 1 := fun i => by
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_one₀ hμ (norm_nonneg _) (norm_eL_le_one i)
  have hmem : GlobalTheory.JR.Step.lift Z μ l ∈
      {Y : Gl (r + 1) F | (∀ i j, ‖Y.1 i j‖ ≤ 1) ∧ (∀ i, ‖Y.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Y.2.2.1 i‖ ≤ 1) ∧ ‖Y.2.2.2‖ ≤ 1} ↔
      (Z ∈ {Y : Gl r F | (∀ i j, ‖Y.1 i j‖ ≤ 1) ∧ (∀ i, ‖Y.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Y.2.2.1 i‖ ≤ 1) ∧ ‖Y.2.2.2‖ ≤ 1}
        ∧ ‖l‖ ≤ 1) := by
    simp only [Set.mem_setOf_eq, GlobalTheory.JR.Step.lift]
    rw [norm_full_le_one_iff]
    exact ⟨fun ⟨h1, _, _, h4⟩ => ⟨h1, h4⟩, fun ⟨h1, h4⟩ => ⟨h1, hb, norm_eL_le_one, h4⟩⟩
  unfold unitG
  by_cases hZ : Z ∈ {Y : Gl r F | (∀ i j, ‖Y.1 i j‖ ≤ 1) ∧ (∀ i, ‖Y.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Y.2.2.1 i‖ ≤ 1) ∧ ‖Y.2.2.2‖ ≤ 1}
  · by_cases hl : ‖l‖ ≤ 1
    · rw [Set.indicator_of_mem (hmem.2 ⟨hZ, hl⟩), Set.indicator_of_mem hZ, if_pos hl]
      simp
    · rw [Set.indicator_of_notMem (fun h => hl (hmem.1 h).2), if_neg hl, zero_mul]
  · rw [Set.indicator_of_notMem (fun h => hZ (hmem.1 h).1), Set.indicator_of_notMem hZ, mul_zero]

end GlobalTheory.JR.UnitGLift
