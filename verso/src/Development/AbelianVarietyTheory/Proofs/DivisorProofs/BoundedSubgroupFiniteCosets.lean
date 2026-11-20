import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlPiEquivSymmContinuous
open Matrix
open scoped Classical

namespace GlobalTheory.LKLoc

/- English proof (translation)
Establish `key : ((a⁻¹ * b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 + ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((b : Matrix (Fin n) (Fin n) L) - (a : Matrix (Fin n) (Fin n) L))`. Rewrite using `[Units.val_mul, Matrix.mul_sub, Units.inv_mul]`. Normalize the expressions using the abelian group laws. Establish `hs : ‖(((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((b : Matrix (Fin n) (Fin n) L) - (a : Matrix (Fin n) (Fin n) L))) i j‖ ≤ 1`. Rewrite using `[Matrix.mul_apply]`.

Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul (ha i k) (by simpa using hab k j) (norm_nonneg _) hC`. Use `_ = n * C * ε := by simp [mul_assoc]`.

Use `_ ≤ 1 := hε`. Establish `h1 : ‖(1 : Matrix (Fin n) (Fin n) L) i j‖ ≤ 1`. Apply the tactic sequence `rw [Matrix.one_apply]; split_ifs <;> simp`. Express the relevant statement in the definitionally equal form `‖(( ((a⁻¹ * b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j : L) : PadicAlgCl p)‖ ≤ 1`. Rewrite using `[key, Matrix.add_apply, IntermediateField.coe_add]`.

Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 hs)`.
-/
theorem inv_mul_entry_mem_intK (p : ℕ) [Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ)
    (a b : GL (Fin n) L) (C ε : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i j, ‖((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j‖ ≤ C)
    (hab : ∀ i j, ‖(b : Matrix (Fin n) (Fin n) L) i j - (a : Matrix (Fin n) (Fin n) L) i j‖ ≤ ε)
    (hε : n * C * ε ≤ 1) (i j : Fin n) :
    ((a⁻¹ * b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ intK p L := by
  have key : ((a⁻¹ * b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      1 + ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
        ((b : Matrix (Fin n) (Fin n) L) - (a : Matrix (Fin n) (Fin n) L)) := by
    rw [Units.val_mul, Matrix.mul_sub, Units.inv_mul]
    abel
  have hs : ‖(((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
        ((b : Matrix (Fin n) (Fin n) L) - (a : Matrix (Fin n) (Fin n) L))) i j‖ ≤ 1 := by
    rw [Matrix.mul_apply]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k, ‖((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i k *
            ((b : Matrix (Fin n) (Fin n) L) - (a : Matrix (Fin n) (Fin n) L)) k j‖
        ≤ ∑ _k : Fin n, C * ε := Finset.sum_le_sum fun k _ => by
          rw [norm_mul]
          exact mul_le_mul (ha i k) (by simpa using hab k j) (norm_nonneg _) hC
      _ = n * C * ε := by simp [mul_assoc]
      _ ≤ 1 := hε
  have h1 : ‖(1 : Matrix (Fin n) (Fin n) L) i j‖ ≤ 1 := by
    rw [Matrix.one_apply]; split_ifs <;> simp
  change ‖(( ((a⁻¹ * b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j : L) : PadicAlgCl p)‖ ≤ 1
  rw [key, Matrix.add_apply, IntermediateField.coe_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 hs)

/- English proof (translation)
Introduce `p _ L hL n B c hB`. Use `haveI : ProperSpace L := FiniteDimensional.proper ℚ_[p] L`. Use `set C := max c 0 with hCdef`. Establish `hC : 0 ≤ C` using `le_max_right _ _`. Use `set ε : ℝ := 1 / (2 * (n * C + 1)) with hεdef`.

Establish `hε : 0 < ε` using `by positivity`. Set `f : GL (Fin n) L → (Fin n → Fin n → L)` to `fun z i j => (z : Matrix (Fin n) (Fin n) L) i j`. Set `S : Set (Fin n → Fin n → L)` to `Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : L) C`. Establish `hS : IsCompact S` using `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _`. Take `⟨t, ht, hcov⟩` from `Metric.totallyBounded_iff.1 hS.totallyBounded ε hε`.

Set `g : (Fin n → Fin n → L) → GL (Fin n) L` to `fun y => if h : ∃ z ∈ B, dist (f z) y < ε then h.choose else 1`. Establish `hgB : ∀ y, g y ∈ B` using `fun y => by`. Distinguish the cases in `h : ∃ z ∈ B, dist (f z) y < ε`. Simplify using `only [g, dif_pos h]`. Conclude with `h.choose_spec.1`.

Simplify using `only [g, dif_neg h]`. Conclude with `B.one_mem`. Establish `hbd : ∀ z ∈ B, ∀ i j, ‖(z : Matrix (Fin n) (Fin n) L) i j‖ ≤ C` using `fun z hz i j => (hB z hz i j).trans (le_max_left _ _)`. Establish `hnC : (n : ℝ) * C * (2 * ε) ≤ 1`. Rewrite using `[hεdef]`.

Establish `h0 : (0 : ℝ) < n * C + 1` using `by positivity`. Rewrite using `[show (n : ℝ) * C * (2 * (1 / (2 * (n * C + 1)))) = n * C / (n * C + 1) by field_simp]`. Rewrite using `[div_le_one h0]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨ht.toFinset.image g, ?_, ?_⟩` and prove the remaining obligations.

Introduce `s hs`. Take `⟨y, -, rfl⟩` from `Finset.mem_image.1 hs`. Conclude with `hgB y`. Introduce `z hz`. Establish `hzS : f z ∈ S`.

Simplify using `only [S, Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]`. Introduce `i j`. Conclude with `hbd z hz i j`. Take `⟨y, hy, hzy⟩` from `Set.mem_iUnion₂.1 (hcov hzS)`. Establish `hex : ∃ z ∈ B, dist (f z) y < ε` using `⟨z, hz, hzy⟩`.

Establish `hgy : g y ∈ B ∧ dist (f (g y)) y < ε`. Simplify using `only [g, dif_pos hex]`. Conclude with `hex.choose_spec`. Use `⟨g y, Finset.mem_image.2 ⟨y, ht.mem_toFinset.2 hy, rfl⟩, ?_⟩` and prove the remaining obligations. Take `⟨hwB, hwy⟩` from `hgy`.

Use `set w := g y`. Establish `hd : dist (f z) (f w) ≤ 2 * ε`. Use `dist_triangle_right (f z) (f w) y` as an intermediate fact. Use `Metric.mem_ball.1 hzy` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hent : ∀ i j, ‖(z : Matrix (Fin n) (Fin n) L) i j - (w : Matrix (Fin n) (Fin n) L) i j‖ ≤ 2 * ε` using `fun i j => by`. Rewrite using `[← dist_eq_norm]`. Conclude with `((dist_le_pi_dist (f z i) (f w i) j).trans (dist_le_pi_dist (f z) (f w) i)).trans hd`. Rewrite using `[KintK, GlobalTheory.LKRes.mem_range_map_subtype_iff]`. Use `⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations.

Conclude with `inv_mul_entry_mem_intK p L n w z C (2 * ε) hC (hbd _ (B.inv_mem hwB)) hent hnC i j`. Rewrite using `[_root_.mul_inv_rev, inv_inv]`. Conclude with `inv_mul_entry_mem_intK p L n z w C (2 * ε) hC (hbd _ (B.inv_mem hz)) (fun i j => by rw [norm_sub_rev]; exact hent i j) hnC i j`.
-/
theorem exists_finset_inv_mul_mem_KintK : ∀ (p : ℕ) [Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p)),
    FiniteDimensional ℚ_[p] L →
    ∀ (n : ℕ) (B : Subgroup (GL (Fin n) L)) (c : ℝ),
      (∀ z ∈ B, ∀ i j, ‖((((z : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j : L) : PadicAlgCl p)‖ ≤ c) →
      ∃ T : Finset (GL (Fin n) L), (∀ t ∈ T, t ∈ B) ∧ ∀ z ∈ B, ∃ t ∈ T, t⁻¹ * z ∈ GlobalTheory.LKLoc.KintK p L n := by
  intro p _ L hL n B c hB
  haveI : ProperSpace L := FiniteDimensional.proper ℚ_[p] L
  set C := max c 0 with hCdef
  have hC : 0 ≤ C := le_max_right _ _
  set ε : ℝ := 1 / (2 * (n * C + 1)) with hεdef
  have hε : 0 < ε := by positivity
  let f : GL (Fin n) L → (Fin n → Fin n → L) := fun z i j => (z : Matrix (Fin n) (Fin n) L) i j
  let S : Set (Fin n → Fin n → L) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : L) C
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  obtain ⟨t, ht, hcov⟩ := Metric.totallyBounded_iff.1 hS.totallyBounded ε hε
  let g : (Fin n → Fin n → L) → GL (Fin n) L := fun y =>
    if h : ∃ z ∈ B, dist (f z) y < ε then h.choose else 1
  have hgB : ∀ y, g y ∈ B := fun y => by
    by_cases h : ∃ z ∈ B, dist (f z) y < ε
    · simp only [g, dif_pos h]; exact h.choose_spec.1
    · simp only [g, dif_neg h]; exact B.one_mem
  have hbd : ∀ z ∈ B, ∀ i j, ‖(z : Matrix (Fin n) (Fin n) L) i j‖ ≤ C := fun z hz i j =>
    (hB z hz i j).trans (le_max_left _ _)
  have hnC : (n : ℝ) * C * (2 * ε) ≤ 1 := by
    rw [hεdef]
    have h0 : (0 : ℝ) < n * C + 1 := by positivity
    rw [show (n : ℝ) * C * (2 * (1 / (2 * (n * C + 1)))) = n * C / (n * C + 1) by field_simp]
    rw [div_le_one h0]; linarith
  refine ⟨ht.toFinset.image g, ?_, ?_⟩
  · intro s hs
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hs
    exact hgB y
  · intro z hz
    have hzS : f z ∈ S := by
      simp only [S, Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
      intro i j; exact hbd z hz i j
    obtain ⟨y, hy, hzy⟩ := Set.mem_iUnion₂.1 (hcov hzS)
    have hex : ∃ z ∈ B, dist (f z) y < ε := ⟨z, hz, hzy⟩
    have hgy : g y ∈ B ∧ dist (f (g y)) y < ε := by
      simp only [g, dif_pos hex]; exact hex.choose_spec
    refine ⟨g y, Finset.mem_image.2 ⟨y, ht.mem_toFinset.2 hy, rfl⟩, ?_⟩
    obtain ⟨hwB, hwy⟩ := hgy
    set w := g y
    have hd : dist (f z) (f w) ≤ 2 * ε := by
      have := dist_triangle_right (f z) (f w) y
      have := Metric.mem_ball.1 hzy
      linarith
    have hent : ∀ i j, ‖(z : Matrix (Fin n) (Fin n) L) i j - (w : Matrix (Fin n) (Fin n) L) i j‖ ≤ 2 * ε :=
      fun i j => by
        rw [← dist_eq_norm]
        exact ((dist_le_pi_dist (f z i) (f w i) j).trans (dist_le_pi_dist (f z) (f w) i)).trans hd
    rw [KintK, GlobalTheory.LKRes.mem_range_map_subtype_iff]
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · exact inv_mul_entry_mem_intK p L n w z C (2 * ε) hC (hbd _ (B.inv_mem hwB)) hent hnC i j
    · rw [_root_.mul_inv_rev, inv_inv]
      exact inv_mul_entry_mem_intK p L n z w C (2 * ε) hC (hbd _ (B.inv_mem hz))
        (fun i j => by rw [norm_sub_rev]; exact hent i j) hnC i j

end GlobalTheory.LKLoc
