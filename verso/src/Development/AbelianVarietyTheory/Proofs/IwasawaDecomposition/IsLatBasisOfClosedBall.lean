import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement

set_option autoImplicit false

namespace GlobalTheory.LatticeBasisClosedBall

/- English proof (translation)
Establish `hdim : Fintype.card (Fin (2 * g)) = Module.finrank ℝ (Fin g → ℂ)`. Rewrite using `[Module.finrank_pi_fintype]`. Simplify using `[Complex.finrank_real_complex, mul_comm]`. Establish `hspan : Submodule.span ℝ (Set.range lam) = ⊤` using `hli.span_eq_top_of_card_eq_finrank' hdim`. Establish `hw : w ∈ Submodule.span ℝ (Set.range lam)` using `hspan ▸ Submodule.mem_top`.

Conclude with `(Submodule.mem_span_range_iff_exists_fun ℝ).1 hw`.
-/
theorem exists_real_coords {g : ℕ} (lam : Fin (2 * g) → Fin g → ℂ) (hli : LinearIndependent ℝ lam)
    (w : Fin g → ℂ) : ∃ c : Fin (2 * g) → ℝ, ∑ j, c j • lam j = w := by
  have hdim : Fintype.card (Fin (2 * g)) = Module.finrank ℝ (Fin g → ℂ) := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  have hspan : Submodule.span ℝ (Set.range lam) = ⊤ := hli.span_eq_top_of_card_eq_finrank' hdim
  have hw : w ∈ Submodule.span ℝ (Set.range lam) := hspan ▸ Submodule.mem_top
  exact (Submodule.mem_span_range_iff_exists_fun ℝ).1 hw

/- English proof (translation)
Introduce `g H lam R hli hmem hR hball`. Establish `hint : ∀ m : Fin (2 * g) → ℤ, ∑ j, m j • lam j ∈ H` using `fun m => H.sum_mem fun j _ => H.zsmul_mem (hmem j) (m j)`. Use `⟨hli, fun w => ⟨fun hw => ?_, ?_⟩⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `exists_real_coords lam hli w`. Establish `hsplit : w - ∑ j, ⌊c j⌋ • lam j = ∑ j, Int.fract (c j) • lam j`.

Rewrite using `[← hc, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Int.fract, sub_smul, Int.cast_smul_eq_zsmul]`. Establish `hH : w - ∑ j, ⌊c j⌋ • lam j ∈ H` using `H.sub_mem hw (hint _)`. Establish `hnorm : w - ∑ j, ⌊c j⌋ • lam j ∈ Metric.closedBall (0 : Fin g → ℂ) R`.

Rewrite using `[mem_closedBall_zero_iff, hsplit]`. Use `(norm_sum_le _ _).trans (le_trans (Finset.sum_le_sum fun j _ => ?_) hR)` and prove the remaining obligations. Rewrite using `[norm_smul, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) (Int.fract_lt_one _).le`. Take `⟨m, hm⟩` from `hball _ hnorm hH`.

Use `⟨fun j => m j + ⌊c j⌋, ?_⟩` and prove the remaining obligations. Simplify using `only [add_smul, Finset.sum_add_distrib]`. Rewrite using `[← hm, sub_add_cancel]`. Introduce and unpack `⟨m, rfl⟩`. Conclude with `hint m`.
-/
theorem isLatBasis_of_closedBall : ∀ {g : ℕ} (H : AddSubgroup (Fin g → ℂ)) (lam : Fin (2 * g) → Fin g → ℂ)
    (R : ℝ), LinearIndependent ℝ lam → (∀ j : Fin (2 * g), lam j ∈ H) → ∑ j : Fin (2 * g), ‖lam j‖ ≤ R →
    (∀ w ∈ Metric.closedBall (0 : Fin g → ℂ) R, w ∈ H →
      ∃ m : Fin (2 * g) → ℤ, w = ∑ j : Fin (2 * g), m j • lam j) →
    GlobalTheory.ShFam.Hor.LogCh.IsLatBasis (↑H : Set (Fin g → ℂ)) lam := by
  intro g H lam R hli hmem hR hball
  have hint : ∀ m : Fin (2 * g) → ℤ, ∑ j, m j • lam j ∈ H := fun m =>
    H.sum_mem fun j _ => H.zsmul_mem (hmem j) (m j)
  refine ⟨hli, fun w => ⟨fun hw => ?_, ?_⟩⟩
  · obtain ⟨c, hc⟩ := exists_real_coords lam hli w
    have hsplit : w - ∑ j, ⌊c j⌋ • lam j = ∑ j, Int.fract (c j) • lam j := by
      rw [← hc, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Int.fract, sub_smul, Int.cast_smul_eq_zsmul]
    have hH : w - ∑ j, ⌊c j⌋ • lam j ∈ H := H.sub_mem hw (hint _)
    have hnorm : w - ∑ j, ⌊c j⌋ • lam j ∈ Metric.closedBall (0 : Fin g → ℂ) R := by
      rw [mem_closedBall_zero_iff, hsplit]
      refine (norm_sum_le _ _).trans (le_trans (Finset.sum_le_sum fun j _ => ?_) hR)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (Int.fract_lt_one _).le
    obtain ⟨m, hm⟩ := hball _ hnorm hH
    refine ⟨fun j => m j + ⌊c j⌋, ?_⟩
    simp only [add_smul, Finset.sum_add_distrib]
    rw [← hm, sub_add_cancel]
  · rintro ⟨m, rfl⟩
    exact hint m

end GlobalTheory.LatticeBasisClosedBall
