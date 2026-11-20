import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalMaximumPrinciple
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalTrace
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter RealInnerProductSpace

/- English proof (translation)
Establish `hj : ∀ i, ⟪c, a i⟫ ≤ ‖c‖ ^ 2` using `fun i => (real_inner_le_norm c (a i)).trans (by rw [sq]; exact mul_le_mul_of_nonneg_left (hle i) (norm_nonneg c))`. Establish `htot : ∑ i, ⟪c, a i⟫ = m * ‖c‖ ^ 2`. Rewrite using `[← inner_sum, hsum, ← Nat.cast_smul_eq_nsmul ℝ, real_inner_smul_right, real_inner_self_eq_norm_sq]`. Establish `h0` using `(Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sub_nonneg.2 (hj i))).1 (by rw [Finset.sum_sub_distrib, htot, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sub_self]) j (Finset.mem_univ j)`. Establish `hsq : ‖a j - c‖ ^ 2 ≤ 0`.

Rewrite using `[norm_sub_sq_real, real_inner_comm]`. Use polynomial arithmetic with `[hle j, norm_nonneg (a j), norm_nonneg c]`. Conclude with `sub_eq_zero.1 (norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 (le_antisymm hsq (sq_nonneg _))))`.
-/
theorem eq_of_sum_eq_nsmul_of_norm_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}
    (a : Fin m → E) (c : E) (hle : ∀ j, ‖a j‖ ≤ ‖c‖) (hsum : ∑ j, a j = m • c) (j : Fin m) :
    a j = c := by
  have hj : ∀ i, ⟪c, a i⟫ ≤ ‖c‖ ^ 2 := fun i =>
    (real_inner_le_norm c (a i)).trans
      (by rw [sq]; exact mul_le_mul_of_nonneg_left (hle i) (norm_nonneg c))
  have htot : ∑ i, ⟪c, a i⟫ = m * ‖c‖ ^ 2 := by
    rw [← inner_sum, hsum, ← Nat.cast_smul_eq_nsmul ℝ, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sub_nonneg.2 (hj i))).1
    (by rw [Finset.sum_sub_distrib, htot, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, sub_self]) j (Finset.mem_univ j)
  have hsq : ‖a j - c‖ ^ 2 ≤ 0 := by
    rw [norm_sub_sq_real, real_inner_comm]
    nlinarith [hle j, norm_nonneg (a j), norm_nonneg c]
  exact sub_eq_zero.1 (norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1
    (le_antisymm hsq (sq_nonneg _))))

/- English proof (translation)
Introduce `σ _ I w U g hI _ hw hU hg hle`. Take `⟨k, A, B, D, m, T, hB, hwB, hBU, hD, hwD, hfib, hT, hrep⟩` from `htr σ I w U g hI hw hU hg`. Establish `hle' : ∀ z ∈ zeroSetIn I ∩ B, ‖g z‖ ≤ ‖g w‖` using `fun z hz => hle z ⟨hz.1, hBU hz.2⟩`. Establish `hTw : T (A w) = m • g w`. Take `⟨x, hx, -, hTx⟩` from `hrep (A w) hwD`.

Rewrite using `[hTx, Finset.sum_congr rfl fun j _ => congrArg g (hfib (x j) (hx j).1 (hx j).2), Finset.sum_const, Finset.card_univ, Fintype.card_fin]`. Establish `hmax : IsLocalMax (norm ∘ T) (A w)` using `by filter_upwards [hD.mem_nhds hwD] with y hy`. Take `⟨x, hx, -, hTx⟩` from `hrep y hy`. Simplify using `only [Function.comp_apply, hTx, hTw]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin]`. Simplify using `[nsmul_eq_mul]`. Establish `hconst` using `Complex.eventually_eq_of_isLocalMax_norm (Filter.eventually_of_mem (hD.mem_nhds hwD) fun y hy => (hT y hy).differentiableAt (hD.mem_nhds hy)) hmax`. Establish `hcont : Tendsto A (𝓝 w) (𝓝 (A w))` using `A.continuous.tendsto w`. Use `filter_upwards [hB.mem_nhds hwB, hcont.eventually hconst, hcont.eventually (hD.mem_nhds hwD)] with z hzB hzT hzD hzZ`.

Take `⟨x, hx, hcov, hTx⟩` from `hrep (A z) hzD`. Take `⟨j, rfl⟩` from `hcov z ⟨hzZ, hzB⟩ rfl`. Conclude with `eq_of_sum_eq_nsmul_of_norm_le (fun i => g (x i)) (g w) (fun i => hle' _ (hx i).1) (by rw [← hTx, hzT, hTw]) j`.
-/
theorem NormalMaximumPrinciple.proof (htr : LocalTrace.Statement) : NormalMaximumPrinciple.Statement := by
  intro σ _ I w U g hI _ hw hU hg hle
  obtain ⟨k, A, B, D, m, T, hB, hwB, hBU, hD, hwD, hfib, hT, hrep⟩ := htr σ I w U g hI hw hU hg
  have hle' : ∀ z ∈ zeroSetIn I ∩ B, ‖g z‖ ≤ ‖g w‖ := fun z hz => hle z ⟨hz.1, hBU hz.2⟩

  have hTw : T (A w) = m • g w := by
    obtain ⟨x, hx, -, hTx⟩ := hrep (A w) hwD
    rw [hTx, Finset.sum_congr rfl fun j _ => congrArg g (hfib (x j) (hx j).1 (hx j).2),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin]

  have hmax : IsLocalMax (norm ∘ T) (A w) := by
    filter_upwards [hD.mem_nhds hwD] with y hy
    obtain ⟨x, hx, -, hTx⟩ := hrep y hy
    simp only [Function.comp_apply, hTx, hTw]
    calc ‖∑ j, g (x j)‖ ≤ ∑ j, ‖g (x j)‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin m, ‖g w‖ := Finset.sum_le_sum fun j _ => hle' _ (hx j).1
      _ = ‖m • g w‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; simp [nsmul_eq_mul]
  have hconst := Complex.eventually_eq_of_isLocalMax_norm
    (Filter.eventually_of_mem (hD.mem_nhds hwD) fun y hy =>
      (hT y hy).differentiableAt (hD.mem_nhds hy)) hmax
  have hcont : Tendsto A (𝓝 w) (𝓝 (A w)) := A.continuous.tendsto w
  filter_upwards [hB.mem_nhds hwB, hcont.eventually hconst, hcont.eventually (hD.mem_nhds hwD)]
    with z hzB hzT hzD hzZ
  obtain ⟨x, hx, hcov, hTx⟩ := hrep (A z) hzD
  obtain ⟨j, rfl⟩ := hcov z ⟨hzZ, hzB⟩ rfl
  exact eq_of_sum_eq_nsmul_of_norm_le (fun i => g (x i)) (g w) (fun i => hle' _ (hx i).1)
    (by rw [← hTx, hzT, hTw]) j

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
