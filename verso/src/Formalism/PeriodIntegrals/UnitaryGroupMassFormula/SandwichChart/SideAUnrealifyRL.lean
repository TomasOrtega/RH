import Mathlib
import Formalism.PeriodIntegrals.LongWeylElementSquare
import Formalism.PeriodIntegrals.SwSand
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SandwichChart.SandwichOfOfCharts

noncomputable section

open Matrix Filter Topology Classical
open scoped ENNReal NNReal

namespace PI.SwSandwichOfWork

open PI.SwBig PI.SwSand

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

variable {k r : ℕ}

/- English proof (translation)
Use extensionality with `i j`. Use `first`. Consider the case `(apply Complex.ext <;> simp [unrealify, RL, realifyFun])`. Consider the case `(apply Complex.ext <;> rfl)`.
-/
private theorem SideA_unrealify_RL (X : Mat k r) : unrealify (RL X) = X := by
  ext i j
  first
    | (apply Complex.ext <;> simp [unrealify, RL, realifyFun])
    | (apply Complex.ext <;> rfl)

/- English proof (translation)
Establish `h1 : rhoS k r S x ≤ (‖(RL X : EuclideanSpace ℝ _)‖₊ : ℝ≥0∞)`. Unfold `rhoS`. Use `iInf₂_le (⟨RL X, hX⟩ : lieE S) ?_` and prove the remaining obligations. Use function extensionality and compare the values at `i j`. Simplify using `only [SideA_unrealify_RL, hx, Matrix.of_apply]`.

Combine the equalities or inequalities in the displayed calculation. Consider the case `(rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, ENNReal.ofReal_pow (norm_nonneg _)])`. Consider the case `(rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]; rfl)`. Consider the case `simp [ENNReal.ofReal_pow]`.
-/
private theorem SideA_rhoS_le (S : Set (Mat k r)) (X : Mat k r) (hX : RL X ∈ lieE S) (x : Mt k r)
    (hx : NormedSpace.exp X = Matrix.of x) :
    rhoS k r S x ^ 2 ≤ ENNReal.ofReal (‖RL X‖ ^ 2) := by
  have h1 : rhoS k r S x ≤ (‖(RL X : EuclideanSpace ℝ _)‖₊ : ℝ≥0∞) := by
    unfold rhoS
    refine iInf₂_le (⟨RL X, hX⟩ : lieE S) ?_
    funext i j
    simp only [SideA_unrealify_RL, hx, Matrix.of_apply]
  calc rhoS k r S x ^ 2 ≤ (‖(RL X : EuclideanSpace ℝ _)‖₊ : ℝ≥0∞) ^ 2 := by gcongr
    _ = ENNReal.ofReal (‖RL X‖ ^ 2) := by
      first
        | (rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, ENNReal.ofReal_pow (norm_nonneg _)])
        | (rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]; rfl)
        | simp [ENNReal.ofReal_pow]

/- English proof (translation)
Introduce `hNR hLG hLW hGU hPF hW0 hLEN hExpN hLI hCB k r ε hε hε1`. Take `⟨δ, hδ, hCBδ⟩` from `hCB k r (ε / 2) (by linarith)`. Use `⟨δ, hδ, fun ρ hρ hρδ n c m n' hn hm hn' hPsi => ?_⟩` and prove the remaining obligations. Take `⟨x, hxball, hxeq⟩` from `hPsi`. Establish `hxmem : (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) ∈ (uH k r).map RL`.

Rewrite using `[← hLG k r]`. Conclude with `x.2`. Take `⟨Y, hY, hYx⟩` from `Submodule.mem_map.mp hxmem`. Establish `hYn : ‖Y‖ < ρ`. Rewrite using `[← hNR k r Y, hYx]`.

Conclude with `mem_ball_zero_iff.mp hxball`. Establish `hexpY : NormedSpace.exp Y = w0B k r * (Matrix.of n * bigCell k r c 1 * Matrix.of m * (Matrix.of n')⁻¹)`. Use extensionality with `i j`. Establish `h` using `congrFun (congrFun hxeq i) j`. Simplify using `only [Psi] at h`.

Rewrite `h` using `[← hYx, SideA_unrealify_RL]`. Conclude with `h`. Take `⟨v, hv, hPhi, hvη, hLm⟩` from `hCBδ Y hY (hYn.trans hρδ)`. Establish `hv'` using `hv`. Rewrite `hv'` using `[Vs, Submodule.mem_prod, Submodule.mem_prod, Submodule.mem_prod]`.

Take `⟨hv1, -, hv3, hv4⟩` from `hv'`. Establish `hEq : Matrix.of n * bigCell k r c 1 * Matrix.of m * (Matrix.of n')⁻¹ = NormedSpace.exp v.1 * bigCell k r (1 + v.2.1) 1 * NormedSpace.exp v.2.2.1 * (NormedSpace.exp v.2.2.2)⁻¹`. Establish `h` using `hexpY.symm.trans (hPhi.symm.trans (hPF k r _ _ _ _))`. Establish `h2 : w0B k r * (w0B k r * (Matrix.of n * bigCell k r c 1 * Matrix.of m * (Matrix.of n')⁻¹)) = w0B k r * (w0B k r * (NormedSpace.exp v.1 * bigCell k r (1 + v.2.1) 1 * NormedSpace.exp v.2.2.1 * (NormedSpace.exp v.2.2.2)⁻¹))` using `by rw [h]`. Simplify using `only [← Matrix.mul_assoc, hW0 k r, Matrix.one_mul] at h2`.

Conclude with `h2`. Establish `hc2 : ∀ a, (1 + v.2.1) a ≠ 0`. Introduce `a h0`. Establish `hxa : ‖v.2.1 a‖ < 1`. Combine the equalities or inequalities in the displayed calculation.

Establish `h1 : v.2.1 a = -1`. Simplify using `only [Pi.add_apply, Pi.one_apply] at h0`. Take the linear combination `h0`. Rewrite `hxa` using `[h1]`. Simplify using `at hxa`.

Take `⟨hnX, hcx, hmZ, hn'X'⟩` from `hGU k r _ _ _ _ _ _ c (1 + v.2.1) hn (hExpN k r _ hv1) hm ((hLW k r).1 _ hv3) hn' (hExpN k r _ hv4) hc2 hEq`. Establish `hA` using `SideA_rhoS_le (Nset k r) v.1 (by rw [hLEN k r]; exact Submodule.mem_map_of_mem hv1) n hnX.symm`. Establish `hB` using `SideA_rhoS_le (UWb k r) v.2.2.1 (by rw [(hLW k r).2]; exact Submodule.mem_map_of_mem hv3) m hmZ.symm`. Establish `hC` using `SideA_rhoS_le (Nset k r) v.2.2.2 (by rw [hLEN k r]; exact Submodule.mem_map_of_mem hv4) n' hn'X'.symm`. Establish `hcs : ∑ a, ‖c a - 1‖ ^ 2 = ∑ a, ‖v.2.1 a‖ ^ 2`.

Rewrite using `[hcx]`. Simplify using the standard rewrite rules. Establish `hL0 : 0 ≤ ‖Lm k r v‖` using `norm_nonneg _`. Establish `hlt : ‖Lm k r v‖ < (1 + ε) * ρ`. Establish `h1 : (1 - ε / 2) * ‖Lm k r v‖ < ρ` using `lt_of_le_of_lt hLm hYn`.

Use polynomial arithmetic with `[mul_nonneg hε.le hL0, mul_nonneg (mul_nonneg hε.le (sub_nonneg.mpr hε1.le)) hL0]`. Establish `hsq : ‖Lm k r v‖ ^ 2 < ((1 + ε) * ρ) ^ 2` using `by nlinarith`. Establish `hsum : ‖RL v.1‖ ^ 2 + 2 * ∑ a, ‖v.2.1 a‖ ^ 2 + ‖RL v.2.2.1‖ ^ 2 + ‖RL v.2.2.2‖ ^ 2 = ‖Lm k r v‖ ^ 2`. Rewrite using `[← (hLI k r).2.2 v hv, hNR k r]`. Unfold `Qf`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hcs]`. Use `gcongr`. Use `_ = ENNReal.ofReal (‖RL v.1‖ ^ 2 + 2 * ∑ a, ‖v.2.1 a‖ ^ 2 + ‖RL v.2.2.1‖ ^ 2 + ‖RL v.2.2.2‖ ^ 2) := by`. Apply the tactic sequence `rw [ENNReal.ofReal_add, ENNReal.ofReal_add, ENNReal.ofReal_add] <;> positivity`.

Use `_ = ENNReal.ofReal (‖Lm k r v‖ ^ 2) := by rw [hsum]`. Use `_ < ENNReal.ofReal (((1 + ε) * ρ) ^ 2) := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hsq`.
-/
theorem sideA : SideA := by
  intro hNR hLG hLW hGU hPF hW0 hLEN hExpN hLI hCB k r ε hε hε1
  obtain ⟨δ, hδ, hCBδ⟩ := hCB k r (ε / 2) (by linarith)
  refine ⟨δ, hδ, fun ρ hρ hρδ n c m n' hn hm hn' hPsi => ?_⟩
  obtain ⟨x, hxball, hxeq⟩ := hPsi
  have hxmem : (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) ∈
      (uH k r).map RL := by
    rw [← hLG k r]
    exact x.2
  obtain ⟨Y, hY, hYx⟩ := Submodule.mem_map.mp hxmem
  have hYn : ‖Y‖ < ρ := by
    rw [← hNR k r Y, hYx]
    exact mem_ball_zero_iff.mp hxball
  have hexpY : NormedSpace.exp Y =
      w0B k r * (Matrix.of n * bigCell k r c 1 * Matrix.of m * (Matrix.of n')⁻¹) := by
    ext i j
    have h := congrFun (congrFun hxeq i) j
    simp only [Psi] at h
    rw [← hYx, SideA_unrealify_RL] at h
    exact h
  obtain ⟨v, hv, hPhi, hvη, hLm⟩ := hCBδ Y hY (hYn.trans hρδ)
  have hv' := hv
  rw [Vs, Submodule.mem_prod, Submodule.mem_prod, Submodule.mem_prod] at hv'
  obtain ⟨hv1, -, hv3, hv4⟩ := hv'

  have hEq : Matrix.of n * bigCell k r c 1 * Matrix.of m * (Matrix.of n')⁻¹ =
      NormedSpace.exp v.1 * bigCell k r (1 + v.2.1) 1 * NormedSpace.exp v.2.2.1 *
        (NormedSpace.exp v.2.2.2)⁻¹ := by
    have h := hexpY.symm.trans (hPhi.symm.trans (hPF k r _ _ _ _))
    have h2 : w0B k r * (w0B k r * (Matrix.of n * bigCell k r c 1 * Matrix.of m * (Matrix.of n')⁻¹)) =
        w0B k r * (w0B k r * (NormedSpace.exp v.1 * bigCell k r (1 + v.2.1) 1 *
          NormedSpace.exp v.2.2.1 * (NormedSpace.exp v.2.2.2)⁻¹)) := by rw [h]
    simp only [← Matrix.mul_assoc, hW0 k r, Matrix.one_mul] at h2
    exact h2
  have hc2 : ∀ a, (1 + v.2.1) a ≠ 0 := by
    intro a h0
    have hxa : ‖v.2.1 a‖ < 1 := by
      calc ‖v.2.1 a‖ ≤ ‖v.2.1‖ := norm_le_pi_norm _ a
        _ ≤ ‖v.2‖ := norm_fst_le _
        _ ≤ ‖v‖ := norm_snd_le _
        _ < ε / 2 := hvη
        _ < 1 := by linarith
    have h1 : v.2.1 a = -1 := by
      simp only [Pi.add_apply, Pi.one_apply] at h0
      linear_combination h0
    rw [h1] at hxa
    simp at hxa
  obtain ⟨hnX, hcx, hmZ, hn'X'⟩ := hGU k r _ _ _ _ _ _ c (1 + v.2.1) hn (hExpN k r _ hv1) hm
    ((hLW k r).1 _ hv3) hn' (hExpN k r _ hv4) hc2 hEq
  have hA := SideA_rhoS_le (Nset k r) v.1
    (by rw [hLEN k r]; exact Submodule.mem_map_of_mem hv1) n hnX.symm
  have hB := SideA_rhoS_le (UWb k r) v.2.2.1
    (by rw [(hLW k r).2]; exact Submodule.mem_map_of_mem hv3) m hmZ.symm
  have hC := SideA_rhoS_le (Nset k r) v.2.2.2
    (by rw [hLEN k r]; exact Submodule.mem_map_of_mem hv4) n' hn'X'.symm
  have hcs : ∑ a, ‖c a - 1‖ ^ 2 = ∑ a, ‖v.2.1 a‖ ^ 2 := by
    rw [hcx]
    simp
  have hL0 : 0 ≤ ‖Lm k r v‖ := norm_nonneg _
  have hlt : ‖Lm k r v‖ < (1 + ε) * ρ := by
    have h1 : (1 - ε / 2) * ‖Lm k r v‖ < ρ := lt_of_le_of_lt hLm hYn
    nlinarith [mul_nonneg hε.le hL0, mul_nonneg (mul_nonneg hε.le (sub_nonneg.mpr hε1.le)) hL0]
  have hsq : ‖Lm k r v‖ ^ 2 < ((1 + ε) * ρ) ^ 2 := by nlinarith
  have hsum : ‖RL v.1‖ ^ 2 + 2 * ∑ a, ‖v.2.1 a‖ ^ 2 + ‖RL v.2.2.1‖ ^ 2 + ‖RL v.2.2.2‖ ^ 2 =
      ‖Lm k r v‖ ^ 2 := by
    rw [← (hLI k r).2.2 v hv, hNR k r]
  unfold Qf
  calc rhoS k r (Nset k r) n ^ 2 + ENNReal.ofReal (2 * ∑ a, ‖c a - 1‖ ^ 2) +
        rhoS k r (UWb k r) m ^ 2 + rhoS k r (Nset k r) n' ^ 2
      ≤ ENNReal.ofReal (‖RL v.1‖ ^ 2) + ENNReal.ofReal (2 * ∑ a, ‖v.2.1 a‖ ^ 2) +
        ENNReal.ofReal (‖RL v.2.2.1‖ ^ 2) + ENNReal.ofReal (‖RL v.2.2.2‖ ^ 2) := by
        rw [hcs]
        gcongr
    _ = ENNReal.ofReal (‖RL v.1‖ ^ 2 + 2 * ∑ a, ‖v.2.1 a‖ ^ 2 + ‖RL v.2.2.1‖ ^ 2 +
        ‖RL v.2.2.2‖ ^ 2) := by
        rw [ENNReal.ofReal_add, ENNReal.ofReal_add, ENNReal.ofReal_add] <;> positivity
    _ = ENNReal.ofReal (‖Lm k r v‖ ^ 2) := by rw [hsum]
    _ < ENNReal.ofReal (((1 + ε) * ρ) ^ 2) :=
        (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hsq

end PI.SwSandwichOfWork
