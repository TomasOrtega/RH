import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBaseChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.LU

variable {N j : ℕ}

/- English proof (translation)
Establish `ha` using `a.2`. Establish `hb` using `b.2`. Rewrite using `[Fin.le_def, stepCols, Finset.mem_filter]`. Establish `hv : ((stepOf N j b : Fin N) : ℕ) = if N - j ≤ (b : ℕ) then (b : ℕ) - (N - j) else (b : ℕ) + j` using `rfl`. Generalize the expression as in `((stepOf N j b : Fin N) : ℕ) = i at hv ⊢`.

Simplify using `only [Finset.mem_univ, true_and]`. Apply the tactic sequence `split_ifs at hv ⊢ <;> omega`.
-/
theorem mem_stepCols_stepOf (hj : j ≤ N) (a b : Fin N) :
    a ∈ stepCols N j (stepOf N j b) ↔ a ≤ b ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) := by
  have ha := a.2
  have hb := b.2
  rw [Fin.le_def, stepCols, Finset.mem_filter]
  have hv : ((stepOf N j b : Fin N) : ℕ) = if N - j ≤ (b : ℕ) then (b : ℕ) - (N - j) else (b : ℕ) + j := rfl
  generalize ((stepOf N j b : Fin N) : ℕ) = i at hv ⊢
  simp only [Finset.mem_univ, true_and]
  split_ifs at hv ⊢ <;> omega

/- English proof (translation)
Set `e : Fin C.card ≃ {a // P a}` to `(C.orderIsoOfFin rfl).toEquiv.trans (Equiv.subtypeEquivRight hP)`. Rewrite using `[minorIJ, dif_pos rfl, ← Matrix.det_submatrix_equiv_self e (G.submatrix (Subtype.val : {a // P a} → Fin N) Subtype.val)]`. Both sides reduce to the same expression.
-/
theorem det_subtype_eq_minorIJ (G : Matrix (Fin N) (Fin N) ℂ) (C : Finset (Fin N)) (P : Fin N → Prop)
    [Fintype {a // P a}] [DecidableEq {a // P a}] (hP : ∀ a, a ∈ C ↔ P a) :
    (G.submatrix (Subtype.val : {a // P a} → Fin N) Subtype.val).det = minorIJ G C C := by
  let e : Fin C.card ≃ {a // P a} := (C.orderIsoOfFin rfl).toEquiv.trans (Equiv.subtypeEquivRight hP)
  rw [minorIJ, dif_pos rfl, ← Matrix.det_submatrix_equiv_self e
    (G.submatrix (Subtype.val : {a // P a} → Fin N) Subtype.val)]
  rfl

/- English proof (translation)
Distinguish the cases in `hp : IsProperStep N j (stepOf N j b)`. Conclude with `hs _ hp`. Establish `hb` using `b.2`. Establish `hlast : (b : ℕ) + 1 = N ∨ (b : ℕ) + 1 = N - j`. Simplify using `only [IsProperStep, stepOf, not_and_or, not_not] at hp`.

Apply the tactic sequence `split_ifs at hp <;> omega`. Establish `hD` using `GlobalTheory.CompanionTheory.Ar.PB.CPts.detFac_ne_zero hj (⟨N - 1, by omega⟩ : Fin N) hG hd`. Rewrite `hD` using `[detFac, if_pos (by simp only; omega), if_pos (by simp only; omega)]`. Distinguish the cases in `h : N - j ≤ (b : ℕ)`. Establish `e : stepCols N j (stepOf N j b) = wIdx N j`.

Use extensionality with `a`. Establish `ha` using `a.2`. Rewrite using `[mem_stepCols_stepOf hj, Fin.le_def]`. Simplify using `only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[e]`. Conclude with `left_ne_zero_of_mul hD`. Establish `e : stepCols N j (stepOf N j b) = omIdx N j`. Use extensionality with `a`. Establish `ha` using `a.2`.

Rewrite using `[mem_stepCols_stepOf hj, Fin.le_def]`. Simplify using `only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[e]`. Conclude with `right_ne_zero_of_mul hD`.
-/
theorem minor_stepOf_ne_zero (hj : j ≤ N) {G : Matrix (Fin N) (Fin N) ℂ} (hG : IsBlockDiag j G) (hd : G.det ≠ 0)
    (hs : ∀ i : Fin N, IsProperStep N j i → minorIJ G (stepCols N j i) (stepCols N j i) ≠ 0) (b : Fin N) :
    minorIJ G (stepCols N j (stepOf N j b)) (stepCols N j (stepOf N j b)) ≠ 0 := by
  by_cases hp : IsProperStep N j (stepOf N j b)
  · exact hs _ hp
  have hb := b.2
  have hlast : (b : ℕ) + 1 = N ∨ (b : ℕ) + 1 = N - j := by
    simp only [IsProperStep, stepOf, not_and_or, not_not] at hp
    split_ifs at hp <;> omega
  have hD := GlobalTheory.CompanionTheory.Ar.PB.CPts.detFac_ne_zero hj (⟨N - 1, by omega⟩ : Fin N) hG hd
  rw [detFac, if_pos (by simp only; omega), if_pos (by simp only; omega)] at hD
  by_cases h : N - j ≤ (b : ℕ)
  · have e : stepCols N j (stepOf N j b) = wIdx N j := by
      ext a
      have ha := a.2
      rw [mem_stepCols_stepOf hj, Fin.le_def]
      simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    rw [e]
    exact left_ne_zero_of_mul hD
  · have e : stepCols N j (stepOf N j b) = omIdx N j := by
      ext a
      have ha := a.2
      rw [mem_stepCols_stepOf hj, Fin.le_def]
      simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    rw [e]
    exact right_ne_zero_of_mul hD

/- English proof (translation)
Introduce `N j G hj hG hd hs`. Establish `hu : ∀ b : Fin N, IsUnit (G.submatrix (Subtype.val : {a : Fin N // a ≤ b ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)} → Fin N) Subtype.val).det` using `fun b => by`. Rewrite using `[det_subtype_eq_minorIJ G (stepCols N j (stepOf N j b)) _ fun a => mem_stepCols_stepOf hj a b]`. Conclude with `(minor_stepOf_ne_zero hj hG hd hs b).isUnit`. Take `⟨B, hB, hBt, hL⟩` from `hG.exists_upper hu`.

Establish `hdB : B.det ≠ 0` using `fun h => by`. Use `hL.det` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, h, mul_zero]`. Conclude with `zero_ne_one this`. Establish `huB : IsUnit B.det` using `hdB.isUnit`.

Use `letI := Matrix.invertibleOfIsUnitDet B huB`. Use `⟨G * B, B⁻¹, hG.mul hB, hL, hB.inv huB, blockTriangular_inv_of_blockTriangular hBt, fun c => ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : (B⁻¹).det ≠ 0` using `(Matrix.isUnit_nonsing_inv_det B huB).ne_zero`. Rewrite `h1` using `[Matrix.det_of_upperTriangular (blockTriangular_inv_of_blockTriangular hBt)]`. Conclude with `(Finset.prod_ne_zero_iff.1 h1) c (Finset.mem_univ c)`.

Rewrite using `[Matrix.mul_nonsing_inv_cancel_right _ _ huB]`.
-/
theorem exists_lower_upper : ∀ (N j : ℕ) (G : Matrix (Fin N) (Fin N) ℂ), j ≤ N → IsBlockDiag j G → G.det ≠ 0 →
    (∀ i : Fin N, IsProperStep N j i → minorIJ G (stepCols N j i) (stepCols N j i) ≠ 0) →
    ∃ L U : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j L ∧ IsLowerUni L ∧ IsBlockDiag j U ∧ U.BlockTriangular id ∧
      (∀ c, U c c ≠ 0) ∧ G = L * U := by
  intro N j G hj hG hd hs
  have hu : ∀ b : Fin N, IsUnit (G.submatrix
      (Subtype.val : {a : Fin N // a ≤ b ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)} → Fin N) Subtype.val).det := fun b => by
    rw [det_subtype_eq_minorIJ G (stepCols N j (stepOf N j b)) _ fun a => mem_stepCols_stepOf hj a b]
    exact (minor_stepOf_ne_zero hj hG hd hs b).isUnit
  obtain ⟨B, hB, hBt, hL⟩ := hG.exists_upper hu
  have hdB : B.det ≠ 0 := fun h => by
    have := hL.det
    rw [Matrix.det_mul, h, mul_zero] at this
    exact zero_ne_one this
  have huB : IsUnit B.det := hdB.isUnit
  letI := Matrix.invertibleOfIsUnitDet B huB
  refine ⟨G * B, B⁻¹, hG.mul hB, hL, hB.inv huB, blockTriangular_inv_of_blockTriangular hBt, fun c => ?_, ?_⟩
  · have h1 : (B⁻¹).det ≠ 0 := (Matrix.isUnit_nonsing_inv_det B huB).ne_zero
    rw [Matrix.det_of_upperTriangular (blockTriangular_inv_of_blockTriangular hBt)] at h1
    exact (Finset.prod_ne_zero_iff.1 h1) c (Finset.mem_univ c)
  · rw [Matrix.mul_nonsing_inv_cancel_right _ _ huB]

end GlobalTheory.CompanionTheory.Ar.PB.WMan.LU
