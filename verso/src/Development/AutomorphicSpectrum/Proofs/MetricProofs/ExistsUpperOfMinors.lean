import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.BigCell

/- English proof (translation)
Take `rfl : P = Q` from `funext fun a => propext (hPQ a)`. Use `congr!`.
-/
theorem det_sub_congr {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (P Q : Fin N → Prop)
    [Fintype {a // P a}] [Fintype {a // Q a}] [DecidableEq {a // P a}] [DecidableEq {a // Q a}]
    (hPQ : ∀ a, P a ↔ Q a) :
    (h.submatrix (Subtype.val : {a // P a} → Fin N) Subtype.val).det =
      (h.submatrix (Subtype.val : {a // Q a} → Fin N) Subtype.val).det := by
  obtain rfl : P = Q := funext fun a => propext (hPQ a)
  congr!

/- English proof (translation)
Set `e : Fin S.card ≃ {a // P a}` to `(S.orderIsoOfFin rfl).toEquiv.trans (Equiv.subtypeEquivRight fun a => (hP a).symm)`. Rewrite using `[minorIJ, dif_pos rfl, ← Matrix.det_submatrix_equiv_self e]`. Use `congr 1`.
-/
theorem det_sub_eq_minorIJ {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N)) (P : Fin N → Prop)
    [Fintype {a // P a}] [DecidableEq {a // P a}] (hP : ∀ a, P a ↔ a ∈ S) :
    (h.submatrix (Subtype.val : {a // P a} → Fin N) Subtype.val).det = minorIJ h S S := by
  let e : Fin S.card ≃ {a // P a} :=
    (S.orderIsoOfFin rfl).toEquiv.trans (Equiv.subtypeEquivRight fun a => (hP a).symm)
  rw [minorIJ, dif_pos rfl, ← Matrix.det_submatrix_equiv_self e]
  congr 1

/- English proof (translation)
Introduce `N j h hj hbd hdet hmin`. Establish `hsplit` using `Matrix.twoBlockTriangular_det h (fun a : Fin N => (a : ℕ) < N - j) (fun a ha b hb => hbd a b fun e => ha (e.2 hb))`. Rewrite `hdet` using `[hsplit]`. Establish `hA` using `left_ne_zero_of_mul hdet`. Establish `hC` using `right_ne_zero_of_mul hdet`.

Establish `hu : ∀ b : Fin N, IsUnit (h.submatrix (Subtype.val : {a : Fin N // a ≤ b ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)} → Fin N) Subtype.val).det`. Introduce `b`. Rewrite using `[isUnit_iff_ne_zero]`. Establish `hbN` using `b.isLt`. Distinguish the cases in `hb : (b : ℕ) < N - j`.

Distinguish the cases in `hl : (b : ℕ) + 1 = N - j`. Rewrite using `[det_sub_congr h _ (fun a : Fin N => (a : ℕ) < N - j) fun a => by`. Simplify using `only [Fin.le_def, hb, iff_true]`. Use the proof step `omega]`. Conclude with `hA`.

Set `i : Fin N` to `⟨(b : ℕ) + j, by omega⟩`. Establish `hi : (i : ℕ) = (b : ℕ) + j` using `rfl`. Establish `hp : IsProperStep N j i` using `⟨by omega, by omega⟩`. Rewrite using `[det_sub_eq_minorIJ h (stepCols N j i) _ fun a => ?_]`. Conclude with `hmin i hp`.

Establish `: ¬ ((i : ℕ) + 1 ≤ j)` using `by omega`. Simplify using `only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg this, Fin.le_def, hb, iff_true]`. Use linear arithmetic over natural numbers and integers. Distinguish the cases in `hl : (b : ℕ) + 1 = N`. Rewrite using `[det_sub_congr h _ (fun a : Fin N => ¬ (a : ℕ) < N - j) fun a => by`.

Simplify using `only [Fin.le_def, hb, iff_false]`. Use `a.isLt` as an intermediate fact. Use the proof step `omega]`. Conclude with `hC`. Set `i : Fin N` to `⟨(b : ℕ) - (N - j), by omega⟩`.

Establish `hi : (i : ℕ) = (b : ℕ) - (N - j)` using `rfl`. Establish `hp : IsProperStep N j i` using `⟨by omega, by omega⟩`. Rewrite using `[det_sub_eq_minorIJ h (stepCols N j i) _ fun a => ?_]`. Conclude with `hmin i hp`. Establish `: (i : ℕ) + 1 ≤ j` using `by omega`.

Simplify using `only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos this, Fin.le_def, hb, iff_false]`. Use linear arithmetic over natural numbers and integers. Take `⟨B, h1, h2, h3⟩` from `hbd.exists_upper hu`. Use `⟨B, h1, h2, fun hB => ?_, h3⟩` and prove the remaining obligations. Use `h3.det` as an intermediate fact.

Rewrite `this` using `[Matrix.det_mul, hB, mul_zero]`. Conclude with `zero_ne_one this`.
-/
theorem exists_upper_of_minors : ∀ (N j : ℕ) (h : Matrix (Fin N) (Fin N) ℂ), j ≤ N → IsBlockDiag j h → h.det ≠ 0 → (∀ i : Fin N, IsProperStep N j i → minorIJ h (stepCols N j i) (stepCols N j i) ≠ 0) → ∃ B : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j B ∧ B.BlockTriangular id ∧ B.det ≠ 0 ∧ IsLowerUni (h * B) := by
  intro N j h hj hbd hdet hmin
  have hsplit := Matrix.twoBlockTriangular_det h (fun a : Fin N => (a : ℕ) < N - j)
    (fun a ha b hb => hbd a b fun e => ha (e.2 hb))
  rw [hsplit] at hdet
  have hA := left_ne_zero_of_mul hdet
  have hC := right_ne_zero_of_mul hdet
  have hu : ∀ b : Fin N, IsUnit (h.submatrix
      (Subtype.val : {a : Fin N // a ≤ b ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)} → Fin N) Subtype.val).det := by
    intro b
    rw [isUnit_iff_ne_zero]
    have hbN := b.isLt
    by_cases hb : (b : ℕ) < N - j
    · by_cases hl : (b : ℕ) + 1 = N - j
      · rw [det_sub_congr h _ (fun a : Fin N => (a : ℕ) < N - j) fun a => by
          simp only [Fin.le_def, hb, iff_true]; omega]
        exact hA
      · let i : Fin N := ⟨(b : ℕ) + j, by omega⟩
        have hi : (i : ℕ) = (b : ℕ) + j := rfl
        have hp : IsProperStep N j i := ⟨by omega, by omega⟩
        rw [det_sub_eq_minorIJ h (stepCols N j i) _ fun a => ?_]
        · exact hmin i hp
        · have : ¬ ((i : ℕ) + 1 ≤ j) := by omega
          simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg this, Fin.le_def, hb, iff_true]
          omega
    · by_cases hl : (b : ℕ) + 1 = N
      · rw [det_sub_congr h _ (fun a : Fin N => ¬ (a : ℕ) < N - j) fun a => by
          simp only [Fin.le_def, hb, iff_false]
          have := a.isLt
          omega]
        exact hC
      · let i : Fin N := ⟨(b : ℕ) - (N - j), by omega⟩
        have hi : (i : ℕ) = (b : ℕ) - (N - j) := rfl
        have hp : IsProperStep N j i := ⟨by omega, by omega⟩
        rw [det_sub_eq_minorIJ h (stepCols N j i) _ fun a => ?_]
        · exact hmin i hp
        · have : (i : ℕ) + 1 ≤ j := by omega
          simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos this, Fin.le_def, hb, iff_false]
          omega
  obtain ⟨B, h1, h2, h3⟩ := hbd.exists_upper hu
  refine ⟨B, h1, h2, fun hB => ?_, h3⟩
  have := h3.det
  rw [Matrix.det_mul, hB, mul_zero] at this
  exact zero_ne_one this

end GlobalTheory.CompanionTheory.Ar.PB.WSq.BigCell
