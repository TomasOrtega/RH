import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartBottomLeftBlock
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ChartGraph

namespace GlobalTheory.ChartGraph

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Rewrite using `[Matrix.det_of_lowerTriangular (chartMatrixTopBlock X z τ) (by`. Introduce `i j hij`. Establish `hij' : i < j` using `hij`. Use `show nmat X z τ (Fin.castLE X.p0_le i) (Fin.castLE X.p0_le j) = 0`. Establish `h1 : ¬ (Fin.castLE X.p0_le j < Fin.castLE X.p0_le i)`.

Rewrite using `[Fin.lt_iff_val_lt_val]`. Simplify using `only [Fin.coe_castLE]`. Conclude with `not_lt.mpr (le_of_lt hij')`. Establish `h2 : Fin.castLE X.p0_le i ≠ Fin.castLE X.p0_le j`. Introduce `h`.

Apply `ne_of_lt hij'` to reduce the goal to its premises. Conclude with `Fin.castLE_injective _ h`. Simplify using `only [nmat, dif_neg h1, if_neg h2])]`. Apply `Finset.prod_eq_one` to reduce the goal to its premises. Introduce `i _`.

Use `show nmat X z τ (Fin.castLE X.p0_le i) (Fin.castLE X.p0_le i) = 1`. Simplify using `[nmat]`.
-/
theorem chartMatrixTopBlock_det_eq_one (X : Data E r) (z : V (nd X)) (τ : X.Ψ) : (chartMatrixTopBlock X z τ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular (chartMatrixTopBlock X z τ) (by
    intro i j hij
    have hij' : i < j := hij
    show nmat X z τ (Fin.castLE X.p0_le i) (Fin.castLE X.p0_le j) = 0
    have h1 : ¬ (Fin.castLE X.p0_le j < Fin.castLE X.p0_le i) := by
      rw [Fin.lt_iff_val_lt_val]; simp only [Fin.coe_castLE]; exact not_lt.mpr (le_of_lt hij')
    have h2 : Fin.castLE X.p0_le i ≠ Fin.castLE X.p0_le j := by
      intro h; apply ne_of_lt hij'; exact Fin.castLE_injective _ h
    simp only [nmat, dif_neg h1, if_neg h2])]
  apply Finset.prod_eq_one
  intro i _
  show nmat X z τ (Fin.castLE X.p0_le i) (Fin.castLE X.p0_le i) = 1
  simp [nmat]

/- English proof (translation)
Distinguish the cases in `hm : (m : ℕ) < X.p0`. Establish `hrow : ∀ c : Fin X.p0, X.lowBlock (graphCoord X z) τ m (Fin.castLE X.p0_le c) = if (⟨m, hm⟩ : Fin X.p0) = c then 1 else 0`. Introduce `c`. Simplify using `only [Data.lowBlock, Matrix.of_apply]`. Rewrite using `[dif_neg (by omega)]`.

Simplify using `only [add_zero]`. Use `congr 1`. Apply `propext` to reduce the goal to its premises. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `hv : (m : ℕ) = (c : ℕ)` using `by simpa using congrArg (fun t : Fin r => (t : ℕ)) h`. Conclude with `Fin.ext hv`. Introduce `h`. Use `ext`. Rewrite using `[← h]`.

Both sides reduce to the same expression. Simplify using `only [hrow, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Both sides reduce to the same expression. Establish `hm' : X.p0 ≤ (m : ℕ)` using `not_lt.mp hm`. Establish `hrow : ∀ c : Fin X.p0, X.lowBlock (graphCoord X z) τ m (Fin.castLE X.p0_le c) = graphCoord X z τ ⟨(m : ℕ) - X.p0, by have` using `m.isLt; omega⟩ c := by`.

Introduce `c`. Simplify using `only [Data.lowBlock, Matrix.of_apply]`. Establish `hne : m ≠ Fin.castLE X.p0_le c`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact.

Simplify using `at this`. Use `c.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg hne, dif_pos ⟨hm', c.isLt⟩, zero_add]`. Both sides reduce to the same expression.

Simplify using `only [hrow]`. Establish `hdet : IsUnit (chartMatrixTopBlock X z τ).det` using `by rw [chartMatrixTopBlock_det_eq_one]; exact isUnit_one`. Establish `key : chartBottomLeftBlock X z τ * (chartMatrixTopBlock X z τ)⁻¹ * chartMatrixTopBlock X z τ = chartBottomLeftBlock X z τ`. Rewrite using `[Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]`. Use `congrFun (congrFun key ⟨(m : ℕ) - X.p0, by have := m.isLt; omega⟩) a` as an intermediate fact.

Rewrite `this` using `[Matrix.mul_apply]`. Establish `h2 : chartBottomLeftBlock X z τ ⟨(m : ℕ) - X.p0, by have` using `m.isLt; omega⟩ a = nmat X z τ m (Fin.castLE X.p0_le a) := by show nmat X z τ ⟨X.p0 + ((m : ℕ) - X.p0), _⟩ (Fin.castLE X.p0_le a) = _`. Use `congr 1`. Use `ext`. Simplify using `only`.

Use linear arithmetic over natural numbers and integers. Conclude with `(this.trans h2).symm`.
-/
theorem entry_eq (X : Data E r) (z : V (nd X)) (τ : X.Ψ) (m : Fin r) (a : Fin X.p0) :
    nmat X z τ m (Fin.castLE X.p0_le a) =
      ∑ c : Fin X.p0, X.lowBlock (graphCoord X z) τ m (Fin.castLE X.p0_le c) * chartMatrixTopBlock X z τ c a := by
  by_cases hm : (m : ℕ) < X.p0
  · have hrow : ∀ c : Fin X.p0, X.lowBlock (graphCoord X z) τ m (Fin.castLE X.p0_le c) =
        if (⟨m, hm⟩ : Fin X.p0) = c then 1 else 0 := by
      intro c
      simp only [Data.lowBlock, Matrix.of_apply]
      rw [dif_neg (by omega)]
      simp only [add_zero]
      congr 1
      apply propext
      constructor
      · intro h
        have hv : (m : ℕ) = (c : ℕ) := by simpa using congrArg (fun t : Fin r => (t : ℕ)) h
        exact Fin.ext hv
      · intro h; ext; rw [← h]; rfl
    simp only [hrow, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rfl
  · have hm' : X.p0 ≤ (m : ℕ) := not_lt.mp hm
    have hrow : ∀ c : Fin X.p0, X.lowBlock (graphCoord X z) τ m (Fin.castLE X.p0_le c) =
        graphCoord X z τ ⟨(m : ℕ) - X.p0, by have := m.isLt; omega⟩ c := by
      intro c
      simp only [Data.lowBlock, Matrix.of_apply]
      have hne : m ≠ Fin.castLE X.p0_le c := by
        intro h; have := congrArg Fin.val h; simp at this; have := c.isLt; omega
      rw [if_neg hne, dif_pos ⟨hm', c.isLt⟩, zero_add]
      rfl
    simp only [hrow]
    have hdet : IsUnit (chartMatrixTopBlock X z τ).det := by rw [chartMatrixTopBlock_det_eq_one]; exact isUnit_one
    have key : chartBottomLeftBlock X z τ * (chartMatrixTopBlock X z τ)⁻¹ * chartMatrixTopBlock X z τ = chartBottomLeftBlock X z τ := by
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]
    have := congrFun (congrFun key ⟨(m : ℕ) - X.p0, by have := m.isLt; omega⟩) a
    rw [Matrix.mul_apply] at this
    have h2 : chartBottomLeftBlock X z τ ⟨(m : ℕ) - X.p0, by have := m.isLt; omega⟩ a = nmat X z τ m (Fin.castLE X.p0_le a) := by
      show nmat X z τ ⟨X.p0 + ((m : ℕ) - X.p0), _⟩ (Fin.castLE X.p0_le a) = _
      congr 1
      ext; simp only; omega
    exact (this.trans h2).symm

/- English proof (translation)
Introduce `E _ _ _ r X x z τ`. Use `⟨chartMatrixTopBlock_det_eq_one X z τ, fun a => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `k`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Use `show (mat x τ * mat (nmat X z) τ) k (Fin.castLE X.p0_le a) = ∑ c : Fin X.p0, chartMatrixTopBlock X z τ c a * (mat x τ * X.lowBlock (graphCoord X z) τ) k (Fin.castLE X.p0_le c)`.

Simplify using `only [Matrix.mul_apply, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Use `show mat x τ k m * nmat X z τ m (Fin.castLE X.p0_le a) = _`. Rewrite using `[entry_eq, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cols_graph : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r)
    (z : V (nd X)) (τ : X.Ψ), (chartMatrixTopBlock X z τ).det = 1 ∧ ∀ a : Fin X.p0,
    col (mat (cpt X x z) τ) (Fin.castLE X.p0_le a) =
      ∑ c : Fin X.p0, chartMatrixTopBlock X z τ c a • col (mat (X.xZ x (graphCoord X z)) τ) (Fin.castLE X.p0_le c) := by
  intro E _ _ _ r X x z τ
  refine ⟨chartMatrixTopBlock_det_eq_one X z τ, fun a => ?_⟩
  funext k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  show (mat x τ * mat (nmat X z) τ) k (Fin.castLE X.p0_le a) =
    ∑ c : Fin X.p0, chartMatrixTopBlock X z τ c a * (mat x τ * X.lowBlock (graphCoord X z) τ) k (Fin.castLE X.p0_le c)
  simp only [Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  show mat x τ k m * nmat X z τ m (Fin.castLE X.p0_le a) = _
  rw [entry_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

end GlobalTheory.ChartGraph
