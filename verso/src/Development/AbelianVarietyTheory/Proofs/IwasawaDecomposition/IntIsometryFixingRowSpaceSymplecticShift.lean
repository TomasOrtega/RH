import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExponentialOfSemiAbelianFibreLinearChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombMatAddMul
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Establish `h4 : ε * M' * φᵀ = -1`. Use `congrArg Matrix.transpose h3` as an intermediate fact. Rewrite `this` using `[Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hM, Matrix.transpose_one]`. Rewrite using `[← neg_neg (ε * M' * φᵀ), ← this]`. Simplify using `[Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]`.

Establish `hPR : Matrix.fromRows ε φ * (M' * Matrix.fromCols (-φᵀ) εᵀ) = 1`. Rewrite using `[Matrix.mul_fromCols, Matrix.fromRows_mul_fromCols, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_neg, Matrix.mul_neg, h1, h2, h3, h4, neg_neg, neg_zero, Matrix.fromBlocks_one]`. Set `e : Fin g ⊕ Fin g ≃ Fin r` to `finSumFinEquiv.trans (finCongr (by omega))`. Establish `hRP : (M' * Matrix.fromCols (-φᵀ) εᵀ) * Matrix.fromRows ε φ = 1` using `(Matrix.mul_eq_one_comm_of_equiv e).mp hPR`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hRP, Matrix.mul_one]`. Use `_ = -(X * M' * φᵀ) * ε + (X * M' * εᵀ) * φ := by`. Rewrite using `[Matrix.mul_assoc M', Matrix.fromCols_mul_fromRows]`. Simplify using `only [Matrix.mul_add, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg]`.
-/
theorem symplecticPair_decomp {g r : ℕ} (hr : r = 2 * g) (M' : Matrix (Fin r) (Fin r) ℚ)
    (hM : M'ᵀ = -M') (ε φ : Matrix (Fin g) (Fin r) ℚ) (h1 : ε * M' * εᵀ = 0)
    (h2 : φ * M' * φᵀ = 0) (h3 : φ * M' * εᵀ = 1) (X : Matrix (Fin g) (Fin r) ℚ) :
    X = -(X * M' * φᵀ) * ε + (X * M' * εᵀ) * φ := by
  have h4 : ε * M' * φᵀ = -1 := by
    have := congrArg Matrix.transpose h3
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hM,
      Matrix.transpose_one] at this
    rw [← neg_neg (ε * M' * φᵀ), ← this]
    simp [Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]
  have hPR : Matrix.fromRows ε φ * (M' * Matrix.fromCols (-φᵀ) εᵀ) = 1 := by
    rw [Matrix.mul_fromCols, Matrix.fromRows_mul_fromCols, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_neg, Matrix.mul_neg,
      h1, h2, h3, h4, neg_neg, neg_zero, Matrix.fromBlocks_one]
  let e : Fin g ⊕ Fin g ≃ Fin r := finSumFinEquiv.trans (finCongr (by omega))
  have hRP : (M' * Matrix.fromCols (-φᵀ) εᵀ) * Matrix.fromRows ε φ = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv e).mp hPR
  calc X = X * ((M' * Matrix.fromCols (-φᵀ) εᵀ) * Matrix.fromRows ε φ) := by
        rw [hRP, Matrix.mul_one]
    _ = -(X * M' * φᵀ) * ε + (X * M' * εᵀ) * φ := by
        rw [Matrix.mul_assoc M', Matrix.fromCols_mul_fromRows]
        simp only [Matrix.mul_add, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg]

/- English proof (translation)
Introduce `g r r₀ rk M T c α φ β hr hMt hTM hcT hεε hφφ hφε hβ`. Establish `keyZ : T * M * cᵀ = M * cᵀ`. Combine the equalities or inequalities in the displayed calculation. Establish `hcTZ : c * T = c` using `hcT`. Establish `map_mul' : ∀ {a b d : ℕ} (A : Matrix (Fin a) (Fin b) ℤ) (B : Matrix (Fin b) (Fin d) ℤ), (A * B).map (Int.cast : ℤ → ℚ) = A.map (Int.cast : ℤ → ℚ) * B.map (Int.cast : ℤ → ℚ)` using `fun A B => Matrix.map_mul (f := Int.castRingHom ℚ)`.

Use `set M' := M.map (Int.cast : ℤ → ℚ) with hM'`. Use `set T' := T.map (Int.cast : ℤ → ℚ) with hT'`. Use `set c' := c.map (Int.cast : ℤ → ℚ) with hc'`. Establish `key : T' * M' * c'ᵀ = M' * c'ᵀ`. Use `congrArg (fun A => A.map (Int.cast : ℤ → ℚ)) keyZ` as an intermediate fact.

Simplify `this` using `only [map_mul', Matrix.transpose_map]`. Establish `hcT' : c' * T' = c'`. Use `congrArg (fun A => A.map (Int.cast : ℤ → ℚ)) hcTZ` as an intermediate fact. Simplify `this` using `only [map_mul']`. Establish `hMt' : M'ᵀ = -M'`.

Rewrite using `[hM', ← Matrix.transpose_map, hMt]`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Use `set ε := α * c' with hε`. Use `set X := φ * T' - φ with hX`.

Establish `hXc : X * M' * c'ᵀ = 0`. Rewrite using `[hX, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc φ T', Matrix.mul_assoc φ (T' * M'), key, Matrix.mul_assoc φ M', sub_self]`. Establish `hXε : X * M' * εᵀ = 0`. Rewrite using `[hε, Matrix.transpose_mul, ← Matrix.mul_assoc, hXc, Matrix.zero_mul]`. Establish `hdec` using `symplecticPair_decomp hr M' hMt' ε φ hεε hφφ hφε X`.

Rewrite `hdec` using `[hXε, Matrix.zero_mul, add_zero]`. Use `⟨-(X * M' * φᵀ)ᵀ, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j hij`. Simplify using `only [Matrix.neg_apply, Matrix.transpose_apply, neg_eq_zero]`. Break down `hij with hi | hj` into its components or cases.

Establish `: (X * M' * φᵀ) j i = (X * M' * c'ᵀ * βᵀ) j i`. Rewrite using `[Matrix.mul_assoc (X * M') c'ᵀ, ← Matrix.transpose_mul]`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[hβ i hi m]`.

Simplify using `only [Matrix.mul_apply]`. Rewrite using `[this, hXc, Matrix.zero_mul, Matrix.zero_apply]`. Establish `hrow : ∀ m, X j m = 0`. Introduce `m`. Establish `hφj : ∀ m, φ j m = (β * c') j m` using `hβ j hj`.

Rewrite using `[hX, Matrix.sub_apply, Matrix.mul_apply, hφj m]`. Establish `: ∑ k, φ j k * T' k m = ((β * c') * T') j m`. Simplify using `only [Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hφj k]`.

Simplify using `only [Matrix.mul_apply]`. Rewrite using `[this, Matrix.mul_assoc, hcT', sub_self]`. Simplify using `only [Matrix.mul_apply, hrow, zero_mul, Finset.sum_const_zero]`. Rewrite using `[Matrix.transpose_neg, Matrix.transpose_transpose, ← hdec, hX]`. Normalize the expressions using the abelian group laws.
-/
theorem isometry_fixing_rowSpace_shift : ∀ (g r r₀ rk : ℕ) (M T : Matrix (Fin r) (Fin r) ℤ) (c : Matrix (Fin r₀) (Fin r) ℤ) (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (β : Matrix (Fin g) (Fin r₀) ℚ), r = 2 * g → Mᵀ = -M → T * M * Tᵀ = M → c * T = c → (α * c.map (Int.cast : ℤ → ℚ)) * M.map (Int.cast : ℤ → ℚ) * (α * c.map (Int.cast : ℤ → ℚ))ᵀ = 0 → φ * M.map (Int.cast : ℤ → ℚ) * φᵀ = 0 → φ * M.map (Int.cast : ℤ → ℚ) * (α * c.map (Int.cast : ℤ → ℚ))ᵀ = 1 → (∀ j : Fin g, rk ≤ j.val → ∀ m, φ j m = (β * c.map (Int.cast : ℤ → ℚ)) j m) → ∃ b : Matrix (Fin g) (Fin g) ℚ, (∀ i j : Fin g, (rk ≤ i.val ∨ rk ≤ j.val) → b i j = 0) ∧ φ * T.map (Int.cast : ℤ → ℚ) = φ + bᵀ * (α * c.map (Int.cast : ℤ → ℚ)) := by
  intro g r r₀ rk M T c α φ β hr hMt hTM hcT hεε hφφ hφε hβ
  have keyZ : T * M * cᵀ = M * cᵀ := by
    calc T * M * cᵀ = T * M * (c * T)ᵀ := by rw [hcT]
      _ = T * M * Tᵀ * cᵀ := by rw [Matrix.transpose_mul, Matrix.mul_assoc (T * M)]
      _ = M * cᵀ := by rw [hTM]
  have hcTZ : c * T = c := hcT
  have map_mul' : ∀ {a b d : ℕ} (A : Matrix (Fin a) (Fin b) ℤ) (B : Matrix (Fin b) (Fin d) ℤ),
      (A * B).map (Int.cast : ℤ → ℚ) = A.map (Int.cast : ℤ → ℚ) * B.map (Int.cast : ℤ → ℚ) :=
    fun A B => Matrix.map_mul (f := Int.castRingHom ℚ)
  set M' := M.map (Int.cast : ℤ → ℚ) with hM'
  set T' := T.map (Int.cast : ℤ → ℚ) with hT'
  set c' := c.map (Int.cast : ℤ → ℚ) with hc'
  have key : T' * M' * c'ᵀ = M' * c'ᵀ := by
    have := congrArg (fun A => A.map (Int.cast : ℤ → ℚ)) keyZ
    simpa only [map_mul', Matrix.transpose_map] using this
  have hcT' : c' * T' = c' := by
    have := congrArg (fun A => A.map (Int.cast : ℤ → ℚ)) hcTZ
    simpa only [map_mul'] using this
  have hMt' : M'ᵀ = -M' := by
    rw [hM', ← Matrix.transpose_map, hMt]; ext i j; simp
  set ε := α * c' with hε
  set X := φ * T' - φ with hX
  have hXc : X * M' * c'ᵀ = 0 := by
    rw [hX, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_assoc φ T', Matrix.mul_assoc φ (T' * M'),
      key, Matrix.mul_assoc φ M', sub_self]
  have hXε : X * M' * εᵀ = 0 := by
    rw [hε, Matrix.transpose_mul, ← Matrix.mul_assoc, hXc, Matrix.zero_mul]
  have hdec := symplecticPair_decomp hr M' hMt' ε φ hεε hφφ hφε X
  rw [hXε, Matrix.zero_mul, add_zero] at hdec
  refine ⟨-(X * M' * φᵀ)ᵀ, ?_, ?_⟩
  · intro i j hij
    simp only [Matrix.neg_apply, Matrix.transpose_apply, neg_eq_zero]
    rcases hij with hi | hj
    ·
      have : (X * M' * φᵀ) j i = (X * M' * c'ᵀ * βᵀ) j i := by
        rw [Matrix.mul_assoc (X * M') c'ᵀ, ← Matrix.transpose_mul]
        simp only [Matrix.mul_apply, Matrix.transpose_apply]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [hβ i hi m]
        simp only [Matrix.mul_apply]
      rw [this, hXc, Matrix.zero_mul, Matrix.zero_apply]
    · have hrow : ∀ m, X j m = 0 := by
        intro m
        have hφj : ∀ m, φ j m = (β * c') j m := hβ j hj
        rw [hX, Matrix.sub_apply, Matrix.mul_apply, hφj m]
        have : ∑ k, φ j k * T' k m = ((β * c') * T') j m := by
          simp only [Matrix.mul_apply]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hφj k]; simp only [Matrix.mul_apply]
        rw [this, Matrix.mul_assoc, hcT', sub_self]
      simp only [Matrix.mul_apply, hrow, zero_mul, Finset.sum_const_zero]
  · rw [Matrix.transpose_neg, Matrix.transpose_transpose, ← hdec, hX]
    abel

end GlobalTheory
