import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsFibreChartIff
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJEqSubmatrix
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.Shear

variable {N : ℕ}

/- English proof (translation)
Rewrite using `[SchurCalc.elem_apply, if_neg hxy.ne, if_neg, add_zero]`. Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `lt_asymm hab hxy`.
-/
theorem shear_above {ca cb : Fin N} (hab : ca < cb) (t : ℂ) {x y : Fin N} (hxy : x < y) :
    (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) x y = 0 := by
  rw [SchurCalc.elem_apply, if_neg hxy.ne, if_neg, add_zero]
  rintro ⟨rfl, rfl⟩
  exact lt_asymm hab hxy

/- English proof (translation)
Rewrite using `[SchurCalc.elem_apply, if_pos rfl, if_neg, add_zero]`. Introduce and unpack `⟨rfl, h⟩`. Conclude with `hab.ne h`.
-/
theorem shear_diag {ca cb : Fin N} (hab : ca < cb) (t : ℂ) (x : Fin N) :
    (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) x x = 1 := by
  rw [SchurCalc.elem_apply, if_pos rfl, if_neg, add_zero]
  rintro ⟨rfl, h⟩
  exact hab.ne h

/- English proof (translation)
Rewrite using `[Matrix.det_of_lowerTriangular _ (fun x y h => shear_above hab t h)]`. Conclude with `Finset.prod_eq_one fun x _ => shear_diag hab t x`.
-/
theorem det_shear {ca cb : Fin N} (hab : ca < cb) (t : ℂ) :
    (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (fun x y h => shear_above hab t h)]
  exact Finset.prod_eq_one fun x _ => shear_diag hab t x

/- English proof (translation)
Establish `ht : ((1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ).submatrix (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl)).BlockTriangular OrderDual.toDual` using `fun x y h => shear_above hab t ((S.orderEmbOfFin rfl).strictMono h)`. Rewrite using `[MinorCalc.minorIJ_eq_det _ S S _ rfl rfl, Matrix.det_of_lowerTriangular _ ht]`. Conclude with `Finset.prod_eq_one fun x _ => shear_diag hab t _`.
-/
theorem minor_shear {ca cb : Fin N} (hab : ca < cb) (t : ℂ) (S : Finset (Fin N)) :
    minorIJ (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) S S = 1 := by
  have ht : ((1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ).submatrix (S.orderEmbOfFin rfl)
      (S.orderEmbOfFin rfl)).BlockTriangular OrderDual.toDual :=
    fun x y h => shear_above hab t ((S.orderEmbOfFin rfl).strictMono h)
  rw [MinorCalc.minorIJ_eq_det _ S S _ rfl rfl, Matrix.det_of_lowerTriangular _ ht]
  exact Finset.prod_eq_one fun x _ => shear_diag hab t _

/- English proof (translation)
Establish `hne : k ≠ c` using `fun e => hk (e ▸ hc)`. Rewrite using `[SchurCalc.elem_apply, if_neg hne, if_neg, add_zero]`. Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `hk (hS hc)`.
-/
theorem support_shear {ca cb : Fin N} (t : ℂ) {S : Finset (Fin N)} (hS : ca ∈ S → cb ∈ S) (k c : Fin N)
    (hc : c ∈ S) (hk : k ∉ S) : (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) k c = 0 := by
  have hne : k ≠ c := fun e => hk (e ▸ hc)
  rw [SchurCalc.elem_apply, if_neg hne, if_neg, add_zero]
  rintro ⟨rfl, rfl⟩
  exact hk (hS hc)

/- English proof (translation)
Rewrite using `[MinorCalc.minorIJ_mul_of_support _ _ _ _ (support_shear t hS), minor_shear hab, mul_one]`.
-/
theorem minor_mul_shear {ca cb : Fin N} (hab : ca < cb) (t : ℂ) {S : Finset (Fin N)} (hS : ca ∈ S → cb ∈ S)
    (A : Matrix (Fin N) (Fin N) ℂ) (I : Finset (Fin N)) :
    minorIJ (A * (1 + Matrix.single cb ca t)) I S = minorIJ A I S := by
  rw [MinorCalc.minorIJ_mul_of_support _ _ _ _ (support_shear t hS), minor_shear hab, mul_one]

/- English proof (translation)
Take `⟨H, hH⟩ : ∃ H, H = hᴴ * G * h` from `⟨_, rfl⟩`. Take `⟨U, hU⟩ : ∃ U : Matrix (Fin N) (Fin N) ℂ, U = 1 + Matrix.single cb ca t` from `⟨_, rfl⟩`. Establish `e : (h * U)ᴴ * G * (h * U) = (Uᴴ * H) * U`. Rewrite using `[hH]`. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`.

Rewrite using `[← hU, ← hH, e, hU, minor_mul_shear hab t hS, ← hU]`. Apply `star_injective` to reduce the goal to its premises. Rewrite using `[← SchurCalc.minor_conjTranspose, ← SchurCalc.minor_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose, hU, minor_mul_shear hab t hS]`.
-/
theorem minor_gram_shear {ca cb : Fin N} (hab : ca < cb) (t : ℂ) {S : Finset (Fin N)} (hS : ca ∈ S → cb ∈ S)
    (G h : Matrix (Fin N) (Fin N) ℂ) :
    minorIJ ((h * (1 + Matrix.single cb ca t))ᴴ * G * (h * (1 + Matrix.single cb ca t))) S S =
      minorIJ (hᴴ * G * h) S S := by
  obtain ⟨H, hH⟩ : ∃ H, H = hᴴ * G * h := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin N) (Fin N) ℂ, U = 1 + Matrix.single cb ca t := ⟨_, rfl⟩
  have e : (h * U)ᴴ * G * (h * U) = (Uᴴ * H) * U := by
    rw [hH]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [← hU, ← hH, e, hU, minor_mul_shear hab t hS, ← hU]
  apply star_injective
  rw [← SchurCalc.minor_conjTranspose, ← SchurCalc.minor_conjTranspose, conjTranspose_mul,
    conjTranspose_conjTranspose, hU, minor_mul_shear hab t hS]

/- English proof (translation)
Introduce `N j a b ca cb t hj hb hcase hca hcb`. Establish `hab : ca < cb` using `Fin.lt_def.2 (by omega)`. Establish `ha2` using `a.2`. Establish `hb2` using `b.2`. Establish `hcb2` using `cb.2`.

Unfold `lastCol at hca`. Establish `hblock : (ca : ℕ) < N - j ↔ (cb : ℕ) < N - j`. Break down `hcase with h | h` into its components or cases. Rewrite `hca` using `[if_pos (by omega)]`. Use linear arithmetic over natural numbers and integers.

Rewrite `hca` using `[if_neg (by omega)]`. Use linear arithmetic over natural numbers and integers. Establish `hw : ca ∈ wIdx N j → cb ∈ wIdx N j`. Simplify using `only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and]`. Use linear arithmetic over natural numbers and integers.

Establish `ho : ca ∈ omIdx N j → cb ∈ omIdx N j`. Simplify using `only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and]`. Use linear arithmetic over natural numbers and integers. Establish `hstep : ∀ i : Fin N, i ≠ a → ca ∈ stepCols N j i → cb ∈ stepCols N j i`. Introduce `i hi`.

Establish `hia : (i : ℕ) ≠ a` using `fun e => hi (Fin.ext e)`. Establish `hi2` using `i.2`. Simplify using `only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]`. Break down `hcase with h | h` into its components or cases. Apply the tactic sequence `rw [if_pos (by omega)] at hca split_ifs <;> omega`.

Apply the tactic sequence `rw [if_neg (by omega)] at hca split_ifs <;> omega`. Use `⟨?_, det_shear hab t, ?_, ?_⟩` and prove the remaining obligations. Introduce `p q hpq`. Rewrite using `[SchurCalc.elem_apply, if_neg (fun e => hpq (by rw [e])), if_neg, add_zero]`. Introduce and unpack `⟨rfl, rfl⟩`.

Conclude with `hpq hblock.symm`. Introduce `h i`. Unfold `facOf`. Rewrite using `[minor_mul_shear hab t hw, minor_mul_shear hab t ho]`. Introduce `G h i hi`.

Unfold `blockPot`. Rewrite using `[minor_gram_shear hab t (hstep i hi)]`.
-/
theorem shear_main : ∀ (N j : ℕ) (a b ca cb : Fin N) (t : ℂ), j ≤ N → (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) ∧ (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ).det = 1 ∧ (∀ h : Matrix (Fin N) (Fin N) ℂ, ∀ i, facOf N j a (h * (1 + Matrix.single cb ca t)) i = facOf N j a h i) ∧ ∀ G h : Matrix (Fin N) (Fin N) ℂ, ∀ i, i ≠ a → blockPot j i G (h * (1 + Matrix.single cb ca t)) = blockPot j i G h := by
  intro N j a b ca cb t hj hb hcase hca hcb
  have hab : ca < cb := Fin.lt_def.2 (by omega)
  have ha2 := a.2
  have hb2 := b.2
  have hcb2 := cb.2
  unfold lastCol at hca
  have hblock : (ca : ℕ) < N - j ↔ (cb : ℕ) < N - j := by
    rcases hcase with h | h
    · rw [if_pos (by omega)] at hca
      omega
    · rw [if_neg (by omega)] at hca
      omega
  have hw : ca ∈ wIdx N j → cb ∈ wIdx N j := by
    simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have ho : ca ∈ omIdx N j → cb ∈ omIdx N j := by
    simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hstep : ∀ i : Fin N, i ≠ a → ca ∈ stepCols N j i → cb ∈ stepCols N j i := by
    intro i hi
    have hia : (i : ℕ) ≠ a := fun e => hi (Fin.ext e)
    have hi2 := i.2
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hcase with h | h
    · rw [if_pos (by omega)] at hca
      split_ifs <;> omega
    · rw [if_neg (by omega)] at hca
      split_ifs <;> omega
  refine ⟨?_, det_shear hab t, ?_, ?_⟩
  · intro p q hpq
    rw [SchurCalc.elem_apply, if_neg (fun e => hpq (by rw [e])), if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    exact hpq hblock.symm
  · intro h i
    unfold facOf
    rw [minor_mul_shear hab t hw, minor_mul_shear hab t ho]
  · intro G h i hi
    unfold blockPot
    rw [minor_gram_shear hab t (hstep i hi)]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.Shear
