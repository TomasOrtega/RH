import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.ModelS.FMul

open GlobalTheory.CompanionTheory.ModelS

variable {n : ℕ}

/- English proof (translation)
The claim follows from `Fin.castLE_injective _`.
-/
theorem ini_injective (j : Fin n) : Function.Injective (ini j) :=
  Fin.castLE_injective _

/- English proof (translation)
Use extensionality with `a c`. Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply, id]`. Use `symm`. Use `Fintype.sum_of_injective (ini j) (ini_injective j) _ _ ?_ (fun i => rfl)` and prove the remaining obligations. Introduce `k hk`.

Establish `hjk : j < k`. Assume the negation of the conclusion as `h`. Establish `h' : (k : ℕ) ≤ j`. Use `not_lt.1 h` as an intermediate fact. Conclude with `Fin.le_def.1 this`.

Conclude with `hk ⟨⟨k, by omega⟩, by ext; rfl⟩`. Establish `haj : ini j a ≤ j`. Use `a.isLt` as an intermediate fact. Rewrite using `[Fin.le_def]`. Use `show (a : ℕ) ≤ j`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hz _ _ haj hjk, zero_mul]`.
-/
theorem rows_mul (j : Fin n) (p g : Mat n) (hz : ∀ a b : Fin n, a ≤ j → j < b → p a b = 0) :
    (p * g).submatrix (ini j) id = p.submatrix (ini j) (ini j) * g.submatrix (ini j) id := by
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, id]
  symm
  refine Fintype.sum_of_injective (ini j) (ini_injective j) _ _ ?_ (fun i => rfl)
  intro k hk
  have hjk : j < k := by
    by_contra h
    have h' : (k : ℕ) ≤ j := by
      have := not_lt.1 h
      exact Fin.le_def.1 this
    exact hk ⟨⟨k, by omega⟩, by ext; rfl⟩
  have haj : ini j a ≤ j := by
    have := a.isLt
    rw [Fin.le_def]
    show (a : ℕ) ≤ j
    omega
  rw [hz _ _ haj hjk, zero_mul]

/- English proof (translation)
Establish `h : (p * g).submatrix (ini j) (ini j) = p.submatrix (ini j) (ini j) * g.submatrix (ini j) (ini j)`. Use extensionality with `a c`. Conclude with `congrFun (congrFun (rows_mul j p g hz) a) (ini j c)`. Rewrite using `[lm, h, Matrix.det_mul, lm, lm]`.
-/
theorem lm_mul (j : Fin n) (p g : Mat n) (hz : ∀ a b : Fin n, a ≤ j → j < b → p a b = 0) :
    lm j (p * g) = lm j p * lm j g := by
  have h : (p * g).submatrix (ini j) (ini j) =
      p.submatrix (ini j) (ini j) * g.submatrix (ini j) (ini j) := by
    ext a c
    exact congrFun (congrFun (rows_mul j p g hz) a) (ini j c)
  rw [lm, h, Matrix.det_mul, lm, lm]

/- English proof (translation)
Rewrite using `[gm, rows_mul j p g hz, Matrix.conjTranspose_mul]`. Establish `h : p.submatrix (ini j) (ini j) * g.submatrix (ini j) id * ((g.submatrix (ini j) id)ᴴ * (p.submatrix (ini j) (ini j))ᴴ) = p.submatrix (ini j) (ini j) * (g.submatrix (ini j) id * (g.submatrix (ini j) id)ᴴ) * (p.submatrix (ini j) (ini j))ᴴ`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[h, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, lm, gm]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gm_mul (j : Fin n) (p g : Mat n) (hz : ∀ a b : Fin n, a ≤ j → j < b → p a b = 0) :
    gm j (p * g) = lm j p * star (lm j p) * gm j g := by
  rw [gm, rows_mul j p g hz, Matrix.conjTranspose_mul]
  have h : p.submatrix (ini j) (ini j) * g.submatrix (ini j) id *
      ((g.submatrix (ini j) id)ᴴ * (p.submatrix (ini j) (ini j))ᴴ) =
      p.submatrix (ini j) (ini j) * (g.submatrix (ini j) id * (g.submatrix (ini j) id)ᴴ) *
        (p.submatrix (ini j) (ini j))ᴴ := by
    simp only [Matrix.mul_assoc]
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, lm, gm]
  ring

/- English proof (translation)
Establish `h : ((1 : Mat n).submatrix (ini j) id) * ((1 : Mat n).submatrix (ini j) id)ᴴ = 1`. Rewrite using `[Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.mul_one, Matrix.submatrix_one _ (ini_injective j)]`. Rewrite using `[gm, h, Matrix.det_one]`.
-/
theorem gm_one (j : Fin n) : gm j (1 : Mat n) = 1 := by
  have h : ((1 : Mat n).submatrix (ini j) id) * ((1 : Mat n).submatrix (ini j) id)ᴴ = 1 := by
    rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one,
      ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.mul_one,
      Matrix.submatrix_one _ (ini_injective j)]
  rw [gm, h, Matrix.det_one]

/- English proof (translation)
Use `gm_mul j p 1 hz` as an intermediate fact. Rewrite `this` using `[Matrix.mul_one, gm_one, mul_one]`. Then use the resulting hypothesis.
-/
theorem gm_left (j : Fin n) (p : Mat n) (hz : ∀ a b : Fin n, a ≤ j → j < b → p a b = 0) :
    gm j p = lm j p * star (lm j p) := by
  have := gm_mul j p 1 hz
  rwa [Matrix.mul_one, gm_one, mul_one] at this

/- English proof (translation)
Take `⟨-, hl⟩` from `hl`. Establish `hlam` using `hl _ _ he`. Establish `hmu : muZ lam lev j = muZ lam lev ⟨j + 1, h⟩`. Simplify using `only [muZ, hlam, he]`. Establish `hy : yZ lam lev j = yZ lam lev ⟨j + 1, h⟩`.

Simplify using `only [yZ, hlam, hmu]`. Prove the components needed by the constructor for the conclusion. Simplify using `only [dif, dif_pos h, hmu, sub_self]`. Simplify using `only [dif, dif_pos h, hy, sub_self]`.
-/
theorem dif_eq_zero (lam : Fin n → ℤ) (lev : Fin n → ℕ) (hl : IsLev lam lev) (j : Fin n) (h : (j : ℕ) + 1 < n)
    (he : lev j = lev ⟨j + 1, h⟩) : dif (muZ lam lev) j = 0 ∧ dif (yZ lam lev) j = 0 := by
  obtain ⟨-, hl⟩ := hl
  have hlam := hl _ _ he
  have hmu : muZ lam lev j = muZ lam lev ⟨j + 1, h⟩ := by
    simp only [muZ, hlam, he]
  have hy : yZ lam lev j = yZ lam lev ⟨j + 1, h⟩ := by
    simp only [yZ, hlam, hmu]
  constructor
  · simp only [dif, dif_pos h, hmu, sub_self]
  · simp only [dif, dif_pos h, hy, sub_self]

/- English proof (translation)
Introduce `n lam _ lev hl p hp g hg`. Take `⟨hp1, hp2⟩` from `hp`. Establish `hpg : p * g ∈ GLs n` using `by show (p * g).det ≠ 0`. Rewrite using `[Matrix.det_mul]`. Conclude with `mul_ne_zero hp1 hg`.

Simplify using `only [fRaw, Set.indicator_of_mem hpg, Set.indicator_of_mem hp1, Set.indicator_of_mem hg]`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hgood : ∀ a b : Fin n, a ≤ j → j < b → lev a < lev b`. Establish `hz : ∀ a b : Fin n, a ≤ j → j < b → p a b = 0` using `fun a b h1 h2 => hp2 a b (hgood a b h1 h2)`.

Rewrite using `[lm_mul j p g hz, gm_mul j p g hz, ← gm_left j p hz, mul_zpow, mul_zpow, mul_mul_mul_comm]`. Use `push_neg at hgood`. Take `⟨a, b, haj, hjb, hba⟩` from `hgood`. Establish `hmono` using `hl.1`. Establish `hb : (j : ℕ) < b` using `Fin.lt_def.1 hjb`.

Establish `h : (j : ℕ) + 1 < n` using `by have := b.isLt; omega`. Establish `h1 : lev j ≤ lev ⟨j + 1, h⟩` using `hmono (Fin.le_def.2 (by simp))`. Establish `h2 : lev ⟨j + 1, h⟩ ≤ lev b` using `hmono (Fin.le_def.2 (by simpa using hb))`. Establish `h3 : lev a ≤ lev j` using `hmono haj`. Establish `he : lev j = lev ⟨j + 1, h⟩` using `by omega`.

Take `⟨d1, d2⟩` from `dif_eq_zero lam lev hl j h he`. Simplify using `only [d1, d2, zpow_zero, mul_one]`.
-/
theorem fRaw_mul : ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev →
    ∀ p ∈ GlobalTheory.CompanionTheory.ModelS.Pb lev, ∀ g ∈ GLs n,
      GlobalTheory.CompanionTheory.ModelS.fRaw lam lev (p * g) = GlobalTheory.CompanionTheory.ModelS.fRaw lam lev p * GlobalTheory.CompanionTheory.ModelS.fRaw lam lev g := by
  intro n lam _ lev hl p hp g hg
  obtain ⟨hp1, hp2⟩ := hp
  have hpg : p * g ∈ GLs n := by
    show (p * g).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hp1 hg
  simp only [fRaw, Set.indicator_of_mem hpg, Set.indicator_of_mem hp1, Set.indicator_of_mem hg]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hgood : ∀ a b : Fin n, a ≤ j → j < b → lev a < lev b
  · have hz : ∀ a b : Fin n, a ≤ j → j < b → p a b = 0 := fun a b h1 h2 => hp2 a b (hgood a b h1 h2)
    rw [lm_mul j p g hz, gm_mul j p g hz, ← gm_left j p hz, mul_zpow, mul_zpow, mul_mul_mul_comm]
  · push_neg at hgood
    obtain ⟨a, b, haj, hjb, hba⟩ := hgood
    have hmono := hl.1
    have hb : (j : ℕ) < b := Fin.lt_def.1 hjb
    have h : (j : ℕ) + 1 < n := by have := b.isLt; omega
    have h1 : lev j ≤ lev ⟨j + 1, h⟩ := hmono (Fin.le_def.2 (by simp))
    have h2 : lev ⟨j + 1, h⟩ ≤ lev b := hmono (Fin.le_def.2 (by simpa using hb))
    have h3 : lev a ≤ lev j := hmono haj
    have he : lev j = lev ⟨j + 1, h⟩ := by omega
    obtain ⟨d1, d2⟩ := dif_eq_zero lam lev hl j h he
    simp only [d1, d2, zpow_zero, mul_one]

end GlobalTheory.CompanionTheory.ModelS.FMul
