import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

namespace GlobalTheory.FlagCell2

/- English proof (translation)
Simplify using `only [upU, Matrix.of_apply]`. Use `split_ifs with hk`. Conclude with `h ⟨(k, a), hk⟩ ha`. Both sides reduce to the same expression. Both sides reduce to the same expression.
-/
theorem upU_row_eq {s : ℕ} (y y' : Low s → ℂ) (i : Fin s)
    (h : ∀ j : Low s, j.1.2 ≤ i → y' j = y j) (a : Fin s) (ha : a ≤ i) (k : Fin s) :
    upU y' a k = upU y a k := by
  simp only [upU, Matrix.of_apply]
  split_ifs with hk
  · exact h ⟨(k, a), hk⟩ ha
  · rfl
  · rfl

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply, upU_row_eq y y' i h a ha, upU_row_eq y y' i h c hc]`.
-/
theorem upU_gram_entry_eq {s : ℕ} (G : Matrix (Fin s) (Fin s) ℂ) (y y' : Low s → ℂ) (i : Fin s)
    (h : ∀ j : Low s, j.1.2 ≤ i → y' j = y j) (a c : Fin s) (ha : a ≤ i) (hc : c ≤ i) :
    (upU y' * G * (upU y')ᴴ) a c = (upU y * G * (upU y)ᴴ) a c := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, upU_row_eq y y' i h a ha,
    upU_row_eq y y' i h c hc]

/- English proof (translation)
Unfold `leadMinor`. Use `congr 1`. Use extensionality with `a b`. Simplify using `only [Matrix.submatrix_apply]`. Apply `upU_gram_entry_eq G y y' i h` to reduce the goal to its premises.

Rewrite using `[Fin.le_def]`. Use `a.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[Fin.le_def]`. Use `b.2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem leadMinor_upU_gram_eq {s : ℕ} (G : Matrix (Fin s) (Fin s) ℂ) (y y' : Low s → ℂ) (i : Fin s)
    (h : ∀ j : Low s, j.1.2 ≤ i → y' j = y j) (j : ℕ) (hj : j ≤ (i : ℕ) + 1) :
    leadMinor (upU y' * G * (upU y')ᴴ) j = leadMinor (upU y * G * (upU y)ᴴ) j := by
  unfold leadMinor
  congr 1
  ext a b
  simp only [Matrix.submatrix_apply]
  apply upU_gram_entry_eq G y y' i h
  · rw [Fin.le_def]; have := a.2; omega
  · rw [Fin.le_def]; have := b.2; omega

/- English proof (translation)
Introduce `s G y y' i h`. Unfold `grD`. Rewrite using `[leadMinor_upU_gram_eq G y y' i h _ (by simp), leadMinor_upU_gram_eq G y y' i h _ (by omega)]`.
-/
theorem grD_upU_gram_eq : ∀ (s : ℕ) (G : Matrix (Fin s) (Fin s) ℂ) (y y' : Low s → ℂ) (i : Fin s), (∀ j : Low s, j.1.2 ≤ i → y' j = y j) → grD (upU y' * G * (upU y')ᴴ) i = grD (upU y * G * (upU y)ᴴ) i := by
  intro s G y y' i h
  unfold grD
  rw [leadMinor_upU_gram_eq G y y' i h _ (by simp), leadMinor_upU_gram_eq G y y' i h _ (by omega)]

end GlobalTheory.FlagCell2
