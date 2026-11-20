import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

variable {s : ℕ} {G : Matrix (Fin s) (Fin s) ℂ}

/- English proof (translation)
Establish `h1 : 0 < leadMinor G j` using `(h.submatrix Subtype.val_injective).det_pos`. Rewrite `h1` using `[Complex.lt_def]`. Conclude with `⟨by simpa using h1.1, by simpa using h1.2.symm⟩`.
-/
theorem leadMinor_pos_of_posDef (h : G.PosDef) (j : ℕ) : 0 < (leadMinor G j).re ∧ (leadMinor G j).im = 0 := by
  have h1 : 0 < leadMinor G j := (h.submatrix Subtype.val_injective).det_pos
  rw [Complex.lt_def] at h1
  exact ⟨by simpa using h1.1, by simpa using h1.2.symm⟩

/- English proof (translation)
Take `⟨a1, a2⟩` from `leadMinor_pos_of_posDef h ((i : ℕ) + 1)`. Take `⟨b1, b2⟩` from `leadMinor_pos_of_posDef h (i : ℕ)`. Use `⟨div_pos a1 b1, ?_⟩` and prove the remaining obligations. Establish `e : (fun a : {a : Fin s // (a : ℕ) < (i : ℕ) + 1} => if a.1 = i then i else a.1) = Subtype.val`. Use function extensionality and compare the values at `a`.

Use `split_ifs with ha`. Conclude with `ha.symm`. Both sides reduce to the same expression. Establish `ea : leadMinor G ((i : ℕ) + 1) = ((leadMinor G ((i : ℕ) + 1)).re : ℂ)` using `Complex.ext (by simp) (by simpa using a2)`. Establish `eb : leadMinor G (i : ℕ) = ((leadMinor G (i : ℕ)).re : ℂ)` using `Complex.ext (by simp) (by simpa using b2)`.

Simplify using `only [ldPart, Matrix.of_apply, grD]`. Rewrite using `[e, Complex.ofReal_div, ← ea, ← eb]`. Both sides reduce to the same expression.
-/
theorem ldPart_diag_of_posDef (h : G.PosDef) (i : Fin s) : 0 < grD G i ∧ ldPart G i i = grD G i := by
  obtain ⟨a1, a2⟩ := leadMinor_pos_of_posDef h ((i : ℕ) + 1)
  obtain ⟨b1, b2⟩ := leadMinor_pos_of_posDef h (i : ℕ)
  refine ⟨div_pos a1 b1, ?_⟩
  have e : (fun a : {a : Fin s // (a : ℕ) < (i : ℕ) + 1} => if a.1 = i then i else a.1) = Subtype.val := by
    funext a
    split_ifs with ha
    · exact ha.symm
    · rfl
  have ea : leadMinor G ((i : ℕ) + 1) = ((leadMinor G ((i : ℕ) + 1)).re : ℂ) :=
    Complex.ext (by simp) (by simpa using a2)
  have eb : leadMinor G (i : ℕ) = ((leadMinor G (i : ℕ)).re : ℂ) :=
    Complex.ext (by simp) (by simpa using b2)
  simp only [ldPart, Matrix.of_apply, grD]
  rw [e, Complex.ofReal_div, ← ea, ← eb]
  rfl

/- English proof (translation)
Establish `hij' : (i : ℕ) < j` using `hij`. Simplify using `only [ldPart, Matrix.of_apply]`. Rewrite using `[Matrix.det_zero_of_row_eq (i := ⟨i, by omega⟩) (j := ⟨j, by omega⟩), zero_div]`. Introduce `h`. Conclude with `hij.ne (congrArg Subtype.val h)`.

Use function extensionality and compare the values at `b`. Simplify using `[Matrix.submatrix_apply]`.
-/
theorem ldPart_eq_zero_of_lt (G : Matrix (Fin s) (Fin s) ℂ) {i j : Fin s} (hij : i < j) : ldPart G i j = 0 := by
  have hij' : (i : ℕ) < j := hij
  simp only [ldPart, Matrix.of_apply]
  rw [Matrix.det_zero_of_row_eq (i := ⟨i, by omega⟩) (j := ⟨j, by omega⟩), zero_div]
  · intro h
    exact hij.ne (congrArg Subtype.val h)
  · funext b
    simp [Matrix.submatrix_apply]

/- English proof (translation)
Introduce `s G h`. Use `⟨leadMinor_pos_of_posDef h, ldPart_diag_of_posDef h, fun i j hij => ldPart_eq_zero_of_lt G hij, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_of_lowerTriangular (ldPart G) (fun i j hij => ldPart_eq_zero_of_lt G (by simpa using hij)), isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]`. Introduce `i _`. Take `⟨h1, h2⟩` from `ldPart_diag_of_posDef h i`.

Rewrite using `[h2]`. Conclude with `h1.ne'` after adjusting the coercions.
-/
theorem ldPart_posDef_spec : ∀ (s : ℕ) (G : Matrix (Fin s) (Fin s) ℂ), G.PosDef → (∀ j, 0 < (leadMinor G j).re ∧ (leadMinor G j).im = 0) ∧ (∀ i, 0 < grD G i ∧ ldPart G i i = grD G i) ∧ (∀ i j, i < j → ldPart G i j = 0) ∧ IsUnit (ldPart G).det := by
  intro s G h
  refine ⟨leadMinor_pos_of_posDef h, ldPart_diag_of_posDef h, fun i j hij => ldPart_eq_zero_of_lt G hij, ?_⟩
  rw [Matrix.det_of_lowerTriangular (ldPart G) (fun i j hij => ldPart_eq_zero_of_lt G (by simpa using hij)),
    isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro i _
  obtain ⟨h1, h2⟩ := ldPart_diag_of_posDef h i
  rw [h2]
  exact_mod_cast h1.ne'

end GlobalTheory.ChernCalc
