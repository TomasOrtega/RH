import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

/- English proof (translation)
Use `⟨∏ i, (c i).den, fun j => (c j).num * (((∏ i, (c i).den) / (c j).den : ℕ) : ℤ), ?_, ?_⟩` and prove the remaining obligations. Conclude with `Finset.prod_pos (fun i _ => (c i).den_pos)`. Introduce `j`. Take `⟨k, hk⟩ : (c j).den ∣ ∏ i, (c i).den` from `Finset.dvd_prod_of_mem _ (Finset.mem_univ j)`. Use `show (((c j).num * (((∏ i, (c i).den) / (c j).den : ℕ) : ℤ) : ℤ) : ℚ) = ((∏ i, (c i).den : ℕ) : ℚ) * c j`.

Rewrite using `[hk, Nat.mul_div_cancel_left _ (c j).den_pos]`. Use `push_cast`. Rewrite using `[← Rat.mul_den_eq_num]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_clear_denominators_bis {J : Type} [Fintype J] (c : J → ℚ) :
    ∃ (q : ℕ) (n : J → ℤ), 0 < q ∧ ∀ j, (n j : ℚ) = q * c j := by
  classical
  refine ⟨∏ i, (c i).den, fun j => (c j).num * (((∏ i, (c i).den) / (c j).den : ℕ) : ℤ), ?_, ?_⟩
  · exact Finset.prod_pos (fun i _ => (c i).den_pos)
  · intro j
    obtain ⟨k, hk⟩ : (c j).den ∣ ∏ i, (c i).den := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
    show (((c j).num * (((∏ i, (c i).den) / (c j).den : ℕ) : ℤ) : ℤ) : ℚ) = ((∏ i, (c i).den : ℕ) : ℚ) * c j
    rw [hk, Nat.mul_div_cancel_left _ (c j).den_pos]
    push_cast
    rw [← Rat.mul_den_eq_num]
    ring

end RootFieldNumerics

/- English proof (translation)
Introduce `Ψ _ N M lam s hlam`. Use `choose f hf using hlam`. Set `c : Option (Ψ × Fin N) → ℚ` to `fun j => match j with`. Consider the case `some r => -f r.1 r.2`. Consider the case `none => s / M.kA`.

Take `⟨q, n, hq, hn⟩` from `RootFieldNumerics.exists_clear_denominators_bis c`. Use `⟨q, n, hq, fun j => ?_⟩` and prove the remaining obligations. Establish `h : ((n j : ℚ) : ℝ) = ((q * c j : ℚ) : ℝ)` using `by rw [hn j]`. Move the coercions through the operations in `at h`. Rewrite using `[h]`.

Use `congr 1`. Consider the cases of `j with`. Consider the case `none => simp [c, RootModel.coef]`. Consider the case `some r => simp [c, RootModel.coef, hf]`.
-/
theorem RootFieldNumerics.exists_integer_coefficients_rational : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (lam : Wt Ψ N) (s : ℚ), IsRatWt lam → ∃ (q : ℕ) (n : Option (Ψ × Fin N) → ℤ), 0 < q ∧ ∀ j, (n j : ℝ) = q * M.coef lam s j := by
  intro Ψ _ N M lam s hlam
  classical
  choose f hf using hlam
  let c : Option (Ψ × Fin N) → ℚ := fun j => match j with
    | some r => -f r.1 r.2
    | none => s / M.kA
  obtain ⟨q, n, hq, hn⟩ := RootFieldNumerics.exists_clear_denominators_bis c
  refine ⟨q, n, hq, fun j => ?_⟩
  have h : ((n j : ℚ) : ℝ) = ((q * c j : ℚ) : ℝ) := by rw [hn j]
  push_cast at h
  rw [h]
  congr 1
  cases j with
  | none => simp [c, RootModel.coef]
  | some r => simp [c, RootModel.coef, hf]
