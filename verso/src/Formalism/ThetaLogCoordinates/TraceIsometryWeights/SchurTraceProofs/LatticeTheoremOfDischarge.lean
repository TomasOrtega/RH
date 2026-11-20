import Formalism.ThetaLogCoordinates.TraceIsometryWeights.StatementG

namespace Formalism.InvariantFactorPaths.PW

open MvPolynomial Finset Formalism.GM.M Formalism.GM

/- English proof (translation)
Unfold `Letters.setTies`. Simplify using `only`. Use `split_ifs with hx`. Conclude with `h _`. Conclude with `le_rfl`.
-/
theorem setTies_deg_le {N : ℕ} (LL : Letters N) (T : TieData) (n n' : Fin T.t → ℕ) (h : ∀ i, n i ≤ n' i) (x : Fin N) :
    (LL.setTies T n).deg x ≤ (LL.setTies T n').deg x := by
  unfold Letters.setTies
  dsimp only
  split_ifs with hx
  · exact h _
  · exact le_rfl

/- English proof (translation)
Take `⟨C₀, hC₀, hM⟩` from `hM`. Use `⟨C₀, hC₀, ?_⟩` and prove the remaining obligations. Introduce `p _ N r _ _ LL T a E κ Yl n₀ dd ρ hp hr hρ hadm hE hY hS hdeg hz hκ hineq hL4`. Use `hM p N r LL T a E κ Yl n₀ dd ρ hp hr hρ hadm hE hY hS hdeg hz hκ ?_` and prove the remaining obligations. Introduce `n hn`.

Establish `hle : ∀ i, n i ≤ n₀ i + dd i * (Yl i - 1)`. Introduce `i`. Establish `hi` using `Fintype.mem_piFinset.mp hn i`. Take `⟨j, hj, hji⟩` from `Finset.mem_image.mp hi`. Establish `hj' : j < Yl i` using `Finset.mem_range.mp hj`.

Rewrite using `[← hji]`. Conclude with `Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.le_sub_one_of_lt hj')) _`. Establish `hdeg' : ∀ x, (LL.setTies T n).deg x ≤ 2 * a` using `fun x => (setTies_deg_le LL T n _ hle x).trans (hdeg x)`. Take `⟨hP, hW, -⟩` from `hD p N r (LL.setTies T n) ρ a κ hdeg' hineq hκ`. Conclude with `⟨hP, hW, hL4 n hn⟩`.
-/
theorem lattice_theorem_of_discharge (hM : Formalism.GM.M.TheoremM) (hD : HeightBoundImplication) : LatticeTheoremHeightBound := by
  obtain ⟨C₀, hC₀, hM⟩ := hM
  refine ⟨C₀, hC₀, ?_⟩
  intro p _ N r _ _ LL T a E κ Yl n₀ dd ρ hp hr hρ hadm hE hY hS hdeg hz hκ hineq hL4
  refine hM p N r LL T a E κ Yl n₀ dd ρ hp hr hρ hadm hE hY hS hdeg hz hκ ?_
  intro n hn
  have hle : ∀ i, n i ≤ n₀ i + dd i * (Yl i - 1) := by
    intro i
    have hi := Fintype.mem_piFinset.mp hn i
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
    have hj' : j < Yl i := Finset.mem_range.mp hj
    rw [← hji]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.le_sub_one_of_lt hj')) _
  have hdeg' : ∀ x, (LL.setTies T n).deg x ≤ 2 * a := fun x =>
    (setTies_deg_le LL T n _ hle x).trans (hdeg x)
  obtain ⟨hP, hW, -⟩ := hD p N r (LL.setTies T n) ρ a κ hdeg' hineq hκ
  exact ⟨hP, hW, hL4 n hn⟩

end Formalism.InvariantFactorPaths.PW
