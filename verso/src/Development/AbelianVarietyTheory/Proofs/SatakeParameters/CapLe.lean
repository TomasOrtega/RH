import Mathlib
import Formalism.SharpRestriction.ParConsts
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NonemptyPlacesOfRecord
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMemTopPlaces
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.CapBound

/- English proof (translation)
Establish `hw : wPl D (j + 1) z = (((D.hcW u (tauPl D z)).e ⟨j, hj⟩ : ℚ) : ℝ)`. Unfold `wPl wj`. Rewrite using `[dif_pos (by simpa using hj), D.hcW_e]`. Both sides reduce to the same expression. Establish `hk : 5 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega`.

Establish `hk' : (5 : ℝ) ≤ D.R.k` using `by exact_mod_cast hk`. Establish `hr' : (r : ℝ) ≤ 1` using `by exact_mod_cast hr1`. Establish `h2 : r < D.R.N j` using `by unfold Ranks.N; omega`. Rewrite using `[nuRowOK D u j hj z r, if_pos h2, RowWeightLemmas.nuRow_head D u j hj _ r hr, hw]`. Unfold `kaJ Ranks.N`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem row_le (D : D7) (u : D.what₂.Word) (j : ℕ) (hj : j < D.R.m) (z : Bool × HH D) (r : ℕ) (hr1 : r ≤ 1)
    (hr : r < D.R.k) :
    (((nuD D u j z).rowLen r : ℕ) : ℝ) ≤
      wPl D (j + 1) z - kaJ D (j + 1) + (((D.hcW u (tauPl D z)).u ⟨r, hr⟩ : ℚ) : ℝ) := by
  have hw : wPl D (j + 1) z = (((D.hcW u (tauPl D z)).e ⟨j, hj⟩ : ℚ) : ℝ) := by
    unfold wPl wj
    rw [dif_pos (by simpa using hj), D.hcW_e]
    rfl
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hr' : (r : ℝ) ≤ 1 := by exact_mod_cast hr1
  have h2 : r < D.R.N j := by unfold Ranks.N; omega
  rw [nuRowOK D u j hj z r, if_pos h2, RowWeightLemmas.nuRow_head D u j hj _ r hr, hw]
  unfold kaJ Ranks.N
  push_cast
  linarith

/- English proof (translation)
Introduce `eps Fm`. Take `⟨x0, hx0⟩` from `GlobalTheory.fill_eq_wPl Fm`. Use `⟨x0, fun x hx hx1 i u j hj z => ?_⟩` and prove the remaining obligations. Establish `hk : 5 ≤ (Fm.D x i).R.k`. Use `(Fm.D x i).R.m_add_three_le_k` as an intermediate fact.

Use `(Fm.D x i).R.two_le_m` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hS` using `(Fm.L x i).Sc_pos`. Unfold `fillG cG`. Rewrite using `[hx0 x hx hx1 i j hj z]`.

Use `split_ifs with hz`. Establish `h1` using `row_le (Fm.D x i) u j hj z 1 le_rfl (by omega)`. Take `⟨-, h4⟩` from `(Fm.L x i).cloud_u u (tauPl (Fm.D x i) z) ⟨1, by omega⟩ le_rfl (by show 1 + 1 < _; omega)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `row_le (Fm.D x i) u j hj z 0 (by omega) (by omega)`.

Take `⟨-, h4⟩` from `GlobalTheory.LongRows.u_bounds_off (Fm.params x hx1 i) u _ (GlobalTheory.LongRows.not_mem_topPlaces _ z hz) 0 (by omega)`. Rewrite `h4` using `[if_pos rfl]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cap_le : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), (if IsTopPl (Fm.D x i) z then (((nuD (Fm.D x i) u j z).rowLen 1 : ℕ) : ℝ) else (((nuD (Fm.D x i) u j z).rowLen 0 : ℕ) : ℝ)) ≤ fillG (Fm.Gx x i) (bL (Fm.L x i)) (j + 1) z + cG (Fm.L x i) := by
  intro eps Fm
  obtain ⟨x0, hx0⟩ := GlobalTheory.fill_eq_wPl Fm
  refine ⟨x0, fun x hx hx1 i u j hj z => ?_⟩
  have hk : 5 ≤ (Fm.D x i).R.k := by
    have := (Fm.D x i).R.m_add_three_le_k; have := (Fm.D x i).R.two_le_m; omega
  have hS := (Fm.L x i).Sc_pos
  unfold fillG cG
  rw [hx0 x hx hx1 i j hj z]
  split_ifs with hz
  · have h1 := row_le (Fm.D x i) u j hj z 1 le_rfl (by omega)
    obtain ⟨-, h4⟩ := (Fm.L x i).cloud_u u (tauPl (Fm.D x i) z) ⟨1, by omega⟩ le_rfl (by show 1 + 1 < _; omega)
    linarith
  · have h1 := row_le (Fm.D x i) u j hj z 0 (by omega) (by omega)
    obtain ⟨-, h4⟩ := GlobalTheory.LongRows.u_bounds_off (Fm.params x hx1 i) u _
      (GlobalTheory.LongRows.not_mem_topPlaces _ z hz) 0 (by omega)
    rw [if_pos rfl] at h4
    linarith

end GlobalTheory.CapBound
