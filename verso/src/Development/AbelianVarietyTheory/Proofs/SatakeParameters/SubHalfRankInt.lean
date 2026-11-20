import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetOpIntegral
import Formalism.LocalToGlobal.Columns.BaseLemmas

namespace GlobalTheory.ColPeriod

open Formalism.L2.Col Formalism.BasicNotions Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint (WtCompat)

/- English proof (translation)
Take `⟨a, ha⟩` from `R.k_even`. Take `⟨c, hc⟩` from `R.t_odd`. Unfold `Ranks.N`. Rewrite using `[ha, hc]`. Conclude with `⟨z - a - (j : ℤ) * (c + 1), by push_cast; ring⟩`.
-/
theorem sub_half_rank_int (R : Ranks) (z : ℤ) (j : ℕ) : ∃ a : ℤ, (z : ℚ) - (R.N j : ℚ) / 2 = a := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨c, hc⟩ := R.t_odd
  unfold Ranks.N
  rw [ha, hc]
  exact ⟨z - a - (j : ℤ) * (c + 1), by push_cast; ring⟩

/- English proof (translation)
Introduce `X Pr R W u j hj`. Establish `hs : ∀ τ : X.Tau, ∃ a : ℤ, sExp R ((W.hc u τ).e ⟨j, hj⟩) (j + 1) = a`. Introduce `τ`. Take `⟨z, hz⟩` from `(W.hc u τ).e_int ⟨j, hj⟩`. Rewrite using `[hz]`.

Conclude with `sub_half_rank_int R z _`. Establish `hs' : ∀ τ : X.Tau, ∃ a : ℤ, sExp' R ((W.hc u τ).e ⟨j, hj⟩) (j + 1) = a`. Introduce `τ`. Take `⟨z, hz⟩` from `(W.hc u τ).e_int ⟨j, hj⟩`. Rewrite using `[hz]`.

Conclude with `sub_half_rank_int R z _`. Use `choose s hs using hs`. Use `choose s' hs' using hs'`. Establish `hlt` using `N_lt_succ R j`. Establish `h1 : ∀ τ (i : Fin (R.N j)), (W.lamTrue u (j + 1) τ).w (Fin.castLE hlt.le i) + s τ = (W.lamTrue u j τ).w i + s' τ`.

Introduce `τ i`. Establish `h` using `W.lamTrue_old u hj τ (Fin.castLE hlt.le i) i.2`. Rewrite `h` using `[hs, hs']`. Establish `h' : (((W.lamTrue u (j + 1) τ).w (Fin.castLE hlt.le i) + s τ : ℤ) : ℚ) = (((W.lamTrue u j τ).w i + s' τ : ℤ) : ℚ)`. Use `push_cast`.

Rewrite using `[h]`. Simplify using the standard rewrite rules. Conclude with `h'` after adjusting the coercions. Establish `h2 : ∀ τ (i : Fin (R.N (j + 1))), R.N j ≤ (i : ℕ) → (W.lamTrue u (j + 1) τ).w i = -s τ`. Introduce `τ i hi`.

Establish `h` using `W.lamTrue_new u hj τ i (by omega)`. Rewrite `h` using `[hs]`. Conclude with `h` after adjusting the coercions. Establish `h3 : ∀ (τ : X.Tau) (a : Fin (R.N j)), (W.lamTrue u j τ).w a + s' τ = (W.nuW u (j + 1) τ).w a`. Introduce `τ a`.

Establish `h` using `W.nuW_eq_true u hj τ a`. Rewrite `h` using `[hs']`. Conclude with `h.symm` after adjusting the coercions. Use `⟨s, s', ⟨h1, h2, fun τ => ?_⟩, h3⟩` and prove the remaining obligations. Establish `hpos : 0 < R.N j` using `R.N_pos j`.

Establish `e1 : (W.lamTrue u j τ).detShift = (W.lamTrue u j τ).w ⟨R.N j - 1, by omega⟩`. Unfold `DomWeight.detShift`. Rewrite using `[dif_pos hpos]`. Establish `e2 : (W.nuW u (j + 1) τ).detShift = (W.nuW u (j + 1) τ).w (⟨R.N j - 1, by omega⟩ : Fin (R.N j))`. Unfold `DomWeight.detShift`.

Conclude with `dif_pos hpos`. Establish `hge : 0 ≤ (W.lamTrue u j τ).w ⟨R.N j - 1, by omega⟩ + s' τ`. Rewrite using `[← h1]`. Establish `ha` using `(W.lamTrue u (j + 1) τ).anti (show Fin.castLE hlt.le (⟨R.N j - 1, by omega⟩ : Fin (R.N j)) ≤ ⟨R.N j, hlt⟩ from by`. Rewrite using `[Fin.le_def]`.

Use the proof step `simp)`. Establish `hb` using `h2 τ ⟨R.N j, hlt⟩ le_rfl`. Use linear arithmetic over natural numbers and integers. Unfold `nuLast`. Rewrite using `[e1, e2, ← h3, Int.toNat_of_nonneg hge]`.
-/
theorem chainWeights : ChainWeights := by
  intro X Pr R W u j hj
  have hs : ∀ τ : X.Tau, ∃ a : ℤ, sExp R ((W.hc u τ).e ⟨j, hj⟩) (j + 1) = a := by
    intro τ
    obtain ⟨z, hz⟩ := (W.hc u τ).e_int ⟨j, hj⟩
    rw [hz]
    exact sub_half_rank_int R z _
  have hs' : ∀ τ : X.Tau, ∃ a : ℤ, sExp' R ((W.hc u τ).e ⟨j, hj⟩) (j + 1) = a := by
    intro τ
    obtain ⟨z, hz⟩ := (W.hc u τ).e_int ⟨j, hj⟩
    rw [hz]
    exact sub_half_rank_int R z _
  choose s hs using hs
  choose s' hs' using hs'
  have hlt := N_lt_succ R j
  have h1 : ∀ τ (i : Fin (R.N j)),
      (W.lamTrue u (j + 1) τ).w (Fin.castLE hlt.le i) + s τ = (W.lamTrue u j τ).w i + s' τ := by
    intro τ i
    have h := W.lamTrue_old u hj τ (Fin.castLE hlt.le i) i.2
    rw [hs, hs'] at h
    have h' : (((W.lamTrue u (j + 1) τ).w (Fin.castLE hlt.le i) + s τ : ℤ) : ℚ) =
        (((W.lamTrue u j τ).w i + s' τ : ℤ) : ℚ) := by
      push_cast
      rw [h]
      simp
    exact_mod_cast h'
  have h2 : ∀ τ (i : Fin (R.N (j + 1))), R.N j ≤ (i : ℕ) → (W.lamTrue u (j + 1) τ).w i = -s τ := by
    intro τ i hi
    have h := W.lamTrue_new u hj τ i (by omega)
    rw [hs] at h
    exact_mod_cast h
  have h3 : ∀ (τ : X.Tau) (a : Fin (R.N j)), (W.lamTrue u j τ).w a + s' τ = (W.nuW u (j + 1) τ).w a := by
    intro τ a
    have h := W.nuW_eq_true u hj τ a
    rw [hs'] at h
    exact_mod_cast h.symm
  refine ⟨s, s', ⟨h1, h2, fun τ => ?_⟩, h3⟩
  have hpos : 0 < R.N j := R.N_pos j
  have e1 : (W.lamTrue u j τ).detShift = (W.lamTrue u j τ).w ⟨R.N j - 1, by omega⟩ := by
    unfold DomWeight.detShift
    rw [dif_pos hpos]
  have e2 : (W.nuW u (j + 1) τ).detShift = (W.nuW u (j + 1) τ).w (⟨R.N j - 1, by omega⟩ : Fin (R.N j)) := by
    unfold DomWeight.detShift
    exact dif_pos hpos
  have hge : 0 ≤ (W.lamTrue u j τ).w ⟨R.N j - 1, by omega⟩ + s' τ := by
    rw [← h1]
    have ha := (W.lamTrue u (j + 1) τ).anti
      (show Fin.castLE hlt.le (⟨R.N j - 1, by omega⟩ : Fin (R.N j)) ≤ ⟨R.N j, hlt⟩ from by
        rw [Fin.le_def]; simp)
    have hb := h2 τ ⟨R.N j, hlt⟩ le_rfl
    omega
  unfold nuLast
  rw [e1, e2, ← h3, Int.toNat_of_nonneg hge]

end GlobalTheory.ColPeriod
