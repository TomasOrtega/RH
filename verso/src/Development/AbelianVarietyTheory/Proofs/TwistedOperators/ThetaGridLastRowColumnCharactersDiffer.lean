import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopOrthEmb
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.ChiGrid GlobalTheory.Unf GlobalTheory.FunObj GlobalTheory.RowUnf GlobalTheory.RowChain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChars

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

/- English proof (translation)
The claim follows from `(G.isV (X := .top j) hj (fun _ h => by cases h)).rank`.
-/
theorem rank_top (G : GridData L sc) {j : ℕ} (hj : j ≤ D.R.m) : (G.V (.top j)).rank = rankX D j :=
  (G.isV (X := .top j) hj (fun _ h => by cases h)).rank

/- English proof (translation)
The claim follows from `(G.isV (X := .grid D.R.m j) ⟨le_rfl, hj⟩ (fun _ h => by have := D.R.two_le_m; have := (Node.grid.inj h).1; omega)).rank`.
-/
theorem rank_grid (G : GridData L sc) {j : ℕ} (hj : j ≤ D.R.m) :
    (G.V (.grid D.R.m j)).rank = rankV D D.R.m j :=
  (G.isV (X := .grid D.R.m j) ⟨le_rfl, hj⟩ (fun _ h => by
    have := D.R.two_le_m; have := (Node.grid.inj h).1; omega)).rank

/- English proof (translation)
Take `⟨c, hc⟩` from `D.R.t_odd`. Establish `: rankX D j = rankX D 0 + 2 * (j * (c + 1))`. Simplify using `only [rankX, hc]`. Expand and normalize the polynomial expressions, which then agree. Use linear arithmetic over natural numbers and integers.
-/
theorem rankX_mod (j : ℕ) : rankX D j % 2 = rankX D 0 % 2 := by
  obtain ⟨c, hc⟩ := D.R.t_odd
  have : rankX D j = rankX D 0 + 2 * (j * (c + 1)) := by
    simp only [rankX, hc]; ring
  omega

/- English proof (translation)
Establish `h : sLen D - 1 = D.R.r + 5` using `by simp only [sLen]; omega`. Simplify using `only [rankV, rankX, rankP, nRk]`. Rewrite using `[h]`. Simplify using `only [sLen]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rankV_row (j : ℕ) : rankV D D.R.m j + 1 + j = rankX D j + D.R.m := by
  have h : sLen D - 1 = D.R.r + 5 := by simp only [sLen]; omega
  simp only [rankV, rankX, rankP, nRk]
  rw [h]
  simp only [sLen]
  ring

/- English proof (translation)
Simplify using `only [rankV]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rankV_succ (j : ℕ) : rankV D D.R.m (j + 1) = rankV D D.R.m j + D.R.t := by
  simp only [rankV]; ring

noncomputable def chiZ (L : LevCh D T) : (AE D)ˣ →* Circle := if Odd (rankX D 0) then L.eta else L.eta⁻¹

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show Formalism.IndefR.Lift.attChr _ _ (G.V (.top j)).rank = _`. Rewrite using `[rank_top G hj.le]`. Both sides reduce to the same expression. Use `show Formalism.IndefR.Lift.attChr _ _ (G.V (.top (j + 1))).rank = _`.

Rewrite using `[rank_top G hj]`. Both sides reduce to the same expression.
-/
theorem chr_top (G : GridData L sc) (t : T) {j : ℕ} (hj : j < D.R.m) :
    G.chrS (.top t j) = Formalism.IndefR.Lift.attChr (L.mu t (j + 1)) L.eta (rankX D j) ∧
    G.chrT (.top t j) = Formalism.IndefR.Lift.attChr (L.mu t (j + 1)) L.eta (rankX D (j + 1)) := by
  refine ⟨?_, ?_⟩
  · show Formalism.IndefR.Lift.attChr _ _ (G.V (.top j)).rank = _
    rw [rank_top G hj.le]; rfl
  · show Formalism.IndefR.Lift.attChr _ _ (G.V (.top (j + 1))).rank = _
    rw [rank_top G hj]; rfl

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show Formalism.IndefR.Lift.attChr _ _ (G.V (.grid D.R.m j)).rank = _`. Rewrite using `[rank_grid G hj.le]`. Both sides reduce to the same expression. Use `show Formalism.IndefR.Lift.attChr _ _ (G.V (.grid D.R.m (j + 1))).rank = _`.

Rewrite using `[rank_grid G hj]`. Both sides reduce to the same expression.
-/
theorem chr_mu (G : GridData L sc) (t : T) {j : ℕ} (hj : j < D.R.m) :
    G.chrS (.mu t D.R.m j) = Formalism.IndefR.Lift.attChr (L.mu t (j + 1)) L.eta (rankV D D.R.m j) ∧
    G.chrT (.mu t D.R.m j) = Formalism.IndefR.Lift.attChr (L.mu t (j + 1)) L.eta (rankV D D.R.m (j + 1)) := by
  refine ⟨?_, ?_⟩
  · show Formalism.IndefR.Lift.attChr _ _ (G.V (.grid D.R.m j)).rank = _
    rw [rank_grid G hj.le]; rfl
  · show Formalism.IndefR.Lift.attChr _ _ (G.V (.grid D.R.m (j + 1))).rank = _
    rw [rank_grid G hj]; rfl

/- English proof (translation)
Establish `hm` using `D.R.two_le_m`. Take `⟨a, ha⟩` from `D.R.m_even`. Rewrite using `[(chr_top G t (by omega)).1, (chr_mu G t (by omega)).1]`. Establish `h1` using `rankV_row (D := D) 0`. Simplify using `only [chiZ, Formalism.IndefR.Lift.attChr, Nat.odd_iff]`.

Apply the tactic sequence `split_ifs <;> first | (exfalso; omega) | group`.
-/
theorem chiZ_eq (G : GridData L sc) (t : T) :
    chiZ L = (G.chrS (.top t 0))⁻¹ * G.chrS (.mu t D.R.m 0) := by
  have hm := D.R.two_le_m
  obtain ⟨a, ha⟩ := D.R.m_even
  rw [(chr_top G t (by omega)).1, (chr_mu G t (by omega)).1]
  have h1 := rankV_row (D := D) 0
  simp only [chiZ, Formalism.IndefR.Lift.attChr, Nat.odd_iff]
  split_ifs <;> first | (exfalso; omega) | group

/- English proof (translation)
Establish `hm` using `D.R.two_le_m`. Take `⟨a, ha⟩` from `D.R.m_even`. Take `⟨c, hc⟩` from `D.R.t_odd`. Establish `HA` using `Wl.om_is (.top t 0) (show 0 + 1 ≤ D.R.m by omega)`. Establish `HB` using `Wl.om_is (.mu t D.R.m 0) (show D.R.m ≤ D.R.m ∧ 0 + 1 ≤ D.R.m by omega)`.

Use `⟨chiZ L, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[chiZ_eq G t]`. Use `⟨?_, fun x => ?_⟩` and prove the remaining obligations. Conclude with `(HA.hecS.1.inv).mul HB.hecS.1`. Rewrite using `[MonoidHom.mul_apply, MonoidHom.inv_apply, HA.hecS.2 x, HB.hecS.2 x, inv_one, one_mul]`.

Rewrite using `[chiZ_eq G t]`. Establish `rA : (G.pS (.top t 0)).rank = rankX D 0` using `rank_top G (by omega)`. Establish `rB : (G.pS (.mu t D.R.m 0)).rank = rankV D D.R.m 0` using `rank_grid G (by omega)`. Establish `eA` using `HA.resS`. Establish `eB` using `HB.resS`.

Rewrite `eA` using `[rA]`. Rewrite `eB` using `[rB]`. Use `⟨eA.1, fun η hη x => ?_⟩` and prove the remaining obligations. Rewrite using `[MonoidHom.mul_apply, MonoidHom.inv_apply, eA.2 η hη x, eB.2 η hη x]`. Establish `hx : η x * η x = 1` using `GlobalTheory.VolHeckeCompare.IsEta_mul_self hη x`.

Establish `hn : rankV D D.R.m 0 = rankX D 0 + 2 * (a - 1) + 1`. Use `rankV_row (D := D) 0` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[hn, pow_add, pow_add, pow_mul, pow_two, hx, one_pow, mul_one, inv_mul_cancel_left]`. Introduce `j hj`.

Rewrite using `[(chr_top G t hj).1, (chr_top G t hj).2]`. Establish `h1` using `rankX_mod (D := D) j`. Establish `h2` using `rankX_mod (D := D) (j + 1)`. Simplify using `only [Formalism.IndefR.Lift.attChr, Nat.odd_iff]`. Rewrite using `[h1, h2]`.

Introduce `j hj hp`. Rewrite using `[(chr_top G t hj).1, (chr_top G t hj).2, (chr_mu G t hj).1, (chr_mu G t hj).2]`. Establish `h1` using `rankX_mod (D := D) j`. Establish `h2` using `rankX_mod (D := D) (j + 1)`. Establish `h3` using `rankV_row (D := D) j`.

Establish `h4` using `rankV_succ (D := D) j`. Simplify using `only [chiZ, Formalism.IndefR.Lift.attChr, Nat.odd_iff]`. Apply the tactic sequence `refine ⟨?_, ?_⟩ <;> split_ifs <;> first | rfl | (exfalso; omega) | group`. Introduce `j hj hp`. Rewrite using `[(chr_top G t hj).1, (chr_top G t hj).2, (chr_mu G t hj).1, (chr_mu G t hj).2]`.

Establish `h1` using `rankX_mod (D := D) j`. Establish `h2` using `rankX_mod (D := D) (j + 1)`. Establish `h3` using `rankV_row (D := D) j`. Establish `h4` using `rankV_succ (D := D) j`. Simplify using `only [chiZ, Formalism.IndefR.Lift.attChr, Nat.odd_iff]`.

Apply the tactic sequence `refine ⟨?_, ?_⟩ <;> split_ifs <;> first | rfl | (exfalso; omega) | group`.
-/
theorem rowChars {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T) :
    ∃ χz : (AE D)ˣ →* Circle, IsHeckeChar D χz ∧ ResEta D χz 1 ∧
      (∀ j, j < D.R.m → G.chrS (.top t j) = G.chrT (.top t j)) ∧
      (∀ j, j < D.R.m → (D.R.m - 1 - j) % 2 = 0 →
        G.chrS (.mu t D.R.m j) = G.chrS (.top t j) ∧ G.chrT (.mu t D.R.m j) = G.chrT (.top t j) * χz) ∧
      (∀ j, j < D.R.m → (D.R.m - 1 - j) % 2 = 1 →
        G.chrS (.mu t D.R.m j) = G.chrS (.top t j) * χz ∧ G.chrT (.mu t D.R.m j) = G.chrT (.top t j)) := by
  have hm := D.R.two_le_m
  obtain ⟨a, ha⟩ := D.R.m_even
  obtain ⟨c, hc⟩ := D.R.t_odd
  have HA := Wl.om_is (.top t 0) (show 0 + 1 ≤ D.R.m by omega)
  have HB := Wl.om_is (.mu t D.R.m 0) (show D.R.m ≤ D.R.m ∧ 0 + 1 ≤ D.R.m by omega)
  refine ⟨chiZ L, ?_, ?_, ?_, ?_, ?_⟩
  · rw [chiZ_eq G t]
    refine ⟨?_, fun x => ?_⟩
    · exact (HA.hecS.1.inv).mul HB.hecS.1
    · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, HA.hecS.2 x, HB.hecS.2 x, inv_one, one_mul]
  · rw [chiZ_eq G t]
    have rA : (G.pS (.top t 0)).rank = rankX D 0 := rank_top G (by omega)
    have rB : (G.pS (.mu t D.R.m 0)).rank = rankV D D.R.m 0 := rank_grid G (by omega)
    have eA := HA.resS
    have eB := HB.resS
    rw [rA] at eA
    rw [rB] at eB
    refine ⟨eA.1, fun η hη x => ?_⟩
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, eA.2 η hη x, eB.2 η hη x]
    have hx : η x * η x = 1 := GlobalTheory.VolHeckeCompare.IsEta_mul_self hη x
    have hn : rankV D D.R.m 0 = rankX D 0 + 2 * (a - 1) + 1 := by
      have := rankV_row (D := D) 0
      omega
    rw [hn, pow_add, pow_add, pow_mul, pow_two, hx, one_pow, mul_one, inv_mul_cancel_left]
  · intro j hj
    rw [(chr_top G t hj).1, (chr_top G t hj).2]
    have h1 := rankX_mod (D := D) j
    have h2 := rankX_mod (D := D) (j + 1)
    simp only [Formalism.IndefR.Lift.attChr, Nat.odd_iff]
    rw [h1, h2]
  · intro j hj hp
    rw [(chr_top G t hj).1, (chr_top G t hj).2, (chr_mu G t hj).1, (chr_mu G t hj).2]
    have h1 := rankX_mod (D := D) j
    have h2 := rankX_mod (D := D) (j + 1)
    have h3 := rankV_row (D := D) j
    have h4 := rankV_succ (D := D) j
    simp only [chiZ, Formalism.IndefR.Lift.attChr, Nat.odd_iff]
    refine ⟨?_, ?_⟩ <;> split_ifs <;> first | rfl | (exfalso; omega) | group
  · intro j hj hp
    rw [(chr_top G t hj).1, (chr_top G t hj).2, (chr_mu G t hj).1, (chr_mu G t hj).2]
    have h1 := rankX_mod (D := D) j
    have h2 := rankX_mod (D := D) (j + 1)
    have h3 := rankV_row (D := D) j
    have h4 := rankV_succ (D := D) j
    simp only [chiZ, Formalism.IndefR.Lift.attChr, Nat.odd_iff]
    refine ⟨?_, ?_⟩ <;> split_ifs <;> first | rfl | (exfalso; omega) | group

end GlobalTheory.RowChars
