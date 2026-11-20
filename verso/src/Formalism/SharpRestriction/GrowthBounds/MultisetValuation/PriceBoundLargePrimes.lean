import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.PriceBoundSmallPrimes
import Formalism.LocalRingCardinality.ColumnWeightSpreadOffTop

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

section Fl

variable {p : ℕ} {G : Formalism.MainNotions.G.GAtP p} (Fl : Formalism.MainNotions.G.Fills G) (v : Fin G.P.nV)

/- English proof (translation)
Unfold `lamI`. Rewrite using `[dif_pos ⟨by omega, le_rfl⟩]`. Both sides reduce to the same expression.
-/
theorem ne_lamI_last (s : Fin (G.P.n' v)) : lamI (G.P.lam0 v) s (G.P.m + 1) = G.P.lam0 v s (Fin.last G.P.m) := by
  unfold lamI
  rw [dif_pos ⟨by omega, le_rfl⟩]
  rfl

/- English proof (translation)
Establish `hc : (0 : ℤ) ≤ Fl.c` using `Int.natCast_nonneg _`. Unfold `lamI`. Distinguish the cases in `h : 1 ≤ a ∧ a ≤ G.P.m + 1`. Rewrite using `[dif_pos h]`. Distinguish the cases in `hs : s ∈ Fl.TT v`.

Take `⟨h1, h2, h3⟩` from `(Fl.base v s).1 hs`. Distinguish the cases in `ha : a = 1`. Substitute `ha` using the available equality. Rewrite using `[if_pos ⟨hs, rfl⟩]`. Establish `: G.P.lam0 v s ⟨1 - 1, by omega⟩ = Fl.a v s` using `h1`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg (fun h' => ha h'.2)]`. Distinguish the cases in `hl : a = G.P.m + 1`. Substitute `hl` using the available equality. Establish `: G.P.lam0 v s ⟨G.P.m + 1 - 1, by omega⟩ = -Fl.b v s` using `h2`.

Use `hb hs` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `(abs_le.1 (h3 ⟨a - 1, by omega⟩ (by show 0 < a - 1; omega) (by show a - 1 < G.P.m; omega))).2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg (fun h' => hs h'.1)]`.

Use `(abs_le.1 ((Fl.base v s).2 hs ⟨a - 1, by omega⟩)).2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[dif_neg h, if_neg (fun h' => h ⟨by omega, by omega⟩)]`. Use linear arithmetic over natural numbers and integers.
-/
theorem ne_lamI_le (s : Fin (G.P.n' v)) (a : ℕ) (hm : 2 ≤ G.P.m) (hb : s ∈ Fl.TT v → 0 ≤ Fl.b v s) :
    lamI (G.P.lam0 v) s a ≤ (Fl.c : ℤ) + (if s ∈ Fl.TT v ∧ a = 1 then Fl.a v s else 0) := by
  have hc : (0 : ℤ) ≤ Fl.c := Int.natCast_nonneg _
  unfold lamI
  by_cases h : 1 ≤ a ∧ a ≤ G.P.m + 1
  · rw [dif_pos h]
    by_cases hs : s ∈ Fl.TT v
    · obtain ⟨h1, h2, h3⟩ := (Fl.base v s).1 hs
      by_cases ha : a = 1
      · subst ha
        rw [if_pos ⟨hs, rfl⟩]
        have : G.P.lam0 v s ⟨1 - 1, by omega⟩ = Fl.a v s := h1
        omega
      · rw [if_neg (fun h' => ha h'.2)]
        by_cases hl : a = G.P.m + 1
        · subst hl
          have : G.P.lam0 v s ⟨G.P.m + 1 - 1, by omega⟩ = -Fl.b v s := h2
          have := hb hs
          omega
        · have := (abs_le.1 (h3 ⟨a - 1, by omega⟩ (by show 0 < a - 1; omega) (by show a - 1 < G.P.m; omega))).2
          omega
    · rw [if_neg (fun h' => hs h'.1)]
      have := (abs_le.1 ((Fl.base v s).2 hs ⟨a - 1, by omega⟩)).2
      omega
  · rw [dif_neg h, if_neg (fun h' => h ⟨by omega, by omega⟩)]
    omega

end Fl

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

/- English proof (translation)
Unfold `Formalism.MainNotions.G.kaJ`. Establish `h1 : (1 : ℝ) ≤ j` using `by exact_mod_cast hj`. Establish `h2 : (0 : ℝ) ≤ D.R.k` using `Nat.cast_nonneg _`. Establish `h3 : (0 : ℝ) ≤ D.R.t` using `Nat.cast_nonneg _`. Establish `: 0 ≤ (2 * (j : ℝ) - 1) * ((D.R.t : ℝ) + 1)` using `mul_nonneg (by linarith) (by linarith)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ne_kaJ_nonneg (j : ℕ) (hj : 1 ≤ j) : 0 ≤ Formalism.MainNotions.G.kaJ D j := by
  unfold Formalism.MainNotions.G.kaJ
  have h1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have h2 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have : 0 ≤ (2 * (j : ℝ) - 1) * ((D.R.t : ℝ) + 1) := mul_nonneg (by linarith) (by linarith)
  linarith

/- English proof (translation)
Unfold `Scale.w''`. Conclude with `div_nonneg L.sc.b'_pos.le (mul_nonneg L.sc.x_pos.le (Nat.cast_nonneg _))`.
-/
theorem ne_w''_nonneg : 0 ≤ L.sc.w'' D.R.n := by
  unfold Scale.w''
  exact div_nonneg L.sc.b'_pos.le (mul_nonneg L.sc.x_pos.le (Nat.cast_nonneg _))

section Orbit

variable (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (hT : GatTies D) (hL : Formalism.MainNotions.G.LatTied hT X Y)
  (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
  (t0 : Formalism.MainNotions.G.HH D) (ht0 : t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w))

include hL ht0 in

/- English proof (translation)
Take `⟨_, h2, _, h4⟩` from `((hL u w hg).2.2.2.2.2.2 t0 ht0).2 s`. Rewrite using `[h4 j hj]`. Establish `hn : t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) ∉ D.host.TT` using `fun h => hs (h2.2 h)`. Unfold `Formalism.MainNotions.G.fillG Formalism.MainNotions.G.fill`. Rewrite using `[if_neg (fun h => hn h.2)]`.

Establish `h5` using `(X.off_thin j (false, t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) ⟨fun h => hn h.2, fun h => by simpa using h.1⟩).2`. Establish `h6` using `ne_kaJ_nonneg (D := D) j (Finset.mem_Icc.1 hj).1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ne_w_non (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0)))
    (hs : s ∉ (Y.Fl u w hg).TT (Y.vOf u w hg t0)) :
    ((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ) ≤ L.sc.w'' D.R.n + L.etaSz := by
  obtain ⟨_, h2, _, h4⟩ := ((hL u w hg).2.2.2.2.2.2 t0 ht0).2 s
  rw [h4 j hj]
  have hn : t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) ∉ D.host.TT := fun h => hs (h2.2 h)
  unfold Formalism.MainNotions.G.fillG Formalism.MainNotions.G.fill
  rw [if_neg (fun h => hn h.2)]
  have h5 := (X.off_thin j (false, t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w))
    ⟨fun h => hn h.2, fun h => by simpa using h.1⟩).2
  have h6 := ne_kaJ_nonneg (D := D) j (Finset.mem_Icc.1 hj).1
  linarith

include hL ht0 in

/- English proof (translation)
Take `⟨_, h2, h3, h4⟩` from `((hL u w hg).2.2.2.2.2.2 t0 ht0).2 s`. Rewrite using `[h4 j hj, (h3 hs).2]`. Establish `hn : t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) ∈ D.host.TT` using `h2.1 hs`. Unfold `Formalism.MainNotions.G.fillG Formalism.MainNotions.G.fill`. Rewrite using `[if_pos ⟨rfl, hn⟩]`.

Establish `h5` using `(X.off_top j (false, t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) ⟨rfl, hn⟩).2`. Establish `h6` using `ne_kaJ_nonneg (D := D) j (Finset.mem_Icc.1 hj).1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ne_w_top (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0)))
    (hs : s ∈ (Y.Fl u w hg).TT (Y.vOf u w hg t0)) :
    ((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ) ≤
      ((Y.Fl u w hg).b (Y.vOf u w hg t0) s : ℝ) + L.sc.b' / L.sc.x + L.etaSz := by
  obtain ⟨_, h2, h3, h4⟩ := ((hL u w hg).2.2.2.2.2.2 t0 ht0).2 s
  rw [h4 j hj, (h3 hs).2]
  have hn : t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) ∈ D.host.TT := h2.1 hs
  unfold Formalism.MainNotions.G.fillG Formalism.MainNotions.G.fill
  rw [if_pos ⟨rfl, hn⟩]
  have h5 := (X.off_top j (false, t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) ⟨rfl, hn⟩).2
  have h6 := ne_kaJ_nonneg (D := D) j (Finset.mem_Icc.1 hj).1
  linarith

include hL ht0 in
/- English proof (translation)
Unfold `Formalism.MainNotions.G.nP`. Rewrite using `[if_neg (nc_notSg hg), nc_n_eq X Y hT hL u w hg t0 ht0]`.
-/
theorem ne_nP : (Formalism.MainNotions.G.nP D (D.what₂.places.resChar w) : ℝ) = ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℕ) := by
  unfold Formalism.MainNotions.G.nP
  rw [if_neg (nc_notSg hg), nc_n_eq X Y hT hL u w hg t0 ht0]

/- English proof (translation)
Unfold `Formalism.MainNotions.G.Nm Ranks.N`. Establish `h1 : (j : ℝ) ≤ D.R.m` using `by exact_mod_cast (Finset.mem_Icc.1 hj).2`. Establish `h2 : (0 : ℝ) ≤ D.R.t` using `Nat.cast_nonneg _`. Establish `h3 : (0 : ℝ) ≤ D.R.k` using `Nat.cast_nonneg _`. Establish `h4 : (0 : ℝ) ≤ j` using `Nat.cast_nonneg _`.

Use `push_cast`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ (D.R.t : ℝ) + 1), mul_nonneg h4 (by linarith : (0 : ℝ) ≤ (D.R.t : ℝ) + 1)]`.
-/
theorem ne_Nm (j : ℕ) (hj : j ∈ SizeData₂.lifts D) : (j : ℝ) * ((D.R.t : ℝ) + 1) / 2 ≤ Formalism.MainNotions.G.Nm D := by
  unfold Formalism.MainNotions.G.Nm Ranks.N
  have h1 : (j : ℝ) ≤ D.R.m := by exact_mod_cast (Finset.mem_Icc.1 hj).2
  have h2 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ (D.R.t : ℝ) + 1),
    mul_nonneg h4 (by linarith : (0 : ℝ) ≤ (D.R.t : ℝ) + 1)]

end Orbit

open Classical in

/- English proof (translation)
Introduce `D L X Y K hK _ hT hL u w hg hp t0 ht0 j hj`. Establish `hr : (D.gat u w hg).P.r = 1` using `by rw [(hL u w hg).2.2.2.1, if_neg (not_lt.2 hp)]`. Establish `ht : (Y.Fl u w hg).t = D.R.t` using `(hL u w hg).2.1`. Establish `hc : ((Y.Fl u w hg).c : ℝ) ≤ Formalism.MainNotions.G.cG L` using `(hL u w hg).2.2.1`. Establish `hinj` using `nc_iota_inj X Y hT hL u w hg t0 ht0`.

Establish `hA : 0 ≤ L.sc.w'' D.R.n + L.etaSz + Formalism.MainNotions.G.cG L`. Use `ne_w''_nonneg (L := L)` as an intermediate fact. Use `L.etaSz_pos` as an intermediate fact. Use `nc_cG_nonneg (L := L)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[hr]`. Establish `h1` using `price_sum_single_edge (Y.Fl u w hg).t j ((Y.Fl u w hg).TT (Y.vOf u w hg t0)) ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0)) ((Y.Fl u w hg).w (Y.vOf u w hg t0)) (L.sc.w'' D.R.n + L.etaSz + Formalism.MainNotions.G.cG L) (fun s => ((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ) - ((Y.Fl u w …`. Establish `e : (D.gat u w hg).P.m + 2 - 1 = (D.gat u w hg).P.m + 1` using `rfl`. Rewrite using `[e, Finset.Icc_self, Finset.sum_singleton, ne_lamI_last]`. Use `split_ifs with hs`.

Rewrite using `[((Y.Fl u w hg).base (Y.vOf u w hg t0) s).1 hs |>.2.1]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2` using `ne_w_non X Y hT hL u w hg t0 ht0 j hj s hs`. Establish `h3` using `(abs_le.1 (((Y.Fl u w hg).base (Y.vOf u w hg t0) s).2 hs (Fin.last _))).2`.

Establish `h4 : (((D.gat u w hg).P.lam0 (Y.vOf u w hg t0) s (Fin.last _) : ℤ) : ℝ) ≤ ((Y.Fl u w hg).c : ℝ)`. Conclude with `h3` after adjusting the coercions. Use `push_cast`. Use the proof step `linarith)`. Use `le_trans h1 ?_` and prove the remaining obligations.

Unfold `Formalism.MainNotions.G.Pr`. Rewrite using `[if_pos hp, nc_topsOn X Y hT hL u w hg t0 ht0, Finset.filter_image, Finset.sum_image (fun a _ b _ h => hinj h)]`. Establish `hf : ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).filter (fun a => ¬ Formalism.MainNotions.G.IsV X (D.what₂.places.resChar w) (nc_iota Y u w hg t0 a)) = ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).filter IsOddPos`. Apply `Finset.filter_congr` to reduce the goal to its premises. Introduce `s _`.

Rewrite using `[nc_isV X Y hT hL u w hg t0 ht0 s, not_not]`. Rewrite using `[hf, ne_nP X Y hT hL u w hg t0 ht0, ht]`. Establish `e1 : ∑ s ∈ ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).filter IsOddPos, (((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ) - ((Y.Fl u w hg).b (Y.vOf u w hg t0) s : ℝ)) = ∑ s ∈ ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).filter IsOddPos, (Formalism.MainNotions.G.fillG X (Formalism.MainNotions.G.bL L) …`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `s hs`.

Take `⟨_, _, h3, h4⟩` from `((hL u w hg).2.2.2.2.2.2 t0 ht0).2 s`. Rewrite using `[h4 j hj, (h3 (Finset.mem_filter.1 hs).1).2]`. Rewrite using `[e1]`. Establish `hN` using `ne_Nm (D := D) j hj`. Establish `hn : (0 : ℝ) ≤ ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℕ)` using `Nat.cast_nonneg _`.

Establish `hNm : 0 ≤ Formalism.MainNotions.G.Nm D` using `le_trans (by positivity) hN`. Establish `h5 : ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℝ) * (L.sc.w'' D.R.n + L.etaSz + Formalism.MainNotions.G.cG L + Formalism.MainNotions.G.Nm D) ≤ K.Pr1 * ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℝ) * (L.sc.w'' D.R.n + L.etaSz + Formalism.MainNotions.G.cG L + Formalism.MainNotions.G.N …`. Use `mul_le_mul_of_nonneg_right hK (mul_nonneg hn (by linarith : 0 ≤ L.sc.w'' D.R.n + L.etaSz + Formalism.MainNotions.G.cG L + Formalism.MainNotions.G.Nm D))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h6 : ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℝ) * ((1 : ℕ) : ℝ) * j * ((D.R.t : ℝ) + 1) / 2 ≤ ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℝ) * Formalism.MainNotions.G.Nm D`.

Use `mul_le_mul_of_nonneg_left hN hn` as an intermediate fact. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem price_bound_large_primes : PriceBoundLargePrimes 1 := by
  intro D L X Y K hK _ hT hL u w hg hp t0 ht0 j hj
  have hr : (D.gat u w hg).P.r = 1 := by rw [(hL u w hg).2.2.2.1, if_neg (not_lt.2 hp)]
  have ht : (Y.Fl u w hg).t = D.R.t := (hL u w hg).2.1
  have hc : ((Y.Fl u w hg).c : ℝ) ≤ Formalism.MainNotions.G.cG L := (hL u w hg).2.2.1
  have hinj := nc_iota_inj X Y hT hL u w hg t0 ht0
  have hA : 0 ≤ L.sc.w'' D.R.n + L.etaSz + Formalism.MainNotions.G.cG L := by
    have := ne_w''_nonneg (L := L)
    have := L.etaSz_pos
    have := nc_cG_nonneg (L := L)
    linarith
  rw [hr]
  have h1 := price_sum_single_edge (Y.Fl u w hg).t j ((Y.Fl u w hg).TT (Y.vOf u w hg t0)) ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
    ((Y.Fl u w hg).w (Y.vOf u w hg t0)) (L.sc.w'' D.R.n + L.etaSz + Formalism.MainNotions.G.cG L)
    (fun s => ((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ) - ((Y.Fl u w hg).b (Y.vOf u w hg t0) s : ℝ)) hA
    (fun s _ => by
      have e : (D.gat u w hg).P.m + 2 - 1 = (D.gat u w hg).P.m + 1 := rfl
      rw [e, Finset.Icc_self, Finset.sum_singleton, ne_lamI_last]
      split_ifs with hs
      · rw [((Y.Fl u w hg).base (Y.vOf u w hg t0) s).1 hs |>.2.1]
        push_cast
        linarith
      · have h2 := ne_w_non X Y hT hL u w hg t0 ht0 j hj s hs
        have h3 := (abs_le.1 (((Y.Fl u w hg).base (Y.vOf u w hg t0) s).2 hs (Fin.last _))).2
        have h4 : (((D.gat u w hg).P.lam0 (Y.vOf u w hg t0) s (Fin.last _) : ℤ) : ℝ) ≤ ((Y.Fl u w hg).c : ℝ) := by
          exact_mod_cast h3
        push_cast
        linarith)
  refine le_trans h1 ?_
  unfold Formalism.MainNotions.G.Pr
  rw [if_pos hp, nc_topsOn X Y hT hL u w hg t0 ht0, Finset.filter_image, Finset.sum_image (fun a _ b _ h => hinj h)]
  have hf : ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).filter
      (fun a => ¬ Formalism.MainNotions.G.IsV X (D.what₂.places.resChar w) (nc_iota Y u w hg t0 a)) =
      ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).filter IsOddPos := by
    apply Finset.filter_congr
    intro s _
    rw [nc_isV X Y hT hL u w hg t0 ht0 s, not_not]
  rw [hf, ne_nP X Y hT hL u w hg t0 ht0, ht]
  have e1 : ∑ s ∈ ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).filter IsOddPos,
      (((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ) - ((Y.Fl u w hg).b (Y.vOf u w hg t0) s : ℝ)) =
      ∑ s ∈ ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).filter IsOddPos,
        (Formalism.MainNotions.G.fillG X (Formalism.MainNotions.G.bL L) j (false, nc_iota Y u w hg t0 s) -
          (Formalism.MainNotions.G.bL L (nc_iota Y u w hg t0 s) : ℝ)) := by
    apply Finset.sum_congr rfl
    intro s hs
    obtain ⟨_, _, h3, h4⟩ := ((hL u w hg).2.2.2.2.2.2 t0 ht0).2 s
    rw [h4 j hj, (h3 (Finset.mem_filter.1 hs).1).2]
  rw [e1]
  have hN := ne_Nm (D := D) j hj
  have hn : (0 : ℝ) ≤ ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℕ) := Nat.cast_nonneg _
  have hNm : 0 ≤ Formalism.MainNotions.G.Nm D := le_trans (by positivity) hN
  have h5 : ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℝ) * (L.sc.w'' D.R.n + L.etaSz + Formalism.MainNotions.G.cG L + Formalism.MainNotions.G.Nm D) ≤
      K.Pr1 * ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℝ) *
        (L.sc.w'' D.R.n + L.etaSz + Formalism.MainNotions.G.cG L + Formalism.MainNotions.G.Nm D) := by
    have := mul_le_mul_of_nonneg_right hK
      (mul_nonneg hn (by linarith : 0 ≤ L.sc.w'' D.R.n + L.etaSz + Formalism.MainNotions.G.cG L + Formalism.MainNotions.G.Nm D))
    linarith
  have h6 : ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℝ) * ((1 : ℕ) : ℝ) * j * ((D.R.t : ℝ) + 1) / 2 ≤
      ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℝ) * Formalism.MainNotions.G.Nm D := by
    have := mul_le_mul_of_nonneg_left hN hn
    push_cast
    linarith
  linarith

end Formalism.MainNotions.FormalGroupSystem.Pf
