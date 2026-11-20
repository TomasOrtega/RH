import Formalism.HermitianCurvature.HermitianCurvatureProofs.OnePointBasisFundamentalDomainVolume
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.InterlacingGrids.FreeFamily
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.InterlacingGrids.LagSum
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.InterlacingGrids.GridSum

namespace CompanionTheory.WaveGrid

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Finset

/- English proof (translation)
Use `⟨fun a => hc _ (List.get_mem L a), fun a b hab => ?_⟩` and prove the remaining obligations. Break down `lt_or_gt_of_ne hab with h | h` into its components or cases. Conclude with `List.pairwise_iff_get.1 hp a b h`. Use `List.pairwise_iff_get.1 hp b a h` as an intermediate fact. Rewrite `this` using `[abs_sub_comm]`. Then use the resulting hypothesis.
-/
theorem cutWord_of_list (P : M.Par) (l0 : ℕ) (L : List C.Letter)
    (hc : ∀ l ∈ L, I.OnCut P.u P.u' l0 l.2)
    (hp : L.Pairwise fun l l' => 2 < |l.2 - l'.2|) : KB.CutWord P l0 L := by
  refine ⟨fun a => hc _ (List.get_mem L a), fun a b hab => ?_⟩
  rcases lt_or_gt_of_ne hab with h | h
  · exact List.pairwise_iff_get.1 hp a b h
  · have := List.pairwise_iff_get.1 hp b a h
    rwa [abs_sub_comm] at this

/- English proof (translation)
Use `⟨fun l hl => ?_, List.pairwise_iff_get.2 fun a b hab => h.2 a b (ne_of_lt hab)⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `List.get_of_mem hl`. Conclude with `h.1 a`.
-/
theorem list_of_cutWord {P : M.Par} {l0 : ℕ} {L : List C.Letter} (h : KB.CutWord P l0 L) :
    (∀ l ∈ L, I.OnCut P.u P.u' l0 l.2) ∧ L.Pairwise fun l l' => 2 < |l.2 - l'.2| := by
  refine ⟨fun l hl => ?_, List.pairwise_iff_get.2 fun a b hab => h.2 a b (ne_of_lt hab)⟩
  obtain ⟨a, rfl⟩ := List.get_of_mem hl
  exact h.1 a

/- English proof (translation)
Establish `h` using `abs_add_le (a + t) (-t)`. Rewrite `h` using `[add_neg_cancel_right, abs_neg]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem two_lt_of_five {a t : ℝ} (ha : 5 ≤ |a|) (ht : |t| ≤ 1) : 2 < |a + t| := by
  have h := abs_add_le (a + t) (-t)
  rw [add_neg_cancel_right, abs_neg] at h
  linarith

/- English proof (translation)
Take `⟨y', hy', hne, h | h⟩` from `hl`. Substitute `h` using the available equality. Establish `h5` using `hsep y hy y' hy' (Ne.symm hne)`. Use `⟨by simp only; linarith, ?_⟩` and prove the remaining obligations. Establish `e : (y + 1) - y' = (y - y') + 1` using `by ring`.

Simplify using `only`. Rewrite using `[e]`. Conclude with `two_lt_of_five h5 (by norm_num)`. Substitute `h` using the available equality. Establish `h5` using `hsep y hy y' hy' (Ne.symm hne)`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `e : y - (y' + 1) = (y - y') + (-1)` using `by ring`. Simplify using `only`. Rewrite using `[e]`. Conclude with `two_lt_of_five h5 (by norm_num)`.

Establish `e : (y + 1) - (y' + 1) = y - y'` using `by ring`. Simplify using `only`. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem free_dist {Y : Finset ℝ} (hsep : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → 5 ≤ |y - y'|) {y : ℝ} (hy : y ∈ Y)
    {l : C.Letter} (hl : ∃ y' ∈ Y, y' ≠ y ∧ (l = (true, y') ∨ l = (false, y' + 1))) :
    2 < |y - l.2| ∧ 2 < |(y + 1) - l.2| := by
  obtain ⟨y', hy', hne, h | h⟩ := hl
  · subst h
    have h5 := hsep y hy y' hy' (Ne.symm hne)
    refine ⟨by simp only; linarith, ?_⟩
    have e : (y + 1) - y' = (y - y') + 1 := by ring
    simp only
    rw [e]
    exact two_lt_of_five h5 (by norm_num)
  · subst h
    have h5 := hsep y hy y' hy' (Ne.symm hne)
    refine ⟨?_, ?_⟩
    · have e : y - (y' + 1) = (y - y') + (-1) := by ring
      simp only
      rw [e]
      exact two_lt_of_five h5 (by norm_num)
    · have e : (y + 1) - (y' + 1) = y - y' := by ring
      simp only
      rw [e]
      linarith

section grid

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Establish `hsepg : ∀ a i a' i', (a, i) ≠ (a', i') → 5 ≤ |grid a i - grid a' i'|`. Introduce `a i a' i' hne`. Use `hsep _ (hY a i) _ (hY a' i') fun h => hne ?_` and prove the remaining obligations. Take `⟨h1, h2⟩` from `hinj a i a' i' h`. Rewrite using `[h1, h2]`.

Take `⟨hwc, hwp⟩` from `list_of_cutWord hw`. Use `⟨fun a i j h => (hinj a i a j h).2, hY, fun n => ?_, ?_⟩` and prove the remaining obligations. Establish `hnew : (TBBx5.ysOf grid n).Pairwise fun y y' => 2 < |y - y'|`. Unfold `TBBx5.ysOf`. Rewrite using `[List.pairwise_ofFn]`.

Introduce `a b hab`. Use `hsepg a (n a) b (n b) (fun h => (ne_of_lt hab) (Prod.mk.inj h).1)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hmem : ∀ y ∈ TBBx5.ysOf grid n, ∃ a, grid a (n a) = y` using `fun y hy => List.mem_ofFn.1 hy`. Use `⟨?_, ?_, hnew⟩` and prove the remaining obligations.

Rewrite using `[TBBx5.plusW_eq]`. Use `cutWord_of_list P p.l0 _ (fun l hl => ?_) ?_` and prove the remaining obligations. Break down `List.mem_append.1 hl with hl | hl` into its components or cases. Take `⟨y, hy, rfl⟩` from `List.mem_map.1 hl`. Take `⟨a, rfl⟩` from `hmem y hy`.

Conclude with `(hcut _ (hY a (n a))).1`. Conclude with `hwc l hl`. Use `List.pairwise_append.2 ⟨List.pairwise_map.2 hnew, hwp, fun l hl l' hl' => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, rfl⟩` from `List.mem_map.1 hl`. Take `⟨a, rfl⟩` from `hmem y hy`.

Conclude with `(free_dist hsep (hY a (n a)) (hfree a (n a) l' hl')).1`. Rewrite using `[TBBx5.minusW_eq]`. Use `cutWord_of_list P p.l0 _ (fun l hl => ?_) ?_` and prove the remaining obligations. Break down `List.mem_append.1 hl with hl | hl` into its components or cases. Take `⟨y, hy, rfl⟩` from `List.mem_map.1 hl`.

Take `⟨a, rfl⟩` from `hmem y hy`. Conclude with `(hcut _ (hY a (n a))).2`. Conclude with `hwc l hl`. Use `List.pairwise_append.2 ⟨List.pairwise_map.2 (hnew.imp fun h => ?_), hwp, fun l hl l' hl' => ?_⟩` and prove the remaining obligations. Simplify `h` using `[add_sub_add_right_eq_sub]`.

Take `⟨y, hy, rfl⟩` from `List.mem_map.1 hl`. Take `⟨a, rfl⟩` from `hmem y hy`. Conclude with `(free_dist hsep (hY a (n a)) (hfree a (n a) l' hl')).2`. Conclude with `GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.grid_sum_le grid (fun a i => F7.lagCo (grid a) i) nn (fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re) B hB (fun a => GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.lag_abs_sum_le_one (grid a) (fun i j h => hse …`.
-/
theorem gridOK_of_free (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (Y : Finset ℝ) (B : ℝ) (K : ℕ) (w : List C.Letter)
    (d : ℕ) (grid : Fin K → Fin (d + 1) → ℝ) (hB : 0 ≤ B)
    (hcut : ∀ y ∈ Y, I.OnCut P.u P.u' p.l0 y ∧ I.OnCut P.u P.u' p.l0 (y + 1))
    (hsep : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → 5 ≤ |y - y'|)
    (hw : KB.CutWord P p.l0 w)
    (hY : ∀ a i, grid a i ∈ Y)
    (hinj : ∀ a i a' i', grid a i = grid a' i' → a = a' ∧ i = i')
    (hfree : ∀ a i, ∀ l ∈ w, ∃ y ∈ Y, y ≠ grid a i ∧ (l = (true, y) ∨ l = (false, y + 1)))
    (hq : ∀ a i, (0 < nn (grid a i) ∧ 0 < nn (grid a i + 1) ∧
        0 < (Wd.qw (M.qC P) (D.positionted w) ((grid a i : ℝ) : ℂ)).re) ∧
        nn (grid a i) * nn (grid a i + 1) ≤ B ^ 2 * (Wd.qw (M.qC P) (D.positionted w) ((grid a i : ℝ) : ℂ)).re) :
    TBBx5.GridOK p nn Y B K w d grid := by
  have hsepg : ∀ a i a' i', (a, i) ≠ (a', i') → 5 ≤ |grid a i - grid a' i'| := by
    intro a i a' i' hne
    refine hsep _ (hY a i) _ (hY a' i') fun h => hne ?_
    obtain ⟨h1, h2⟩ := hinj a i a' i' h
    rw [h1, h2]
  obtain ⟨hwc, hwp⟩ := list_of_cutWord hw
  refine ⟨fun a i j h => (hinj a i a j h).2, hY, fun n => ?_, ?_⟩
  · have hnew : (TBBx5.ysOf grid n).Pairwise fun y y' => 2 < |y - y'| := by
      unfold TBBx5.ysOf
      rw [List.pairwise_ofFn]
      intro a b hab
      have := hsepg a (n a) b (n b) (fun h => (ne_of_lt hab) (Prod.mk.inj h).1)
      linarith
    have hmem : ∀ y ∈ TBBx5.ysOf grid n, ∃ a, grid a (n a) = y := fun y hy => List.mem_ofFn.1 hy
    refine ⟨?_, ?_, hnew⟩
    · rw [TBBx5.plusW_eq]
      refine cutWord_of_list P p.l0 _ (fun l hl => ?_) ?_
      · rcases List.mem_append.1 hl with hl | hl
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hl
          obtain ⟨a, rfl⟩ := hmem y hy
          exact (hcut _ (hY a (n a))).1
        · exact hwc l hl
      · refine List.pairwise_append.2 ⟨List.pairwise_map.2 hnew, hwp, fun l hl l' hl' => ?_⟩
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hl
        obtain ⟨a, rfl⟩ := hmem y hy
        exact (free_dist hsep (hY a (n a)) (hfree a (n a) l' hl')).1
    · rw [TBBx5.minusW_eq]
      refine cutWord_of_list P p.l0 _ (fun l hl => ?_) ?_
      · rcases List.mem_append.1 hl with hl | hl
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hl
          obtain ⟨a, rfl⟩ := hmem y hy
          exact (hcut _ (hY a (n a))).2
        · exact hwc l hl
      · refine List.pairwise_append.2 ⟨List.pairwise_map.2 (hnew.imp fun h => ?_), hwp, fun l hl l' hl' => ?_⟩
        · simpa [add_sub_add_right_eq_sub] using h
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hl
          obtain ⟨a, rfl⟩ := hmem y hy
          exact (free_dist hsep (hY a (n a)) (hfree a (n a) l' hl')).2
  · exact GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.grid_sum_le grid (fun a i => F7.lagCo (grid a) i) nn
      (fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re) B hB
      (fun a => GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.lag_abs_sum_le_one (grid a)
        (fun i j h => hsepg a i a j (fun h' => h (Prod.mk.inj h').2)))
      (fun a i => (hq a i).1) (fun a i => (hq a i).2)

def FreeBound (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (Y : Finset ℝ) (B : ℝ) (K N : ℕ) : Prop :=
  ∀ w, TBB.AdmW P p.l0 Y w → w.length + K ≤ N → ∀ y ∈ Y,
    (∀ l ∈ w, ∃ y' ∈ Y, y' ≠ y ∧ (l = (true, y') ∨ l = (false, y' + 1))) →
    (0 < nn y ∧ 0 < nn (y + 1) ∧ 0 < (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re) ∧
      nn y * nn (y + 1) ≤ B ^ 2 * (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re

/- English proof (translation)
Introduce `j hj w hw hN`. Establish `h1 : w.length ≤ N - K` using `by omega`. Establish `h2 : K * (2 * j + 1) ≤ K * (2 * P.r + 1)` using `Nat.mul_le_mul_left _ (by omega)`. Take `⟨g, hgY, hginj, hgfree⟩` from `GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.exists_free_family Y w K (2 * j + 1) hw.2 ((Nat.add_le_add h1 h2).trans hcard)`. Conclude with `⟨g, gridOK_of_free p nn Y B K w (2 * j) g hB hcut hsep hw.1 hgY hginj hgfree (fun a i => hq w hw hN _ (hgY a i) (hgfree a i))⟩`.
-/
theorem waveGrid_of_sep (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (Y : Finset ℝ) (B : ℝ) (K N : ℕ) (hB : 0 ≤ B)
    (hcut : ∀ y ∈ Y, I.OnCut P.u P.u' p.l0 y ∧ I.OnCut P.u P.u' p.l0 (y + 1))
    (hsep : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → 5 ≤ |y - y'|)
    (hcard : N - K + K * (2 * P.r + 1) ≤ Y.card) (hq : FreeBound p nn Y B K N) :
    TBBx5.WaveGrid p nn Y B K N := by
  intro j hj w hw hN
  have h1 : w.length ≤ N - K := by omega
  have h2 : K * (2 * j + 1) ≤ K * (2 * P.r + 1) := Nat.mul_le_mul_left _ (by omega)
  obtain ⟨g, hgY, hginj, hgfree⟩ := GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.exists_free_family Y w K (2 * j + 1)
    hw.2 ((Nat.add_le_add h1 h2).trans hcard)
  exact ⟨g, gridOK_of_free p nn Y B K w (2 * j) g hB hcut hsep hw.1 hgY hginj hgfree
    (fun a i => hq w hw hN _ (hgY a i) (hgfree a i))⟩

/- English proof (translation)
Introduce `b s hb hs hbs w hw hN`. Establish `h1 : w.length ≤ N - K` using `by omega`. Establish `h2 : K * (2 * (b + s - 1 - s) + s + 1) ≤ K * (2 * P.r + 1)` using `Nat.mul_le_mul_left _ (by omega)`. Take `⟨g, hgY, hginj, hgfree⟩` from `GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.exists_free_family Y w K (2 * (b + s - 1 - s) + s + 1) hw.2 ((Nat.add_le_add h1 h2).trans hcard)`. Conclude with `⟨g, gridOK_of_free p nn Y B K w (2 * (b + s - 1 - s) + s) g hB hcut hsep hw.1 hgY hginj hgfree (fun a i => hq w hw hN _ (hgY a i) (hgfree a i))⟩`.
-/
theorem liftGrid_of_sep (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (Y : Finset ℝ) (B : ℝ) (K N : ℕ) (hB : 0 ≤ B)
    (hcut : ∀ y ∈ Y, I.OnCut P.u P.u' p.l0 y ∧ I.OnCut P.u P.u' p.l0 (y + 1))
    (hsep : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → 5 ≤ |y - y'|)
    (hcard : N - K + K * (2 * P.r + 1) ≤ Y.card) (hq : FreeBound p nn Y B K N) :
    TBBx5.LiftGrid p nn Y B K N := by
  intro b s hb hs hbs w hw hN
  have h1 : w.length ≤ N - K := by omega
  have h2 : K * (2 * (b + s - 1 - s) + s + 1) ≤ K * (2 * P.r + 1) := Nat.mul_le_mul_left _ (by omega)
  obtain ⟨g, hgY, hginj, hgfree⟩ := GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.exists_free_family Y w K
    (2 * (b + s - 1 - s) + s + 1) hw.2 ((Nat.add_le_add h1 h2).trans hcard)
  exact ⟨g, gridOK_of_free p nn Y B K w (2 * (b + s - 1 - s) + s) g hB hcut hsep hw.1 hgY hginj hgfree
    (fun a i => hq w hw hN _ (hgY a i) (hgfree a i))⟩

end grid

end CompanionTheory.WaveGrid
