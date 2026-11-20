import Formalism.LocalToGlobal.Divisibility.RecBridge
import Formalism.SharpRestriction.Divisibility.HookProducts.HookProd

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions Formalism.MainNotions.G

structure NumRecTieH (Nd : NumDatum) {D : D7} (L : SizeData₂ D) (u : D.what₂.Word) (δ : Code Nd) (Tl : ℕ) (Del h0 : ℕ) : Prop where

  datum : Nd = ofRecord D L Del h0

  word : HEq δ (letterOf D L Del h0 u)

  prime : Tl = (D.mem u).A.T

  del : D.s.Del = (Del : ℚ)

  eta : L.etaSz = (D.R.m : ℝ) * (h0 : ℝ)

end Formalism.L2.DIV

namespace Formalism.L2.DIV.NumTieH

open Formalism.BasicNotions Formalism.L2.DIV Formalism.MainNotions.G

variable (D : D7) (L : SizeData₂ D) (Del h0 : ℕ)

/- English proof (translation)
Establish `s : (∑ z : Bool × HH D, (ofRecord D L Del h0).kerPlace (letterOf D L Del h0 u) j z) = ∑ ρ : D.what₂.Tau, DV.kerPlace D L u j ρ` using `(Finset.sum_congr rfl (fun z _ => ofRecord_kerPlace D L Del h0 hDel u j z)).trans ((tauPl_bijective D).sum_comp (fun ρ => DV.kerPlace D L u j ρ))`. Establish `e : (ofRecord D L Del h0).hB C (letterOf D L Del h0 u) j = (∑ z : Bool × HH D, (ofRecord D L Del h0).kerPlace (letterOf D L Del h0 u) j z) + C * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * (ofRecord D L Del h0).La + C * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.R.N D.R.m : ℝ) ^ 2 * L.sc.L` using `rfl`. Rewrite using `[e, s, ofRecord_La]`. Both sides reduce to the same expression.
-/
theorem hB_eq (hDel : D.s.Del = (Del : ℚ)) (C : ℝ) (u : D.what₂.Word) (j : ℕ) :
    (ofRecord D L Del h0).hB C (letterOf D L Del h0 u) j = DV.kernelPlaceMeanBound D L C u j := by
  have s : (∑ z : Bool × HH D, (ofRecord D L Del h0).kerPlace (letterOf D L Del h0 u) j z) =
      ∑ ρ : D.what₂.Tau, DV.kerPlace D L u j ρ :=
    (Finset.sum_congr rfl (fun z _ => ofRecord_kerPlace D L Del h0 hDel u j z)).trans
      ((tauPl_bijective D).sum_comp (fun ρ => DV.kerPlace D L u j ρ))
  have e : (ofRecord D L Del h0).hB C (letterOf D L Del h0 u) j =
      (∑ z : Bool × HH D, (ofRecord D L Del h0).kerPlace (letterOf D L Del h0 u) j z) +
        C * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * (ofRecord D L Del h0).La +
        C * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.R.N D.R.m : ℝ) ^ 2 * L.sc.L := rfl
  rw [e, s, ofRecord_La]
  rfl

/- English proof (translation)
Unfold `NumDatum.Lp DV.Lprime`. Rewrite using `[ofRecord_rd]`.
-/
theorem Lp_eq : (ofRecord D L Del h0).Lp = DV.Lprime D L := by
  unfold NumDatum.Lp DV.Lprime
  rw [ofRecord_rd]

/- English proof (translation)
Establish `hk : 5 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega`. Take `⟨zi, hzi⟩` from `DV.sigPar_int D τ i`. Take `⟨zs, hzs⟩` from `DV.sigPar_int D τ (i + 1)`. Establish `hlt : DV.sigPar D τ (i + 1) < DV.sigPar D τ i`. Unfold `DV.sigPar`.

Distinguish the cases in `h1 : i + 1 < D.R.k - 1`. Rewrite using `[dif_pos h1, dif_pos (by omega : i < D.R.k - 1)]`. Establish `a` using `(D.hc τ).v_gt_u ⟨i, by omega⟩`. Establish `b` using `(D.hc τ).u_gt_v ⟨i + 1, h1⟩`. Conclude with `lt_trans b a`.

Distinguish the cases in `h2 : i + 1 = D.R.k - 1`. Rewrite using `[dif_neg h1, dif_pos (by omega : i < D.R.k - 1)]`. Establish `hb : i + 1 - (D.R.k - 1) < D.R.m` using `by omega`. Rewrite using `[dif_pos hb]`. Establish `a` using `(D.hc τ).v_gt_u ⟨i, by omega⟩`.

Establish `b` using `(D.hc τ).u_last_gt (by omega) (by have := D.R.two_le_m; omega)`. Establish `e1 : (⟨i + 1 - (D.R.k - 1), hb⟩ : Fin D.R.m) = ⟨0, by have` using `D.R.two_le_m; omega⟩ := Fin.ext (by simp; omega)`. Establish `e2 : (⟨(⟨i, by omega⟩ : Fin (D.R.k - 1)).1 + 1, by omega⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩` using `Fin.ext (by simp; omega)`. Rewrite using `[e1]`. Rewrite `a` using `[e2]`.

Conclude with `lt_trans b a`. Rewrite using `[dif_neg h1, dif_neg (by omega : ¬ i < D.R.k - 1)]`. Establish `hb1 : i + 1 - (D.R.k - 1) < D.R.m` using `by omega`. Establish `hb0 : i - (D.R.k - 1) < D.R.m` using `by omega`. Rewrite using `[dif_pos hb1, dif_pos hb0]`.

Establish `g1` using `(D.hc τ).gap_be ⟨i - (D.R.k - 1), hb0⟩`. Establish `g2` using `(D.hc τ).gap_eb ⟨i - (D.R.k - 1), hb0⟩ (by show i - (D.R.k - 1) + 1 < D.R.m; omega)`. Establish `e1 : (⟨i + 1 - (D.R.k - 1), hb1⟩ : Fin D.R.m) = ⟨i - (D.R.k - 1) + 1, by omega⟩` using `Fin.ext (by simp; omega)`. Rewrite using `[e1]`. Establish `ht : (0 : ℚ) ≤ D.R.t` using `by positivity`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `hlt`, the goal using `[hzi, hzs]`. Establish `: zs < zi` using `by exact_mod_cast hlt`. Establish `: zs + 1 ≤ zi` using `this`. Conclude with `this` after adjusting the coercions.
-/
theorem sigPar_succ (τ : D.what₂.Tau) (i : ℕ) (hi : i + 1 < D.R.k - 1 + D.R.m) :
    DV.sigPar D τ (i + 1) + 1 ≤ DV.sigPar D τ i := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  obtain ⟨zi, hzi⟩ := DV.sigPar_int D τ i
  obtain ⟨zs, hzs⟩ := DV.sigPar_int D τ (i + 1)
  have hlt : DV.sigPar D τ (i + 1) < DV.sigPar D τ i := by
    unfold DV.sigPar
    by_cases h1 : i + 1 < D.R.k - 1
    · rw [dif_pos h1, dif_pos (by omega : i < D.R.k - 1)]
      have a := (D.hc τ).v_gt_u ⟨i, by omega⟩
      have b := (D.hc τ).u_gt_v ⟨i + 1, h1⟩
      exact lt_trans b a
    · by_cases h2 : i + 1 = D.R.k - 1
      · rw [dif_neg h1, dif_pos (by omega : i < D.R.k - 1)]
        have hb : i + 1 - (D.R.k - 1) < D.R.m := by omega
        rw [dif_pos hb]
        have a := (D.hc τ).v_gt_u ⟨i, by omega⟩
        have b := (D.hc τ).u_last_gt (by omega) (by have := D.R.two_le_m; omega)
        have e1 : (⟨i + 1 - (D.R.k - 1), hb⟩ : Fin D.R.m) = ⟨0, by have := D.R.two_le_m; omega⟩ := Fin.ext (by simp; omega)
        have e2 : (⟨(⟨i, by omega⟩ : Fin (D.R.k - 1)).1 + 1, by omega⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩ :=
          Fin.ext (by simp; omega)
        rw [e1]
        rw [e2] at a
        exact lt_trans b a
      · rw [dif_neg h1, dif_neg (by omega : ¬ i < D.R.k - 1)]
        have hb1 : i + 1 - (D.R.k - 1) < D.R.m := by omega
        have hb0 : i - (D.R.k - 1) < D.R.m := by omega
        rw [dif_pos hb1, dif_pos hb0]
        have g1 := (D.hc τ).gap_be ⟨i - (D.R.k - 1), hb0⟩
        have g2 := (D.hc τ).gap_eb ⟨i - (D.R.k - 1), hb0⟩ (by show i - (D.R.k - 1) + 1 < D.R.m; omega)
        have e1 : (⟨i + 1 - (D.R.k - 1), hb1⟩ : Fin D.R.m) = ⟨i - (D.R.k - 1) + 1, by omega⟩ := Fin.ext (by simp; omega)
        rw [e1]
        have ht : (0 : ℚ) ≤ D.R.t := by positivity
        linarith
  rw [hzi, hzs] at hlt ⊢
  have : zs < zi := by exact_mod_cast hlt
  have : zs + 1 ≤ zi := this
  exact_mod_cast this

end Formalism.L2.DIV.NumTieH

namespace Formalism.L2.DIV.NumTieH

open Formalism.BasicNotions Formalism.L2.DIV Formalism.MainNotions.G

variable (D : D7) (L : SizeData₂ D) (Del h0 : ℕ)

/- English proof (translation)
Establish `hp : (D.R.sigW j).1 = D.R.k + j - 1` using `rfl`. Establish `h` using `sigPar_succ D τ i (by omega)`. Rewrite using `[DV.aPlusQ_eq, DV.aPlusQ_eq]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem aPlusQ_succ_le {j : ℕ} (hj : j ≤ D.R.m) (τ : D.what₂.Tau) {i : ℕ} (hi : i + 1 < (D.R.sigW j).1) :
    DV.aPlusQ D j τ (i + 1) ≤ DV.aPlusQ D j τ i := by
  have hp : (D.R.sigW j).1 = D.R.k + j - 1 := rfl
  have h := sigPar_succ D τ i (by omega)
  rw [DV.aPlusQ_eq, DV.aPlusQ_eq]
  push_cast
  linarith

/- English proof (translation)
Proceed by induction on `l, hil using Nat.le_induction with`. Consider the case `base => exact le_rfl`. Consider the case `succ l hil ih => exact (aPlusQ_succ_le D hj τ hl).trans (ih (by omega))`.
-/
theorem aPlusQ_anti {j : ℕ} (hj : j ≤ D.R.m) (τ : D.what₂.Tau) {i l : ℕ} (hil : i ≤ l) (hl : l < (D.R.sigW j).1) :
    DV.aPlusQ D j τ l ≤ DV.aPlusQ D j τ i := by
  induction l, hil using Nat.le_induction with
  | base => exact le_rfl
  | succ l hil ih => exact (aPlusQ_succ_le D hj τ hl).trans (ih (by omega))

/- English proof (translation)
Establish `hp : (D.R.sigW j).1 = D.R.k + j - 1` using `rfl`. Conclude with `(DV.aPlusQ_last D j h1 hj τ).trans (aPlusQ_anti D hj τ (by omega) (by omega))`.
-/
theorem aPlusQ_one_le {j : ℕ} (h1 : 1 ≤ j) (hj : j ≤ D.R.m) (τ : D.what₂.Tau) {i : ℕ} (hi : i < (D.R.sigW j).1) :
    1 ≤ DV.aPlusQ D j τ i := by
  have hp : (D.R.sigW j).1 = D.R.k + j - 1 := rfl
  exact (DV.aPlusQ_last D j h1 hj τ).trans (aPlusQ_anti D hj τ (by omega) (by omega))

/- English proof (translation)
Take `⟨w, hw⟩` from `DV.aPlusQ_int D j (tauPl D z) i`. Establish `h1w : (1 : ℚ) ≤ w` using `hw ▸ aPlusQ_one_le D h1 hj (tauPl D z) hi`. Establish `h0w : 0 ≤ w` using `by exact_mod_cast (show (0 : ℚ) ≤ w by linarith)`. Unfold `NumDatum.apN DV.aPlus`. Rewrite using `[ofRecord_aPlus, hw, Int.floor_intCast]`.

Establish `e : ((w.toNat : ℕ) : ℤ) = w` using `Int.toNat_of_nonneg h0w`. Establish `e2 : ((w.toNat : ℕ) : ℝ) = (w : ℝ)` using `by exact_mod_cast congrArg (fun x : ℤ => (x : ℝ)) e`. Rewrite using `[e2]`. Simplify using the standard rewrite rules.
-/
theorem apN_cast {j : ℕ} (h1 : 1 ≤ j) (hj : j ≤ D.R.m) (z : Bool × HH D) {i : ℕ} (hi : i < (D.R.sigW j).1) :
    (((ofRecord D L Del h0).apN j z i : ℕ) : ℝ) = DV.aPlus D j (tauPl D z) i := by
  obtain ⟨w, hw⟩ := DV.aPlusQ_int D j (tauPl D z) i
  have h1w : (1 : ℚ) ≤ w := hw ▸ aPlusQ_one_le D h1 hj (tauPl D z) hi
  have h0w : 0 ≤ w := by exact_mod_cast (show (0 : ℚ) ≤ w by linarith)
  unfold NumDatum.apN DV.aPlus
  rw [ofRecord_aPlus, hw, Int.floor_intCast]
  have e : ((w.toNat : ℕ) : ℤ) = w := Int.toNat_of_nonneg h0w
  have e2 : ((w.toNat : ℕ) : ℝ) = (w : ℝ) := by exact_mod_cast congrArg (fun x : ℤ => (x : ℝ)) e
  rw [e2]
  simp

/- English proof (translation)
Establish `e` using `apN_cast D L Del h0 h1 hj z hi`. Establish `h` using `aPlusQ_one_le D h1 hj (tauPl D z) hi`. Establish `: (1 : ℝ) ≤ (((ofRecord D L Del h0).apN j z i : ℕ) : ℝ)`. Rewrite using `[e]`. Unfold `DV.aPlus`.

Conclude with `h` after adjusting the coercions. Conclude with `this` after adjusting the coercions.
-/
theorem apN_ge {j : ℕ} (h1 : 1 ≤ j) (hj : j ≤ D.R.m) (z : Bool × HH D) {i : ℕ} (hi : i < (D.R.sigW j).1) :
    1 ≤ (ofRecord D L Del h0).apN j z i := by
  have e := apN_cast D L Del h0 h1 hj z hi
  have h := aPlusQ_one_le D h1 hj (tauPl D z) hi
  have : (1 : ℝ) ≤ (((ofRecord D L Del h0).apN j z i : ℕ) : ℝ) := by
    rw [e]; unfold DV.aPlus; exact_mod_cast h
  exact_mod_cast this

/- English proof (translation)
Establish `el` using `apN_cast D L Del h0 h1 hj z hl`. Establish `ei` using `apN_cast D L Del h0 h1 hj z (show i < (D.R.sigW j).1 by omega)`. Establish `h` using `aPlusQ_anti D hj (tauPl D z) hil.le hl`. Establish `: (((ofRecord D L Del h0).apN j z l : ℕ) : ℝ) ≤ (((ofRecord D L Del h0).apN j z i : ℕ) : ℝ)`. Rewrite using `[el, ei]`.

Unfold `DV.aPlus`. Conclude with `h` after adjusting the coercions. Conclude with `this` after adjusting the coercions.
-/
theorem apN_anti {j : ℕ} (h1 : 1 ≤ j) (hj : j ≤ D.R.m) (z : Bool × HH D) {i l : ℕ} (hil : i < l) (hl : l < (D.R.sigW j).1) :
    (ofRecord D L Del h0).apN j z l ≤ (ofRecord D L Del h0).apN j z i := by
  have el := apN_cast D L Del h0 h1 hj z hl
  have ei := apN_cast D L Del h0 h1 hj z (show i < (D.R.sigW j).1 by omega)
  have h := aPlusQ_anti D hj (tauPl D z) hil.le hl
  have : (((ofRecord D L Del h0).apN j z l : ℕ) : ℝ) ≤ (((ofRecord D L Del h0).apN j z i : ℕ) : ℝ) := by
    rw [el, ei]; unfold DV.aPlus; exact_mod_cast h
  exact_mod_cast this

end Formalism.L2.DIV.NumTieH

namespace Formalism.L2.DIV.NumTieH

open Formalism.BasicNotions Formalism.L2.DIV Formalism.MainNotions.G

variable (D : D7) (L : SizeData₂ D) (Del h0 : ℕ)

/- English proof (translation)
Use `set p := (D.R.sigW j).1 with hp`. Use `set A := (ofRecord D L Del h0).apN j z with hA`. Establish `hH` using `Formalism.MainNotions.DIV.HookProducts.hookProd_mul_prod p A (fun i hi => apN_ge D L Del h0 h1 hj z hi) (fun i l hil hl => apN_anti D L Del h0 h1 hj z hil hl)`. Establish `hdiag : (ofRecord D L Del h0).apDiag j z = YoungDiagram.ofRowLens (((List.range p).map A).insertionSort (· ≥ ·)) List.sortedGE_insertionSort` using `rfl`. Use `set μ := YoungDiagram.ofRowLens (((List.range p).map A).insertionSort (· ≥ ·)) List.sortedGE_insertionSort with hμ`.

Establish `hR : (Formalism.LatticeIndexTer.hookProd μ : ℝ) * ∏ i ∈ Finset.range p, ∏ l ∈ Finset.Ioo i p, ((A i + l - A l - i : ℕ) : ℝ) = ∏ i ∈ Finset.range p, ((A i + p - 1 - i).factorial : ℝ)` using `by exact_mod_cast hH`. Establish `hΔ : ∀ i ∈ Finset.range p, ∀ l ∈ Finset.Ioo i p, (0 : ℝ) < ((A i + l - A l - i : ℕ) : ℝ)`. Introduce `i _ l hl`. Rewrite `hl` using `[Finset.mem_Ioo]`. Establish `ha : A l ≤ A i` using `apN_anti D L Del h0 h1 hj z hl.1 hl.2`.

Establish `: 1 ≤ A i + l - A l - i` using `by omega`. Conclude with `this` after adjusting the coercions. Establish `hΔp : (0 : ℝ) < ∏ i ∈ Finset.range p, ∏ l ∈ Finset.Ioo i p, ((A i + l - A l - i : ℕ) : ℝ)` using `Finset.prod_pos fun i hi => Finset.prod_pos fun l hl => hΔ i hi l hl`. Establish `hFp : (0 : ℝ) < ∏ i ∈ Finset.range p, ((A i + p - 1 - i).factorial : ℝ)` using `Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos _`. Establish `hHp : (Formalism.LatticeIndexTer.hookProd μ : ℝ) ≠ 0`.

Introduce `h0'`. Rewrite `hR` using `[h0', zero_mul]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlog : Real.log (Formalism.LatticeIndexTer.hookProd μ : ℝ) = Real.log (∏ i ∈ Finset.range p, ((A i + p - 1 - i).factorial : ℝ)) - Real.log (∏ i ∈ Finset.range p, ∏ l ∈ Finset.Ioo i p, ((A i + l - A l - i : ℕ) : ℝ))`. Rewrite using `[← hR, Real.log_mul hHp hΔp.ne']`.

Expand and normalize the polynomial expressions, which then agree. Unfold `NumDatum.logHook`. Rewrite using `[hdiag, hlog, Real.log_prod (fun i _ => by positivity)]`. Rewrite using `[Real.log_prod (fun i hi => (Finset.prod_pos fun l hl => hΔ i hi l hl).ne')]`. Unfold `DV.logHook`.

Use `congr 1`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `hi' : i < p` using `Finset.mem_range.1 hi`. Rewrite using `[← apN_cast D L Del h0 h1 hj z hi']`. Take `⟨k, hk⟩ : ∃ k, A i + p - 1 - i = k` from `⟨_, rfl⟩`.

Establish `hk1 : k + 1 + i = A i + p` using `by omega`. Establish `hk2 : ((A i : ℕ) : ℝ) + (p : ℝ) - (i : ℝ) = (k : ℝ) + 1`. Establish `: ((k + 1 + i : ℕ) : ℝ) = ((A i + p : ℕ) : ℝ)` using `by rw [hk1]`. Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[hk, hk2, Real.Gamma_nat_eq_factorial]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `hi' : i < p` using `Finset.mem_range.1 hi`. Rewrite using `[Real.log_prod (fun l hl => (hΔ i hi l hl).ne')]`. Use `Finset.sum_congr rfl fun l hl => ?_` and prove the remaining obligations.

Establish `hl'` using `Finset.mem_Ioo.1 hl`. Rewrite using `[← apN_cast D L Del h0 h1 hj z hi', ← apN_cast D L Del h0 h1 hj z hl'.2]`. Establish `ha : A l ≤ A i` using `apN_anti D L Del h0 h1 hj z hl'.1 hl'.2`. Establish `e : ((A i + l - A l - i : ℕ) : ℝ) = (A i : ℝ) - (A l : ℝ) + (l : ℝ) - (i : ℝ)`. Establish `h2 : A i + l - A l - i + A l + i = A i + l` using `by omega`.

Establish `: ((A i + l - A l - i + A l + i : ℕ) : ℝ) = ((A i + l : ℕ) : ℝ)` using `by rw [h2]`. Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[e]`.
-/
theorem logHook_eq {j : ℕ} (h1 : 1 ≤ j) (hj : j ≤ D.R.m) (z : Bool × HH D) :
    (ofRecord D L Del h0).logHook j z = DV.logHook (D.R.sigW j).1 (DV.aPlus D j (tauPl D z)) := by
  set p := (D.R.sigW j).1 with hp
  set A := (ofRecord D L Del h0).apN j z with hA
  have hH := Formalism.MainNotions.DIV.HookProducts.hookProd_mul_prod p A (fun i hi => apN_ge D L Del h0 h1 hj z hi) (fun i l hil hl => apN_anti D L Del h0 h1 hj z hil hl)
  have hdiag : (ofRecord D L Del h0).apDiag j z =
      YoungDiagram.ofRowLens (((List.range p).map A).insertionSort (· ≥ ·)) List.sortedGE_insertionSort := rfl
  set μ := YoungDiagram.ofRowLens (((List.range p).map A).insertionSort (· ≥ ·)) List.sortedGE_insertionSort with hμ
  have hR : (Formalism.LatticeIndexTer.hookProd μ : ℝ) * ∏ i ∈ Finset.range p, ∏ l ∈ Finset.Ioo i p, ((A i + l - A l - i : ℕ) : ℝ) =
      ∏ i ∈ Finset.range p, ((A i + p - 1 - i).factorial : ℝ) := by exact_mod_cast hH
  have hΔ : ∀ i ∈ Finset.range p, ∀ l ∈ Finset.Ioo i p, (0 : ℝ) < ((A i + l - A l - i : ℕ) : ℝ) := by
    intro i _ l hl
    rw [Finset.mem_Ioo] at hl
    have ha : A l ≤ A i := apN_anti D L Del h0 h1 hj z hl.1 hl.2
    have : 1 ≤ A i + l - A l - i := by omega
    exact_mod_cast this
  have hΔp : (0 : ℝ) < ∏ i ∈ Finset.range p, ∏ l ∈ Finset.Ioo i p, ((A i + l - A l - i : ℕ) : ℝ) :=
    Finset.prod_pos fun i hi => Finset.prod_pos fun l hl => hΔ i hi l hl
  have hFp : (0 : ℝ) < ∏ i ∈ Finset.range p, ((A i + p - 1 - i).factorial : ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos _
  have hHp : (Formalism.LatticeIndexTer.hookProd μ : ℝ) ≠ 0 := by
    intro h0'; rw [h0', zero_mul] at hR; linarith
  have hlog : Real.log (Formalism.LatticeIndexTer.hookProd μ : ℝ) =
      Real.log (∏ i ∈ Finset.range p, ((A i + p - 1 - i).factorial : ℝ)) -
        Real.log (∏ i ∈ Finset.range p, ∏ l ∈ Finset.Ioo i p, ((A i + l - A l - i : ℕ) : ℝ)) := by
    rw [← hR, Real.log_mul hHp hΔp.ne']; ring
  unfold NumDatum.logHook
  rw [hdiag, hlog, Real.log_prod (fun i _ => by positivity)]
  rw [Real.log_prod (fun i hi => (Finset.prod_pos fun l hl => hΔ i hi l hl).ne')]
  unfold DV.logHook
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < p := Finset.mem_range.1 hi
    rw [← apN_cast D L Del h0 h1 hj z hi']
    obtain ⟨k, hk⟩ : ∃ k, A i + p - 1 - i = k := ⟨_, rfl⟩
    have hk1 : k + 1 + i = A i + p := by omega
    have hk2 : ((A i : ℕ) : ℝ) + (p : ℝ) - (i : ℝ) = (k : ℝ) + 1 := by
      have : ((k + 1 + i : ℕ) : ℝ) = ((A i + p : ℕ) : ℝ) := by rw [hk1]
      push_cast at this; linarith
    rw [hk, hk2, Real.Gamma_nat_eq_factorial]
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < p := Finset.mem_range.1 hi
    rw [Real.log_prod (fun l hl => (hΔ i hi l hl).ne')]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hl' := Finset.mem_Ioo.1 hl
    rw [← apN_cast D L Del h0 h1 hj z hi', ← apN_cast D L Del h0 h1 hj z hl'.2]
    have ha : A l ≤ A i := apN_anti D L Del h0 h1 hj z hl'.1 hl'.2
    have e : ((A i + l - A l - i : ℕ) : ℝ) = (A i : ℝ) - (A l : ℝ) + (l : ℝ) - (i : ℝ) := by
      have h2 : A i + l - A l - i + A l + i = A i + l := by omega
      have : ((A i + l - A l - i + A l + i : ℕ) : ℝ) = ((A i + l : ℕ) : ℝ) := by rw [h2]
      push_cast at this; linarith
    rw [e]

/- English proof (translation)
Establish `s : (∑ z : Bool × HH D, (ofRecord D L Del h0).logHook j z) = ∑ ρ : D.what₂.Tau, DV.logHook (D.R.sigW j).1 (DV.aPlus D j ρ)` using `(Finset.sum_congr rfl (fun z _ => logHook_eq D L Del h0 h1 hj z)).trans ((tauPl_bijective D).sum_comp (fun ρ => DV.logHook (D.R.sigW j).1 (DV.aPlus D j ρ)))`. Establish `e : (ofRecord D L Del h0).hX C j = (∑ z : Bool × HH D, (ofRecord D L Del h0).logHook j z) - C * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * (ofRecord D L Del h0).Lp` using `rfl`. Rewrite using `[e, s, Lp_eq]`. Both sides reduce to the same expression.
-/
theorem hX_eq (C : ℝ) {j : ℕ} (h1 : 1 ≤ j) (hj : j ≤ D.R.m) :
    (ofRecord D L Del h0).hX C j = DV.L6lo D L C j := by
  have s : (∑ z : Bool × HH D, (ofRecord D L Del h0).logHook j z) =
      ∑ ρ : D.what₂.Tau, DV.logHook (D.R.sigW j).1 (DV.aPlus D j ρ) :=
    (Finset.sum_congr rfl (fun z _ => logHook_eq D L Del h0 h1 hj z)).trans
      ((tauPl_bijective D).sum_comp (fun ρ => DV.logHook (D.R.sigW j).1 (DV.aPlus D j ρ)))
  have e : (ofRecord D L Del h0).hX C j = (∑ z : Bool × HH D, (ofRecord D L Del h0).logHook j z) -
      C * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * (ofRecord D L Del h0).Lp := rfl
  rw [e, s, Lp_eq]
  rfl

end Formalism.L2.DIV.NumTieH

namespace Formalism.L2.DIV

open Formalism.BasicNotions

/- English proof (translation)
Take `⟨hNd, hδ, hT, hDel, hEta⟩` from `t`. Substitute `hNd` using the available equality. Take `rfl` from `eq_of_heq hδ`. Substitute `hT` using the available equality. Rewrite using `[RecNums.ofNum_hu]`.

Unfold `NumDatum.hU`. Rewrite using `[← ofRecord_hA D L Del h0 hDel hEta]`. Establish `sB : ∑ j ∈ (ofRecord D L Del h0).lifts, (ofRecord D L Del h0).hB Ch (letterOf D L Del h0 u) j = ∑ j ∈ SizeData₂.lifts D, DV.kernelPlaceMeanBound D L Ch u j` using `Finset.sum_congr rfl fun j _ => NumTieH.hB_eq D L Del h0 hDel Ch u j`. Establish `sX : ∑ j ∈ (ofRecord D L Del h0).lifts, (ofRecord D L Del h0).hX Ch j = ∑ j ∈ SizeData₂.lifts D, DV.L6lo D L Ch j` using `Finset.sum_congr rfl fun j hj => by`. Establish `hj' : 1 ≤ j ∧ j ≤ D.R.m` using `Finset.mem_Icc.1 hj`.

Conclude with `NumTieH.hX_eq D L Del h0 Ch hj'.1 hj'.2`. Rewrite using `[sB, sX]`.
-/
theorem hnum_of_numRecTieH (Nd : NumDatum) {J : Type} [Fintype J] (eJ : J ≃ Fin Nd.R.m) (δ : Code Nd) (Tl : ℕ)
    (Nc lam0 C0 ce Ch Sw C1 : ℝ) (H : Nd.NumFacts δ Nc lam0 C0 ce Ch Sw C1) {D : D7} (L : SizeData₂ D) (u : D.what₂.Word)
    (Del h0 : ℕ) (t : NumRecTieH Nd L u δ Tl Del h0) :
    (RecNums.ofNum Nd eJ δ Tl Nc lam0 C0 ce Ch Sw C1 H).hu =
      DV.SZbP D L Ch u + (∑ j ∈ SizeData₂.lifts D, DV.kernelPlaceMeanBound D L Ch u j) - ∑ j ∈ SizeData₂.lifts D, DV.L6lo D L Ch j := by
  obtain ⟨hNd, hδ, hT, hDel, hEta⟩ := t
  subst hNd
  obtain rfl := eq_of_heq hδ
  subst hT
  rw [RecNums.ofNum_hu]
  unfold NumDatum.hU
  rw [← ofRecord_hA D L Del h0 hDel hEta]
  have sB : ∑ j ∈ (ofRecord D L Del h0).lifts, (ofRecord D L Del h0).hB Ch (letterOf D L Del h0 u) j =
      ∑ j ∈ SizeData₂.lifts D, DV.kernelPlaceMeanBound D L Ch u j :=
    Finset.sum_congr rfl fun j _ => NumTieH.hB_eq D L Del h0 hDel Ch u j
  have sX : ∑ j ∈ (ofRecord D L Del h0).lifts, (ofRecord D L Del h0).hX Ch j = ∑ j ∈ SizeData₂.lifts D, DV.L6lo D L Ch j :=
    Finset.sum_congr rfl fun j hj => by
      have hj' : 1 ≤ j ∧ j ≤ D.R.m := Finset.mem_Icc.1 hj
      exact NumTieH.hX_eq D L Del h0 Ch hj'.1 hj'.2
  rw [sB, sX]

end Formalism.L2.DIV
