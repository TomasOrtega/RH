import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable

open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

namespace GlobalTheory.LvT

variable {D : D7} {u : D.what₂.Word}

/- English proof (translation)
Unfold `Wt TauWeight`. Use `le_trans ?_ (Finset.le_sup (f := fun i => Finset.univ.sup fun a : Fin (D.R.N i) => if a.1 = 0 ∧ τ ∈ topsOf D.host D.eTau then 0 else ((X.fm.lam i τ).w a - ((i * (D.R.t + 1) / 2 : ℕ) : ℤ)).natAbs) (Finset.mem_range.2 (Nat.lt_succ_of_le hj)))` and prove the remaining obligations. Use `le_trans ?_ (Finset.le_sup (f := fun a : Fin (D.R.N j) => if a.1 = 0 ∧ τ ∈ topsOf D.host D.eTau then 0 else ((X.fm.lam j τ).w a - ((j * (D.R.t + 1) / 2 : ℕ) : ℤ)).natAbs) (Finset.mem_univ a))` and prove the remaining obligations. Rewrite using `[if_neg ha]`. Conclude with `le_rfl`.
-/
theorem natAbs_lamT_le_Wt (X : Ch D u) (j : ℕ) (hj : j ≤ D.R.m) (τ : D.what₂.Tau) (a : Fin (D.R.N j))
    (ha : ¬ (a.1 = 0 ∧ τ ∈ tops D)) : ((PtModel.lamT X j τ).w a).natAbs ≤ Wt X τ := by
  unfold Wt TauWeight
  refine le_trans ?_ (Finset.le_sup (f := fun i => Finset.univ.sup fun a : Fin (D.R.N i) =>
    if a.1 = 0 ∧ τ ∈ topsOf D.host D.eTau then 0
    else ((X.fm.lam i τ).w a - ((i * (D.R.t + 1) / 2 : ℕ) : ℤ)).natAbs)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hj)))
  refine le_trans ?_ (Finset.le_sup (f := fun a : Fin (D.R.N j) =>
    if a.1 = 0 ∧ τ ∈ topsOf D.host D.eTau then 0
    else ((X.fm.lam j τ).w a - ((j * (D.R.t + 1) / 2 : ℕ) : ℤ)).natAbs) (Finset.mem_univ a))
  rw [if_neg ha]
  exact le_rfl

/- English proof (translation)
Establish `hN : D.R.N (i + 1) = D.R.k + (i + 1) * (D.R.t + 1)` using `rfl`. Establish `hm : (i + 1) * (D.R.t + 1) = i * (D.R.t + 1) + D.R.t + 1` using `by ring`. Establish `ha' : a.1 = D.R.k + (D.R.t + i * (D.R.t + 1))` using `by omega`. Establish `hk : ¬ a.1 < D.R.k` using `by omega`. Establish `hq : (a.1 - D.R.k) / (D.R.t + 1) = i`.

Rewrite using `[ha', Nat.add_sub_cancel_left, Nat.add_mul_div_right _ _ (Nat.succ_pos _), Nat.div_eq_of_lt (Nat.lt_succ_self _), zero_add]`. Establish `h1` using `X.fm.lam_eq (i + 1) hi τ a`. Rewrite `h1` using `[dif_neg hk]`. Simplify using `only [hq] at h1`. Establish `h2` using `X.C.sDiv_eq i hi τ`.

Take `⟨c, hc⟩` from `D.R.t_odd`. Establish `h3 : (i + 1) * (D.R.t + 1) / 2 = (i + 1) * (c + 1)`. Establish `: (i + 1) * (D.R.t + 1) = 2 * ((i + 1) * (c + 1))` using `by rw [hc]; ring`. Rewrite using `[this, Nat.mul_div_cancel_left _ (by norm_num)]`. Establish `hcq : (D.R.t : ℚ) = 2 * c + 1` using `by exact_mod_cast hc`.

Express the relevant statement in the definitionally equal form `(X.fm.lam (i + 1) τ).w a - (((i + 1) * (D.R.t + 1) / 2 : ℕ) : ℤ) = _`. Rewrite using `[h3]`. Establish `: (((X.fm.lam (i + 1) τ).w a - (((i + 1) * (c + 1) : ℕ) : ℤ) : ℤ) : ℚ) = ((-X.C.sDiv i τ : ℤ) : ℚ)`. Use `push_cast`. Rewrite using `[h1, h2]`.

Simplify using `only [wG, sExp, Ranks.N, Nat.add_sub_cancel]`. Use `push_cast`. Rewrite using `[hcq]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `this` after adjusting the coercions.
-/
theorem lamT_last (X : Ch D u) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) (a : Fin (D.R.N (i + 1)))
    (ha : a.1 = D.R.N (i + 1) - 1) : (PtModel.lamT X (i + 1) τ).w a = -X.C.sDiv i τ := by
  have hN : D.R.N (i + 1) = D.R.k + (i + 1) * (D.R.t + 1) := rfl
  have hm : (i + 1) * (D.R.t + 1) = i * (D.R.t + 1) + D.R.t + 1 := by ring
  have ha' : a.1 = D.R.k + (D.R.t + i * (D.R.t + 1)) := by omega
  have hk : ¬ a.1 < D.R.k := by omega
  have hq : (a.1 - D.R.k) / (D.R.t + 1) = i := by
    rw [ha', Nat.add_sub_cancel_left, Nat.add_mul_div_right _ _ (Nat.succ_pos _),
      Nat.div_eq_of_lt (Nat.lt_succ_self _), zero_add]
  have h1 := X.fm.lam_eq (i + 1) hi τ a
  rw [dif_neg hk] at h1
  simp only [hq] at h1
  have h2 := X.C.sDiv_eq i hi τ
  obtain ⟨c, hc⟩ := D.R.t_odd
  have h3 : (i + 1) * (D.R.t + 1) / 2 = (i + 1) * (c + 1) := by
    have : (i + 1) * (D.R.t + 1) = 2 * ((i + 1) * (c + 1)) := by rw [hc]; ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  have hcq : (D.R.t : ℚ) = 2 * c + 1 := by exact_mod_cast hc
  change (X.fm.lam (i + 1) τ).w a - (((i + 1) * (D.R.t + 1) / 2 : ℕ) : ℤ) = _
  rw [h3]
  have : (((X.fm.lam (i + 1) τ).w a - (((i + 1) * (c + 1) : ℕ) : ℤ) : ℤ) : ℚ) = ((-X.C.sDiv i τ : ℤ) : ℚ) := by
    push_cast
    rw [h1, h2]
    simp only [wG, sExp, Ranks.N, Nat.add_sub_cancel]
    push_cast
    rw [hcq]
    ring
  exact_mod_cast this

/- English proof (translation)
Introduce `D u X hb hs`. Use `⟨hb, fun i hi τ => ?_⟩` and prove the remaining obligations. Establish `hpos` using `D.R.N_pos (i + 1)`. Establish `hlast` using `lamT_last X i hi τ ⟨D.R.N (i + 1) - 1, by omega⟩ rfl`. Establish `hk` using `D.R.m_add_three_le_k`.

Establish `hN : D.R.N (i + 1) = D.R.k + (i + 1) * (D.R.t + 1)` using `rfl`. Use `⟨hs i hi τ, ?_, ?_, fun hτ => ?_⟩` and prove the remaining obligations. Establish `h` using `natAbs_lamT_le_Wt X (i + 1) hi τ ⟨D.R.N (i + 1) - 1, by omega⟩ (fun h => by`. Use `h.1` as an intermediate fact. Simplify using `only at this`.

Use the proof step `omega)`. Rewrite `h` using `[hlast]`. Use linear arithmetic over natural numbers and integers. Unfold `DomWeight.detShift`. Rewrite using `[dif_pos hpos]`.

Conclude with `hlast`. Establish `h` using `natAbs_lamT_le_Wt X (i + 1) hi τ ⟨0, hpos⟩ (fun h => hτ h.2)`. Use linear arithmetic over natural numbers and integers.
-/
theorem wtBounds_of_nonneg : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u), (∀ τ ∈ tops D, 0 ≤ X.fm.bTop τ) →
    (∀ i, i < D.R.m → ∀ τ, 0 ≤ X.C.sDiv i τ) → WtBounds X := by
  intro D u X hb hs
  refine ⟨hb, fun i hi τ => ?_⟩
  have hpos := D.R.N_pos (i + 1)
  have hlast := lamT_last X i hi τ ⟨D.R.N (i + 1) - 1, by omega⟩ rfl
  have hk := D.R.m_add_three_le_k
  have hN : D.R.N (i + 1) = D.R.k + (i + 1) * (D.R.t + 1) := rfl
  refine ⟨hs i hi τ, ?_, ?_, fun hτ => ?_⟩
  · have h := natAbs_lamT_le_Wt X (i + 1) hi τ ⟨D.R.N (i + 1) - 1, by omega⟩ (fun h => by
      have := h.1
      simp only at this
      omega)
    rw [hlast] at h
    omega
  · unfold DomWeight.detShift
    rw [dif_pos hpos]
    exact hlast
  · have h := natAbs_lamT_le_Wt X (i + 1) hi τ ⟨0, hpos⟩ (fun h => hτ h.2)
    omega

end GlobalTheory.LvT
