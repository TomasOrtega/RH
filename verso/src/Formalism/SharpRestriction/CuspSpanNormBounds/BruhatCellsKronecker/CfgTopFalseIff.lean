import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro
import Formalism.HermitianCurvature.StatementSz

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Finset

/- English proof (translation)
Establish `hh : 1 ≤ j + 1 ∧ j + 1 ≤ D.R.k - 1` using `⟨by omega, by omega⟩`. Rewrite using `[vOne, dif_pos hh]`. Simplify using `only [Nat.add_sub_cancel]`.
-/
theorem vOne_succ (D : D7) (τ : D.what₂.Tau) (j : ℕ) (h : j < D.R.k - 1) :
    vOne D τ (j + 1) = (((D.hc τ).v ⟨j, h⟩ : ℚ) : ℝ) := by
  have hh : 1 ≤ j + 1 ∧ j + 1 ≤ D.R.k - 1 := ⟨by omega, by omega⟩
  rw [vOne, dif_pos hh]
  simp only [Nat.add_sub_cancel]

/- English proof (translation)
Establish `hh : 1 ≤ j + 1 ∧ j + 1 ≤ D.R.m` using `⟨by omega, by omega⟩`. Rewrite using `[bOne, dif_pos hh]`. Simplify using `only [Nat.add_sub_cancel]`.
-/
theorem bOne_succ (D : D7) (τ : D.what₂.Tau) (j : ℕ) (h : j < D.R.m) :
    bOne D τ (j + 1) = (((D.hc τ).b ⟨j, h⟩ : ℚ) : ℝ) := by
  have hh : 1 ≤ j + 1 ∧ j + 1 ≤ D.R.m := ⟨by omega, by omega⟩
  rw [bOne, dif_pos hh]
  simp only [Nat.add_sub_cancel]

/- English proof (translation)
Establish `hh : 1 ≤ j + 1 ∧ j + 1 ≤ D.R.k` using `⟨by omega, by omega⟩`. Rewrite using `[uOne, dif_pos hh]`. Simplify using `only [uS, Nat.add_sub_cancel]`.
-/
theorem uOne_succ (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (j : ℕ) (h : j < D.R.k) :
    uOne D u τ (j + 1) = (((D.hcW u τ).u ⟨j, h⟩ : ℚ) : ℝ) := by
  have hh : 1 ≤ j + 1 ∧ j + 1 ≤ D.R.k := ⟨by omega, by omega⟩
  rw [uOne, dif_pos hh]
  simp only [uS, Nat.add_sub_cancel]

/- English proof (translation)
Establish `h1` using `D.R.m_add_three_le_k`. Establish `h2` using `D.R.two_le_m`. Use linear arithmetic over natural numbers and integers.
-/
theorem five_le_k (D : D7) : 5 ≤ D.R.k := by
  have h1 := D.R.m_add_three_le_k
  have h2 := D.R.two_le_m
  omega

/- English proof (translation)
Establish `h2` using `D.R.two_le_m`. Take `⟨c, hc⟩` from `D.R.m_even`. Unfold `Ranks.rS`. Use linear arithmetic over natural numbers and integers.
-/
theorem m_eq (D : D7) : D.R.m = 2 * D.R.rS + 2 := by
  have h2 := D.R.two_le_m
  obtain ⟨c, hc⟩ := D.R.m_even
  unfold Ranks.rS
  omega

/- English proof (translation)
Establish `hk` using `five_le_k D`. Establish `e1` using `uOne_succ D u τ 0 (by omega)`. Establish `e2` using `uOne_succ D D.u₀ τ 0 (by omega)`. Simplify using `only [Nat.zero_add] at e1 e2`. Rewrite using `[e1, e2, D.hcW_first u τ (by omega), D.hcW_first D.u₀ τ (by omega)]`.
-/
theorem uOne_one (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : uOne D u τ 1 = uOne D D.u₀ τ 1 := by
  have hk := five_le_k D
  have e1 := uOne_succ D u τ 0 (by omega)
  have e2 := uOne_succ D D.u₀ τ 0 (by omega)
  simp only [Nat.zero_add] at e1 e2
  rw [e1, e2, D.hcW_first u τ (by omega), D.hcW_first D.u₀ τ (by omega)]

/- English proof (translation)
Establish `hk` using `five_le_k D`. Establish `e1` using `uOne_succ D u τ (D.R.k - 1) (by omega)`. Establish `e2` using `uOne_succ D D.u₀ τ (D.R.k - 1) (by omega)`. Rewrite `e1`, `e2` using `[Nat.sub_add_cancel (by omega : 1 ≤ D.R.k)]`. Rewrite using `[e1, e2, D.hcW_last u τ (by omega), D.hcW_last D.u₀ τ (by omega)]`.
-/
theorem uOne_last (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : uOne D u τ D.R.k = uOne D D.u₀ τ D.R.k := by
  have hk := five_le_k D
  have e1 := uOne_succ D u τ (D.R.k - 1) (by omega)
  have e2 := uOne_succ D D.u₀ τ (D.R.k - 1) (by omega)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ D.R.k)] at e1 e2
  rw [e1, e2, D.hcW_last u τ (by omega), D.hcW_last D.u₀ τ (by omega)]

/- English proof (translation)
Establish `hj : j < D.R.k - 1` using `by omega`. Rewrite using `[vOne_succ D τ j hj, show j + 2 = j + 1 + 1 from rfl, vOne_succ D τ (j + 1) h]`. Establish `g` using `D.s.cloud_gap D.u₀ τ j h`. Rewrite `g` using `[D.hcW_base]`. Establish `g2 : (((D.hc τ).v ⟨j, hj⟩ : ℚ) : ℝ) - (((D.hc τ).v ⟨j + 1, h⟩ : ℚ) : ℝ) = 4 * (D.s.Del : ℝ)`.

Conclude with `g` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem vOne_gap (D : D7) (τ : D.what₂.Tau) (j : ℕ) (h : j + 1 < D.R.k - 1) :
    vOne D τ (j + 1) = vOne D τ (j + 2) + 4 * (D.s.Del : ℝ) := by
  have hj : j < D.R.k - 1 := by omega
  rw [vOne_succ D τ j hj, show j + 2 = j + 1 + 1 from rfl, vOne_succ D τ (j + 1) h]
  have g := D.s.cloud_gap D.u₀ τ j h
  rw [D.hcW_base] at g
  have g2 : (((D.hc τ).v ⟨j, hj⟩ : ℚ) : ℝ) - (((D.hc τ).v ⟨j + 1, h⟩ : ℚ) : ℝ) = 4 * (D.s.Del : ℝ) := by
    exact_mod_cast g
  linarith

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `j hj`. Rewrite using `[show D.R.k - 1 = j + 1 by omega]`.

Simplify using the standard rewrite rules. Consider the case `succ d ih`. Introduce `j hj`. Establish `h1` using `vOne_gap D τ j (by omega)`. Establish `h2` using `ih (j + 1) (by omega)`.

Rewrite `h2` using `[show j + 1 + 1 = j + 2 from rfl]`. Rewrite using `[h1, h2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vOne_arith (D : D7) (τ : D.what₂.Tau) : ∀ d j : ℕ, j + d + 2 = D.R.k →
    vOne D τ (j + 1) = vOne D τ (D.R.k - 1) + 4 * (D.s.Del : ℝ) * d := by
  intro d
  induction d with
  | zero =>
    intro j hj
    rw [show D.R.k - 1 = j + 1 by omega]
    simp
  | succ d ih =>
    intro j hj
    have h1 := vOne_gap D τ j (by omega)
    have h2 := ih (j + 1) (by omega)
    rw [show j + 1 + 1 = j + 2 from rfl] at h2
    rw [h1, h2]
    push_cast
    ring

open Classical in

def cfgOf (D : D7) (τ : D.what₂.Tau) : Sz.Cfg where
  k := D.R.k
  m := D.R.m
  Del := (D.s.Del : ℝ)
  vlast := vOne D τ (D.R.k - 1)
  b := bOne D τ
  a := uOne D D.u₀ τ 1
  top := decide (IsTop D τ)
  bp := bTop D τ

def deOf (D : D7) (u : D.what₂.Word) (l : ℕ) : ℝ :=
  if h : 1 ≤ l ∧ l ≤ D.R.k - 2 then (if D.s.letter u ⟨l - 1, by omega⟩ then 1 else 0) else 0

/- English proof (translation)
Establish `hh : 1 ≤ l + 1 ∧ l + 1 ≤ D.R.k - 2` using `⟨by omega, by omega⟩`. Rewrite using `[deOf, dif_pos hh]`. Simplify using `only [Nat.add_sub_cancel]`.
-/
theorem deOf_succ (D : D7) (u : D.what₂.Word) (l : ℕ) (h : l < D.R.k - 2) :
    deOf D u (l + 1) = if D.s.letter u ⟨l, h⟩ then 1 else 0 := by
  have hh : 1 ≤ l + 1 ∧ l + 1 ≤ D.R.k - 2 := ⟨by omega, by omega⟩
  rw [deOf, dif_pos hh]
  simp only [Nat.add_sub_cancel]

/- English proof (translation)
Establish `hk` using `five_le_k D`. Unfold `Sz.IsWord`. Use `⟨fun i => ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `unfold deOf split_ifs <;> simp`. Establish `hn : ¬ (1 ≤ D.R.k - 1 ∧ D.R.k - 1 ≤ D.R.k - 2)` using `by omega`.

Rewrite using `[deOf, dif_neg hn]`.
-/
theorem isWord_deOf (D : D7) (u : D.what₂.Word) : Sz.IsWord D.R.k (deOf D u) := by
  have hk := five_le_k D
  unfold Sz.IsWord
  refine ⟨fun i => ?_, ?_⟩
  · unfold deOf
    split_ifs <;> simp
  · have hn : ¬ (1 ≤ D.R.k - 1 ∧ D.R.k - 1 ≤ D.R.k - 2) := by omega
    rw [deOf, dif_neg hn]

/- English proof (translation)
Simplify using `[cfgOf]`.
-/
theorem cfg_top_iff (D : D7) (τ : D.what₂.Tau) : (cfgOf D τ).top = true ↔ IsTop D τ := by
  simp [cfgOf]

/- English proof (translation)
Simplify using `[cfgOf]`.
-/
theorem cfg_top_false_iff (D : D7) (τ : D.what₂.Tau) : (cfgOf D τ).top = false ↔ ¬ IsTop D τ := by
  simp [cfgOf]

/- English proof (translation)
Use `show vOne D τ (D.R.k - 1) + 4 * (D.s.Del : ℝ) * ((D.R.k : ℝ) - 1 - (i : ℝ)) = vOne D τ i`. Take `⟨j, rfl⟩ : ∃ j, i = j + 1` from `⟨i - 1, by omega⟩`. Establish `hk` using `five_le_k D`. Rewrite using `[vOne_arith D τ (D.R.k - 2 - j) j (by omega)]`. Establish `hc : ((D.R.k - 2 - j : ℕ) : ℝ) = (D.R.k : ℝ) - 2 - j`.

Rewrite using `[Nat.sub_sub, Nat.cast_sub (show 2 + j ≤ D.R.k by omega)]`. Apply the tactic sequence `push_cast <;> ring`. Rewrite using `[hc]`. Apply the tactic sequence `push_cast <;> ring`.
-/
theorem cfg_v (D : D7) (τ : D.what₂.Tau) (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ D.R.k - 1) :
    (cfgOf D τ).v i = vOne D τ i := by
  show vOne D τ (D.R.k - 1) + 4 * (D.s.Del : ℝ) * ((D.R.k : ℝ) - 1 - (i : ℝ)) = vOne D τ i
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hk := five_le_k D
  rw [vOne_arith D τ (D.R.k - 2 - j) j (by omega)]
  have hc : ((D.R.k - 2 - j : ℕ) : ℝ) = (D.R.k : ℝ) - 2 - j := by
    rw [Nat.sub_sub, Nat.cast_sub (show 2 + j ≤ D.R.k by omega)]
    push_cast <;> ring
  rw [hc]
  push_cast <;> ring

/- English proof (translation)
Establish `hk` using `five_le_k D`. Simplify using `only [Sz.Cfg.u]`. Use `split_ifs with hi1 hik`. Substitute `hi1` using the available equality. Conclude with `(uOne_one D u τ).symm`.

Establish `hik' : i = D.R.k` using `hik`. Rewrite using `[hik']`. Unfold `Sz.Cfg.ulast`. Use `split_ifs with ht`. Rewrite using `[cfg_top_iff] at ht show -bTop D τ = _`.

Unfold `bTop`. Rewrite using `[neg_neg]`. Conclude with `(uOne_last D u τ).symm`. Rewrite using `[cfg_top_iff] at ht show vOne D τ (D.R.k - 1) - 1 / 2 = _`. Conclude with `(h5 ht).symm`.

Establish `hik' : i ≠ D.R.k` using `hik`. Take `⟨l, rfl⟩ : ∃ l, i = l + 2` from `⟨i - 2, by omega⟩`. Establish `hl : l < D.R.k - 2` using `by omega`. Rewrite using `[show l + 2 - 1 = l + 1 by omega, cfg_v D τ (l + 1) (by omega) (by omega), vOne_succ D τ l (by omega), deOf_succ D u l hl, show l + 2 = l + 1 + 1 from rfl, uOne_succ D u τ (l + 1) (by omega)]`. Establish `e` using `D.s.u_letter u τ l hl`.

Rewrite using `[e, D.hcW_v u τ]`. Use `show _ - _ - _ * ((D.s.Del : ℚ) : ℝ) = _`. Apply the tactic sequence `split_ifs <;> push_cast <;> ring`.
-/
theorem cfg_u (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau)
    (h5 : ¬ IsTop D τ → uOne D u τ D.R.k = vOne D τ (D.R.k - 1) - 1 / 2)
    (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ D.R.k) :
    (cfgOf D τ).u (deOf D u) i = uOne D u τ i := by
  have hk := five_le_k D
  simp only [Sz.Cfg.u]
  split_ifs with hi1 hik
  · subst hi1
    exact (uOne_one D u τ).symm
  · have hik' : i = D.R.k := hik
    rw [hik']
    unfold Sz.Cfg.ulast
    split_ifs with ht
    · rw [cfg_top_iff] at ht
      show -bTop D τ = _
      unfold bTop
      rw [neg_neg]
      exact (uOne_last D u τ).symm
    · rw [cfg_top_iff] at ht
      show vOne D τ (D.R.k - 1) - 1 / 2 = _
      exact (h5 ht).symm
  · have hik' : i ≠ D.R.k := hik
    obtain ⟨l, rfl⟩ : ∃ l, i = l + 2 := ⟨i - 2, by omega⟩
    have hl : l < D.R.k - 2 := by omega
    rw [show l + 2 - 1 = l + 1 by omega, cfg_v D τ (l + 1) (by omega) (by omega),
      vOne_succ D τ l (by omega), deOf_succ D u l hl, show l + 2 = l + 1 + 1 from rfl,
      uOne_succ D u τ (l + 1) (by omega)]
    have e := D.s.u_letter u τ l hl
    rw [e, D.hcW_v u τ]
    show _ - _ - _ * ((D.s.Del : ℚ) : ℝ) = _
    split_ifs <;> push_cast <;> ring

/- English proof (translation)
Establish `hk` using `five_le_k D`. Establish `ha` using `a.isLt`. Simplify using `only [Sz.Cfg.lam, lamS]`. Distinguish the cases in `h : a.1 < D.R.k - 1`. Establish `h1 : a.1 + 1 < (cfgOf D τ).k` using `by show a.1 + 1 < D.R.k`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[if_pos h1, dif_pos h, cfg_v D τ (a.1 + 1) (by omega) (by omega), vOne_succ D τ a.1 h]`. Establish `h1 : ¬ (a.1 + 1 < (cfgOf D τ).k)` using `by show ¬ (a.1 + 1 < D.R.k)`. Use linear arithmetic over natural numbers and integers. Establish `h2 : a.1 - (D.R.k - 1) < D.R.m`.

Establish `ha' : a.1 < D.R.k + D.R.m - 1` using `ha`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg h1, dif_neg h, dif_pos h2]`. Use `show -bOne D τ (a.1 + 1 + 1 - D.R.k) = _`. Rewrite using `[show a.1 + 1 + 1 - D.R.k = (a.1 - (D.R.k - 1)) + 1 by omega, bOne_succ D τ _ h2]`.
-/
theorem cfg_lam (D : D7) (τ : D.what₂.Tau) (a : Fin D.R.r) :
    (cfgOf D τ).lam (a.1 + 1) = lamS D.R (D.hc τ) a := by
  have hk := five_le_k D
  have ha := a.isLt
  simp only [Sz.Cfg.lam, lamS]
  by_cases h : a.1 < D.R.k - 1
  · have h1 : a.1 + 1 < (cfgOf D τ).k := by
      show a.1 + 1 < D.R.k
      omega
    rw [if_pos h1, dif_pos h, cfg_v D τ (a.1 + 1) (by omega) (by omega), vOne_succ D τ a.1 h]
  · have h1 : ¬ (a.1 + 1 < (cfgOf D τ).k) := by
      show ¬ (a.1 + 1 < D.R.k)
      omega
    have h2 : a.1 - (D.R.k - 1) < D.R.m := by
      have ha' : a.1 < D.R.k + D.R.m - 1 := ha
      omega
    rw [if_neg h1, dif_neg h, dif_pos h2]
    show -bOne D τ (a.1 + 1 + 1 - D.R.k) = _
    rw [show a.1 + 1 + 1 - D.R.k = (a.1 - (D.R.k - 1)) + 1 by omega, bOne_succ D τ _ h2]

/- English proof (translation)
Use `show (cfgOf D τ).lam (a.1 + 1) = lamS D.R (D.hc τ) (Fin.cast (dimS_eq D.R) a)`. Conclude with `cfg_lam D τ (Fin.cast (dimS_eq D.R) a)`.
-/
theorem cfg_lamH (D : D7) (τ : D.what₂.Tau) (a : Fin (2 * D.R.rS + D.R.k + 1)) :
    (cfgOf D τ).lam (a.1 + 1) = lamSH D.R (D.hc τ) a := by
  show (cfgOf D τ).lam (a.1 + 1) = lamS D.R (D.hc τ) (Fin.cast (dimS_eq D.R) a)
  exact cfg_lam D τ (Fin.cast (dimS_eq D.R) a)

/- English proof (translation)
Proceed by induction on `p with`. Consider the case `zero`. Rewrite using `[Finset.Icc_eq_empty (show ¬ (1 ≤ 0) by omega)]`. Simplify using the standard rewrite rules. Consider the case `succ n ih`.

Rewrite using `[Finset.prod_Icc_succ_top (show 1 ≤ n + 1 by omega), ih, Fin.prod_univ_castSucc]`. Simplify using the standard rewrite rules.
-/
theorem prod_Icc_eq_fin (p : ℕ) (F : ℕ → ℝ) : ∏ i ∈ Icc 1 p, F i = ∏ a : Fin p, F (a.1 + 1) := by
  induction p with
  | zero =>
    rw [Finset.Icc_eq_empty (show ¬ (1 ≤ 0) by omega)]
    simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (show 1 ≤ n + 1 by omega), ih, Fin.prod_univ_castSucc]
    simp

/- English proof (translation)
Unfold `Sz.Vand vand`. Rewrite using `[prod_Icc_eq_fin]`. Use `Finset.prod_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Use `symm`. Use `Finset.prod_nbij' (fun b => b.1 + 1) (fun j => if hj : j - 1 < p then ⟨j - 1, hj⟩ else a) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations.

Introduce `b hb`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hb`. Establish `hb' : a.1 < b.1` using `hb`. Establish `hbp` using `b.isLt`. Simplify using `only [Finset.mem_Ioc]`.

Use linear arithmetic over natural numbers and integers. Introduce `j hj`. Simplify using `only [Finset.mem_Ioc] at hj`. Establish `hjp : j - 1 < p` using `by omega`. Simplify using `only [hjp, ↓reduceDIte, Finset.mem_filter, Finset.mem_univ, true_and]`.

Use `show a.1 < j - 1`. Use linear arithmetic over natural numbers and integers. Introduce `b _`. Establish `hbp : b.1 + 1 - 1 < p`. Use `b.isLt` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Simplify using `only [hbp, ↓reduceDIte]`. Use `ext`. Simplify using the standard rewrite rules. Introduce `j hj`.

Simplify using `only [Finset.mem_Ioc] at hj`. Establish `hjp : j - 1 < p` using `by omega`. Simplify using `only [hjp, ↓reduceDIte]`. Use linear arithmetic over natural numbers and integers. Introduce `b _ show y a - y b = x (a.1 + 1) - x (b.1 + 1)`.

Rewrite using `[h a, h b]`.
-/
theorem Vand_eq_vand {p : ℕ} (x : ℕ → ℝ) (y : Fin p → ℝ) (h : ∀ a : Fin p, x (a.1 + 1) = y a) :
    Sz.Vand p x = vand y := by
  unfold Sz.Vand vand
  rw [prod_Icc_eq_fin]
  refine Finset.prod_congr rfl (fun a _ => ?_)
  symm
  refine Finset.prod_nbij' (fun b => b.1 + 1) (fun j => if hj : j - 1 < p then ⟨j - 1, hj⟩ else a)
    ?_ ?_ ?_ ?_ ?_
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    have hb' : a.1 < b.1 := hb
    have hbp := b.isLt
    simp only [Finset.mem_Ioc]
    omega
  · intro j hj
    simp only [Finset.mem_Ioc] at hj
    have hjp : j - 1 < p := by omega
    simp only [hjp, ↓reduceDIte, Finset.mem_filter, Finset.mem_univ, true_and]
    show a.1 < j - 1
    omega
  · intro b _
    have hbp : b.1 + 1 - 1 < p := by
      have := b.isLt
      omega
    simp only [hbp, ↓reduceDIte]
    ext
    simp
  · intro j hj
    simp only [Finset.mem_Ioc] at hj
    have hjp : j - 1 < p := by omega
    simp only [hjp, ↓reduceDIte]
    omega
  · intro b _
    show y a - y b = x (a.1 + 1) - x (b.1 + 1)
    rw [h a, h b]

/- English proof (translation)
Apply `Vand_eq_vand` to reduce the goal to its premises. Introduce `a`. Rewrite using `[cfg_u D u τ h5 (a.1 + 1) (by omega) (by have := a.isLt; omega), uOne_succ D u τ a.1 a.isLt]`. Both sides reduce to the same expression.
-/
theorem Vand_u (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau)
    (h5 : ¬ IsTop D τ → uOne D u τ D.R.k = vOne D τ (D.R.k - 1) - 1 / 2) :
    Sz.Vand D.R.k ((cfgOf D τ).u (deOf D u)) = vand (uS D u τ) := by
  apply Vand_eq_vand
  intro a
  rw [cfg_u D u τ h5 (a.1 + 1) (by omega) (by have := a.isLt; omega), uOne_succ D u τ a.1 a.isLt]
  rfl

/- English proof (translation)
Establish `hp : (cfgOf D τ).k + (cfgOf D τ).m - 1 = 2 * D.R.rS + D.R.k + 1` using `by show D.R.k + D.R.m - 1 = 2 * D.R.rS + D.R.k + 1`. Use `m_eq D` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[hp]`. Apply `Vand_eq_vand` to reduce the goal to its premises.

Introduce `a`. Conclude with `cfg_lamH D τ a`.
-/
theorem Vand_lam (D : D7) (τ : D.what₂.Tau) :
    Sz.Vand ((cfgOf D τ).k + (cfgOf D τ).m - 1) (cfgOf D τ).lam = vand (lamSH D.R (D.hc τ)) := by
  have hp : (cfgOf D τ).k + (cfgOf D τ).m - 1 = 2 * D.R.rS + D.R.k + 1 := by
    show D.R.k + D.R.m - 1 = 2 * D.R.rS + D.R.k + 1
    have := m_eq D
    omega
  rw [hp]
  apply Vand_eq_vand
  intro a
  exact cfg_lamH D τ a

/- English proof (translation)
Rewrite using `[Host.v]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rdE_eq (D : D7) : D.host.rdE = 2 * D.host.v := by
  rw [Host.v]
  ring

/- English proof (translation)
Rewrite using `[Host.ka, Host.v, div_div_eq_mul_div]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ka_eq (D : D7) : D.host.ka = 2 * Real.pi / D.host.rdE := by
  rw [Host.ka, Host.v, div_div_eq_mul_div]
  ring

/- English proof (translation)
Establish `h2 : 2 ∣ m * (m - 1)` using `(Nat.even_mul_pred_self m).two_dvd`. Establish `h3 : ((m * (m - 1) / 2 : ℕ) : ℝ) = ((m * (m - 1) : ℕ) : ℝ) / ((2 : ℕ) : ℝ)` using `Nat.cast_div h2 (by norm_num)`. Rewrite using `[h3, Nat.cast_mul, Nat.cast_sub hm]`. Evaluate the numerical expressions.
-/
theorem cast_tri (m : ℕ) (hm : 1 ≤ m) : ((m * (m - 1) / 2 : ℕ) : ℝ) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
  have h2 : 2 ∣ m * (m - 1) := (Nat.even_mul_pred_self m).two_dvd
  have h3 : ((m * (m - 1) / 2 : ℕ) : ℝ) = ((m * (m - 1) : ℕ) : ℝ) / ((2 : ℕ) : ℝ) :=
    Nat.cast_div h2 (by norm_num)
  rw [h3, Nat.cast_mul, Nat.cast_sub hm]
  norm_num

/- English proof (translation)
Establish `hm : 1 ≤ D.R.m`. Use `D.R.two_le_m` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `e1 : (((D.R.m - 1) * D.R.k + D.R.m * (D.R.m - 1) / 2 : ℕ) : ℝ) = ((D.R.m : ℝ) - 1) * D.R.k + (D.R.m : ℝ) * ((D.R.m : ℝ) - 1) / 2`. Rewrite using `[Nat.cast_add, cast_tri _ hm, Nat.cast_mul, Nat.cast_sub hm, Nat.cast_one]`.

Establish `e2 : ((D.R.k * D.R.m + D.R.m * (D.R.m - 1) / 2 : ℕ) : ℝ) = (D.R.k : ℝ) * D.R.m + (D.R.m : ℝ) * ((D.R.m : ℝ) - 1) / 2`. Rewrite using `[Nat.cast_add, cast_tri _ hm, Nat.cast_mul]`. Unfold `Formalism.FourierDecayAlt.Sz.Tcrit Formalism.FourierDecayAlt.Sz.TcritPow Formalism.MainNotions.S.Tcrit`. Rewrite using `[← Real.rpow_natCast D.host.ka, e1, ← Real.rpow_natCast (gg D), e2, ← Real.rpow_neg hka]`.
-/
theorem Tcrit_eq (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (hka : 0 ≤ D.host.ka) :
    Sz.Tcrit D.R.k D.R.m D.host.ka D.host.rdE (gg D) (VV D τ) (vand (uS D u τ)) = Tcrit D u τ := by
  have hm : 1 ≤ D.R.m := by
    have := D.R.two_le_m
    omega
  have e1 : (((D.R.m - 1) * D.R.k + D.R.m * (D.R.m - 1) / 2 : ℕ) : ℝ) =
      ((D.R.m : ℝ) - 1) * D.R.k + (D.R.m : ℝ) * ((D.R.m : ℝ) - 1) / 2 := by
    rw [Nat.cast_add, cast_tri _ hm, Nat.cast_mul, Nat.cast_sub hm, Nat.cast_one]
  have e2 : ((D.R.k * D.R.m + D.R.m * (D.R.m - 1) / 2 : ℕ) : ℝ) =
      (D.R.k : ℝ) * D.R.m + (D.R.m : ℝ) * ((D.R.m : ℝ) - 1) / 2 := by
    rw [Nat.cast_add, cast_tri _ hm, Nat.cast_mul]
  unfold Formalism.FourierDecayAlt.Sz.Tcrit Formalism.FourierDecayAlt.Sz.TcritPow Formalism.MainNotions.S.Tcrit
  rw [← Real.rpow_natCast D.host.ka, e1, ← Real.rpow_natCast (gg D), e2, ← Real.rpow_neg hka]

/- English proof (translation)
Unfold `Scale.L`. Conclude with `Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le`.
-/
theorem one_le_L {D : D7} (large₂ : SizeData₂ D) : 1 ≤ large₂.sc.L := by
  unfold Scale.L
  exact Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le

/- English proof (translation)
Unfold `Scale.b`. Conclude with `Real.log_exp _`.
-/
theorem log_b {D : D7} (large₂ : SizeData₂ D) : Real.log large₂.sc.b = large₂.sc.L := by
  unfold Scale.b
  exact Real.log_exp _

/- English proof (translation)
Establish `h` using `one_le_L large₂`. Unfold `Scale.b`. Rewrite using `[← Real.exp_zero]`. Conclude with `Real.exp_lt_exp.mpr (by linarith)`.
-/
theorem one_lt_b {D : D7} (large₂ : SizeData₂ D) : 1 < large₂.sc.b := by
  have h := one_le_L large₂
  unfold Scale.b
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (by linarith)

/- English proof (translation)
Establish `h1` using `D.R.m_le_f`. Establish `h2` using `D.R.two_le_m`. Establish `h3 : 1 ≤ D.R.f`. Unfold `Ranks.f Ranks.n`. Use linear arithmetic over natural numbers and integers.

Conclude with `h3` after adjusting the coercions.
-/
theorem one_le_f (D : D7) : (1 : ℝ) ≤ D.R.f := by
  have h1 := D.R.m_le_f
  have h2 := D.R.two_le_m
  have h3 : 1 ≤ D.R.f := by
    unfold Ranks.f Ranks.n
    omega
  exact_mod_cast h3

/- English proof (translation)
Take `⟨i, rfl⟩ : ∃ i, j = i + 1` from `⟨j - 1, by omega⟩`. Establish `hi : i < D.R.m` using `by omega`. Establish `hi' : i + 1 < D.R.m` using `h2`. Rewrite using `[bOne_succ D τ i hi, bOne_succ D τ (i + 1) hi']`. Establish `g1` using `(D.hc τ).gap_be ⟨i, hi⟩`.

Establish `g2` using `(D.hc τ).gap_eb ⟨i, hi⟩ hi'`. Establish `ht : (0 : ℚ) ≤ D.R.t` using `Nat.cast_nonneg _`. Establish `h3 : ((D.hc τ).b ⟨i, hi⟩ : ℚ) + 1 ≤ (D.hc τ).b ⟨i + 1, hi'⟩` using `by linarith`. Conclude with `h3` after adjusting the coercions.
-/
theorem bOne_gap (D : D7) (τ : D.what₂.Tau) (j : ℕ) (h1 : 1 ≤ j) (h2 : j < D.R.m) :
    bOne D τ j + 1 ≤ bOne D τ (j + 1) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hi : i < D.R.m := by omega
  have hi' : i + 1 < D.R.m := h2
  rw [bOne_succ D τ i hi, bOne_succ D τ (i + 1) hi']
  have g1 := (D.hc τ).gap_be ⟨i, hi⟩
  have g2 := (D.hc τ).gap_eb ⟨i, hi⟩ hi'
  have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
  have h3 : ((D.hc τ).b ⟨i, hi⟩ : ℚ) + 1 ≤ (D.hc τ).b ⟨i + 1, hi'⟩ := by linarith
  exact_mod_cast h3

/- English proof (translation)
Establish `hk5` using `five_le_k D`. Establish `hm2` using `D.R.two_le_m`. Establish `hf` using `one_le_f D`. Establish `hL` using `one_le_L large₂`. Establish `hkR : (5 : ℝ) ≤ (D.R.k : ℝ)` using `by exact_mod_cast hk5`.

Unfold `StandingNumericalData at hD`. Unfold `StandingHypotheses at hH`. Simplify using `only at hD hH`. Take `⟨hv, -, hau, -, -, htop, -⟩` from `hD`. Take `⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hbb, -, -, -, hDel, -, -, -, -, hCl0⟩` from `hH`.

Use `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show 4 ≤ D.R.k`. Use linear arithmetic over natural numbers and integers. Use `show 2 ≤ D.R.m`. Use linear arithmetic over natural numbers and integers.

Use `show (1 : ℝ) ≤ ((D.s.Del : ℚ) : ℝ)`. Use `le_trans ?_ hDel` and prove the remaining obligations. Apply `Real.one_le_rpow _ hCl0.le` to reduce the goal to its premises. Establish `h1 : (1 : ℝ) ≤ (D.R.k : ℝ) * (D.R.f : ℝ)` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities.

Use `show 0 ≤ vOne D τ (D.R.k - 1)`. Conclude with `(hv τ (D.R.k - 1) (by omega) le_rfl).1`. Rewrite using `[cfg_v D τ 1 le_rfl (by omega)]`. Conclude with `(hv τ 1 le_rfl (by omega)).2`. Use `show 1 ≤ bOne D τ 1`.

Establish `h` using `(hbb τ 1 le_rfl (by omega)).1`. Establish `h2 : (1 : ℝ) ≤ (D.R.k : ℝ) ^ Cl` using `Real.one_le_rpow (by linarith) hCl0.le`. Conclude with `le_trans h2 (le_trans (le_max_left _ _) h)`. Introduce `j h1 h2`. Conclude with `bOne_gap D τ j h1 h2`.

Rewrite using `[cfg_v D τ 1 le_rfl (by omega)]`. Conclude with `hau D.u₀ τ`. Introduce `ht`. Rewrite `ht` using `[cfg_top_iff]`. Take `⟨h1, h2⟩` from `htop τ ht`.

Use `show bOne D τ 1 / 2 ≤ bTop D τ ∧ bTop D τ ≤ bOne D τ 1 - 3`. Conclude with `⟨h2, by linarith⟩`.
-/
theorem cfg_ok {D : D7} {large₂ : SizeData₂ D} {C0 C' Cl Cg cb Cu cT CT : ℝ} (hD : StandingNumericalData D C0)
    (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (τ : D.what₂.Tau) : (cfgOf D τ).Ok := by
  have hk5 := five_le_k D
  have hm2 := D.R.two_le_m
  have hf := one_le_f D
  have hL := one_le_L large₂
  have hkR : (5 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast hk5
  unfold StandingNumericalData at hD
  unfold StandingHypotheses at hH
  dsimp only at hD hH
  obtain ⟨hv, -, hau, -, -, htop, -⟩ := hD
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hbb, -, -, -, hDel, -, -, -, -, hCl0⟩ := hH
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show 4 ≤ D.R.k
    omega
  · show 2 ≤ D.R.m
    omega
  · show (1 : ℝ) ≤ ((D.s.Del : ℚ) : ℝ)
    refine le_trans ?_ hDel
    apply Real.one_le_rpow _ hCl0.le
    have h1 : (1 : ℝ) ≤ (D.R.k : ℝ) * (D.R.f : ℝ) := by nlinarith
    nlinarith
  · show 0 ≤ vOne D τ (D.R.k - 1)
    exact (hv τ (D.R.k - 1) (by omega) le_rfl).1
  · rw [cfg_v D τ 1 le_rfl (by omega)]
    exact (hv τ 1 le_rfl (by omega)).2
  · show 1 ≤ bOne D τ 1
    have h := (hbb τ 1 le_rfl (by omega)).1
    have h2 : (1 : ℝ) ≤ (D.R.k : ℝ) ^ Cl := Real.one_le_rpow (by linarith) hCl0.le
    exact le_trans h2 (le_trans (le_max_left _ _) h)
  · intro j h1 h2
    exact bOne_gap D τ j h1 h2
  · rw [cfg_v D τ 1 le_rfl (by omega)]
    exact hau D.u₀ τ
  · intro ht
    rw [cfg_top_iff] at ht
    obtain ⟨h1, h2⟩ := htop τ ht
    show bOne D τ 1 / 2 ≤ bTop D τ ∧ bTop D τ ≤ bOne D τ 1 - 3
    exact ⟨h2, by linarith⟩

/- English proof (translation)
Establish `hk5` using `five_le_k D`. Establish `hm2` using `D.R.two_le_m`. Establish `hL` using `one_le_L large₂`. Establish `hkR : (5 : ℝ) ≤ (D.R.k : ℝ)` using `by exact_mod_cast hk5`. Establish `hmR : (2 : ℝ) ≤ (D.R.m : ℝ)` using `by exact_mod_cast hm2`.

Establish `hDel0 : (0 : ℝ) < ((D.s.Del : ℚ) : ℝ)` using `by exact_mod_cast D.s.Del_pos`. Unfold `StandingHypotheses at hH`. Simplify using `only at hH`. Take `⟨-, -, -, -, -, -, h7, h8, -, -, -, -, -, -, -, hbb, -, -, -, -, -, -, -, -, hCl0⟩` from `hH`. Establish `hb1 : 1 ≤ bOne D τ 1`.

Establish `h` using `(hbb τ 1 le_rfl (by omega)).1`. Establish `h2 : (1 : ℝ) ≤ (D.R.k : ℝ) ^ Cl` using `Real.one_le_rpow (by linarith) hCl0.le`. Conclude with `le_trans h2 (le_trans (le_max_left _ _) h)`. Use `⟨(one_lt_b large₂).le, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show 4 * (D.R.m : ℝ) * (D.R.k : ℝ) * ((D.s.Del : ℚ) : ℝ) / bOne D τ 1 ≤ 1 / 10`.

Rewrite using `[div_le_iff₀ (by linarith)]`. Establish `h` using `h8 τ 1 le_rfl (by omega)`. Establish `hmkD : (0 : ℝ) ≤ (D.R.m : ℝ) * (D.R.k : ℝ) * ((D.s.Del : ℚ) : ℝ)` using `mul_nonneg (mul_nonneg (by linarith) (by linarith)) hDel0.le`. Establish `p` using `mul_le_mul_of_nonneg_right h40 hmkD`. Use the polynomial consequences of the given equalities and inequalities.

Introduce `j h1 h2`. Establish `h` using `(hbb τ j h1 h2).2`. Rewrite `h` using `[Real.rpow_two]`. Conclude with `h`. Use `show 2 * (D.R.m : ℝ) * Real.log large₂.sc.b / (D.R.k : ℝ) ≤ 1 / 10`.

Rewrite using `[log_b, div_le_iff₀ (by linarith)]`. Establish `hmL : (0 : ℝ) ≤ (D.R.m : ℝ) ^ 2 * large₂.sc.L` using `by positivity`. Establish `hmL' : (0 : ℝ) ≤ (D.R.m : ℝ) * large₂.sc.L` using `by positivity`. Establish `p1` using `mul_le_mul_of_nonneg_right h40 hmL`. Establish `p2 : (D.R.m : ℝ) * large₂.sc.L ≤ (D.R.m : ℝ) ^ 2 * large₂.sc.L`.

Use polynomial arithmetic with `[mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ (D.R.m : ℝ) - 1) (by linarith : (0 : ℝ) ≤ (D.R.m : ℝ))) (by linarith : (0 : ℝ) ≤ large₂.sc.L)]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem cfg_small {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ}
    (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (h40 : 40 ≤ Cl) (τ : D.what₂.Tau) : (cfgOf D τ).Small large₂.sc.b := by
  have hk5 := five_le_k D
  have hm2 := D.R.two_le_m
  have hL := one_le_L large₂
  have hkR : (5 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast hk5
  have hmR : (2 : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast hm2
  have hDel0 : (0 : ℝ) < ((D.s.Del : ℚ) : ℝ) := by exact_mod_cast D.s.Del_pos
  unfold StandingHypotheses at hH
  dsimp only at hH
  obtain ⟨-, -, -, -, -, -, h7, h8, -, -, -, -, -, -, -, hbb, -, -, -, -, -, -, -, -, hCl0⟩ := hH
  have hb1 : 1 ≤ bOne D τ 1 := by
    have h := (hbb τ 1 le_rfl (by omega)).1
    have h2 : (1 : ℝ) ≤ (D.R.k : ℝ) ^ Cl := Real.one_le_rpow (by linarith) hCl0.le
    exact le_trans h2 (le_trans (le_max_left _ _) h)
  refine ⟨(one_lt_b large₂).le, ?_, ?_, ?_⟩
  · show 4 * (D.R.m : ℝ) * (D.R.k : ℝ) * ((D.s.Del : ℚ) : ℝ) / bOne D τ 1 ≤ 1 / 10
    rw [div_le_iff₀ (by linarith)]
    have h := h8 τ 1 le_rfl (by omega)
    have hmkD : (0 : ℝ) ≤ (D.R.m : ℝ) * (D.R.k : ℝ) * ((D.s.Del : ℚ) : ℝ) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) hDel0.le
    have p := mul_le_mul_of_nonneg_right h40 hmkD
    nlinarith
  · intro j h1 h2
    have h := (hbb τ j h1 h2).2
    rw [Real.rpow_two] at h
    exact h
  · show 2 * (D.R.m : ℝ) * Real.log large₂.sc.b / (D.R.k : ℝ) ≤ 1 / 10
    rw [log_b, div_le_iff₀ (by linarith)]
    have hmL : (0 : ℝ) ≤ (D.R.m : ℝ) ^ 2 * large₂.sc.L := by positivity
    have hmL' : (0 : ℝ) ≤ (D.R.m : ℝ) * large₂.sc.L := by positivity
    have p1 := mul_le_mul_of_nonneg_right h40 hmL
    have p2 : (D.R.m : ℝ) * large₂.sc.L ≤ (D.R.m : ℝ) ^ 2 * large₂.sc.L := by
      nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ (D.R.m : ℝ) - 1)
        (by linarith : (0 : ℝ) ≤ (D.R.m : ℝ))) (by linarith : (0 : ℝ) ≤ large₂.sc.L)]
    nlinarith

end Formalism.MainNotions.BridgeLemma

end
