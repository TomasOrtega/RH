import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHoldsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightEntriesSignsSizes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightGapsBlockAndBar

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FactorDepth GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.MeanTop

namespace GlobalTheory.RefSum.DivWt

section Free

variable {ι : Type} [Fintype ι] {N : ℕ} (W : Wts ι N) (h : W.Hyp) (hd : W.IsDiv)
include h hd

omit [Fintype ι] in

/- English proof (translation)
Introduce `a b hab` and use `by have hab' : (a : ℕ) ≤ b := hab have := (W.div_gap_sum h hd τ (b - a) a b (by omega)).1 linarith`.
-/
theorem antitone (τ : ι) : Antitone (W.u1 τ) := fun a b hab => by
  have hab' : (a : ℕ) ≤ b := hab
  have := (W.div_gap_sum h hd τ (b - a) a b (by omega)).1
  linarith

/- English proof (translation)
Establish `h1` using `(divided_entries ι N W h hd τ a).1`. Establish `h2 : ((W.T : ℝ) + W.Dd + 1) * |(W.u1 τ a : ℝ)| ≤ |(W.u τ a : ℝ)| + W.c0 + 4 * N` using `by exact_mod_cast h1`. Establish `h3` using `h.h5 τ a`. Establish `h4 : 0 ≤ ((W.Dd : ℝ) + 1) * |(W.u1 τ a : ℝ)|` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem mul_abs_le (τ : ι) (a : Fin N) : (W.T : ℝ) * |(W.u1 τ a : ℝ)| ≤ 2 * W.b := by
  have h1 := (divided_entries ι N W h hd τ a).1
  have h2 : ((W.T : ℝ) + W.Dd + 1) * |(W.u1 τ a : ℝ)| ≤ |(W.u τ a : ℝ)| + W.c0 + 4 * N := by exact_mod_cast h1
  have h3 := h.h5 τ a
  have h4 : 0 ≤ ((W.Dd : ℝ) + 1) * |(W.u1 τ a : ℝ)| := by positivity
  linarith

omit [Fintype ι] in

/- English proof (translation)
Establish `hk` using `h.kc_lt`. Establish `hp` using `h.p_lt`. Set `c : Fin N` to `⟨W.kc - 1, by omega⟩`. Establish `hc : (c : ℕ) + 1 = W.kc` using `by simp only [c]; omega`. Take `⟨h1, h2⟩` from `W.div_gap_sum h hd τ (c - a) a c (by omega)`.

Establish `h3 : (((c : ℕ) - a : ℕ) : ℤ) ≤ N` using `by omega`. Rewrite `h1`, `h2` using `[(hd τ).1 c hc, sub_zero]`. Rewrite `h2` using `[h.anchor τ c hc]`. Establish `h4 : 0 ≤ ((W.Dd : ℤ) + 1) * W.u1 τ a` using `by positivity`. Establish `h5 : (W.T : ℤ) * W.u1 τ a ≤ W.u τ a + 2 * N` using `by linarith`.

Establish `h6 : (W.T : ℝ) * (W.u1 τ a : ℝ) ≤ (W.u τ a : ℝ) + 2 * N` using `by exact_mod_cast h5`. Combine the linear relations using `[(h.h3cloud τ a ha).2]`.
-/
theorem mul_cloud_le (τ : ι) (a : Fin N) (ha : (a : ℕ) < W.kc) : (W.T : ℝ) * (W.u1 τ a : ℝ) ≤ W.S + 2 * N := by
  have hk := h.kc_lt
  have hp := h.p_lt
  let c : Fin N := ⟨W.kc - 1, by omega⟩
  have hc : (c : ℕ) + 1 = W.kc := by simp only [c]; omega
  obtain ⟨h1, h2⟩ := W.div_gap_sum h hd τ (c - a) a c (by omega)
  have h3 : (((c : ℕ) - a : ℕ) : ℤ) ≤ N := by omega
  rw [(hd τ).1 c hc, sub_zero] at h1 h2
  rw [h.anchor τ c hc] at h2
  have h4 : 0 ≤ ((W.Dd : ℤ) + 1) * W.u1 τ a := by positivity
  have h5 : (W.T : ℤ) * W.u1 τ a ≤ W.u τ a + 2 * N := by linarith
  have h6 : (W.T : ℝ) * (W.u1 τ a : ℝ) ≤ (W.u τ a : ℝ) + 2 * N := by exact_mod_cast h5
  linarith [(h.h3cloud τ a ha).2]

end Free

/- English proof (translation)
Establish `h1 : ∑ f : Lt1 Dw, 2 * rk f ≤ Fintype.card (Lt1 Dw) * (2 * (Dw.p + Dw.q))`. Rewrite using `[← Finset.card_univ, ← smul_eq_mul]`. Use `Finset.sum_le_card_nsmul _ _ _ fun f _ => ?_` and prove the remaining obligations. Establish `h` using `rk_le f`. Apply the tactic sequence `have : Dw.mult f.1 ≤ Dw.p + Dw.q := by rw [Datum.mult]; split_ifs <;> omega`.

Use linear arithmetic over natural numbers and integers. Establish `h2` using `Nat.mul_le_mul_right (2 * (Dw.p + Dw.q) + 8) (card_Lt1_le_finrank_mul (Dw := Dw))`. Rewrite `h2` using `[mul_add (Fintype.card (Lt1 Dw))]`. Unfold `nCol`. Use linear arithmetic over natural numbers and integers.
-/
theorem nCol_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) :
    nCol Dw ≤ Module.finrank ℚ E * (Dw.p + Dw.q) * (2 * (Dw.p + Dw.q) + 8) + 8 := by
  have h1 : ∑ f : Lt1 Dw, 2 * rk f ≤ Fintype.card (Lt1 Dw) * (2 * (Dw.p + Dw.q)) := by
    rw [← Finset.card_univ, ← smul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun f _ => ?_
    have h := rk_le f
    have : Dw.mult f.1 ≤ Dw.p + Dw.q := by rw [Datum.mult]; split_ifs <;> omega
    omega
  have h2 := Nat.mul_le_mul_right (2 * (Dw.p + Dw.q) + 8) (card_Lt1_le_finrank_mul (Dw := Dw))
  rw [mul_add (Fintype.card (Lt1 Dw))] at h2
  unfold nCol
  omega

/- English proof (translation)
Establish `a : PP * X ≤ 2 * g` using `le_of_mul_le_mul_right (by linarith) hT`. Establish `b1 : 1 ≤ f * r` using `one_le_mul_of_one_le_of_one_le hf hr`. Establish `b2 : f * r ≤ f * r ^ 2` using `by nlinarith`. Establish `c : PP * 60 ≤ PP * X` using `mul_le_mul_of_nonneg_left hX (by linarith)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem gap_num {PP T X h g f r : ℝ} (hT : 0 < T) (hX : 60 ≤ X) (hf : 1 ≤ f) (hr : 1 ≤ r) (hP : f * r ^ 2 ≤ PP)
    (h1 : PP * X * T ≤ h) (h2 : h ≤ 2 * T * g) : 2 * f * r * (2 * r + 8) + 8 + 1 ≤ g := by
  have a : PP * X ≤ 2 * g := le_of_mul_le_mul_right (by linarith) hT
  have b1 : 1 ≤ f * r := one_le_mul_of_one_le_of_one_le hf hr
  have b2 : f * r ≤ f * r ^ 2 := by nlinarith
  have c : PP * 60 ≤ PP * X := mul_le_mul_of_nonneg_left hX (by linarith)
  nlinarith

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

/- English proof (translation)
Take `⟨h0, S, eta, hS, he, hSe, -, hh0, hH⟩` from `h.hyp hi`. Establish `H` using `hH u1`. Establish `hd` using `(quo_iff p i PP h0 S eta u1).1 hq`. Take `⟨hp, hq', hr⟩` from `h.sig`. Establish `hm` using `D.R.two_le_m`.

Establish `hk` using `D.R.m_add_three_le_k`. Establish `hrr : D.R.r = D.R.k + D.R.m - 1` using `rfl`. Establish `hf : 2 ≤ D.R.f` using `D.R.two_le_m.trans D.R.m_le_f`. Simplify using `only [Ranks.sigW] at hp hq'`. Establish `hT1 : 4 * GlobalTheory.CompHt.dimFlag (dat p i) + 4 ≤ lenT p i PP` using `H.h1`.

Establish `hD : 1 ≤ GlobalTheory.CompHt.dimFlag (dat p i)`. Rewrite using `[h.dim]; exact Nat.mul_pos (by omega) (Nat.choose_pos (by omega))`. Take `⟨τ0⟩ : Nonempty (Psi p.T.Q.H)` from `(Nat.card_pos_iff.1 (by rw [h.card]; omega)).1`. Establish `han : (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ0 : ℝ) ≤ 4 * L.sc.b`. Unfold `anchor`.

Rewrite using `[dif_pos (by omega)]`. Conclude with `(le_abs_self _).trans (h.up τ0 _)`. Establish `hlow` using `h.low τ0`. Establish `hw : 4 * ((eta + S + (((dat p i).p + (dat p i).q : ℕ) : ℝ)) + S + ((cZero D ((i : ℕ) + 1) : ℤ) : ℝ) + 2 * (((dat p i).p + (dat p i).q : ℕ) : ℝ)) + 20 * (((dat p i).p + (dat p i).q : ℕ) : ℝ) * (lenT p i PP : ℝ) ≤ (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ0 : ℝ)` using `H.h3w τ0`. Establish `hc0 : (0 : ℝ) ≤ ((cZero D ((i : ℕ) + 1) : ℤ) : ℝ)` using `by exact_mod_cast (cZero_spec D _).2.1`.

Establish `hrows` using `h.what₂.1`. Establish `e1 : ∀ τ a, (lenT p i PP : ℝ) * |(u1 τ a : ℝ)| ≤ 2 * (4 * L.sc.b)` using `mul_abs_le _ H hd`. Establish `e2 : ∀ τ (a : Fin ((dat p i).p + (dat p i).q)), (a : ℕ) < D.R.k - 1 → (lenT p i PP : ℝ) * (u1 τ a : ℝ) ≤ S + 2 * (((dat p i).p + (dat p i).q : ℕ) : ℝ)` using `mul_cloud_le _ H hd`. Establish `e3 : ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (b : ℕ) = a + 1 → (b : ℕ) = (dat p i).p → h0 ≤ 2 * (lenT p i PP : ℤ) * (u1 τ a - u1 τ b)` using `fun τ a b hab hb => ((divided_gaps _ _ _ H hd τ a b hab).2.1 hb).1`. Establish `e4 : ∀ τ, Antitone (u1 τ)` using `antitone _ H hd`.

Establish `e5 : ∀ τ (a : Fin ((dat p i).p + (dat p i).q)), (a : ℕ) + 1 = D.R.k - 1 → u1 τ a = 0` using `fun τ => (hd τ).1`. Establish `hn` using `nCol_le (dat p i)`. Rewrite `hn` using `[GlobalTheory.PinNum.finrank_host D, hr]`. Rewrite `hw` using `[hr]`. Simplify using `only [hr] at e2`.

Unfold `WtAt`. Use `clear H hd hH hq h`. Establish `hT : (1 : ℝ) ≤ lenT p i PP` using `by exact_mod_cast (by omega : 1 ≤ lenT p i PP)`. Establish `hT' : 1 ≤ lenT p i PP` using `by omega`. Generalize the expression as in `lenT p i PP = T at *`.

Generalize the expression as in `(anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ0 : ℝ) = w at *`. Generalize the expression as in `((cZero D ((i : ℕ) + 1) : ℤ) : ℝ) = c at *`. Establish `hf' : (2 : ℝ) ≤ D.R.f` using `by exact_mod_cast hf`. Establish `hm' : (2 : ℝ) ≤ D.R.m` using `by exact_mod_cast hm`. Establish `hk' : (5 : ℝ) ≤ D.R.k` using `by exact_mod_cast (by omega : 5 ≤ D.R.k)`.

Establish `hr' : (D.R.k : ℝ) ≤ D.R.r` using `by exact_mod_cast (by omega : D.R.k ≤ D.R.r)`. Establish `hD' : (1 : ℝ) ≤ GlobalTheory.CompHt.dimFlag (dat p i)` using `by exact_mod_cast hD`. Establish `hkP : (D.R.k : ℝ) ≤ PP` using `by nlinarith`. Establish `hTb : (T : ℝ) ≤ 4 * L.sc.b` using `by nlinarith`. Establish `hb : 0 ≤ L.sc.b` using `by linarith`.

Use `⟨⟨by omega, by omega, by omega, by omega, by omega, GlobalTheory.PinNum.finrank_host D⟩, by omega, ⌊8 * L.sc.b / T⌋₊, D.R.k * (S + 2 * D.R.r) / T, ⟨e4, fun τ a ha => e5 τ a (by omega), fun τ a b ha hb' => ?_, fun τ a => ?_, fun τ => ?_⟩, ?_, ?_, hT'⟩` and prove the remaining obligations. Establish `g1 : (h0 : ℝ) ≤ 2 * (T : ℝ) * ((u1 τ a - u1 τ b : ℤ) : ℝ)` using `by exact_mod_cast e3 τ a b (by omega) hb'`. Establish `hX : (60 : ℝ) ≤ D.R.r * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * GlobalTheory.CompHt.dimFlag (dat p i)`. Combine the equalities or inequalities in the displayed calculation. Establish `g2` using `gap_num (by linarith) hX (by linarith) (by linarith) hP (le_of_eq_of_le (by ring) hh0) g1`.

Establish `g3 : ((nCol (dat p i) : ℕ) : ℝ) ≤ 2 * D.R.f * D.R.r * (2 * D.R.r + 8) + 8` using `by exact_mod_cast hn`. Establish `g4 : ((nCol (dat p i) : ℕ) : ℝ) + 1 ≤ ((u1 τ a - u1 τ b : ℤ) : ℝ)` using `by linarith`. Conclude with `g4` after adjusting the coercions. Establish `g1 : ((|u1 τ a|.toNat : ℕ) : ℝ) = |(u1 τ a : ℝ)|`. Rewrite using `[← Int.cast_natCast, Int.toNat_of_nonneg (abs_nonneg _), Int.cast_abs]`.

Establish `g2 : |u1 τ a|.toNat ≤ ⌊8 * L.sc.b / T⌋₊`. Use `Nat.le_floor ?_` and prove the remaining obligations. Rewrite using `[g1, le_div_iff₀ (by linarith)]`. Combine the linear relations using `[e1 τ a]`. Conclude with `Int.toNat_le.1 g2`.

Rewrite using `[le_div_iff₀ (by linarith), Finset.sum_mul]`. Use `(Finset.sum_le_card_nsmul _ _ (S + 2 * D.R.r) fun a ha => ?_).trans ?_` and prove the remaining obligations. Use `(Finset.mem_filter.1 ha).2` as an intermediate fact. Combine the linear relations using `[e2 τ a (by omega)]`. Rewrite using `[nsmul_eq_mul]`.

Use `mul_le_mul_of_nonneg_right ?_ (by positivity)` and prove the remaining obligations. Establish `: (Finset.univ.filter (fun a : Fin ((dat p i).p + (dat p i).q) => (a : ℕ) + 2 < D.R.k)).card ≤ (Finset.range D.R.k).card` using `Finset.card_le_card_of_injOn (fun a => (a : ℕ)) (fun a ha => by have := (Finset.mem_filter.1 ha).2; simp only [Finset.coe_range, Set.mem_Iio]; omega) (fun a _ b _ e => Fin.ext e)`. Rewrite `this` using `[Finset.card_range]`. Conclude with `this` after adjusting the coercions. Establish `g1 : ((⌊8 * L.sc.b / T⌋₊ : ℕ) : ℝ) ≤ 8 * L.sc.b / T` using `Nat.floor_le (by positivity)`.

Rewrite `g1` using `[le_div_iff₀ (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[mul_div_cancel₀ _ (by linarith)]`. Establish `g1 : (D.R.k : ℝ) * S ≤ PP * (S + eta)` using `mul_le_mul hkP (by linarith) hS (by linarith)`. Establish `g2 : (D.R.r : ℝ) * D.R.k ≤ L.sc.b`.

Use `le_trans ?_ hrows` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem wtAt_of_wtNum {PP : ℝ} (h : WtNum p i PP) (hP : (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 ≤ PP) (hi : (i : ℕ) + 1 < D.R.m)
    (u1 : GlobalTheory.AllWt.Weight (dat p i)) (hq : Quo p i PP u1) : WtAt p i PP 802 u1 := by
  obtain ⟨h0, S, eta, hS, he, hSe, -, hh0, hH⟩ := h.hyp hi
  have H := hH u1
  have hd := (quo_iff p i PP h0 S eta u1).1 hq
  obtain ⟨hp, hq', hr⟩ := h.sig
  have hm := D.R.two_le_m
  have hk := D.R.m_add_three_le_k
  have hrr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hf : 2 ≤ D.R.f := D.R.two_le_m.trans D.R.m_le_f
  simp only [Ranks.sigW] at hp hq'
  have hT1 : 4 * GlobalTheory.CompHt.dimFlag (dat p i) + 4 ≤ lenT p i PP := H.h1
  have hD : 1 ≤ GlobalTheory.CompHt.dimFlag (dat p i) := by
    rw [h.dim]; exact Nat.mul_pos (by omega) (Nat.choose_pos (by omega))
  obtain ⟨τ0⟩ : Nonempty (Psi p.T.Q.H) := (Nat.card_pos_iff.1 (by rw [h.card]; omega)).1
  have han : (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ0 : ℝ) ≤ 4 * L.sc.b := by
    unfold anchor
    rw [dif_pos (by omega)]
    exact (le_abs_self _).trans (h.up τ0 _)
  have hlow := h.low τ0
  have hw : 4 * ((eta + S + (((dat p i).p + (dat p i).q : ℕ) : ℝ)) + S + ((cZero D ((i : ℕ) + 1) : ℤ) : ℝ) +
      2 * (((dat p i).p + (dat p i).q : ℕ) : ℝ)) + 20 * (((dat p i).p + (dat p i).q : ℕ) : ℝ) * (lenT p i PP : ℝ) ≤
      (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ0 : ℝ) := H.h3w τ0
  have hc0 : (0 : ℝ) ≤ ((cZero D ((i : ℕ) + 1) : ℤ) : ℝ) := by exact_mod_cast (cZero_spec D _).2.1
  have hrows := h.what₂.1
  have e1 : ∀ τ a, (lenT p i PP : ℝ) * |(u1 τ a : ℝ)| ≤ 2 * (4 * L.sc.b) := mul_abs_le _ H hd
  have e2 : ∀ τ (a : Fin ((dat p i).p + (dat p i).q)), (a : ℕ) < D.R.k - 1 →
      (lenT p i PP : ℝ) * (u1 τ a : ℝ) ≤ S + 2 * (((dat p i).p + (dat p i).q : ℕ) : ℝ) := mul_cloud_le _ H hd
  have e3 : ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (b : ℕ) = a + 1 → (b : ℕ) = (dat p i).p →
      h0 ≤ 2 * (lenT p i PP : ℤ) * (u1 τ a - u1 τ b) := fun τ a b hab hb =>
    ((divided_gaps _ _ _ H hd τ a b hab).2.1 hb).1
  have e4 : ∀ τ, Antitone (u1 τ) := antitone _ H hd
  have e5 : ∀ τ (a : Fin ((dat p i).p + (dat p i).q)), (a : ℕ) + 1 = D.R.k - 1 → u1 τ a = 0 := fun τ => (hd τ).1
  have hn := nCol_le (dat p i)
  rw [GlobalTheory.PinNum.finrank_host D, hr] at hn
  rw [hr] at hw
  simp only [hr] at e2
  unfold WtAt
  clear H hd hH hq h
  have hT : (1 : ℝ) ≤ lenT p i PP := by exact_mod_cast (by omega : 1 ≤ lenT p i PP)
  have hT' : 1 ≤ lenT p i PP := by omega
  generalize lenT p i PP = T at *
  generalize (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ0 : ℝ) = w at *
  generalize ((cZero D ((i : ℕ) + 1) : ℤ) : ℝ) = c at *
  have hf' : (2 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hm' : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 5 ≤ D.R.k)
  have hr' : (D.R.k : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : D.R.k ≤ D.R.r)
  have hD' : (1 : ℝ) ≤ GlobalTheory.CompHt.dimFlag (dat p i) := by exact_mod_cast hD
  have hkP : (D.R.k : ℝ) ≤ PP := by nlinarith
  have hTb : (T : ℝ) ≤ 4 * L.sc.b := by nlinarith
  have hb : 0 ≤ L.sc.b := by linarith
  refine ⟨⟨by omega, by omega, by omega, by omega, by omega, GlobalTheory.PinNum.finrank_host D⟩, by omega,
    ⌊8 * L.sc.b / T⌋₊, D.R.k * (S + 2 * D.R.r) / T, ⟨e4, fun τ a ha => e5 τ a (by omega), fun τ a b ha hb' => ?_,
      fun τ a => ?_, fun τ => ?_⟩, ?_, ?_, hT'⟩
  · have g1 : (h0 : ℝ) ≤ 2 * (T : ℝ) * ((u1 τ a - u1 τ b : ℤ) : ℝ) := by exact_mod_cast e3 τ a b (by omega) hb'
    have hX : (60 : ℝ) ≤ D.R.r * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * GlobalTheory.CompHt.dimFlag (dat p i) := by
      calc (60 : ℝ) ≤ 5 * 2 ^ 2 * 2 ^ 2 * 5 * 1 := by norm_num
        _ ≤ _ := by gcongr; linarith
    have g2 := gap_num (by linarith) hX (by linarith) (by linarith) hP (le_of_eq_of_le (by ring) hh0) g1
    have g3 : ((nCol (dat p i) : ℕ) : ℝ) ≤ 2 * D.R.f * D.R.r * (2 * D.R.r + 8) + 8 := by exact_mod_cast hn
    have g4 : ((nCol (dat p i) : ℕ) : ℝ) + 1 ≤ ((u1 τ a - u1 τ b : ℤ) : ℝ) := by linarith
    exact_mod_cast g4
  · have g1 : ((|u1 τ a|.toNat : ℕ) : ℝ) = |(u1 τ a : ℝ)| := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (abs_nonneg _), Int.cast_abs]
    have g2 : |u1 τ a|.toNat ≤ ⌊8 * L.sc.b / T⌋₊ := by
      refine Nat.le_floor ?_
      rw [g1, le_div_iff₀ (by linarith)]
      linarith [e1 τ a]
    exact Int.toNat_le.1 g2
  · rw [le_div_iff₀ (by linarith), Finset.sum_mul]
    refine (Finset.sum_le_card_nsmul _ _ (S + 2 * D.R.r) fun a ha => ?_).trans ?_
    · have := (Finset.mem_filter.1 ha).2
      linarith [e2 τ a (by omega)]
    · rw [nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have : (Finset.univ.filter (fun a : Fin ((dat p i).p + (dat p i).q) => (a : ℕ) + 2 < D.R.k)).card ≤
          (Finset.range D.R.k).card :=
        Finset.card_le_card_of_injOn (fun a => (a : ℕ))
          (fun a ha => by have := (Finset.mem_filter.1 ha).2; simp only [Finset.coe_range, Set.mem_Iio]; omega)
          (fun a _ b _ e => Fin.ext e)
      rw [Finset.card_range] at this
      exact_mod_cast this
  · have g1 : ((⌊8 * L.sc.b / T⌋₊ : ℕ) : ℝ) ≤ 8 * L.sc.b / T := Nat.floor_le (by positivity)
    rw [le_div_iff₀ (by linarith)] at g1
    linarith
  · rw [mul_div_cancel₀ _ (by linarith)]
    have g1 : (D.R.k : ℝ) * S ≤ PP * (S + eta) := mul_le_mul hkP (by linarith) hS (by linarith)
    have g2 : (D.R.r : ℝ) * D.R.k ≤ L.sc.b := by
      refine le_trans ?_ hrows
      calc (D.R.r : ℝ) * D.R.k = 1 ^ 2 * D.R.r * 1 * D.R.k * 1 ^ 3 := by ring
        _ ≤ _ := by gcongr <;> linarith
    linarith

/- English proof (translation)
Establish `h1 : D.R.f * D.R.r ^ 2 ≤ T.nWn` using `le_trans (by nlinarith [Nat.zero_le (D.R.f * D.R.r)]) T.nW_lo.1`. Conclude with `le_trans (by exact_mod_cast h1) T.nW_le`.
-/
theorem le_PP {P : ParameterChoice' D L} (T : ParamsT D L P) : (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 ≤ T.PP := by
  have h1 : D.R.f * D.R.r ^ 2 ≤ T.nWn := le_trans (by nlinarith [Nat.zero_le (D.R.f * D.R.r)]) T.nW_lo.1
  exact le_trans (by exact_mod_cast h1) T.nW_le

/- English proof (translation)
The claim follows from `Closed.imp h fun Fm _ _ ⟨_, _, a, h⟩ => ⟨802, by norm_num, a, fun x hx hle ι p hp i hi u1 hq => wtAt_of_wtNum p i (h x hx hle ι p hp i) (le_PP (Fm.parT x hx ι)) hi u1 hq⟩`.
-/
theorem wtPt_of_wtN (h : WtN) : WtPt :=
  Closed.imp h fun Fm _ _ ⟨_, _, a, h⟩ => ⟨802, by norm_num, a, fun x hx hle ι p hp i hi u1 hq =>
    wtAt_of_wtNum p i (h x hx hle ι p hp i) (le_PP (Fm.parT x hx ι)) hi u1 hq⟩

/- English proof (translation)
Introduce `_` and use `wtPt_of_wtN GlobalTheory.T.weight_bound_holds`.
-/
theorem wtPt_of_size : Size → WtPt := fun _ => wtPt_of_wtN GlobalTheory.T.weight_bound_holds

end GlobalTheory.RefSum.DivWt

end
