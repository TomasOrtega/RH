import Formalism.GaussJetBounds.OneLetterGaussJets.StatementN
import Formalism.IncomingBounds.WeightIdentities

noncomputable section
open scoped BigOperators

universe u v w

namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds

open Formalism.IncomingBounds

/- English proof (translation)
Unfold `gam`. Establish `hl' : (3:ℝ) ≤ l` using `by exact_mod_cast hl`. Apply `div_nonneg (by linarith)` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma gamma_nonneg {l : ℕ} (hl : 3 ≤ l) : 0 ≤ gam l := by
  unfold gam
  have hl' : (3:ℝ) ≤ l := by exact_mod_cast hl
  apply div_nonneg (by linarith)
  nlinarith

/- English proof (translation)
Unfold `gam`. Establish `hl' : (3:ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `h1 : (0:ℝ) < l` using `by linarith`. Establish `h2 : (0:ℝ) < (l:ℝ) ^ 2 - 1` using `by nlinarith`. Use `first`.

Consider the case `(rw [div_le_div_iff₀ h1 h2]; nlinarith)`. Consider the case `(rw [div_le_div_iff h1 h2]; nlinarith)`.
-/
lemma inv_le_gamma {l : ℕ} (hl : 3 ≤ l) : 1 / (l : ℝ) ≤ gam l := by
  unfold gam
  have hl' : (3:ℝ) ≤ l := by exact_mod_cast hl
  have h1 : (0:ℝ) < l := by linarith
  have h2 : (0:ℝ) < (l:ℝ) ^ 2 - 1 := by nlinarith
  first
  | (rw [div_le_div_iff₀ h1 h2]; nlinarith)
  | (rw [div_le_div_iff h1 h2]; nlinarith)

/- English proof (translation)
Unfold `gam`. Establish `hl' : (3:ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `h1 : (0:ℝ) < l` using `by linarith`. Establish `h2 : (0:ℝ) < (l:ℝ) ^ 2 - 1` using `by nlinarith`. Rewrite using `[mul_div_assoc']`.

Use `first`. Consider the case `(rw [div_le_div_iff₀ h2 h1]; nlinarith)`. Consider the case `(rw [div_le_div_iff h2 h1]; nlinarith)`.
-/
lemma two_gamma_le_three_div {l : ℕ} (hl : 3 ≤ l) : 2 * gam l ≤ 3 / (l : ℝ) := by
  unfold gam
  have hl' : (3:ℝ) ≤ l := by exact_mod_cast hl
  have h1 : (0:ℝ) < l := by linarith
  have h2 : (0:ℝ) < (l:ℝ) ^ 2 - 1 := by nlinarith
  rw [mul_div_assoc']
  first
  | (rw [div_le_div_iff₀ h2 h1]; nlinarith)
  | (rw [div_le_div_iff h2 h1]; nlinarith)

/- English proof (translation)
Introduce `l d inst hl hd hev TT k D w E hk hw hE hoff hon`. Establish `hA` using `lemmaFa`. Establish `hc` using `lemmaFc`. Establish `hI` using `incomingBound`. Establish `hl3 : (3:ℝ) ≤ l` using `by exact_mod_cast hl`.

Establish `hl0 : (0:ℝ) < l` using `by linarith`. Establish `hk3 : (3:ℝ) ≤ k` using `by exact_mod_cast hk`. Establish `hg` using `gamma_nonneg hl`. Take `⟨S, hS⟩ : ∃ S : ℝ, S = ∑ s : ZMod d, w s` from `⟨_, rfl⟩`. Take `⟨T, hT⟩ : ∃ T : ℝ, T = ∑ s ∈ TT, w s` from `⟨_, rfl⟩`.

Establish `hS0 : 0 ≤ S` using `by rw [hS]; exact Finset.sum_nonneg (fun s _ => (hw s).le)`. Establish `hTS : T ≤ S`. Rewrite using `[hS, hT]`. Conclude with `Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun s _ _ => (hw s).le)`. Take `⟨Ws, hWs⟩ : ∃ f : ZMod d → ℝ, f = fun s => ((k:ℝ) - 1) * w s` from `⟨_, rfl⟩`.

Take `⟨E', hE'⟩ : ∃ f : ZMod d → ℝ, f = fun s => if s ∈ TT then 2 * w s else 0` from `⟨_, rfl⟩`. Establish `hWsapp : ∀ s, Ws s = ((k:ℝ) - 1) * w s` using `fun s => by rw [hWs]`. Rewrite using `[← hS, ← hT, ← hWs]`. Establish `hD0 : 0 ≤ D` using `fun s => by show (0:ℝ) ≤ D s`. Establish `h1` using `hw s`.

Establish `h2` using `(hE s).1`. Distinguish the cases in `hs : s ∈ TT`. Rewrite using `[hon s hs]`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[hoff s hs]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hE'0 : 0 ≤ E'` using `fun s => by show (0:ℝ) ≤ E' s`. Rewrite using `[hE']`. Apply the tactic sequence `try dsimp only`. Use `split_ifs`.

Combine the linear relations using `[hw s]`. Conclude with `le_rfl`. Establish `hDE : D + E' = Ws + E`. Use function extensionality and compare the values at `s`. Simplify using `only [Pi.add_apply, hE', hWs]`.

Distinguish the cases in `hs : s ∈ TT`. Rewrite using `[if_pos hs, hon s hs]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hs, hoff s hs]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨⟨sD, hsD, -, hFsD⟩, -⟩` from `hA l d hl hd hev D hD0`. Establish `h2` using `(hc l d hl hd hev D E' sD hD0 hE'0 ⟨hsD, hFsD⟩).2`. Rewrite `h2` using `[hDE]`. Establish `hE'sum : ∑ s, E' s = 2 * T`. Rewrite using `[hT, Finset.mul_sum, hE', ← Finset.sum_filter]`.

Simplify using the standard rewrite rules. Rewrite `h2` using `[hE'sum]`. Establish `hWs0 : 0 ≤ Ws` using `fun s => by show (0:ℝ) ≤ Ws s`. Rewrite using `[hWsapp]`. Use `hw s` as an intermediate fact.

Establish `: (0:ℝ) ≤ (k:ℝ) - 1` using `by linarith`. Check the signs of the components of the expression. Take `⟨⟨sW, hsW, -, hFsW⟩, -⟩` from `hA l d hl hd hev Ws hWs0`. Establish `hoptW : IsOptDual l d Ws sW` using `⟨hsW, hFsW⟩`. Establish `h3` using `(hc l d hl hd hev Ws E sW hWs0 (fun s => (hE s).1) hoptW).1`.

Establish `hinc` using `hI l d hl hd hev Ws sW hWs0 hoptW`. Establish `hfilt : ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sW s), w s ≤ S / l`. Establish `e1 : ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sW s), Ws s = ((k:ℝ) - 1) * ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sW s), w s`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl (fun s _ => hWsapp s)`.

Establish `e2 : ∑ s, Ws s = ((k:ℝ) - 1) * S`. Rewrite using `[hS, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl (fun s _ => hWsapp s)`. Rewrite `hinc` using `[e1, e2, mul_div_assoc]`. Establish `hk1 : 0 < (k:ℝ) - 1` using `by linarith`.

Conclude with `le_of_mul_le_mul_left hinc hk1`. Establish `hgl` using `inv_le_gamma hl`. Establish `hpt : ∀ s, E s * max (sW s - gam l) 0 ≤ 4 * w s / l + 4 * (if 2 / (l:ℝ) ≤ sW s then w s else 0)`. Introduce `s`. Take `⟨hE0, hE4⟩` from `hE s`.

Establish `hs0` using `(hsW.1 s).1`. Establish `hs1` using `(hsW.1 s).2`. Establish `hws` using `hw s`. Establish `hm0 : 0 ≤ max (sW s - gam l) 0` using `le_max_right _ _`. Establish `hq : 0 ≤ 4 * w s / l` using `by positivity`.

Use `split_ifs with hcase`. Establish `hm : max (sW s - gam l) 0 ≤ 1` using `max_le (by linarith) zero_le_one`. Combine the equalities or inequalities in the displayed calculation. Use `push Not at hcase`. Establish `h21 : 2 / (l:ℝ) = 1 / l + 1 / l` using `by ring`.

Establish `hm : max (sW s - gam l) 0 ≤ 1 / l` using `max_le (by linarith) (by positivity)`. Combine the equalities or inequalities in the displayed calculation. Establish `hsum3 : ∑ s, E s * max (sW s - gam l) 0 ≤ 8 / l * S`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_filter, ← Finset.sum_div, ← Finset.mul_sum, ← hS]`.

Use `_ ≤ 4 * S / l + 4 * (S / l) := by linarith`. Use `_ = 8 / l * S := by ring`. Prove the components needed by the constructor for the conclusion. Establish `: gam l * (2 * T) = 2 * gam l * T` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h2g` using `two_gamma_le_three_div hl`. Establish `hT' : 2 * gam l * T ≤ 3 / l * S`. Combine the equalities or inequalities in the displayed calculation. Establish `h11 : 11 / (l:ℝ) * S = 3 / l * S + 8 / l * S` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem proposition_six : PropSix7 := by
  intro l d inst hl hd hev TT k D w E hk hw hE hoff hon
  classical
  have hA := lemmaFa
  have hc := lemmaFc
  have hI := incomingBound
  have hl3 : (3:ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (0:ℝ) < l := by linarith
  have hk3 : (3:ℝ) ≤ k := by exact_mod_cast hk
  have hg := gamma_nonneg hl
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ s : ZMod d, w s := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ∑ s ∈ TT, w s := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; exact Finset.sum_nonneg (fun s _ => (hw s).le)
  have hTS : T ≤ S := by
    rw [hS, hT]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun s _ _ => (hw s).le)
  obtain ⟨Ws, hWs⟩ : ∃ f : ZMod d → ℝ, f = fun s => ((k:ℝ) - 1) * w s := ⟨_, rfl⟩
  obtain ⟨E', hE'⟩ : ∃ f : ZMod d → ℝ, f = fun s => if s ∈ TT then 2 * w s else 0 := ⟨_, rfl⟩
  have hWsapp : ∀ s, Ws s = ((k:ℝ) - 1) * w s := fun s => by rw [hWs]
  rw [← hS, ← hT, ← hWs]
  have hD0 : 0 ≤ D := fun s => by
    show (0:ℝ) ≤ D s
    have h1 := hw s
    have h2 := (hE s).1
    by_cases hs : s ∈ TT
    · rw [hon s hs]; nlinarith
    · rw [hoff s hs]; nlinarith
  have hE'0 : 0 ≤ E' := fun s => by
    show (0:ℝ) ≤ E' s
    rw [hE']
    try dsimp only
    split_ifs
    · linarith [hw s]
    · exact le_rfl
  have hDE : D + E' = Ws + E := by
    funext s
    simp only [Pi.add_apply, hE', hWs]
    by_cases hs : s ∈ TT
    · rw [if_pos hs, hon s hs]; ring
    · rw [if_neg hs, hoff s hs]; ring

  obtain ⟨⟨sD, hsD, -, hFsD⟩, -⟩ := hA l d hl hd hev D hD0
  have h2 := (hc l d hl hd hev D E' sD hD0 hE'0 ⟨hsD, hFsD⟩).2
  rw [hDE] at h2
  have hE'sum : ∑ s, E' s = 2 * T := by
    rw [hT, Finset.mul_sum, hE', ← Finset.sum_filter]
    simp
  rw [hE'sum] at h2

  have hWs0 : 0 ≤ Ws := fun s => by
    show (0:ℝ) ≤ Ws s
    rw [hWsapp]
    have := hw s
    have : (0:ℝ) ≤ (k:ℝ) - 1 := by linarith
    positivity
  obtain ⟨⟨sW, hsW, -, hFsW⟩, -⟩ := hA l d hl hd hev Ws hWs0
  have hoptW : IsOptDual l d Ws sW := ⟨hsW, hFsW⟩
  have h3 := (hc l d hl hd hev Ws E sW hWs0 (fun s => (hE s).1) hoptW).1
  have hinc := hI l d hl hd hev Ws sW hWs0 hoptW
  have hfilt : ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sW s), w s ≤ S / l := by
    have e1 : ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sW s), Ws s =
        ((k:ℝ) - 1) * ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sW s), w s := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun s _ => hWsapp s)
    have e2 : ∑ s, Ws s = ((k:ℝ) - 1) * S := by
      rw [hS, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun s _ => hWsapp s)
    rw [e1, e2, mul_div_assoc] at hinc
    have hk1 : 0 < (k:ℝ) - 1 := by linarith
    exact le_of_mul_le_mul_left hinc hk1
  have hgl := inv_le_gamma hl
  have hpt : ∀ s, E s * max (sW s - gam l) 0 ≤
      4 * w s / l + 4 * (if 2 / (l:ℝ) ≤ sW s then w s else 0) := by
    intro s
    obtain ⟨hE0, hE4⟩ := hE s
    have hs0 := (hsW.1 s).1
    have hs1 := (hsW.1 s).2
    have hws := hw s
    have hm0 : 0 ≤ max (sW s - gam l) 0 := le_max_right _ _
    have hq : 0 ≤ 4 * w s / l := by positivity
    split_ifs with hcase
    · have hm : max (sW s - gam l) 0 ≤ 1 := max_le (by linarith) zero_le_one
      calc E s * max (sW s - gam l) 0 ≤ E s * 1 := mul_le_mul_of_nonneg_left hm hE0
        _ ≤ 4 * w s := by linarith
        _ ≤ _ := by linarith
    · push Not at hcase
      have h21 : 2 / (l:ℝ) = 1 / l + 1 / l := by ring
      have hm : max (sW s - gam l) 0 ≤ 1 / l := max_le (by linarith) (by positivity)
      calc E s * max (sW s - gam l) 0 ≤ (4 * w s) * (1 / l) :=
            mul_le_mul hE4 hm hm0 (by linarith)
        _ = 4 * w s / l + 4 * 0 := by ring
  have hsum3 : ∑ s, E s * max (sW s - gam l) 0 ≤ 8 / l * S := by
    calc ∑ s, E s * max (sW s - gam l) 0
        ≤ ∑ s, (4 * w s / l + 4 * (if 2 / (l:ℝ) ≤ sW s then w s else 0)) :=
          Finset.sum_le_sum (fun s _ => hpt s)
      _ = 4 * S / l + 4 * ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sW s), w s := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_filter, ← Finset.sum_div,
            ← Finset.mul_sum, ← hS]
      _ ≤ 4 * S / l + 4 * (S / l) := by linarith
      _ = 8 / l * S := by ring
  constructor
  · have : gam l * (2 * T) = 2 * gam l * T := by ring
    linarith
  · have h2g := two_gamma_le_three_div hl
    have hT' : 2 * gam l * T ≤ 3 / l * S :=
      calc 2 * gam l * T ≤ 2 * gam l * S := mul_le_mul_of_nonneg_left hTS (by linarith)
        _ ≤ 3 / l * S := mul_le_mul_of_nonneg_right h2g hS0
    have h11 : 11 / (l:ℝ) * S = 3 / l * S + 8 / l * S := by ring
    linarith

/- English proof (translation)
Establish `hf : Summable f` using `Summable.of_nonneg_of_le (fun e => (hg0 e).trans (hgf e)) hfb hb`. Establish `hg : Summable g` using `Summable.of_nonneg_of_le hg0 (fun e => (hgf e).trans (hfb e)) hb`. Use `first`. Consider the case `exact Summable.tsum_le_tsum hgf hg hf`. Consider the case `exact tsum_le_tsum hgf hg hf`.
-/
lemma tsum_le_of_dominated {f g b : ℕ → ℝ} (hg0 : ∀ e, 0 ≤ g e) (hgf : ∀ e, g e ≤ f e)
    (hfb : ∀ e, f e ≤ b e) (hb : Summable b) : ∑' e, g e ≤ ∑' e, f e := by
  have hf : Summable f := Summable.of_nonneg_of_le (fun e => (hg0 e).trans (hgf e)) hfb hb
  have hg : Summable g := Summable.of_nonneg_of_le hg0 (fun e => (hgf e).trans (hfb e)) hb
  first
  | exact Summable.tsum_le_tsum hgf hg hf
  | exact tsum_le_tsum hgf hg hf

/- English proof (translation)
Establish `hex : ∃ e' : ℕ, Odd e' ∧ s + (e' : ZMod d) ∈ TT`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `htop : dTop d TT s = ⊤`. Unfold `dTop`.

Simplify using `only [iInf_eq_top]`. Introduce `e' he'`. Conclude with `absurd he'.2 (hne e' he'.1)`. Rewrite `h` using `[htop]`. Use `first`.

Consider the case `exact ENat.top_ne_coe e h`. Consider the case `simp at h`. Establish `hle : ∀ e' : ℕ, Odd e' → s + (e' : ZMod d) ∈ TT → dTop d TT s ≤ (e' : ℕ∞)`. Introduce `e' h1 h2`. Unfold `dTop`.

Conclude with `iInf₂_le e' ⟨h1, h2⟩`. Establish `hfind : dTop d TT s = ((Nat.find hex : ℕ) : ℕ∞)`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `hle _ (Nat.find_spec hex).1 (Nat.find_spec hex).2`. Unfold `dTop`.

Apply `le_iInf₂` to reduce the goal to its premises. Introduce `e' he'`. Conclude with `Nat.find_min' hex he'` after adjusting the coercions. Establish `he : e = Nat.find hex`. Rewrite `hfind` using `[h]`.

Conclude with `hfind` after adjusting the coercions. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[he]`. Conclude with `Nat.find_spec hex`. Introduce `e' h1 h2`.

Establish `h3` using `hle e' h1 h2`. Rewrite `h3` using `[h]`. Conclude with `h3` after adjusting the coercions.
-/
lemma least_odd_top_level_spec {d : ℕ} [NeZero d] (TT : Finset (ZMod d)) (s : ZMod d) (e : ℕ)
    (h : dTop d TT s = (e : ℕ∞)) :
    (Odd e ∧ s + (e : ZMod d) ∈ TT) ∧ ∀ e' : ℕ, Odd e' → s + (e' : ZMod d) ∈ TT → e ≤ e' := by
  classical
  have hex : ∃ e' : ℕ, Odd e' ∧ s + (e' : ZMod d) ∈ TT := by
    by_contra hne
    push_neg at hne
    have htop : dTop d TT s = ⊤ := by
      unfold dTop
      simp only [iInf_eq_top]
      intro e' he'
      exact absurd he'.2 (hne e' he'.1)
    rw [htop] at h
    first
    | exact ENat.top_ne_coe e h
    | simp at h
  have hle : ∀ e' : ℕ, Odd e' → s + (e' : ZMod d) ∈ TT → dTop d TT s ≤ (e' : ℕ∞) := by
    intro e' h1 h2
    unfold dTop
    exact iInf₂_le e' ⟨h1, h2⟩
  have hfind : dTop d TT s = ((Nat.find hex : ℕ) : ℕ∞) := by
    apply le_antisymm
    · exact hle _ (Nat.find_spec hex).1 (Nat.find_spec hex).2
    · unfold dTop
      apply le_iInf₂
      intro e' he'
      exact_mod_cast Nat.find_min' hex he'
  have he : e = Nat.find hex := by
    rw [h] at hfind
    exact_mod_cast hfind
  refine ⟨?_, ?_⟩
  · rw [he]
    exact Nat.find_spec hex
  · intro e' h1 h2
    have h3 := hle e' h1 h2
    rw [h] at h3
    exact_mod_cast h3

/- English proof (translation)
Introduce `l d inst hl TT nu1 nu2 s`. Establish `hl2 : (2:ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `hl0 : (0:ℝ) < l` using `by linarith`. Establish `hb : Summable (fun e : ℕ => (nu1 s : ℝ) / (l:ℝ) ^ e)`. Establish `: Summable (fun e : ℕ => ((l:ℝ)⁻¹) ^ e)` using `summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ (by linarith))`.

Simplify `this.mul_left (nu1 s : ℝ)` using `[div_eq_mul_inv, inv_pow]`. Unfold `topTerm oddLevelGainSum`. Use `tsum_le_of_dominated (b := fun e : ℕ => (nu1 s : ℝ) / (l:ℝ) ^ e) ?_ ?_ ?_ hb` and prove the remaining obligations. Apply the tactic sequence `intro e try dsimp only split_ifs`. Conclude with `le_max_right _ _`.

Conclude with `le_rfl`. Apply the tactic sequence `intro e try dsimp only`. Establish `hcap : (0:ℝ) ≤ capL d TT nu1 nu2 (s + (e : ZMod d))` using `Nat.cast_nonneg _`. Establish `hpe : (0:ℝ) < (l:ℝ) ^ e` using `pow_pos hl0 e`. Establish `hn2 : (0:ℝ) ≤ (nu2 s : ℝ) / (l:ℝ) ^ e` using `div_nonneg (Nat.cast_nonneg _) hpe.le`.

Establish `hA' : (0:ℝ) ≤ (nu1 s : ℝ) / (l:ℝ) ^ e` using `div_nonneg (Nat.cast_nonneg _) hpe.le`. Establish `hsub : ((nu1 s : ℝ) - nu2 s) / (l:ℝ) ^ e = (nu1 s : ℝ) / (l:ℝ) ^ e - (nu2 s : ℝ) / (l:ℝ) ^ e` using `sub_div _ _ _`. Distinguish the cases in `ho : Odd e`. Use `swap`. Simplify using `[ho]`.

Break down `lt_trichotomy (e : ℕ∞) (dTop d TT s) with hlt | heq | hgt` into its components or cases. Rewrite using `[if_pos (show Odd e ∧ (e : ℕ∞) < dTop d TT s from ⟨ho, hlt⟩)] split_ifs`. Apply `max_le_max _ le_rfl` to reduce the goal to its premises. Rewrite using `[hsub]`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `le_max_right _ _`. Take `⟨⟨-, hmem⟩, hmin⟩` from `least_odd_top_level_spec TT s e heq.symm`. Establish `hP : ∃ s' ∈ TT, IsLeast {e' : ℕ | Odd e' ∧ s + (e' : ZMod d) = s'} e` using `⟨s + (e : ZMod d), hmem, ⟨ho, rfl⟩, fun e' he' => hmin e' he'.1 (he'.2 ▸ hmem)⟩`. Rewrite using `[if_neg (show ¬ (Odd e ∧ (e : ℕ∞) < dTop d TT s) from fun h => (lt_irrefl _ (heq ▸ h.2))), if_neg (show ¬ (Odd e ∧ dTop d TT s < (e : ℕ∞)) from fun h => (lt_irrefl _ (heq ▸ h.2)))]`. Use `split_ifs with h`.

Conclude with `absurd hP h.2`. Conclude with `le_rfl`. Rewrite using `[if_neg (show ¬ (Odd e ∧ (e : ℕ∞) < dTop d TT s) from fun h => (not_lt.mpr hgt.le h.2)), if_pos (show Odd e ∧ dTop d TT s < (e : ℕ∞) from ⟨ho, hgt⟩)] split_ifs`. Conclude with `max_le (by rw [hsub]; linarith) hA'`. Conclude with `hA'`.

Apply the tactic sequence `intro e try dsimp only`. Establish `hcap : (0:ℝ) ≤ capL d TT nu1 nu2 (s + (e : ZMod d))` using `Nat.cast_nonneg _`. Establish `hpe : (0:ℝ) < (l:ℝ) ^ e` using `pow_pos hl0 e`. Establish `hA' : (0:ℝ) ≤ (nu1 s : ℝ) / (l:ℝ) ^ e` using `div_nonneg (Nat.cast_nonneg _) hpe.le`. Use `split_ifs`.

Conclude with `max_le (by linarith) hA'`. Conclude with `le_rfl`. Conclude with `hA'`.
-/
theorem gain_ge_inner_sum : GainDominatesInnerSum := by
  intro l d inst hl TT nu1 nu2 s
  classical
  have hl2 : (2:ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (0:ℝ) < l := by linarith
  have hb : Summable (fun e : ℕ => (nu1 s : ℝ) / (l:ℝ) ^ e) := by
    have : Summable (fun e : ℕ => ((l:ℝ)⁻¹) ^ e) :=
      summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ (by linarith))
    simpa [div_eq_mul_inv, inv_pow] using this.mul_left (nu1 s : ℝ)
  unfold topTerm oddLevelGainSum
  refine tsum_le_of_dominated (b := fun e : ℕ => (nu1 s : ℝ) / (l:ℝ) ^ e) ?_ ?_ ?_ hb
  · intro e
    try dsimp only
    split_ifs
    · exact le_max_right _ _
    · exact le_rfl
  · intro e
    try dsimp only
    have hcap : (0:ℝ) ≤ capL d TT nu1 nu2 (s + (e : ZMod d)) := Nat.cast_nonneg _
    have hpe : (0:ℝ) < (l:ℝ) ^ e := pow_pos hl0 e
    have hn2 : (0:ℝ) ≤ (nu2 s : ℝ) / (l:ℝ) ^ e := div_nonneg (Nat.cast_nonneg _) hpe.le
    have hA' : (0:ℝ) ≤ (nu1 s : ℝ) / (l:ℝ) ^ e := div_nonneg (Nat.cast_nonneg _) hpe.le
    have hsub : ((nu1 s : ℝ) - nu2 s) / (l:ℝ) ^ e =
        (nu1 s : ℝ) / (l:ℝ) ^ e - (nu2 s : ℝ) / (l:ℝ) ^ e := sub_div _ _ _
    by_cases ho : Odd e
    swap
    · simp [ho]
    rcases lt_trichotomy (e : ℕ∞) (dTop d TT s) with hlt | heq | hgt
    · rw [if_pos (show Odd e ∧ (e : ℕ∞) < dTop d TT s from ⟨ho, hlt⟩)]
      split_ifs
      · apply max_le_max _ le_rfl
        rw [hsub]; linarith
      · exact le_max_right _ _
    · obtain ⟨⟨-, hmem⟩, hmin⟩ := least_odd_top_level_spec TT s e heq.symm
      have hP : ∃ s' ∈ TT, IsLeast {e' : ℕ | Odd e' ∧ s + (e' : ZMod d) = s'} e :=
        ⟨s + (e : ZMod d), hmem, ⟨ho, rfl⟩, fun e' he' => hmin e' he'.1 (he'.2 ▸ hmem)⟩
      rw [if_neg (show ¬ (Odd e ∧ (e : ℕ∞) < dTop d TT s) from fun h => (lt_irrefl _ (heq ▸ h.2))),
        if_neg (show ¬ (Odd e ∧ dTop d TT s < (e : ℕ∞)) from fun h => (lt_irrefl _ (heq ▸ h.2)))]
      split_ifs with h
      · exact absurd hP h.2
      · exact le_rfl
    · rw [if_neg (show ¬ (Odd e ∧ (e : ℕ∞) < dTop d TT s) from fun h => (not_lt.mpr hgt.le h.2)),
        if_pos (show Odd e ∧ dTop d TT s < (e : ℕ∞) from ⟨ho, hgt⟩)]
      split_ifs
      · exact max_le (by rw [hsub]; linarith) hA'
      · exact hA'
  · intro e
    try dsimp only
    have hcap : (0:ℝ) ≤ capL d TT nu1 nu2 (s + (e : ZMod d)) := Nat.cast_nonneg _
    have hpe : (0:ℝ) < (l:ℝ) ^ e := pow_pos hl0 e
    have hA' : (0:ℝ) ≤ (nu1 s : ℝ) / (l:ℝ) ^ e := div_nonneg (Nat.cast_nonneg _) hpe.le
    split_ifs
    · exact max_le (by linarith) hA'
    · exact le_rfl
    · exact hA'

end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
