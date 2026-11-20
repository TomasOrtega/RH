import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcSummableMin

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

def nc_ya (_X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (t0 : Formalism.MainNotions.G.HH D)
    (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0))) : ℝ :=
  Formalism.MainNotions.G.al L (Formalism.MainNotions.G.aL L) (t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w))

def nc_zc (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (t0 : Formalism.MainNotions.G.HH D) (j : ℕ)
    (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0))) : ℝ :=
  Formalism.MainNotions.G.fillG X (Formalism.MainNotions.G.bL L) j (false, t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) + Formalism.MainNotions.G.cG L

open Classical in

def nc_Loc (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts)
    (_hT : GatTies D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (t0 : Formalism.MainNotions.G.HH D) (j : ℕ) : Prop :=
  let p := D.what₂.places.resChar w
  let v := Y.vOf u w hg t0
  let Fl := Y.Fl u w hg
  Formalism.MainNotions.G.gU X K (Formalism.MainNotions.G.aL L) (Formalism.MainNotions.G.bL L) p j t0 =
            Formalism.MainNotions.FormalGroupSystem.gam p * ∑ s ∈ Fl.TT v, nc_ya X Y u w hg t0 s -
              ∑ s ∈ (Fl.TT v).filter IsOddPos, ∑' e : ℕ,
                min (nc_ya X Y u w hg t0 s / ((p : ℝ)) ^ (2 * e + 1)) (nc_zc X Y u w hg t0 j (Formalism.MainNotions.G.posAdd s (2 * e + 1))) -
              Formalism.MainNotions.G.dl X K p t0 ∧
  Formalism.MainNotions.G.g0 X K (Formalism.MainNotions.G.aL L) (Formalism.MainNotions.G.bL L) p j t0 =
            ∑ s ∈ Fl.TT v, ∑' e : ℕ, (if Formalism.MainNotions.G.Excl D p (t0 + s.val • Formalism.MainNotions.G.hP D p) (2 * e + 1) then 0 else
              max 0 (nc_ya X Y u w hg t0 s / ((p : ℝ)) ^ (2 * e + 1) - nc_zc X Y u w hg t0 j (Formalism.MainNotions.G.posAdd s (2 * e + 1)))) -
              Formalism.MainNotions.G.dl X K p t0 ∧
  (∀ s ∈ Fl.TT v, nc_ya X Y u w hg t0 s ≤ al (Fl.TT v) ((D.gat u w hg).P.lam0 v) s) ∧
  (∀ s, 0 ≤ al (Fl.TT v) ((D.gat u w hg).P.lam0 v) s) ∧
  (∀ s, (cap Fl.t (Fl.TT v) ((D.gat u w hg).P.lam0 v) (Fl.w v) j s : ℝ) ≤ nc_zc X Y u w hg t0 j s) ∧
  (∀ s, 0 ≤ cap Fl.t (Fl.TT v) ((D.gat u w hg).P.lam0 v) (Fl.w v) j s) ∧
  (∀ s ∈ Fl.TT v, ∀ e, 2 * e + 1 ∈ dSet (Fl.TT v) s → Formalism.MainNotions.G.Excl D p (t0 + s.val • Formalism.MainNotions.G.hP D p) (2 * e + 1))

def nc_De (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts)
    (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (t0 : Formalism.MainNotions.G.HH D) (j : ℕ) : Prop :=
  de (D.what₂.places.resChar w) (Y.Fl u w hg).t ((Y.Fl u w hg).TT (Y.vOf u w hg t0))
      ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0)) ((Y.Fl u w hg).w (Y.vOf u w hg t0)) j ≤
    Formalism.MainNotions.G.dl X K (D.what₂.places.resChar w) t0

def nc_Need (C₀ : ℝ) : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts),
    C₀ ≤ K.dl1 → C₀ ≤ K.dl2 → C₀ ≤ K.Pr1 → (Formalism.MainNotions.G.rG L.sc < D.R.k ∧ 2 ≤ L.sc.x) → Formalism.MainNotions.SizesAt L →
    ∀ hT : GatTies D, Formalism.MainNotions.G.LatTied hT X Y → ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
      (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      1 ≤ Real.logb (D.what₂.places.resChar w) (2 * L.sc.a) →
      ∀ t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w), ∀ j ∈ SizeData₂.lifts D,
        nc_Loc D L X Y K hT u w hg t0 j ∧ nc_De D L X Y K u w hg t0 j ∧
        Formalism.MainNotions.FormalGroupSystem.Pr (Y.Fl u w hg).t (D.gat u w hg).P.r ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
          ((Y.Fl u w hg).w (Y.vOf u w hg t0)) j ≤
          Formalism.MainNotions.G.Pr X K (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j t0

open Classical in
/- English proof (translation)
Establish `two_le : ∀ (p : ℕ) (x : ℝ), 1 ≤ Real.logb (p : ℝ) x → 2 ≤ p`. Introduce `p x hx`. Assume the negation of the conclusion as `hc`. Establish `hp2 : p < 2` using `by omega`. Apply the tactic sequence `interval_cases p <;> simp [Real.logb] at hx <;> linarith`.

Establish `geom : ∀ p : ℕ, 2 ≤ p → HasSum (fun e : ℕ => 1 / (p : ℝ) ^ (2 * e + 1)) (Formalism.MainNotions.FormalGroupSystem.gam p)`. Introduce `p hp`. Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast (show 1 < p by omega)`. Establish `hp0 : (0 : ℝ) < p` using `by linarith`. Establish `hr0 : 0 ≤ (1 / (p : ℝ)) ^ 2` using `by positivity`.

Establish `hr1 : (1 / (p : ℝ)) ^ 2 < 1`. Rewrite using `[div_pow, one_pow, div_lt_one (pow_pos hp0 2)]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hh` using `(hasSum_geometric_of_lt_one hr0 hr1).mul_left (1 / (p : ℝ))`. Establish `hf : (fun e : ℕ => 1 / (p : ℝ) ^ (2 * e + 1)) = fun i : ℕ => 1 / (p : ℝ) * ((1 / (p : ℝ)) ^ 2) ^ i`.

Use function extensionality and compare the values at `e`. Rewrite using `[← pow_mul, ← pow_succ', one_div_pow]`. Establish `hv : Formalism.MainNotions.FormalGroupSystem.gam p = 1 / (p : ℝ) * (1 - (1 / (p : ℝ)) ^ 2)⁻¹`. Rewrite using `[show (1 : ℝ) - (1 / (p : ℝ)) ^ 2 = ((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ 2 by`. Rewrite using `[div_pow, one_pow, sub_div, div_self (pow_ne_zero 2 hp0.ne')], inv_div]`.

Unfold `Formalism.MainNotions.FormalGroupSystem.gam`. Rewrite using `[← mul_div_assoc, pow_two, ← mul_assoc, one_div_mul_cancel hp0.ne', one_mul]`. Rewrite using `[hf, hv]`. Conclude with `hh`. Establish `minsum : ∀ (p : ℕ), 2 ≤ p → ∀ (a b : ℝ) (C Z : ℕ → ℝ), b ≤ a → 0 ≤ a → (∀ e, 0 ≤ C e) → (∀ e, C e ≤ Z e) → ∑' e : ℕ, min (a / (p : ℝ) ^ (2 * e + 1)) (C e) - ∑' e : ℕ, min (b / (p : ℝ) ^ (2 * e + 1)) (Z e) ≤ Formalism.MainNotions.FormalGroupSystem.gam p * (a - b)`.

Introduce `p hp a b C Z hba ha hC0 hCZ`. Establish `hg` using `geom p hp`. Establish `hp0 : (0 : ℝ) < p` using `by exact_mod_cast (show 0 < p by omega)`. Establish `hq : ∀ e : ℕ, (0 : ℝ) < (p : ℝ) ^ (2 * e + 1)` using `fun e => pow_pos hp0 _`. Establish `hsa : Summable (fun e : ℕ => a / (p : ℝ) ^ (2 * e + 1))` using `(hg.summable.mul_left a).congr (fun e => mul_one_div a _)`.

Establish `hsb : Summable (fun e : ℕ => b / (p : ℝ) ^ (2 * e + 1))` using `(hg.summable.mul_left b).congr (fun e => mul_one_div b _)`. Establish `hf1 : Summable (fun e : ℕ => min (a / (p : ℝ) ^ (2 * e + 1)) (C e))` using `Summable.of_nonneg_of_le (fun e => le_min (div_nonneg ha (hq e).le) (hC0 e)) (fun e => min_le_left _ _) hsa`. Establish `hf2 : Summable (fun e : ℕ => min (b / (p : ℝ) ^ (2 * e + 1)) (Z e))`. Break down `le_or_gt 0 b with hb | hb` into its components or cases. Conclude with `Summable.of_nonneg_of_le (fun e => le_min (div_nonneg hb (hq e).le) ((hC0 e).trans (hCZ e))) (fun e => min_le_left _ _) hsb`.

Use `hsb.congr (fun e => ?_)` and prove the remaining obligations. Establish `hneg : b / (p : ℝ) ^ (2 * e + 1) < 0` using `div_neg_of_neg_of_pos hb (hq e)`. Conclude with `(min_eq_left (by linarith [hC0 e, hCZ e])).symm`. Establish `hm` using `hg.mul_left (a - b)`. Rewrite using `[mul_comm (Formalism.MainNotions.FormalGroupSystem.gam p)]`.

Use `hasSum_le (fun e => ?_) (hf1.hasSum.sub hf2.hasSum) hm` and prove the remaining obligations. Use `show min (a / (p : ℝ) ^ (2 * e + 1)) (C e) - min (b / (p : ℝ) ^ (2 * e + 1)) (Z e) ≤ (a - b) * (1 / (p : ℝ) ^ (2 * e + 1))`. Apply the tactic sequence `have hbq : b / (p : ℝ) ^ (2 * e + 1) ≤ a / (p : ℝ) ^ (2 * e + 1) := by gcongr <;> exact hba`. Establish `h1 : min (b / (p : ℝ) ^ (2 * e + 1)) (C e) ≤ min (b / (p : ℝ) ^ (2 * e + 1)) (Z e)` using `min_le_min_left _ (hCZ e)`. Establish `h2 : min (a / (p : ℝ) ^ (2 * e + 1)) (C e) - min (b / (p : ℝ) ^ (2 * e + 1)) (C e) ≤ a / (p : ℝ) ^ (2 * e + 1) - b / (p : ℝ) ^ (2 * e + 1)`.

Break down `le_total (b / (p : ℝ) ^ (2 * e + 1)) (C e) with hh | hh` into its components or cases. Rewrite using `[min_eq_left hh]`. Combine the linear relations using `[min_le_left (a / (p : ℝ) ^ (2 * e + 1)) (C e)]`. Rewrite using `[min_eq_right hh, min_eq_right (hh.trans hbq)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h3 : a / (p : ℝ) ^ (2 * e + 1) - b / (p : ℝ) ^ (2 * e + 1) = (a - b) * (1 / (p : ℝ) ^ (2 * e + 1))` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `gBcmp : ∀ {n : ℕ} (p : ℕ), 2 ≤ p → ∀ (TT S1 S2 : Finset (Fin n)), S1 ⊆ TT → S2 = S1 → ∀ (A B : Fin n → ℝ) (C Z : Fin n → ℕ → ℝ) (dl de : ℝ), (∀ s ∈ TT, B s ≤ A s) → (∀ s, 0 ≤ A s) → (∀ s e, 0 ≤ C s e) → (∀ s e, C s e ≤ Z s e) → de ≤ dl → Formalism.MainNotions.FormalGroupSystem.ga …`. Introduce `n p hp TT S1 S2 hS hS21 A B C Z dl de hBA hA0 hC0 hCZ hde`. Rewrite using `[hS21]`.

Establish `hg0 : 0 ≤ Formalism.MainNotions.FormalGroupSystem.gam p` using `hasSum_le (fun e => div_nonneg zero_le_one (pow_nonneg (Nat.cast_nonneg p) _)) hasSum_zero (geom p hp)`. Establish `key : ∑ s ∈ S1, (∑' e : ℕ, min (A s / (p : ℝ) ^ (2 * e + 1)) (C s e) - ∑' e : ℕ, min (B s / (p : ℝ) ^ (2 * e + 1)) (Z s e)) ≤ ∑ s ∈ TT, Formalism.MainNotions.FormalGroupSystem.gam p * (A s - B s)` using `(Finset.sum_le_sum (fun s hs => minsum p hp (A s) (B s) (C s) (Z s) (hBA s (hS hs)) (hA0 s) (hC0 s) (hCZ s))).trans (Finset.sum_le_sum_of_subset_of_nonneg hS (fun s hs _ => mul_nonneg hg0 (sub_nonneg.2 (hBA s hs))))`. Rewrite `key` using `[Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, mul_sub]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `gAcmp : ∀ {n : ℕ} (p : ℕ), 2 ≤ p → ∀ (TT : Finset (Fin n)) (A B : Fin n → ℝ) (C Z : Fin n → ℕ → ℝ) (E F : Fin n → ℕ → Prop) (iE : ∀ s e, Decidable (E s e)) (iF : ∀ s e, Decidable (F s e)) (dl de : ℝ), (∀ s ∈ TT, B s ≤ A s) → (∀ s, 0 ≤ A s) → (∀ s e, 0 ≤ C s e) → (∀ s e, C s e ≤ Z …`.

Introduce `n p hp TT A B C Z E F iE iF dl de hBA hA0 hC0 hCZ hFE hde`. Establish `hg` using `geom p hp`. Establish `hp0 : (0 : ℝ) < p` using `by exact_mod_cast (show 0 < p by omega)`. Establish `hq : ∀ e : ℕ, (0 : ℝ) < (p : ℝ) ^ (2 * e + 1)` using `fun e => pow_pos hp0 _`. Establish `hsum : ∑ s ∈ TT, ∑' e : ℕ, @ite ℝ (E s e) (iE s e) 0 (max 0 (B s / (p : ℝ) ^ (2 * e + 1) - Z s e)) ≤ ∑ s ∈ TT, ∑' e : ℕ, @ite ℝ (F s e) (iF s e) 0 (max (A s / (p : ℝ) ^ (2 * e + 1) - C s e) 0)`.

Use `Finset.sum_le_sum (fun s hs => ?_)` and prove the remaining obligations. Establish `hle : ∀ e : ℕ, @ite ℝ (E s e) (iE s e) 0 (max 0 (B s / (p : ℝ) ^ (2 * e + 1) - Z s e)) ≤ @ite ℝ (F s e) (iF s e) 0 (max (A s / (p : ℝ) ^ (2 * e + 1) - C s e) 0)`. Introduce `e`. Apply the tactic sequence `have hbq : B s / (p : ℝ) ^ (2 * e + 1) ≤ A s / (p : ℝ) ^ (2 * e + 1) := by gcongr <;> exact hBA s hs`. Distinguish the cases in `hF : F s e`.

Simplify using `only [if_pos (hFE s hs e hF), if_pos hF, le_refl]`. Rewrite using `[if_neg hF] split_ifs`. Conclude with `le_max_right _ _`. Conclude with `max_le (le_max_right _ _) (le_trans (by linarith [hCZ s e]) (le_max_left _ _))`. Establish `h0 : ∀ e : ℕ, 0 ≤ @ite ℝ (E s e) (iE s e) 0 (max 0 (B s / (p : ℝ) ^ (2 * e + 1) - Z s e))`.

Introduce `e`. Use `split_ifs`. Conclude with `le_refl 0`. Conclude with `le_max_left _ _`. Establish `hR : Summable (fun e : ℕ => @ite ℝ (F s e) (iF s e) 0 (max (A s / (p : ℝ) ^ (2 * e + 1) - C s e) 0))`.

Use `Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) ((hg.summable.mul_left (A s)).congr (fun e => mul_one_div (A s) _))` and prove the remaining obligations. Use `split_ifs`. Conclude with `le_refl 0`. Conclude with `le_max_right _ _`. Use `split_ifs`.

Conclude with `div_nonneg (hA0 s) (hq e).le`. Conclude with `max_le (by linarith [hC0 s e]) (div_nonneg (hA0 s) (hq e).le)`. Conclude with `hasSum_le hle (Summable.of_nonneg_of_le h0 hle hR).hasSum hR.hasSum`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨C₀, ?_⟩` and prove the remaining obligations.

Introduce `D L X Y K h1 h2 h3 hr hx hS hT hTied u w hg hlog t0 ht0 j hj`. Take `⟨hLoc, hDe, hPr⟩` from `h D L X Y K h1 h2 h3 ⟨hr, hx⟩ hS hT hTied u w hg hlog t0 ht0 j hj`. Establish `hp` using `two_le _ _ hlog`. Simplify using `only [nc_Loc] at hLoc`. Take `⟨hgU, hg0, hya, hal0, hcap, hcap0, hEx⟩` from `hLoc`.

Use `⟨?_, ?_, hPr⟩` and prove the remaining obligations. Rewrite using `[hgU]`. Unfold `Formalism.MainNotions.FormalGroupSystem.gB`. Use `gBcmp _ hp _ _ _ ?_ ?_ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `x hx`.

Simplify using `only [Finset.mem_filter] at hx`. Conclude with `hx.1`. Use extensionality with `x`. Simplify using `only [Finset.mem_filter]`. Introduce `s hs`.

Conclude with `hya s hs`. Introduce `s`. Conclude with `hal0 s` after adjusting the coercions. Introduce `s e`. Conclude with `hcap0 _` after adjusting the coercions.

Introduce `s e`. Conclude with `hcap _`. Conclude with `hDe`. Rewrite using `[hg0]`. Unfold `Formalism.MainNotions.FormalGroupSystem.gA`.

Use `gAcmp _ hp _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `s hs`. Conclude with `hya s hs`. Introduce `s`. Conclude with `hal0 s` after adjusting the coercions.

Introduce `s e`. Conclude with `hcap0 _` after adjusting the coercions. Introduce `s e`. Conclude with `hcap _`. Introduce `s hs e he`.

Conclude with `hEx s hs e he`. Conclude with `hDe`.
-/
theorem stmtNumE_of (C₀ : ℝ) (h : nc_Need C₀) : Formalism.MainNotions.FormalGroupSystem.NumericalComparisonUniform := by
  have two_le : ∀ (p : ℕ) (x : ℝ), 1 ≤ Real.logb (p : ℝ) x → 2 ≤ p := by
    intro p x hx
    by_contra hc
    have hp2 : p < 2 := by omega
    interval_cases p <;> simp [Real.logb] at hx <;> linarith
  have geom : ∀ p : ℕ, 2 ≤ p →
      HasSum (fun e : ℕ => 1 / (p : ℝ) ^ (2 * e + 1)) (Formalism.MainNotions.FormalGroupSystem.gam p) := by
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
    have hp0 : (0 : ℝ) < p := by linarith
    have hr0 : 0 ≤ (1 / (p : ℝ)) ^ 2 := by positivity
    have hr1 : (1 / (p : ℝ)) ^ 2 < 1 := by
      rw [div_pow, one_pow, div_lt_one (pow_pos hp0 2)]; nlinarith
    have hh := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (1 / (p : ℝ))
    have hf : (fun e : ℕ => 1 / (p : ℝ) ^ (2 * e + 1)) =
        fun i : ℕ => 1 / (p : ℝ) * ((1 / (p : ℝ)) ^ 2) ^ i := by
      funext e
      rw [← pow_mul, ← pow_succ', one_div_pow]
    have hv : Formalism.MainNotions.FormalGroupSystem.gam p = 1 / (p : ℝ) * (1 - (1 / (p : ℝ)) ^ 2)⁻¹ := by
      rw [show (1 : ℝ) - (1 / (p : ℝ)) ^ 2 = ((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ 2 by
        rw [div_pow, one_pow, sub_div, div_self (pow_ne_zero 2 hp0.ne')], inv_div]
      unfold Formalism.MainNotions.FormalGroupSystem.gam
      rw [← mul_div_assoc, pow_two, ← mul_assoc, one_div_mul_cancel hp0.ne', one_mul]
    rw [hf, hv]
    exact hh
  have minsum : ∀ (p : ℕ), 2 ≤ p → ∀ (a b : ℝ) (C Z : ℕ → ℝ), b ≤ a → 0 ≤ a →
      (∀ e, 0 ≤ C e) → (∀ e, C e ≤ Z e) →
      ∑' e : ℕ, min (a / (p : ℝ) ^ (2 * e + 1)) (C e) -
        ∑' e : ℕ, min (b / (p : ℝ) ^ (2 * e + 1)) (Z e) ≤ Formalism.MainNotions.FormalGroupSystem.gam p * (a - b) := by
    intro p hp a b C Z hba ha hC0 hCZ
    have hg := geom p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    have hq : ∀ e : ℕ, (0 : ℝ) < (p : ℝ) ^ (2 * e + 1) := fun e => pow_pos hp0 _
    have hsa : Summable (fun e : ℕ => a / (p : ℝ) ^ (2 * e + 1)) :=
      (hg.summable.mul_left a).congr (fun e => mul_one_div a _)
    have hsb : Summable (fun e : ℕ => b / (p : ℝ) ^ (2 * e + 1)) :=
      (hg.summable.mul_left b).congr (fun e => mul_one_div b _)
    have hf1 : Summable (fun e : ℕ => min (a / (p : ℝ) ^ (2 * e + 1)) (C e)) :=
      Summable.of_nonneg_of_le (fun e => le_min (div_nonneg ha (hq e).le) (hC0 e))
        (fun e => min_le_left _ _) hsa
    have hf2 : Summable (fun e : ℕ => min (b / (p : ℝ) ^ (2 * e + 1)) (Z e)) := by
      rcases le_or_gt 0 b with hb | hb
      · exact Summable.of_nonneg_of_le
          (fun e => le_min (div_nonneg hb (hq e).le) ((hC0 e).trans (hCZ e)))
          (fun e => min_le_left _ _) hsb
      · refine hsb.congr (fun e => ?_)
        have hneg : b / (p : ℝ) ^ (2 * e + 1) < 0 := div_neg_of_neg_of_pos hb (hq e)
        exact (min_eq_left (by linarith [hC0 e, hCZ e])).symm
    have hm := hg.mul_left (a - b)
    rw [mul_comm (Formalism.MainNotions.FormalGroupSystem.gam p)]
    refine hasSum_le (fun e => ?_) (hf1.hasSum.sub hf2.hasSum) hm
    show min (a / (p : ℝ) ^ (2 * e + 1)) (C e) - min (b / (p : ℝ) ^ (2 * e + 1)) (Z e) ≤
      (a - b) * (1 / (p : ℝ) ^ (2 * e + 1))
    have hbq : b / (p : ℝ) ^ (2 * e + 1) ≤ a / (p : ℝ) ^ (2 * e + 1) := by
      gcongr <;> exact hba
    have h1 : min (b / (p : ℝ) ^ (2 * e + 1)) (C e) ≤ min (b / (p : ℝ) ^ (2 * e + 1)) (Z e) :=
      min_le_min_left _ (hCZ e)
    have h2 : min (a / (p : ℝ) ^ (2 * e + 1)) (C e) - min (b / (p : ℝ) ^ (2 * e + 1)) (C e) ≤
        a / (p : ℝ) ^ (2 * e + 1) - b / (p : ℝ) ^ (2 * e + 1) := by
      rcases le_total (b / (p : ℝ) ^ (2 * e + 1)) (C e) with hh | hh
      · rw [min_eq_left hh]; linarith [min_le_left (a / (p : ℝ) ^ (2 * e + 1)) (C e)]
      · rw [min_eq_right hh, min_eq_right (hh.trans hbq)]; linarith
    have h3 : a / (p : ℝ) ^ (2 * e + 1) - b / (p : ℝ) ^ (2 * e + 1) =
        (a - b) * (1 / (p : ℝ) ^ (2 * e + 1)) := by ring
    linarith
  have gBcmp : ∀ {n : ℕ} (p : ℕ), 2 ≤ p → ∀ (TT S1 S2 : Finset (Fin n)), S1 ⊆ TT → S2 = S1 →
      ∀ (A B : Fin n → ℝ) (C Z : Fin n → ℕ → ℝ) (dl de : ℝ),
      (∀ s ∈ TT, B s ≤ A s) → (∀ s, 0 ≤ A s) → (∀ s e, 0 ≤ C s e) → (∀ s e, C s e ≤ Z s e) →
      de ≤ dl →
      Formalism.MainNotions.FormalGroupSystem.gam p * ∑ s ∈ TT, B s -
                ∑ s ∈ S1, ∑' e : ℕ, min (B s / (p : ℝ) ^ (2 * e + 1)) (Z s e) - dl ≤
        Formalism.MainNotions.FormalGroupSystem.gam p * ∑ s ∈ TT, A s -
          ∑ s ∈ S2, ∑' e : ℕ, min (A s / (p : ℝ) ^ (2 * e + 1)) (C s e) - de := by
    intro n p hp TT S1 S2 hS hS21 A B C Z dl de hBA hA0 hC0 hCZ hde
    rw [hS21]
    have hg0 : 0 ≤ Formalism.MainNotions.FormalGroupSystem.gam p :=
      hasSum_le (fun e => div_nonneg zero_le_one (pow_nonneg (Nat.cast_nonneg p) _))
        hasSum_zero (geom p hp)
    have key : ∑ s ∈ S1, (∑' e : ℕ, min (A s / (p : ℝ) ^ (2 * e + 1)) (C s e) -
        ∑' e : ℕ, min (B s / (p : ℝ) ^ (2 * e + 1)) (Z s e)) ≤
        ∑ s ∈ TT, Formalism.MainNotions.FormalGroupSystem.gam p * (A s - B s) :=
      (Finset.sum_le_sum (fun s hs => minsum p hp (A s) (B s) (C s) (Z s) (hBA s (hS hs))
        (hA0 s) (hC0 s) (hCZ s))).trans
        (Finset.sum_le_sum_of_subset_of_nonneg hS
          (fun s hs _ => mul_nonneg hg0 (sub_nonneg.2 (hBA s hs))))
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, mul_sub] at key
    linarith
  have gAcmp : ∀ {n : ℕ} (p : ℕ), 2 ≤ p → ∀ (TT : Finset (Fin n)) (A B : Fin n → ℝ)
      (C Z : Fin n → ℕ → ℝ) (E F : Fin n → ℕ → Prop) (iE : ∀ s e, Decidable (E s e))
      (iF : ∀ s e, Decidable (F s e)) (dl de : ℝ),
      (∀ s ∈ TT, B s ≤ A s) → (∀ s, 0 ≤ A s) → (∀ s e, 0 ≤ C s e) → (∀ s e, C s e ≤ Z s e) →
      (∀ s ∈ TT, ∀ e, F s e → E s e) → de ≤ dl →
      ∑ s ∈ TT, ∑' e : ℕ, @ite ℝ (E s e) (iE s e) 0 (max 0 (B s / (p : ℝ) ^ (2 * e + 1) - Z s e)) -
          dl ≤
        ∑ s ∈ TT, ∑' e : ℕ, @ite ℝ (F s e) (iF s e) 0 (max (A s / (p : ℝ) ^ (2 * e + 1) - C s e) 0) -
          de := by
    intro n p hp TT A B C Z E F iE iF dl de hBA hA0 hC0 hCZ hFE hde
    have hg := geom p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    have hq : ∀ e : ℕ, (0 : ℝ) < (p : ℝ) ^ (2 * e + 1) := fun e => pow_pos hp0 _
    have hsum : ∑ s ∈ TT, ∑' e : ℕ,
          @ite ℝ (E s e) (iE s e) 0 (max 0 (B s / (p : ℝ) ^ (2 * e + 1) - Z s e)) ≤
        ∑ s ∈ TT, ∑' e : ℕ,
          @ite ℝ (F s e) (iF s e) 0 (max (A s / (p : ℝ) ^ (2 * e + 1) - C s e) 0) := by
      refine Finset.sum_le_sum (fun s hs => ?_)
      have hle : ∀ e : ℕ,
          @ite ℝ (E s e) (iE s e) 0 (max 0 (B s / (p : ℝ) ^ (2 * e + 1) - Z s e)) ≤
            @ite ℝ (F s e) (iF s e) 0 (max (A s / (p : ℝ) ^ (2 * e + 1) - C s e) 0) := by
        intro e
        have hbq : B s / (p : ℝ) ^ (2 * e + 1) ≤ A s / (p : ℝ) ^ (2 * e + 1) := by
          gcongr <;> exact hBA s hs
        by_cases hF : F s e
        · simp only [if_pos (hFE s hs e hF), if_pos hF, le_refl]
        · rw [if_neg hF]
          split_ifs
          · exact le_max_right _ _
          · exact max_le (le_max_right _ _) (le_trans (by linarith [hCZ s e]) (le_max_left _ _))
      have h0 : ∀ e : ℕ,
          0 ≤ @ite ℝ (E s e) (iE s e) 0 (max 0 (B s / (p : ℝ) ^ (2 * e + 1) - Z s e)) := by
        intro e
        split_ifs
        · exact le_refl 0
        · exact le_max_left _ _
      have hR : Summable (fun e : ℕ =>
          @ite ℝ (F s e) (iF s e) 0 (max (A s / (p : ℝ) ^ (2 * e + 1) - C s e) 0)) := by
        refine Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_)
          ((hg.summable.mul_left (A s)).congr (fun e => mul_one_div (A s) _))
        · split_ifs
          · exact le_refl 0
          · exact le_max_right _ _
        · split_ifs
          · exact div_nonneg (hA0 s) (hq e).le
          · exact max_le (by linarith [hC0 s e]) (div_nonneg (hA0 s) (hq e).le)
      exact hasSum_le hle (Summable.of_nonneg_of_le h0 hle hR).hasSum hR.hasSum
    linarith
  refine ⟨C₀, ?_⟩
  intro D L X Y K h1 h2 h3 hr hx hS hT hTied u w hg hlog t0 ht0 j hj
  obtain ⟨hLoc, hDe, hPr⟩ := h D L X Y K h1 h2 h3 ⟨hr, hx⟩ hS hT hTied u w hg hlog t0 ht0 j hj
  have hp := two_le _ _ hlog
  dsimp only [nc_Loc] at hLoc
  obtain ⟨hgU, hg0, hya, hal0, hcap, hcap0, hEx⟩ := hLoc
  refine ⟨?_, ?_, hPr⟩
  · rw [hgU]
    unfold Formalism.MainNotions.FormalGroupSystem.gB
    refine gBcmp _ hp _ _ _ ?_ ?_ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter] at hx
      exact hx.1
    · ext x
      simp only [Finset.mem_filter]
    · intro s hs
      exact hya s hs
    · intro s
      exact_mod_cast hal0 s
    · intro s e
      exact_mod_cast hcap0 _
    · intro s e
      exact hcap _
    · exact hDe
  · rw [hg0]
    unfold Formalism.MainNotions.FormalGroupSystem.gA
    refine gAcmp _ hp _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
    · intro s hs
      exact hya s hs
    · intro s
      exact_mod_cast hal0 s
    · intro s e
      exact_mod_cast hcap0 _
    · intro s e
      exact hcap _
    · intro s hs e he
      exact hEx s hs e he
    · exact hDe

/- English proof (translation)
Take `⟨C, hC⟩` from `stmtNumE_of C₀ h`. Conclude with `⟨C, hC D L X Y⟩`.
-/
theorem stmtNum_of (C₀ : ℝ) (h : nc_Need C₀) (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Formalism.MainNotions.G.Inst D L)
    (Y : Formalism.MainNotions.G.LatInst D) : Formalism.MainNotions.FormalGroupSystem.NumericalComparison D L X Y := by
  obtain ⟨C, hC⟩ := stmtNumE_of C₀ h
  exact ⟨C, hC D L X Y⟩

end Formalism.MainNotions.FormalGroupSystem.Pf
