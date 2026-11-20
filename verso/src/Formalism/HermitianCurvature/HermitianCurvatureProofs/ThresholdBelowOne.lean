import Formalism.HermitianCurvature.StatementJ

open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J

namespace Formalism.FourierDecayAlt.P.Jx11

/- English proof (translation)
Introduce `L f d pl sa al bt κ len lv be X B Mx hκ hlen hbt hsa h1 h2`. Establish `hz : κ ^ (1 - (d : ℤ)) = κ * (κ ^ d)⁻¹`. Rewrite using `[zpow_sub₀ hκ.ne', zpow_one, zpow_natCast, div_eq_mul_inv]`. Establish `hfac : ∀ a, (1 / 2) * (4 / (bt a - al a)) ^ d * (κ * be (pl a)) = κ ^ (1 - (d : ℤ)) * ((1 / 2) * be (pl a) * (4 * κ / len) ^ d)`. Introduce `a`.

Rewrite using `[hbt a, hz, div_pow, div_pow, mul_pow]`. Clear the denominators using the available nonvanishing facts. Establish `hc0 : 0 ≤ ∏ a, (1 / 2) * (4 / (bt a - al a)) ^ d`. Apply `Finset.prod_nonneg` to reduce the goal to its premises. Introduce `a _`.

Rewrite using `[hbt a]`. Check the signs of the components of the expression. Establish `hP : 0 < ∏ _a : Fin L, κ ^ (1 - (d : ℤ))` using `Finset.prod_pos (fun _ _ => zpow_pos hκ _)`. Establish `h3 : (∏ a, sa a) * X ≤ (∏ a, (1 / 2) * (4 / (bt a - al a)) ^ d) * ((∏ a, κ * be (pl a)) * Mx)` using `h1.trans (mul_le_mul_of_nonneg_left h2 hc0)`. Establish `h4 : (∏ a, sa a) = (∏ _a : Fin L, κ ^ (1 - (d : ℤ))) * ∏ a, lv (pl a)`.

Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl (fun a _ => hsa a)`. Establish `h5 : (∏ a, (1 / 2) * (4 / (bt a - al a)) ^ d) * (∏ a, κ * be (pl a)) = (∏ _a : Fin L, κ ^ (1 - (d : ℤ))) * ∏ a, (1 / 2) * be (pl a) * (4 * κ / len) ^ d`. Rewrite using `[← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl (fun a _ => hfac a)`.

Rewrite `h3` using `[h4, ← mul_assoc, h5, mul_assoc, mul_assoc]`. Conclude with `le_of_mul_le_mul_left h3 hP`.
-/
theorem chebToThreshold : ChebToThreshold := by
  intro L f d pl sa al bt κ len lv be X B Mx hκ hlen hbt hsa h1 h2
  have hz : κ ^ (1 - (d : ℤ)) = κ * (κ ^ d)⁻¹ := by
    rw [zpow_sub₀ hκ.ne', zpow_one, zpow_natCast, div_eq_mul_inv]
  have hfac : ∀ a, (1 / 2) * (4 / (bt a - al a)) ^ d * (κ * be (pl a)) =
      κ ^ (1 - (d : ℤ)) * ((1 / 2) * be (pl a) * (4 * κ / len) ^ d) := by
    intro a
    rw [hbt a, hz, div_pow, div_pow, mul_pow]
    field_simp
  have hc0 : 0 ≤ ∏ a, (1 / 2) * (4 / (bt a - al a)) ^ d := by
    apply Finset.prod_nonneg
    intro a _
    rw [hbt a]; positivity
  have hP : 0 < ∏ _a : Fin L, κ ^ (1 - (d : ℤ)) := Finset.prod_pos (fun _ _ => zpow_pos hκ _)
  have h3 : (∏ a, sa a) * X ≤ (∏ a, (1 / 2) * (4 / (bt a - al a)) ^ d) * ((∏ a, κ * be (pl a)) * Mx) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 hc0)
  have h4 : (∏ a, sa a) = (∏ _a : Fin L, κ ^ (1 - (d : ℤ))) * ∏ a, lv (pl a) := by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl (fun a _ => hsa a)
  have h5 : (∏ a, (1 / 2) * (4 / (bt a - al a)) ^ d) * (∏ a, κ * be (pl a)) =
      (∏ _a : Fin L, κ ^ (1 - (d : ℤ))) * ∏ a, (1 / 2) * be (pl a) * (4 * κ / len) ^ d := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun a _ => hfac a)
  rw [h4, ← mul_assoc, h5, mul_assoc, mul_assoc] at h3
  exact le_of_mul_le_mul_left h3 hP

/- English proof (translation)
Establish `hth : ∀ j, F7.thGrid grid j = ∏ a, (|F7.lagCo (grid a) (j a)| / S a)`. Introduce `j`. Unfold `F7.thGrid`. Conclude with `Finset.prod_congr rfl fun a _ => by rw [hS a]`. Establish `hnn : ∀ j, 0 ≤ F7.thGrid grid j`.

Introduce `j`. Rewrite using `[hth j]`. Conclude with `Finset.prod_nonneg fun a _ => div_nonneg (abs_nonneg _) (hpos a).le`. Establish `hsum : ∑ j, F7.thGrid grid j = 1`. Establish `h1 : ∑ j : Fin L → Fin (d + 1), ∏ a, (|F7.lagCo (grid a) (j a)| / S a) = ∏ a, ∑ i, (|F7.lagCo (grid a) i| / S a)`.

Rewrite using `[Finset.prod_univ_sum, Fintype.piFinset_univ]`. Rewrite using `[Finset.sum_congr rfl fun j _ => hth j, h1]`. Apply `Finset.prod_eq_one` to reduce the goal to its premises. Introduce `a _`. Rewrite using `[← Finset.sum_div, hS a, div_self (hpos a).ne']`.

Establish `hP : 0 < ∏ a, S a` using `Finset.prod_pos fun a _ => hpos a`. Establish `hco : ∀ j : Fin L → Fin (d + 1), |∏ a, F7.lagCo (grid a) (j a)| = (∏ a, S a) * F7.thGrid grid j`. Introduce `j`. Rewrite using `[hth j, Finset.prod_div_distrib, Finset.abs_prod, mul_div_cancel₀ _ hP.ne']`. Use `⟨hnn, hsum, ?_⟩` and prove the remaining obligations.

Rewrite using `[hz]`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `j _`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_eq_abs, hco j]`.

Conclude with `mul_le_mul_of_nonneg_left (hF j) (mul_nonneg hP.le (hnn j))`. Use `_ = (∏ a, S a) * (c * ∑ j, F7.thGrid grid j * Mj j) := by`. Rewrite using `[Finset.mul_sum, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem mix {L d : ℕ} (grid : Fin L → Fin (d + 1) → ℝ) (S : Fin L → ℝ)
    (hS : ∀ a, ∑ i, |F7.lagCo (grid a) i| = S a) (hpos : ∀ a, 0 < S a) (z : ℂ)
    (Fj : (Fin L → Fin (d + 1)) → ℂ)
    (hz : z = ∑ j : Fin L → Fin (d + 1), ((∏ a, F7.lagCo (grid a) (j a) : ℝ) : ℂ) * Fj j) (c : ℝ)
    (Mj : (Fin L → Fin (d + 1)) → ℝ) (hF : ∀ j, ‖Fj j‖ ≤ c * Mj j) :
    (∀ j, 0 ≤ F7.thGrid grid j) ∧ ∑ j, F7.thGrid grid j = 1 ∧
      ‖z‖ ≤ (∏ a, S a) * (c * ∑ j, F7.thGrid grid j * Mj j) := by
  have hth : ∀ j, F7.thGrid grid j = ∏ a, (|F7.lagCo (grid a) (j a)| / S a) := by
    intro j
    unfold F7.thGrid
    exact Finset.prod_congr rfl fun a _ => by rw [hS a]
  have hnn : ∀ j, 0 ≤ F7.thGrid grid j := by
    intro j
    rw [hth j]
    exact Finset.prod_nonneg fun a _ => div_nonneg (abs_nonneg _) (hpos a).le
  have hsum : ∑ j, F7.thGrid grid j = 1 := by
    have h1 : ∑ j : Fin L → Fin (d + 1), ∏ a, (|F7.lagCo (grid a) (j a)| / S a) =
        ∏ a, ∑ i, (|F7.lagCo (grid a) i| / S a) := by
      rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    rw [Finset.sum_congr rfl fun j _ => hth j, h1]
    apply Finset.prod_eq_one
    intro a _
    rw [← Finset.sum_div, hS a, div_self (hpos a).ne']
  have hP : 0 < ∏ a, S a := Finset.prod_pos fun a _ => hpos a
  have hco : ∀ j : Fin L → Fin (d + 1), |∏ a, F7.lagCo (grid a) (j a)| = (∏ a, S a) * F7.thGrid grid j := by
    intro j
    rw [hth j, Finset.prod_div_distrib, Finset.abs_prod, mul_div_cancel₀ _ hP.ne']
  refine ⟨hnn, hsum, ?_⟩
  rw [hz]
  calc ‖∑ j : Fin L → Fin (d + 1), ((∏ a, F7.lagCo (grid a) (j a) : ℝ) : ℂ) * Fj j‖
      ≤ ∑ j : Fin L → Fin (d + 1), ‖((∏ a, F7.lagCo (grid a) (j a) : ℝ) : ℂ) * Fj j‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin L → Fin (d + 1), (∏ a, S a) * F7.thGrid grid j * (c * Mj j) := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hco j]
        exact mul_le_mul_of_nonneg_left (hF j) (mul_nonneg hP.le (hnn j))
    _ = (∏ a, S a) * (c * ∑ j, F7.thGrid grid j * Mj j) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring

end Formalism.FourierDecayAlt.P.Jx11

namespace Formalism.FourierDecayAlt.P

open Jx11

/- English proof (translation)
Introduce `m C c₂ κ N I A hκ hA hc`. Unfold `Sz.lamThreshold`. Establish `e : 2 * (1 - 1) + 1 - 1 = 0` using `by norm_num`. Rewrite using `[e, pow_zero, mul_one]`. Conclude with `mul_le_mul_of_nonneg_right hc (by positivity)`.
-/
theorem threshold_below_one : ThresholdBelowOne := by
  intro m C c₂ κ N I A hκ hA hc
  unfold Sz.lamThreshold
  have e : 2 * (1 - 1) + 1 - 1 = 0 := by norm_num
  rw [e, pow_zero, mul_one]
  exact mul_le_mul_of_nonneg_right hc (by positivity)

/- English proof (translation)
Introduce `L f K pl A φ h`. Rewrite using `[← Finset.prod_fiberwise (s := univ) (g := pl) (f := fun a => φ (pl a))]`. Establish `h1 : ∀ v : Fin f, ∏ a ∈ univ.filter (fun a => pl a = v), φ (pl a) = φ v ^ (if v ∈ A then K else 0)`. Introduce `v`. Rewrite using `[← h v, ← Finset.prod_const]`.

Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `a ha`. Rewrite using `[(Finset.mem_filter.1 ha).2]`. Simplify using `only [h1]`. Rewrite using `[← Finset.prod_subset (Finset.subset_univ A)]`.

Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `v hv`. Rewrite using `[if_pos hv]`. Introduce `v _ hv`. Rewrite using `[if_neg hv, pow_zero]`.
-/
theorem letters_at_places : LettersAtPlaces := by
  intro L f K pl A φ h
  rw [← Finset.prod_fiberwise (s := univ) (g := pl) (f := fun a => φ (pl a))]
  have h1 : ∀ v : Fin f, ∏ a ∈ univ.filter (fun a => pl a = v), φ (pl a) = φ v ^ (if v ∈ A then K else 0) := by
    intro v
    rw [← h v, ← Finset.prod_const]
    apply Finset.prod_congr rfl
    intro a ha
    rw [(Finset.mem_filter.1 ha).2]
  simp only [h1]
  rw [← Finset.prod_subset (Finset.subset_univ A)]
  · apply Finset.prod_congr rfl
    intro v hv; rw [if_pos hv]
  · intro v _ hv; rw [if_neg hv, pow_zero]

/- English proof (translation)
Introduce `hPW hC R M _ _ _ _ _ _ Ξ n L f pl dat α β X X' κ len Mx lv be hn hκ hlen hbt hsh hs hF`. Establish `hlt : ∀ a, α a < β a` using `fun a => by have := hbt a; linarith`. Establish `h1` using `hPW R M Ξ n L dat α β X X' _ hn hlt hsh hF`. Conclude with `hC L f (2 * n) pl (fun a => ‖(dat a).s‖) α β κ len lv be _ _ Mx hκ hlen hbt hs h1 le_rfl`.
-/
theorem wave_letters : WaveLetters := by
  intro hPW hC R M _ _ _ _ _ _ Ξ n L f pl dat α β X X' κ len Mx lv be hn hκ hlen hbt hsh hs hF
  have hlt : ∀ a, α a < β a := fun a => by have := hbt a; linarith
  have h1 := hPW R M Ξ n L dat α β X X' _ hn hlt hsh hF
  exact hC L f (2 * n) pl (fun a => ‖(dat a).s‖) α β κ len lv be _ _ Mx hκ hlen hbt hs h1 le_rfl

/- English proof (translation)
Introduce `hPW R M _ _ _ _ _ _ Ξ L f pl dat y X X' κ Mx lv be hκ hsh hs hF`. Establish `: Subsingleton (Fin (2 * 0 + 1))` using `(inferInstance : Subsingleton (Fin 1))`. Establish `h` using `hPW R M Ξ 0 L dat (fun a _ => y a) X X' hsh (fun a => Function.injective_of_subsingleton _)`. Rewrite `h` using `[Fintype.sum_subsingleton _ (fun _ => (0 : Fin (2 * 0 + 1)))]`. Establish `hl : ∀ a : Fin L, F7.lagCo (fun _ : Fin (2 * 0 + 1) => y a) 0 = 1`.

Introduce `a`. Unfold `F7.lagCo`. Apply `Finset.prod_eq_one` to reduce the goal to its premises. Introduce `i hi`. Conclude with `absurd (Subsingleton.elim _ _) (Finset.mem_erase.1 hi).1`.

Simplify using `only [hl, Finset.prod_const_one, Complex.ofReal_one, one_mul] at h`. Establish `hn : (∏ a, ‖(dat a).s‖) * ‖Ξ X X'‖ = ‖F7.Fw Ξ X X' (List.ofFn fun a => (dat a, y a)) 1 1‖`. Rewrite using `[← h, norm_mul, norm_prod]`. Establish `h1 : (∏ a, ‖(dat a).s‖) = (∏ _a : Fin L, κ) * ∏ a, lv (pl a)`. Rewrite using `[← Finset.prod_mul_distrib]`.

Conclude with `Finset.prod_congr rfl (fun a _ => hs a)`. Establish `h2 : (∏ a, κ * be (pl a)) = (∏ _a : Fin L, κ) * ∏ a, be (pl a)`. Rewrite using `[← Finset.prod_mul_distrib]`. Establish `hP : 0 < ∏ _a : Fin L, κ` using `Finset.prod_pos (fun _ _ => hκ)`. Rewrite `hF` using `[← hn, h1, h2, mul_assoc, mul_assoc]`.

Conclude with `le_of_mul_le_mul_left hF hP`.
-/
theorem wave_letters_one : WaveLettersOne := by
  intro hPW R M _ _ _ _ _ _ Ξ L f pl dat y X X' κ Mx lv be hκ hsh hs hF
  have : Subsingleton (Fin (2 * 0 + 1)) := (inferInstance : Subsingleton (Fin 1))
  have h := hPW R M Ξ 0 L dat (fun a _ => y a) X X' hsh (fun a => Function.injective_of_subsingleton _)
  rw [Fintype.sum_subsingleton _ (fun _ => (0 : Fin (2 * 0 + 1)))] at h
  have hl : ∀ a : Fin L, F7.lagCo (fun _ : Fin (2 * 0 + 1) => y a) 0 = 1 := by
    intro a
    unfold F7.lagCo
    apply Finset.prod_eq_one
    intro i hi
    exact absurd (Subsingleton.elim _ _) (Finset.mem_erase.1 hi).1
  simp only [hl, Finset.prod_const_one, Complex.ofReal_one, one_mul] at h
  have hn : (∏ a, ‖(dat a).s‖) * ‖Ξ X X'‖ = ‖F7.Fw Ξ X X' (List.ofFn fun a => (dat a, y a)) 1 1‖ := by
    rw [← h, norm_mul, norm_prod]
  have h1 : (∏ a, ‖(dat a).s‖) = (∏ _a : Fin L, κ) * ∏ a, lv (pl a) := by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl (fun a _ => hs a)
  have h2 : (∏ a, κ * be (pl a)) = (∏ _a : Fin L, κ) * ∏ a, be (pl a) := by
    rw [← Finset.prod_mul_distrib]
  have hP : 0 < ∏ _a : Fin L, κ := Finset.prod_pos (fun _ _ => hκ)
  rw [← hn, h1, h2, mul_assoc, mul_assoc] at hF
  exact le_of_mul_le_mul_left hF hP

/- English proof (translation)
Introduce `hLW hC R M _ _ _ _ _ _ Ξ n s L f pl dat A₀ A₀v e t t' α β X X' κ len Mx ov be hs hκ hlen hbt h0 he ht hA hA0 hB hBv ho hF`. Establish `hlt : ∀ a, α a < β a` using `fun a => by have := hbt a; linarith`. Establish `h1` using `hLW R M Ξ n s L dat A₀ A₀v e t t' α β X X' _ hs h0 he ht hA hA0 hB hBv hlt hF`. Conclude with `hC L f (2 * n + s) pl (fun a => ‖1 / t a - 1 / t' a‖) α β κ len ov be _ _ Mx hκ hlen hbt ho h1 le_rfl`.
-/
theorem lift_letters : LiftLetters := by
  intro hLW hC R M _ _ _ _ _ _ Ξ n s L f pl dat A₀ A₀v e t t' α β X X' κ len Mx ov be hs hκ hlen hbt
    h0 he ht hA hA0 hB hBv ho hF
  have hlt : ∀ a, α a < β a := fun a => by have := hbt a; linarith
  have h1 := hLW R M Ξ n s L dat A₀ A₀v e t t' α β X X' _ hs h0 he ht hA hA0 hB hBv hlt hF
  exact hC L f (2 * n + s) pl (fun a => ‖1 / t a - 1 / t' a‖) α β κ len ov be _ _ Mx hκ hlen hbt ho h1 le_rfl

/- English proof (translation)
Introduce `hPW hCS R M _ _ _ _ _ _ Ξ n L f pl dat α β X X' κ len Mj lv be hn hκ hlen hbt hsh hs hF`. Establish `hlt : ∀ a, α a < β a` using `fun a => by have := hbt a; linarith`. Establish `hd : 1 ≤ 2 * n` using `by omega`. Establish `hid` using `hPW R M Ξ n L dat (fun a => Formalism.SA.C.chebPt (α a) (β a) (2 * n)) X X' hsh (fun a => (hCS (α a) (β a) (2 * n) (hlt a) hd).1)`. Take `⟨m1, m2, m3⟩` from `mix (fun a => Formalism.SA.C.chebPt (α a) (β a) (2 * n)) (fun a => (1 / 2) * (4 / (β a - α a)) ^ (2 * n)) (fun a => (hCS (α a) (β a) (2 * n) (hlt a) hd).2) (fun a => by have := hlt a; have h : 0 < β a - α a := by linarith positivity) _ _ hid _ Mj hF`.

Use `⟨m1, m2, ?_⟩` and prove the remaining obligations. Rewrite `m3` using `[norm_mul, norm_prod]`. Conclude with `chebToThreshold L f (2 * n) pl (fun a => ‖(dat a).s‖) α β κ len lv be _ _ _ hκ hlen hbt hs m3 le_rfl`.
-/
theorem wave_letters_mixed : WaveLettersMix := by
  intro hPW hCS R M _ _ _ _ _ _ Ξ n L f pl dat α β X X' κ len Mj lv be hn hκ hlen hbt hsh hs hF
  have hlt : ∀ a, α a < β a := fun a => by have := hbt a; linarith
  have hd : 1 ≤ 2 * n := by omega
  have hid := hPW R M Ξ n L dat (fun a => Formalism.SA.C.chebPt (α a) (β a) (2 * n)) X X' hsh
    (fun a => (hCS (α a) (β a) (2 * n) (hlt a) hd).1)
  obtain ⟨m1, m2, m3⟩ := mix (fun a => Formalism.SA.C.chebPt (α a) (β a) (2 * n))
    (fun a => (1 / 2) * (4 / (β a - α a)) ^ (2 * n))
    (fun a => (hCS (α a) (β a) (2 * n) (hlt a) hd).2)
    (fun a => by have := hlt a; have h : 0 < β a - α a := by linarith
                 positivity)
    _ _ hid _ Mj hF
  refine ⟨m1, m2, ?_⟩
  rw [norm_mul, norm_prod] at m3
  exact chebToThreshold L f (2 * n) pl (fun a => ‖(dat a).s‖) α β κ len lv be _ _ _ hκ hlen hbt hs
    m3 le_rfl

/- English proof (translation)
Introduce `hLW hCS R M _ _ _ _ _ _ Ξ n s L f pl dat A₀ A₀v e t t' α β X X' κ len Mj ov be hs hκ hlen hbt h0 he ht hA hA0 hB hBv ho hF`. Establish `hlt : ∀ a, α a < β a` using `fun a => by have := hbt a; linarith`. Establish `hd : 1 ≤ 2 * n + s` using `by omega`. Establish `hid` using `hLW R M Ξ n s L dat A₀ A₀v e t t' (fun a => Formalism.SA.C.chebPt (α a) (β a) (2 * n + s)) X X' hs h0 he ht hA hA0 hB hBv (fun a => (hCS (α a) (β a) (2 * n + s) (hlt a) hd).1)`. Take `⟨m1, m2, m3⟩` from `mix (fun a => Formalism.SA.C.chebPt (α a) (β a) (2 * n + s)) (fun a => (1 / 2) * (4 / (β a - α a)) ^ (2 * n + s)) (fun a => (hCS (α a) (β a) (2 * n + s) (hlt a) hd).2) (fun a => by have := hlt a; have h : 0 < β a - α a := by linarith positivity) _ _ hid _ Mj hF`.

Use `⟨m1, m2, ?_⟩` and prove the remaining obligations. Establish `hn : ∀ a, ‖e a * (1 / t a - 1 / t' a)‖ = ‖1 / t a - 1 / t' a‖`. Introduce `a`. Rewrite using `[norm_mul]`. Apply the tactic sequence `rcases he a with h | h <;> rw [h] <;> simp`.

Rewrite `m3` using `[norm_mul, norm_prod, Finset.prod_congr rfl fun a _ => hn a]`. Conclude with `chebToThreshold L f (2 * n + s) pl (fun a => ‖1 / t a - 1 / t' a‖) α β κ len ov be _ _ _ hκ hlen hbt ho m3 le_rfl`.
-/
theorem lift_letters_mixed : LiftLettersMix := by
  intro hLW hCS R M _ _ _ _ _ _ Ξ n s L f pl dat A₀ A₀v e t t' α β X X' κ len Mj ov be hs hκ hlen hbt
    h0 he ht hA hA0 hB hBv ho hF
  have hlt : ∀ a, α a < β a := fun a => by have := hbt a; linarith
  have hd : 1 ≤ 2 * n + s := by omega
  have hid := hLW R M Ξ n s L dat A₀ A₀v e t t' (fun a => Formalism.SA.C.chebPt (α a) (β a) (2 * n + s)) X X'
    hs h0 he ht hA hA0 hB hBv (fun a => (hCS (α a) (β a) (2 * n + s) (hlt a) hd).1)
  obtain ⟨m1, m2, m3⟩ := mix (fun a => Formalism.SA.C.chebPt (α a) (β a) (2 * n + s))
    (fun a => (1 / 2) * (4 / (β a - α a)) ^ (2 * n + s))
    (fun a => (hCS (α a) (β a) (2 * n + s) (hlt a) hd).2)
    (fun a => by have := hlt a; have h : 0 < β a - α a := by linarith
                 positivity)
    _ _ hid _ Mj hF
  refine ⟨m1, m2, ?_⟩
  have hn : ∀ a, ‖e a * (1 / t a - 1 / t' a)‖ = ‖1 / t a - 1 / t' a‖ := by
    intro a
    rw [norm_mul]
    rcases he a with h | h <;> rw [h] <;> simp
  rw [norm_mul, norm_prod, Finset.prod_congr rfl fun a _ => hn a] at m3
  exact chebToThreshold L f (2 * n + s) pl (fun a => ‖1 / t a - 1 / t' a‖) α β κ len ov be _ _ _
    hκ hlen hbt ho m3 le_rfl

end Formalism.FourierDecayAlt.P
