import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialLipschitzCoefficientBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalPointsDenseInWallStatement

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4

noncomputable section

namespace GlobalTheory.Mean4

variable {D : D7} {Y : ShimX D.what₂.Tau}

def wallPt (u : Wt Y) (s : ℝ) : Option (D.what₂.Tau × Fin Y.N) → ℝ := fun o => o.elim s (fun x => u x.1 x.2)

/- English proof (translation)
Use `(pi_norm_le_iff_of_nonneg (by norm_num)).2 ?_` and prove the remaining obligations. Introduce and unpack `(_ | x)`. Simplify using `[wallPt]`. Simplify `hu x.1 x.2` using `[wallPt]`.
-/
theorem wallPt_norm_le (u : Wt Y) (hu : ∀ τ i, |u τ i| ≤ 1 / 2) : ‖wallPt u 0‖ ≤ 1 / 2 := by
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 ?_
  rintro (_ | x)
  · simp [wallPt]
  · simpa [wallPt] using hu x.1 x.2

/- English proof (translation)
Establish `hK : 0 ≤ ‖A.dir‖` using `norm_nonneg _`. Establish `ht2 : t ^ 2 ≤ t` using `by nlinarith`. Establish `ht0 : 0 ≤ t ^ 2` using `sq_nonneg t`. Use `(pi_norm_le_iff_of_nonneg (by positivity)).2 ?_` and prove the remaining obligations. Introduce and unpack `(_ | x)`.

Simplify using `only [wallPt, Pi.sub_apply, Option.elim, sub_zero, Real.norm_eq_abs, abs_of_nonneg ht0]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hd : |A.dir x.1 x.2| ≤ ‖A.dir‖` using `le_trans (norm_le_pi_norm (A.dir x.1) x.2) (norm_le_pi_norm A.dir x.1)`. Establish `hd'` using `abs_le.1 hd`. Establish `h3 : t ^ 2 * A.dir x.1 x.2 ≤ t * ‖A.dir‖` using `by nlinarith`.

Establish `h4 : -(t * ‖A.dir‖) ≤ t ^ 2 * A.dir x.1 x.2` using `by nlinarith`. Simplify using `only [wallPt, Pi.sub_apply, Option.elim, Real.norm_eq_abs, SlopeTestRemainingChoices.sh, offWall]`. Apply the tactic sequence `split_ifs <;> (rw [abs_le]; constructor <;> nlinarith)`.
-/
theorem wallPt_sub_norm_le (A : SlopeTestRemainingChoices Y) (τ₀ : D.what₂.Tau) (u : Wt Y) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    ‖wallPt (A.sh (offWall Y τ₀ t u) (t ^ 2)) (t ^ 2) - wallPt u 0‖ ≤ (3 + ‖A.dir‖) * t := by
  have hK : 0 ≤ ‖A.dir‖ := norm_nonneg _
  have ht2 : t ^ 2 ≤ t := by nlinarith
  have ht0 : 0 ≤ t ^ 2 := sq_nonneg t
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 ?_
  rintro (_ | x)
  · simp only [wallPt, Pi.sub_apply, Option.elim, sub_zero, Real.norm_eq_abs, abs_of_nonneg ht0]
    nlinarith
  · have hd : |A.dir x.1 x.2| ≤ ‖A.dir‖ :=
      le_trans (norm_le_pi_norm (A.dir x.1) x.2) (norm_le_pi_norm A.dir x.1)
    have hd' := abs_le.1 hd
    have h3 : t ^ 2 * A.dir x.1 x.2 ≤ t * ‖A.dir‖ := by nlinarith
    have h4 : -(t * ‖A.dir‖) ≤ t ^ 2 * A.dir x.1 x.2 := by nlinarith
    simp only [wallPt, Pi.sub_apply, Option.elim, Real.norm_eq_abs, SlopeTestRemainingChoices.sh, offWall]
    split_ifs <;> (rw [abs_le]; constructor <;> nlinarith)

/- English proof (translation)
Use `(MvPolynomial.continuous_eval P).comp (f := fun u : Wt Y => wallPt u 0) ?_` and prove the remaining obligations. Use `continuous_pi ?_` and prove the remaining obligations. Introduce and unpack `(_ | x)`. Conclude with `continuous_const`. Conclude with `(continuous_apply x.2).comp (continuous_apply x.1)`.
-/
theorem continuous_evS (P : MvPolynomial (Option (D.what₂.Tau × Fin Y.N)) ℝ) :
    Continuous fun u : Wt Y => evS Y P u 0 := by
  refine (MvPolynomial.continuous_eval P).comp (f := fun u : Wt Y => wallPt u 0) ?_
  refine continuous_pi ?_
  rintro (_ | x)
  · exact continuous_const
  · exact (continuous_apply x.2).comp (continuous_apply x.1)

/- English proof (translation)
Introduce `D Y A Φ hf ⟨C1, h1⟩ hA ⟨Cw, B1, hw⟩`. Take `⟨s₀, hs₀, Ca, hA⟩` from `hA 1`. Take `⟨n, hn, hL⟩` from `GlobalTheory.T.polynomial_lipschitz_coefficient_bound (Option (D.what₂.Tau × Fin Y.N)) (dimY Y + 1)`. Establish `hK : 0 ≤ ‖A.dir‖` using `norm_nonneg _`. Establish `hf0 : 0 < D.R.f`.

Break down `Nat.eq_zero_or_pos D.R.f with h | h` into its components or cases. Rewrite `hf` using `[h]`. Simplify using `at hf`. Conclude with `h`. Establish `hfR : (0 : ℝ) < D.R.f` using `by exact_mod_cast hf0`.

Use `set K := ‖A.dir‖ with hKdef`. Use `set κ : ℝ := 5 * (D.R.f : ℝ) with hκ`. Establish `hκ0 : 0 < κ` using `by positivity`. Use `set δ : ℝ := min s₀ (1 / (2 * (3 + K))) with hδ`. Establish `hδ0 : 0 < δ` using `lt_min hs₀ (by positivity)`.

Take `⟨B2, hB2⟩` from `exists_nat_ge (κ / δ)`. Use `⟨Cw + (Fintype.card Y.Comp : ℝ) * (|Ca| * κ ^ 2 + n * |C1| * (3 + K) * κ), max B1 (max B2 3), ?_⟩` and prove the remaining obligations. Introduce `B hB τ₀ u hu`. Establish `hB1 : B1 ≤ B` using `le_trans (le_max_left _ _) hB`. Establish `hB2' : B2 ≤ B` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hB`.

Establish `hB3 : 3 ≤ B` using `le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hB`. Establish `hB3R : (3 : ℝ) ≤ B` using `by exact_mod_cast hB3`. Establish `hBpos : (0 : ℝ) < B` using `by linarith`. Establish `hlog : 1 ≤ Real.log B`. Rewrite using `[Real.le_log_iff_exp_le hBpos]`.

Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨hP, hsum⟩` from `h1 B (by linarith)`. Establish `hcont : Continuous fun u : Wt Y => atWt Y (Φ B) u`. Establish `: (fun u : Wt Y => atWt Y (Φ B) u) = fun u => ∑ c, evS Y (A.Ps B c) u 0` using `funext fun u => (hsum u).symm`.

Rewrite using `[this]`. Conclude with `continuous_finset_sum _ fun c _ => continuous_evS _`. Establish `hcl` using `GlobalTheory.T.rational_points_dense_in_wall D.what₂.Tau Y.N Y.j τ₀ Y.j_pos Y.j_lt hu`. Use `closure_minimal ?_ (isClosed_le hcont.abs continuous_const) hcl` and prove the remaining obligations. Use `clear hcl hu u`.

Introduce and unpack `u ⟨hu, hrat⟩`. Take `⟨hdom, hsmall⟩` from `hw B hB1 τ₀ u hu hrat _ rfl`. Use `set t : ℚ := 5 * (D.R.f : ℚ) / B with ht`. Establish `htR : (t : ℝ) = κ / B` using `by rw [ht, hκ]; push_cast; ring`. Establish `ht0 : (0 : ℝ) < t` using `by rw [htR]; positivity`.

Establish `htδ : (t : ℝ) ≤ δ`. Rewrite using `[htR, div_le_iff₀ hBpos]`. Establish `h2 : κ / δ ≤ B` using `le_trans hB2 (by exact_mod_cast hB2')`. Rewrite `h2` using `[div_le_iff₀ hδ0]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hts : (t : ℝ) ≤ s₀` using `le_trans htδ (min_le_left _ _)`. Establish `htK : (3 + K) * t ≤ 1 / 2`. Establish `h2 : (t : ℝ) ≤ 1 / (2 * (3 + K))` using `le_trans htδ (min_le_right _ _)`. Rewrite `h2` using `[le_div_iff₀ (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `ht1 : (t : ℝ) ≤ 1 / 6` using `by nlinarith`. Establish `hrat' : IsRat Y (offWall Y τ₀ t u)`. Introduce `τ i`. Take `⟨q, hq⟩` from `hrat τ i`. Simplify using `only [offWall]`.

Use `split_ifs`. Conclude with `⟨q + 2 * t, by rw [hq]; push_cast; ring⟩`. Conclude with `⟨q, by rw [hq]; simp⟩`. Establish `hsup : supAbs Y (offWall Y τ₀ t u) ≤ 1`. Use `Real.iSup_le ?_ zero_le_one` and prove the remaining obligations.

Introduce `x`. Use `abs_le.1 (hu.1 x.1 x.2)` as an intermediate fact. Simplify using `only [offWall]`. Apply the tactic sequence `split_ifs <;> (rw [abs_le]; constructor <;> linarith)`. Establish `hag` using `hA B (by linarith) (offWall Y τ₀ t u) (t ^ 2) hrat' hsup (by have : (0 : ℚ) < t := by exact_mod_cast ht0 positivity) (by push_cast; nlinarith) (by push_cast; exact hdom)`.

Move the coercions through the operations in `at hag`. Establish `hdiff` using `wallPt_sub_norm_le A τ₀ u t ht0.le (by linarith)`. Establish `hb` using `wallPt_norm_le u hu.1`. Establish `ha : ‖wallPt (A.sh (offWall Y τ₀ t u) ((t : ℝ) ^ 2)) ((t : ℝ) ^ 2)‖ ≤ 1`. Use `norm_le_norm_add_norm_sub' (wallPt (A.sh (offWall Y τ₀ t u) ((t : ℝ) ^ 2)) ((t : ℝ) ^ 2)) (wallPt u 0)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hc : ∀ c, |evS Y (A.Ps B c) u 0 - Y.arSelfC (Y.Mbar B (offWall Y τ₀ t u) (t ^ 2)) c| ≤ (|Ca| * κ ^ 2 + n * |C1| * (3 + K) * κ) * Real.log B / B`. Introduce `c`. Establish `e1` using `hag c`. Establish `e2 : |evS Y (A.Ps B c) (A.sh (offWall Y τ₀ t u) ((t : ℝ) ^ 2)) ((t : ℝ) ^ 2) - evS Y (A.Ps B c) u 0| ≤ _` using `hL (A.Ps B c) (|C1| * Real.log B) _ _ (hP c).1 (fun m => le_trans ((hP c).2 m) (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith))) ha (le_trans hb (by norm_num))`.

Establish `e3 : n * (|C1| * Real.log B) * ‖wallPt (A.sh (offWall Y τ₀ t u) ((t : ℝ) ^ 2)) ((t : ℝ) ^ 2) - wallPt u 0‖ ≤ n * |C1| * (3 + K) * κ * Real.log B / B`. Use `le_trans (mul_le_mul_of_nonneg_left hdiff (by positivity)) (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[htR]`. Expand and normalize the polynomial expressions, which then agree. Establish `e4 : Ca * (t : ℝ) ^ 2 ≤ |Ca| * κ ^ 2 * Real.log B / B`.

Use `le_trans (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)) ?_` and prove the remaining obligations. Establish `e5 : (1 : ℝ) / B ≤ Real.log B` using `le_trans (by rw [div_le_one hBpos]; linarith) hlog`. Combine the equalities or inequalities in the displayed calculation. Establish `e6` using `abs_le.1 (le_trans e1 e4)`. Establish `e7` using `abs_le.1 (le_trans e2 e3)`.

Rewrite using `[add_mul, add_div, abs_le]`. Apply the tactic sequence `constructor <;> linarith`. Establish `hs : |atWt Y (Φ B) u - Y.arSelf (Y.Mbar B (offWall Y τ₀ t u) (t ^ 2))| ≤ (Fintype.card Y.Comp : ℝ) * ((|Ca| * κ ^ 2 + n * |C1| * (3 + K) * κ) * Real.log B / B)`. Rewrite using `[← hsum u, Y.arSelf_sum, ← Finset.sum_sub_distrib]`. Use `le_trans (Finset.abs_sum_le_sum_abs _ _) ?_` and prove the remaining obligations.

Use `le_trans (Finset.sum_le_sum fun c _ => hc c) ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Use `show |atWt Y (Φ B) u| ≤ _`. Establish `e8` using `abs_le.1 hs`. Establish `e9` using `abs_le.1 hsmall`.

Establish `e10 : (Cw + (Fintype.card Y.Comp : ℝ) * (|Ca| * κ ^ 2 + n * |C1| * (3 + K) * κ)) * Real.log B / B = Cw * Real.log B / B + (Fintype.card Y.Comp : ℝ) * ((|Ca| * κ ^ 2 + n * |C1| * (3 + K) * κ) * Real.log B / B)` using `by ring`. Rewrite using `[e10, abs_le]`. Apply the tactic sequence `constructor <;> linarith`.
-/
theorem wallBd_of_wallSmall : ∀ (D : D7) (Y : ShimX D.what₂.Tau), ∀ (A : SlopeTestRemainingChoices Y), ∀ (Φ : ℝ → Fn Y),
    2 < D.R.f * (Y.N - 1) → PolySize A Φ → Agree A → WallSmall A → WallBd Φ := by
  intro D Y A Φ hf ⟨C1, h1⟩ hA ⟨Cw, B1, hw⟩
  obtain ⟨s₀, hs₀, Ca, hA⟩ := hA 1
  obtain ⟨n, hn, hL⟩ := GlobalTheory.T.polynomial_lipschitz_coefficient_bound (Option (D.what₂.Tau × Fin Y.N)) (dimY Y + 1)
  have hK : 0 ≤ ‖A.dir‖ := norm_nonneg _
  have hf0 : 0 < D.R.f := by
    rcases Nat.eq_zero_or_pos D.R.f with h | h
    · rw [h] at hf; simp at hf
    · exact h
  have hfR : (0 : ℝ) < D.R.f := by exact_mod_cast hf0
  set K := ‖A.dir‖ with hKdef
  set κ : ℝ := 5 * (D.R.f : ℝ) with hκ
  have hκ0 : 0 < κ := by positivity
  set δ : ℝ := min s₀ (1 / (2 * (3 + K))) with hδ
  have hδ0 : 0 < δ := lt_min hs₀ (by positivity)
  obtain ⟨B2, hB2⟩ := exists_nat_ge (κ / δ)
  refine ⟨Cw + (Fintype.card Y.Comp : ℝ) * (|Ca| * κ ^ 2 + n * |C1| * (3 + K) * κ), max B1 (max B2 3), ?_⟩
  intro B hB τ₀ u hu
  have hB1 : B1 ≤ B := le_trans (le_max_left _ _) hB
  have hB2' : B2 ≤ B := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hB
  have hB3 : 3 ≤ B := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hB
  have hB3R : (3 : ℝ) ≤ B := by exact_mod_cast hB3
  have hBpos : (0 : ℝ) < B := by linarith
  have hlog : 1 ≤ Real.log B := by
    rw [Real.le_log_iff_exp_le hBpos]
    have := Real.exp_one_lt_d9
    linarith
  obtain ⟨hP, hsum⟩ := h1 B (by linarith)
  have hcont : Continuous fun u : Wt Y => atWt Y (Φ B) u := by
    have : (fun u : Wt Y => atWt Y (Φ B) u) = fun u => ∑ c, evS Y (A.Ps B c) u 0 := funext fun u => (hsum u).symm
    rw [this]
    exact continuous_finset_sum _ fun c _ => continuous_evS _
  have hcl := GlobalTheory.T.rational_points_dense_in_wall D.what₂.Tau Y.N Y.j τ₀ Y.j_pos Y.j_lt hu
  refine closure_minimal ?_ (isClosed_le hcont.abs continuous_const) hcl
  clear hcl hu u
  rintro u ⟨hu, hrat⟩
  obtain ⟨hdom, hsmall⟩ := hw B hB1 τ₀ u hu hrat _ rfl
  set t : ℚ := 5 * (D.R.f : ℚ) / B with ht
  have htR : (t : ℝ) = κ / B := by rw [ht, hκ]; push_cast; ring
  have ht0 : (0 : ℝ) < t := by rw [htR]; positivity
  have htδ : (t : ℝ) ≤ δ := by
    rw [htR, div_le_iff₀ hBpos]
    have h2 : κ / δ ≤ B := le_trans hB2 (by exact_mod_cast hB2')
    rw [div_le_iff₀ hδ0] at h2
    linarith
  have hts : (t : ℝ) ≤ s₀ := le_trans htδ (min_le_left _ _)
  have htK : (3 + K) * t ≤ 1 / 2 := by
    have h2 : (t : ℝ) ≤ 1 / (2 * (3 + K)) := le_trans htδ (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h2
    linarith
  have ht1 : (t : ℝ) ≤ 1 / 6 := by nlinarith
  have hrat' : IsRat Y (offWall Y τ₀ t u) := by
    intro τ i
    obtain ⟨q, hq⟩ := hrat τ i
    simp only [offWall]
    split_ifs
    · exact ⟨q + 2 * t, by rw [hq]; push_cast; ring⟩
    · exact ⟨q, by rw [hq]; simp⟩
  have hsup : supAbs Y (offWall Y τ₀ t u) ≤ 1 := by
    refine Real.iSup_le ?_ zero_le_one
    intro x
    have := abs_le.1 (hu.1 x.1 x.2)
    simp only [offWall]
    split_ifs <;> (rw [abs_le]; constructor <;> linarith)
  have hag := hA B (by linarith) (offWall Y τ₀ t u) (t ^ 2) hrat' hsup
    (by have : (0 : ℚ) < t := by exact_mod_cast ht0
        positivity)
    (by push_cast; nlinarith) (by push_cast; exact hdom)
  push_cast at hag
  have hdiff := wallPt_sub_norm_le A τ₀ u t ht0.le (by linarith)
  have hb := wallPt_norm_le u hu.1
  have ha : ‖wallPt (A.sh (offWall Y τ₀ t u) ((t : ℝ) ^ 2)) ((t : ℝ) ^ 2)‖ ≤ 1 := by
    have := norm_le_norm_add_norm_sub' (wallPt (A.sh (offWall Y τ₀ t u) ((t : ℝ) ^ 2)) ((t : ℝ) ^ 2)) (wallPt u 0)
    linarith
  have hc : ∀ c, |evS Y (A.Ps B c) u 0 - Y.arSelfC (Y.Mbar B (offWall Y τ₀ t u) (t ^ 2)) c| ≤
      (|Ca| * κ ^ 2 + n * |C1| * (3 + K) * κ) * Real.log B / B := by
    intro c
    have e1 := hag c
    have e2 : |evS Y (A.Ps B c) (A.sh (offWall Y τ₀ t u) ((t : ℝ) ^ 2)) ((t : ℝ) ^ 2) - evS Y (A.Ps B c) u 0| ≤ _ :=
      hL (A.Ps B c) (|C1| * Real.log B) _ _ (hP c).1
        (fun m => le_trans ((hP c).2 m) (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith))) ha
        (le_trans hb (by norm_num))
    have e3 : n * (|C1| * Real.log B) * ‖wallPt (A.sh (offWall Y τ₀ t u) ((t : ℝ) ^ 2)) ((t : ℝ) ^ 2) - wallPt u 0‖ ≤
        n * |C1| * (3 + K) * κ * Real.log B / B := by
      refine le_trans (mul_le_mul_of_nonneg_left hdiff (by positivity)) (le_of_eq ?_)
      rw [htR]; ring
    have e4 : Ca * (t : ℝ) ^ 2 ≤ |Ca| * κ ^ 2 * Real.log B / B := by
      refine le_trans (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)) ?_
      have e5 : (1 : ℝ) / B ≤ Real.log B := le_trans (by rw [div_le_one hBpos]; linarith) hlog
      calc |Ca| * (t : ℝ) ^ 2 = |Ca| * κ ^ 2 * (1 / B) / B := by rw [htR]; ring
        _ ≤ _ := by gcongr
    have e6 := abs_le.1 (le_trans e1 e4)
    have e7 := abs_le.1 (le_trans e2 e3)
    rw [add_mul, add_div, abs_le]
    constructor <;> linarith
  have hs : |atWt Y (Φ B) u - Y.arSelf (Y.Mbar B (offWall Y τ₀ t u) (t ^ 2))| ≤
      (Fintype.card Y.Comp : ℝ) * ((|Ca| * κ ^ 2 + n * |C1| * (3 + K) * κ) * Real.log B / B) := by
    rw [← hsum u, Y.arSelf_sum, ← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum fun c _ => hc c) ?_
    simp
  show |atWt Y (Φ B) u| ≤ _
  have e8 := abs_le.1 hs
  have e9 := abs_le.1 hsmall
  have e10 : (Cw + (Fintype.card Y.Comp : ℝ) * (|Ca| * κ ^ 2 + n * |C1| * (3 + K) * κ)) * Real.log B / B =
      Cw * Real.log B / B +
        (Fintype.card Y.Comp : ℝ) * ((|Ca| * κ ^ 2 + n * |C1| * (3 + K) * κ) * Real.log B / B) := by ring
  rw [e10, abs_le]
  constructor <;> linarith

end GlobalTheory.Mean4
