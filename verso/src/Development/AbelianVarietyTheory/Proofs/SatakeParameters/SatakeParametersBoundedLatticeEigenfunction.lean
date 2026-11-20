import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NcardSublatticesOfIndexPrimePowerLeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeOperatorAlternatingSeriesIdentityStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormLeOfRecurrenceGrowthStatement

noncomputable section

namespace GlobalTheory.SatakeBound

open GlobalTheory.LatHecke

/- English proof (translation)
Rewrite using `[Multiset.esymm, Multiset.esymm, Multiset.powersetCard_map, Multiset.map_map, ← Multiset.sum_map_mul_left]`. Use `congr 1`. Apply `Multiset.map_congr rfl` to reduce the goal to its premises. Introduce `t ht`. Rewrite `ht` using `[Multiset.mem_powersetCard]`.

Rewrite using `[Function.comp_apply]`. Use `Multiset.prod_map_mul (m := t) (f := fun _ => c) (g := fun x => x)` as an intermediate fact. Rewrite using `[this, Multiset.map_const', Multiset.prod_replicate, Multiset.map_id', ht.2]`.
-/
theorem esymm_map_mul (c : ℂ) (s : Multiset ℂ) (k : ℕ) :
    (s.map (fun x => c * x)).esymm k = c ^ k * s.esymm k := by
  rw [Multiset.esymm, Multiset.esymm, Multiset.powersetCard_map, Multiset.map_map,
    ← Multiset.sum_map_mul_left]
  congr 1
  apply Multiset.map_congr rfl
  intro t ht
  rw [Multiset.mem_powersetCard] at ht
  rw [Function.comp_apply]
  have := Multiset.prod_map_mul (m := t) (f := fun _ => c) (g := fun x => x)
  rw [this, Multiset.map_const', Multiset.prod_replicate, Multiset.map_id', ht.2]

noncomputable def recSeq (s : ℕ → ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => -∑ k ∈ Finset.range (n + 1), s (k + 1) * recSeq s (n - k)
decreasing_by all_goals omega

/- English proof (translation)
Break down `k with _ | j` into its components or cases. Simplify using the standard rewrite rules. Establish `h2 : 2 ∣ (j + 1) * j` using `by rw [mul_comm]; exact (Nat.even_mul_succ_self j).two_dvd`. Rewrite using `[Nat.add_sub_cancel, Nat.cast_div h2 (by norm_num)]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem cast_tri (k : ℕ) : (((k * (k - 1) / 2 : ℕ)) : ℝ) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
  rcases k with _ | j
  · simp
  · have h2 : 2 ∣ (j + 1) * j := by rw [mul_comm]; exact (Nat.even_mul_succ_self j).two_dvd
    rw [Nat.add_sub_cancel, Nat.cast_div h2 (by norm_num)]
    push_cast; ring

/- English proof (translation)
Introduce `O K _ _ _ _ _ _ _ r E _ _ φ α C hcard hφ hC hT x hx`. Establish `hq1 : (1 : ℝ) < (qRes O : ℝ)` using `by exact_mod_cast one_lt_qRes (O := O)`. Establish `hq0 : (0 : ℝ) < (qRes O : ℝ)` using `by linarith`. Break down `Nat.eq_zero_or_pos r with hr | hr` into its components or cases. Substitute `hr` using the available equality.

Rewrite `hcard` using `[Multiset.card_eq_zero]`. Substitute `hcard` using the available equality. Simplify using `at hx`. Choose the witnesses or unpack the hypotheses as in `⟨L0, hL0⟩ : ∃ L0, φ L0 ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Simplify using `only [ne_eq, not_exists, not_not] at h`. Conclude with `hφ (funext h)`. Use `set d : ℕ → ℂ := fun k => if k ≤ r then (((qRes O : ℝ) ^ ((k : ℝ) * ((r : ℝ) - k) / 2) : ℝ) : ℂ) * α.esymm k else 0 with hd_def`. Establish `hd : ∀ k L, heckeElem k φ L = d k • φ L`. Introduce `k L`.

Distinguish the cases in `hk : k ≤ r`. Rewrite using `[hT k hk L, hd_def]`. Simplify using `only [hk, if_true]`. Rewrite using `[heckeElem_eq_zero (by omega), hd_def]; simp only [hk, if_false, zero_smul]`. Establish `hlin : ∀ (c : ℂ) k L, heckeElem k (fun M => c • φ M) L = (c * d k) • φ L`.

Introduce `c k L`. Rewrite using `[heckeElem_eq_sum, ← Finset.smul_sum, ← heckeElem_eq_sum, hd, smul_smul]`. Use `set s : ℕ → ℂ := fun k => (-1 : ℂ) ^ k * (qRes O : ℂ) ^ (k * (k - 1) / 2) * d k with hs_def`. Use `set a : ℕ → ℂ := recSeq s with ha_def`. Establish `hA : ∀ n, heckeAll n φ = fun L => a n • φ L`.

Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Break down `n with _ | m` into its components or cases. Use function extensionality and compare the values at `L`.

Rewrite using `[heckeAll_zero, ha_def, recSeq, one_smul]`. Use function extensionality and compare the values at `L`. Establish `hid` using `GlobalTheory.T.heckeOperator_alternating_series_identity O K r E φ (m + 1) L (by omega)`. Rewrite `hid` using `[Finset.sum_range_succ']`. Establish `key : ∀ k ∈ Finset.range (m + 1), ((-1 : ℂ) ^ (k + 1) * (qRes O : ℂ) ^ ((k + 1) * (k + 1 - 1) / 2)) • heckeElem (k + 1) (heckeAll (m + 1 - (k + 1)) φ) L = (s (k + 1) * a (m - k)) • φ L`.

Introduce `k hk`. Rewrite using `[show m + 1 - (k + 1) = m - k by omega, ih (m - k) (by omega), hlin, smul_smul]`. Use `congr 1`. Rewrite using `[hs_def]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h0 : ((-1 : ℂ) ^ 0 * (qRes O : ℂ) ^ (0 * (0 - 1) / 2)) = 1` using `by simp`. Rewrite `hid` using `[Finset.sum_congr rfl key, h0, one_smul, heckeElem_zero, ← Finset.sum_smul]`. Use `show heckeAll (m + 1) φ L = recSeq s (m + 1) • φ L`. Rewrite using `[recSeq, neg_smul]`. Conclude with `eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hid)`.

Use `set c : ℝ := (qRes O : ℝ) ^ (((r : ℝ) - 1) / 2) with hc_def`. Establish `hc0 : 0 < c` using `Real.rpow_pos_of_pos hq0 _`. Use `set β : Multiset ℂ := α.map (fun y => (c : ℂ) * y) with hβ_def`. Establish `hβs : ∀ k, (-1 : ℂ) ^ k * β.esymm k = s k`. Introduce `k`.

Rewrite using `[hβ_def, esymm_map_mul, hs_def, hd_def]`. Distinguish the cases in `hk : k ≤ r`. Simplify using `only [hk, if_true]`. Establish `hreal : c ^ k = (qRes O : ℝ) ^ (k * (k - 1) / 2) * (qRes O : ℝ) ^ ((k : ℝ) * ((r : ℝ) - k) / 2)`. Rewrite using `[hc_def, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le, ← Real.rpow_natCast (qRes O : ℝ), ← Real.rpow_add hq0, cast_tri]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hcomp : (c : ℂ) ^ k = (qRes O : ℂ) ^ (k * (k - 1) / 2) * (((qRes O : ℝ) ^ ((k : ℝ) * ((r : ℝ) - k) / 2) : ℝ) : ℂ)`. Rewrite using `[← Complex.ofReal_pow, hreal, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast]`. Rewrite using `[hcomp]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hk, if_false, mul_zero]`. Rewrite using `[Multiset.esymm, Multiset.powersetCard_eq_empty _ (by rw [hcard]; omega)]`. Simplify using the standard rewrite rules. Establish `hrel : ∀ n, 1 ≤ n → ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * β.esymm k * a (n - k) = 0`.

Introduce `n hn`. Take `⟨m, rfl⟩ : ∃ m, n = m + 1` from `⟨n - 1, by omega⟩`. Simplify using `only [hβs]`. Rewrite using `[Finset.sum_range_succ']`. Establish `hs0 : s 0 = 1`.

Rewrite using `[hs_def, hd_def]`. Simplify using `[Multiset.esymm, Multiset.powersetCard_zero_left]`. Establish `ha1 : a (m + 1 - 0) = -∑ k ∈ Finset.range (m + 1), s (k + 1) * a (m - k)`. Rewrite using `[Nat.sub_zero, ha_def, recSeq]`. Rewrite using `[hs0, ha1]`.

Establish `: ∀ k ∈ Finset.range (m + 1), s (k + 1) * a (m + 1 - (k + 1)) = s (k + 1) * a (m - k)`. Introduce `k _; rw [show m + 1 - (k + 1) = m - k by omega]`. Rewrite using `[Finset.sum_congr rfl this]`. Expand and normalize the polynomial expressions, which then agree. Establish `hC0 : 0 ≤ C` using `le_trans (norm_nonneg _) (hC L0)`.

Establish `hnL0 : 0 < ‖φ L0‖` using `norm_pos_iff.mpr hL0`. Establish `hbound : ∀ n, ‖a n‖ ≤ (C / ‖φ L0‖) * ((n : ℝ) + 1) ^ r * ((qRes O : ℝ) ^ (r - 1)) ^ n`. Introduce `n`. Establish `h1 : ‖a n‖ * ‖φ L0‖ = ‖heckeAll n φ L0‖`. Rewrite using `[hA n, norm_smul]`.

Establish `h2 : ‖heckeAll n φ L0‖ ≤ (subIdx n L0).ncard * C`. Rewrite using `[heckeAll_eq_sum, Set.ncard_eq_toFinset_card _ (subIdx_finite n L0)]`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Use `(Finset.sum_le_sum fun M _ => hC M).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_const, nsmul_eq_mul]`.

Establish `h3` using `GlobalTheory.T.ncard_sublatticesOfIndexPrimePower_le O K r n L0`. Rewrite using `[show C / ‖φ L0‖ * ((n : ℝ) + 1) ^ r * ((qRes O : ℝ) ^ (r - 1)) ^ n = C * (((n : ℝ) + 1) ^ r * ((qRes O : ℝ) ^ (r - 1)) ^ n) / ‖φ L0‖ by ring, le_div_iff₀ hnL0, h1]`. Combine the equalities or inequalities in the displayed calculation. Establish `hB : 0 < (qRes O : ℝ) ^ (r - 1)` using `pow_pos hq0 _`. Establish `hrec` using `GlobalTheory.T.norm_le_of_recurrence_growth' β a (C / ‖φ L0‖) ((qRes O : ℝ) ^ (r - 1)) r hB (by rw [ha_def, recSeq]) hrel hbound`.

Establish `hxb` using `hrec ((c : ℂ) * x) (Multiset.mem_map_of_mem _ hx)`. Rewrite `hxb` using `[norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0.le]`. Establish `hcc : (qRes O : ℝ) ^ (r - 1) = c * c`. Rewrite using `[hc_def, ← Real.rpow_add hq0, ← Real.rpow_natCast, Nat.cast_sub hr]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hxb` using `[hcc]`. Conclude with `le_of_mul_le_mul_left hxb hc0`.
-/
theorem main : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (φ : Lat O K r → E) (α : Multiset ℂ)
    (C : ℝ), α.card = r → φ ≠ 0 → (∀ L, ‖φ L‖ ≤ C) →
    (∀ k ≤ r, ∀ L, heckeElem k φ L =
      ((((qRes O : ℝ) ^ ((k : ℝ) * ((r : ℝ) - k) / 2) : ℝ) : ℂ) * α.esymm k) • φ L) →
    ∀ a ∈ α, ‖a‖ ≤ (qRes O : ℝ) ^ (((r : ℝ) - 1) / 2) := by
  intro O K _ _ _ _ _ _ _ r E _ _ φ α C hcard hφ hC hT x hx
  have hq1 : (1 : ℝ) < (qRes O : ℝ) := by exact_mod_cast one_lt_qRes (O := O)
  have hq0 : (0 : ℝ) < (qRes O : ℝ) := by linarith
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    rw [Multiset.card_eq_zero] at hcard
    subst hcard
    simp at hx
  obtain ⟨L0, hL0⟩ : ∃ L0, φ L0 ≠ 0 := by
    by_contra h
    simp only [ne_eq, not_exists, not_not] at h
    exact hφ (funext h)

  set d : ℕ → ℂ := fun k => if k ≤ r then
    (((qRes O : ℝ) ^ ((k : ℝ) * ((r : ℝ) - k) / 2) : ℝ) : ℂ) * α.esymm k else 0 with hd_def
  have hd : ∀ k L, heckeElem k φ L = d k • φ L := by
    intro k L
    by_cases hk : k ≤ r
    · rw [hT k hk L, hd_def]; simp only [hk, if_true]
    · rw [heckeElem_eq_zero (by omega), hd_def]; simp only [hk, if_false, zero_smul]
  have hlin : ∀ (c : ℂ) k L, heckeElem k (fun M => c • φ M) L = (c * d k) • φ L := by
    intro c k L
    rw [heckeElem_eq_sum, ← Finset.smul_sum, ← heckeElem_eq_sum, hd, smul_smul]
  set s : ℕ → ℂ := fun k => (-1 : ℂ) ^ k * (qRes O : ℂ) ^ (k * (k - 1) / 2) * d k with hs_def
  set a : ℕ → ℂ := recSeq s with ha_def

  have hA : ∀ n, heckeAll n φ = fun L => a n • φ L := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    rcases n with _ | m
    · funext L
      rw [heckeAll_zero, ha_def, recSeq, one_smul]
    · funext L
      have hid := GlobalTheory.T.heckeOperator_alternating_series_identity O K r E φ (m + 1) L (by omega)
      rw [Finset.sum_range_succ'] at hid
      have key : ∀ k ∈ Finset.range (m + 1),
          ((-1 : ℂ) ^ (k + 1) * (qRes O : ℂ) ^ ((k + 1) * (k + 1 - 1) / 2)) •
            heckeElem (k + 1) (heckeAll (m + 1 - (k + 1)) φ) L = (s (k + 1) * a (m - k)) • φ L := by
        intro k hk
        rw [show m + 1 - (k + 1) = m - k by omega, ih (m - k) (by omega), hlin, smul_smul]
        congr 1
        rw [hs_def]
        ring
      have h0 : ((-1 : ℂ) ^ 0 * (qRes O : ℂ) ^ (0 * (0 - 1) / 2)) = 1 := by simp
      rw [Finset.sum_congr rfl key, h0, one_smul, heckeElem_zero, ← Finset.sum_smul] at hid
      show heckeAll (m + 1) φ L = recSeq s (m + 1) • φ L
      rw [recSeq, neg_smul]
      exact eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hid)

  set c : ℝ := (qRes O : ℝ) ^ (((r : ℝ) - 1) / 2) with hc_def
  have hc0 : 0 < c := Real.rpow_pos_of_pos hq0 _
  set β : Multiset ℂ := α.map (fun y => (c : ℂ) * y) with hβ_def
  have hβs : ∀ k, (-1 : ℂ) ^ k * β.esymm k = s k := by
    intro k
    rw [hβ_def, esymm_map_mul, hs_def, hd_def]
    by_cases hk : k ≤ r
    · simp only [hk, if_true]
      have hreal : c ^ k = (qRes O : ℝ) ^ (k * (k - 1) / 2) *
          (qRes O : ℝ) ^ ((k : ℝ) * ((r : ℝ) - k) / 2) := by
        rw [hc_def, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le, ← Real.rpow_natCast (qRes O : ℝ),
          ← Real.rpow_add hq0, cast_tri]
        congr 1
        ring
      have hcomp : (c : ℂ) ^ k = (qRes O : ℂ) ^ (k * (k - 1) / 2) *
          (((qRes O : ℝ) ^ ((k : ℝ) * ((r : ℝ) - k) / 2) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_pow, hreal, Complex.ofReal_mul, Complex.ofReal_pow,
          Complex.ofReal_natCast]
      rw [hcomp]
      ring
    · simp only [hk, if_false, mul_zero]
      rw [Multiset.esymm, Multiset.powersetCard_eq_empty _ (by rw [hcard]; omega)]
      simp
  have hrel : ∀ n, 1 ≤ n → ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * β.esymm k * a (n - k) = 0 := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [hβs]
    rw [Finset.sum_range_succ']
    have hs0 : s 0 = 1 := by
      rw [hs_def, hd_def]; simp [Multiset.esymm, Multiset.powersetCard_zero_left]
    have ha1 : a (m + 1 - 0) = -∑ k ∈ Finset.range (m + 1), s (k + 1) * a (m - k) := by
      rw [Nat.sub_zero, ha_def, recSeq]
    rw [hs0, ha1]
    have : ∀ k ∈ Finset.range (m + 1), s (k + 1) * a (m + 1 - (k + 1)) = s (k + 1) * a (m - k) := by
      intro k _; rw [show m + 1 - (k + 1) = m - k by omega]
    rw [Finset.sum_congr rfl this]
    ring

  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC L0)
  have hnL0 : 0 < ‖φ L0‖ := norm_pos_iff.mpr hL0
  have hbound : ∀ n, ‖a n‖ ≤ (C / ‖φ L0‖) * ((n : ℝ) + 1) ^ r * ((qRes O : ℝ) ^ (r - 1)) ^ n := by
    intro n
    have h1 : ‖a n‖ * ‖φ L0‖ = ‖heckeAll n φ L0‖ := by
      rw [hA n, norm_smul]
    have h2 : ‖heckeAll n φ L0‖ ≤ (subIdx n L0).ncard * C := by
      rw [heckeAll_eq_sum, Set.ncard_eq_toFinset_card _ (subIdx_finite n L0)]
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun M _ => hC M).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
    have h3 := GlobalTheory.T.ncard_sublatticesOfIndexPrimePower_le O K r n L0
    rw [show C / ‖φ L0‖ * ((n : ℝ) + 1) ^ r * ((qRes O : ℝ) ^ (r - 1)) ^ n =
        C * (((n : ℝ) + 1) ^ r * ((qRes O : ℝ) ^ (r - 1)) ^ n) / ‖φ L0‖ by ring,
      le_div_iff₀ hnL0, h1]
    calc ‖heckeAll n φ L0‖ ≤ (subIdx n L0).ncard * C := h2
      _ ≤ (((n : ℝ) + 1) ^ r * ((qRes O : ℝ) ^ (r - 1)) ^ n) * C :=
          mul_le_mul_of_nonneg_right h3 hC0
      _ = C * (((n : ℝ) + 1) ^ r * ((qRes O : ℝ) ^ (r - 1)) ^ n) := by ring
  have hB : 0 < (qRes O : ℝ) ^ (r - 1) := pow_pos hq0 _
  have hrec := GlobalTheory.T.norm_le_of_recurrence_growth' β a (C / ‖φ L0‖) ((qRes O : ℝ) ^ (r - 1)) r hB
    (by rw [ha_def, recSeq]) hrel hbound
  have hxb := hrec ((c : ℂ) * x) (Multiset.mem_map_of_mem _ hx)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0.le] at hxb
  have hcc : (qRes O : ℝ) ^ (r - 1) = c * c := by
    rw [hc_def, ← Real.rpow_add hq0, ← Real.rpow_natCast, Nat.cast_sub hr]
    congr 1
    push_cast
    ring
  rw [hcc] at hxb
  exact le_of_mul_le_mul_left hxb hc0

end GlobalTheory.SatakeBound
