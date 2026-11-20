import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeOperatorAlternatingSeriesIdentityStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementarySublatticesOfIndexDegreesQBinomialStatement

noncomputable section

open GlobalTheory.LatHecke

namespace GlobalTheory.SubIdxCount

noncomputable def hc (q : ℕ) : ℕ → ℕ → ℕ
  | 0, n => if n = 0 then 1 else 0
  | r + 1, n => ∑ k ∈ Finset.range (n + 1), hc q r k * q ^ (r * (n - k))

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem hc_zero_right (q r : ℕ) : hc q r 0 = 1 := by
  induction r with
  | zero => simp [hc]
  | succ r ih => simp [hc, ih]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules. Chain the equalities or inequalities of the calculation.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem hc_le (q : ℕ) (hq : 1 ≤ q) (r n : ℕ) : hc q r n ≤ (n + 1) ^ r * (q ^ (r - 1)) ^ n := by
  induction r generalizing n with
  | zero => simp only [hc]; split_ifs <;> simp
  | succ r ih =>
    simp only [hc]
    calc ∑ k ∈ Finset.range (n + 1), hc q r k * q ^ (r * (n - k))
        ≤ ∑ k ∈ Finset.range (n + 1), (n + 1) ^ r * q ^ (r * n) := by
          apply Finset.sum_le_sum
          intro k hk
          have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          calc hc q r k * q ^ (r * (n - k))
              ≤ ((k + 1) ^ r * (q ^ (r - 1)) ^ k) * q ^ (r * (n - k)) :=
                Nat.mul_le_mul_right _ (ih k)
            _ = (k + 1) ^ r * q ^ ((r - 1) * k + r * (n - k)) := by
                rw [← pow_mul, pow_add]; ring
            _ ≤ (n + 1) ^ r * q ^ (r * n) := by
                apply Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) _)
                apply Nat.pow_le_pow_right hq
                have h1 : (r - 1) * k ≤ r * k := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
                have h2 : r * k + r * (n - k) = r * n := by
                  rw [← Nat.mul_add, Nat.add_sub_cancel' hk']
                omega
      _ = (n + 1) ^ (r + 1) * (q ^ (r + 1 - 1)) ^ n := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.add_sub_cancel, ← pow_mul,
            pow_succ]
          ring

/- English proof (translation)
By extensionality, compare the relevant components. Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem one_sub_mul_geom (c : ℂ) :
    (1 - PowerSeries.C c * PowerSeries.X) * PowerSeries.mk (fun n => c ^ n) = 1 := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    rw [sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n),
      pow_succ]
    ring

def polP (q r : ℕ) : Polynomial ℂ :=
  ∏ i ∈ Finset.range r, (1 - Polynomial.C ((q : ℂ) ^ i) * Polynomial.X)

/- English proof (translation)
Proceed by induction. Treat this case separately. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Treat this case separately.

Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the hypotheses and the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem polP_mul_hc (q r : ℕ) :
    (polP q r : PowerSeries ℂ) * PowerSeries.mk (fun n => (hc q r n : ℂ)) = 1 := by
  induction r with
  | zero =>
    ext n; simp [polP, hc, PowerSeries.coeff_one]
  | succ r ih =>
    have hmk : PowerSeries.mk (fun n => (hc q (r + 1) n : ℂ)) =
        PowerSeries.mk (fun n => (hc q r n : ℂ)) * PowerSeries.mk (fun n => ((q : ℂ) ^ r) ^ n) := by
      ext n
      rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i (PowerSeries.mk (fun n => (hc q r n : ℂ))) *
          PowerSeries.coeff j (PowerSeries.mk (fun n => ((q : ℂ) ^ r) ^ n)))]
      simp [hc, pow_mul]
    rw [polP, Finset.prod_range_succ, Polynomial.coe_mul, ← polP, hmk]
    calc (polP q r : PowerSeries ℂ) * ((1 - Polynomial.C ((q : ℂ) ^ r) * Polynomial.X :
          Polynomial ℂ) : PowerSeries ℂ) * (PowerSeries.mk (fun n => (hc q r n : ℂ)) *
            PowerSeries.mk (fun n => ((q : ℂ) ^ r) ^ n))
        = ((polP q r : PowerSeries ℂ) * PowerSeries.mk (fun n => (hc q r n : ℂ))) *
          (((1 - Polynomial.C ((q : ℂ) ^ r) * Polynomial.X : Polynomial ℂ) : PowerSeries ℂ) *
            PowerSeries.mk (fun n => ((q : ℂ) ^ r) ^ n)) := by ring
      _ = 1 := by
        rw [ih, one_mul]
        rw [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_C,
          Polynomial.coe_X]
        exact one_sub_mul_geom ((q : ℂ) ^ r)

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
theorem coeff_relation (q r n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range (n + 1), (polP q r).coeff k * (hc q r (n - k) : ℂ) = 0 := by
  have h := congrArg (PowerSeries.coeff n) (polP_mul_hc q r)
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i (polP q r : PowerSeries ℂ) *
      PowerSeries.coeff j (PowerSeries.mk (fun n => (hc q r n : ℂ))))] at h
  simpa [PowerSeries.coeff_one, show n ≠ 0 by omega, Polynomial.coeff_coe] using h

end GlobalTheory.SubIdxCount

namespace GlobalTheory.SubIdxCount

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem elem_coeff (r : ℕ) (L : Lat O K r) (k : ℕ) :
    (-1 : ℂ) ^ k * (qRes O : ℂ) ^ (k * (k - 1) / 2) * ((subElem k L).ncard : ℂ) =
      (polP (qRes O) r).coeff k := by
  obtain ⟨-, -, hemp, hX⟩ := GlobalTheory.T.elementarySublatticesOfIndex_degrees_qBinomial O K r L
  have hQP : (∑ j ∈ Finset.range (r + 1), Polynomial.C ((-1 : ℂ) ^ j *
      (qRes O : ℂ) ^ (j * (j - 1) / 2) * ((subElem j L).ncard : ℂ)) * Polynomial.X ^ j) =
      polP (qRes O) r := by
    apply Polynomial.funext
    intro x
    rw [polP, Polynomial.eval_finsetSum, Polynomial.eval_prod]
    simpa using hX x
  rw [← hQP, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with hk
  · rfl
  · have : r < k := by simp at hk; omega
    rw [hemp k this]; simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Take a linear combination of the given relations to obtain the conclusion.

A detailed English derivation is pending.
-/
theorem ncard_subIdx_eq (r : ℕ) : ∀ (n : ℕ) (L : Lat O K r),
    (subIdx n L).ncard = hc (qRes O) r n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro L
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [subIdx_zero, Set.ncard_singleton, hc_zero_right]
  have hid := GlobalTheory.T.heckeOperator_alternating_series_identity O K r ℂ (fun _ => (1 : ℂ)) n L hn
  have hall : ∀ (m : ℕ) (M : Lat O K r),
      heckeAll m (fun _ => (1 : ℂ)) M = ((subIdx m M).ncard : ℂ) := by
    intro m M
    rw [heckeAll_eq_sum, Set.ncard_eq_toFinset_card _ (subIdx_finite m M)]
    simp
  have hterm : ∀ k ∈ Finset.range n,
      ((-1 : ℂ) ^ (k + 1) * (qRes O : ℂ) ^ ((k + 1) * (k + 1 - 1) / 2)) •
        heckeElem (k + 1) (heckeAll (n - (k + 1)) (fun _ => (1 : ℂ))) L =
      (polP (qRes O) r).coeff (k + 1) * (hc (qRes O) r (n - (k + 1)) : ℂ) := by
    intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    have hc' : heckeAll (n - (k + 1)) (fun (_ : Lat O K r) => (1 : ℂ)) =
        fun (_ : Lat O K r) => (hc (qRes O) r (n - (k + 1)) : ℂ) := by
      funext M; rw [hall, ih _ (by omega) M]
    rw [hc', heckeElem_eq_sum, Finset.sum_const, ← Set.ncard_eq_toFinset_card _
      (subElem_finite _ L), ← elem_coeff r L (k + 1), smul_eq_mul, nsmul_eq_mul]
    ring
  have hsum := Finset.sum_congr rfl hterm
  rw [Finset.sum_range_succ'] at hid
  rw [hsum] at hid
  have hrel := coeff_relation (qRes O) r n hn
  rw [Finset.sum_range_succ'] at hrel
  have h0 := elem_coeff r L 0
  rw [subElem_zero, Set.ncard_singleton] at h0
  rw [heckeElem_zero, hall] at hid
  simp only [pow_zero, zero_mul, Nat.zero_div, Nat.cast_one, mul_one, Nat.sub_zero,
    one_smul] at hid h0
  rw [← h0, one_mul] at hrel
  have : ((subIdx n L).ncard : ℂ) = (hc (qRes O) r n : ℂ) := by
    linear_combination hid - hrel
  exact_mod_cast this

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem ncard_subIdx_le : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ)
    (n : ℕ) (L : Lat O K r),
    ((subIdx n L).ncard : ℝ) ≤ ((n : ℝ) + 1) ^ r * ((qRes O : ℝ) ^ (r - 1)) ^ n := by
  intro O K _ _ _ _ _ _ _ r n L
  rw [ncard_subIdx_eq r n L]
  have h := hc_le (qRes O) (one_lt_qRes (O := O)).le r n
  exact_mod_cast h

end GlobalTheory.SubIdxCount
