import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot

noncomputable section

namespace GlobalTheory.NL

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

namespace LevPt

open PowerSeries

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
theorem simple_zero {L : Type} [Field L] (f : PowerSeries L) (h0 : constantCoeff f = 0)
    (h1 : coeff 1 f ≠ 0) : ∃ w : PowerSeries L, IsUnit w ∧ f = X * w := by
  obtain ⟨w, rfl⟩ := X_dvd_iff.mpr h0
  refine ⟨w, ?_, rfl⟩
  rw [isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
  simpa using h1

/- English proof (translation)
Establish an intermediate fact. Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.

Move the embeddings inside the algebraic operations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Simplify to obtain the desired conclusion from the available facts.
-/
theorem coeff_one_pow_of_deriv {L : Type} [Field L] (U : PowerSeries L)
    (hU : derivative L U = U) (m : ℕ) : coeff 1 (U ^ m) = (m : L) * constantCoeff U ^ m := by
  have h : derivative L (U ^ m) = (m : PowerSeries L) * U ^ m := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, Derivation.leibniz, ih, hU]
      push_cast
      simp only [smul_eq_mul]
      ring
  have h2 := congrArg (coeff 0) h
  rw [coeff_derivative] at h2
  simpa using h2

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem φA_one_add : W.φA (1 + letπ) = (1 + letπ) ^ PD.p := by
  rw [map_add, map_one, W.φA_π]
  funext i
  have := W.q₀_def
  simp only [Pi.add_apply, Pi.mul_apply, Pi.one_apply, Pi.pow_apply, letπ, LocWach.q]
  linear_combination this

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.
-/
theorem φA_pow_one_add (k : ℕ) : (W.φA ^ k) (1 + letπ) = (1 + letπ) ^ (PD.p ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, AlgHom.mul_apply, φA_one_add, map_pow, ih, ← pow_mul, ← pow_succ]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem X_eq : W.X = (1 + letπ) ^ (PD.p ^ (W.s - 1)) - 1 := by
  rw [← φA_pow_one_add W, map_add, map_one, LocWach.X]
  ring

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Take a linear combination of the given relations to obtain the conclusion.

Establish an intermediate fact. By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem q_eq : W.q = ∑ k ∈ Finset.range PD.p, (1 + letπ : LetA O n) ^ k := by
  funext i
  have h := W.q₀_def
  have h2 := geom_sum_mul (1 + X : PowerSeries O) PD.p
  have h3 : X * (W.q₀ - ∑ k ∈ Finset.range PD.p, (1 + X : PowerSeries O) ^ k) = 0 := by
    linear_combination h - h2
  have h4 : W.q₀ - ∑ k ∈ Finset.range PD.p, (1 + X : PowerSeries O) ^ k = 0 := by
    ext m
    have := congrArg (coeff (m + 1)) h3
    rw [coeff_succ_X_mul] at this
    simpa using this
  simp only [LocWach.q, Finset.sum_apply, Pi.pow_apply, Pi.add_apply, Pi.one_apply, letπ]
  exact sub_eq_zero.mp h4

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem Q_eq : W.Q = ∑ k ∈ Finset.range PD.p, ((1 + letπ : LetA O n) ^ (PD.p ^ (W.s - 1))) ^ k := by
  rw [LocWach.Q, q_eq, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_pow, φA_pow_one_add]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem lev_letE (i : ZMod n) (ζ : LL) : W.lev i ζ (letE i) = 1 := by
  have h := W.lev_letter i ζ (1 - letE i) (by simp [letE])
  rw [map_sub, map_one] at h
  exact (sub_eq_zero.mp h).symm

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem lev_values [CharZero LL] (i : ZMod n) (ζ : LL) (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) :
    (∃ w : PowerSeries LL, IsUnit w ∧ W.lev i ζ letπ = C (ζ - 1) + X * w) ∧
    (ζ ^ (PD.p ^ (W.s - 1)) = 1 → (∃ w : PowerSeries LL, IsUnit w ∧ W.lev i ζ W.X = X * w) ∧
      IsUnit (W.lev i ζ W.Q)) ∧
    (IsPrimitiveRoot ζ (PD.p ^ W.s) → (∃ w : PowerSeries LL, IsUnit w ∧ W.lev i ζ W.Q = X * w) ∧
      IsUnit (W.lev i ζ W.X)) ∧
    (constantCoeff (W.lev i ζ W.X) = 0 ↔ ζ ^ (PD.p ^ (W.s - 1)) = 1) ∧
    (constantCoeff (W.lev i ζ W.Q) = 0 ↔ IsPrimitiveRoot ζ (PD.p ^ W.s)) ∧ W.lev i ζ W.Q ≠ 0 := by
  have hp : PD.p.Prime := PD.hp
  haveI : Fact PD.p.Prime := ⟨hp⟩
  obtain ⟨E, hE0, hE1, hE⟩ := W.lev_π i ζ hζ
  obtain ⟨j, hj⟩ := hζ
  have hζ0 : ζ ≠ 0 := hj.ne_zero (pow_ne_zero _ hp.ne_zero)
  set U : PowerSeries LL := C ζ * E with hUdef
  have hU0 : constantCoeff U = ζ := by simp [hUdef, hE0]
  have hU1 : derivative LL U = U := by
    rw [hUdef, Derivation.leibniz, hE1, derivative_C]
    simp
  have hlevU : W.lev i ζ (1 + letπ) = U := by rw [map_add, map_one, hE]
  have hc1 : ∀ m : ℕ, m ≠ 0 → coeff 1 (U ^ m - 1) ≠ 0 := by
    intro m hm
    rw [map_sub, coeff_one_pow_of_deriv U hU1, hU0, coeff_one]
    simp [hm, hζ0]
  have hc0 : ∀ m : ℕ, constantCoeff (U ^ m - 1) = ζ ^ m - 1 := by
    intro m
    simp [hU0]
  obtain ⟨r, hr⟩ : ∃ r, W.s = r + 1 := ⟨W.s - 1, by have := W.s_pos; omega⟩
  have hX : W.lev i ζ W.X = U ^ (PD.p ^ r) - 1 := by
    rw [X_eq, map_sub, map_one, map_pow, hlevU, hr, Nat.add_sub_cancel]
  have hQ : W.lev i ζ W.Q = ∑ k ∈ Finset.range PD.p, (U ^ (PD.p ^ r)) ^ k := by
    rw [Q_eq, map_sum, hr, Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_pow, map_pow, hlevU]
  have hXQ : W.lev i ζ W.Q * W.lev i ζ W.X = U ^ (PD.p ^ (r + 1)) - 1 := by
    rw [hX, hQ, geom_sum_mul, ← pow_mul, ← pow_succ]
  have hQ0 : constantCoeff (W.lev i ζ W.Q) = ∑ k ∈ Finset.range PD.p, (ζ ^ (PD.p ^ r)) ^ k := by
    rw [hQ, map_sum]
    simp [hU0]
  have hprim : IsPrimitiveRoot ζ (PD.p ^ (r + 1)) ↔
      ζ ^ (PD.p ^ (r + 1)) = 1 ∧ ¬ ζ ^ (PD.p ^ r) = 1 := by
    constructor
    · intro h
      refine ⟨h.pow_eq_one, h.pow_ne_one_of_pos_of_lt (pow_ne_zero _ hp.ne_zero) ?_⟩
      exact Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self r)
    · rintro ⟨h1, h2⟩
      rw [← orderOf_eq_prime_pow h2 h1]
      exact IsPrimitiveRoot.orderOf _
  have hQone : ζ ^ (PD.p ^ r) = 1 → constantCoeff (W.lev i ζ W.Q) ≠ 0 := by
    intro h
    rw [hQ0, h]
    simp [hp.ne_zero]
  have hX0 : constantCoeff (W.lev i ζ W.X) = 0 ↔ ζ ^ (PD.p ^ r) = 1 := by
    rw [hX, hc0, sub_eq_zero]
  have hQiff : constantCoeff (W.lev i ζ W.Q) = 0 ↔ IsPrimitiveRoot ζ (PD.p ^ (r + 1)) := by
    have hc := congrArg constantCoeff hXQ
    rw [map_mul, hc0] at hc
    rw [hprim]
    constructor
    · intro h
      rw [h, zero_mul] at hc
      exact ⟨(sub_eq_zero.mp hc.symm), fun h' => hQone h' h⟩
    · rintro ⟨h1, h2⟩
      rw [h1, sub_self] at hc
      exact (mul_eq_zero.mp hc).resolve_right (fun h => h2 (hX0.mp h))
  rw [hr, Nat.add_sub_cancel]
  refine ⟨?_, ?_, ?_, hX0, hQiff, ?_⟩
  · obtain ⟨w, hw, hw'⟩ := simple_zero (U - C ζ) (by simp [hU0]) (by
      have := hc1 1 one_ne_zero
      rw [pow_one, map_sub, coeff_one] at this
      rw [map_sub, coeff_C]
      simpa using this)
    refine ⟨w, hw, ?_⟩
    rw [map_sub, map_one]
    linear_combination hE + hw'
  · intro h
    refine ⟨simple_zero _ (hX0.mpr h) (by rw [hX]; exact hc1 _ (pow_ne_zero _ hp.ne_zero)), ?_⟩
    rw [isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
    exact hQone h
  · intro h
    have hXu : IsUnit (W.lev i ζ W.X) := by
      rw [isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
      exact fun h' => (hprim.mp h).2 (hX0.mp h')
    refine ⟨?_, hXu⟩
    obtain ⟨w, hw, hw'⟩ := simple_zero (U ^ (PD.p ^ (r + 1)) - 1)
      (by rw [hc0, h.pow_eq_one, sub_self]) (hc1 _ (pow_ne_zero _ hp.ne_zero))
    obtain ⟨u, hu⟩ := hXu
    refine ⟨w * ↑u⁻¹, hw.mul (Units.isUnit _), ?_⟩
    rw [← mul_assoc, ← hw', ← hXQ, ← hu, Units.mul_inv_cancel_right]
  · intro h
    apply hc1 (PD.p ^ (r + 1)) (pow_ne_zero _ hp.ne_zero)
    rw [← hXQ, h, zero_mul, map_zero]

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Supply the required witnesses or components. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_nonunit {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l) (ζ : ↥LL.1)
    (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) :
    ∃ x : ↥(OL LL), ¬ IsUnit x ∧ (x : ↥LL.1) = ζ - 1 := by
  have hp : l.Prime := Fact.out
  obtain ⟨j, hj⟩ := hζ
  have hint : IsIntegral ℤ_[l] ζ := (hj.isIntegral (pow_pos hp.pos j)).tower_top
  let x : ↥(OL LL) := ⟨ζ - 1, (OL LL).sub_mem hint (OL LL).one_mem⟩
  refine ⟨x, fun hx => ?_, rfl⟩
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp x 1 j
  have h1 : (x + 1) ^ (l ^ j) = 1 := by
    apply Subtype.ext
    simp [x, hj.pow_eq_one]
  have hl : IsUnit ((l : ℕ) : ↥(OL LL)) := by
    have h2 : IsUnit (x ^ (l ^ j)) := hx.pow _
    refine isUnit_of_dvd_unit ?_ h2
    rw [h1, one_pow] at hr
    exact ⟨-(x * r), by linear_combination -hr⟩
  obtain ⟨y, hy⟩ := hl.exists_right_inv
  have hy' : (l : ↥LL.1) * (y : ↥LL.1) = 1 := by
    have := congrArg (fun z : ↥(OL LL) => (z : ↥LL.1)) hy
    simpa using this
  have hv := congrArg (P.v LL) hy'
  rw [AddValuation.map_mul, P.v_l, AddValuation.map_one] at hv
  have h0 : 0 ≤ P.v LL y := (P.v_O LL y).mpr y.2
  have : (1 : WithTop ℚ) ≤ 1 + P.v LL y := le_add_of_nonneg_right h0
  rw [hv] at this
  exact absurd this (by norm_num)

end LevPt

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem lev_at_root_of_unity : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (i : Let K) (ζ : ↥LL.1), (∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) → (∃ x : ↥(OL LL), ¬ IsUnit x ∧ (x : ↥LL.1) = ζ - 1 ∧ ∃ w : PowerSeries ↥LL.1, IsUnit w ∧ W.lev i ζ letπ = PowerSeries.C (x : ↥LL.1) + PowerSeries.X * w) ∧ W.lev i ζ (letE i) = 1 ∧ (ζ ^ (l ^ (s - 1)) = 1 → (∃ w : PowerSeries ↥LL.1, IsUnit w ∧ W.lev i ζ W.X = PowerSeries.X * w) ∧ IsUnit (W.lev i ζ W.Q)) ∧ (IsPrimitiveRoot ζ (l ^ s) → (∃ w : PowerSeries ↥LL.1, IsUnit w ∧ W.lev i ζ W.Q = PowerSeries.X * w) ∧ IsUnit (W.lev i ζ W.X)) ∧ (PowerSeries.constantCoeff (W.lev i ζ W.X) = 0 ↔ ζ ^ (l ^ (s - 1)) = 1) ∧ (PowerSeries.constantCoeff (W.lev i ζ W.Q) = 0 ↔ IsPrimitiveRoot ζ (l ^ s)) ∧ W.lev i ζ W.Q ≠ 0 := by
  intro D HW l _ K s LL h W i ζ hζ
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hs : W.s = s := (HW l).W_s K s LL h
  clear_value W
  haveI : CharZero ↥LL.1 := algebraRat.charZero _
  have hζ' : ∃ j : ℕ, IsPrimitiveRoot ζ (((D.loc l).PD K).p ^ j) := by rw [hp]; exact hζ
  obtain ⟨H1, H2⟩ := LevPt.lev_values W i ζ hζ'
  simp only [hp, hs] at H2
  obtain ⟨x, hx, hx'⟩ := LevPt.exists_nonunit (D.loc l) LL ζ hζ
  refine ⟨⟨x, hx, hx', ?_⟩, LevPt.lev_letE W i ζ, H2⟩
  rw [hx']
  exact H1

end GlobalTheory.NL
