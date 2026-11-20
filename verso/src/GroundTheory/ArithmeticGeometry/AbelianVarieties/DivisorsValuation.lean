import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.DivisorsOrd
import GroundTheory.ArithmeticGeometry.AbelianVarieties.FunctionFieldPoint

namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
  IsDedekindDomain WithZero

open scoped nonZeroDivisors

universe u

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem exists_eq_pow_of_le_one_iff {L : Type*} [Field L] (w v : Valuation L ℤᵐ⁰)
    (h : ∀ f, w f ≤ 1 ↔ v f ≤ 1) {π : L} (hπ : v π = exp (-1)) :
    ∃ e : ℕ, 0 < e ∧ ∀ f, w f = v f ^ e := by
  have key : ∀ (u : Valuation L ℤᵐ⁰) (f : L), f ≠ 0 → (u f < 1 ↔ ¬ u f⁻¹ ≤ 1) :=
    fun u f hf => by rw [not_le, Valuation.one_lt_val_iff u (inv_ne_zero hf), inv_inv]
  have hlt : ∀ f : L, f ≠ 0 → (w f < 1 ↔ v f < 1) := fun f hf => by
    rw [key w f hf, key v f hf, h f⁻¹]
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact exp_ne_zero hπ.symm
  have hwπ : w π < 1 := (hlt π hπ0).mpr (by rw [hπ, ← exp_zero, exp_lt_exp]; norm_num)
  have hwπ0 : w π ≠ 0 := (Valuation.ne_zero_iff _).mpr hπ0
  obtain ⟨c, hwπc⟩ : ∃ c : ℤ, w π = exp c := ⟨_, (exp_log hwπ0).symm⟩
  have hc0 : c < 0 := by
    have := hwπ
    rwa [hwπc, ← exp_zero, exp_lt_exp] at this
  refine ⟨c.natAbs, by omega, fun f => ?_⟩
  rcases eq_or_ne f 0 with rfl | hf
  · rw [map_zero, map_zero, zero_pow (by omega)]
  have hvf0 : v f ≠ 0 := (Valuation.ne_zero_iff _).mpr hf
  obtain ⟨l, hvf⟩ : ∃ l : ℤ, v f = exp l := ⟨_, (exp_log hvf0).symm⟩
  have hg : v (f * π ^ l) = 1 := by
    rw [map_mul, map_zpow₀, hπ, hvf, ← exp_zsmul, ← exp_add, ← exp_zero]
    congr 1
    simp
  have hwg : w (f * π ^ l) = 1 := by
    have hg0 : f * π ^ l ≠ 0 := mul_ne_zero hf (zpow_ne_zero _ hπ0)
    refine le_antisymm ((h _).mpr hg.le) (not_lt.mp fun hl => ?_)
    have := (hlt _ hg0).mp hl
    rw [hg] at this
    exact lt_irrefl _ this
  rw [map_mul, map_zpow₀, hwπc, ← exp_zsmul] at hwg
  rw [eq_inv_of_mul_eq_one_left hwg, hvf, ← exp_nsmul, ← exp_neg]
  congr 1
  simp only [smul_eq_mul, nsmul_eq_mul]
  rw [Int.ofNat_natAbs_of_nonpos hc0.le]
  ring

variable {F : Type u} [Field F] (W : WeierstrassCurve F)

section Poly

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem algebraMap_C_functionField (c : F) :
    algebraMap F[X] W.toAffine.FunctionField (C c) = algebraMap F W.toAffine.FunctionField c :=
  (IsScalarTower.algebraMap_apply F F[X] W.toAffine.FunctionField c).symm

/- English proof (translation)
Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem genY_sq_add : genY W ^ 2 + algebraMap F W.toAffine.FunctionField W.a₁ * genX W * genY W +
    algebraMap F W.toAffine.FunctionField W.a₃ * genY W = genX W ^ 3 +
      algebraMap F W.toAffine.FunctionField W.a₂ * genX W ^ 2 +
      algebraMap F W.toAffine.FunctionField W.a₄ * genX W +
      algebraMap F W.toAffine.FunctionField W.a₆ := by
  have e := (equation_iff _ _).mp (equation_gen W)
  simpa only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] using e

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem algebraMap_smul_basis (p q : F[X]) :
    algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (p • (1 : W.toAffine.CoordinateRing) + q • AdjoinRoot.mk W.toAffine.polynomial X) =
      algebraMap F[X] W.toAffine.FunctionField p +
        algebraMap F[X] W.toAffine.FunctionField q * genY W := by
  rw [map_add, Algebra.smul_def, Algebra.smul_def, mul_one, map_mul,
    ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rfl

variable {W}

/- English proof (translation)
Proceed by induction. Treat this case separately. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules.

Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem valuation_poly_le_one (w : Valuation W.toAffine.FunctionField ℤᵐ⁰)
    (hF : ∀ c : F, c ≠ 0 → w (algebraMap F W.toAffine.FunctionField c) = 1)
    (hx : w (genX W) ≤ 1) (p : F[X]) : w (algebraMap F[X] W.toAffine.FunctionField p) ≤ 1 := by
  induction p using Polynomial.induction_on with
  | C c =>
    rw [algebraMap_C_functionField]
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    · exact (hF c hc).le
  | add p q hp hq => rw [map_add]; exact w.map_add_le hp hq
  | monomial n c ih =>
    rw [pow_succ, ← mul_assoc, map_mul, map_mul, ← genX_eq]
    exact mul_le_one' ih hx

/- English proof (translation)
Proceed by induction. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Separate the alternatives or extract the components of the hypothesis. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Use the polynomial consequences of the given equalities and inequalities. Rewrite the conclusion using the stated equalities.
-/
theorem valuation_poly_of_one_lt (w : Valuation W.toAffine.FunctionField ℤᵐ⁰)
    (hF : ∀ c : F, c ≠ 0 → w (algebraMap F W.toAffine.FunctionField c) = 1) {k : ℤ} (hk0 : 0 < k)
    (hk : w (genX W) = exp k) {p : F[X]} (hp : p ≠ 0) :
    w (algebraMap F[X] W.toAffine.FunctionField p) = exp (p.natDegree * k) := by
  induction h : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ d ih =>
    have hlead : w (algebraMap F[X] W.toAffine.FunctionField
        (C p.leadingCoeff * X ^ p.natDegree)) = exp (d * k) := by
      rw [map_mul, map_pow, algebraMap_C_functionField, Valuation.map_mul, Valuation.map_pow,
        hF _ (leadingCoeff_ne_zero.mpr hp), ← genX_eq, hk, one_mul, ← exp_nsmul, h, nsmul_eq_mul]
    rw [← eraseLead_add_C_mul_X_pow p, map_add]
    rcases (eraseLead_natDegree_lt_or_eraseLead_eq_zero p) with hlt | he
    · by_cases he : p.eraseLead = 0
      · rw [he, map_zero, zero_add, hlead]
      · have hd : (p.eraseLead.natDegree : ℤ) < d := by exact_mod_cast h ▸ hlt
        rw [Valuation.map_add_eq_of_lt_right _ ?_, hlead]
        rw [hlead, ih _ (h ▸ hlt) he rfl, exp_lt_exp]
        nlinarith
    · rw [he, map_zero, zero_add, hlead]

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem valuation_poly_le_of_one_lt (w : Valuation W.toAffine.FunctionField ℤᵐ⁰)
    (hF : ∀ c : F, c ≠ 0 → w (algebraMap F W.toAffine.FunctionField c) = 1) {k : ℤ} (hk0 : 0 < k)
    (hk : w (genX W) = exp k) (p : F[X]) {n : ℕ} (hn : p.natDegree ≤ n) :
    w (algebraMap F[X] W.toAffine.FunctionField p) ≤ exp (n * k) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · rw [valuation_poly_of_one_lt w hF hk0 hk hp, exp_le_exp]
    have : (p.natDegree : ℤ) ≤ n := by exact_mod_cast hn
    nlinarith

end Poly

section Gen

noncomputable def weierstrassB : F[X] := C W.a₁ * X + C W.a₃

noncomputable def weierstrassRHS : F[X] := X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆

/- English proof (translation)
Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem genY_sq_add_weierstrassB :
    genY W ^ 2 + algebraMap F[X] W.toAffine.FunctionField (weierstrassB W) * genY W =
      algebraMap F[X] W.toAffine.FunctionField (weierstrassRHS W) := by
  simp only [weierstrassB, weierstrassRHS, map_add, map_mul, map_pow,
    algebraMap_C_functionField, ← genX_eq]
  linear_combination genY_sq_add W

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem natDegree_weierstrassRHS : (weierstrassRHS W).natDegree = 3 := by
  unfold weierstrassRHS; compute_degree!

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem natDegree_weierstrassB_le : (weierstrassB W).natDegree ≤ 1 := by
  unfold weierstrassB; compute_degree

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem weierstrassRHS_ne_zero : weierstrassRHS W ≠ 0 := by
  intro h
  have := natDegree_weierstrassRHS W
  rw [h, natDegree_zero] at this
  exact absurd this (by norm_num)

variable {W}

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Evaluate the numerical expressions. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Evaluate the numerical expressions.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. It suffices to derive a contradiction. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
theorem valuation_genY_of_one_lt (w : Valuation W.toAffine.FunctionField ℤᵐ⁰)
    (hF : ∀ c : F, c ≠ 0 → w (algebraMap F W.toAffine.FunctionField c) = 1) {k : ℤ} (hk0 : 0 < k)
    (hk : w (genX W) = exp k) : ∃ m : ℤ, w (genY W) = exp m ∧ 2 * m = 3 * k := by
  have hy0 : w (genY W) ≠ 0 := (Valuation.ne_zero_iff _).mpr (genY_ne_zero W)
  obtain ⟨m, hm⟩ : ∃ m : ℤ, w (genY W) = exp m := ⟨_, (exp_log hy0).symm⟩
  refine ⟨m, hm, ?_⟩
  have hwQ : w (algebraMap F[X] W.toAffine.FunctionField (weierstrassRHS W)) = exp (3 * k) := by
    rw [valuation_poly_of_one_lt w hF hk0 hk (weierstrassRHS_ne_zero W), natDegree_weierstrassRHS]
    norm_num
  have hwB : w (algebraMap F[X] W.toAffine.FunctionField (weierstrassB W)) ≤ exp (1 * k) :=
    valuation_poly_le_of_one_lt w hF hk0 hk _ (natDegree_weierstrassB_le W)
  have hwy2 : w (genY W ^ 2) = exp (2 * m) := by
    rw [Valuation.map_pow, hm, ← exp_nsmul, nsmul_eq_mul]
    norm_num
  have hwBy : w (algebraMap F[X] W.toAffine.FunctionField (weierstrassB W) * genY W) ≤
      exp (k + m) := by
    rw [Valuation.map_mul, hm]
    calc _ ≤ exp (1 * k) * exp m := mul_le_mul_left hwB _
      _ = exp (k + m) := by rw [← exp_add, one_mul]
  have heq := congrArg w (genY_sq_add_weierstrassB W)
  rcases lt_or_ge k m with hkm | hmk
  · have hlt : w (algebraMap F[X] W.toAffine.FunctionField (weierstrassB W) * genY W) <
        w (genY W ^ 2) := by
      rw [hwy2]
      exact lt_of_le_of_lt hwBy (exp_lt_exp.mpr (by linarith))
    rw [Valuation.map_add_eq_of_lt_left _ hlt, hwy2, hwQ] at heq
    exact exp_inj.mp heq
  · exfalso
    have hle : w (genY W ^ 2 + algebraMap F[X] W.toAffine.FunctionField (weierstrassB W) *
        genY W) ≤ exp (2 * k) :=
      w.map_add_le (by rw [hwy2, exp_le_exp]; linarith) (hwBy.trans (by rw [exp_le_exp]; linarith))
    rw [heq, hwQ, exp_le_exp] at hle
    linarith

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Evaluate the numerical expressions. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem valuation_genY_le_one (w : Valuation W.toAffine.FunctionField ℤᵐ⁰)
    (hF : ∀ c : F, c ≠ 0 → w (algebraMap F W.toAffine.FunctionField c) = 1)
    (hx : w (genX W) ≤ 1) : w (genY W) ≤ 1 := by
  by_contra hy
  have hy0 : w (genY W) ≠ 0 := (Valuation.ne_zero_iff _).mpr (genY_ne_zero W)
  obtain ⟨m, hm⟩ : ∃ m : ℤ, w (genY W) = exp m := ⟨_, (exp_log hy0).symm⟩
  rw [not_le, hm, ← exp_zero, exp_lt_exp] at hy
  have hwB := valuation_poly_le_one w hF hx (weierstrassB W)
  have hwQ := valuation_poly_le_one w hF hx (weierstrassRHS W)
  have hwy2 : w (genY W ^ 2) = exp (2 * m) := by
    rw [Valuation.map_pow, hm, ← exp_nsmul, nsmul_eq_mul]
    norm_num
  have hlt : w (algebraMap F[X] W.toAffine.FunctionField (weierstrassB W) * genY W) <
      w (genY W ^ 2) := by
    rw [Valuation.map_mul, hm, hwy2]
    calc _ ≤ 1 * exp m := mul_le_mul_left hwB _
      _ < exp (2 * m) := by rw [one_mul, exp_lt_exp]; linarith
  have heq := congrArg w (genY_sq_add_weierstrassB W)
  rw [Valuation.map_add_eq_of_lt_left _ hlt, hwy2] at heq
  rw [← heq, ← exp_zero, exp_le_exp] at hwQ
  linarith

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem natDegree_norm_smul_basis_of_q_eq_zero {p : F[X]} :
    (Algebra.norm F[X] (p • (1 : W.toAffine.CoordinateRing) + (0 : F[X]) •
      AdjoinRoot.mk W.toAffine.polynomial X)).natDegree = 2 * p.natDegree := by
  rw [zero_smul, add_zero, Algebra.smul_def, mul_one, Algebra.norm_algebraMap,
    finrank_coordinateRing, natDegree_pow]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Put the expressions in a common number system so they can be compared.
-/
theorem natDegree_norm_smul_basis_of_p_eq_zero {q : F[X]} (hq : q ≠ 0) :
    (Algebra.norm F[X] ((0 : F[X]) • (1 : W.toAffine.CoordinateRing) +
      q • AdjoinRoot.mk W.toAffine.polynomial X)).natDegree = 2 * q.natDegree + 3 := by
  have h := degree_norm_smul_basis (W' := W.toAffine) 0 q
  rw [degree_eq_natDegree hq, degree_zero] at h
  apply natDegree_eq_of_degree_eq_some
  rw [h, max_eq_right (by rw [two_nsmul, WithBot.bot_add]; exact bot_le)]
  norm_cast

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Put the expressions in a common number system so they can be compared.
-/
theorem natDegree_norm_smul_basis_of_ne_zero {p q : F[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    (Algebra.norm F[X] (p • (1 : W.toAffine.CoordinateRing) +
      q • AdjoinRoot.mk W.toAffine.polynomial X)).natDegree =
      max (2 * p.natDegree) (2 * q.natDegree + 3) := by
  have h := degree_norm_smul_basis (W' := W.toAffine) p q
  rw [degree_eq_natDegree hq, degree_eq_natDegree hp] at h
  apply natDegree_eq_of_degree_eq_some
  rw [h]
  norm_cast

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Substitute using the available equality. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Put the polynomial expressions in normal form.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Put the polynomial expressions in normal form. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities.

Put the polynomial expressions in normal form. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Simplify by unfolding definitions. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem eq_valuationInfty_of_genX (w : Valuation W.toAffine.FunctionField ℤᵐ⁰)
    (hF : ∀ c : F, c ≠ 0 → w (algebraMap F W.toAffine.FunctionField c) = 1)
    (hx : w (genX W) = exp 2) : w = valuationInfty W := by
  obtain ⟨m, hm, hm3⟩ := valuation_genY_of_one_lt w hF two_pos hx
  have hm' : m = 3 := by linarith
  subst hm'
  have hA : ∀ a : W.toAffine.CoordinateRing,
      w (algebraMap _ W.toAffine.FunctionField a) =
        valuationInfty W (algebraMap _ W.toAffine.FunctionField a) := by
    intro a
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    rw [valuationInfty_algebraMap, valuationInftyCoord_apply W ha]
    obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq a
    rw [algebraMap_smul_basis]
    rcases eq_or_ne q 0 with rfl | hq
    · have hp : p ≠ 0 := by rintro rfl; simp at ha
      rw [natDegree_norm_smul_basis_of_q_eq_zero, map_zero, zero_mul, add_zero,
        valuation_poly_of_one_lt w hF two_pos hx hp]
      push_cast; ring_nf
    · have hwQy : w (algebraMap F[X] W.toAffine.FunctionField q * genY W) =
          exp (2 * (q.natDegree : ℤ) + 3) := by
        rw [Valuation.map_mul, valuation_poly_of_one_lt w hF two_pos hx hq, hm, ← exp_add]
        ring_nf
      rcases eq_or_ne p 0 with rfl | hp
      · rw [natDegree_norm_smul_basis_of_p_eq_zero hq, map_zero, zero_add, hwQy]
        push_cast; ring_nf
      · rw [natDegree_norm_smul_basis_of_ne_zero hp hq]
        have hwP := valuation_poly_of_one_lt w hF two_pos hx hp
        rcases lt_or_gt_of_ne (show (2 * p.natDegree : ℤ) ≠ 2 * q.natDegree + 3 by omega) with
          hlt | hlt
        · rw [Valuation.map_add_eq_of_lt_right _ (by rw [hwP, hwQy, exp_lt_exp]; linarith), hwQy,
            max_eq_right (by omega)]
          push_cast; ring_nf
        · rw [Valuation.map_add_eq_of_lt_left _ (by rw [hwP, hwQy, exp_lt_exp]; linarith), hwP,
            max_eq_left (by omega)]
          push_cast; ring_nf
  refine Valuation.ext fun f => ?_
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective W.toAffine.CoordinateRing⁰ f
  dsimp only
  have hs : (s : W.toAffine.CoordinateRing) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have hspec := IsLocalization.mk'_spec W.toAffine.FunctionField a s
  have h1 := congrArg w hspec
  have h2 := congrArg (valuationInfty W) hspec
  rw [Valuation.map_mul, hA, hA] at h1
  rw [Valuation.map_mul] at h2
  have hvs : valuationInfty W (algebraMap _ W.toAffine.FunctionField
      (s : W.toAffine.CoordinateRing)) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hs)
  exact mul_right_cancel₀ hvs (h1.trans h2.symm)

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem valuation_coordinateRing_le_one (w : Valuation W.toAffine.FunctionField ℤᵐ⁰)
    (hF : ∀ c : F, c ≠ 0 → w (algebraMap F W.toAffine.FunctionField c) = 1)
    (hx : w (genX W) ≤ 1) (a : W.toAffine.CoordinateRing) :
    w (algebraMap _ W.toAffine.FunctionField a) ≤ 1 := by
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq a
  rw [algebraMap_smul_basis]
  refine w.map_add_le (valuation_poly_le_one w hF hx p) ?_
  rw [Valuation.map_mul]
  exact mul_le_one' (valuation_poly_le_one w hF hx q) (valuation_genY_le_one w hF hx)

end Gen

section CaseA

variable {W} [IsAlgClosed F] [W.IsElliptic]

/- English proof (translation)
Establish an intermediate fact. Introduce a local definition for the expression. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Chain the equalities or inequalities of the calculation.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Assume the negation of the conclusion and derive a contradiction. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Simplify by unfolding definitions. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Introduce a local definition for the expression.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem exists_eq_pow_valuation_of_le_one (w : Valuation W.toAffine.FunctionField ℤᵐ⁰)
    (hF : ∀ c : F, c ≠ 0 → w (algebraMap F W.toAffine.FunctionField c) = 1)
    (hx : w (genX W) ≤ 1) (hnt : ∃ f, f ≠ 0 ∧ w f ≠ 1) :
    ∃ v : HeightOneSpectrum W.toAffine.CoordinateRing,
      (∀ a, a ∈ v.asIdeal ↔ w (algebraMap _ W.toAffine.FunctionField a) < 1) ∧
      ∃ e : ℕ, 0 < e ∧ ∀ f, w f = v.valuation W.toAffine.FunctionField f ^ e := by
  have hA := valuation_coordinateRing_le_one w hF hx
  let P : Ideal W.toAffine.CoordinateRing :=
    { carrier := {a | w (algebraMap _ W.toAffine.FunctionField a) < 1}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_add] at ha hb ⊢
        exact lt_of_le_of_lt (w.map_add _ _) (max_lt ha hb)
      smul_mem' := fun c a ha => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at ha ⊢
        calc _ ≤ 1 * w (algebraMap _ W.toAffine.FunctionField a) := mul_le_mul_left (hA c) _
          _ < 1 := by rwa [one_mul] }
  have hmem : ∀ a, a ∈ P ↔ w (algebraMap _ W.toAffine.FunctionField a) < 1 := fun a => Iff.rfl
  have hone : ∀ a, a ∉ P → w (algebraMap _ W.toAffine.FunctionField a) = 1 :=
    fun a ha => le_antisymm (hA a) (not_lt.mp ha)
  have hPprime : P.IsPrime := by
    refine ⟨fun htop => ?_, fun {a b} hab => ?_⟩
    · have h1 : (1 : W.toAffine.CoordinateRing) ∈ P := htop ▸ Submodule.mem_top
      rw [hmem, map_one, map_one] at h1
      exact lt_irrefl _ h1
    · by_contra hn
      push Not at hn
      rw [hmem, map_mul, Valuation.map_mul, hone a hn.1, hone b hn.2, one_mul] at hab
      exact lt_irrefl _ hab
  have hP0 : P ≠ ⊥ := by
    intro hbot
    obtain ⟨f, hf, hwf⟩ := hnt
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective W.toAffine.CoordinateRing⁰ f
    apply hwf
    dsimp only at hf ⊢
    have hs : (s : W.toAffine.CoordinateRing) ≠ 0 := nonZeroDivisors.ne_zero s.2
    have ha : a ≠ 0 := by rintro rfl; exact hf (IsLocalization.mk'_zero _)
    have hnot : ∀ b : W.toAffine.CoordinateRing, b ≠ 0 → b ∉ P := fun b hb hbP =>
      hb ((Submodule.mem_bot _).mp (hbot ▸ hbP))
    have h1 := congrArg w (IsLocalization.mk'_spec W.toAffine.FunctionField a s)
    rw [Valuation.map_mul, hone _ (hnot _ hs), hone _ (hnot _ ha), mul_one] at h1
    exact h1
  let v : HeightOneSpectrum W.toAffine.CoordinateRing := ⟨P, hPprime, hP0⟩
  refine ⟨v, hmem, ?_⟩
  have hval_one : ∀ d : W.toAffine.CoordinateRing, d ∉ v.asIdeal →
      v.valuation W.toAffine.FunctionField (algebraMap _ _ d) = 1 := fun d hd => by
    rw [HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl]
    exact hd
  have hle : ∀ f, w f ≤ 1 ↔ v.valuation W.toAffine.FunctionField f ≤ 1 := by
    intro f
    constructor
    · intro hwf
      by_contra hvf
      rw [not_le] at hvf
      have hf : f ≠ 0 := by rintro rfl; simp at hvf
      have hvf' : v.valuation W.toAffine.FunctionField f⁻¹ ≤ 1 := by
        rw [map_inv₀]
        exact (inv_lt_one_of_one_lt₀ hvf).le
      obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer
        (K := W.toAffine.FunctionField) v f⁻¹ hvf'
      have hd : (d : W.toAffine.CoordinateRing) ∉ v.asIdeal := d.2
      have hvn : v.valuation W.toAffine.FunctionField (algebraMap _ _ n) < 1 := by
        rw [← hnd, Valuation.map_mul, hval_one _ hd, mul_one, map_inv₀]
        exact inv_lt_one_of_one_lt₀ hvf
      rw [HeightOneSpectrum.valuation_lt_one_iff_mem] at hvn
      have hwn := (hmem n).mp hvn
      rw [← hnd, Valuation.map_mul, hone _ hd, mul_one, map_inv₀] at hwn
      have : 1 < w f := by
        rwa [inv_lt_one₀ ((Valuation.pos_iff _).mpr hf)] at hwn
      exact absurd hwf (not_le.mpr this)
    · intro hvf
      obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer
        (K := W.toAffine.FunctionField) v f hvf
      have h1 := congrArg w hnd
      rw [Valuation.map_mul, hone _ d.2, mul_one] at h1
      exact h1 ▸ hA n
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer W.toAffine.FunctionField
  exact exists_eq_pow_of_le_one_iff w _ hle hπ

end CaseA

end GroundTheory.Arith.Abelian
