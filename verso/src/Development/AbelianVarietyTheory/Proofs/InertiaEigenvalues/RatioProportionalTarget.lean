import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGaussGCTarget
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ISupMonomialHolderLogConvexStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisValuationSubEqIntMulRadiusStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisSubUnitLeDigitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisRadiusPosDefiniteStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFrobeniusFixedEqPadicInt
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon.Gauss

namespace RatioProp

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Conclude with `(Fact.out : l.Prime).one_lt` after adjusting the coercions.
-/
theorem one_lt_l : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt

/- English proof (translation)
The claim follows from `inv_pos.2 (by linarith [(one_lt_l : (1 : ℝ) < l)])`.
-/
theorem inv_l_pos : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.2 (by linarith [(one_lt_l : (1 : ℝ) < l)])

/- English proof (translation)
The claim follows from `inv_lt_one_of_one_lt₀ one_lt_l`.
-/
theorem inv_l_lt_one : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ one_lt_l

/- English proof (translation)
The claim follows from `lt_of_lt_of_le inv_l_pos h0`.
-/
theorem rho_pos {ρ : ℝ} (h0 : (l : ℝ)⁻¹ ≤ ρ) : 0 < ρ := lt_of_lt_of_le inv_l_pos h0

/- English proof (translation)
The claim follows from `isGauss_gC_target l ρ h0 h1`.
-/
theorem gauss {ρ : ℝ} (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) : IsGauss l ρ (gC l ρ) :=
  isGauss_gC_target l ρ h0 h1

/- English proof (translation)
The claim follows from `(GlobalTheory.MemLoc.PhiFix.phiA_alg l _).trans (congrArg _ (GlobalTheory.MemLoc.PhiFix.φA_zA l c))`.
-/
theorem phi_zc (c : ℤ_[l]) : φc l (zc l c) = zc l c :=
  (GlobalTheory.MemLoc.PhiFix.phiA_alg l _).trans (congrArg _ (GlobalTheory.MemLoc.PhiFix.φA_zA l c))

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => rfl`. Consider the case `succ m ih`. Rewrite using `[Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul, map_pow, map_natCast]`.
-/
theorem iter_lpow (m j : ℕ) (x : Formalism.Per.Acris l) :
    (φc l)^[m] ((l : Formalism.Per.Acris l) ^ j * x) = (l : Formalism.Per.Acris l) ^ j * (φc l)^[m] x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul, map_pow, map_natCast]

/- English proof (translation)
Establish `hm` using `(gauss h0 h1).2.2.2.1 0 (l : Formalism.Per.Acris l)`. Rewrite `hm` using `[zero_mul, (GlobalTheory.T.gaussNormAcris_basic_values l ρ h0 h1).2.1]`. Establish `e : gC l ρ 0 * (1 - ρ) = 0` using `by linear_combination hm`. Break down `mul_eq_zero.1 e with h | h` into its components or cases. Conclude with `h`.

Conclude with `absurd h (by linarith)`.
-/
theorem gC_zero {ρ : ℝ} (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) : gC l ρ 0 = 0 := by
  have hm := (gauss h0 h1).2.2.2.1 0 (l : Formalism.Per.Acris l)
  rw [zero_mul, (GlobalTheory.T.gaussNormAcris_basic_values l ρ h0 h1).2.1] at hm
  have e : gC l ρ 0 * (1 - ρ) = 0 := by linear_combination hm
  rcases mul_eq_zero.1 e with h | h
  · exact h
  · exact absurd h (by linarith)

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => rw [pow_zero, one_mul, pow_zero, one_mul]`. Consider the case `succ m ih`. Rewrite using `[pow_succ', mul_assoc, (gauss h0 h1).2.2.2.1, (GlobalTheory.T.gaussNormAcris_basic_values l ρ h0 h1).2.1, ih, pow_succ']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gC_lpow {ρ : ℝ} (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) (m : ℕ) (x : Formalism.Per.Acris l) :
    gC l ρ ((l : Formalism.Per.Acris l) ^ m * x) = ρ ^ m * gC l ρ x := by
  induction m with
  | zero => rw [pow_zero, one_mul, pow_zero, one_mul]
  | succ m ih =>
    rw [pow_succ', mul_assoc, (gauss h0 h1).2.2.2.1, (GlobalTheory.T.gaussNormAcris_basic_values l ρ h0 h1).2.1, ih, pow_succ']
    ring

/- English proof (translation)
Introduce `e`. Establish `h` using `gC_lpow le_rfl inv_l_lt_one m x`. Rewrite `h` using `[e, gC_zero le_rfl inv_l_lt_one]`. Establish `hp` using `GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x hx _ le_rfl inv_l_lt_one`. Establish `: (0 : ℝ) < (l : ℝ)⁻¹ ^ m * gC l (l : ℝ)⁻¹ x` using `mul_pos (pow_pos inv_l_pos m) hp`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lpow_ne_zero {x : Formalism.Per.Acris l} (hx : x ≠ 0) (m : ℕ) : (l : Formalism.Per.Acris l) ^ m * x ≠ 0 := by
  intro e
  have h := gC_lpow le_rfl inv_l_lt_one m x
  rw [e, gC_zero le_rfl inv_l_lt_one] at h
  have hp := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x hx _ le_rfl inv_l_lt_one
  have : (0 : ℝ) < (l : ℝ)⁻¹ ^ m * gC l (l : ℝ)⁻¹ x := mul_pos (pow_pos inv_l_pos m) hp
  linarith

/- English proof (translation)
Establish `e : W - zc l (c + (l : ℤ_[l]) ^ k * y) * W' = (W - zc l c * W') + -((l : Formalism.Per.Acris l) ^ k * (zc l y * W'))`. Simplify using `only [map_add, map_mul, map_pow, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `((gauss h0 h1).2.1 _ _).trans (max_le_max le_rfl ?_)` and prove the remaining obligations.

Rewrite using `[(gauss h0 h1).2.2.1, gC_lpow h0 h1, (gauss h0 h1).2.2.2.1]`. Conclude with `mul_le_mul_of_nonneg_left (mul_le_of_le_one_left ((gauss h0 h1).1 _).1 ((gauss h0 h1).1 _).2) (pow_nonneg (rho_pos h0).le _)`.
-/
theorem pert {ρ : ℝ} (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) (W W' : Formalism.Per.Acris l) (c y : ℤ_[l]) (k : ℕ) :
    gC l ρ (W - zc l (c + (l : ℤ_[l]) ^ k * y) * W') ≤ max (gC l ρ (W - zc l c * W')) (ρ ^ k * gC l ρ W') := by
  have e : W - zc l (c + (l : ℤ_[l]) ^ k * y) * W' =
      (W - zc l c * W') + -((l : Formalism.Per.Acris l) ^ k * (zc l y * W')) := by
    simp only [map_add, map_mul, map_pow, map_natCast]
    ring
  rw [e]
  refine ((gauss h0 h1).2.1 _ _).trans (max_le_max le_rfl ?_)
  rw [(gauss h0 h1).2.2.1, gC_lpow h0 h1, (gauss h0 h1).2.2.2.1]
  exact mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_left ((gauss h0 h1).1 _).1 ((gauss h0 h1).1 _).2) (pow_nonneg (rho_pos h0).le _)

def digitSet (W W' : Formalism.Per.Acris l) (k : ℕ) : Set ℤ_[l] :=
  {c | ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ (W - zc l c * W') ≤ ρ ^ k * gC l ρ W'}

/- English proof (translation)
Rewrite using `[← isOpen_compl_iff, Metric.isOpen_iff]`. Introduce `c hc`. Simplify using `only [digitSet, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_le] at hc`. Take `⟨ρ, h0, h1, hlt⟩` from `hc`. Use `⟨(l : ℝ) ^ (-(k : ℤ)), zpow_pos (by linarith [(one_lt_l : (1 : ℝ) < l)]) _, fun c' hc' hT => ?_⟩` and prove the remaining obligations.

Rewrite `hc'` using `[Metric.mem_ball, dist_eq_norm]`. Establish `hmem : c - c' ∈ Ideal.span {(l : ℤ_[l]) ^ k}`. Rewrite using `[← PadicInt.norm_le_pow_iff_mem_span_pow, norm_sub_rev]`. Conclude with `hc'.le`. Take `⟨y, hy⟩` from `Ideal.mem_span_singleton'.1 hmem`.

Establish `hp` using `pert h0 h1 W W' c' y k`. Establish `e : c' + (l : ℤ_[l]) ^ k * y = c` using `by rw [mul_comm, hy]; ring`. Rewrite `hp` using `[e]`. Conclude with `absurd (hp.trans (max_le (hT ρ h0 h1) le_rfl)) (not_le.2 hlt)`.
-/
theorem isClosed_digitSet (W W' : Formalism.Per.Acris l) (k : ℕ) : IsClosed (digitSet W W' k) := by
  rw [← isOpen_compl_iff, Metric.isOpen_iff]
  intro c hc
  simp only [digitSet, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_le] at hc
  obtain ⟨ρ, h0, h1, hlt⟩ := hc
  refine ⟨(l : ℝ) ^ (-(k : ℤ)), zpow_pos (by linarith [(one_lt_l : (1 : ℝ) < l)]) _, fun c' hc' hT => ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hc'
  have hmem : c - c' ∈ Ideal.span {(l : ℤ_[l]) ^ k} := by
    rw [← PadicInt.norm_le_pow_iff_mem_span_pow, norm_sub_rev]
    exact hc'.le
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hmem
  have hp := pert h0 h1 W W' c' y k
  have e : c' + (l : ℤ_[l]) ^ k * y = c := by rw [mul_comm, hy]; ring
  rw [e] at hp
  exact absurd (hp.trans (max_le (hT ρ h0 h1) le_rfl)) (not_le.2 hlt)

/- English proof (translation)
Establish `hl : (1 : ℝ) < l` using `one_lt_l`. Establish `hρ0 : 0 < ρ` using `rho_pos h0`. Establish `hr : -Real.logb l ρ ∈ Set.Ioc (0 : ℝ) 1`. Prove the components needed by the constructor for the conclusion. Combine the linear relations using `[Real.logb_neg hl hρ0 h1]`.

Use `(Real.logb_le_logb hl inv_l_pos hρ0).2 h0` as an intermediate fact. Rewrite `this` using `[Real.logb_inv, Real.logb_self_eq_one hl]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e` using `hn _ hr`. Establish `hpow : (l : ℝ) ^ (-(-Real.logb l ρ)) = ρ`.

Rewrite using `[neg_neg, Real.rpow_logb (by linarith) (ne_of_gt hl) hρ0]`. Simplify using `only [vr] at e`. Rewrite `e` using `[hpow]`. Establish `hV0` using `GlobalTheory.T.gaussNormAcrisRadius_pos_definite l V hV ρ h0 h1`. Establish `hW0` using `GlobalTheory.T.gaussNormAcrisRadius_pos_definite l W' hW' ρ h0 h1`.

Apply `Real.logb_injOn_pos hl hV0 (mul_pos (zpow_pos hρ0 n) hW0)` to reduce the goal to its premises. Establish `hz : Real.logb l (ρ ^ n) = n * Real.logb l ρ`. Simplify using `only [Real.logb, Real.log_zpow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Real.logb_mul (ne_of_gt (zpow_pos hρ0 n)) (ne_of_gt hW0), hz]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gC_eq_of_vr {V W' : Formalism.Per.Acris l} (hV : V ≠ 0) (hW' : W' ≠ 0) (n : ℤ)
    (hn : ∀ r ∈ Set.Ioc (0 : ℝ) 1, vr l r V - vr l r W' = n * r) {ρ : ℝ} (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) :
    gC l ρ V = ρ ^ n * gC l ρ W' := by
  have hl : (1 : ℝ) < l := one_lt_l
  have hρ0 : 0 < ρ := rho_pos h0
  have hr : -Real.logb l ρ ∈ Set.Ioc (0 : ℝ) 1 := by
    constructor
    · linarith [Real.logb_neg hl hρ0 h1]
    · have := (Real.logb_le_logb hl inv_l_pos hρ0).2 h0
      rw [Real.logb_inv, Real.logb_self_eq_one hl] at this
      linarith
  have e := hn _ hr
  have hpow : (l : ℝ) ^ (-(-Real.logb l ρ)) = ρ := by
    rw [neg_neg, Real.rpow_logb (by linarith) (ne_of_gt hl) hρ0]
  simp only [vr] at e
  rw [hpow] at e
  have hV0 := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l V hV ρ h0 h1
  have hW0 := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l W' hW' ρ h0 h1
  apply Real.logb_injOn_pos hl hV0 (mul_pos (zpow_pos hρ0 n) hW0)
  have hz : Real.logb l (ρ ^ n) = n * Real.logb l ρ := by
    simp only [Real.logb, Real.log_zpow]
    ring
  rw [Real.logb_mul (ne_of_gt (zpow_pos hρ0 n)) (ne_of_gt hW0), hz]
  linarith

/- English proof (translation)
Establish `hrV : φc l (W - zc l c * W') * W' = (W - zc l c * W') * φc l W'`. Rewrite using `[map_sub, map_mul, phi_zc]`. Take the linear combination `hr`. Distinguish the cases in `hV0 : W - zc l c * W' = 0`. Use `⟨c, fun ρ h0 h1 => ?_⟩` and prove the remaining obligations.

Rewrite using `[hV0, gC_zero h0 h1]`. Conclude with `mul_nonneg (pow_nonneg (rho_pos h0).le _) ((gauss h0 h1).1 _).1`. Take `⟨n, hn⟩` from `GlobalTheory.T.acrisValuation_sub_eq_int_mul_radius l h s hs _ W' he hV0 hW' hrV`. Establish `hg : ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ (W - zc l c * W') = ρ ^ n * gC l ρ W'` using `fun ρ h0 h1 => gC_eq_of_vr hV0 hW' n hn h0 h1`. Establish `hW0` using `GlobalTheory.T.gaussNormAcrisRadius_pos_definite l W' hW' _ le_rfl inv_l_lt_one`.

Establish `hk : (k : ℤ) ≤ n`. Establish `a` using `hc _ le_rfl inv_l_lt_one`. Rewrite `a` using `[hg _ le_rfl inv_l_lt_one]`. Establish `b` using `le_of_mul_le_mul_right a hW0`. Rewrite `b` using `[← zpow_natCast]`.

Conclude with `(zpow_le_zpow_iff_right_of_lt_one₀ inv_l_pos inv_l_lt_one).1 b`. Take `⟨m, rfl⟩ : ∃ m : ℕ, n = m` from `⟨n.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩`. Establish `hkm : k ≤ m` using `by exact_mod_cast hk`. Take `⟨u, -, hu⟩` from `GlobalTheory.T.gaussNormAcris_sub_unit_le_digit l h s hs (W - zc l c * W') ((l : Formalism.Per.Acris l) ^ m * W') (by rw [iter_lpow, he]; ring) (lpow_ne_zero hW' m) (by rw [map_mul, map_pow, map_natCast]; linear_combination (l : Formalism.Per.Acris l) ^ m * hrV) (fun ρ h0 h1 => b …`. Use `⟨c + u * (l : ℤ_[l]) ^ m, fun ρ h0 h1 => ?_⟩` and prove the remaining obligations.

Establish `e : W - zc l (c + u * (l : ℤ_[l]) ^ m) * W' = (W - zc l c * W') - zc l u * ((l : Formalism.Per.Acris l) ^ m * W')`. Simplify using `only [map_add, map_mul, map_pow, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `(hu ρ h0 h1).trans ?_` and prove the remaining obligations.

Rewrite using `[gC_lpow h0 h1, ← mul_assoc, ← pow_succ']`. Conclude with `mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (rho_pos h0).le h1.le (by omega)) ((gauss h0 h1).1 _).1`.
-/
theorem digit_step {h s : ℕ} (hs : s < h) {W W' : Formalism.Per.Acris l}
    (he : (φc l)^[h] W' = (l : Formalism.Per.Acris l) ^ s * W') (hW' : W' ≠ 0)
    (hr : φc l W * W' = W * φc l W') (k : ℕ) (c : ℤ_[l]) (hc : c ∈ digitSet W W' k) :
    (digitSet W W' (k + 1)).Nonempty := by
  have hrV : φc l (W - zc l c * W') * W' = (W - zc l c * W') * φc l W' := by
    rw [map_sub, map_mul, phi_zc]
    linear_combination hr
  by_cases hV0 : W - zc l c * W' = 0
  · refine ⟨c, fun ρ h0 h1 => ?_⟩
    rw [hV0, gC_zero h0 h1]
    exact mul_nonneg (pow_nonneg (rho_pos h0).le _) ((gauss h0 h1).1 _).1
  obtain ⟨n, hn⟩ := GlobalTheory.T.acrisValuation_sub_eq_int_mul_radius l h s hs _ W' he hV0 hW' hrV
  have hg : ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ (W - zc l c * W') = ρ ^ n * gC l ρ W' :=
    fun ρ h0 h1 => gC_eq_of_vr hV0 hW' n hn h0 h1
  have hW0 := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l W' hW' _ le_rfl inv_l_lt_one
  have hk : (k : ℤ) ≤ n := by
    have a := hc _ le_rfl inv_l_lt_one
    rw [hg _ le_rfl inv_l_lt_one] at a
    have b := le_of_mul_le_mul_right a hW0
    rw [← zpow_natCast] at b
    exact (zpow_le_zpow_iff_right_of_lt_one₀ inv_l_pos inv_l_lt_one).1 b
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hkm : k ≤ m := by exact_mod_cast hk
  obtain ⟨u, -, hu⟩ := GlobalTheory.T.gaussNormAcris_sub_unit_le_digit l h s hs (W - zc l c * W') ((l : Formalism.Per.Acris l) ^ m * W')
    (by rw [iter_lpow, he]; ring) (lpow_ne_zero hW' m)
    (by rw [map_mul, map_pow, map_natCast]; linear_combination (l : Formalism.Per.Acris l) ^ m * hrV)
    (fun ρ h0 h1 => by rw [hg ρ h0 h1, gC_lpow h0 h1, zpow_natCast])
  refine ⟨c + u * (l : ℤ_[l]) ^ m, fun ρ h0 h1 => ?_⟩
  have e : W - zc l (c + u * (l : ℤ_[l]) ^ m) * W' =
      (W - zc l c * W') - zc l u * ((l : Formalism.Per.Acris l) ^ m * W') := by
    simp only [map_add, map_mul, map_pow, map_natCast]
    ring
  rw [e]
  refine (hu ρ h0 h1).trans ?_
  rw [gC_lpow h0 h1, ← mul_assoc, ← pow_succ']
  exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (rho_pos h0).le h1.le (by omega))
    ((gauss h0 h1).1 _).1

/- English proof (translation)
Establish `hmono : ∀ i, digitSet W W' (i + 1) ⊆ digitSet W W' i` using `fun i c hc ρ h0 h1 => (hc ρ h0 h1).trans (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (rho_pos h0).le h1.le (Nat.le_succ i)) ((gauss h0 h1).1 _).1)`. Establish `hne : ∀ i, (digitSet W W' i).Nonempty`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => exact ⟨0, fun ρ h0 h1 => by rw [map_zero, zero_mul, sub_zero, pow_zero, one_mul, hg ρ h0 h1]⟩`.

Consider the case `succ i ih`. Take `⟨c, hc⟩` from `ih`. Conclude with `digit_step hs he hW' hr i c hc`. Take `⟨c, hc⟩` from `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _ hmono hne (isCompact_univ.of_isClosed_subset (isClosed_digitSet W W' 0) (Set.subset_univ _)) (isClosed_digitSet W W')`. Rewrite `hc` using `[Set.mem_iInter]`.

Use `⟨c, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne'`. Establish `hpos` using `GlobalTheory.T.gaussNormAcrisRadius_pos_definite l (W - zc l c * W') (sub_ne_zero.2 hne') _ le_rfl inv_l_lt_one`. Establish `hlim : Filter.Tendsto (fun i : ℕ => (l : ℝ)⁻¹ ^ i * gC l (l : ℝ)⁻¹ W') Filter.atTop (nhds 0)`. Simplify using `using (tendsto_pow_atTop_nhds_zero_of_lt_one inv_l_pos.le inv_l_lt_one).mul_const (gC l (l : ℝ)⁻¹ W')`.

Use `ge_of_tendsto' hlim (fun i => hc i _ le_rfl inv_l_lt_one)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem eq_zc_mul {h s : ℕ} (hs : s < h) {W W' : Formalism.Per.Acris l}
    (he : (φc l)^[h] W' = (l : Formalism.Per.Acris l) ^ s * W') (hW' : W' ≠ 0)
    (hr : φc l W * W' = W * φc l W')
    (hg : ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ W = gC l ρ W') :
    ∃ c : ℤ_[l], W = zc l c * W' := by
  have hmono : ∀ i, digitSet W W' (i + 1) ⊆ digitSet W W' i := fun i c hc ρ h0 h1 =>
    (hc ρ h0 h1).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one (rho_pos h0).le h1.le (Nat.le_succ i)) ((gauss h0 h1).1 _).1)
  have hne : ∀ i, (digitSet W W' i).Nonempty := by
    intro i
    induction i with
    | zero => exact ⟨0, fun ρ h0 h1 => by rw [map_zero, zero_mul, sub_zero, pow_zero, one_mul, hg ρ h0 h1]⟩
    | succ i ih =>
      obtain ⟨c, hc⟩ := ih
      exact digit_step hs he hW' hr i c hc
  obtain ⟨c, hc⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _ hmono hne
    (isCompact_univ.of_isClosed_subset (isClosed_digitSet W W' 0) (Set.subset_univ _))
    (isClosed_digitSet W W')
  rw [Set.mem_iInter] at hc
  refine ⟨c, ?_⟩
  by_contra hne'
  have hpos := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l (W - zc l c * W') (sub_ne_zero.2 hne') _ le_rfl inv_l_lt_one
  have hlim : Filter.Tendsto (fun i : ℕ => (l : ℝ)⁻¹ ^ i * gC l (l : ℝ)⁻¹ W') Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one inv_l_pos.le inv_l_lt_one).mul_const
      (gC l (l : ℝ)⁻¹ W')
  have := ge_of_tendsto' hlim (fun i => hc i _ le_rfl inv_l_lt_one)
  linarith

end RatioProp

open RatioProp in

/- English proof (translation)
Introduce `l _ h s hs w w' _ he' hw' hr`. Distinguish the cases in `hw : w = 0`. Conclude with `⟨1, 0, one_ne_zero, by rw [hw, mul_zero, map_zero, zero_mul]⟩`. Take `⟨n, hn⟩` from `GlobalTheory.T.acrisValuation_sub_eq_int_mul_radius l h s hs w w' he' hw hw' hr`. Establish `hg : ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ w = ρ ^ n * gC l ρ w'` using `fun ρ h0 h1 => gC_eq_of_vr hw hw' n hn h0 h1`.

Break down `le_or_gt 0 n with hn0 | hn0` into its components or cases. Take `⟨m, rfl⟩ : ∃ m : ℕ, n = m` from `⟨n.toNat, (Int.toNat_of_nonneg hn0).symm⟩`. Take `⟨c, hc⟩` from `eq_zc_mul hs (W := w) (W' := (l : Formalism.Per.Acris l) ^ m * w') (by rw [iter_lpow, he']; ring) (lpow_ne_zero hw' m) (by rw [map_mul, map_pow, map_natCast]; linear_combination (l : Formalism.Per.Acris l) ^ m * hr) (fun ρ h0 h1 => by rw [hg ρ h0 h1, gC_lpow h0 h1, zpow_natCast])`. Use `⟨1, c * (l : ℤ_[l]) ^ m, one_ne_zero, ?_⟩` and prove the remaining obligations. Rewrite using `[map_one, one_mul, hc, map_mul, map_pow, map_natCast]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = -n` from `⟨(-n).toNat, Int.toNat_of_nonneg (by omega)⟩`. Take `⟨c, hc⟩` from `eq_zc_mul hs (W := (l : Formalism.Per.Acris l) ^ m * w) (W' := w') he' hw' (by rw [map_mul, map_pow, map_natCast]; linear_combination (l : Formalism.Per.Acris l) ^ m * hr) (fun ρ h0 h1 => by`. Rewrite using `[gC_lpow h0 h1, hg ρ h0 h1, ← mul_assoc, ← zpow_natCast, hm, ← zpow_add₀ (ne_of_gt (rho_pos h0)), neg_add_cancel, zpow_zero, one_mul])`. Use `⟨(l : ℤ_[l]) ^ m, c, pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero), ?_⟩` and prove the remaining obligations.

Rewrite using `[map_pow, map_natCast, hc]`.
-/
theorem ratio_proportional_target : ∀ (l : ℕ) [Fact l.Prime] (h s : ℕ), s < h → ∀ w w' : Formalism.Per.Acris l,
    (φc l)^[h] w = (l : Formalism.Per.Acris l) ^ s * w → (φc l)^[h] w' = (l : Formalism.Per.Acris l) ^ s * w' → w' ≠ 0 →
    φc l w * w' = w * φc l w' → ∃ c d : ℤ_[l], c ≠ 0 ∧ zc l c * w = zc l d * w' := by
  intro l _ h s hs w w' _ he' hw' hr
  by_cases hw : w = 0
  · exact ⟨1, 0, one_ne_zero, by rw [hw, mul_zero, map_zero, zero_mul]⟩
  obtain ⟨n, hn⟩ := GlobalTheory.T.acrisValuation_sub_eq_int_mul_radius l h s hs w w' he' hw hw' hr
  have hg : ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ w = ρ ^ n * gC l ρ w' :=
    fun ρ h0 h1 => gC_eq_of_vr hw hw' n hn h0 h1
  rcases le_or_gt 0 n with hn0 | hn0
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, (Int.toNat_of_nonneg hn0).symm⟩
    obtain ⟨c, hc⟩ := eq_zc_mul hs (W := w) (W' := (l : Formalism.Per.Acris l) ^ m * w')
      (by rw [iter_lpow, he']; ring) (lpow_ne_zero hw' m)
      (by rw [map_mul, map_pow, map_natCast]; linear_combination (l : Formalism.Per.Acris l) ^ m * hr)
      (fun ρ h0 h1 => by rw [hg ρ h0 h1, gC_lpow h0 h1, zpow_natCast])
    refine ⟨1, c * (l : ℤ_[l]) ^ m, one_ne_zero, ?_⟩
    rw [map_one, one_mul, hc, map_mul, map_pow, map_natCast]
    ring
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = -n := ⟨(-n).toNat, Int.toNat_of_nonneg (by omega)⟩
    obtain ⟨c, hc⟩ := eq_zc_mul hs (W := (l : Formalism.Per.Acris l) ^ m * w) (W' := w') he' hw'
      (by rw [map_mul, map_pow, map_natCast]; linear_combination (l : Formalism.Per.Acris l) ^ m * hr)
      (fun ρ h0 h1 => by
        rw [gC_lpow h0 h1, hg ρ h0 h1, ← mul_assoc, ← zpow_natCast, hm,
          ← zpow_add₀ (ne_of_gt (rho_pos h0)), neg_add_cancel, zpow_zero, one_mul])
    refine ⟨(l : ℤ_[l]) ^ m, c, pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero), ?_⟩
    rw [map_pow, map_natCast, hc]

end GlobalTheory.PMon.Gauss
