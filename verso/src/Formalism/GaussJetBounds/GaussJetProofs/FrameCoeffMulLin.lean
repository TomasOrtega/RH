import Formalism.GaussJetBounds.StatementC
import Formalism.GaussJetBounds.GaussJetProofs.AsmRDotAddRight

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

section Rank

end Rank

section Pure

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Rewrite using `[Finset.sum_empty, Finset.sum_empty, zero_pow (pow_ne_zero _ hl.ne_zero), sub_zero, norm_zero]`. Conclude with `norm_nonneg _`. Consider the case `insert a S ha ih`.

Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha]`. Establish `hV : ‖∑ b ∈ S, U b‖ ≤ 1` using `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun b _ => hU b)`. Choose the witnesses or unpack the hypotheses as in `⟨R, hReq, hRle⟩ : ∃ R : K, (U a + ∑ b ∈ S, U b) ^ (l ^ e) = U a ^ (l ^ e) + (∑ b ∈ S, U b) ^ (l ^ e) + (l : K) * R ∧ ‖R‖ ≤ 1 := by`. Use `⟨_, add_pow_prime_pow_eq' hl (U a) (∑ b ∈ S, U b) e, ?_⟩` and prove the remaining obligations. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun k _ => ?_)` and prove the remaining obligations.

Rewrite using `[norm_mul, norm_mul, norm_pow, norm_pow]`. Establish `h1 : ‖U a‖ ^ k ≤ 1` using `pow_le_one₀ (norm_nonneg _) (hU a)`. Establish `h2 : ‖∑ b ∈ S, U b‖ ^ (l ^ e - k) ≤ 1` using `pow_le_one₀ (norm_nonneg _) hV`. Establish `h3` using `IsUltrametricDist.norm_natCast_le_one K ((l ^ e).choose k / l)`. Combine the equalities or inequalities in the displayed calculation.

Establish `heq : (U a + ∑ b ∈ S, U b) ^ (l ^ e) - (U a ^ (l ^ e) + ∑ b ∈ S, U b ^ (l ^ e)) = ((∑ b ∈ S, U b) ^ (l ^ e) - ∑ b ∈ S, U b ^ (l ^ e)) + (l : K) * R`. Rewrite using `[hReq]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[heq]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih ?_)` and prove the remaining obligations.

Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem frame_frob_norm {K : Type*} [NormedField K] [IsUltrametricDist K] {l : ℕ}
    (hl : l.Prime) {ι : Type*} (U : ι → K) (hU : ∀ a, ‖U a‖ ≤ 1) (e : ℕ) (S : Finset ι) :
    ‖(∑ a ∈ S, U a) ^ (l ^ e) - ∑ a ∈ S, U a ^ (l ^ e)‖ ≤ ‖(l : K)‖ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, zero_pow (pow_ne_zero _ hl.ne_zero), sub_zero,
      norm_zero]
    exact norm_nonneg _
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hV : ‖∑ b ∈ S, U b‖ ≤ 1 :=
      IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun b _ => hU b)
    obtain ⟨R, hReq, hRle⟩ : ∃ R : K, (U a + ∑ b ∈ S, U b) ^ (l ^ e) =
        U a ^ (l ^ e) + (∑ b ∈ S, U b) ^ (l ^ e) + (l : K) * R ∧ ‖R‖ ≤ 1 := by
      refine ⟨_, add_pow_prime_pow_eq' hl (U a) (∑ b ∈ S, U b) e, ?_⟩
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun k _ => ?_)
      rw [norm_mul, norm_mul, norm_pow, norm_pow]
      have h1 : ‖U a‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) (hU a)
      have h2 : ‖∑ b ∈ S, U b‖ ^ (l ^ e - k) ≤ 1 := pow_le_one₀ (norm_nonneg _) hV
      have h3 := IsUltrametricDist.norm_natCast_le_one K ((l ^ e).choose k / l)
      calc ‖U a‖ ^ k * ‖∑ b ∈ S, U b‖ ^ (l ^ e - k) * ‖(((l ^ e).choose k / l : ℕ) : K)‖
          ≤ 1 * 1 * 1 := by gcongr
        _ = 1 := by ring
    have heq : (U a + ∑ b ∈ S, U b) ^ (l ^ e) - (U a ^ (l ^ e) + ∑ b ∈ S, U b ^ (l ^ e)) =
        ((∑ b ∈ S, U b) ^ (l ^ e) - ∑ b ∈ S, U b ^ (l ^ e)) + (l : K) * R := by
      rw [hReq]; ring
    rw [heq]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih ?_)
    rw [norm_mul]
    calc ‖(l : K)‖ * ‖R‖ ≤ ‖(l : K)‖ * 1 := by gcongr
      _ = ‖(l : K)‖ := mul_one _

/- English proof (translation)
Rewrite using `[Finset.mul_sum, MvPolynomial.coeff_sum]`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Rewrite using `[mul_left_comm, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_mul_X']`.
-/
private theorem frame_coeff_mul_lin {R ι : Type*} [CommSemiring R] [Fintype ι] [DecidableEq ι]
    (Q : MvPolynomial ι R) (c : ι → R) (m : ι →₀ ℕ) :
    MvPolynomial.coeff m (Q * ∑ y, MvPolynomial.C (c y) * MvPolynomial.X y) =
      ∑ y, c y * (if y ∈ m.support then MvPolynomial.coeff (m - Finsupp.single y 1) Q else 0) := by
  rw [Finset.mul_sum, MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [mul_left_comm, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_mul_X']

/- English proof (translation)
Proceed by induction on `B with`. Consider the case `zero => simp`. Consider the case `succ B ih`. Rewrite using `[pow_succ, frame_coeff_mul_lin, Finset.sum_eq_single j]`. Rewrite using `[if_pos (by simp), ← Finsupp.single_tsub, Nat.add_sub_cancel, ih, pow_succ, mul_comm]`.

Introduce `y _ hy`. Rewrite using `[if_neg (by simp [Ne.symm hy]), mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ j) h`.
-/
private theorem frame_coeff_pow_lin {R ι : Type*} [CommSemiring R] [Fintype ι] [DecidableEq ι]
    (c : ι → R) (j : ι) (B : ℕ) :
    MvPolynomial.coeff (Finsupp.single j B)
      ((∑ y, MvPolynomial.C (c y) * MvPolynomial.X y) ^ B) = c j ^ B := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [pow_succ, frame_coeff_mul_lin, Finset.sum_eq_single j]
    · rw [if_pos (by simp), ← Finsupp.single_tsub, Nat.add_sub_cancel, ih, pow_succ, mul_comm]
    · intro y _ hy
      rw [if_neg (by simp [Ne.symm hy]), mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h

/- English proof (translation)
Proceed by induction on `A with`. Consider the case `zero => simp [frame_coeff_pow_lin]`. Consider the case `succ A ih`. Rewrite using `[pow_succ, ← mul_assoc, frame_coeff_mul_lin, Finset.sum_eq_single i]`. Establish `hmem : i ∈ (Finsupp.single i (A + 1) + Finsupp.single j B).support`.

Rewrite using `[Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same]`. Use linear arithmetic over natural numbers and integers. Establish `hsub : Finsupp.single i (A + 1) + Finsupp.single j B - Finsupp.single i 1 = Finsupp.single i A + Finsupp.single j B`. Use extensionality with `y`. Simplify using `only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.add_apply, Finsupp.single_apply]`.

Distinguish the cases in `h1 : i = y`. Substitute `h1` using the available equality. Simplify using `[Ne.symm hij]`. Simplify using `[h1]`. Rewrite using `[if_pos hmem, hsub, ih, pow_succ]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `y _ hy`. Distinguish the cases in `hcy : c y = 0`. Rewrite using `[hcy, zero_mul]`. Rewrite using `[if_neg, mul_zero]`.

Rewrite using `[Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply, if_neg (Ne.symm hy), if_neg (Ne.symm (hc y hcy))]`. Simplify using the standard rewrite rules. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.
-/
private theorem frame_coeff_two {R ι : Type*} [CommSemiring R] [Fintype ι] [DecidableEq ι]
    (c c' : ι → R) (i j : ι) (hij : i ≠ j) (hc : ∀ y, c y ≠ 0 → y ≠ j) (A B : ℕ) :
    MvPolynomial.coeff (Finsupp.single i A + Finsupp.single j B)
      ((∑ y, MvPolynomial.C (c' y) * MvPolynomial.X y) ^ B *
        (∑ y, MvPolynomial.C (c y) * MvPolynomial.X y) ^ A) = c i ^ A * c' j ^ B := by
  induction A with
  | zero => simp [frame_coeff_pow_lin]
  | succ A ih =>
    rw [pow_succ, ← mul_assoc, frame_coeff_mul_lin, Finset.sum_eq_single i]
    · have hmem : i ∈ (Finsupp.single i (A + 1) + Finsupp.single j B).support := by
        rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same]; omega
      have hsub : Finsupp.single i (A + 1) + Finsupp.single j B - Finsupp.single i 1 =
          Finsupp.single i A + Finsupp.single j B := by
        ext y
        simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.add_apply, Finsupp.single_apply]
        by_cases h1 : i = y
        · subst h1; simp [Ne.symm hij]
        · simp [h1]
      rw [if_pos hmem, hsub, ih, pow_succ]; ring
    · intro y _ hy
      by_cases hcy : c y = 0
      · rw [hcy, zero_mul]
      · rw [if_neg, mul_zero]
        rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply,
          if_neg (Ne.symm hy), if_neg (Ne.symm (hc y hcy))]
        simp
    · intro h; exact absurd (Finset.mem_univ i) h

/- English proof (translation)
Use `MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun y _ => ?_` and prove the remaining obligations. Distinguish the cases in `hcy : c y = 0`. Rewrite using `[hcy, map_zero, zero_mul]`. Conclude with `MvPolynomial.isWeightedHomogeneous_zero R _ _`. Establish `h1` using `(MvPolynomial.isWeightedHomogeneous_X R (fun y => Finsupp.single (lt y) 1) y).C_mul (c y)`.

Establish `h2 : Finsupp.single t 1 = (fun y => Finsupp.single (lt y) 1) y` using `by simp [hc y hcy]`. Rewrite using `[h2]`. Conclude with `h1`.
-/
private theorem frame_lin_hom {R ι τ : Type*} [CommSemiring R] [Fintype ι] (lt : ι → τ)
    (c : ι → R) (t : τ) (hc : ∀ y, c y ≠ 0 → lt y = t) :
    MvPolynomial.IsWeightedHomogeneous (fun y => Finsupp.single (lt y) 1)
      (∑ y, MvPolynomial.C (c y) * MvPolynomial.X y) (Finsupp.single t 1) := by
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun y _ => ?_
  by_cases hcy : c y = 0
  · rw [hcy, map_zero, zero_mul]; exact MvPolynomial.isWeightedHomogeneous_zero R _ _
  · have h1 := (MvPolynomial.isWeightedHomogeneous_X R
      (fun y => Finsupp.single (lt y) 1) y).C_mul (c y)
    have h2 : Finsupp.single t 1 = (fun y => Finsupp.single (lt y) 1) y := by simp [hc y hcy]
    rw [h2]; exact h1

/- English proof (translation)
Establish `h1` using `MvPolynomial.IsWeightedHomogeneous.prod e.support (fun t => P t ^ e t) (fun t => e t • Finsupp.single t 1) (fun t _ => (hP t).pow (e t))`. Establish `h2 : (∑ t ∈ e.support, e t • Finsupp.single t 1) = e`. Repeatedly rewrite using `[Finsupp.smul_single_one]`. Conclude with `Finsupp.sum_single e`. Rewrite `h1` using `[h2]`.

Conclude with `h1`.
-/
private theorem frame_prod_hom {R ι τ : Type*} [CommSemiring R] (lt : ι → τ)
    (P : τ → MvPolynomial ι R)
    (hP : ∀ t, MvPolynomial.IsWeightedHomogeneous (fun y => Finsupp.single (lt y) 1) (P t)
      (Finsupp.single t 1)) (e : τ →₀ ℕ) :
    MvPolynomial.IsWeightedHomogeneous (fun y => Finsupp.single (lt y) 1)
      (e.prod fun t k => P t ^ k) e := by
  have h1 := MvPolynomial.IsWeightedHomogeneous.prod e.support (fun t => P t ^ e t)
    (fun t => e t • Finsupp.single t 1) (fun t _ => (hP t).pow (e t))
  have h2 : (∑ t ∈ e.support, e t • Finsupp.single t 1) = e := by
    simp_rw [Finsupp.smul_single_one]
    exact Finsupp.sum_single e
  rw [h2] at h1
  exact h1

/- English proof (translation)
Unfold `bSum`. Rewrite using `[map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun ab _ => ?_` and prove the remaining obligations. Use `set φ : MvPolynomial ι K →+* MvPowerSeries ι K := MvPolynomial.coeToMvPowerSeries.ringHom with hφ`. Use `set P : ZMod d → MvPolynomial ι K := fun t => ∑ y, MvPolynomial.C (M (t, ab.1, ab.2) y) * MvPolynomial.X y with hPdef`.

Establish `hL : ∀ t, linSub M (t, ab.1, ab.2) = φ (P t)`. Introduce `t`. Simplify using `only [linSub, hPdef, hφ, map_sum, map_mul, MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_C, MvPolynomial.coe_X]`. Establish `hsub : MvPowerSeries.HasSubst (fun t => linSub (K` using `K) M (t, ab.1, ab.2)) := by`. Apply `MvPowerSeries.hasSubst_of_constantCoeff_zero` to reduce the goal to its premises.

Introduce `t`. Simplify using `[linSub]`. Establish `hPh : ∀ t, MvPolynomial.IsWeightedHomogeneous (fun y => Finsupp.single (lt y) 1) (P t) (Finsupp.single t 1)` using `fun t => frame_lin_hom lt (fun y => M (t, ab.1, ab.2) y) t (fun y hy => hM _ y hy)`. Establish `hwt : Finsupp.weight (fun y => Finsupp.single (lt y) 1) (Finsupp.single i A + Finsupp.single j B) = Finsupp.single (lt i) A + Finsupp.single (lt j) B`. Simplify using `only [map_add, Finsupp.weight_single, Finsupp.smul_single_one]`.

Establish `hij' : i ≠ j` using `fun h => hij (congrArg lt h)`. Establish `hterm : ∀ e : ZMod d →₀ ℕ, MvPowerSeries.coeff (Finsupp.single i A + Finsupp.single j B) (e.prod fun t k => linSub M (t, ab.1, ab.2) ^ k) = if e = Finsupp.single (lt i) A + Finsupp.single (lt j) B then M (lt i, ab.1, ab.2) i ^ A * M (lt j, ab.1, ab.2) j ^ B else 0`. Introduce `e`. Establish `hprod : (e.prod fun t k => linSub M (t, ab.1, ab.2) ^ k) = φ (e.prod fun t k => P t ^ k)`. Simplify using `only [hL, ← map_pow]`.

Conclude with `(map_finsuppProd φ e _).symm`. Rewrite using `[hprod, hφ, MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coeff_coe]`. Use `split_ifs with he`. Rewrite using `[he, Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), Finsupp.prod_single_index (h := fun t k => P t ^ k) (by simp), Finsupp.prod_single_index (h := fun t k => P t ^ k) (by simp), mul_comm]`. Conclude with `frame_coeff_two (fun y => M (lt i, ab.1, ab.2) y) (fun y => M (lt j, ab.1, ab.2) y) i j hij' (fun y hy hyj => hij ((hM _ y hy).symm.trans (by rw [hyj]))) A B`.

Assume the negation of the conclusion as `hne`. Conclude with `he ((frame_prod_hom lt P hPh e hne).symm.trans hwt)`. Rewrite using `[MvPowerSeries.coeff_subst hsub, finsum_eq_single _ (Finsupp.single (lt i) A + Finsupp.single (lt j) B) (fun e he => by rw [hterm, if_neg he, smul_zero]), hterm, if_pos rfl, smul_eq_mul]`.
-/
private theorem frame_pure_formula {K : Type u} [Field K] {d N0 N1 : ℕ} [NeZero d]
    {ι : Type} [Fintype ι] [DecidableEq ι] (lt : ι → ZMod d) (M : ZV d N0 N1 → ι → K)
    (hM : ∀ x i, M x i ≠ 0 → lt i = x.1) (be : MvPowerSeries (ZMod d) K) (i j : ι) (A B : ℕ)
    (hij : lt i ≠ lt j) :
    MvPowerSeries.coeff (Finsupp.single i A + Finsupp.single j B) (bSum M be) =
      MvPowerSeries.coeff (Finsupp.single (lt i) A + Finsupp.single (lt j) B) be *
        ∑ ab : Fin N0 × Fin N1, M (lt i, ab.1, ab.2) i ^ A * M (lt j, ab.1, ab.2) j ^ B := by
  classical
  unfold bSum
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ab _ => ?_
  set φ : MvPolynomial ι K →+* MvPowerSeries ι K := MvPolynomial.coeToMvPowerSeries.ringHom
    with hφ
  set P : ZMod d → MvPolynomial ι K :=
    fun t => ∑ y, MvPolynomial.C (M (t, ab.1, ab.2) y) * MvPolynomial.X y with hPdef
  have hL : ∀ t, linSub M (t, ab.1, ab.2) = φ (P t) := by
    intro t
    simp only [linSub, hPdef, hφ, map_sum, map_mul, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
      MvPolynomial.coe_C, MvPolynomial.coe_X]
  have hsub : MvPowerSeries.HasSubst (fun t => linSub (K := K) M (t, ab.1, ab.2)) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro t; simp [linSub]
  have hPh : ∀ t, MvPolynomial.IsWeightedHomogeneous (fun y => Finsupp.single (lt y) 1) (P t)
      (Finsupp.single t 1) := fun t =>
    frame_lin_hom lt (fun y => M (t, ab.1, ab.2) y) t (fun y hy => hM _ y hy)
  have hwt : Finsupp.weight (fun y => Finsupp.single (lt y) 1)
      (Finsupp.single i A + Finsupp.single j B) =
      Finsupp.single (lt i) A + Finsupp.single (lt j) B := by
    simp only [map_add, Finsupp.weight_single, Finsupp.smul_single_one]
  have hij' : i ≠ j := fun h => hij (congrArg lt h)
  have hterm : ∀ e : ZMod d →₀ ℕ, MvPowerSeries.coeff (Finsupp.single i A + Finsupp.single j B)
      (e.prod fun t k => linSub M (t, ab.1, ab.2) ^ k) =
      if e = Finsupp.single (lt i) A + Finsupp.single (lt j) B then
        M (lt i, ab.1, ab.2) i ^ A * M (lt j, ab.1, ab.2) j ^ B else 0 := by
    intro e
    have hprod : (e.prod fun t k => linSub M (t, ab.1, ab.2) ^ k) =
        φ (e.prod fun t k => P t ^ k) := by
      simp only [hL, ← map_pow]
      exact (map_finsuppProd φ e _).symm
    rw [hprod, hφ, MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coeff_coe]
    split_ifs with he
    · rw [he, Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
        Finsupp.prod_single_index (h := fun t k => P t ^ k) (by simp),
        Finsupp.prod_single_index (h := fun t k => P t ^ k) (by simp), mul_comm]
      exact frame_coeff_two (fun y => M (lt i, ab.1, ab.2) y) (fun y => M (lt j, ab.1, ab.2) y)
        i j hij' (fun y hy hyj => hij ((hM _ y hy).symm.trans (by rw [hyj]))) A B
    · by_contra hne
      exact he ((frame_prod_hom lt P hPh e hne).symm.trans hwt)
  rw [MvPowerSeries.coeff_subst hsub, finsum_eq_single _
    (Finsupp.single (lt i) A + Finsupp.single (lt j) B)
    (fun e he => by rw [hterm, if_neg he, smul_zero]), hterm, if_pos rfl, smul_eq_mul]

/- English proof (translation)
Introduce `K _ _ _ l d N0 N1 _ hl hpi h0 x hx be hbe s s' hss' k b b' α β`. Establish `hM : ∀ (z y : ZV d N0 N1), frameM (N1` using `N1) x z y ≠ 0 → y.1 = z.1 := by`. Introduce `z y h`. Unfold `frameM at h`. Use `split_ifs at h with h1`.

Conclude with `h1.1`. Conclude with `absurd rfl h`. Establish `hform : ∀ b1 b2 : Fin N1, MvPowerSeries.coeff (pureMon l ((s, ⟨0, h0⟩, b1) : ZV d N0 N1) (s', k, b2) α β) (bSum (frameM (N1` using `N1) x) be) = MvPowerSeries.coeff (pureMon l s s' α β) be * ∑ ab : Fin N0 × Fin N1, frameM (N1 := N1) x (s, ab.1, ab.2) (s, ⟨0, h0⟩, b1) ^ (l ^ α) * frameM (N1 := N1) x (s', ab.1, ab.2) (s', k, b2) ^ (l ^ β) := by`. Introduce `b1 b2`. Unfold `pureMon`.

Conclude with `frame_pure_formula Prod.fst (frameM (N1 := N1) x) hM be _ _ _ _ hss'`. Establish `hz : ∀ m : ℕ, (0 : K) ^ (l ^ m) = 0` using `fun m => zero_pow (pow_ne_zero _ hl.ne_zero)`. Use `⟨fun hbb' => ?_, fun hyp => ?_⟩` and prove the remaining obligations. Rewrite using `[hform]`. Use `mul_eq_zero_of_right _ (Finset.sum_eq_zero fun ab _ => ?_)` and prove the remaining obligations.

Simplify using `only [frameM, true_and]`. Distinguish the cases in `h1 : b = ab.2`. Rewrite using `[if_pos h1, if_neg (fun h2 => hbb' (h1.trans h2.symm)), hz, mul_zero]`. Rewrite using `[if_neg h1, hz, zero_mul]`. Unfold `MonoWtGe`.

Rewrite using `[hform b b]`. Establish `hS : (∑ ab : Fin N0 × Fin N1, frameM (N1` using `N1) x (s, ab.1, ab.2) (s, ⟨0, h0⟩, b) ^ (l ^ α) * frameM (N1 := N1) x (s', ab.1, ab.2) (s', k, b) ^ (l ^ β)) = ∑ a : Fin N0, x (s, ⟨0, h0⟩, a) ^ (l ^ α) * x (s', k, a) ^ (l ^ β) := by`. Rewrite using `[Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `only [frameM, true_and]`.

Rewrite using `[Finset.sum_eq_single b (fun b'' _ hb'' => by rw [if_neg (Ne.symm hb''), hz, zero_mul]) (fun h => absurd (Finset.mem_univ b) h), if_pos rfl, if_pos rfl]`. Rewrite using `[hS]`. Establish `hsum1 : ∀ (U : Fin N0 → K), (∀ a, ‖U a‖ ≤ 1) → ‖∑ a, U a‖ ≤ ‖(l : K)‖ → ∀ e : ℕ, ‖∑ a, U a ^ (l ^ e)‖ ≤ ‖(l : K)‖`. Introduce `U hU hsU e`. Establish `hfr` using `frame_frob_norm hl U hU e Finset.univ`.

Establish `h1 : ‖(∑ a, U a) ^ (l ^ e)‖ ≤ ‖(l : K)‖`. Rewrite using `[norm_pow]`. Establish `hle1 : ‖∑ a, U a‖ ≤ 1` using `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun a _ => hU a)`. Conclude with `(pow_le_of_le_one (norm_nonneg _) hle1 (pow_ne_zero _ hl.ne_zero)).trans hsU`. Establish `heq : ∑ a, U a ^ (l ^ e) = (∑ a, U a) ^ (l ^ e) + -((∑ a, U a) ^ (l ^ e) - ∑ a, U a ^ (l ^ e))` using `by ring`.

Rewrite using `[heq]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 ?_)` and prove the remaining obligations. Rewrite using `[norm_neg]`. Conclude with `hfr`. Establish `hSn : ‖∑ a : Fin N0, x (s, ⟨0, h0⟩, a) ^ (l ^ α) * x (s', k, a) ^ (l ^ β)‖ ≤ ‖(l : K)‖` using `by split_ifs at hyp with hba`.

Establish `hU : ∀ a, ‖x (s, ⟨0, h0⟩, a) ^ (l ^ (α - β)) * x (s', k, a)‖ ≤ 1` using `fun a => by`. Rewrite using `[norm_mul, norm_pow]`. Conclude with `mul_le_one₀ (pow_le_one₀ (norm_nonneg _) (hx _)) (norm_nonneg _) (hx _)`. Establish `h` using `hsum1 _ hU hyp β`. Establish `hpow : ∀ a, (x (s, ⟨0, h0⟩, a) ^ (l ^ (α - β)) * x (s', k, a)) ^ (l ^ β) = x (s, ⟨0, h0⟩, a) ^ (l ^ α) * x (s', k, a) ^ (l ^ β)` using `fun a => by`.

Rewrite using `[mul_pow, ← pow_mul, ← pow_add, Nat.sub_add_cancel hba]`. Simplify `h` using `only [hpow]`. Establish `hU : ∀ a, ‖x (s, ⟨0, h0⟩, a) * x (s', k, a) ^ (l ^ (β - α))‖ ≤ 1` using `fun a => by`. Rewrite using `[norm_mul, norm_pow]`. Conclude with `mul_le_one₀ (hx _) (pow_nonneg (norm_nonneg _) _) (pow_le_one₀ (norm_nonneg _) (hx _))`.

Establish `h` using `hsum1 _ hU hyp α`. Establish `hpow : ∀ a, (x (s, ⟨0, h0⟩, a) * x (s', k, a) ^ (l ^ (β - α))) ^ (l ^ α) = x (s, ⟨0, h0⟩, a) ^ (l ^ α) * x (s', k, a) ^ (l ^ β)` using `fun a => by`. Rewrite using `[mul_pow, ← pow_mul, ← pow_add, Nat.sub_add_cancel (le_of_lt (not_le.mp hba))]`. Simplify `h` using `only [hpow]`. Establish `hc` using `hbe (pureMon l s s' α β)`.

Unfold `MonoWtGe at hc`. Rewrite `hc`, the goal using `[asmR_dot_pureMon]`. Establish `hπ : 0 < ‖(l : K)‖` using `norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.ne_zero)`. Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation.

Establish `he : 1 / ((l : ℝ) - 1) - ((l : ℝ) ^ α * rho l + (l : ℝ) ^ β * rho l) = (1 / ((l : ℝ) - 1) - 1 - ((l : ℝ) ^ α * rho l + (l : ℝ) ^ β * rho l)) + 1` using `by ring`. Rewrite using `[he, Real.rpow_add hπ, Real.rpow_one]`.
-/
theorem frame_pure_weight : FramePure.{u} := by
  intro K _ _ _ l d N0 N1 _ hl hpi h0 x hx be hbe s s' hss' k b b' α β
  classical
  have hM : ∀ (z y : ZV d N0 N1), frameM (N1 := N1) x z y ≠ 0 → y.1 = z.1 := by
    intro z y h
    unfold frameM at h
    split_ifs at h with h1
    · exact h1.1
    · exact absurd rfl h
  have hform : ∀ b1 b2 : Fin N1,
      MvPowerSeries.coeff (pureMon l ((s, ⟨0, h0⟩, b1) : ZV d N0 N1) (s', k, b2) α β)
        (bSum (frameM (N1 := N1) x) be) =
      MvPowerSeries.coeff (pureMon l s s' α β) be *
        ∑ ab : Fin N0 × Fin N1, frameM (N1 := N1) x (s, ab.1, ab.2) (s, ⟨0, h0⟩, b1) ^ (l ^ α) *
          frameM (N1 := N1) x (s', ab.1, ab.2) (s', k, b2) ^ (l ^ β) := by
    intro b1 b2
    unfold pureMon
    exact frame_pure_formula Prod.fst (frameM (N1 := N1) x) hM be _ _ _ _ hss'
  have hz : ∀ m : ℕ, (0 : K) ^ (l ^ m) = 0 := fun m => zero_pow (pow_ne_zero _ hl.ne_zero)
  refine ⟨fun hbb' => ?_, fun hyp => ?_⟩
  · rw [hform]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun ab _ => ?_)
    simp only [frameM, true_and]
    by_cases h1 : b = ab.2
    · rw [if_pos h1, if_neg (fun h2 => hbb' (h1.trans h2.symm)), hz, mul_zero]
    · rw [if_neg h1, hz, zero_mul]
  · unfold MonoWtGe
    rw [hform b b]
    have hS : (∑ ab : Fin N0 × Fin N1, frameM (N1 := N1) x (s, ab.1, ab.2) (s, ⟨0, h0⟩, b) ^ (l ^ α) *
          frameM (N1 := N1) x (s', ab.1, ab.2) (s', k, b) ^ (l ^ β)) =
        ∑ a : Fin N0, x (s, ⟨0, h0⟩, a) ^ (l ^ α) * x (s', k, a) ^ (l ^ β) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [frameM, true_and]
      rw [Finset.sum_eq_single b (fun b'' _ hb'' => by rw [if_neg (Ne.symm hb''), hz, zero_mul])
        (fun h => absurd (Finset.mem_univ b) h), if_pos rfl, if_pos rfl]
    rw [hS]
    have hsum1 : ∀ (U : Fin N0 → K), (∀ a, ‖U a‖ ≤ 1) → ‖∑ a, U a‖ ≤ ‖(l : K)‖ → ∀ e : ℕ,
        ‖∑ a, U a ^ (l ^ e)‖ ≤ ‖(l : K)‖ := by
      intro U hU hsU e
      have hfr := frame_frob_norm hl U hU e Finset.univ
      have h1 : ‖(∑ a, U a) ^ (l ^ e)‖ ≤ ‖(l : K)‖ := by
        rw [norm_pow]
        have hle1 : ‖∑ a, U a‖ ≤ 1 :=
          IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun a _ => hU a)
        exact (pow_le_of_le_one (norm_nonneg _) hle1 (pow_ne_zero _ hl.ne_zero)).trans hsU
      have heq : ∑ a, U a ^ (l ^ e) =
          (∑ a, U a) ^ (l ^ e) + -((∑ a, U a) ^ (l ^ e) - ∑ a, U a ^ (l ^ e)) := by ring
      rw [heq]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 ?_)
      rw [norm_neg]; exact hfr
    have hSn : ‖∑ a : Fin N0, x (s, ⟨0, h0⟩, a) ^ (l ^ α) * x (s', k, a) ^ (l ^ β)‖ ≤
        ‖(l : K)‖ := by
      split_ifs at hyp with hba
      · have hU : ∀ a, ‖x (s, ⟨0, h0⟩, a) ^ (l ^ (α - β)) * x (s', k, a)‖ ≤ 1 := fun a => by
          rw [norm_mul, norm_pow]
          exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) (hx _)) (norm_nonneg _) (hx _)
        have h := hsum1 _ hU hyp β
        have hpow : ∀ a, (x (s, ⟨0, h0⟩, a) ^ (l ^ (α - β)) * x (s', k, a)) ^ (l ^ β) =
            x (s, ⟨0, h0⟩, a) ^ (l ^ α) * x (s', k, a) ^ (l ^ β) := fun a => by
          rw [mul_pow, ← pow_mul, ← pow_add, Nat.sub_add_cancel hba]
        simpa only [hpow] using h
      · have hU : ∀ a, ‖x (s, ⟨0, h0⟩, a) * x (s', k, a) ^ (l ^ (β - α))‖ ≤ 1 := fun a => by
          rw [norm_mul, norm_pow]
          exact mul_le_one₀ (hx _) (pow_nonneg (norm_nonneg _) _) (pow_le_one₀ (norm_nonneg _) (hx _))
        have h := hsum1 _ hU hyp α
        have hpow : ∀ a, (x (s, ⟨0, h0⟩, a) * x (s', k, a) ^ (l ^ (β - α))) ^ (l ^ α) =
            x (s, ⟨0, h0⟩, a) ^ (l ^ α) * x (s', k, a) ^ (l ^ β) := fun a => by
          rw [mul_pow, ← pow_mul, ← pow_add, Nat.sub_add_cancel (le_of_lt (not_le.mp hba))]
        simpa only [hpow] using h
    have hc := hbe (pureMon l s s' α β)
    unfold MonoWtGe at hc
    rw [asmR_dot_pureMon] at hc ⊢
    have hπ : 0 < ‖(l : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.ne_zero)
    rw [norm_mul]
    calc ‖MvPowerSeries.coeff (pureMon l s s' α β) be‖ *
          ‖∑ a : Fin N0, x (s, ⟨0, h0⟩, a) ^ (l ^ α) * x (s', k, a) ^ (l ^ β)‖
        ≤ ‖(l : K)‖ ^ (1 / ((l : ℝ) - 1) - 1 - ((l : ℝ) ^ α * rho l + (l : ℝ) ^ β * rho l)) *
            ‖(l : K)‖ :=
          mul_le_mul hc hSn (norm_nonneg _) (Real.rpow_nonneg hπ.le _)
      _ = ‖(l : K)‖ ^ (1 / ((l : ℝ) - 1) - ((l : ℝ) ^ α * rho l + (l : ℝ) ^ β * rho l)) := by
        have he : 1 / ((l : ℝ) - 1) - ((l : ℝ) ^ α * rho l + (l : ℝ) ^ β * rho l) =
            (1 / ((l : ℝ) - 1) - 1 - ((l : ℝ) ^ α * rho l + (l : ℝ) ^ β * rho l)) + 1 := by ring
        rw [he, Real.rpow_add hπ, Real.rpow_one]

end Pure

end Formalism.DworkPowerSeriesWeights
