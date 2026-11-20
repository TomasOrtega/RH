import Mathlib
import GroundTheory.PAdicHodge.WAKummerEps
import GroundTheory.PAdicHodge.FundamentalSeqLog
import GroundTheory.PAdicHodge.FundamentalSeqBCris
import GroundTheory.PAdicHodge.ACrisFrobFixed
set_option maxSynthPendingDepth 1

noncomputable section

open _root_.WittVector IsLocalRing

namespace GroundTheory.PAdicHodge

namespace ACris

section General

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]

local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "𝔭" => Ideal.span {(p : ACris K p)}

/- English proof (translation)
The claim follows from `logJ_eq_of_isAdicSum ((isAdicSum_log hx).congr fun _ => rfl)`.
-/
theorem logJ_eq_log {x : AInf K p} (hx : x ∈ RingHom.ker θ) (hx' : x ∈ pdIdeal K p) :
    logJ hx' = log hx :=
  logJ_eq_of_isAdicSum ((isAdicSum_log hx).congr fun _ => rfl)

/- English proof (translation)
The claim follows from `logJ_eq_log (mu_mem_ker hη) _`.
-/
theorem logTeich_eq_periodT {η : 𝒪♭} (hη : PreTilt.untilt η = 1)
    (hη' : PreTilt.untilt η - 1 ∈ Ideal.span {(p : 𝒪)}) : logTeich hη' = periodT hη :=
  logJ_eq_log (mu_mem_ker hη) _

variable [CharZero K]

/- English proof (translation)
Rewrite using `[Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]`. Conclude with `Ideal.mem_span_singleton_self _`.
-/
theorem span_p_le_comap_theta : 𝔭 ≤ (Ideal.span {(p : 𝒪)}).comap (theta K p) := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
  exact Ideal.mem_span_singleton_self _

/- English proof (translation)
Establish `h` using `congrArg (thetaAway K p) (factorial_mul_dpow n x)`. Rewrite `h` using `[map_mul, map_natCast, map_pow, thetaAway_algebraMap]`. Rewrite using `[eq_div_iff (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)), mul_comm, h]`.
-/
theorem thetaAway_dpow_eq (n : ℕ) (x : AInf K p) :
    thetaAway K p (dpow n x) = ((θ x : 𝒪) : K) ^ n / (n.factorial : K) := by
  have h := congrArg (thetaAway K p) (factorial_mul_dpow n x)
  rw [map_mul, map_natCast, map_pow, thetaAway_algebraMap] at h
  rw [eq_div_iff (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)), mul_comm, h]

/- English proof (translation)
Rewrite using `[logTermJA, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, theta_of, coe_thetaZero, coe_logTermJ, map_mul, map_mul, map_pow, map_neg, map_one, map_natCast, thetaAway_dpow_eq, Nat.factorial_succ, Nat.cast_mul]`. Establish `h1 : ((n.factorial : ℕ) : K) ≠ 0` using `Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)`. Establish `h2 : ((n + 1 : ℕ) : K) ≠ 0` using `Nat.cast_ne_zero.2 n.succ_ne_zero`. Clear the denominators using the available nonvanishing facts.
-/
theorem coe_theta_logTermJA {x : AInf K p} (hx : x ∈ pdIdeal K p) (n : ℕ) :
    ((theta K p (logTermJA hx n) : 𝒪) : K) = (-1) ^ n * ((θ x : 𝒪) : K) ^ (n + 1) / ((n + 1 : ℕ) : K) := by
  rw [logTermJA, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, theta_of,
    coe_thetaZero, coe_logTermJ, map_mul, map_mul, map_pow, map_neg, map_one, map_natCast,
    thetaAway_dpow_eq, Nat.factorial_succ, Nat.cast_mul]
  have h1 : ((n.factorial : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  have h2 : ((n + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 n.succ_ne_zero
  field_simp

/- English proof (translation)
Establish `h1` using `(isAdicSum_logJ hx).map (theta K p) span_p_le_comap_theta`. Establish `h2` using `(isAdicSum_logJ hy).map (theta K p) span_p_le_comap_theta`. Use `h1.unique (h2.congr fun n => Subtype.ext ?_)` and prove the remaining obligations. Rewrite using `[coe_theta_logTermJA, coe_theta_logTermJA, h]`.
-/
theorem theta_logJ_congr {x y : AInf K p} (hx : x ∈ pdIdeal K p) (hy : y ∈ pdIdeal K p)
    (h : θ x = θ y) : theta K p (logJ hx) = theta K p (logJ hy) := by
  have h1 := (isAdicSum_logJ hx).map (theta K p) span_p_le_comap_theta
  have h2 := (isAdicSum_logJ hy).map (theta K p) span_p_le_comap_theta
  refine h1.unique (h2.congr fun n => Subtype.ext ?_)
  rw [coe_theta_logTermJA, coe_theta_logTermJA, h]

/- English proof (translation)
Establish `hs` using `(isAdicSum_logJ hx).map (theta K p) span_p_le_comap_theta`. Rewrite using `[Metric.tendsto_atTop]`. Introduce `r hr`. Take `⟨k, hk⟩` from `exists_pow_lt_of_lt_one hr (IsPerfectoidField.norm_natCast_lt_one (K := K) (p := p))`. Take `⟨N, hN⟩` from `hs k`.

Use `⟨N, fun M hM => ?_⟩` and prove the remaining obligations. Establish `h1` using `hN M hM`. Rewrite `h1` using `[Ideal.span_singleton_pow, Ideal.mem_span_singleton']`. Take `⟨c, hc⟩` from `h1`. Establish `e : ∑ n ∈ Finset.range M, (-1) ^ n * ((θ x : 𝒪) : K) ^ (n + 1) / ((n + 1 : ℕ) : K) = ((∑ n ∈ Finset.range M, theta K p (logTermJA hx n) : 𝒪) : K)`.

Rewrite using `[AddSubmonoidClass.coe_finsetSum]`. Conclude with `Finset.sum_congr rfl fun n _ => (coe_theta_logTermJA hx n).symm`. Rewrite using `[dist_eq_norm, e, ← norm_neg, neg_sub, ← AddSubgroupClass.coe_sub, ← hc, MulMemClass.coe_mul, norm_mul, SubmonoidClass.coe_pow, norm_pow]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `mem_normInteger.1 c.2`.

Conclude with `le_of_eq (by simp)`. Use `_ < r := by rw [one_mul]; exact hk`.
-/
theorem tendsto_theta_logJ {x : AInf K p} (hx : x ∈ pdIdeal K p) :
    Filter.Tendsto (fun N => ∑ n ∈ Finset.range N,
        (-1) ^ n * ((θ x : 𝒪) : K) ^ (n + 1) / ((n + 1 : ℕ) : K))
      Filter.atTop (nhds ((theta K p (logJ hx) : 𝒪) : K)) := by
  have hs := (isAdicSum_logJ hx).map (theta K p) span_p_le_comap_theta
  rw [Metric.tendsto_atTop]
  intro r hr
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hr (IsPerfectoidField.norm_natCast_lt_one (K := K) (p := p))
  obtain ⟨N, hN⟩ := hs k
  refine ⟨N, fun M hM => ?_⟩
  have h1 := hN M hM
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h1
  obtain ⟨c, hc⟩ := h1
  have e : ∑ n ∈ Finset.range M, (-1) ^ n * ((θ x : 𝒪) : K) ^ (n + 1) / ((n + 1 : ℕ) : K) =
      ((∑ n ∈ Finset.range M, theta K p (logTermJA hx n) : 𝒪) : K) := by
    rw [AddSubmonoidClass.coe_finsetSum]
    exact Finset.sum_congr rfl fun n _ => (coe_theta_logTermJA hx n).symm
  rw [dist_eq_norm, e, ← norm_neg, neg_sub, ← AddSubgroupClass.coe_sub, ← hc, MulMemClass.coe_mul,
    norm_mul, SubmonoidClass.coe_pow, norm_pow]
  calc ‖(c : K)‖ * ‖((p : 𝒪) : K)‖ ^ k ≤ 1 * ‖(p : K)‖ ^ k := by
        gcongr
        · exact mem_normInteger.1 c.2
        · exact le_of_eq (by simp)
    _ < r := by rw [one_mul]; exact hk

/- English proof (translation)
Establish `h` using `tendsto_theta_logJ (mu_mem_pdIdeal hx)`. Establish `hθ : ((θ (AInf.mu (K` using `K) x) : 𝒪) : K) = ((PreTilt.untilt x : 𝒪) : K) - 1 := by`. Rewrite using `[AInf.mu, map_sub, fontaineTheta_teichmuller, map_one, AddSubgroupClass.coe_sub, OneMemClass.coe_one]`. Simplify using `only [hθ] at h`. Conclude with `h`.
-/
theorem tendsto_theta_logTeich {x : 𝒪♭} (hx : PreTilt.untilt x - 1 ∈ Ideal.span {(p : 𝒪)}) :
    Filter.Tendsto (fun N => ∑ n ∈ Finset.range N,
        (-1) ^ n * (((PreTilt.untilt x : 𝒪) : K) - 1) ^ (n + 1) / ((n + 1 : ℕ) : K))
      Filter.atTop (nhds ((theta K p (logTeich hx) : 𝒪) : K)) := by
  have h := tendsto_theta_logJ (mu_mem_pdIdeal hx)
  have hθ : ((θ (AInf.mu (K := K) x) : 𝒪) : K) = ((PreTilt.untilt x : 𝒪) : K) - 1 := by
    rw [AInf.mu, map_sub, fontaineTheta_teichmuller, map_one, AddSubgroupClass.coe_sub,
      OneMemClass.coe_one]
  simp only [hθ] at h
  exact h

/- English proof (translation)
Establish `hS : Ideal.Quotient.mk (kerAway K p ^ 2) (∑ k ∈ Finset.range n, dpow k x * dpow (n + 1 - k) δ) = 0`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_eq_zero fun k hk => by`. Rewrite using `[map_mul, mk_dpow_eq_zero hδ (by have := Finset.mem_range.1 hk; omega), mul_zero]`. Rewrite using `[← map_sub, coe_logTermJ, coe_logTermJ, dpow_add, Finset.sum_range_succ, Finset.sum_range_succ, Nat.add_sub_cancel_left, Nat.sub_self, dpow_zero, dpow_one]`.

Establish `e : (-1) ^ n * (n.factorial : 𝔸) * (∑ k ∈ Finset.range n, dpow k x * dpow (n + 1 - k) δ + dpow n x * algebraMap (AInf K p) 𝔸 δ + dpow (n + 1) x * 1) - (-1) ^ n * (n.factorial : 𝔸) * dpow (n + 1) x = (-1) ^ n * (n.factorial : 𝔸) * ∑ k ∈ Finset.range n, dpow k x * dpow (n + 1 - k) …`. Rewrite using `[map_mul, map_pow, map_neg, neg_pow (algebraMap (AInf K p) 𝔸 x), ← factorial_mul_dpow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, map_add, map_mul, hS, mul_zero, zero_add]`.
-/
theorem mk_logTermJ_add_sub {x δ : AInf K p} (hx : x ∈ pdIdeal K p) (hδ : δ ∈ RingHom.ker θ)
    (hz : x + δ ∈ pdIdeal K p) (n : ℕ) :
    Ideal.Quotient.mk (kerAway K p ^ 2) (logTermJ hz n : 𝔸) -
        Ideal.Quotient.mk (kerAway K p ^ 2) (logTermJ hx n : 𝔸) =
      Ideal.Quotient.mk (kerAway K p ^ 2) (algebraMap (AInf K p) 𝔸 ((-x) ^ n * δ)) := by
  have hS : Ideal.Quotient.mk (kerAway K p ^ 2)
      (∑ k ∈ Finset.range n, dpow k x * dpow (n + 1 - k) δ) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero fun k hk => by
      rw [map_mul, mk_dpow_eq_zero hδ (by have := Finset.mem_range.1 hk; omega), mul_zero]
  rw [← map_sub, coe_logTermJ, coe_logTermJ, dpow_add, Finset.sum_range_succ, Finset.sum_range_succ,
    Nat.add_sub_cancel_left, Nat.sub_self, dpow_zero, dpow_one]
  have e : (-1) ^ n * (n.factorial : 𝔸) * (∑ k ∈ Finset.range n, dpow k x * dpow (n + 1 - k) δ +
      dpow n x * algebraMap (AInf K p) 𝔸 δ + dpow (n + 1) x * 1) -
      (-1) ^ n * (n.factorial : 𝔸) * dpow (n + 1) x =
      (-1) ^ n * (n.factorial : 𝔸) * ∑ k ∈ Finset.range n, dpow k x * dpow (n + 1 - k) δ +
        algebraMap (AInf K p) 𝔸 ((-x) ^ n * δ) := by
    rw [map_mul, map_pow, map_neg, neg_pow (algebraMap (AInf K p) 𝔸 x), ← factorial_mul_dpow]
    ring
  rw [e, map_add, map_mul, hS, mul_zero, zero_add]

/- English proof (translation)
Establish `hδ : (1 + x) * k ∈ RingHom.ker θ` using `Ideal.mul_mem_left _ _ hk`. Rewrite using `[Finset.sum_congr rfl fun n _ => mk_logTermJ_add_sub hx hδ hz n, ← map_sum, ← map_sum]`. Use `congr 2`. Establish `h` using `mul_neg_geom_sum (-x) N`. Rewrite using `[← Finset.sum_mul]`.

Take the linear combination `k * h`.
-/
theorem mk_sum_logTermJ_mul_sub {x k : AInf K p} (hx : x ∈ pdIdeal K p) (hk : k ∈ RingHom.ker θ)
    (hz : x + (1 + x) * k ∈ pdIdeal K p) (N : ℕ) :
    ∑ n ∈ Finset.range N, (Ideal.Quotient.mk (kerAway K p ^ 2) (logTermJ hz n : 𝔸) -
        Ideal.Quotient.mk (kerAway K p ^ 2) (logTermJ hx n : 𝔸)) =
      Ideal.Quotient.mk (kerAway K p ^ 2) (algebraMap (AInf K p) 𝔸 (k - k * (-x) ^ N)) := by
  have hδ : (1 + x) * k ∈ RingHom.ker θ := Ideal.mul_mem_left _ _ hk
  rw [Finset.sum_congr rfl fun n _ => mk_logTermJ_add_sub hx hδ hz n, ← map_sum, ← map_sum]
  congr 2
  have h := mul_neg_geom_sum (-x) N
  rw [← Finset.sum_mul]
  linear_combination k * h

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Establish `hle : 𝔭 ≤ (Ideal.span {(p : acrisQ K p 2)}).comap (embedding₂ K p 2)`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]`. Conclude with `Ideal.mem_span_singleton_self _`. Establish `hterm : ∀ {w : AInf K p} (hw : w ∈ pdIdeal K p) (n : ℕ), ((embedding₂ K p 2 (logTermJA hw n) : acrisQ K p 2) : 𝔸 ⧸ kerAway K p ^ 2) = Ideal.Quotient.mk (kerAway K p ^ 2) (logTermJ hw n : 𝔸)` using `fun hw n => by`. Rewrite using `[logTermJA, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, iotaM_of, coe_iotaZero]`.

Establish `hs` using `((isAdicSum_logJ hz).map (embedding₂ K p 2) hle).sub ((isAdicSum_logJ hx).map (embedding₂ K p 2) hle)`. Establish `hkA : algebraMap (AInf K p) 𝔸 k ∈ ACrisZero K p` using `Subalgebra.algebraMap_mem _ k`. Use `set tk : acrisQ K p 2 := ⟨Ideal.Quotient.mk _ (algebraMap (AInf K p) 𝔸 k), mk_mem_acrisQ 2 hkA⟩ with htk`. Establish `hs' : IsAdicSum (Ideal.span {(p : acrisQ K p 2)}) (fun n => embedding₂ K p 2 (logTermJA hz n) - embedding₂ K p 2 (logTermJA hx n)) tk`. Introduce `j`.

Use `⟨p * j, fun M hM => ?_⟩` and prove the remaining obligations. Use `set w : ACrisZero K p := algebraMap (AInf K p) (ACrisZero K p) k * (-1) ^ M * (M.factorial : ACrisZero K p) * dpowJ hx M with hw`. Establish `hwmem : w ∈ Ideal.span {(p : ACrisZero K p)} ^ j` using `Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (natCast_mem_pow (pow_dvd_factorial hM)))`. Establish `hmem : iotaZero K p 2 w ∈ Ideal.span {(p : acrisQ K p 2)} ^ j` using `(Ideal.le_comap_pow _ j) (Ideal.pow_right_mono (span_p_le_comap_iotaZero 2) j hwmem)`. Use `hmem using 1` and compare the differences between its conclusion and the goal.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[AddSubgroupClass.coe_sub, AddSubmonoidClass.coe_finsetSum]`. Simplify using `only [AddSubgroupClass.coe_sub, hterm]`. Rewrite using `[mk_sum_logTermJ_mul_sub hx hk hz M, coe_iotaZero, htk, ← map_sub]`. Use `congr 1`.

Rewrite using `[hw, Subalgebra.coe_mul, Subalgebra.coe_mul, Subalgebra.coe_mul, coe_dpowJ]`. Simplify using `only [Subalgebra.coe_algebraMap, Subalgebra.coe_pow, Subalgebra.coe_neg, Subalgebra.coe_one, SubringClass.coe_natCast]`. Rewrite using `[map_sub, map_mul, map_pow, map_neg, neg_pow (algebraMap (AInf K p) 𝔸 x), ← factorial_mul_dpow]`. Expand and normalize the polynomial expressions, which then agree. Establish `h` using `hs.unique hs'`.

Rewrite using `[iotaQ, RingHom.comp_apply, RingHom.comp_apply, ← map_sub, h]`. Both sides reduce to the same expression.
-/
theorem iotaQ_logJ_mul_sub {x k : AInf K p} (hx : x ∈ pdIdeal K p) (hk : k ∈ RingHom.ker θ)
    (hz : x + (1 + x) * k ∈ pdIdeal K p) :
    iotaQ K p 2 (logJ hz) - iotaQ K p 2 (logJ hx) =
      Ideal.Quotient.mk (kerAway K p ^ 2) (algebraMap (AInf K p) 𝔸 k) := by
  have hle : 𝔭 ≤ (Ideal.span {(p : acrisQ K p 2)}).comap (embedding₂ K p 2) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
    exact Ideal.mem_span_singleton_self _
  have hterm : ∀ {w : AInf K p} (hw : w ∈ pdIdeal K p) (n : ℕ),
      ((embedding₂ K p 2 (logTermJA hw n) : acrisQ K p 2) : 𝔸 ⧸ kerAway K p ^ 2) =
        Ideal.Quotient.mk (kerAway K p ^ 2) (logTermJ hw n : 𝔸) := fun hw n => by
    rw [logTermJA, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      iotaM_of, coe_iotaZero]
  have hs := ((isAdicSum_logJ hz).map (embedding₂ K p 2) hle).sub ((isAdicSum_logJ hx).map (embedding₂ K p 2) hle)
  have hkA : algebraMap (AInf K p) 𝔸 k ∈ ACrisZero K p := Subalgebra.algebraMap_mem _ k
  set tk : acrisQ K p 2 := ⟨Ideal.Quotient.mk _ (algebraMap (AInf K p) 𝔸 k), mk_mem_acrisQ 2 hkA⟩ with htk
  have hs' : IsAdicSum (Ideal.span {(p : acrisQ K p 2)})
      (fun n => embedding₂ K p 2 (logTermJA hz n) - embedding₂ K p 2 (logTermJA hx n)) tk := by
    intro j
    refine ⟨p * j, fun M hM => ?_⟩
    set w : ACrisZero K p := algebraMap (AInf K p) (ACrisZero K p) k * (-1) ^ M *
      (M.factorial : ACrisZero K p) * dpowJ hx M with hw
    have hwmem : w ∈ Ideal.span {(p : ACrisZero K p)} ^ j :=
      Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (natCast_mem_pow (pow_dvd_factorial hM)))
    have hmem : iotaZero K p 2 w ∈ Ideal.span {(p : acrisQ K p 2)} ^ j :=
      (Ideal.le_comap_pow _ j) (Ideal.pow_right_mono (span_p_le_comap_iotaZero 2) j hwmem)
    convert hmem using 1
    apply Subtype.ext
    rw [AddSubgroupClass.coe_sub, AddSubmonoidClass.coe_finsetSum]
    simp only [AddSubgroupClass.coe_sub, hterm]
    rw [mk_sum_logTermJ_mul_sub hx hk hz M, coe_iotaZero, htk, ← map_sub]
    congr 1
    rw [hw, Subalgebra.coe_mul, Subalgebra.coe_mul, Subalgebra.coe_mul, coe_dpowJ]
    simp only [Subalgebra.coe_algebraMap, Subalgebra.coe_pow, Subalgebra.coe_neg,
      Subalgebra.coe_one, SubringClass.coe_natCast]
    rw [map_sub, map_mul, map_pow, map_neg, neg_pow (algebraMap (AInf K p) 𝔸 x), ← factorial_mul_dpow]
    ring
  have h := hs.unique hs'
  rw [iotaQ, RingHom.comp_apply, RingHom.comp_apply, ← map_sub, h]
  rfl

/- English proof (translation)
Rewrite using `[iotaQ_log, Finset.sum_range_succ, Finset.sum_range_one, logTermZero, logTermZero]`. Simplify using `only [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_neg, Subalgebra.coe_one, SubringClass.coe_natCast, coe_dpowZero]`. Rewrite using `[map_add, map_mul (Ideal.Quotient.mk (kerAway K p ^ 2)) _ (dpow (1 + 1) k), mk_dpow_eq_zero hk (show 2 ≤ 1 + 1 from le_refl _), mul_zero, add_zero, zero_add, dpow_one]`. Simplify using the standard rewrite rules.
-/
theorem iotaQ_two_log {k : AInf K p} (hk : k ∈ RingHom.ker θ) :
    iotaQ K p 2 (log hk) = Ideal.Quotient.mk (kerAway K p ^ 2) (algebraMap (AInf K p) 𝔸 k) := by
  rw [iotaQ_log, Finset.sum_range_succ, Finset.sum_range_one, logTermZero, logTermZero]
  simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_neg, Subalgebra.coe_one,
    SubringClass.coe_natCast, coe_dpowZero]
  rw [map_add, map_mul (Ideal.Quotient.mk (kerAway K p ^ 2)) _ (dpow (1 + 1) k),
    mk_dpow_eq_zero hk (show 2 ≤ 1 + 1 from le_refl _), mul_zero, add_zero, zero_add, dpow_one]
  simp

end General

section Cp

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝒪" => normInteger ℂ_[p]
local notation "𝒪♭" => PreTilt (normInteger ℂ_[p]) p
local notation "θ" => fontaineTheta (normInteger ℂ_[p]) p
local notation "𝔸" => Localization.Away (p : AInf ℂ_[p] p)
local notation "𝔭" => Ideal.span {(p : ACris ℂ_[p] p)}

section Galois

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

/- English proof (translation)
Rewrite using `[Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, galCris_natCast_p]`. Conclude with `Ideal.mem_span_singleton_self _`.
-/
theorem span_p_le_comap_galCris (σ : Gal(PadicAlgCl p/K)) : 𝔭 ≤ Ideal.comap (galCris σ) 𝔭 := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, galCris_natCast_p]
  exact Ideal.mem_span_singleton_self _

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Rewrite using `[gal_smul_def]`. Use `(logJ_eq_of_isAdicSum (((isAdicSum_logJ hx).map (galCris σ) (span_p_le_comap_galCris σ)).congr fun n => ?_)).symm` and prove the remaining obligations. Rewrite using `[logTermJA, logTermJA, AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, RingHom.id_apply, galCris_of]`. Use `congrArg (AdicCompletion.of _ _) (Subtype.ext ?_)` and prove the remaining obligations. Rewrite using `[gal_smul_zero_def, coe_galZero, coe_logTermJ, coe_logTermJ, map_mul, map_mul, map_pow, map_neg, map_one, map_natCast, galAway_dpow]`.
-/
theorem gal_smul_logJ (σ : Gal(PadicAlgCl p/K)) {x : AInf ℂ_[p] p} (hx : x ∈ pdIdeal ℂ_[p] p)
    (hσx : σ • x ∈ pdIdeal ℂ_[p] p) : σ • logJ hx = logJ hσx := by
  rw [gal_smul_def]
  refine (logJ_eq_of_isAdicSum (((isAdicSum_logJ hx).map (galCris σ) (span_p_le_comap_galCris σ)).congr
    fun n => ?_)).symm
  rw [logTermJA, logTermJA, AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply, RingHom.id_apply, galCris_of]
  refine congrArg (AdicCompletion.of _ _) (Subtype.ext ?_)
  rw [gal_smul_zero_def, coe_galZero, coe_logTermJ, coe_logTermJ, map_mul, map_mul, map_pow, map_neg,
    map_one, map_natCast, galAway_dpow]

/- English proof (translation)
Rewrite using `[AInf.mu, AInf.mu, smul_sub, smul_one, AInf.gal_smul_teichmuller]`.
-/
theorem gal_smul_mu (σ : Gal(PadicAlgCl p/K)) (x : 𝒪♭) :
    σ • AInf.mu (K := ℂ_[p]) x = AInf.mu (tiltGal σ x) := by
  rw [AInf.mu, AInf.mu, smul_sub, smul_one, AInf.gal_smul_teichmuller]

/- English proof (translation)
Rewrite `hx`, the goal using `[mem_span_singleton_iff_norm_le]`. Rewrite using `[AddSubgroupClass.coe_sub, OneMemClass.coe_one, AInf.coe_untilt_gal]`. Establish `e : σ • ((PreTilt.untilt x : 𝒪) : ℂ_[p]) - 1 = σ • (((PreTilt.untilt x : 𝒪) : ℂ_[p]) - 1)`. Rewrite using `[smul_sub, smul_one]`. Rewrite using `[e, ← galCp_apply, norm_galCp]`.

Simplify using `using hx`.
-/
theorem untilt_tiltGal_sub_one_mem (σ : Gal(PadicAlgCl p/K)) {x : 𝒪♭}
    (hx : PreTilt.untilt x - 1 ∈ Ideal.span {(p : 𝒪)}) :
    PreTilt.untilt (tiltGal σ x) - 1 ∈ Ideal.span {(p : 𝒪)} := by
  rw [mem_span_singleton_iff_norm_le] at hx ⊢
  rw [AddSubgroupClass.coe_sub, OneMemClass.coe_one, AInf.coe_untilt_gal]
  have e : σ • ((PreTilt.untilt x : 𝒪) : ℂ_[p]) - 1 = σ • (((PreTilt.untilt x : 𝒪) : ℂ_[p]) - 1) := by
    rw [smul_sub, smul_one]
  rw [e, ← galCp_apply, norm_galCp]
  simpa using hx

/- English proof (translation)
Establish `h` using `mu_mem_pdIdeal (K := ℂ_[p]) (untilt_tiltGal_sub_one_mem σ hx)`. Rewrite using `[logTeich, logTeich, gal_smul_logJ σ (mu_mem_pdIdeal hx) (by rw [gal_smul_mu]; exact h)]`. Conclude with `logJ_congr (gal_smul_mu σ x) _ _`.
-/
theorem gal_smul_logTeich (σ : Gal(PadicAlgCl p/K)) {x : 𝒪♭}
    (hx : PreTilt.untilt x - 1 ∈ Ideal.span {(p : 𝒪)}) :
    σ • logTeich hx = logTeich (untilt_tiltGal_sub_one_mem σ hx) := by
  have h := mu_mem_pdIdeal (K := ℂ_[p]) (untilt_tiltGal_sub_one_mem σ hx)
  rw [logTeich, logTeich, gal_smul_logJ σ (mu_mem_pdIdeal hx) (by rw [gal_smul_mu]; exact h)]
  exact logJ_congr (gal_smul_mu σ x) _ _

end Galois

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem logTeich_congr {x y : 𝒪♭} (h : x = y) (hx : PreTilt.untilt x - 1 ∈ Ideal.span {(p : 𝒪)})
    (hy : PreTilt.untilt y - 1 ∈ Ideal.span {(p : 𝒪)}) : logTeich (K := ℂ_[p]) hx = logTeich hy := by
  subst h; rfl

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Use `set y := algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) D with hy`. Establish `hφy : phiPlus ℂ_[p] p y = (p : BCrisPlus ℂ_[p] p) ^ 1 * y`. Rewrite using `[hy, phiPlus_algebraMap, hφ, pow_one, map_mul, map_natCast]`. Establish `hιy : iotaPlus ℂ_[p] p y ∈ Ideal.span {fontaineT (epsilon p) (untilt_epsilon) ^ 1}`. Rewrite using `[hy, iotaPlus_algebraMap, pow_one, ← maximalIdeal_eq_span_fontaineT untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one, IsPerfectoidField.maximalIdeal_bDeRhamPlus, RingHom.mem_ker, thetaField_iota, hθ]`.

Both sides reduce to the same expression. Take `⟨q, hq⟩` from `exists_eq_algebraMap_mul_pow_of_phiPlus_eq untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one 1 hφy hιy`. Use `⟨q, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (iotaPlus ℂ_[p] p) hq`. Rewrite `h` using `[hy, iotaPlus_algebraMap, pow_one, map_mul, iotaPlus_algebraMap_padic]`.

Rewrite using `[h, periodTPlus, iotaPlus_algebraMap, iota_periodT]`.
-/
theorem exists_iota_eq_mul_fontaineT {D : ACris ℂ_[p] p} (hφ : phi ℂ_[p] p D = (p : ACris ℂ_[p] p) * D)
    (hθ : theta ℂ_[p] p D = 0) :
    ∃ q : ℚ_[p], iota ℂ_[p] p D =
      algebraMap ℚ_[p] (BDeRhamPlus (normInteger ℂ_[p]) p) q * fontaineT (epsilon p) (untilt_epsilon) := by
  set y := algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) D with hy
  have hφy : phiPlus ℂ_[p] p y = (p : BCrisPlus ℂ_[p] p) ^ 1 * y := by
    rw [hy, phiPlus_algebraMap, hφ, pow_one, map_mul, map_natCast]
  have hιy : iotaPlus ℂ_[p] p y ∈ Ideal.span {fontaineT (epsilon p) (untilt_epsilon) ^ 1} := by
    rw [hy, iotaPlus_algebraMap, pow_one, ← maximalIdeal_eq_span_fontaineT untilt_epsilon
      untilt_frobeniusEquiv_symm_epsilon_ne_one, IsPerfectoidField.maximalIdeal_bDeRhamPlus,
      RingHom.mem_ker, thetaField_iota, hθ]
    rfl
  obtain ⟨q, hq⟩ := exists_eq_algebraMap_mul_pow_of_phiPlus_eq untilt_epsilon
    untilt_frobeniusEquiv_symm_epsilon_ne_one 1 hφy hιy
  refine ⟨q, ?_⟩
  have h := congrArg (iotaPlus ℂ_[p] p) hq
  rw [hy, iotaPlus_algebraMap, pow_one, map_mul, iotaPlus_algebraMap_padic] at h
  rw [h, periodTPlus, iotaPlus_algebraMap, iota_periodT]

omit hp in

/- English proof (translation)
Introduce `h`. Rewrite `h` using `[ht, Ideal.span_singleton_pow, Ideal.mem_span_singleton']`. Take `⟨c, hc⟩` from `h`. Establish `h1 : t * (c * t) = t * 1`. Rewrite using `[mul_one]`.

Combine the equalities or inequalities in the displayed calculation. Establish `h2` using `mul_left_cancel₀ ht0 h1`. Establish `htm : t ∈ maximalIdeal R` using `by rw [ht]; exact Ideal.mem_span_singleton_self t`. Conclude with `(IsLocalRing.mem_maximalIdeal t).1 htm ⟨⟨t, c, by rw [mul_comm]; exact h2, h2⟩, rfl⟩`.
-/
theorem not_mem_maximalIdeal_sq_of_span_eq {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    {t : R} (ht : maximalIdeal R = Ideal.span {t}) (ht0 : t ≠ 0) : t ∉ maximalIdeal R ^ 2 := by
  intro h
  rw [ht, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h
  obtain ⟨c, hc⟩ := h
  have h1 : t * (c * t) = t * 1 := by
    rw [mul_one]
    calc t * (c * t) = c * t ^ 2 := by ring
      _ = t := hc
  have h2 := mul_left_cancel₀ ht0 h1
  have htm : t ∈ maximalIdeal R := by rw [ht]; exact Ideal.mem_span_singleton_self t
  exact (IsLocalRing.mem_maximalIdeal t).1 htm ⟨⟨t, c, by rw [mul_comm]; exact h2, h2⟩, rfl⟩

set_option maxHeartbeats 3200000 in

/- English proof (translation)
Use `set D := logTeich (K := ℂ_[p]) hxη - logTeich hx - periodT hη with hD`. Establish `hmu : AInf.mu (K` using `ℂ_[p]) (x * η) = AInf.mu x + (1 + AInf.mu x) * AInf.mu η := by`. Rewrite using `[AInf.mu, AInf.mu, AInf.mu, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hz : AInf.mu (K` using `ℂ_[p]) x + (1 + AInf.mu x) * AInf.mu η ∈ pdIdeal ℂ_[p] p := hmu ▸ mu_mem_pdIdeal hxη`.

Establish `h2 : iotaQ ℂ_[p] p 2 D = 0`. Establish `h` using `iotaQ_logJ_mul_sub (mu_mem_pdIdeal hx) (mu_mem_ker hη) hz`. Rewrite using `[hD, map_sub, map_sub, logTeich, logJ_congr hmu _ hz, logTeich, h, periodT, iotaQ_two_log, sub_self]`. Establish `hφ : phi ℂ_[p] p D = (p : ACris ℂ_[p] p) * D`. Rewrite using `[hD, map_sub, map_sub, phi_logTeich, phi_logTeich, phi_periodT_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hθ : theta ℂ_[p] p D = 0`. Establish `hθμ : fontaineTheta (normInteger ℂ_[p]) p (AInf.mu (x * η)) = fontaineTheta (normInteger ℂ_[p]) p (AInf.mu x)`. Rewrite using `[AInf.mu, AInf.mu, map_sub, map_sub, fontaineTheta_teichmuller, fontaineTheta_teichmuller, map_mul, hη, mul_one]`. Rewrite using `[hD, map_sub, map_sub, logTeich, logTeich, theta_logJ_congr (mu_mem_pdIdeal hxη) (mu_mem_pdIdeal hx) hθμ, theta_periodT, sub_self, sub_zero]`.

Take `⟨q, hq⟩` from `exists_iota_eq_mul_fontaineT hφ hθ`. Establish `hm2 : iota ℂ_[p] p D ∈ maximalIdeal (BDeRhamPlus (normInteger ℂ_[p]) p) ^ 2`. Rewrite using `[← IsPerfectoidField.ker_evalB, RingHom.mem_ker]`. Conclude with `(evalₐ_iota 2 D).trans h2`. Establish `hq0 : q = 0`.

Assume the negation of the conclusion as `hq0`. Establish `hu : IsUnit (algebraMap ℚ_[p] (BDeRhamPlus (normInteger ℂ_[p]) p) q)` using `(isUnit_iff_ne_zero.2 hq0).map _`. Rewrite `hm2` using `[hq, Ideal.unit_mul_mem_iff_mem _ hu]`. Conclude with `not_mem_maximalIdeal_sq_of_span_eq (maximalIdeal_eq_span_fontaineT untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one) (fontaineT_ne_zero untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one) hm2`. Establish `hD0 : D = 0` using `iota_injective (by rw [hq, hq0, map_zero, zero_mul, map_zero])`.

Rewrite `hD0` using `[hD]`. Take the linear combination `hD0`.
-/
theorem logTeich_mul_eq_add {x η : 𝒪♭} (hx : PreTilt.untilt x - 1 ∈ Ideal.span {(p : 𝒪)})
    (hη : PreTilt.untilt η = 1) (hxη : PreTilt.untilt (x * η) - 1 ∈ Ideal.span {(p : 𝒪)}) :
    logTeich (K := ℂ_[p]) hxη = logTeich hx + periodT hη := by
  set D := logTeich (K := ℂ_[p]) hxη - logTeich hx - periodT hη with hD
  have hmu : AInf.mu (K := ℂ_[p]) (x * η) = AInf.mu x + (1 + AInf.mu x) * AInf.mu η := by
    rw [AInf.mu, AInf.mu, AInf.mu, map_mul]; ring
  have hz : AInf.mu (K := ℂ_[p]) x + (1 + AInf.mu x) * AInf.mu η ∈ pdIdeal ℂ_[p] p :=
    hmu ▸ mu_mem_pdIdeal hxη

  have h2 : iotaQ ℂ_[p] p 2 D = 0 := by
    have h := iotaQ_logJ_mul_sub (mu_mem_pdIdeal hx) (mu_mem_ker hη) hz
    rw [hD, map_sub, map_sub, logTeich, logJ_congr hmu _ hz, logTeich, h, periodT, iotaQ_two_log,
      sub_self]

  have hφ : phi ℂ_[p] p D = (p : ACris ℂ_[p] p) * D := by
    rw [hD, map_sub, map_sub, phi_logTeich, phi_logTeich, phi_periodT_eq_mul]; ring
  have hθ : theta ℂ_[p] p D = 0 := by
    have hθμ : fontaineTheta (normInteger ℂ_[p]) p (AInf.mu (x * η)) =
        fontaineTheta (normInteger ℂ_[p]) p (AInf.mu x) := by
      rw [AInf.mu, AInf.mu, map_sub, map_sub, fontaineTheta_teichmuller, fontaineTheta_teichmuller,
        map_mul, hη, mul_one]
    rw [hD, map_sub, map_sub, logTeich, logTeich, theta_logJ_congr (mu_mem_pdIdeal hxη)
      (mu_mem_pdIdeal hx) hθμ, theta_periodT, sub_self, sub_zero]
  obtain ⟨q, hq⟩ := exists_iota_eq_mul_fontaineT hφ hθ

  have hm2 : iota ℂ_[p] p D ∈ maximalIdeal (BDeRhamPlus (normInteger ℂ_[p]) p) ^ 2 := by
    rw [← IsPerfectoidField.ker_evalB, RingHom.mem_ker]
    exact (evalₐ_iota 2 D).trans h2
  have hq0 : q = 0 := by
    by_contra hq0
    have hu : IsUnit (algebraMap ℚ_[p] (BDeRhamPlus (normInteger ℂ_[p]) p) q) :=
      (isUnit_iff_ne_zero.2 hq0).map _
    rw [hq, Ideal.unit_mul_mem_iff_mem _ hu] at hm2
    exact not_mem_maximalIdeal_sq_of_span_eq (maximalIdeal_eq_span_fontaineT untilt_epsilon
      untilt_frobeniusEquiv_symm_epsilon_ne_one)
      (fontaineT_ne_zero untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one) hm2
  have hD0 : D = 0 := iota_injective (by rw [hq, hq0, map_zero, zero_mul, map_zero])
  rw [hD] at hD0
  linear_combination hD0

/- English proof (translation)
Apply `iota_injective` to reduce the goal to its premises. Rewrite using `[iota_periodT, map_mul, iota_padicInt, iota_periodT, fontaineT_epsPow]`.
-/
theorem periodT_epsPow {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (a : ℤ_[p]) :
    periodT (untilt_epsPow hε a) = algebraMap (AInf ℂ_[p] p) (ACris ℂ_[p] p)
      (IsPerfectoidField.padicIntToWitt p a) * periodT hε := by
  apply iota_injective
  rw [iota_periodT, map_mul, iota_padicInt, iota_periodT, fontaineT_epsPow]

/- English proof (translation)
Establish `e` using `tiltGal_eq_mul_epsPow hε hζ hx0 hfix σ`. Establish `h1 : PreTilt.untilt (x * epsPow hε (kummerCocycle hε hζ hx0 hfix σ)) - 1 ∈ Ideal.span {(p : 𝒪)}` using `e ▸ untilt_tiltGal_sub_one_mem σ hx`. Rewrite using `[gal_smul_logTeich, logTeich_congr e _ h1, logTeich_mul_eq_add hx (untilt_epsPow hε _) h1, periodT_epsPow]`.
-/
theorem gal_smul_logTeich_eq {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {ε : 𝒪♭}
    (hε : PreTilt.untilt ε = 1) (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1)
    {x : 𝒪♭} (hx0 : x ≠ 0)
    (hfix : ∀ σ : Gal(PadicAlgCl p/K),
      σ • ((PreTilt.untilt x : 𝒪) : ℂ_[p]) = ((PreTilt.untilt x : 𝒪) : ℂ_[p]))
    (hx : PreTilt.untilt x - 1 ∈ Ideal.span {(p : 𝒪)}) (σ : Gal(PadicAlgCl p/K)) :
    σ • logTeich hx = logTeich hx + algebraMap (AInf ℂ_[p] p) (ACris ℂ_[p] p)
      (IsPerfectoidField.padicIntToWitt p (kummerCocycle hε hζ hx0 hfix σ)) * periodT hε := by
  have e := tiltGal_eq_mul_epsPow hε hζ hx0 hfix σ
  have h1 : PreTilt.untilt (x * epsPow hε (kummerCocycle hε hζ hx0 hfix σ)) - 1 ∈
      Ideal.span {(p : 𝒪)} := e ▸ untilt_tiltGal_sub_one_mem σ hx
  rw [gal_smul_logTeich, logTeich_congr e _ h1, logTeich_mul_eq_add hx (untilt_epsPow hε _) h1,
    periodT_epsPow]

end Cp

end ACris

end GroundTheory.PAdicHodge
