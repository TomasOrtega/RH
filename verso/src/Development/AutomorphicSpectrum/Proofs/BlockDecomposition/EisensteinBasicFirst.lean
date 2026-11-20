import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

namespace GlobalTheory.CompanionTheory.RSEuler

open Nat Finset

noncomputable def mulExt (h : ℕ → ℕ → ℂ) (m : ℕ) : ℂ := if m = 0 then 0 else m.factorization.prod h

/- English proof (translation)
Simplify using `[mulExt]`.
-/
theorem mulExt_zero (h : ℕ → ℕ → ℂ) : mulExt h 0 = 0 := by simp [mulExt]

/- English proof (translation)
Simplify using `[mulExt]`.
-/
theorem mulExt_one (h : ℕ → ℕ → ℂ) : mulExt h 1 = 1 := by simp [mulExt]

/- English proof (translation)
Break down `eq_or_ne m 0 with rfl | hm` into its components or cases. Simplify using `[mulExt]`. Break down `eq_or_ne n 0 with rfl | hn` into its components or cases. Simplify using `[mulExt]`. Rewrite using `[mulExt, mulExt, mulExt, if_neg (mul_ne_zero hm hn), if_neg hm, if_neg hn, Nat.factorization_mul_of_coprime hmn]`.

Conclude with `Finsupp.prod_add_index_of_disjoint (by simpa [Nat.support_factorization] using hmn.disjoint_primeFactors) h`.
-/
theorem mulExt_mul (h : ℕ → ℕ → ℂ) {m n : ℕ} (hmn : Nat.Coprime m n) :
    mulExt h (m * n) = mulExt h m * mulExt h n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [mulExt]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [mulExt]
  rw [mulExt, mulExt, mulExt, if_neg (mul_ne_zero hm hn), if_neg hm, if_neg hn,
    Nat.factorization_mul_of_coprime hmn]
  exact Finsupp.prod_add_index_of_disjoint
    (by simpa [Nat.support_factorization] using hmn.disjoint_primeFactors) h

/- English proof (translation)
Rewrite using `[mulExt, if_neg (pow_ne_zero _ hp.ne_zero), hp.factorization_pow, Finsupp.prod_single_index (h0 p)]`.
-/
theorem mulExt_prime_pow (h : ℕ → ℕ → ℂ) (h0 : ∀ p, h p 0 = 1) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    mulExt h (p ^ e) = h p e := by
  rw [mulExt, if_neg (pow_ne_zero _ hp.ne_zero), hp.factorization_pow,
    Finsupp.prod_single_index (h0 p)]

noncomputable def cst : ℝ := ∑' n : ℕ, ((n : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ n

/- English proof (translation)
Establish `h` using `summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 (r := 1 / 2) (by norm_num)`. Establish `h2` using `((summable_nat_add_iff 2).2 h).mul_left 4`. Use `h2.congr fun n => ?_` and prove the remaining obligations. Use `push_cast`. Rewrite using `[pow_add]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem summable_cst : Summable fun n : ℕ => ((n : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ n := by
  have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 (r := 1 / 2) (by norm_num)
  have h2 := ((summable_nat_add_iff 2).2 h).mul_left 4
  refine h2.congr fun n => ?_
  push_cast
  rw [pow_add]
  ring

/- English proof (translation)
Establish `hle : ∀ n, g (n + 1) ≤ x * (((n : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ n)` using `fun n => by`. Use `(hb (n + 1)).trans ?_` and prove the remaining obligations. Establish `: x ^ n ≤ (1 / 2 : ℝ) ^ n` using `pow_le_pow_left₀ hx0 hx n`. Use `push_cast`. Combine the equalities or inequalities in the displayed calculation.

Establish `hs1 : Summable fun n => g (n + 1)` using `Summable.of_nonneg_of_le (fun n => hg _) hle (summable_cst.mul_left x)`. Establish `hs : Summable g` using `(summable_nat_add_iff 1).1 hs1`. Use `⟨hs, ?_⟩` and prove the remaining obligations. Rewrite using `[hs.tsum_eq_zero_add]`. Use `hs1.tsum_le_tsum hle (summable_cst.mul_left x)` as an intermediate fact.

Rewrite `this` using `[tsum_mul_left]`. Establish `e : x * ∑' n : ℕ, ((n : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ n = cst * x` using `by rw [cst]; ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem tsum_norm_le (g : ℕ → ℝ) (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (hg0 : g 0 ≤ 1)
    (hg : ∀ n, 0 ≤ g n) (hb : ∀ n, g n ≤ ((n : ℝ) + 1) ^ 2 * x ^ n) :
    Summable g ∧ ∑' n, g n ≤ 1 + cst * x := by
  have hle : ∀ n, g (n + 1) ≤ x * (((n : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ n) := fun n => by
    refine (hb (n + 1)).trans ?_
    have : x ^ n ≤ (1 / 2 : ℝ) ^ n := pow_le_pow_left₀ hx0 hx n
    push_cast
    calc ((n : ℝ) + 1 + 1) ^ 2 * x ^ (n + 1) = x * (((n : ℝ) + 2) ^ 2 * x ^ n) := by ring
      _ ≤ _ := by gcongr
  have hs1 : Summable fun n => g (n + 1) :=
    Summable.of_nonneg_of_le (fun n => hg _) hle (summable_cst.mul_left x)
  have hs : Summable g := (summable_nat_add_iff 1).1 hs1
  refine ⟨hs, ?_⟩
  rw [hs.tsum_eq_zero_add]
  have := hs1.tsum_le_tsum hle (summable_cst.mul_left x)
  rw [tsum_mul_left] at this
  have e : x * ∑' n : ℕ, ((n : ℝ) + 2) ^ 2 * (1 / 2 : ℝ) ^ n = cst * x := by rw [cst]; ring
  linarith

/- English proof (translation)
Use `set F : ℕ → ℝ := fun m => ‖mulExt h m‖ with hF`. Establish `hF1 : F 1 = 1` using `by simp [hF, mulExt_one]`. Establish `hFm : ∀ {m n : ℕ}, Nat.Coprime m n → F (m * n) = F m * F n` using `fun hmn => by`. Simplify using `only [hF, mulExt_mul h hmn, norm_mul]`. Establish `hFp : ∀ {p : ℕ}, p.Prime → ∀ e, F (p ^ e) = ‖h p e‖` using `fun hp e => by`.

Simplify using `only [hF, mulExt_prime_pow h h0 hp]`. Establish `hx : ∀ p : ℕ, p.Prime → (p : ℝ) ^ (-σ) ≤ 1 / 2` using `fun p hp => by`. Establish `h2 : (2 : ℝ) ≤ p` using `by exact_mod_cast hp.two_le`. Establish `h3 : (p : ℝ) ^ (-σ) ≤ (p : ℝ) ^ (-1 : ℝ)` using `Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)`. Rewrite `h3` using `[Real.rpow_neg_one]`.

Use `h3.trans ?_` and prove the remaining obligations. Rewrite using `[one_div]`. Conclude with `inv_anti₀ (by norm_num) h2`. Establish `hloc : ∀ {p : ℕ}, p.Prime → Summable (fun n : ℕ => ‖F (p ^ n)‖) ∧ ∑' n : ℕ, F (p ^ n) ≤ 1 + cst * (p : ℝ) ^ (-σ)` using `fun {p} hp => by`. Establish `hp0 : (0 : ℝ) ≤ p` using `Nat.cast_nonneg p`.

Establish `key` using `tsum_norm_le (fun n => F (p ^ n)) ((p : ℝ) ^ (-σ)) (Real.rpow_nonneg hp0 _) (hx p hp) (by simp [hF1]) (fun n => norm_nonneg _) (fun n => by`. Simplify using `only [hFp hp]`. Use `(hb p hp n).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[← Real.rpow_natCast ((p : ℝ) ^ (-σ)) n, ← Real.rpow_mul hp0]`. Use `congr 2`.

Use the proof step `ring)`. Use `⟨key.1.congr fun n => ?_, key.2⟩` and prove the remaining obligations. Conclude with `(Real.norm_of_nonneg (show 0 ≤ F (p ^ n) from norm_nonneg _)).symm`. Establish `hZ : Summable fun n : ℕ => (n : ℝ) ^ (-σ)` using `Real.summable_nat_rpow.2 (by linarith)`. Establish `hc0 : 0 ≤ cst` using `tsum_nonneg fun n => by positivity`.

Use `summable_of_sum_le (c := Real.exp (cst * ∑' n : ℕ, (n : ℝ) ^ (-σ))) (fun _ => norm_nonneg _) fun u => ?_` and prove the remaining obligations. Take `⟨N, hN⟩ : ∃ N : ℕ, ∀ m ∈ u, m < N` from `⟨u.sup id + 1, fun m hm => Nat.lt_succ_of_le (Finset.le_sup (f := id) hm)⟩`. Establish `hall` using `EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum (f := F) hF1 hFm (fun hp => (hloc hp).1) N`. Establish `hsum` using `hall.2`. Establish `hind` using `(hasSum_subtype_iff_indicator (f := F) (s := (N.smoothNumbers : Set ℕ))).1 hsum`.

Establish `h1 : ∑ m ∈ u, F m ≤ ∏ p ∈ N.primesBelow, ∑' n : ℕ, F (p ^ n)`. Use `le_trans (le_of_eq ?_) (sum_le_hasSum u (fun i _ => ?_) hind)` and prove the remaining obligations. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos m with rfl | hpos` into its components or cases. Simplify using `[hF, mulExt_zero, Set.indicator]`.

Rewrite using `[Set.indicator_of_mem (Nat.mem_smoothNumbers_of_lt hpos (hN m hm))]`. Conclude with `Set.indicator_nonneg (fun _ _ => norm_nonneg _) _`. Use `h1.trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `Finset.prod_le_prod (fun p _ => tsum_nonneg fun n => norm_nonneg _) fun p hp => ?_` and prove the remaining obligations.

Establish `hpp` using `Nat.prime_of_mem_primesBelow hp`. Use `(hloc hpp).2.trans ?_` and prove the remaining obligations. Use `Real.add_one_le_exp (cst * (p : ℝ) ^ (-σ))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `_ = Real.exp (cst * ∑ p ∈ N.primesBelow, (p : ℝ) ^ (-σ)) := by`.

Rewrite using `[← Real.exp_sum, Finset.mul_sum]`. Use `_ ≤ _ := by`. Use `Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hc0)` and prove the remaining obligations. Conclude with `hZ.sum_le_tsum _ (fun i _ => by positivity)`.
-/
theorem summable_norm_mulExt (h : ℕ → ℕ → ℂ) (σ : ℝ) (hσ : 1 < σ) (h0 : ∀ p, h p 0 = 1)
    (hb : ∀ p, p.Prime → ∀ n : ℕ, ‖h p n‖ ≤ ((n : ℝ) + 1) ^ 2 * (p : ℝ) ^ (-(n * σ))) :
    Summable fun m => ‖mulExt h m‖ := by
  set F : ℕ → ℝ := fun m => ‖mulExt h m‖ with hF
  have hF1 : F 1 = 1 := by simp [hF, mulExt_one]
  have hFm : ∀ {m n : ℕ}, Nat.Coprime m n → F (m * n) = F m * F n := fun hmn => by
    simp only [hF, mulExt_mul h hmn, norm_mul]
  have hFp : ∀ {p : ℕ}, p.Prime → ∀ e, F (p ^ e) = ‖h p e‖ := fun hp e => by
    simp only [hF, mulExt_prime_pow h h0 hp]
  have hx : ∀ p : ℕ, p.Prime → (p : ℝ) ^ (-σ) ≤ 1 / 2 := fun p hp => by
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have h3 : (p : ℝ) ^ (-σ) ≤ (p : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    rw [Real.rpow_neg_one] at h3
    refine h3.trans ?_
    rw [one_div]
    exact inv_anti₀ (by norm_num) h2
  have hloc : ∀ {p : ℕ}, p.Prime → Summable (fun n : ℕ => ‖F (p ^ n)‖) ∧
      ∑' n : ℕ, F (p ^ n) ≤ 1 + cst * (p : ℝ) ^ (-σ) := fun {p} hp => by
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    have key := tsum_norm_le (fun n => F (p ^ n)) ((p : ℝ) ^ (-σ)) (Real.rpow_nonneg hp0 _)
      (hx p hp) (by simp [hF1]) (fun n => norm_nonneg _) (fun n => by
        simp only [hFp hp]
        refine (hb p hp n).trans (le_of_eq ?_)
        rw [← Real.rpow_natCast ((p : ℝ) ^ (-σ)) n, ← Real.rpow_mul hp0]
        congr 2
        ring)
    refine ⟨key.1.congr fun n => ?_, key.2⟩
    exact (Real.norm_of_nonneg (show 0 ≤ F (p ^ n) from norm_nonneg _)).symm
  have hZ : Summable fun n : ℕ => (n : ℝ) ^ (-σ) := Real.summable_nat_rpow.2 (by linarith)
  have hc0 : 0 ≤ cst := tsum_nonneg fun n => by positivity
  refine summable_of_sum_le (c := Real.exp (cst * ∑' n : ℕ, (n : ℝ) ^ (-σ)))
    (fun _ => norm_nonneg _) fun u => ?_
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ m ∈ u, m < N := ⟨u.sup id + 1, fun m hm =>
    Nat.lt_succ_of_le (Finset.le_sup (f := id) hm)⟩
  have hall := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum (f := F) hF1 hFm
    (fun hp => (hloc hp).1) N
  have hsum := hall.2
  have hind := (hasSum_subtype_iff_indicator (f := F) (s := (N.smoothNumbers : Set ℕ))).1 hsum
  have h1 : ∑ m ∈ u, F m ≤ ∏ p ∈ N.primesBelow, ∑' n : ℕ, F (p ^ n) := by
    refine le_trans (le_of_eq ?_) (sum_le_hasSum u (fun i _ => ?_) hind)
    · refine Finset.sum_congr rfl fun m hm => ?_
      rcases Nat.eq_zero_or_pos m with rfl | hpos
      · simp [hF, mulExt_zero, Set.indicator]
      · rw [Set.indicator_of_mem (Nat.mem_smoothNumbers_of_lt hpos (hN m hm))]
    · exact Set.indicator_nonneg (fun _ _ => norm_nonneg _) _
  refine h1.trans ?_
  calc ∏ p ∈ N.primesBelow, ∑' n : ℕ, F (p ^ n)
      ≤ ∏ p ∈ N.primesBelow, Real.exp (cst * (p : ℝ) ^ (-σ)) := by
        refine Finset.prod_le_prod (fun p _ => tsum_nonneg fun n => norm_nonneg _) fun p hp => ?_
        have hpp := Nat.prime_of_mem_primesBelow hp
        refine (hloc hpp).2.trans ?_
        have := Real.add_one_le_exp (cst * (p : ℝ) ^ (-σ))
        linarith
    _ = Real.exp (cst * ∑ p ∈ N.primesBelow, (p : ℝ) ^ (-σ)) := by
        rw [← Real.exp_sum, Finset.mul_sum]
    _ ≤ _ := by
        refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hc0)
        exact hZ.sum_le_tsum _ (fun i _ => by positivity)

/- English proof (translation)
Use `EulerProduct.eulerProduct_hasProd (f := mulExt h) (mulExt_one h) (fun hmn => mulExt_mul h hmn) (summable_norm_mulExt h σ hσ h0 hb) (mulExt_zero h)` as an intermediate fact. Establish `e : (fun p : Nat.Primes => ∑' e, mulExt h ((p : ℕ) ^ e)) = fun p : Nat.Primes => ∑' e, h p e`. Use function extensionality and compare the values at `fun p => tsum_congr fun e => mulExt_prime_pow h h0 p.2 e`. Rewrite `this` using `[e]`. Then use the resulting hypothesis.
-/
theorem hasProd_mulExt (h : ℕ → ℕ → ℂ) (σ : ℝ) (hσ : 1 < σ) (h0 : ∀ p, h p 0 = 1)
    (hb : ∀ p, p.Prime → ∀ n : ℕ, ‖h p n‖ ≤ ((n : ℝ) + 1) ^ 2 * (p : ℝ) ^ (-(n * σ))) :
    HasProd (fun p : Nat.Primes => ∑' e, h p e) (∑' m, mulExt h m) := by
  have := EulerProduct.eulerProduct_hasProd (f := mulExt h) (mulExt_one h)
    (fun hmn => mulExt_mul h hmn) (summable_norm_mulExt h σ hσ h0 hb) (mulExt_zero h)
  have e : (fun p : Nat.Primes => ∑' e, mulExt h ((p : ℕ) ^ e)) = fun p : Nat.Primes => ∑' e, h p e :=
    funext fun p => tsum_congr fun e => mulExt_prime_pow h h0 p.2 e
  rwa [e] at this

end GlobalTheory.CompanionTheory.RSEuler

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementSection (adeleAt finUnitAt finUnitsAt intUnitsAtS intUnitsAt
  hasSum_integral_finiteIdeleMeasure_of_invariant integral_finiteIdele_prod_local_mul
  mem_units_iff_ord_eq_zero)
open scoped NumberField.AdeleRing ValuativeRel ENNReal Classical

namespace GlobalTheory.CompanionTheory.RSEuler

open Ad3 Ad3.R

def od (b : Afˣ) : Pl →₀ ℤ := IdeleGroup.ordFinsupp ℚ (IdeleGroup.ofFinite b)

/- English proof (translation)
Establish `h1` using `HeckeCharacter.valued_eq_exp_ord b v`. Establish `h2` using `valued_eq_exp_neg_ord (v := v) (x := ((lf v b : (Qv v)ˣ) : Qv v)) (Units.ne_zero _)`. Establish `h3 : WithZero.exp (-IdeleGroup.ord v (IdeleGroup.ofFinite b)) = WithZero.exp (-GroundTheory.LocalField.ord ((lf v b : (Qv v)ˣ) : Qv v))` using `h1.symm.trans h2`. Establish `h4` using `WithZero.exp_injective h3`. Express the relevant statement in the definitionally equal form `IdeleGroup.ord v _ = _`.

Use linear arithmetic over natural numbers and integers.
-/
theorem od_eq_ord (b : Afˣ) (v : Pl) :
    od b v = GroundTheory.LocalField.ord ((lf v b : (Qv v)ˣ) : Qv v) := by
  have h1 := HeckeCharacter.valued_eq_exp_ord b v
  have h2 := valued_eq_exp_neg_ord (v := v) (x := ((lf v b : (Qv v)ˣ) : Qv v)) (Units.ne_zero _)
  have h3 : WithZero.exp (-IdeleGroup.ord v (IdeleGroup.ofFinite b)) =
      WithZero.exp (-GroundTheory.LocalField.ord ((lf v b : (Qv v)ˣ) : Qv v)) := h1.symm.trans h2
  have h4 := WithZero.exp_injective h3
  change IdeleGroup.ord v _ = _
  omega

/- English proof (translation)
Establish `hu' : GroundTheory.LocalField.ord (((unifUnit (Qv v) ^ (-(n : ℤ))) * a : (Qv v)ˣ) : Qv v) = 0`. Rewrite using `[ord_units_mul, ord_unifUnit_zpow, h]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `hu (unifUnit (Qv v) ^ n) _ hu'`. Rewrite using `[← h1]`.

Use `congr 1`. Simplify using `[zpow_neg]`.
-/
theorem apply_eq_pow {v : Pl} {g : (Qv v)ˣ → ℂ}
    (hu : ∀ a u : (Qv v)ˣ, GroundTheory.LocalField.ord (u : Qv v) = 0 → g (a * u) = g a)
    (a : (Qv v)ˣ) (n : ℕ) (h : GroundTheory.LocalField.ord (a : Qv v) = n) :
    g a = g (unifUnit (Qv v) ^ n) := by
  have hu' : GroundTheory.LocalField.ord (((unifUnit (Qv v) ^ (-(n : ℤ))) * a : (Qv v)ˣ) : Qv v) = 0 := by
    rw [ord_units_mul, ord_unifUnit_zpow, h]
    ring
  have h1 := hu (unifUnit (Qv v) ^ n) _ hu'
  rw [← h1]
  congr 1
  simp [zpow_neg]

def Gf (S : Finset Pl) (G : ∀ v : Pl, (Qv v)ˣ → ℂ) (b : Afˣ) : ℂ :=
  ∏ᶠ v : {v : Pl // v ∉ S}, G v.1 (lf v.1 b)

def Hf (S : Finset Pl) (G : ∀ v : Pl, (Qv v)ˣ → ℂ) (b : Afˣ) : ℂ :=
  if ∀ v ∈ S, od b v = 0 then Gf S G b else 0

def Gd (S : Finset Pl) (G : ∀ v : Pl, (Qv v)ˣ → ℂ) (σ : ℝ) : Prop :=
  ∀ v ∉ S, (∀ a u : (Qv v)ˣ, GroundTheory.LocalField.ord (u : Qv v) = 0 → G v (a * u) = G v a) ∧
    (∀ a, G v a ≠ 0 → (a : Qv v) ∈ 𝒪[Qv v]) ∧ G v 1 = 1 ∧
    ∀ n : ℕ, ‖G v (unifUnit (Qv v) ^ n)‖ ≤ ((n : ℝ) + 1) ^ 2 * (pOf v : ℝ) ^ (-(n * σ))

/- English proof (translation)
The claim follows from `ordFinsupp_ofFinite_mul b hw`.
-/
theorem od_mul {b w : Afˣ} (hw : w ∈ finiteIntegralUnits ℚ) : od (b * w) = od b :=
  ordFinsupp_ofFinite_mul b hw

/- English proof (translation)
Establish `hw' : IdeleGroup.ofFinite w ∈ IdeleGroup.standardOpenSubgroup ℚ` using `hw`. Rewrite `hw'` using `[IdeleGroup.mem_standardOpenSubgroup_iff_ord]`. Conclude with `hw' v`.
-/
theorem od_unit {w : Afˣ} (hw : w ∈ finiteIntegralUnits ℚ) (v : Pl) : od w v = 0 := by
  have hw' : IdeleGroup.ofFinite w ∈ IdeleGroup.standardOpenSubgroup ℚ := hw
  rw [IdeleGroup.mem_standardOpenSubgroup_iff_ord] at hw'
  exact hw' v

/- English proof (translation)
Use `finprod_congr fun v => ?_` and prove the remaining obligations. Establish `e : lf v.1 (b * w) = lf v.1 b * lf v.1 w` using `map_mul _ _ _`. Rewrite using `[e]`. Conclude with `(hG v.1 v.2).1 _ _ (by rw [← od_eq_ord]; exact od_unit hw v.1)`.
-/
theorem Gf_mul {S : Finset Pl} {G : ∀ v : Pl, (Qv v)ˣ → ℂ} {σ : ℝ} (hG : Gd S G σ) (b : Afˣ)
    {w : Afˣ} (hw : w ∈ finiteIntegralUnits ℚ) : Gf S G (b * w) = Gf S G b := by
  refine finprod_congr fun v => ?_
  have e : lf v.1 (b * w) = lf v.1 b * lf v.1 w := map_mul _ _ _
  rw [e]
  exact (hG v.1 v.2).1 _ _ (by rw [← od_eq_ord]; exact od_unit hw v.1)

/- English proof (translation)
Simplify using `only [Hf, od_mul hw, Gf_mul hG b hw]`.
-/
theorem Hf_mul {S : Finset Pl} {G : ∀ v : Pl, (Qv v)ˣ → ℂ} {σ : ℝ} (hG : Gd S G σ) (b : Afˣ)
    {w : Afˣ} (hw : w ∈ finiteIntegralUnits ℚ) : Hf S G (b * w) = Hf S G b := by
  simp only [Hf, od_mul hw, Gf_mul hG b hw]

def hh (vOf : ℕ → Pl) (S : Finset Pl) (G : ∀ v : Pl, (Qv v)ˣ → ℂ) (p e : ℕ) : ℂ :=
  if e = 0 then 1 else if vOf p ∈ S then 0 else G (vOf p) (unifUnit (Qv (vOf p)) ^ e)

/- English proof (translation)
Simplify using `[hh]`.
-/
theorem hh_zero (vOf : ℕ → Pl) (S : Finset Pl) (G : ∀ v : Pl, (Qv v)ˣ → ℂ) (p : ℕ) :
    hh vOf S G p 0 = 1 := by simp [hh]

/- English proof (translation)
Simplify using `[hh, hv, h, he]`.
-/
theorem hh_of_mem {vOf : ℕ → Pl} (hv : ∀ v, vOf (pOf v) = v) {S : Finset Pl}
    (G : ∀ v : Pl, (Qv v)ˣ → ℂ) {v : Pl} (h : v ∈ S) {e : ℕ} (he : e ≠ 0) :
    hh vOf S G (pOf v) e = 0 := by
  simp [hh, hv, h, he]

/- English proof (translation)
Break down `eq_or_ne e 0 with rfl | he` into its components or cases. Simplify using `[hh, (hG v h).2.2.1]`. Establish `key : ∀ w, w = v → (if w ∈ S then (0 : ℂ) else G w (unifUnit (Qv w) ^ e)) = G v (unifUnit (Qv v) ^ e)`. Introduce and unpack `_ rfl`. Simplify using `[h]`.

Simplify `key _ (hv v)` using `[hh, he]`.
-/
theorem hh_of_notMem {vOf : ℕ → Pl} (hv : ∀ v, vOf (pOf v) = v) {S : Finset Pl}
    {G : ∀ v : Pl, (Qv v)ˣ → ℂ} {σ : ℝ} (hG : Gd S G σ) {v : Pl} (h : v ∉ S) (e : ℕ) :
    hh vOf S G (pOf v) e = G v (unifUnit (Qv v) ^ e) := by
  rcases eq_or_ne e 0 with rfl | he
  · simp [hh, (hG v h).2.2.1]
  · have key : ∀ w, w = v → (if w ∈ S then (0 : ℂ) else G w (unifUnit (Qv w) ^ e)) =
        G v (unifUnit (Qv v) ^ e) := by
      rintro _ rfl
      simp [h]
    simpa [hh, he] using key _ (hv v)

/- English proof (translation)
Take `⟨v, rfl⟩` from `hsurj p hp`. Establish `hp0 : (0 : ℝ) ≤ pOf v` using `Nat.cast_nonneg _`. Distinguish the cases in `hS : v ∈ S`. Break down `eq_or_ne n 0 with rfl | hn` into its components or cases. Simplify using `[hh_zero]`.

Rewrite using `[hh_of_mem hv G hS hn, norm_zero]`. Use `Real.rpow_nonneg hp0 (-(n * σ))` as an intermediate fact. Check the signs of the components of the expression. Rewrite using `[hh_of_notMem hv hG hS]`. Conclude with `(hG v hS).2.2.2 n`.
-/
theorem hh_bound {vOf : ℕ → Pl} (hv : ∀ v, vOf (pOf v) = v)
    (hsurj : ∀ p : ℕ, p.Prime → ∃ v, pOf v = p) {S : Finset Pl}
    {G : ∀ v : Pl, (Qv v)ˣ → ℂ} {σ : ℝ} (hG : Gd S G σ) (p : ℕ) (hp : p.Prime) (n : ℕ) :
    ‖hh vOf S G p n‖ ≤ ((n : ℝ) + 1) ^ 2 * (p : ℝ) ^ (-(n * σ)) := by
  obtain ⟨v, rfl⟩ := hsurj p hp
  have hp0 : (0 : ℝ) ≤ pOf v := Nat.cast_nonneg _
  by_cases hS : v ∈ S
  · rcases eq_or_ne n 0 with rfl | hn
    · simp [hh_zero]
    · rw [hh_of_mem hv G hS hn, norm_zero]
      have := Real.rpow_nonneg hp0 (-(n * σ))
      positivity
  · rw [hh_of_notMem hv hG hS]
    exact (hG v hS).2.2.2 n

/- English proof (translation)
Rewrite using `[mulExt, if_neg hm, Finsupp.prod]`. Distinguish the cases in `hS : ∀ v ∈ S, od b v = 0`. Rewrite using `[Hf, if_pos hS, Gf]`. Establish `fact : ∀ v : {v : Pl // v ∉ S}, G v.1 (lf v.1 b) = hh vOf S G (pOf v.1) (m.factorization (pOf v.1))` using `fun v => by`. Rewrite using `[hh_of_notMem hv hG v.2]`.

Conclude with `apply_eq_pow (hG v.1 v.2).1 _ _ (by rw [← od_eq_ord, hb])`. Repeatedly rewrite using `[fact]`. Use `set g : {v : Pl // v ∉ S} → ℕ := fun v => pOf v.1 with hg`. Establish `ginj : Function.Injective g` using `fun x y h => Subtype.ext (hinj h)`. Use `set φ : ℕ → ℂ := fun p => hh vOf S G p (m.factorization p) with hφ`.

Establish `hsub : Function.mulSupport (fun v => φ (g v)) ⊆ ((m.factorization.support.preimage g ginj.injOn : Finset _) : Set _)` using `fun v hvs => by`. Simplify using `only [Finset.coe_preimage, Set.mem_preimage, Finset.mem_coe, Finsupp.mem_support_iff]`. Introduce `h0`. Apply `hvs` to reduce the goal to its premises. Simplify using `only [hφ, h0, hh_zero]`.

Express the relevant statement in the definitionally equal form `∏ᶠ v, φ (g v) = _`. Rewrite using `[finprod_eq_prod_of_mulSupport_subset _ hsub, Finset.prod_preimage g _ ginj.injOn φ fun x hx hxr => ?_]`. Establish `hxp : x.Prime` using `Nat.prime_of_mem_primeFactors (by simpa using hx)`. Take `⟨v, rfl⟩` from `hsurj x hxp`. Establish `hvS : v ∈ S`.

Assume the negation of the conclusion as `h`. Conclude with `hxr ⟨⟨v, h⟩, rfl⟩`. Establish `h0` using `hb v`. Rewrite `h0` using `[hS v hvS]`. Establish `h1 : m.factorization (pOf v) = 0` using `by exact_mod_cast h0.symm`.

Simplify using `only [hφ, h1, hh_zero]`. Rewrite `hS` using `[Hf, if_neg hS] push Not`. Take `⟨v, hvS, hne⟩` from `hS`. Establish `h1 : m.factorization (pOf v) ≠ 0` using `fun h => hne (by rw [hb, h]; rfl)`. Establish `h2 : hh vOf S G (pOf v) (m.factorization (pOf v)) = 0` using `hh_of_mem hv G hvS h1`.

Conclude with `(Finset.prod_eq_zero (Finsupp.mem_support_iff.2 h1) h2).symm`.
-/
theorem Hf_eq {vOf : ℕ → Pl} (hv : ∀ v, vOf (pOf v) = v)
    (hinj : Function.Injective pOf)
    (hsurj : ∀ p : ℕ, p.Prime → ∃ v, pOf v = p) {S : Finset Pl}
    {G : ∀ v : Pl, (Qv v)ˣ → ℂ} {σ : ℝ} (hG : Gd S G σ) (b : Afˣ) {m : ℕ} (hm : m ≠ 0)
    (hb : ∀ v, od b v = m.factorization (pOf v)) : Hf S G b = mulExt (hh vOf S G) m := by
  rw [mulExt, if_neg hm, Finsupp.prod]
  by_cases hS : ∀ v ∈ S, od b v = 0
  · rw [Hf, if_pos hS, Gf]
    have fact : ∀ v : {v : Pl // v ∉ S}, G v.1 (lf v.1 b) =
        hh vOf S G (pOf v.1) (m.factorization (pOf v.1)) := fun v => by
      rw [hh_of_notMem hv hG v.2]
      exact apply_eq_pow (hG v.1 v.2).1 _ _ (by rw [← od_eq_ord, hb])
    simp_rw [fact]
    set g : {v : Pl // v ∉ S} → ℕ := fun v => pOf v.1 with hg
    have ginj : Function.Injective g := fun x y h => Subtype.ext (hinj h)
    set φ : ℕ → ℂ := fun p => hh vOf S G p (m.factorization p) with hφ
    have hsub : Function.mulSupport (fun v => φ (g v)) ⊆
        ((m.factorization.support.preimage g ginj.injOn : Finset _) : Set _) := fun v hvs => by
      simp only [Finset.coe_preimage, Set.mem_preimage, Finset.mem_coe, Finsupp.mem_support_iff]
      intro h0
      apply hvs
      simp only [hφ, h0, hh_zero]
    change ∏ᶠ v, φ (g v) = _
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub,
      Finset.prod_preimage g _ ginj.injOn φ fun x hx hxr => ?_]
    have hxp : x.Prime := Nat.prime_of_mem_primeFactors (by simpa using hx)
    obtain ⟨v, rfl⟩ := hsurj x hxp
    have hvS : v ∈ S := by
      by_contra h
      exact hxr ⟨⟨v, h⟩, rfl⟩
    have h0 := hb v
    rw [hS v hvS] at h0
    have h1 : m.factorization (pOf v) = 0 := by exact_mod_cast h0.symm
    simp only [hφ, h1, hh_zero]
  · rw [Hf, if_neg hS]
    push Not at hS
    obtain ⟨v, hvS, hne⟩ := hS
    have h1 : m.factorization (pOf v) ≠ 0 := fun h => hne (by rw [hb, h]; rfl)
    have h2 : hh vOf S G (pOf v) (m.factorization (pOf v)) = 0 := hh_of_mem hv G hvS h1
    exact (Finset.prod_eq_zero (Finsupp.mem_support_iff.2 h1) h2).symm

/- English proof (translation)
Use `set f : ℕ →₀ ℕ := Finsupp.mapDomain pOf (n.mapRange Int.toNat rfl) with hf`. Establish `hfp : ∀ p ∈ f.support, p.Prime` using `fun p hp => by`. Use `Finsupp.mapDomain_support hp` as an intermediate fact. Take `⟨v, -, rfl⟩` from `Finset.mem_image.1 this`. Conclude with `hprime v`.

Use `⟨f.prod (· ^ ·), ?_, fun v => ?_⟩` and prove the remaining obligations. Use `Finset.prod_ne_zero_iff.2 fun p hp => pow_ne_zero _ (hfp p hp).ne_zero` and prove the remaining obligations. Rewrite using `[Nat.prod_pow_factorization_eq_self hfp, hf, Finsupp.mapDomain_apply hinj]`. Simplify using `[hn v]`.
-/
theorem exists_of_nonneg (hprime : ∀ v, (pOf v).Prime) (hinj : Function.Injective pOf)
    (n : Pl →₀ ℤ) (hn : ∀ v, 0 ≤ n v) :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ v, n v = m.factorization (pOf v) := by
  set f : ℕ →₀ ℕ := Finsupp.mapDomain pOf (n.mapRange Int.toNat rfl) with hf
  have hfp : ∀ p ∈ f.support, p.Prime := fun p hp => by
    have := Finsupp.mapDomain_support hp
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 this
    exact hprime v
  refine ⟨f.prod (· ^ ·), ?_, fun v => ?_⟩
  · refine Finset.prod_ne_zero_iff.2 fun p hp => pow_ne_zero _ (hfp p hp).ne_zero
  · rw [Nat.prod_pow_factorization_eq_self hfp, hf, Finsupp.mapDomain_apply hinj]
    simp [hn v]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v, od b v < 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hb (exists_of_nonneg hprime hinj _ h)`. Distinguish the cases in `hS : ∀ v ∈ S, od b v = 0`.

Establish `hvS : v ∉ S` using `fun h => by`. Use `hS v h` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[Hf, if_pos hS, Gf]`. Use `finprod_eq_zero _ ⟨v, hvS⟩ ?_ ?_` and prove the remaining obligations.

Assume the negation of the conclusion as `hne`. Establish `h1` using `(hG v hvS).2.1 _ hne`. Establish `h2` using `GodementSectionLocal.ord_nonneg_of_mem_integers (Units.ne_zero _) h1`. Rewrite `h2` using `[← od_eq_ord]`. Establish `h3 : 0 ≤ od b v` using `h2`.

Use linear arithmetic over natural numbers and integers. Use `((od b).support.finite_toSet.preimage Subtype.val_injective.injOn).subset fun x hx => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_preimage, Finset.mem_coe, Finsupp.mem_support_iff]`. Introduce `h0`. Apply `hx` to reduce the goal to its premises.

Use `apply_eq_pow (hG x.1 x.2).1 (lf x.1 b) 0 (by rw [← od_eq_ord, h0]; rfl)` as an intermediate fact. Simplify using `only [this, pow_zero]`. Conclude with `(hG x.1 x.2).2.2.1`. Rewrite using `[Hf, if_neg hS]`.
-/
theorem Hf_zero (hprime : ∀ v, (pOf v).Prime) (hinj : Function.Injective pOf)
    {S : Finset Pl} {G : ∀ v : Pl, (Qv v)ˣ → ℂ} {σ : ℝ} (hG : Gd S G σ) (b : Afˣ)
    (hb : ¬ ∃ m : ℕ, m ≠ 0 ∧ ∀ v, od b v = m.factorization (pOf v)) : Hf S G b = 0 := by
  obtain ⟨v, hv⟩ : ∃ v, od b v < 0 := by
    by_contra h
    push Not at h
    exact hb (exists_of_nonneg hprime hinj _ h)
  by_cases hS : ∀ v ∈ S, od b v = 0
  · have hvS : v ∉ S := fun h => by
      have := hS v h
      omega
    rw [Hf, if_pos hS, Gf]
    refine finprod_eq_zero _ ⟨v, hvS⟩ ?_ ?_
    · by_contra hne
      have h1 := (hG v hvS).2.1 _ hne
      have h2 := GodementSectionLocal.ord_nonneg_of_mem_integers (Units.ne_zero _) h1
      rw [← od_eq_ord] at h2
      have h3 : 0 ≤ od b v := h2
      omega
    · refine ((od b).support.finite_toSet.preimage Subtype.val_injective.injOn).subset
        fun x hx => ?_
      simp only [Set.mem_preimage, Finset.mem_coe, Finsupp.mem_support_iff]
      intro h0
      apply hx
      have := apply_eq_pow (hG x.1 x.2).1 (lf x.1 b) 0 (by rw [← od_eq_ord, h0]; rfl)
      simp only [this, pow_zero]
      exact (hG x.1 x.2).2.2.1
  · rw [Hf, if_neg hS]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h v hv`. Conclude with `(mem_units_iff_ord_eq_zero b v).1 (h ⟨v, hv⟩ (Set.mem_univ _))`. Introduce `h v _`. Conclude with `(mem_units_iff_ord_eq_zero b v.1).2 (h v.1 v.2)`.
-/
theorem mem_units_iff {S : Finset Pl} (b : Afˣ) :
    b ∈ finUnitsAt S ⁻¹' intUnitsAtS S ↔ ∀ v ∈ S, od b v = 0 := by
  constructor
  · intro h v hv
    exact (mem_units_iff_ord_eq_zero b v).1 (h ⟨v, hv⟩ (Set.mem_univ _))
  · intro h v _
    exact (mem_units_iff_ord_eq_zero b v.1).2 (h v.1 v.2)

/- English proof (translation)
Use function extensionality and compare the values at `b`. Distinguish the cases in `h : ∀ v ∈ S, od b v = 0`. Rewrite using `[Set.indicator_of_mem ((mem_units_iff b).2 h), Hf, if_pos h]`. Rewrite using `[Set.indicator_of_notMem (fun h' => h ((mem_units_iff b).1 h')), Hf, if_neg h]`.
-/
theorem indicator_eq (S : Finset Pl) (G : ∀ v : Pl, (Qv v)ˣ → ℂ) :
    (finUnitsAt S ⁻¹' intUnitsAtS S).indicator (Gf S G) = Hf S G := by
  funext b
  by_cases h : ∀ v ∈ S, od b v = 0
  · rw [Set.indicator_of_mem ((mem_units_iff b).2 h), Hf, if_pos h]
  · rw [Set.indicator_of_notMem (fun h' => h ((mem_units_iff b).1 h')), Hf, if_neg h]

def nm (hinj : Function.Injective pOf) (m : ℕ) : Pl →₀ ℤ :=
  (m.factorization.comapDomain pOf hinj.injOn).mapRange (fun n : ℕ => (n : ℤ)) rfl

/- English proof (translation)
Simplify using `[nm, Finsupp.comapDomain_apply]`.
-/
theorem nm_apply (hinj : Function.Injective pOf) (m : ℕ) (v : Pl) :
    nm hinj m v = m.factorization (pOf v) := by
  simp [nm, Finsupp.comapDomain_apply]

abbrev QQ : Type := Afˣ ⧸ finiteIntegralUnits ℚ

/- English proof (translation)
Take `⟨b, hb⟩` from `HeckeCharacter.exists_ordFinsupp_eq (nm hinj m)`. Take `⟨w, hw⟩` from `QuotientGroup.mk_out_eq_mul (finiteIntegralUnits ℚ) b`. Use `⟨(b : QQ), fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[hw, od_mul w.2, ← nm_apply hinj]`. Conclude with `congrArg (fun f => f v) hb`.
-/
theorem exists_class (hinj : Function.Injective pOf) (m : ℕ) :
    ∃ c : QQ, ∀ v, od c.out v = m.factorization (pOf v) := by
  obtain ⟨b, hb⟩ := HeckeCharacter.exists_ordFinsupp_eq (nm hinj m)
  obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul (finiteIntegralUnits ℚ) b
  refine ⟨(b : QQ), fun v => ?_⟩
  rw [hw, od_mul w.2, ← nm_apply hinj]
  exact congrArg (fun f => f v) hb

/- English proof (translation)
The claim follows from `ordFinsupp_ofFinite_out_injective (Finsupp.ext h)`.
-/
theorem class_unique {c d : QQ} (h : ∀ v, od c.out v = od d.out v) : c = d :=
  ordFinsupp_ofFinite_out_injective (Finsupp.ext h)

/- English proof (translation)
Use `set f := mulExt (hh vOf S G) with hf`. Establish `hsn : Summable fun m => ‖f m‖` using `summable_norm_mulExt _ σ hσ (hh_zero vOf S G) (hh_bound hv hsurj hG)`. Set `ι : {m : ℕ // m ≠ 0} → QQ` to `fun m => (exists_class hinj m.1).choose`. Establish `hι : ∀ m v, od (ι m).out v = m.1.factorization (pOf v)` using `fun m => (exists_class hinj m.1).choose_spec`. Establish `ιinj : Function.Injective ι` using `fun m m' h => by`.

Use `Subtype.ext (Nat.eq_of_factorization_eq m.2 m'.2 fun p => ?_)` and prove the remaining obligations. Distinguish the cases in `hp : p.Prime`. Take `⟨v, rfl⟩` from `hsurj p hp`. Establish `h1` using `hι m v`. Rewrite `h1` using `[h, hι m' v]`.

Conclude with `h1.symm` after adjusting the coercions. Simplify using `[Nat.factorization_eq_zero_of_not_prime _ hp]`. Establish `hval : ∀ m, Hf S G (ι m).out = f m.1` using `fun m => Hf_eq hv hinj hsurj hG _ m.2 (hι m)`. Establish `hout : ∀ c, c ∉ Set.range ι → Hf S G c.out = 0` using `fun c hc => Hf_zero hprime hinj hG _ fun ⟨m, hm, hcm⟩ => hc ⟨⟨m, hm⟩, class_unique fun v => by`. Rewrite using `[hι, hcm]⟩`.

Establish `hsub : Function.support f ⊆ {m : ℕ | m ≠ 0}` using `fun m hm h0 => hm (by`. Rewrite using `[h0, hf, mulExt_zero])`. Establish `hs1 : HasSum (fun m : {m : ℕ // m ≠ 0} => f m.1) (∑' m, f m)` using `(hasSum_subtype_iff_of_support_subset hsub).2 hsn.of_norm.hasSum`. Establish `hs2 : Summable (fun m : {m : ℕ // m ≠ 0} => ‖f m.1‖)` using `hsn.subtype _`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[← ιinj.summable_iff (fun c hc => by simp [hout c hc])]`. Use `hs2.congr fun m => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, hval]`. Rewrite using `[← ιinj.hasSum_iff hout]`. Conclude with `hs1.congr_fun fun m => hval m`.
-/
theorem hasSum_Hf {vOf : ℕ → Pl} (hv : ∀ v, vOf (pOf v) = v)
    (hprime : ∀ v, (pOf v).Prime) (hinj : Function.Injective pOf)
    (hsurj : ∀ p : ℕ, p.Prime → ∃ v, pOf v = p) {S : Finset Pl}
    {G : ∀ v : Pl, (Qv v)ˣ → ℂ} {σ : ℝ} (hσ : 1 < σ) (hG : Gd S G σ) :
    Summable (fun c : QQ => ‖Hf S G c.out‖) ∧
      HasSum (fun c : QQ => Hf S G c.out) (∑' m, mulExt (hh vOf S G) m) := by
  set f := mulExt (hh vOf S G) with hf
  have hsn : Summable fun m => ‖f m‖ :=
    summable_norm_mulExt _ σ hσ (hh_zero vOf S G) (hh_bound hv hsurj hG)
  let ι : {m : ℕ // m ≠ 0} → QQ := fun m => (exists_class hinj m.1).choose
  have hι : ∀ m v, od (ι m).out v = m.1.factorization (pOf v) := fun m =>
    (exists_class hinj m.1).choose_spec
  have ιinj : Function.Injective ι := fun m m' h => by
    refine Subtype.ext (Nat.eq_of_factorization_eq m.2 m'.2 fun p => ?_)
    by_cases hp : p.Prime
    · obtain ⟨v, rfl⟩ := hsurj p hp
      have h1 := hι m v
      rw [h, hι m' v] at h1
      exact_mod_cast h1.symm
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  have hval : ∀ m, Hf S G (ι m).out = f m.1 := fun m =>
    Hf_eq hv hinj hsurj hG _ m.2 (hι m)
  have hout : ∀ c, c ∉ Set.range ι → Hf S G c.out = 0 := fun c hc =>
    Hf_zero hprime hinj hG _ fun ⟨m, hm, hcm⟩ => hc ⟨⟨m, hm⟩, class_unique fun v => by
      rw [hι, hcm]⟩
  have hsub : Function.support f ⊆ {m : ℕ | m ≠ 0} := fun m hm h0 => hm (by
    rw [h0, hf, mulExt_zero])
  have hs1 : HasSum (fun m : {m : ℕ // m ≠ 0} => f m.1) (∑' m, f m) :=
    (hasSum_subtype_iff_of_support_subset hsub).2 hsn.of_norm.hasSum
  have hs2 : Summable (fun m : {m : ℕ // m ≠ 0} => ‖f m.1‖) :=
    hsn.subtype _
  constructor
  · rw [← ιinj.summable_iff (fun c hc => by simp [hout c hc])]
    refine hs2.congr fun m => ?_
    simp only [Function.comp_apply, hval]
  · rw [← ιinj.hasSum_iff hout]
    exact hs1.congr_fun fun m => hval m

/- English proof (translation)
Establish `hinv : ∀ x, ∀ w ∈ finiteIntegralUnits ℚ, Hf S G (x * w) = Hf S G x` using `fun x w hw => Hf_mul hG x hw`. Establish `hcont : Continuous (Hf S G)` using `continuous_of_forall_mul_eq (isOpen_finiteIntegralUnits ℚ) hinv`. Use `⟨hcont.aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Rewrite using `[hasFiniteIntegral_iff_enorm]`. Establish `h1` using `lintegral_eq_tsum_of_forall_mul_eq (finiteIdeleMeasure ℚ) (isOpen_finiteIntegralUnits ℚ) (F := fun x => ‖Hf S G x‖ₑ) (fun x w hw => by simp only [hinv x w hw])`.

Rewrite using `[h1, finiteIdeleMeasure_finiteIntegralUnits]`. Simplify using `only [mul_one]`. Establish `h2 : Summable fun c : QQ => ‖Hf S G c.out‖₊` using `NNReal.summable_coe.1 hs`. Conclude with `(ENNReal.tsum_coe_ne_top_iff_summable.2 h2).lt_top`.
-/
theorem integrable_Hf {S : Finset Pl} {G : ∀ v : Pl, (Qv v)ˣ → ℂ} {σ : ℝ} (hG : Gd S G σ)
    (hs : Summable (fun c : QQ => ‖Hf S G c.out‖)) :
    Integrable (Hf S G) (finiteIdeleMeasure ℚ) := by
  have hinv : ∀ x, ∀ w ∈ finiteIntegralUnits ℚ, Hf S G (x * w) = Hf S G x := fun x w hw =>
    Hf_mul hG x hw
  have hcont : Continuous (Hf S G) :=
    continuous_of_forall_mul_eq (isOpen_finiteIntegralUnits ℚ) hinv
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have h1 := lintegral_eq_tsum_of_forall_mul_eq (finiteIdeleMeasure ℚ)
    (isOpen_finiteIntegralUnits ℚ) (F := fun x => ‖Hf S G x‖ₑ)
    (fun x w hw => by simp only [hinv x w hw])
  rw [h1, finiteIdeleMeasure_finiteIntegralUnits]
  simp only [mul_one]
  have h2 : Summable fun c : QQ => ‖Hf S G c.out‖₊ := NNReal.summable_coe.1 hs
  exact (ENNReal.tsum_coe_ne_top_iff_summable.2 h2).lt_top

/- English proof (translation)
Introduce `S A G σ hσ hA hG'`. Establish `hG : Gd S G σ` using `hG'`. Take `⟨hloc, hinj, hsurj, -⟩` from `hB`. Establish `hprime : ∀ v, (pOf v).Prime` using `fun v => (hloc v).2.2.1`. Establish `: Nonempty Pl` using `⟨(hsurj 2 Nat.prime_two).choose⟩`.

Use `set vOf : ℕ → Pl := Function.invFun pOf with hvOf`. Establish `hv : ∀ v, vOf (pOf v) = v` using `Function.leftInverse_invFun hinj`. Establish `hsn` using `(hasSum_Hf hv hprime hinj hsurj hσ hG)`. Use `set L := ∑' m, mulExt (hh vOf S G) m with hL`. Establish `hprod : HasProd (fun v : {v : Pl // v ∉ S} => ∑' n : ℕ, G v.1 (unifUnit (Qv v.1) ^ n)) L`.

Establish `h1` using `hasProd_mulExt (hh vOf S G) σ hσ (hh_zero vOf S G) (hh_bound hv hsurj hG)`. Set `ι : {v : Pl // v ∉ S} → Nat.Primes` to `fun v => ⟨pOf v.1, hprime v.1⟩`. Establish `ιinj : Function.Injective ι` using `fun x y h => Subtype.ext (hinj (congrArg Subtype.val h))`. Establish `hout : ∀ x, x ∉ Set.range ι → ∑' e, hh vOf S G x e = 1` using `fun x hx => by`. Take `⟨v, hv'⟩` from `hsurj x.1 x.2`.

Establish `hvS : v ∈ S`. Assume the negation of the conclusion as `h`. Conclude with `hx ⟨⟨v, h⟩, Subtype.ext hv'⟩`. Rewrite using `[tsum_eq_single 0 fun e he => by rw [← hv']; exact hh_of_mem hv G hvS he, hh_zero]`. Establish `h2` using `(ιinj.hasProd_iff hout).2 h1`.

Conclude with `h2.congr_fun fun v => tsum_congr fun n => (hh_of_notMem hv hG v.2 n).symm`. Establish `hint` using `integrable_Hf hG hsn.1`. Establish `hinv : ∀ x, ∀ w ∈ finiteIntegralUnits ℚ, Hf S G (x * w) = Hf S G x` using `fun x w hw => Hf_mul hG x hw`. Establish `hval : ∫ b, Hf S G b ∂finiteIdeleMeasure ℚ = L` using `(hasSum_integral_finiteIdeleMeasure_of_invariant hint hinv).unique hsn.2`. Establish `hGcont : Continuous (Gf S G)` using `continuous_of_forall_mul_eq (isOpen_finiteIntegralUnits ℚ) fun x w hw => Gf_mul hG x hw`.

Establish `hdep : ∀ b b', (∀ w ∉ S, finUnitAt w b = finUnitAt w b') → Gf S G b = Gf S G b'` using `fun b b' h => finprod_congr fun v => congrArg (G v.1) (h v.1 v.2)`. Establish `key` using `integral_finiteIdele_prod_local_mul S A hA hGcont.measurable hdep (by rw [indicator_eq]; exact hint)`. Use `⟨hprod.multipliable, ?_⟩` and prove the remaining obligations. Rewrite using `[hprod.tprod_eq, ← hval, ← indicator_eq]`. Conclude with `key.2`.
-/
theorem eulerProduct_integral (hB : B0) : E1 := by
  intro S A G σ hσ hA hG'
  have hG : Gd S G σ := hG'
  obtain ⟨hloc, hinj, hsurj, -⟩ := hB
  have hprime : ∀ v, (pOf v).Prime := fun v => (hloc v).2.2.1
  have : Nonempty Pl := ⟨(hsurj 2 Nat.prime_two).choose⟩
  set vOf : ℕ → Pl := Function.invFun pOf with hvOf
  have hv : ∀ v, vOf (pOf v) = v := Function.leftInverse_invFun hinj
  have hsn := (hasSum_Hf hv hprime hinj hsurj hσ hG)
  set L := ∑' m, mulExt (hh vOf S G) m with hL
  have hprod : HasProd (fun v : {v : Pl // v ∉ S} => ∑' n : ℕ, G v.1 (unifUnit (Qv v.1) ^ n)) L := by
    have h1 := hasProd_mulExt (hh vOf S G) σ hσ (hh_zero vOf S G) (hh_bound hv hsurj hG)
    let ι : {v : Pl // v ∉ S} → Nat.Primes := fun v => ⟨pOf v.1, hprime v.1⟩
    have ιinj : Function.Injective ι := fun x y h => Subtype.ext (hinj (congrArg Subtype.val h))
    have hout : ∀ x, x ∉ Set.range ι → ∑' e, hh vOf S G x e = 1 := fun x hx => by
      obtain ⟨v, hv'⟩ := hsurj x.1 x.2
      have hvS : v ∈ S := by
        by_contra h
        exact hx ⟨⟨v, h⟩, Subtype.ext hv'⟩
      rw [tsum_eq_single 0 fun e he => by rw [← hv']; exact hh_of_mem hv G hvS he, hh_zero]
    have h2 := (ιinj.hasProd_iff hout).2 h1
    exact h2.congr_fun fun v => tsum_congr fun n => (hh_of_notMem hv hG v.2 n).symm
  have hint := integrable_Hf hG hsn.1
  have hinv : ∀ x, ∀ w ∈ finiteIntegralUnits ℚ, Hf S G (x * w) = Hf S G x := fun x w hw =>
    Hf_mul hG x hw
  have hval : ∫ b, Hf S G b ∂finiteIdeleMeasure ℚ = L :=
    (hasSum_integral_finiteIdeleMeasure_of_invariant hint hinv).unique hsn.2
  have hGcont : Continuous (Gf S G) :=
    continuous_of_forall_mul_eq (isOpen_finiteIntegralUnits ℚ) fun x w hw => Gf_mul hG x hw
  have hdep : ∀ b b', (∀ w ∉ S, finUnitAt w b = finUnitAt w b') → Gf S G b = Gf S G b' :=
    fun b b' h => finprod_congr fun v => congrArg (G v.1) (h v.1 v.2)
  have key := integral_finiteIdele_prod_local_mul S A hA hGcont.measurable hdep
    (by rw [indicator_eq]; exact hint)
  refine ⟨hprod.multipliable, ?_⟩
  rw [hprod.tprod_eq, ← hval, ← indicator_eq]
  exact key.2

end GlobalTheory.CompanionTheory.RSEuler

end
