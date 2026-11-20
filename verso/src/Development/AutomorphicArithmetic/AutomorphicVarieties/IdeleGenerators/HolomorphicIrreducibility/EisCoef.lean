import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.TsumNormEisensteinTranslate
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Lipschitz

open Complex UpperHalfPlane UpperTheory.V.Af

namespace UpperTheory.V.Sd

/- English proof (translation)
Establish `hs : Summable fun c : ℕ+ × ℕ+ => (c.2 : ℂ) ^ (k - 1) * x ^ (c.2 : ℕ) * q ^ (c.1 * c.2 : ℕ)`. Use `Summable.of_norm_bounded (summable_prod_mul_pow (k - 1) hq).norm fun c => ?_` and prove the remaining obligations. Simplify using `[norm_pow, hx]`. Use `⟨∑' c : ℕ+ × ℕ+, (c.2 : ℂ) ^ (k - 1) * x ^ (c.2 : ℕ) * q ^ (c.1 * c.2 : ℕ), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hasSum_pnat_iff_hasSum_succ (f := fun m => Lk k (x * q ^ m))]`.

Use `hs.hasSum.prod_fiberwise fun m => ?_` and prove the remaining obligations. Establish `h1 : ‖x * q ^ (m : ℕ)‖ < 1`. Rewrite using `[norm_mul, hx, one_mul, norm_pow]`. Conclude with `pow_lt_one₀ (norm_nonneg _) hq m.ne_zero`. Establish `h2` using `(lipschitz k hk).1 _ h1`.

Rewrite `h2` using `[← hasSum_nat_add_iff' 1]`. Establish `hk' : k - 1 ≠ 0` using `by omega`. Simplify using `only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_pow hk', zero_mul, sub_zero] at h2`. Rewrite `h2` using `[← hasSum_pnat_iff_hasSum_succ (f := fun e : ℕ => (e : ℂ) ^ (k - 1) * (x * q ^ (m : ℕ)) ^ e)]`. Simplify `h2` using `only [mul_pow, pow_mul, mul_assoc]`.

Rewrite using `[← hasSum_pnat_iff_hasSum_succ (f := fun n => (∑ e ∈ n.divisors, (e : ℂ) ^ (k - 1) * x ^ e) * q ^ n)]`. Establish `h2` using `sigmaAntidiagonalEquivProd.hasSum_iff.2 hs.hasSum`. Use `h2.sigma fun n => ?_` and prove the remaining obligations. Use `(congrArg (HasSum _) ?_).mpr (hasSum_fintype _)` and prove the remaining obligations. Simplify using `only [Function.comp, sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors, PNat.mk_coe, Equiv.coe_fn_mk, Finset.univ_eq_attach]`.

Rewrite using `[(n : ℕ).divisorsAntidiagonal.sum_attach (fun y : ℕ × ℕ => (y.2 : ℂ) ^ (k - 1) * x ^ y.2 * q ^ (y.1 * y.2)), Nat.sum_divisorsAntidiagonal' (fun u y => (y : ℂ) ^ (k - 1) * x ^ y * q ^ (u * y)), Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hi)]`.
-/
private lemma lambert (k : ℕ) (hk : 2 ≤ k) {x q : ℂ} (hx : ‖x‖ = 1) (hq : ‖q‖ < 1) :
    ∃ S : ℂ, HasSum (fun m : ℕ => Lk k (x * q ^ (m + 1))) S ∧
      HasSum (fun n : ℕ => (∑ e ∈ (n + 1).divisors, (e : ℂ) ^ (k - 1) * x ^ e) * q ^ (n + 1)) S := by
  have hs : Summable fun c : ℕ+ × ℕ+ => (c.2 : ℂ) ^ (k - 1) * x ^ (c.2 : ℕ) * q ^ (c.1 * c.2 : ℕ) := by
    refine Summable.of_norm_bounded (summable_prod_mul_pow (k - 1) hq).norm fun c => ?_
    simp [norm_pow, hx]
  refine ⟨∑' c : ℕ+ × ℕ+, (c.2 : ℂ) ^ (k - 1) * x ^ (c.2 : ℕ) * q ^ (c.1 * c.2 : ℕ), ?_, ?_⟩
  · rw [← hasSum_pnat_iff_hasSum_succ (f := fun m => Lk k (x * q ^ m))]
    refine hs.hasSum.prod_fiberwise fun m => ?_
    have h1 : ‖x * q ^ (m : ℕ)‖ < 1 := by
      rw [norm_mul, hx, one_mul, norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) hq m.ne_zero
    have h2 := (lipschitz k hk).1 _ h1
    rw [← hasSum_nat_add_iff' 1] at h2
    have hk' : k - 1 ≠ 0 := by omega
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_pow hk', zero_mul, sub_zero] at h2
    rw [← hasSum_pnat_iff_hasSum_succ (f := fun e : ℕ => (e : ℂ) ^ (k - 1) * (x * q ^ (m : ℕ)) ^ e)] at h2
    simpa only [mul_pow, pow_mul, mul_assoc] using h2
  · rw [← hasSum_pnat_iff_hasSum_succ (f := fun n => (∑ e ∈ n.divisors, (e : ℂ) ^ (k - 1) * x ^ e) * q ^ n)]
    have h2 := sigmaAntidiagonalEquivProd.hasSum_iff.2 hs.hasSum
    refine h2.sigma fun n => ?_
    refine (congrArg (HasSum _) ?_).mpr (hasSum_fintype _)
    simp only [Function.comp, sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors,
      PNat.mk_coe, Equiv.coe_fn_mk, Finset.univ_eq_attach]
    rw [(n : ℕ).divisorsAntidiagonal.sum_attach
      (fun y : ℕ × ℕ => (y.2 : ℂ) ^ (k - 1) * x ^ y.2 * q ^ (y.1 * y.2)),
      Nat.sum_divisorsAntidiagonal' (fun u y => (y : ℂ) ^ (k - 1) * x ^ y * q ^ (u * y)), Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hi)]

/- English proof (translation)
Establish `hN : (N : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 (NeZero.ne N)`. Establish `hC : lipC k ≠ 0`. Unfold `lipC`. Use `Nat.factorial_ne_zero (k - 1)` as an intermediate fact. Simplify using `[Real.pi_ne_zero, this]`.

Establish `h0 : ((b : ℂ) / N).im = 0`. Rewrite using `[show (b : ℂ) / N = (((b : ℝ) / N : ℝ) : ℂ) by push_cast; rfl, ofReal_im]`. Establish `h` using `(lipschitz k hk).2 (m * (z : ℂ) + b / N) ?_ ?_`. Establish `e : cexp (2 * Real.pi * Complex.I * (m * (z : ℂ) + b / N)) = (ZMod.stdAddChar (b : ZMod N) : ℂ) * (Function.Periodic.qParam 1 z) ^ m`. Rewrite using `[ZMod.stdAddChar_coe, Function.Periodic.qParam, ← Complex.exp_nat_mul, ← Complex.exp_add]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[e]`. Establish `h'` using `h.mul_left (lipC k)⁻¹`.

Rewrite `h'` using `[inv_mul_cancel_left₀ hC]`. Use `(congrArg (fun F => HasSum F _) (funext fun j => ?_)).mpr (h')` and prove the remaining obligations. Establish `: (((N * m : ℤ)) : ℂ) * (z : ℂ) + ((b + N * j : ℤ) : ℂ) = N * (m * (z : ℂ) + b / N + j)`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, mul_zpow, zpow_neg (N : ℂ), zpow_natCast]`. Clear the denominators using the available nonvanishing facts. Use `z.im_pos` as an intermediate fact. Simplify using `[h0]`.

Check the signs of the components of the expression. Introduce `j hj`. Establish `h1` using `congrArg Complex.im hj`. Use `z.im_pos.ne'` as an intermediate fact. Simplify using `[h0, this] at h1`.

Substitute `h1` using the available equality. Apply `hb` to reduce the goal to its premises. Establish `: (b : ℂ) = ((N * j : ℤ) : ℂ)`. Use `push_cast`. Rewrite using `[← hj]`.

Clear the denominators using the available nonvanishing facts. Simplify using the standard rewrite rules. Rewrite using `[Int.cast_injective this]`. Simplify using the standard rewrite rules.
-/
private lemma row (N k : ℕ) [NeZero N] (hk : 2 ≤ k) (b : ℤ) (hb : (b : ZMod N) ≠ 0) (z : ℍ) (m : ℕ) :
    HasSum (fun j : ℤ => (N : ℂ) ^ k / lipC k * ((((N * m : ℤ)) : ℂ) * (z : ℂ) + ((b + N * j : ℤ) : ℂ)) ^ (-(k : ℤ)))
      (Lk k ((ZMod.stdAddChar (b : ZMod N) : ℂ) * (Function.Periodic.qParam 1 z) ^ m)) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hC : lipC k ≠ 0 := by
    unfold lipC
    have := Nat.factorial_ne_zero (k - 1)
    simp [Real.pi_ne_zero, this]
  have h0 : ((b : ℂ) / N).im = 0 := by
    rw [show (b : ℂ) / N = (((b : ℝ) / N : ℝ) : ℂ) by push_cast; rfl, ofReal_im]
  have h := (lipschitz k hk).2 (m * (z : ℂ) + b / N) ?_ ?_
  · have e : cexp (2 * Real.pi * Complex.I * (m * (z : ℂ) + b / N)) =
        (ZMod.stdAddChar (b : ZMod N) : ℂ) * (Function.Periodic.qParam 1 z) ^ m := by
      rw [ZMod.stdAddChar_coe, Function.Periodic.qParam, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [e] at h
    have h' := h.mul_left (lipC k)⁻¹
    rw [inv_mul_cancel_left₀ hC] at h'
    refine (congrArg (fun F => HasSum F _) (funext fun j => ?_)).mpr (h')
    have : (((N * m : ℤ)) : ℂ) * (z : ℂ) + ((b + N * j : ℤ) : ℂ) = N * (m * (z : ℂ) + b / N + j) := by
      push_cast
      field_simp
      ring
    rw [this, mul_zpow, zpow_neg (N : ℂ), zpow_natCast]
    field_simp
  · have := z.im_pos
    simp [h0]
    positivity
  · intro j hj
    have h1 := congrArg Complex.im hj
    have := z.im_pos.ne'
    simp [h0, this] at h1
    subst h1
    apply hb
    have : (b : ℂ) = ((N * j : ℤ) : ℂ) := by
      push_cast
      rw [← hj]
      field_simp
      simp
    rw [Int.cast_injective this]
    simp

/- English proof (translation)
Establish `hN : (N : ℤ) ≠ 0` using `Nat.cast_ne_zero.2 (NeZero.ne N)`. Establish `hs : Summable fun v : ℤ × ℤ => ((v.1 : ℂ) * (z : ℂ) + (v.2 : ℂ)) ^ (-(k : ℤ))`. Use `(EisensteinSeries.summable_norm_eisSummand (k := k) (by exact_mod_cast hk) z).of_norm` as an intermediate fact. Rewrite `this` using `[← (finTwoArrowEquiv ℤ).symm.summable_iff]`. Conclude with `this`.

Set `g : ℤ × ℤ → {v : ℤ × ℤ // (v.1 : ZMod N) = 0 ∧ (v.2 : ZMod N) = (b : ZMod N)}` to `fun c => ⟨(N * c.1, b + N * c.2), by simp⟩`. Establish `hg : Function.Bijective g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a1, a2⟩ ⟨b1, b2⟩ h`. Simplify `h` using `[g, hN, NeZero.ne N]`.

Introduce and unpack `⟨⟨v1, v2⟩, h1, h2⟩`. Take `⟨c1, rfl⟩` from `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h1`. Take `⟨c2, h⟩` from `(ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h2.symm`. Use `⟨(c1, c2), Subtype.ext (Prod.ext rfl ?_)⟩` and prove the remaining obligations. Simplify using `only [g] at h ⊢`.

Use linear arithmetic over natural numbers and integers. Establish `h` using `((Equiv.ofBijective g hg).hasSum_iff.2 (hs.subtype _).hasSum).mul_left ((N : ℂ) ^ k / lipC k)`. Conclude with `h`.
-/
private lemma reindex (N k : ℕ) [NeZero N] (hk : 3 ≤ k) (b : ℤ) (z : ℍ) :
    HasSum (fun c : ℤ × ℤ => (N : ℂ) ^ k / lipC k *
      ((((N * c.1 : ℤ)) : ℂ) * (z : ℂ) + ((b + N * c.2 : ℤ) : ℂ)) ^ (-(k : ℤ))) (eisFun N k (b : ZMod N) z) := by
  have hN : (N : ℤ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hs : Summable fun v : ℤ × ℤ => ((v.1 : ℂ) * (z : ℂ) + (v.2 : ℂ)) ^ (-(k : ℤ)) := by
    have := (EisensteinSeries.summable_norm_eisSummand (k := k) (by exact_mod_cast hk) z).of_norm
    rw [← (finTwoArrowEquiv ℤ).symm.summable_iff] at this
    exact this
  let g : ℤ × ℤ → {v : ℤ × ℤ // (v.1 : ZMod N) = 0 ∧ (v.2 : ZMod N) = (b : ZMod N)} :=
    fun c => ⟨(N * c.1, b + N * c.2), by simp⟩
  have hg : Function.Bijective g := by
    constructor
    · rintro ⟨a1, a2⟩ ⟨b1, b2⟩ h
      simpa [g, hN, NeZero.ne N] using h
    · rintro ⟨⟨v1, v2⟩, h1, h2⟩
      obtain ⟨c1, rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h1
      obtain ⟨c2, h⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h2.symm
      refine ⟨(c1, c2), Subtype.ext (Prod.ext rfl ?_)⟩
      simp only [g] at h ⊢
      omega
  have h := ((Equiv.ofBijective g hg).hasSum_iff.2 (hs.subtype _).hasSum).mul_left ((N : ℂ) ^ k / lipC k)
  exact h

/- English proof (translation)
Use `set q := Function.Periodic.qParam 1 (z : ℂ) with hqd`. Establish `hq : ‖q‖ < 1` using `by simpa using UpperHalfPlane.norm_qParam_lt_one 1 z`. Establish `hk2 : 2 ≤ k` using `by omega`. Establish `hn : ∀ c : ZMod N, ‖(ZMod.stdAddChar c : ℂ)‖ = 1` using `fun c => by`. Rewrite using `[ZMod.stdAddChar_apply]`.

Conclude with `Circle.norm_coe _`. Take `⟨S, hS1, hS2⟩` from `lambert k hk2 (hn b) hq`. Take `⟨T, hT1, hT2⟩` from `lambert k hk2 (hn (-b)) hq`. Set `g : ℤ → ℂ` to `fun m => if 0 ≤ m then Lk k ((ZMod.stdAddChar (b : ZMod N) : ℂ) * q ^ m.toNat) else (-1) ^ k * Lk k ((ZMod.stdAddChar (-(b : ZMod N)) : ℂ) * q ^ (-m).toNat)`. Establish `h1 : HasSum g (eisFun N k (b : ZMod N) z)`.

Use `(reindex N k hk b z).prod_fiberwise fun m => ?_` and prove the remaining obligations. Distinguish the cases in `hm : 0 ≤ m`. Use `lift m to ℕ using hm`. Simplify `row N k hk2 b hb z m` using `only [g, Nat.cast_nonneg, if_true, Int.toNat_natCast]`. Take `⟨m, rfl⟩ : ∃ m' : ℕ, m = -(m' : ℤ)` from `⟨(-m).toNat, by omega⟩`.

Establish `h` using `(row N k hk2 (-b) (by simpa using hb) z m).mul_left ((-1) ^ k)`. Rewrite `h` using `[← (Equiv.neg ℤ).hasSum_iff]`. Simplify using `only [g, if_neg hm, neg_neg, Int.toNat_natCast]`. Rewrite `h` using `[Int.cast_neg]`. Use `(congrArg (fun F => HasSum F _) (funext fun j => ?_)).mpr (h)` and prove the remaining obligations.

Establish `: (((N * -(m : ℤ) : ℤ)) : ℂ) * (z : ℂ) + ((b + N * j : ℤ) : ℂ) = (-1) * ((((N * m : ℤ)) : ℂ) * (z : ℂ) + ((-b + N * -j : ℤ) : ℂ))`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Function.comp, Equiv.neg_apply]`. Rewrite using `[this, mul_zpow, zpow_neg (-1 : ℂ), zpow_natCast, ← inv_pow, inv_neg_one]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h2 : HasSum g ((Lk k (ZMod.stdAddChar (b : ZMod N) : ℂ) + S) + (-1) ^ k * T)`. Use `HasSum.of_nat_of_neg_add_one ?_ ?_` and prove the remaining obligations. Use `HasSum.zero_add (f := fun m : ℕ => Lk k ((ZMod.stdAddChar (b : ZMod N) : ℂ) * q ^ m)) hS1` as an intermediate fact. Simplify `this` using `[g]`.

Use `(congrArg (fun F => HasSum F _) (funext fun n => ?_)).mpr (hT1.mul_left ((-1) ^ k))` and prove the remaining obligations. Establish `: ¬ (0 : ℤ) ≤ -((n : ℤ) + 1)` using `by omega`. Simplify using `only [g, if_neg this, neg_neg]`. Both sides reduce to the same expression. Rewrite using `[h1.unique h2, add_assoc, ← hasSum_nat_add_iff' 1]`.

Simplify using `only [Finset.range_one, Finset.sum_singleton, if_true, pow_zero, smul_eq_mul, mul_one, add_sub_cancel_left, Nat.succ_ne_zero, if_false]`. Use `(congrArg (fun F => HasSum F _) (funext fun n => ?_)).mpr (hS2.add (hT2.mul_left ((-1) ^ k)))` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← add_mul, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `congr 1`. Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations.

Rewrite using `[← AddChar.map_nsmul_eq_pow, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, nsmul_eq_mul, mul_neg, mul_comm (e : ZMod N)]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma expansion (N k : ℕ) [NeZero N] (hk : 3 ≤ k) (b : ℤ) (hb : (b : ZMod N) ≠ 0) (z : ℍ) :
    HasSum (fun n : ℕ => (if n = 0 then Lk k (ZMod.stdAddChar (b : ZMod N) : ℂ) else
      ∑ e ∈ n.divisors, (e : ℂ) ^ (k - 1) * ((ZMod.stdAddChar ((b : ZMod N) * (e : ZMod N)) : ℂ) +
        (-1) ^ k * (ZMod.stdAddChar (-((b : ZMod N) * (e : ZMod N))) : ℂ))) • (Function.Periodic.qParam 1 z) ^ n)
      (eisFun N k (b : ZMod N) z) := by
  set q := Function.Periodic.qParam 1 (z : ℂ) with hqd
  have hq : ‖q‖ < 1 := by simpa using UpperHalfPlane.norm_qParam_lt_one 1 z
  have hk2 : 2 ≤ k := by omega
  have hn : ∀ c : ZMod N, ‖(ZMod.stdAddChar c : ℂ)‖ = 1 := fun c => by
    rw [ZMod.stdAddChar_apply]; exact Circle.norm_coe _
  obtain ⟨S, hS1, hS2⟩ := lambert k hk2 (hn b) hq
  obtain ⟨T, hT1, hT2⟩ := lambert k hk2 (hn (-b)) hq
  let g : ℤ → ℂ := fun m => if 0 ≤ m then Lk k ((ZMod.stdAddChar (b : ZMod N) : ℂ) * q ^ m.toNat) else
    (-1) ^ k * Lk k ((ZMod.stdAddChar (-(b : ZMod N)) : ℂ) * q ^ (-m).toNat)
  have h1 : HasSum g (eisFun N k (b : ZMod N) z) := by
    refine (reindex N k hk b z).prod_fiberwise fun m => ?_
    by_cases hm : 0 ≤ m
    · lift m to ℕ using hm
      simpa only [g, Nat.cast_nonneg, if_true, Int.toNat_natCast] using row N k hk2 b hb z m
    · obtain ⟨m, rfl⟩ : ∃ m' : ℕ, m = -(m' : ℤ) := ⟨(-m).toNat, by omega⟩
      have h := (row N k hk2 (-b) (by simpa using hb) z m).mul_left ((-1) ^ k)
      rw [← (Equiv.neg ℤ).hasSum_iff] at h
      simp only [g, if_neg hm, neg_neg, Int.toNat_natCast]
      rw [Int.cast_neg] at h
      refine (congrArg (fun F => HasSum F _) (funext fun j => ?_)).mpr (h)
      have : (((N * -(m : ℤ) : ℤ)) : ℂ) * (z : ℂ) + ((b + N * j : ℤ) : ℂ) =
          (-1) * ((((N * m : ℤ)) : ℂ) * (z : ℂ) + ((-b + N * -j : ℤ) : ℂ)) := by
        push_cast
        ring
      simp only [Function.comp, Equiv.neg_apply]
      rw [this, mul_zpow, zpow_neg (-1 : ℂ), zpow_natCast, ← inv_pow, inv_neg_one]
      ring
  have h2 : HasSum g ((Lk k (ZMod.stdAddChar (b : ZMod N) : ℂ) + S) + (-1) ^ k * T) := by
    refine HasSum.of_nat_of_neg_add_one ?_ ?_
    · have := HasSum.zero_add (f := fun m : ℕ => Lk k ((ZMod.stdAddChar (b : ZMod N) : ℂ) * q ^ m)) hS1
      simpa [g] using this
    · refine (congrArg (fun F => HasSum F _) (funext fun n => ?_)).mpr (hT1.mul_left ((-1) ^ k))
      have : ¬ (0 : ℤ) ≤ -((n : ℤ) + 1) := by omega
      simp only [g, if_neg this, neg_neg]
      rfl
  rw [h1.unique h2, add_assoc, ← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, if_true, pow_zero, smul_eq_mul, mul_one, add_sub_cancel_left,
    Nat.succ_ne_zero, if_false]
  refine (congrArg (fun F => HasSum F _) (funext fun n => ?_)).mpr (hS2.add (hT2.mul_left ((-1) ^ k)))
  rw [← mul_assoc, ← add_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← AddChar.map_nsmul_eq_pow, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, nsmul_eq_mul, mul_neg, mul_comm (e : ZMod N)]
  ring

end UpperTheory.V.Sd

/- English proof (translation)
Introduce `N k _ hk a ha`. Take `⟨b, rfl⟩` from `ZMod.intCast_surjective a`. Take `⟨f, hf⟩` from `UpperTheory.V.Sd.eisMF N k hk b`. Establish `h` using `ModularFormClass.qExpansion_coeff_unique (f := f) one_pos (by rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples 1) (fun τ => by rw [hf]; exact UpperTheory.V.Sd.expansion N k hk b ha τ)`. Rewrite `h` using `[hf]`.

Use `⟨(h 0).symm, fun n hn => ?_⟩` and prove the remaining obligations. Rewrite using `[UpperTheory.V.Af.coef, ← h n, if_neg (by omega)]`.
-/
theorem UpperTheory.V.Sd.eisCoef :
    UpperTheory.V.Sd.EisCoef := by
  intro N k _ hk a ha
  obtain ⟨b, rfl⟩ := ZMod.intCast_surjective a
  obtain ⟨f, hf⟩ := UpperTheory.V.Sd.eisMF N k hk b
  have h := ModularFormClass.qExpansion_coeff_unique (f := f) one_pos
    (by rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples 1)
    (fun τ => by rw [hf]; exact UpperTheory.V.Sd.expansion N k hk b ha τ)
  rw [hf] at h
  refine ⟨(h 0).symm, fun n hn => ?_⟩
  rw [UpperTheory.V.Af.coef, ← h n, if_neg (by omega)]
