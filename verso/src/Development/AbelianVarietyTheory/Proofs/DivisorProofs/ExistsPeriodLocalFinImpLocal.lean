import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixedLocalChains.Period

open Finset

/- English proof (translation)
Establish `hs : Summable (fun n : ℕ => r ^ (n + 1) * a n)`. Use `Summable.of_norm_bounded ((summable_geometric_of_lt_one hr0 hr1).mul_left (B * r)) (fun n => ?_)` and prove the remaining obligations. Rewrite using `[Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hr0 _), pow_succ]`. Use `mul_le_mul_of_nonneg_left (hB n) (mul_nonneg (pow_nonneg hr0 n) hr0)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h` using `hs.sum_add_tsum_nat_add o`. Establish `hshift : (fun i : ℕ => r ^ (i + o + 1) * a (i + o)) = fun i => r ^ o * (r ^ (i + 1) * a i)`. Use function extensionality and compare the values at `i`. Rewrite using `[ha, show i + o + 1 = o + (i + 1) by omega, pow_add]; ring`. Simplify using `only [hshift, tsum_mul_left] at h`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem one_sub_mul_tsum_of_periodic (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (o : ℕ) (a : ℕ → ℝ)
    (ha : ∀ n, a (n + o) = a n) (B : ℝ) (hB : ∀ n, |a n| ≤ B) :
    (1 - r ^ o) * ∑' n : ℕ, r ^ (n + 1) * a n = ∑ n ∈ range o, r ^ (n + 1) * a n := by
  have hs : Summable (fun n : ℕ => r ^ (n + 1) * a n) := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hr0 hr1).mul_left (B * r)) (fun n => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hr0 _), pow_succ]
    have := mul_le_mul_of_nonneg_left (hB n) (mul_nonneg (pow_nonneg hr0 n) hr0)
    linarith
  have h := hs.sum_add_tsum_nat_add o
  have hshift : (fun i : ℕ => r ^ (i + o + 1) * a (i + o)) = fun i => r ^ o * (r ^ (i + 1) * a i) := by
    funext i
    rw [ha, show i + o + 1 = o + (i + 1) by omega, pow_add]; ring
  simp only [hshift, tsum_mul_left] at h
  linarith

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Simplify using `only [phiPow, pow_zero, Function.iterate_zero, id]`. Both sides reduce to the same expression. Consider the case `succ n ih`.

Rewrite using `[Function.iterate_succ_apply', ← ih]`. Simplify using `only [phiPow, pow_succ', pow_one]`. Both sides reduce to the same expression.
-/
theorem phiPow_eq_iterate (D : D7) (p : ℕ) [Fact p.Prime] (n : ℕ) (τ : Emb D p) :
    phiPow D n τ = (phiPow D (p := p) 1)^[n] τ := by
  induction n with
  | zero =>
    simp only [phiPow, pow_zero, Function.iterate_zero, id]
    rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← ih]
    simp only [phiPow, pow_succ', pow_one]
    rfl

/- English proof (translation)
Introduce `τ τ' h`. Use extensionality with `x`. Use `congrArg (fun f : Emb D p => f x) h` as an intermediate fact. Simplify using `only [phiPow, pow_one, RingHom.comp_apply] at this`. Conclude with `(sgF p).injective this`.
-/
theorem phiPow_one_injective (D : D7) (p : ℕ) [Fact p.Prime] : Function.Injective (phiPow D (p := p) 1) := by
  intro τ τ' h
  ext x
  have := congrArg (fun f : Emb D p => f x) h
  simp only [phiPow, pow_one, RingHom.comp_apply] at this
  exact (sgF p).injective this

/- English proof (translation)
Break down `isEmpty_or_nonempty (Emb D p) with h | h` into its components or cases. Use `infer_instance`. Take `⟨τ⟩` from `h`. Establish `: CharZero (KW p)` using `(RingHom.charZero_iff τ.injective).1 inferInstance`. Use `infer_instance`.
-/
theorem emb_finite (D : D7) (p : ℕ) [Fact p.Prime] : Finite (Emb D p) := by
  rcases isEmpty_or_nonempty (Emb D p) with h | h
  · infer_instance
  · obtain ⟨τ⟩ := h
    have : CharZero (KW p) := (RingHom.charZero_iff τ.injective).1 inferInstance
    infer_instance

end GlobalTheory.MixedLocalChains.Period

open GlobalTheory.MixedLocalChains.Period in
/- English proof (translation)
Introduce `D p _`. Use `emb_finite D p` as an intermediate fact. Establish `hbij` using `Finite.injective_iff_bijective.1 (phiPow_one_injective D p)`. Set `e : Equiv.Perm (Emb D p)` to `Equiv.ofBijective _ hbij`. Use `⟨orderOf e, orderOf_pos e, fun τ => ?_, ?_⟩` and prove the remaining obligations.

Establish `h1` using `congrArg (fun f : Equiv.Perm (Emb D p) => f τ) (pow_orderOf_eq_one e)`. Simplify using `only [Equiv.Perm.coe_pow, Equiv.Perm.coe_one, id] at h1`. Conclude with `h1`. Introduce `N rk M hfin τ k hk m _ Q _ set r : ℝ := ((p : ℝ) ^ k)⁻¹ with hr`. Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast (Fact.out : p.Prime).one_lt`.

Establish `hr0 : 0 ≤ r` using `by positivity`. Establish `hr1 : r < 1` using `inv_lt_one_of_one_lt₀ (one_lt_pow₀ hp1 (by omega))`. Establish `hpow : ∀ n : ℕ, ((p : ℝ) ^ (n * k))⁻¹ = r ^ n` using `fun n => by`. Rewrite using `[hr, inv_pow, ← pow_mul, mul_comm]`. Set `g : Emb D p → ℝ` to `fun σ => chDiv (M.lie σ).x (k - 1) (evQ _ Q)`.

Set `a : ℕ → ℝ` to `fun n => g (phiPow D (n + 1) τ)`. Establish `hper : ∀ n, a (n + orderOf e) = a n` using `fun n => by`. Establish `h1` using `congrArg (fun f : Equiv.Perm (Emb D p) => f τ) (pow_orderOf_eq_one e)`. Simplify using `only [Equiv.Perm.coe_pow, Equiv.Perm.coe_one, id] at h1`. Simplify using `only [a]`.

Rewrite using `[phiPow_eq_iterate, phiPow_eq_iterate, show n + orderOf e + 1 = (n + 1) + orderOf e by omega, Function.iterate_add_apply]`. Conclude with `congrArg (fun σ => g ((phiPow D (p := p) 1)^[n + 1] σ)) h1`. Choose the witnesses or unpack the hypotheses as in `⟨B, hB⟩ : ∃ B : ℝ, ∀ σ, |g σ| ≤ B := by`. Take `⟨B, hB⟩` from `(Set.finite_range (fun σ => |g σ|)).bddAbove`. Conclude with `⟨B, fun σ => hB ⟨σ, rfl⟩⟩`.

Establish `key` using `one_sub_mul_tsum_of_periodic r hr0 hr1 (orderOf e) a hper B (fun n => hB _)`. Establish `hf` using `hfin τ k hk (evQ _ Q)`. Simplify using `only [hpow] at hf ⊢`. Establish `hne : (1 : ℝ) - r ^ orderOf e ≠ 0`. Establish `: r ^ orderOf e < 1` using `pow_lt_one₀ hr0 hr1 (orderOf_pos e).ne'`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hS : chk (M.lie τ) k (evQ _ Q) + chk (M.om τ) k (evQ _ Q) + chDiv (M.lie τ).x (k - 1) (evQ _ Q) / ((p : ℝ) - 1) = ∑' n : ℕ, r ^ (n + 1) * a n`. Apply `mul_left_cancel₀ hne` to reduce the goal to its premises. Rewrite using `[key, hf]`. Simplify using `only [a, g] at hS`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem GlobalTheory.MixedLocalChains.exists_period_localFin_imp_local : ∀ (D : D7) (p : ℕ) [Fact p.Prime], ∃ o : ℕ, 0 < o ∧ (∀ τ : Emb D p, (phiPow D (p := p) 1)^[o] τ = τ) ∧ ∀ (N : ℕ) (rk : Emb D p → ℕ) (M : DV.Mdl D p N rk), LocalFin M o → Local M := by
  intro D p _
  have := emb_finite D p
  have hbij := Finite.injective_iff_bijective.1 (phiPow_one_injective D p)
  let e : Equiv.Perm (Emb D p) := Equiv.ofBijective _ hbij
  refine ⟨orderOf e, orderOf_pos e, fun τ => ?_, ?_⟩
  · have h1 := congrArg (fun f : Equiv.Perm (Emb D p) => f τ) (pow_orderOf_eq_one e)
    simp only [Equiv.Perm.coe_pow, Equiv.Perm.coe_one, id] at h1
    exact h1
  · intro N rk M hfin τ k hk m _ Q _
    set r : ℝ := ((p : ℝ) ^ k)⁻¹ with hr
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    have hr0 : 0 ≤ r := by positivity
    have hr1 : r < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hp1 (by omega))
    have hpow : ∀ n : ℕ, ((p : ℝ) ^ (n * k))⁻¹ = r ^ n := fun n => by
      rw [hr, inv_pow, ← pow_mul, mul_comm]
    let g : Emb D p → ℝ := fun σ => chDiv (M.lie σ).x (k - 1) (evQ _ Q)
    let a : ℕ → ℝ := fun n => g (phiPow D (n + 1) τ)
    have hper : ∀ n, a (n + orderOf e) = a n := fun n => by
      have h1 := congrArg (fun f : Equiv.Perm (Emb D p) => f τ) (pow_orderOf_eq_one e)
      simp only [Equiv.Perm.coe_pow, Equiv.Perm.coe_one, id] at h1
      simp only [a]
      rw [phiPow_eq_iterate, phiPow_eq_iterate, show n + orderOf e + 1 = (n + 1) + orderOf e by omega,
        Function.iterate_add_apply]
      exact congrArg (fun σ => g ((phiPow D (p := p) 1)^[n + 1] σ)) h1
    obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ σ, |g σ| ≤ B := by
      obtain ⟨B, hB⟩ := (Set.finite_range (fun σ => |g σ|)).bddAbove
      exact ⟨B, fun σ => hB ⟨σ, rfl⟩⟩
    have key := one_sub_mul_tsum_of_periodic r hr0 hr1 (orderOf e) a hper B (fun n => hB _)
    have hf := hfin τ k hk (evQ _ Q)
    simp only [hpow] at hf ⊢
    have hne : (1 : ℝ) - r ^ orderOf e ≠ 0 := by
      have : r ^ orderOf e < 1 := pow_lt_one₀ hr0 hr1 (orderOf_pos e).ne'
      linarith
    have hS : chk (M.lie τ) k (evQ _ Q) + chk (M.om τ) k (evQ _ Q) + chDiv (M.lie τ).x (k - 1) (evQ _ Q) / ((p : ℝ) - 1) =
        ∑' n : ℕ, r ^ (n + 1) * a n := by
      apply mul_left_cancel₀ hne
      rw [key, hf]
    simp only [a, g] at hS
    linarith
