import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

open GlobalTheory.InertZeta

namespace GlobalTheory.InertZeta.LeviSum

/- English proof (translation)
Apply `HasSum.of_nat_of_neg_add_one` to reduce the goal to its premises. Establish `e : ∀ n : ℕ, β ^ (n : ℤ) * y₀ ^ (n : ℤ).natAbs = (y₀ * β) ^ n` using `fun n => by`. Simplify using `[zpow_natCast, mul_pow, mul_comm]`. Simplify using `only [e]`. Conclude with `hasSum_geometric_of_norm_lt_one h1`.

Establish `e : ∀ n : ℕ, β ^ (-((n : ℤ) + 1)) * y₀ ^ (-((n : ℤ) + 1)).natAbs = y₀ / β * (y₀ / β) ^ n` using `fun n => by`. Rewrite using `[show (-((n : ℤ) + 1)) = -((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast, show (-((n + 1 : ℕ) : ℤ)).natAbs = n + 1 by omega, div_pow]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [e]`.

Conclude with `(hasSum_geometric_of_norm_lt_one h2).mul_left (y₀ / β)`.
-/
theorem int_geom (β y₀ : ℂ) (hβ : β ≠ 0) (h1 : ‖y₀ * β‖ < 1) (h2 : ‖y₀ / β‖ < 1) :
    HasSum (fun a : ℤ => β ^ a * y₀ ^ a.natAbs) ((1 - y₀ * β)⁻¹ + y₀ / β * (1 - y₀ / β)⁻¹) := by
  apply HasSum.of_nat_of_neg_add_one
  · have e : ∀ n : ℕ, β ^ (n : ℤ) * y₀ ^ (n : ℤ).natAbs = (y₀ * β) ^ n := fun n => by
      simp [zpow_natCast, mul_pow, mul_comm]
    simp only [e]
    exact hasSum_geometric_of_norm_lt_one h1
  · have e : ∀ n : ℕ, β ^ (-((n : ℤ) + 1)) * y₀ ^ (-((n : ℤ) + 1)).natAbs = y₀ / β * (y₀ / β) ^ n := fun n => by
      rw [show (-((n : ℤ) + 1)) = -((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
        show (-((n + 1 : ℕ) : ℤ)).natAbs = n + 1 by omega, div_pow]
      field_simp
      ring
    simp only [e]
    exact (hasSum_geometric_of_norm_lt_one h2).mul_left (y₀ / β)

/- English proof (translation)
Establish `h : ((a.natAbs : ℕ) : ℤ) = 2 * (a.toNat : ℤ) - a` using `by omega`. Rewrite using `[← zpow_natCast, ← zpow_add₀ hq, ← pow_mul, ← zpow_natCast]`. Use `congr 1`. Rewrite using `[Nat.cast_mul, Nat.cast_mul, h]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem q_pow (q : ℂ) (hq : q ≠ 0) (N : ℕ) (a : ℤ) :
    q ^ ((2 * N + 2) * a.toNat) * q ^ (-a * ((N : ℤ) + 1)) = (q ^ (N + 1)) ^ a.natAbs := by
  have h : ((a.natAbs : ℕ) : ℤ) = 2 * (a.toNat : ℤ) - a := by omega
  rw [← zpow_natCast, ← zpow_add₀ hq, ← pow_mul, ← zpow_natCast]
  congr 1
  rw [Nat.cast_mul, Nat.cast_mul, h]
  push_cast
  ring

/- English proof (translation)
Establish `hq0 : (q : ℂ) ≠ 0` using `by exact_mod_cast (by omega : q ≠ 0)`. Use `set y₀ := (q : ℂ) ^ (N + 1) * X₀ with hy₀`. Establish `hA` using `int_geom β y₀ hβ (by rw [norm_mul]; exact h1) (by rw [norm_div, div_eq_mul_inv]; exact h2)`. Establish `sA : Summable (fun a : ℤ => ‖β ^ a * y₀ ^ a.natAbs‖)` using `summable_norm_iff.mpr hA.summable`. Establish `sB : Summable (fun b : Y => ‖((q : ℂ) ^ 2 * X₀) ^ l b * ψ b‖)` using `summable_norm_iff.mpr hZ.summable`.

Establish `sAB : Summable (fun p : ℤ × Y => (β ^ p.1 * y₀ ^ p.1.natAbs) * (((q : ℂ) ^ 2 * X₀) ^ l p.2 * ψ p.2))` using `summable_mul_of_summable_norm (f := fun a : ℤ => β ^ a * y₀ ^ a.natAbs) (g := fun b : Y => ((q : ℂ) ^ 2 * X₀) ^ l b * ψ b) sA sB`. Establish `hprod` using `(HasSum.mul (f := fun a : ℤ => β ^ a * y₀ ^ a.natAbs) (g := fun b : Y => ((q : ℂ) ^ 2 * X₀) ^ l b * ψ b) hA hZ sAB).mul_right (jFac q N X₀)`. Establish `n1 : 1 - y₀ * β ≠ 0` using `fun h => by`. Establish `e : ‖y₀ * β‖ = 1` using `by rw [← sub_eq_zero.mp h, norm_one]`. Rewrite `e` using `[norm_mul]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `n2 : 1 - y₀ / β ≠ 0` using `fun h => by`. Establish `e : ‖y₀ / β‖ = 1` using `by rw [← sub_eq_zero.mp h, norm_one]`. Rewrite `e` using `[norm_div, div_eq_mul_inv]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hβy : β - y₀ ≠ 0` using `fun h => n2 (by rw [← sub_eq_zero.mp h, div_self hβ, sub_self])`. Establish `hβy' : -y₀ + β ≠ 0` using `by rwa [neg_add_eq_sub]`. Establish `n3 : 1 - y₀ ^ 2 ≠ 0` using `fun h => by`. Rewrite `h` using `[sub_eq_zero]`. Use `congrArg norm h` as an intermediate fact.

Rewrite `this` using `[norm_one, norm_pow]`. Use polynomial arithmetic with `[norm_nonneg y₀]`. Establish `ev : ((1 - y₀ * β)⁻¹ + y₀ / β * (1 - y₀ / β)⁻¹) * Z₀ * jFac q N X₀ = (1 - X₀) * (1 + q * X₀) * ((1 - y₀ * β)⁻¹ * (1 - y₀ / β)⁻¹) * Z₀`. Simplify using `only [jFac]`. Rewrite using `[← hy₀]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← ev]`. Use `hprod using 1` and compare the differences between its conclusion and the goal. Use `case e'_3 => rfl`.

Use function extensionality and compare the values at `p`. Take `⟨a, b⟩` from `p`. Simplify using `only`. Rewrite using `[hy₀, mul_pow, ← q_pow (q : ℂ) hq0 N a, pow_add, pow_add, mul_pow, ← pow_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem core (Y : Type) (q N : ℕ) (l : Y → ℕ) (ψ : Y → ℂ) (β X₀ Z₀ : ℂ) (hq : 1 ≤ q) (hβ : β ≠ 0)
    (hy : ‖(q : ℂ) ^ (N + 1) * X₀‖ < 1) (h1 : ‖(q : ℂ) ^ (N + 1) * X₀‖ * ‖β‖ < 1)
    (h2 : ‖(q : ℂ) ^ (N + 1) * X₀‖ * ‖β‖⁻¹ < 1)
    (hZ : HasSum (fun b => ((q : ℂ) ^ 2 * X₀) ^ l b * ψ b) Z₀) :
    HasSum (fun p : ℤ × Y => ((q : ℂ) ^ (2 * l p.2 + (2 * N + 2) * p.1.toNat) * X₀ ^ (p.1.natAbs + l p.2) *
      jFac q N X₀) * (β ^ p.1 * (q : ℂ) ^ (-p.1 * ((N : ℤ) + 1)) * ψ p.2))
      ((1 - X₀) * (1 + q * X₀) * ((1 - (q : ℂ) ^ (N + 1) * X₀ * β)⁻¹ * (1 - (q : ℂ) ^ (N + 1) * X₀ / β)⁻¹) * Z₀) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  set y₀ := (q : ℂ) ^ (N + 1) * X₀ with hy₀
  have hA := int_geom β y₀ hβ (by rw [norm_mul]; exact h1) (by rw [norm_div, div_eq_mul_inv]; exact h2)
  have sA : Summable (fun a : ℤ => ‖β ^ a * y₀ ^ a.natAbs‖) := summable_norm_iff.mpr hA.summable
  have sB : Summable (fun b : Y => ‖((q : ℂ) ^ 2 * X₀) ^ l b * ψ b‖) := summable_norm_iff.mpr hZ.summable
  have sAB : Summable (fun p : ℤ × Y => (β ^ p.1 * y₀ ^ p.1.natAbs) * (((q : ℂ) ^ 2 * X₀) ^ l p.2 * ψ p.2)) :=
    summable_mul_of_summable_norm (f := fun a : ℤ => β ^ a * y₀ ^ a.natAbs)
      (g := fun b : Y => ((q : ℂ) ^ 2 * X₀) ^ l b * ψ b) sA sB
  have hprod := (HasSum.mul (f := fun a : ℤ => β ^ a * y₀ ^ a.natAbs)
      (g := fun b : Y => ((q : ℂ) ^ 2 * X₀) ^ l b * ψ b) hA hZ sAB).mul_right (jFac q N X₀)
  have n1 : 1 - y₀ * β ≠ 0 := fun h => by
    have e : ‖y₀ * β‖ = 1 := by rw [← sub_eq_zero.mp h, norm_one]
    rw [norm_mul] at e; linarith
  have n2 : 1 - y₀ / β ≠ 0 := fun h => by
    have e : ‖y₀ / β‖ = 1 := by rw [← sub_eq_zero.mp h, norm_one]
    rw [norm_div, div_eq_mul_inv] at e; linarith
  have hβy : β - y₀ ≠ 0 := fun h => n2 (by rw [← sub_eq_zero.mp h, div_self hβ, sub_self])
  have hβy' : -y₀ + β ≠ 0 := by rwa [neg_add_eq_sub]
  have n3 : 1 - y₀ ^ 2 ≠ 0 := fun h => by
    rw [sub_eq_zero] at h
    have := congrArg norm h
    rw [norm_one, norm_pow] at this
    nlinarith [norm_nonneg y₀]
  have ev : ((1 - y₀ * β)⁻¹ + y₀ / β * (1 - y₀ / β)⁻¹) * Z₀ * jFac q N X₀ =
      (1 - X₀) * (1 + q * X₀) * ((1 - y₀ * β)⁻¹ * (1 - y₀ / β)⁻¹) * Z₀ := by
    simp only [jFac]
    rw [← hy₀]
    field_simp
    ring
  rw [← ev]
  convert hprod using 1
  case e'_3 => rfl
  funext p
  obtain ⟨a, b⟩ := p
  simp only
  rw [hy₀, mul_pow, ← q_pow (q : ℂ) hq0 N a, pow_add, pow_add, mul_pow, ← pow_mul]
  ring

end GlobalTheory.InertZeta.LeviSum

namespace GlobalTheory.InertZeta

open LeviSum in

/- English proof (translation)
Introduce `Y C q N ℓ l φ₀ α X y Z hq hα hy hy1 hyα hyα' H hZ`. Substitute `hy` using the available equality. Establish `hg` using `core Y q N l φ₀ α X Z hq hα hy1 hyα hyα' hZ`. Establish `hfib : ∀ ab : ℤ × Y, HasSum (fun c => X ^ ℓ ab.1 ab.2 c * (α ^ ab.1 * (q : ℂ) ^ (-ab.1 * ((N : ℤ) + 1)) * φ₀ ab.2)) (((q : ℂ) ^ (2 * l ab.2 + (2 * N + 2) * ab.1.toNat) * X ^ (ab.1.natAbs + l ab.2) * jFac q N X) * (α ^ ab.1 * (q : ℂ) ^ (-ab.1 * ((N : ℤ) + 1)) * φ₀ ab.2))` using `fun ab => (H X hy1 ab.1 ab.2).mul_right _`. Establish `hXn : ‖(q : ℂ) ^ (N + 1) * ((‖X‖ : ℝ) : ℂ)‖ = ‖(q : ℂ) ^ (N + 1) * X‖`.

Rewrite using `[norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm]`. Establish `hαn : ‖((‖α‖ : ℝ) : ℂ)‖ = ‖α‖` using `by rw [Complex.norm_real, Real.norm_eq_abs, abs_norm]`. Establish `hZn : Summable (fun b => ((q : ℂ) ^ 2 * ((‖X‖ : ℝ) : ℂ)) ^ l b * ((‖φ₀ b‖ : ℝ) : ℂ))`. Use `Complex.summable_ofReal.mpr (summable_norm_iff.mpr hZ.summable)` as an intermediate fact. Use `this using 2 with b` and compare the differences between its conclusion and the goal.

Move the coercions through the operations in `[norm_mul, norm_pow, Complex.norm_natCast]`. Expand and normalize the polynomial expressions, which then agree. Establish `hgn` using `core Y q N l (fun b => ((‖φ₀ b‖ : ℝ) : ℂ)) ((‖α‖ : ℝ) : ℂ) ((‖X‖ : ℝ) : ℂ) _ hq (by exact_mod_cast norm_ne_zero_iff.mpr hα) (hXn ▸ hy1) (by rw [hXn, hαn]; exact hyα) (by rw [hXn, hαn]; exact hyα') hZn.hasSum`. Establish `hfibn : ∀ ab : ℤ × Y, HasSum (fun c => ((‖X‖ : ℝ) : ℂ) ^ ℓ ab.1 ab.2 c * (((‖α‖ : ℝ) : ℂ) ^ ab.1 * (q : ℂ) ^ (-ab.1 * ((N : ℤ) + 1)) * ((‖φ₀ ab.2‖ : ℝ) : ℂ))) (((q : ℂ) ^ (2 * l ab.2 + (2 * N + 2) * ab.1.toNat) * ((‖X‖ : ℝ) : ℂ) ^ (ab.1.natAbs + l ab.2) * jFac q N ((‖X‖ : ℝ) : ℂ) …` using `fun ab => (H _ (hXn ▸ hy1) ab.1 ab.2).mul_right _`. Establish `hnorm : ∀ p : (ℤ × Y) × C, ((‖X ^ ℓ p.1.1 p.1.2 p.2 * (α ^ p.1.1 * (q : ℂ) ^ (-p.1.1 * ((N : ℤ) + 1)) * φ₀ p.1.2)‖ : ℝ) : ℂ) = ((‖X‖ : ℝ) : ℂ) ^ ℓ p.1.1 p.1.2 p.2 * (((‖α‖ : ℝ) : ℂ) ^ p.1.1 * (q : ℂ) ^ (-p.1.1 * ((N : ℤ) + 1)) * ((‖φ₀ p.1.2‖ : ℝ) : ℂ))`.

Introduce `p`. Rewrite using `[norm_mul, norm_mul, norm_mul, norm_pow, norm_zpow, norm_zpow, Complex.norm_natCast]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hsum : Summable (fun p : (ℤ × Y) × C => X ^ ℓ p.1.1 p.1.2 p.2 * (α ^ p.1.1 * (q : ℂ) ^ (-p.1.1 * ((N : ℤ) + 1)) * φ₀ p.1.2))`.

Rewrite using `[← summable_norm_iff, summable_prod_of_nonneg (fun _ => norm_nonneg _)]`. Use `⟨fun ab => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Complex.summable_ofReal]`. Conclude with `(funext fun c => (hnorm (ab, c)).symm) ▸ (hfibn ab).summable`. Rewrite using `[← Complex.summable_ofReal]`.

Use `hgn.summable.congr fun ab => ?_` and prove the remaining obligations. Rewrite using `[Complex.ofReal_tsum]`. Conclude with `((funext fun c => (hnorm (ab, c)).symm) ▸ (hfibn ab)).tsum_eq.symm`. Rewrite using `[hg.unique (hsum.hasSum.prod_fiberwise hfib)]`. Conclude with `hsum.hasSum`.
-/
theorem step : Step := by
  intro Y C q N ℓ l φ₀ α X y Z hq hα hy hy1 hyα hyα' H hZ
  subst hy
  have hg := core Y q N l φ₀ α X Z hq hα hy1 hyα hyα' hZ
  have hfib : ∀ ab : ℤ × Y, HasSum (fun c => X ^ ℓ ab.1 ab.2 c *
      (α ^ ab.1 * (q : ℂ) ^ (-ab.1 * ((N : ℤ) + 1)) * φ₀ ab.2))
      (((q : ℂ) ^ (2 * l ab.2 + (2 * N + 2) * ab.1.toNat) * X ^ (ab.1.natAbs + l ab.2) * jFac q N X) *
        (α ^ ab.1 * (q : ℂ) ^ (-ab.1 * ((N : ℤ) + 1)) * φ₀ ab.2)) :=
    fun ab => (H X hy1 ab.1 ab.2).mul_right _

  have hXn : ‖(q : ℂ) ^ (N + 1) * ((‖X‖ : ℝ) : ℂ)‖ = ‖(q : ℂ) ^ (N + 1) * X‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm]
  have hαn : ‖((‖α‖ : ℝ) : ℂ)‖ = ‖α‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_norm]
  have hZn : Summable (fun b => ((q : ℂ) ^ 2 * ((‖X‖ : ℝ) : ℂ)) ^ l b * ((‖φ₀ b‖ : ℝ) : ℂ)) := by
    have := Complex.summable_ofReal.mpr (summable_norm_iff.mpr hZ.summable)
    convert this using 2 with b
    push_cast [norm_mul, norm_pow, Complex.norm_natCast]
    ring
  have hgn := core Y q N l (fun b => ((‖φ₀ b‖ : ℝ) : ℂ)) ((‖α‖ : ℝ) : ℂ) ((‖X‖ : ℝ) : ℂ) _ hq
    (by exact_mod_cast norm_ne_zero_iff.mpr hα) (hXn ▸ hy1) (by rw [hXn, hαn]; exact hyα)
    (by rw [hXn, hαn]; exact hyα') hZn.hasSum
  have hfibn : ∀ ab : ℤ × Y, HasSum (fun c => ((‖X‖ : ℝ) : ℂ) ^ ℓ ab.1 ab.2 c *
      (((‖α‖ : ℝ) : ℂ) ^ ab.1 * (q : ℂ) ^ (-ab.1 * ((N : ℤ) + 1)) * ((‖φ₀ ab.2‖ : ℝ) : ℂ)))
      (((q : ℂ) ^ (2 * l ab.2 + (2 * N + 2) * ab.1.toNat) * ((‖X‖ : ℝ) : ℂ) ^ (ab.1.natAbs + l ab.2) *
        jFac q N ((‖X‖ : ℝ) : ℂ)) *
        (((‖α‖ : ℝ) : ℂ) ^ ab.1 * (q : ℂ) ^ (-ab.1 * ((N : ℤ) + 1)) * ((‖φ₀ ab.2‖ : ℝ) : ℂ))) :=
    fun ab => (H _ (hXn ▸ hy1) ab.1 ab.2).mul_right _
  have hnorm : ∀ p : (ℤ × Y) × C,
      ((‖X ^ ℓ p.1.1 p.1.2 p.2 * (α ^ p.1.1 * (q : ℂ) ^ (-p.1.1 * ((N : ℤ) + 1)) * φ₀ p.1.2)‖ : ℝ) : ℂ) =
      ((‖X‖ : ℝ) : ℂ) ^ ℓ p.1.1 p.1.2 p.2 *
        (((‖α‖ : ℝ) : ℂ) ^ p.1.1 * (q : ℂ) ^ (-p.1.1 * ((N : ℤ) + 1)) * ((‖φ₀ p.1.2‖ : ℝ) : ℂ)) := by
    intro p
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_zpow, norm_zpow, Complex.norm_natCast]
    push_cast
    rfl
  have hsum : Summable (fun p : (ℤ × Y) × C =>
      X ^ ℓ p.1.1 p.1.2 p.2 * (α ^ p.1.1 * (q : ℂ) ^ (-p.1.1 * ((N : ℤ) + 1)) * φ₀ p.1.2)) := by
    rw [← summable_norm_iff, summable_prod_of_nonneg (fun _ => norm_nonneg _)]
    refine ⟨fun ab => ?_, ?_⟩
    · rw [← Complex.summable_ofReal]
      exact (funext fun c => (hnorm (ab, c)).symm) ▸ (hfibn ab).summable
    · rw [← Complex.summable_ofReal]
      refine hgn.summable.congr fun ab => ?_
      rw [Complex.ofReal_tsum]
      exact ((funext fun c => (hnorm (ab, c)).symm) ▸ (hfibn ab)).tsum_eq.symm
  rw [hg.unique (hsum.hasSum.prod_fiberwise hfib)]
  exact hsum.hasSum

end GlobalTheory.InertZeta
