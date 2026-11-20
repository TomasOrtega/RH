import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd

noncomputable section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold Real

namespace GlobalTheory.Hk

/- English proof (translation)
Establish `: (0 : ℝ) < p` using `by exact_mod_cast hp`. Rewrite using `[Complex.div_natCast_im]`. Simplify using `using div_pos hz this`.
-/
private theorem im_div_pos' {p : ℕ} (hp : 0 < p) {z : ℂ} (hz : 0 < z.im) (b : ℕ) :
    0 < ((z + b) / (p : ℂ)).im := by
  have : (0 : ℝ) < p := by exact_mod_cast hp
  rw [Complex.div_natCast_im]
  simpa using div_pos hz this

/- English proof (translation)
Establish `hζ` using `Complex.isPrimitiveRoot_exp p hp.ne'`. Use `set ζ := Complex.exp (2 * π * Complex.I / p)`. Repeatedly rewrite using `[← pow_mul, fun b => mul_comm b m, pow_mul]`. Use `split_ifs with h`. Rewrite using `[(hζ.pow_eq_one_iff_dvd m).2 h]`.

Simplify using the standard rewrite rules. Establish `h1 : ζ ^ m ≠ 1` using `fun e => h ((hζ.pow_eq_one_iff_dvd m).1 e)`. Rewrite using `[geom_sum_eq h1, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one]`. Simplify using the standard rewrite rules.
-/
private theorem sum_root' {p : ℕ} (hp : 0 < p) (m : ℕ) :
    ∑ b ∈ Finset.range p, (Complex.exp (2 * π * Complex.I / p) ^ b) ^ m =
      if p ∣ m then (p : ℂ) else 0 := by
  have hζ := Complex.isPrimitiveRoot_exp p hp.ne'
  set ζ := Complex.exp (2 * π * Complex.I / p)
  simp_rw [← pow_mul, fun b => mul_comm b m, pow_mul]
  split_ifs with h
  · rw [(hζ.pow_eq_one_iff_dvd m).2 h]; simp
  · have h1 : ζ ^ m ≠ 1 := fun e => h ((hζ.pow_eq_one_iff_dvd m).1 e)
    rw [geom_sum_eq h1, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one]; simp

/- English proof (translation)
Establish `hp0 : (q : ℂ) ≠ 0` using `by exact_mod_cast hq0.ne'`. Establish `hinj : Function.Injective fun m : ℕ => q * m` using `mul_right_injective₀ hq0.ne'`. Establish `hrange : ∀ n, n ∉ Set.range (fun m : ℕ => q * m) → ¬ q ∣ n` using `fun n hn ⟨m, hm⟩ => hn ⟨m, hm.symm⟩`. Use `set Q := Function.Periodic.qParam 1 τ with hQ`. Use `set x := Complex.exp (2 * π * Complex.I * τ / q) with hx`.

Establish `hxq : x ^ q = Q`. Rewrite using `[hx, ← Complex.exp_nat_mul, hQ, Function.Periodic.qParam]`. Use `congr 1`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Establish `hB : ∀ b : ℕ, HasSum (fun m => a m * x ^ m * (Complex.exp (2 * π * Complex.I / q) ^ b) ^ m) (f (ofComplex (((τ : ℂ) + b) / q)))` using `fun b => by`. Establish `h` using `hf (ofComplex (((τ : ℂ) + b) / q))`. Rewrite `h`, the goal using `[ofComplex_apply_of_im_pos (im_div_pos' hq0 τ.2 b)]`. Use `h using 2 with m` and compare the differences between its conclusion and the goal. Establish `e : Function.Periodic.qParam 1 (((τ : ℂ) + b) / q) = x * Complex.exp (2 * π * Complex.I / q) ^ b`.

Rewrite using `[hx, Function.Periodic.qParam, ← Complex.exp_nat_mul, ← Complex.exp_add]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[e, mul_pow, mul_assoc]`.

Establish `hC` using `hasSum_sum (s := Finset.range q) fun b _ => hB b`. Rewrite `hC` using `[← Finset.mul_sum, sum_root' hq0]`. Rewrite `hC` using `[← hinj.hasSum_iff fun n hn => by simp [hrange n hn]]`. Establish `hD` using `hC.mul_left (q : ℂ)⁻¹`. Use `cast (congrArg (HasSum · (uOp q f τ)) (funext fun n => ?_)) hD` and prove the remaining obligations.

Simplify using `only [Function.comp, dvd_mul_right, if_true, pow_mul, hxq, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem hasSum_uOp (q : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ) (hq0 : 0 < q)
    (hf : ∀ τ : ℍ, HasSum (fun m => a m • Function.Periodic.qParam 1 τ ^ m) (f τ)) (τ : ℍ) :
    HasSum (fun m => a (q * m) • Function.Periodic.qParam 1 τ ^ m) (uOp q f τ) := by
  have hp0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  have hinj : Function.Injective fun m : ℕ => q * m := mul_right_injective₀ hq0.ne'
  have hrange : ∀ n, n ∉ Set.range (fun m : ℕ => q * m) → ¬ q ∣ n :=
    fun n hn ⟨m, hm⟩ => hn ⟨m, hm.symm⟩
  set Q := Function.Periodic.qParam 1 τ with hQ
  set x := Complex.exp (2 * π * Complex.I * τ / q) with hx
  have hxq : x ^ q = Q := by
    rw [hx, ← Complex.exp_nat_mul, hQ, Function.Periodic.qParam]; congr 1; push_cast; field_simp
  have hB : ∀ b : ℕ, HasSum (fun m => a m * x ^ m * (Complex.exp (2 * π * Complex.I / q) ^ b) ^ m)
      (f (ofComplex (((τ : ℂ) + b) / q))) := fun b => by
    have h := hf (ofComplex (((τ : ℂ) + b) / q))
    rw [ofComplex_apply_of_im_pos (im_div_pos' hq0 τ.2 b)] at h ⊢
    convert h using 2 with m
    have e : Function.Periodic.qParam 1 (((τ : ℂ) + b) / q) =
        x * Complex.exp (2 * π * Complex.I / q) ^ b := by
      rw [hx, Function.Periodic.qParam, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1; push_cast; ring
    simp [e, mul_pow, mul_assoc]
  have hC := hasSum_sum (s := Finset.range q) fun b _ => hB b
  simp_rw [← Finset.mul_sum, sum_root' hq0] at hC
  rw [← hinj.hasSum_iff fun n hn => by simp [hrange n hn]] at hC
  have hD := hC.mul_left (q : ℂ)⁻¹
  refine cast (congrArg (HasSum · (uOp q f τ)) (funext fun n => ?_)) hD
  simp only [Function.comp, dvd_mul_right, if_true, pow_mul, hxq, smul_eq_mul]
  field_simp

end GlobalTheory.Hk
