import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory

/- English proof (translation)
Introduce `p _ G β y y₀ c hyc`. Use `haveI : Module.Finite ℚ G.C := Module.Finite.trans G.F G.C`. Use `haveI : Nontrivial G.C := inferInstance`. Use `set d : G.C → ℚ := fun a => LinearMap.det (LinearMap.mulLeft ℚ a) with hd`. Establish `dmul : ∀ a b, d (a * b) = d a * d b`.

Introduce `a b`. Simplify using `only [hd, LinearMap.mulLeft_mul, LinearMap.det_comp]`. Establish `done : d 1 = 1` using `by simp [hd, LinearMap.mulLeft_one]`. Establish `dsc : ∀ s : ℚ, d (algebraMap ℚ G.C s) = s ^ Module.finrank ℚ G.C`. Introduce `s`.

Establish `: LinearMap.mulLeft ℚ (algebraMap ℚ G.C s) = s • LinearMap.id`. Use extensionality with `x`. Simplify using `[Algebra.smul_def]`. Simplify using `only [hd, this, LinearMap.det_smul, LinearMap.det_id, mul_one]`. Establish `dunit : ∀ u : G.Cˣ, d (u : G.C) * d ((u⁻¹ : G.Cˣ) : G.C) = 1`.

Introduce `u`. Rewrite using `[← dmul, Units.mul_inv, done]`. Establish `shmul : ∀ a b : G.C, sh G (a * b) = sh G b * sh G a`. Introduce `a b`. Simplify using `only [sh, map_mul, MulOpposite.unop_mul]`.

Establish `shone : sh G 1 = 1` using `by simp [sh]`. Establish `dsh_conj : d (sh G (c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C))) = d (sh G (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))`. Establish `e : d (sh G ((c⁻¹ : G.Cˣ) : G.C)) * d (sh G (c : G.C)) = 1`. Rewrite using `[← dmul, ← shmul, Units.mul_inv, shone, done]`. Rewrite using `[shmul, shmul, dmul, dmul]`.

Combine the equalities or inequalities in the displayed calculation. Establish `d_conj : d (c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C)) = d (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)`. Rewrite using `[dmul, dmul]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨hy, hs⟩` from `y.2`.

Take `⟨hy₀, hs₀⟩` from `y₀.2`. Establish `ey` using `congrArg d hy`. Establish `ey₀` using `congrArg d hy₀`. Rewrite `ey`, `ey₀` using `[dmul, dmul, dmul, dsc]`. Rewrite `ey` using `[hyc, d_conj, dsh_conj, ey₀]`.

Establish `hβ : d (β : G.C) ≠ 0`. Introduce `h`. Use `dunit β` as an intermediate fact. Rewrite `this` using `[h, zero_mul]`. Conclude with `zero_ne_one this`.

Establish `hN : Module.finrank ℚ G.C ≠ 0` using `Module.finrank_pos.ne'`. Establish `hpow : ((y : G.Cˣ × ℚˣ).2 : ℚ) ^ Module.finrank ℚ G.C = ((y₀ : G.Cˣ × ℚˣ).2 : ℚ) ^ Module.finrank ℚ G.C` using `(mul_right_cancel₀ hβ ey).symm`. Conclude with `Units.ext ((pow_left_inj₀ hs.le hs₀.le hN).1 hpow)`.
-/
theorem grp_factor_eq_of_conj : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (y y₀ : grp G β) (c : G.Cˣ),
    (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C) →
    (y : G.Cˣ × ℚˣ).2 = (y₀ : G.Cˣ × ℚˣ).2 := by
  intro p _ G β y y₀ c hyc
  haveI : Module.Finite ℚ G.C := Module.Finite.trans G.F G.C
  haveI : Nontrivial G.C := inferInstance
  set d : G.C → ℚ := fun a => LinearMap.det (LinearMap.mulLeft ℚ a) with hd
  have dmul : ∀ a b, d (a * b) = d a * d b := by
    intro a b; simp only [hd, LinearMap.mulLeft_mul, LinearMap.det_comp]
  have done : d 1 = 1 := by simp [hd, LinearMap.mulLeft_one]
  have dsc : ∀ s : ℚ, d (algebraMap ℚ G.C s) = s ^ Module.finrank ℚ G.C := by
    intro s
    have : LinearMap.mulLeft ℚ (algebraMap ℚ G.C s) = s • LinearMap.id := by
      ext x; simp [Algebra.smul_def]
    simp only [hd, this, LinearMap.det_smul, LinearMap.det_id, mul_one]
  have dunit : ∀ u : G.Cˣ, d (u : G.C) * d ((u⁻¹ : G.Cˣ) : G.C) = 1 := by
    intro u; rw [← dmul, Units.mul_inv, done]
  have shmul : ∀ a b : G.C, sh G (a * b) = sh G b * sh G a := by
    intro a b; simp only [sh, map_mul, MulOpposite.unop_mul]
  have shone : sh G 1 = 1 := by simp [sh]
  have dsh_conj : d (sh G (c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C))) =
      d (sh G (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) := by
    have e : d (sh G ((c⁻¹ : G.Cˣ) : G.C)) * d (sh G (c : G.C)) = 1 := by
      rw [← dmul, ← shmul, Units.mul_inv, shone, done]
    rw [shmul, shmul, dmul, dmul]
    calc d (sh G ((c⁻¹ : G.Cˣ) : G.C)) * (d (sh G (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) * d (sh G (c : G.C)))
        = d (sh G (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) *
          (d (sh G ((c⁻¹ : G.Cˣ) : G.C)) * d (sh G (c : G.C))) := by ring
      _ = _ := by rw [e, mul_one]
  have d_conj : d (c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C)) =
      d (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) := by
    rw [dmul, dmul]
    calc d (c : G.C) * d (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * d ((c⁻¹ : G.Cˣ) : G.C)
        = d (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * (d (c : G.C) * d ((c⁻¹ : G.Cˣ) : G.C)) := by ring
      _ = _ := by rw [dunit, mul_one]
  obtain ⟨hy, hs⟩ := y.2
  obtain ⟨hy₀, hs₀⟩ := y₀.2
  have ey := congrArg d hy
  have ey₀ := congrArg d hy₀
  rw [dmul, dmul, dmul, dsc] at ey ey₀
  rw [hyc, d_conj, dsh_conj, ey₀] at ey
  have hβ : d (β : G.C) ≠ 0 := by
    intro h; have := dunit β; rw [h, zero_mul] at this; exact zero_ne_one this
  have hN : Module.finrank ℚ G.C ≠ 0 := Module.finrank_pos.ne'
  have hpow : ((y : G.Cˣ × ℚˣ).2 : ℚ) ^ Module.finrank ℚ G.C = ((y₀ : G.Cˣ × ℚˣ).2 : ℚ) ^ Module.finrank ℚ G.C :=
    (mul_right_cancel₀ hβ ey).symm
  exact Units.ext ((pow_left_inj₀ hs.le hs₀.le hN).1 hpow)

end GlobalTheory
