import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatConj

section Ring

variable {A : Type} [CommRing A] (δ : A → A)
  (hadd : ∀ x y, δ (x + y) = δ x + δ y) (hmul : ∀ x y, δ (x * y) = x * δ y + y * δ x)
include hadd hmul

/- English proof (translation)
Establish `h0 : δ 0 = 0`. Use `hadd 0 0` as an intermediate fact. Simplify using `only [add_zero] at this`. Take the linear combination `-this`. Establish `h1 : δ 1 = 0`.

Use `hmul 1 1` as an intermediate fact. Rewrite `this` using `[_root_.one_mul]`. Take the linear combination `-this`. Proceed by induction on `k with`. Consider the case `zero => simpa using h0`.

Consider the case `succ k ih => rw [Nat.cast_succ, hadd, ih, h1, add_zero]`.
-/
theorem der_natCast (k : ℕ) : δ (k : A) = 0 := by
  have h0 : δ 0 = 0 := by
    have := hadd 0 0
    simp only [add_zero] at this
    linear_combination -this
  have h1 : δ 1 = 0 := by
    have := hmul 1 1
    rw [_root_.one_mul] at this
    linear_combination -this
  induction k with
  | zero => simpa using h0
  | succ k ih => rw [Nat.cast_succ, hadd, ih, h1, add_zero]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Use `hmul 1 1` as an intermediate fact. Rewrite `this` using `[_root_.one_mul]`. Simplify using `only [pow_zero, Nat.cast_zero, zero_mul]`.

Take the linear combination `-this`. Consider the case `succ k ih`. Rewrite using `[pow_succ, hmul, ih]`. Use `push_cast`. Take the linear combination `-(δ g * g ^ k) * hg`.
-/
theorem der_pow (g g' : A) (hg : g * g' = 1) (k : ℕ) : δ (g ^ k) = (k : A) * g ^ k * (δ g * g') := by
  induction k with
  | zero =>
    have := hmul 1 1
    rw [_root_.one_mul] at this
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    linear_combination -this
  | succ k ih =>
    rw [pow_succ, hmul, ih]
    push_cast
    linear_combination -(δ g * g ^ k) * hg

/- English proof (translation)
Rewrite using `[hmul, der_pow δ hadd hmul g g' hg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem der_pow_mul (g g' : A) (hg : g * g' = 1) (k : ℕ) (f : A) :
    δ (g ^ k * f) = g ^ k * (δ f + (k : A) * (δ g * g') * f) := by
  rw [hmul, der_pow δ hadd hmul g g' hg]
  ring

/- English proof (translation)
Rewrite using `[hmul, der_natCast δ hadd hmul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem der_natCast_mul (k : ℕ) (x : A) : δ ((k : A) * x) = (k : A) * δ x := by
  rw [hmul, der_natCast δ hadd hmul]
  ring

end Ring

end GlobalTheory.HeatConj

namespace GlobalTheory.HeatConj

/- English proof (translation)
Introduce `R _ G _ _ n dd Θ hΘ u d W₀ Wp Wo p p' k g g' hg hWo hd hdd f`. Establish `E3` using `der_pow_mul (d Wo) (hd.1 Wo hWo) (hd.2.1 Wo hWo) g g' hg k f`. Establish `E2 : ∀ a, dd a Wo (g ^ k * f) = g ^ k * (dd a Wo f + (k : Γ(G.left, Wo)) * (dd a Wo g * g') * f)` using `fun a => der_pow_mul (dd a Wo) ((hdd a).1 Wo hWo) ((hdd a).2.1 Wo hWo) g g' hg k f`. Establish `E1 : ∀ a b, dd a Wo (dd b Wo (g ^ k * f)) = g ^ k * (dd a Wo (dd b Wo f) + (k : Γ(G.left, Wo)) * (dd b Wo g * g') * dd a Wo f + (k : Γ(G.left, Wo)) * (dd a Wo g * g') * dd b Wo f + (k : Γ(G.left, Wo)) * dd a Wo (dd b Wo g * g') * f + (k : Γ(G.left, Wo)) ^ 2 * (dd a Wo g * g') * ( …`. Introduce `a b`.

Establish `ha` using `(hdd a).1 Wo hWo`. Establish `hm` using `(hdd a).2.1 Wo hWo`. Rewrite using `[E2 b, der_pow_mul (dd a Wo) ha hm g g' hg k, ha, mul_assoc (k : Γ(G.left, Wo)), der_natCast_mul (dd a Wo) ha hm, hm]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsym : ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd a Wo g * g') * dd b Wo f = ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd b Wo g * g') * dd a Wo f`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Establish `: Θ b a = Θ a b`. Use `congrFun (congrFun hΘ a) b` as an intermediate fact. Simplify `this` using `[Matrix.transpose_apply]`.

Rewrite using `[this]`. Establish `hS : ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * dd a Wo (dd b Wo (g ^ k * f)) = g ^ k * ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * dd a Wo (dd b Wo f) + ((k : Γ(G.left, Wo)) * g ^ k) * ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd b Wo g * g') * dd a Wo f + ((k : Γ(G.left, Wo)) * g ^ k) * ∑ a, ∑ …`. Simplify using `only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[E1]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hU : ∑ a, constFn G.hom Wo (u a) * dd a Wo (g ^ k * f) = g ^ k * ∑ a, constFn G.hom Wo (u a) * dd a Wo f + ((k : Γ(G.left, Wo)) * g ^ k) * (∑ a, constFn G.hom Wo (u a) * (dd a Wo g * g')) * f`. Simplify using `only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[E2]`.

Expand and normalize the polynomial expressions, which then agree. Unfold `op`. Rewrite using `[E3]`. Take the linear combination `-hS + 2 * hU - ((k : Γ(G.left, Wo)) * g ^ k) * hsym`.
-/
theorem op_pow_mul : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (dd : Fin n → Fld G.left) (Θ : Matrix (Fin n) (Fin n) R), Θᵀ = Θ → ∀ (u : Fin n → R) (d : Fld G.left) (W₀ Wp Wo : G.left.Opens) (p p' : Γ(G.left, Wp)) (k : ℕ) (g g' : Γ(G.left, Wo)), g * g' = 1 → Wo ≤ W₀ → IsField W₀ d → (∀ a, IsField W₀ (dd a)) → ∀ f, op G dd Θ u d p p' k Wo (g ^ k * f) = g ^ k * (op G dd Θ u d p p' k Wo f - 2 * (k : Γ(G.left, Wo)) * ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd b Wo g * g') * dd a Wo f + ((k : Γ(G.left, Wo)) ^ 2 * (2 * (d Wo g * g') - ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd a Wo g * g') * (dd b Wo g * g')) + (k : Γ(G.left, Wo)) * (2 * ∑ a, constFn G.hom Wo (u a) * (dd a Wo g * g') - ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * dd a Wo (dd b Wo g * g'))) * f) := by
  intro R _ G _ _ n dd Θ hΘ u d W₀ Wp Wo p p' k g g' hg hWo hd hdd f
  have E3 := der_pow_mul (d Wo) (hd.1 Wo hWo) (hd.2.1 Wo hWo) g g' hg k f
  have E2 : ∀ a, dd a Wo (g ^ k * f) = g ^ k * (dd a Wo f + (k : Γ(G.left, Wo)) * (dd a Wo g * g') * f) :=
    fun a => der_pow_mul (dd a Wo) ((hdd a).1 Wo hWo) ((hdd a).2.1 Wo hWo) g g' hg k f
  have E1 : ∀ a b, dd a Wo (dd b Wo (g ^ k * f)) = g ^ k * (dd a Wo (dd b Wo f) +
      (k : Γ(G.left, Wo)) * (dd b Wo g * g') * dd a Wo f + (k : Γ(G.left, Wo)) * (dd a Wo g * g') * dd b Wo f +
      (k : Γ(G.left, Wo)) * dd a Wo (dd b Wo g * g') * f +
      (k : Γ(G.left, Wo)) ^ 2 * (dd a Wo g * g') * (dd b Wo g * g') * f) := by
    intro a b
    have ha := (hdd a).1 Wo hWo
    have hm := (hdd a).2.1 Wo hWo
    rw [E2 b, der_pow_mul (dd a Wo) ha hm g g' hg k, ha, mul_assoc (k : Γ(G.left, Wo)),
      der_natCast_mul (dd a Wo) ha hm, hm]
    ring
  have hsym : ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd a Wo g * g') * dd b Wo f =
      ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd b Wo g * g') * dd a Wo f := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have : Θ b a = Θ a b := by
      have := congrFun (congrFun hΘ a) b
      simpa [Matrix.transpose_apply] using this
    rw [this]
  have hS : ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * dd a Wo (dd b Wo (g ^ k * f)) =
      g ^ k * ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * dd a Wo (dd b Wo f) +
      ((k : Γ(G.left, Wo)) * g ^ k) * ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd b Wo g * g') * dd a Wo f +
      ((k : Γ(G.left, Wo)) * g ^ k) * ∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd a Wo g * g') * dd b Wo f +
      ((k : Γ(G.left, Wo)) * g ^ k) * (∑ a, ∑ b, constFn G.hom Wo (Θ a b) * dd a Wo (dd b Wo g * g')) * f +
      ((k : Γ(G.left, Wo)) ^ 2 * g ^ k) *
        (∑ a, ∑ b, constFn G.hom Wo (Θ a b) * (dd a Wo g * g') * (dd b Wo g * g')) * f := by
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [E1]
    ring
  have hU : ∑ a, constFn G.hom Wo (u a) * dd a Wo (g ^ k * f) =
      g ^ k * ∑ a, constFn G.hom Wo (u a) * dd a Wo f +
      ((k : Γ(G.left, Wo)) * g ^ k) * (∑ a, constFn G.hom Wo (u a) * (dd a Wo g * g')) * f := by
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [E2]
    ring
  unfold op
  rw [E3]
  linear_combination -hS + 2 * hU - ((k : Γ(G.left, Wo)) * g ^ k) * hsym

end GlobalTheory.HeatConj
