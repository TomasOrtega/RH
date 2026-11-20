import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TraceDefinitePairsEqAutomorphicTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutantOfMaximalDegreeElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentraliserInvolution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatePairRelated
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CentSim

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Use `set y : G.Cˣ := γ with hydef`. Use `set c : G.C := algebraMap ℚ G.C c₀`. Use `set Y := sh G (y : G.C)`. Use `set Yi := sh G ((y⁻¹ : G.Cˣ) : G.C)`. Establish `hYYi : Y * Yi = 1`.

Simplify using `only [Y, Yi, ← GlobalTheory.CentConj.sh_mul', Units.inv_mul, GlobalTheory.CentConj.sh_one']`. Establish `hzi : Commute z ((y⁻¹ : G.Cˣ) : G.C)` using `hz.units_inv_right`. Establish `hcomm : Yi * sh G z = sh G z * Yi`. Simplify using `only [Yi, ← GlobalTheory.CentConj.sh_mul']`. Rewrite using `[hzi.eq]`.

Establish `hcc : ∀ w : G.C, c * w = w * c` using `fun w => Algebra.commutes _ w`. Establish `h1 : (y : G.C) * β = c * β * Yi`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : ((β⁻¹ : G.Cˣ) : G.C) * y = c * Yi * ((β⁻¹ : G.Cˣ) : G.C)`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [mul_assoc, Units.mul_inv, mul_one]`. Use `_ = c * Yi * ((β⁻¹ : G.Cˣ) : G.C) := by`. Rewrite using `[h1, ← mul_assoc, ← mul_assoc, ← hcc, mul_assoc c, Units.inv_mul, mul_one]`. Express the relevant statement in the definitionally equal form `(β : G.C) * sh G z * ((β⁻¹ : G.Cˣ) : G.C) * y = y * ((β : G.C) * sh G z * ((β⁻¹ : G.Cˣ) : G.C))`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[h2]`. Simplify using `only [mul_assoc]`. Rewrite using `[← mul_assoc (sh G z) c, ← hcc (sh G z), mul_assoc c, ← mul_assoc (β : G.C) c, ← hcc (β : G.C)]`. Simplify using `only [mul_assoc]`. Use `_ = c * (β * (Yi * sh G z)) * ((β⁻¹ : G.Cˣ) : G.C) := by rw [hcomm]`.

Use `_ = (y : G.C) * β * sh G z * ((β⁻¹ : G.Cˣ) : G.C) := by rw [h1]; simp only [mul_assoc]`. Use `_ = _ := by simp only [mul_assoc]`.
-/
theorem commute_conj_sh_sim (G : HTGroup p) (β γ : G.Cˣ) (c₀ : ℚ)
    (h : (γ : G.C) * β * sh G γ = algebraMap ℚ G.C c₀ * β) (z : G.C) (hz : Commute z (γ : G.C)) :
    Commute ((β : G.C) * sh G z * ((β⁻¹ : G.Cˣ) : G.C)) (γ : G.C) := by
  set y : G.Cˣ := γ with hydef
  set c : G.C := algebraMap ℚ G.C c₀
  set Y := sh G (y : G.C)
  set Yi := sh G ((y⁻¹ : G.Cˣ) : G.C)
  have hYYi : Y * Yi = 1 := by
    simp only [Y, Yi, ← GlobalTheory.CentConj.sh_mul', Units.inv_mul, GlobalTheory.CentConj.sh_one']
  have hzi : Commute z ((y⁻¹ : G.Cˣ) : G.C) := hz.units_inv_right
  have hcomm : Yi * sh G z = sh G z * Yi := by
    simp only [Yi, ← GlobalTheory.CentConj.sh_mul']; rw [hzi.eq]
  have hcc : ∀ w : G.C, c * w = w * c := fun w => Algebra.commutes _ w
  have h1 : (y : G.C) * β = c * β * Yi := by
    calc (y : G.C) * β = (y : G.C) * β * (Y * Yi) := by rw [hYYi, mul_one]
      _ = c * β * Yi := by rw [← mul_assoc, h]
  have h2 : ((β⁻¹ : G.Cˣ) : G.C) * y = c * Yi * ((β⁻¹ : G.Cˣ) : G.C) := by
    calc ((β⁻¹ : G.Cˣ) : G.C) * y = ((β⁻¹ : G.Cˣ) : G.C) * ((y : G.C) * β) * ((β⁻¹ : G.Cˣ) : G.C) := by
          simp only [mul_assoc, Units.mul_inv, mul_one]
      _ = c * Yi * ((β⁻¹ : G.Cˣ) : G.C) := by
          rw [h1, ← mul_assoc, ← mul_assoc, ← hcc, mul_assoc c, Units.inv_mul, mul_one]
  change (β : G.C) * sh G z * ((β⁻¹ : G.Cˣ) : G.C) * y = y * ((β : G.C) * sh G z * ((β⁻¹ : G.Cˣ) : G.C))
  calc (β : G.C) * sh G z * ((β⁻¹ : G.Cˣ) : G.C) * y
        = (β : G.C) * sh G z * (((β⁻¹ : G.Cˣ) : G.C) * y) := by rw [mul_assoc]
    _ = c * (β * (sh G z * Yi)) * ((β⁻¹ : G.Cˣ) : G.C) := by
        rw [h2]; simp only [mul_assoc]
        rw [← mul_assoc (sh G z) c, ← hcc (sh G z), mul_assoc c, ← mul_assoc (β : G.C) c, ← hcc (β : G.C)]
        simp only [mul_assoc]
    _ = c * (β * (Yi * sh G z)) * ((β⁻¹ : G.Cˣ) : G.C) := by rw [hcomm]
    _ = (y : G.C) * β * sh G z * ((β⁻¹ : G.Cˣ) : G.C) := by rw [h1]; simp only [mul_assoc]
    _ = _ := by simp only [mul_assoc]

/- English proof (translation)
Introduce `p _ G β γ c₀ hβ hsim hirr hdeg`. Take `⟨E, _, _, _, j, hj, hcent⟩` from `GlobalTheory.CentIrr.centralizer_unit_eq_field p G γ hirr hdeg`. Use `set w : E → G.C := fun e => (β : G.C) * sh G (j e) * ((β⁻¹ : G.Cˣ) : G.C) with hw`. Establish `hex : ∀ e, ∃ e', j e' = w e` using `fun e => (hcent _).1 (commute_conj_sh_sim G β γ (c₀ : ℚ) hsim (j e) ((hcent _).2 ⟨e, rfl⟩))`. Use `choose t ht using hex`.

Establish `tt : ∀ e, t (t e) = e`. Introduce `e`. Apply `hj` to reduce the goal to its premises. Rewrite using `[ht, hw]`. Simplify using `only`.

Rewrite using `[ht, GlobalTheory.CentConj.sh_mul', GlobalTheory.CentConj.sh_mul', GlobalTheory.CentConj.sh_sh', hβ, GlobalTheory.CentConj.sh_inv_of_sym G β hβ]`. Simplify using `only [mul_assoc, Units.mul_inv, mul_one]`. Rewrite using `[← mul_assoc, Units.mul_inv, one_mul]`. Establish `hm : ∀ a b, t (a * b) = t a * t b`. Introduce `a b`.

Apply `hj` to reduce the goal to its premises. Rewrite using `[mul_comm a b, ht, map_mul, ht, ht, hw]`. Simplify using `only`. Rewrite using `[map_mul, GlobalTheory.CentConj.sh_mul']`. Simplify using `only [mul_assoc]`.

Rewrite using `[← mul_assoc ((β⁻¹ : G.Cˣ) : G.C) (β : G.C), Units.inv_mul, one_mul]`. Establish `ha : ∀ a b, t (a + b) = t a + t b`. Introduce `a b`. Apply `hj` to reduce the goal to its premises. Rewrite using `[ht, map_add, ht, ht, hw]`.

Simplify using `only`. Rewrite using `[map_add, GlobalTheory.CentConj.sh_add']`. Use `noncomm_ring`. Establish `h1 : t 1 = 1`. Apply `hj` to reduce the goal to its premises.

Rewrite using `[ht, hw]`. Simplify using `only`. Rewrite using `[map_one, GlobalTheory.CentConj.sh_one', mul_one, Units.mul_inv]`. Establish `h0 : t 0 = 0`. Establish `h` using `ha 0 0`.

Rewrite `h` using `[add_zero]`. Conclude with `left_eq_add.mp h`. Set `τ : E →+* E` to `{ toFun := t, map_one' := h1, map_mul' := hm, map_zero' := h0, map_add' := ha }`. Use `⟨E, inferInstance, inferInstance, j.toRingHom.toRatAlgHom, τ.toRatAlgHom, hj, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `z`.

Conclude with `hcent z`. Introduce `x`. Conclude with `ht x`. Introduce `x`. Conclude with `tt x`.
-/
theorem centraliser_field_involution : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β γ : G.Cˣ) (c₀ : ℚˣ), sh G β = β →
    (γ : G.C) * β * sh G γ = algebraMap ℚ G.C c₀ * β → Irreducible (minpoly G.F (γ : G.C)) →
    (minpoly G.F (γ : G.C)).natDegree = G.n →
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (ι : L →ₐ[ℚ] G.C) (c : L →ₐ[ℚ] L),
      Function.Injective ι ∧ (∀ z : G.C, z * γ = γ * z ↔ ∃ w, ι w = z) ∧
      (∀ x, ι (c x) = β * sh G (ι x) * ((β⁻¹ : G.Cˣ) : G.C)) ∧ ∀ x, c (c x) = x := by
  intro p _ G β γ c₀ hβ hsim hirr hdeg
  obtain ⟨E, _, _, _, j, hj, hcent⟩ := GlobalTheory.CentIrr.centralizer_unit_eq_field p G γ hirr hdeg
  set w : E → G.C := fun e => (β : G.C) * sh G (j e) * ((β⁻¹ : G.Cˣ) : G.C) with hw
  have hex : ∀ e, ∃ e', j e' = w e := fun e =>
    (hcent _).1 (commute_conj_sh_sim G β γ (c₀ : ℚ) hsim (j e) ((hcent _).2 ⟨e, rfl⟩))
  choose t ht using hex
  have tt : ∀ e, t (t e) = e := by
    intro e
    apply hj
    rw [ht, hw]; dsimp only
    rw [ht, GlobalTheory.CentConj.sh_mul', GlobalTheory.CentConj.sh_mul', GlobalTheory.CentConj.sh_sh', hβ,
      GlobalTheory.CentConj.sh_inv_of_sym G β hβ]
    simp only [mul_assoc, Units.mul_inv, mul_one]
    rw [← mul_assoc, Units.mul_inv, one_mul]
  have hm : ∀ a b, t (a * b) = t a * t b := by
    intro a b
    apply hj
    rw [mul_comm a b, ht, map_mul, ht, ht, hw]; dsimp only
    rw [map_mul, GlobalTheory.CentConj.sh_mul']
    simp only [mul_assoc]
    rw [← mul_assoc ((β⁻¹ : G.Cˣ) : G.C) (β : G.C), Units.inv_mul, one_mul]
  have ha : ∀ a b, t (a + b) = t a + t b := by
    intro a b
    apply hj
    rw [ht, map_add, ht, ht, hw]; dsimp only
    rw [map_add, GlobalTheory.CentConj.sh_add']; noncomm_ring
  have h1 : t 1 = 1 := by
    apply hj
    rw [ht, hw]; dsimp only
    rw [map_one, GlobalTheory.CentConj.sh_one', mul_one, Units.mul_inv]
  have h0 : t 0 = 0 := by
    have h := ha 0 0
    rw [add_zero] at h
    exact left_eq_add.mp h
  let τ : E →+* E := { toFun := t, map_one' := h1, map_mul' := hm, map_zero' := h0, map_add' := ha }
  refine ⟨E, inferInstance, inferInstance, j.toRingHom.toRatAlgHom, τ.toRatAlgHom, hj, ?_, ?_, ?_⟩
  · intro z
    exact hcent z
  · intro x; exact ht x
  · intro x; exact tt x

end GlobalTheory.CentSim

/- English proof (translation)
The claim follows from `GlobalTheory.CentSim.centraliser_field_involution`.
-/
example : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β γ : G.Cˣ) (c₀ : ℚˣ), sh G β = β →
    (γ : G.C) * β * sh G γ = algebraMap ℚ G.C c₀ * β → Irreducible (minpoly G.F (γ : G.C)) →
    (minpoly G.F (γ : G.C)).natDegree = G.n →
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (ι : L →ₐ[ℚ] G.C) (c : L →ₐ[ℚ] L),
      Function.Injective ι ∧ (∀ z : G.C, z * γ = γ * z ↔ ∃ w, ι w = z) ∧
      (∀ x, ι (c x) = β * sh G (ι x) * ((β⁻¹ : G.Cˣ) : G.C)) ∧ ∀ x, c (c x) = x :=
  GlobalTheory.CentSim.centraliser_field_involution
