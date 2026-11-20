import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FieldCase

open Polynomial

namespace GlobalTheory

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.FieldCaseReduction.main`. Consider the case `exact _root_.GlobalTheory.FieldCaseReduction.main`. Consider the case `(apply _root_.GlobalTheory.FieldCaseReduction.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.FieldCaseReduction.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.FieldCaseReduction.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.FieldCaseReduction.main ..)`.
-/
theorem binQuad_represents_unit_of_finite_reduced (S : Type) [CommRing S] [Finite S]
    [IsReduced S] (t m f : S) (hd : IsUnit (t ^ 2 - 4 * m)) (hf : IsUnit f) :
    ∃ a b : S, a ^ 2 + t * a * b + m * b ^ 2 = f := by
  first
  | exact @_root_.GlobalTheory.FieldCaseReduction.main
  | exact _root_.GlobalTheory.FieldCaseReduction.main
  | (apply _root_.GlobalTheory.FieldCaseReduction.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.FieldCaseReduction.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FieldCaseReduction.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FieldCaseReduction.main ..)

/- English proof (translation)
Introduce `R _ _ _ τ hτ θ hθ f hf hτf`. Set `A : Subring R` to `τ.eqLocus (RingHom.id R)`. Establish `memA : ∀ x, τ x = x → x ∈ A` using `fun x hx => show τ x = RingHom.id R x from hx`. Establish `fixA : ∀ x : A, τ (x : R) = x` using `fun x => x.2`. Take `⟨u, hu⟩` from `hθ`.

Establish `h4 : ((4 : A) : R) = 4` using `map_ofNat A.subtype 4`. Establish `hτd : τ (θ - τ θ) = -(θ - τ θ)` using `by rw [map_sub, hτ]; ring`. Establish `hτdi : τ (↑u⁻¹ : R) = -↑u⁻¹`. Establish `h1 : τ (↑u⁻¹ : R) * (θ - τ θ) = -1`. Use `congrArg τ u.inv_mul` as an intermediate fact.

Rewrite `this` using `[map_mul, map_one, hu, hτd]`. Take the linear combination `-this`. Combine the equalities or inequalities in the displayed calculation. Take `⟨v, hv⟩` from `hf`. Establish `hτfi : τ (↑v⁻¹ : R) = ↑v⁻¹`.

Establish `h1 : τ (↑v⁻¹ : R) * f = 1`. Rewrite using `[← hτf, ← map_mul, ← hv, v.inv_mul, map_one]`. Combine the equalities or inequalities in the displayed calculation. Set `tA : A` to `⟨θ + τ θ, memA _ (by rw [map_add, hτ, add_comm])⟩`. Set `mA : A` to `⟨θ * τ θ, memA _ (by rw [map_mul, hτ, mul_comm])⟩`.

Set `fA : A` to `⟨f, memA _ hτf⟩`. Set `wA : A` to `⟨↑u⁻¹ * ↑u⁻¹, memA _ (by rw [map_mul, hτdi]; ring)⟩`. Set `vA : A` to `⟨↑v⁻¹, memA _ hτfi⟩`. Establish `hdisc : IsUnit (tA ^ 2 - 4 * mA)`. It suffices to establish `h : (tA ^ 2 - 4 * mA) * wA = 1 from ⟨⟨_, wA, h, by rw [mul_comm]; exact h⟩, rfl⟩`.

Use `Subtype.ext ?_` and prove the remaining obligations. Establish `e1 : (θ + τ θ) ^ 2 - 4 * (θ * τ θ) = ↑u * ↑u` using `by rw [hu]; ring`. Move the coercions through the operations in `[tA, mA, wA]`. Rewrite using `[h4, e1, show (↑u : R) * ↑u * (↑u⁻¹ * ↑u⁻¹) = (↑u * ↑u⁻¹) * (↑u * ↑u⁻¹) by ring, u.mul_inv, one_mul]`. Establish `hfA : IsUnit fA`.

It suffices to establish `h : fA * vA = 1 from ⟨⟨_, vA, h, by rw [mul_comm]; exact h⟩, rfl⟩`. Use `Subtype.ext ?_` and prove the remaining obligations. Move the coercions through the operations in `[fA, vA]`. Rewrite using `[← hv, v.mul_inv]`. Use `haveI : IsReduced A := ⟨fun x hx => Subtype.ext (IsNilpotent.eq_zero (hx.map A.subtype))⟩`.

Take `⟨a, b, hab⟩` from `binQuad_represents_unit_of_finite_reduced A tA mA fA hdisc hfA`. Establish `hab'` using `congrArg Subtype.val hab`. Move the coercions through the operations in `[tA, mA, fA] at hab'`. Use `⟨(a : R) + θ * b, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_mul, fixA a, fixA b]`.

Take the linear combination `hab'`.
-/
theorem norm_surj_of_finite_reduced_involution : ∀ (R : Type) [CommRing R] [Finite R]
    [IsReduced R] (τ : R →+* R), (∀ x, τ (τ x) = x) → ∀ θ : R, IsUnit (θ - τ θ) →
    ∀ f : R, IsUnit f → τ f = f → ∃ c : R, τ c * c = f := by
  intro R _ _ _ τ hτ θ hθ f hf hτf
  classical
  let A : Subring R := τ.eqLocus (RingHom.id R)
  have memA : ∀ x, τ x = x → x ∈ A := fun x hx => show τ x = RingHom.id R x from hx
  have fixA : ∀ x : A, τ (x : R) = x := fun x => x.2
  obtain ⟨u, hu⟩ := hθ
  have h4 : ((4 : A) : R) = 4 := map_ofNat A.subtype 4
  have hτd : τ (θ - τ θ) = -(θ - τ θ) := by rw [map_sub, hτ]; ring
  have hτdi : τ (↑u⁻¹ : R) = -↑u⁻¹ := by
    have h1 : τ (↑u⁻¹ : R) * (θ - τ θ) = -1 := by
      have := congrArg τ u.inv_mul
      rw [map_mul, map_one, hu, hτd] at this
      linear_combination -this
    calc τ (↑u⁻¹ : R) = τ ↑u⁻¹ * ((θ - τ θ) * ↑u⁻¹) := by rw [← hu, u.mul_inv, mul_one]
      _ = -↑u⁻¹ := by rw [← mul_assoc, h1]; ring
  obtain ⟨v, hv⟩ := hf
  have hτfi : τ (↑v⁻¹ : R) = ↑v⁻¹ := by
    have h1 : τ (↑v⁻¹ : R) * f = 1 := by
      rw [← hτf, ← map_mul, ← hv, v.inv_mul, map_one]
    calc τ (↑v⁻¹ : R) = τ ↑v⁻¹ * (f * ↑v⁻¹) := by rw [← hv, v.mul_inv, mul_one]
      _ = ↑v⁻¹ := by rw [← mul_assoc, h1, one_mul]
  let tA : A := ⟨θ + τ θ, memA _ (by rw [map_add, hτ, add_comm])⟩
  let mA : A := ⟨θ * τ θ, memA _ (by rw [map_mul, hτ, mul_comm])⟩
  let fA : A := ⟨f, memA _ hτf⟩
  let wA : A := ⟨↑u⁻¹ * ↑u⁻¹, memA _ (by rw [map_mul, hτdi]; ring)⟩
  let vA : A := ⟨↑v⁻¹, memA _ hτfi⟩
  have hdisc : IsUnit (tA ^ 2 - 4 * mA) := by
    suffices h : (tA ^ 2 - 4 * mA) * wA = 1 from ⟨⟨_, wA, h, by rw [mul_comm]; exact h⟩, rfl⟩
    refine Subtype.ext ?_
    have e1 : (θ + τ θ) ^ 2 - 4 * (θ * τ θ) = ↑u * ↑u := by rw [hu]; ring
    push_cast [tA, mA, wA]
    rw [h4, e1, show (↑u : R) * ↑u * (↑u⁻¹ * ↑u⁻¹) = (↑u * ↑u⁻¹) * (↑u * ↑u⁻¹) by ring, u.mul_inv,
      one_mul]
  have hfA : IsUnit fA := by
    suffices h : fA * vA = 1 from ⟨⟨_, vA, h, by rw [mul_comm]; exact h⟩, rfl⟩
    refine Subtype.ext ?_
    push_cast [fA, vA]
    rw [← hv, v.mul_inv]
  haveI : IsReduced A := ⟨fun x hx => Subtype.ext (IsNilpotent.eq_zero (hx.map A.subtype))⟩
  obtain ⟨a, b, hab⟩ := binQuad_represents_unit_of_finite_reduced A tA mA fA hdisc hfA
  have hab' := congrArg Subtype.val hab
  push_cast [tA, mA, fA] at hab'
  refine ⟨(a : R) + θ * b, ?_⟩
  rw [map_add, map_mul, fixA a, fixA b]
  linear_combination hab'

end GlobalTheory
