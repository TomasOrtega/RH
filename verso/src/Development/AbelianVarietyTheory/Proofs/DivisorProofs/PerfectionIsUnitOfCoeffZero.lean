import Mathlib

namespace GlobalTheory

open IsLocalRing

open IsLocalRing in
/- English proof (translation)
Introduce `p _ O _ _ _`. Use `haveI : IsLocalRing (ModP O p) := IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective`. Use `haveI : IsLocalHom (Perfection.coeff (ModP O p) p 0) := by`. Use `⟨fun x hx => ?_⟩` and prove the remaining obligations. Establish `hunit : ∀ n, IsUnit (Perfection.coeff (ModP O p) p n x)`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => exact hx`. Consider the case `succ n ih`. Rewrite `ih` using `[← Perfection.coeff_pow_p' x n]`.

Conclude with `(isUnit_pow_iff (Fact.out : p.Prime).ne_zero).mp ih`. Set `y : Perfection (ModP O p) p` to `⟨fun n => ↑(hunit n).unit⁻¹, fun n => by`. Establish `key : (hunit (n + 1)).unit ^ p = (hunit n).unit` using `Units.ext (by simpa using Perfection.coeff_pow_p' x n)`. Rewrite using `[← Units.val_pow_eq_pow_val, inv_pow, key]⟩`. Establish `hxy : x * y = 1` using `Perfection.ext fun n => by`.

Rewrite using `[map_mul, map_one]`. Use `show Perfection.coeff (ModP O p) p n x * ↑(hunit n).unit⁻¹ = 1`. Conclude with `(hunit n).mul_val_inv`. Conclude with `⟨⟨x, y, hxy, mul_comm y x ▸ hxy⟩, rfl⟩`. Conclude with `(Perfection.coeff (ModP O p) p 0).domain_isLocalRing`.
-/
theorem _root_.GlobalTheory.preTilt_isLocalRing : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    [Fact ¬IsUnit (p : O)], IsLocalRing (PreTilt O p) := by
  intro p _ O _ _ _
  haveI : IsLocalRing (ModP O p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Perfection.coeff (ModP O p) p 0) := by
    refine ⟨fun x hx => ?_⟩
    have hunit : ∀ n, IsUnit (Perfection.coeff (ModP O p) p n x) := by
      intro n
      induction n with
      | zero => exact hx
      | succ n ih =>
        rw [← Perfection.coeff_pow_p' x n] at ih
        exact (isUnit_pow_iff (Fact.out : p.Prime).ne_zero).mp ih
    let y : Perfection (ModP O p) p := ⟨fun n => ↑(hunit n).unit⁻¹, fun n => by
      have key : (hunit (n + 1)).unit ^ p = (hunit n).unit :=
        Units.ext (by simpa using Perfection.coeff_pow_p' x n)
      rw [← Units.val_pow_eq_pow_val, inv_pow, key]⟩
    have hxy : x * y = 1 := Perfection.ext fun n => by
      rw [map_mul, map_one]
      show Perfection.coeff (ModP O p) p n x * ↑(hunit n).unit⁻¹ = 1
      exact (hunit n).mul_val_inv
    exact ⟨⟨x, y, hxy, mul_comm y x ▸ hxy⟩, rfl⟩
  exact (Perfection.coeff (ModP O p) p 0).domain_isLocalRing

end GlobalTheory
