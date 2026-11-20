import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseCharpolyLinearEqui
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[gal]`.
-/
theorem gal_id_eq {F : Type} [Field F] (n : ℕ) (y : GL (Fin n) F) : gal (RingHom.id F) n y = y := by
  ext i j; simp [gal]

/- English proof (translation)
Unfold `hcTw`. Use `congr 1`. Establish `h : ∀ z : GL (Fin n) F, z⁻¹ * (y⁻¹ * x * gal t n y) * gal t n z = (y * z)⁻¹ * x * gal t n (y * z)`. Introduce `z`. Simplify using `only [map_mul, mul_inv_rev]`.

Use `group`. Repeatedly rewrite using `[h]`. Conclude with `finsum_comp_equiv (Equiv.mulLeft y) (f := fun w : GL (Fin n) F => if InPar a (w⁻¹ * x * gal t n w) then α (tlG a (w⁻¹ * x * gal t n w)) * β (brG a b (w⁻¹ * x * gal t n w)) else 0)`.
-/
theorem hcTw_twisted_class {F : Type} [Field F] (t : F →+* F) (a b n : ℕ) (α : GL (Fin a) F → ℂ)
    (β : GL (Fin b) F → ℂ) (x y : GL (Fin n) F) :
    hcTw t a b α β n (y⁻¹ * x * gal t n y) = hcTw t a b α β n x := by
  unfold hcTw
  congr 1
  have h : ∀ z : GL (Fin n) F, z⁻¹ * (y⁻¹ * x * gal t n y) * gal t n z
      = (y * z)⁻¹ * x * gal t n (y * z) := by
    intro z; simp only [map_mul, mul_inv_rev]; group
  simp_rw [h]
  exact finsum_comp_equiv (Equiv.mulLeft y)
    (f := fun w : GL (Fin n) F => if InPar a (w⁻¹ * x * gal t n w) then
      α (tlG a (w⁻¹ * x * gal t n w)) * β (brG a b (w⁻¹ * x * gal t n w)) else 0)

/- English proof (translation)
Introduce `x y`. Use `hcTw_twisted_class (RingHom.id F) a b n α β x y` as an intermediate fact. Rewrite `this` using `[gal_id_eq]`. Conclude with `this`.
-/
theorem hc_isCl {F : Type} [Field F] (a b n : ℕ) (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) :
    IsCl (hc a b α β n) := by
  intro x y
  have := hcTw_twisted_class (RingHom.id F) a b n α β x y
  rw [gal_id_eq] at this
  exact this

/- English proof (translation)
Introduce `x y`. Unfold `psiG`. Set `e : (Fin n → F) ≃ₗ[F] (Fin n → F)` to `LinearEquiv.ofLinear (Matrix.toLin' ((y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) (Matrix.toLin' ((y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) (by rw [← Matrix.toLin'_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.toLin'_one]) (by rw [← Matrix.toLin'_mul, ← U …`. Establish `he : e.conj (Matrix.toLin' ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) = Matrix.toLin' (((y⁻¹ * x * y : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F)`. Rewrite using `[LinearEquiv.conj_apply, Units.val_mul, Units.val_mul, Matrix.toLin'_mul, Matrix.toLin'_mul]`.

Both sides reduce to the same expression. Rewrite using `[← he, psi_conj]`.
-/
theorem psiG_isCl {F : Type} [Field F] (S : F[X] → ℂ) (n : ℕ) : IsCl (psiG S n) := by
  intro x y
  unfold psiG
  let e : (Fin n → F) ≃ₗ[F] (Fin n → F) :=
    LinearEquiv.ofLinear (Matrix.toLin' ((y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
      (Matrix.toLin' ((y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
      (by rw [← Matrix.toLin'_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.toLin'_one])
  have he : e.conj (Matrix.toLin' ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) =
      Matrix.toLin' (((y⁻¹ * x * y : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F) := by
    rw [LinearEquiv.conj_apply, Units.val_mul, Units.val_mul, Matrix.toLin'_mul, Matrix.toLin'_mul]
    rfl
  rw [← he, psi_conj]

/- English proof (translation)
Introduce `x y`. Unfold `chG`. Use `congr 1`. Use `Matrix.charpoly_units_conj (y⁻¹ : GL (Fin n) F) (x : Matrix (Fin n) (Fin n) F)` as an intermediate fact. Rewrite using `[← this, Units.val_mul, Units.val_mul]`.

Use `congr 2`. Rewrite using `[← Matrix.coe_units_inv, inv_inv]`.
-/
theorem chG_isCl {F : Type} [Field F] (S : F[X] → ℂ) (n : ℕ) : IsCl (chG S n) := by
  intro x y
  unfold chG
  congr 1
  have := Matrix.charpoly_units_conj (y⁻¹ : GL (Fin n) F) (x : Matrix (Fin n) (Fin n) F)
  rw [← this, Units.val_mul, Units.val_mul]
  congr 2
  rw [← Matrix.coe_units_inv, inv_inv]

/- English proof (translation)
Introduce `F _ _ t a b n α β`. Conclude with `⟨fun x y => hcTw_twisted_class t a b n α β x y, hc_isCl a b n α β, fun S => ⟨psiG_isCl S n, chG_isCl S n⟩⟩`.
-/
theorem twisted_class_main : ∀ (F : Type) [Field F] [Finite F], ∀ (t : F →+* F) (a b n : ℕ) (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ), (∀ x y, hcTw t a b α β n (y⁻¹ * x * gal t n y) = hcTw t a b α β n x) ∧ IsCl (hc a b α β n) ∧ ∀ S : F[X] → ℂ, IsCl (psiG S n) ∧ IsCl (chG S n) := by
  intro F _ _ t a b n α β
  exact ⟨fun x y => hcTw_twisted_class t a b n α β x y, hc_isCl a b n α β,
    fun S => ⟨psiG_isCl S n, chG_isCl S n⟩⟩

end GlobalTheory.Shin
