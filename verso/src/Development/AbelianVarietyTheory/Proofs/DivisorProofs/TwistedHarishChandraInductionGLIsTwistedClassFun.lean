import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseCharpolyLinearEqui
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem gal_id_eq {F : Type} [Field F] (n : ℕ) (y : GL (Fin n) F) : gal (RingHom.id F) n y = y := by
  ext i j; simp [gal]

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Rewrite the conclusion repeatedly using the stated equalities. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem hc_isCl {F : Type} [Field F] (a b n : ℕ) (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) :
    IsCl (hc a b α β n) := by
  intro x y
  have := hcTw_twisted_class (RingHom.id F) a b n α β x y
  rw [gal_id_eq] at this
  exact this

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.
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
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities.
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
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem twisted_class_main : ∀ (F : Type) [Field F] [Finite F], ∀ (t : F →+* F) (a b n : ℕ) (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ), (∀ x y, hcTw t a b α β n (y⁻¹ * x * gal t n y) = hcTw t a b α β n x) ∧ IsCl (hc a b α β n) ∧ ∀ S : F[X] → ℂ, IsCl (psiG S n) ∧ IsCl (chG S n) := by
  intro F _ _ t a b n α β
  exact ⟨fun x y => hcTw_twisted_class t a b n α β x y, hc_isCl a b n α β,
    fun S => ⟨psiG_isCl S n, chG_isCl S n⟩⟩

end GlobalTheory.Shin
