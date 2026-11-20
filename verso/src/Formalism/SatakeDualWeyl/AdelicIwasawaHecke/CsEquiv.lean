import Formalism.SatakeDualWeyl.DefsCS
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bridge

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P

open Formalism.UG Formalism.UG.CS

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem csEquiv_bc_mulVec (γ : GL n E) (x : n → E) :
    (((bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
        Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ
        (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i))) =
      fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (((γ : Matrix n n E) *ᵥ x) i) := by
  funext i
  rw [RingHom.map_mulVec]
  rfl

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem csEquiv_mem (Λ : Submodule (𝓞 E) (n → E)) (γ : GL n E)
    (g k : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hk : k ∈ stabGL (latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ)) (x : n → E) :
    x ∈ globLat (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * g * k) Λ ↔
      ((γ⁻¹ : GL n E) : Matrix n n E) *ᵥ x ∈ globLat g Λ := by
  have hki := (stabGL _).inv_mem hk
  show (((bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * g * k)⁻¹ :
      GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ
      (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ ↔
    ((g⁻¹ : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix n n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ
      (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((((γ⁻¹ : GL n E) : Matrix n n E) *ᵥ x) i)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ← map_inv, csEquiv_bc_mulVec]
  exact (hki _).symm

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem csEquiv_main (Λ : Submodule (𝓞 E) (n → E)) (γ : GL n E)
    (g k : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hk : k ∈ stabGL (latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ)) :
    globLat (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * g * k) Λ =
      Formalism.HermitianLatticesTheory.gmap (glEquiv γ) (globLat g Λ) := by
  ext x
  rw [csEquiv_mem Λ γ g k hk x]
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [Submodule.mem_map]
  constructor
  · intro hx
    refine ⟨_, hx, ?_⟩
    simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    rw [glEquiv_apply', Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  · rintro ⟨y, hy, rfl⟩
    simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    rw [glEquiv_apply', Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
    exact hy

end

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem global_lattice_equiv_holds : Formalism.UG.CS.GlobLatEquiv := by
  intro F E _ _ _ _ _ n _ _ Λ γ g k hk
  exact csEquiv_main Λ γ g k hk

end Formalism.UG.P
