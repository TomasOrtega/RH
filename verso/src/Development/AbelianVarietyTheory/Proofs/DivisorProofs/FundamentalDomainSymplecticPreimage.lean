import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtMapApply

set_option autoImplicit false

open Matrix MeasureTheory Set GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped ContDiff

namespace GlobalTheory.TorsionForm

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem sp_vecMul_vecMul_inv {g : ℕ} (γ : Sp g) (x : Fl g) :
    (x ᵥ* γ.mat) ᵥ* (γ⁻¹).mat = x := by
  have h : γ.mat * (γ⁻¹).mat = 1 := congrArg Subtype.val (mul_inv_cancel γ)
  rw [Matrix.vecMul_vecMul, h, Matrix.vecMul_one]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem sp_vecMul_inv_vecMul {g : ℕ} (γ : Sp g) (x : Fl g) :
    (x ᵥ* (γ⁻¹).mat) ᵥ* γ.mat = x := by
  have h : (γ⁻¹).mat * γ.mat = 1 := congrArg Subtype.val (inv_mul_cancel γ)
  rw [Matrix.vecMul_vecMul, h, Matrix.vecMul_one]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sp_vecMul_quasiMeasurePreserving {g : ℕ} (γ : Sp g) :
    Measure.QuasiMeasurePreserving (fun x : Fl g => x ᵥ* γ.mat) volume volume := by
  have h : γ.mat * (γ⁻¹).mat = 1 := congrArg Subtype.val (mul_inv_cancel γ)
  have hd : (γ.mat).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det h
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hdet : LinearMap.det (Matrix.toLin' (γ.mat)ᵀ) ≠ 0 := by
    rw [LinearMap.det_toLin', Matrix.det_transpose]; exact hd
  have := Measure.LinearMap.quasiMeasurePreserving (volume : Measure (Fl g)) _ hdet
  convert this using 1
  funext x
  rw [Matrix.toLin'_apply, Matrix.mulVec_transpose]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isAddFundamentalDomain_preimage_latAct {g : ℕ} (M : Submodule ℤ (Fl g)) (γ : Sp g)
    (D : Set (Fl g)) (hD : IsAddFundamentalDomain (latAct M γ) D volume) :
    IsAddFundamentalDomain M ((fun x : Fl g => x ᵥ* (γ⁻¹).mat) ⁻¹' D) volume := by
  have hmem : ∀ y : Fl g, y ∈ latAct M γ ↔ y ᵥ* γ.mat ∈ M := by
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change (x ᵥ* (γ⁻¹).mat) ᵥ* γ.mat ∈ M
      rw [sp_vecMul_inv_vecMul]; exact hx
    · intro hy
      exact ⟨y ᵥ* γ.mat, hy, sp_vecMul_vecMul_inv γ y⟩
  refine hD.preimage_of_equiv (sp_vecMul_quasiMeasurePreserving γ⁻¹)
    (e := fun l => (⟨(l : Fl g) ᵥ* γ.mat, (hmem l).1 l.2⟩ : M)) ⟨?_, ?_⟩ ?_
  · intro a b hab
    have h := congrArg (fun l : M => (l : Fl g) ᵥ* (γ⁻¹).mat) hab
    simp only [sp_vecMul_vecMul_inv] at h
    exact Subtype.ext h
  · intro l
    refine ⟨⟨(l : Fl g) ᵥ* (γ⁻¹).mat, (hmem _).2 ?_⟩, Subtype.ext (sp_vecMul_inv_vecMul γ l)⟩
    rw [sp_vecMul_inv_vecMul]; exact l.2
  · intro l x
    change ((l : Fl g) ᵥ* γ.mat + x) ᵥ* (γ⁻¹).mat = (l : Fl g) + x ᵥ* (γ⁻¹).mat
    rw [Matrix.add_vecMul, sp_vecMul_vecMul_inv]

end GlobalTheory.TorsionForm
