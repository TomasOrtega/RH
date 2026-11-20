import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff
import Mathlib.NumberTheory.Padics.PadicIntegers

open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem UpperTheory.V.B5.exists_padicInt_lift_of_integralAt :
    ∀ {Γ : Type} [CommGroup Γ] [Finite Γ] (l : ℕ) [Fact l.Prime] (y : MonoidAlgebra ℚ Γ), IntAt l 0 y → ∃ Yp : MonoidAlgebra ℤ_[l] Γ, MonoidAlgebra.mapRingHom Γ (algebraMap ℤ_[l] ℚ_[l]) Yp = MonoidAlgebra.mapRingHom Γ (Rat.castHom ℚ_[l]) y := by
  intro Γ _ _ l _ y hy
  have hle : ∀ g : Γ, ‖((y.coeff g : ℚ) : ℚ_[l])‖ ≤ 1 := by
    intro g
    have h := hy g
    rw [pow_zero, div_one, mem_Zl] at h
    exact Padic.norm_rat_le_one h
  let x : Γ → ℤ_[l] := fun g => ⟨((y.coeff g : ℚ) : ℚ_[l]), hle g⟩
  refine ⟨MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm x), ?_⟩
  apply MonoidAlgebra.ext
  ext g
  rw [MonoidAlgebra.coeff_mapRingHom, MonoidAlgebra.coeff_mapRingHom]
  change algebraMap ℤ_[l] ℚ_[l] ((Finsupp.equivFunOnFinite.symm x) g) = _
  rw [Finsupp.equivFunOnFinite_symm_apply_apply]
  rfl
