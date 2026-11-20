import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff
import Mathlib.NumberTheory.Padics.PadicIntegers

open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

/- English proof (translation)
Introduce `Γ _ _ l _ y hy`. Establish `hle : ∀ g : Γ, ‖((y.coeff g : ℚ) : ℚ_[l])‖ ≤ 1`. Introduce `g`. Establish `h` using `hy g`. Rewrite `h` using `[pow_zero, div_one, mem_Zl]`.

Conclude with `Padic.norm_rat_le_one h`. Set `x : Γ → ℤ_[l]` to `fun g => ⟨((y.coeff g : ℚ) : ℚ_[l]), hle g⟩`. Use `⟨MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm x), ?_⟩` and prove the remaining obligations. Apply `MonoidAlgebra.ext` to reduce the goal to its premises. Use extensionality with `g`.

Rewrite using `[MonoidAlgebra.coeff_mapRingHom, MonoidAlgebra.coeff_mapRingHom]`. Express the relevant statement in the definitionally equal form `algebraMap ℤ_[l] ℚ_[l] ((Finsupp.equivFunOnFinite.symm x) g) = _`. Rewrite using `[Finsupp.equivFunOnFinite_symm_apply_apply]`. Both sides reduce to the same expression.
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
