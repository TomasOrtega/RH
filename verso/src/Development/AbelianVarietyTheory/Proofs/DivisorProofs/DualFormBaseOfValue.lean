import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DTermOrigin

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

namespace GlobalTheory.DualBase

/- English proof (translation)
Introduce `E _ _ _ I _ _ φ hcm hval d δ hd hδ hφ η`. Establish `hδ0 : δ ≠ 0`. Introduce and unpack `rfl`. Establish `: (d : E) = 0` using `by simpa using hδ.symm`. Establish `: d = 0` using `by exact_mod_cast this`.

Use linear arithmetic over natural numbers and integers. Take `⟨i0, -⟩` from `hcm (Classical.choice (inferInstance : Nonempty (E →+* ℂ)))`. Establish `hconj : IsCMField.complexConj E δ = -δ`. Apply `(φ i0).injective` to reduce the goal to its premises. Rewrite using `[IsCMField.complexEmbedding_complexConj, hφ, map_neg, hφ]`.

Simplify using `[Complex.conj_ofReal]`. Establish `hξ0 : ((η : ℤ) : E) * δ⁻¹ ≠ 0` using `mul_ne_zero (by simp) (inv_ne_zero hδ0)`. Establish `hξc : IsCMField.complexConj E (((η : ℤ) : E) * δ⁻¹) = -(((η : ℤ) : E) * δ⁻¹)`. Rewrite using `[map_mul, map_inv₀, hconj, map_intCast, inv_neg, mul_neg]`. Take `⟨h1, h2⟩` from `hval _ hξ0 hξc`.

Use `⟨h1, fun B hB ε => ?_⟩` and prove the remaining obligations. Take `⟨h3, h4⟩` from `h2 B hB ε`. Use `⟨h3, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[h4 i, map_mul, map_inv₀, map_intCast, hφ]`. Establish `hs : (Real.sqrt d : ℂ) ≠ 0`.

Establish `: 0 < Real.sqrt d` using `Real.sqrt_pos.2 (by exact_mod_cast hd)`. Conclude with `this.ne'` after adjusting the coercions. Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Apply the tactic sequence `rcases Int.units_eq_one_or η with rfl | rfl <;> rcases Int.units_eq_one_or ε with rfl | rfl <;>`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts.
-/
theorem dualFormBase_of_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I]
    (φ : I → E →+* ℂ), IsCMType φ → DualFormValue φ → DualFormBase φ := by
  intro E _ _ _ I _ _ φ hcm hval d δ hd hδ hφ η
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    have : (d : E) = 0 := by simpa using hδ.symm
    have : d = 0 := by exact_mod_cast this
    omega
  obtain ⟨i0, -⟩ := hcm (Classical.choice (inferInstance : Nonempty (E →+* ℂ)))
  have hconj : IsCMField.complexConj E δ = -δ := by
    apply (φ i0).injective
    rw [IsCMField.complexEmbedding_complexConj, hφ, map_neg, hφ]
    simp [Complex.conj_ofReal]
  have hξ0 : ((η : ℤ) : E) * δ⁻¹ ≠ 0 := mul_ne_zero (by simp) (inv_ne_zero hδ0)
  have hξc : IsCMField.complexConj E (((η : ℤ) : E) * δ⁻¹) = -(((η : ℤ) : E) * δ⁻¹) := by
    rw [map_mul, map_inv₀, hconj, map_intCast, inv_neg, mul_neg]
  obtain ⟨h1, h2⟩ := hval _ hξ0 hξc
  refine ⟨h1, fun B hB ε => ?_⟩
  obtain ⟨h3, h4⟩ := h2 B hB ε
  refine ⟨h3, fun i => ?_⟩
  rw [h4 i, map_mul, map_inv₀, map_intCast, hφ]
  have hs : (Real.sqrt d : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
    exact_mod_cast this.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rcases Int.units_eq_one_or η with rfl | rfl <;> rcases Int.units_eq_one_or ε with rfl | rfl <;>
    · push_cast
      field_simp

/- English proof (translation)
Substitute `hε hη` using the available equality. Simplify using the standard rewrite rules.
-/
example (ε : ℤˣ) (η : ℤˣ) (hε : ε = 1) (hη : η = -1) : (((ε * η : ℤˣ) : ℤ) : ℂ) = -1 := by
  subst hε hη; simp

end GlobalTheory.DualBase
