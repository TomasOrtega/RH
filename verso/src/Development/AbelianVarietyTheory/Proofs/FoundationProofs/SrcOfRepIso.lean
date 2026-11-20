import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLatticeComplement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.SrcConj

variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ}

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, Units.val_mul, tw_val, tw_val, h s, Units.val_mul, Units.val_mul, Matrix.mul_smul, Matrix.smul_mul]`.
-/
theorem tw_conj (r r' : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) (g : GL (Fin n) k)
    (h : ∀ s, r' s = g * r s * g⁻¹) (s : Γ) : tw r' χ s = g * tw r χ s * g⁻¹ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, tw_val, tw_val, h s, Units.val_mul, Units.val_mul,
    Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Use `GlobalTheory.LatticeComplement.isSSRep_of_intertwine r r' (g : Matrix (Fin n) (Fin n) k) ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) ?_ ?_ hr` and prove the remaining obligations. Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`. Introduce `s`. Rewrite using `[h s, ← Units.val_mul, ← Units.val_mul]`. Use `congr 1`.

Use `group`.
-/
theorem isSSRep_conj (r r' : Γ →* GL (Fin n) k) (g : GL (Fin n) k) (h : ∀ s, r' s = g * r s * g⁻¹)
    (hr : IsSSRep r) : IsSSRep r' := by
  refine GlobalTheory.LatticeComplement.isSSRep_of_intertwine r r' (g : Matrix (Fin n) (Fin n) k)
    ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) ?_ ?_ hr
  · rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  · intro s
    rw [h s, ← Units.val_mul, ← Units.val_mul]
    congr 1
    group

/- English proof (translation)
Use `⟨isSSRep_conj V V' g h hV.1, hV.2.mono fun w hw A hA => ?_⟩` and prove the remaining obligations. Take `⟨hI, hF⟩` from `hw A hA`. Use `⟨fun s hs => by rw [h s, hI s hs, mul_one, mul_inv_cancel], fun σ hσ => ?_⟩` and prove the remaining obligations. Rewrite using `[← hF σ hσ, h σ⁻¹, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]`.
-/
theorem att_conj {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {k' : ℕ}
    (f : Newform k') (V V' : G ℚ Ω →* GL (Fin 2) (Qbar l)) (g : GL (Fin 2) (Qbar l))
    (h : ∀ s, V' s = g * V s * g⁻¹) (hV : f.Att ι V) : f.Att ι V' := by
  refine ⟨isSSRep_conj V V' g h hV.1, hV.2.mono fun w hw A hA => ?_⟩
  obtain ⟨hI, hF⟩ := hw A hA
  refine ⟨fun s hs => by rw [h s, hI s hs, mul_one, mul_inv_cancel], fun σ hσ => ?_⟩
  rw [← hF σ hσ, h σ⁻¹, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

end GlobalTheory.Ord2.SrcConj

end
