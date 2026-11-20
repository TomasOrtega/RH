import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreCompat

open scoped TensorProduct

namespace GlobalTheory.CentralizerMapTensor

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cenMap_tmul_eq (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (F B : Type) [Field F] [NumberField F] [Ring B]
    [Algebra F B] [Algebra ℚ B] [IsScalarTower ℚ F B] (x : ℚ_[ℓ]) (f : F) :
    GlobalTheory.LKInvGood.cenMap ℓ F B (x ⊗ₜ[ℚ] f) = x ⊗ₜ[ℚ] algebraMap F B f := rfl

/- English proof (translation)
Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero]`. Conclude with `Commute.zero_left _`. Consider the case `add a₁ a₂ h₁ h₂ => rw [map_add]`. Conclude with `h₁.add_left h₂`.

Consider the case `tmul x f`. Rewrite using `[cenMap_tmul_eq]`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => exact Commute.zero_right _`. Consider the case `add y₁ y₂ h₁ h₂ => exact h₁.add_right h₂`.

Consider the case `tmul z b`. Unfold `Commute SemiconjBy`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_comm x z, Algebra.commutes f b]`.
-/
theorem commute_cenMap (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (F B : Type) [Field F] [NumberField F] [Ring B]
    [Algebra F B] [Algebra ℚ B] [IsScalarTower ℚ F B] (a : ℚ_[ℓ] ⊗[ℚ] F) (y : ℚ_[ℓ] ⊗[ℚ] B) :
    Commute (GlobalTheory.LKInvGood.cenMap ℓ F B a) y := by
  induction a using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Commute.zero_left _
  | add a₁ a₂ h₁ h₂ => rw [map_add]; exact h₁.add_left h₂
  | tmul x f =>
    rw [cenMap_tmul_eq]
    induction y using TensorProduct.induction_on with
    | zero => exact Commute.zero_right _
    | add y₁ y₂ h₁ h₂ => exact h₁.add_right h₂
    | tmul z b =>
      unfold Commute SemiconjBy
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        mul_comm x z, Algebra.commutes f b]

end GlobalTheory.CentralizerMapTensor
