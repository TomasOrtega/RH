import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncMatTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryStabilizerPreservesVacuumConditionAtPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemAdelicLatticeAtPlaceOfTensorWithLattice
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.LatStabTensor

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vecMulVec_mulVec {R : Type} [CommRing R] {n d : ℕ} (u : Fin n → R) (A : Matrix (Fin d) (Fin d) R)
    (z : Fin d → R) : Matrix.vecMulVec u (A *ᵥ z) = Matrix.vecMulVec u z * Aᵀ := by
  ext i j
  simp only [Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Substitute using the available equality. It suffices to derive a contradiction.

Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Prove the components needed by the constructor for the conclusion. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem latAt_stab : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s : ℕ), X.IsHerm σ B r s →
    ∀ (m : ℕ) (x y : Fin m → Fin n → E), (∀ i, x i ∈ X.L ∧ y i ∈ X.L) → ∑ i, form σ X.J (x i) (y i) = 1 →
    ∀ (v : Pl F) (k : UA σ W.J), (∀ γ, γ * Matrix.transpose (mat k) ∈ latAtV X W v ↔ γ ∈ latAtV X W v) →
    ∀ z ∈ GlobalTheory.InertSph.latAt W v, mat k *ᵥ z ∈ GlobalTheory.InertSph.latAt W v ∧ mat k⁻¹ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  intro F E _ _ _ _ _ σ B n d X W r s hX m x y hxy hsum v k hk z hz
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      exfalso
      have : ∀ i, form σ X.J (x i) (y i) = 0 := fun i => by simp [form, dotProduct]
      simp [this] at hsum
    · exact h0
  have hinv : mat k * mat k⁻¹ = 1 := k.1.val_inv
  have hT : (mat k⁻¹)ᵀ * (mat k)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hinv, Matrix.transpose_one]
  constructor
  · refine GlobalTheory.LatExtract.main F E n d X W v _ hn hX.lat fun x' hx' => ?_
    rw [vecMulVec_mulVec]
    exact (hk _).2 (GlobalTheory.InertSph.vecMulVec_mem_latAtV X W v hx' hz)
  · refine GlobalTheory.LatExtract.main F E n d X W v _ hn hX.lat fun x' hx' => ?_
    rw [vecMulVec_mulVec]
    refine (hk _).1 ?_
    rw [Matrix.mul_assoc, hT, Matrix.mul_one]
    exact GlobalTheory.InertSph.vecMulVec_mem_latAtV X W v hx' hz

end GlobalTheory.LatStabTensor
