import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsScalarTowerCenAlgebra
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitSectionAvoidPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CenOrderFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderContainingIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOrderTensorPadicFreeAlmostAllStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOrderTensorPadicIsAzumayaAlmostAllStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AzumayaFreeRankSqEquivMatrixOverLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AzumayaMatrixOfFinitePadicAlgebraOfLocalStatement

noncomputable section
open scoped TensorProduct
open GlobalTheory.LKInvGood

namespace GlobalTheory.LocMatrix

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Conclude with `Algebra.adjoin_mono (Set.image_mono hle)`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `GlobalTheory.one_tmul_mem_locOrder_of_nsmul_mem OB x N hN (hNΛ x hx) ℓ hℓ`.
-/
theorem locOrder_eq_of_le {B : Type} [Ring B] [Algebra ℚ B] (OB Λ : Subring B) (hle : OB ≤ Λ)
    (N : ℕ) (hN : 0 < N) (hNΛ : ∀ x ∈ Λ, (N : B) * x ∈ OB) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ N) :
    locOrder ℓ OB = locOrder ℓ Λ := by
  apply le_antisymm
  · exact Algebra.adjoin_mono (Set.image_mono hle)
  · refine Algebra.adjoin_le ?_
    rintro _ ⟨x, hx, rfl⟩
    exact GlobalTheory.one_tmul_mem_locOrder_of_nsmul_mem OB x N hN (hNΛ x hx) ℓ hℓ

/- English proof (translation)
Introduce `F B _ _ _ _ _ _ _ _ _ n hn OB hfin hspan`. Take `⟨Λ, hle, hΛ, hΛfin, N₁, hN₁, hN₁Λ⟩` from `GlobalTheory.T.exists_order_containing_integers F B OB hfin hspan`. Establish `hspanΛ : ∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ Λ` using `fun b => by`. Take `⟨m, hm, hmb⟩` from `hspan b`. Conclude with `⟨m, hm, hle hmb⟩`.

Take `⟨N₂, hN₂, hfree⟩` from `GlobalTheory.T.localOrderTensorPadic_free_almost_all F B Λ hΛ hΛfin hspanΛ`. Take `⟨N₃, hN₃, hazu⟩` from `GlobalTheory.T.localOrderTensorPadic_isAzumaya_almost_all F B Λ hΛ hΛfin hspanΛ`. Use `⟨N₁ * N₂ * N₃, by positivity, fun ℓ _ hℓ => ?_⟩` and prove the remaining obligations. Establish `h₁ : ¬ ℓ ∣ N₁` using `fun h => hℓ (Dvd.dvd.mul_right (Dvd.dvd.mul_right h _) _)`. Establish `h₂ : ¬ ℓ ∣ N₂` using `fun h => hℓ (Dvd.dvd.mul_right (Dvd.dvd.mul_left h _) _)`.

Establish `h₃ : ¬ ℓ ∣ N₃` using `fun h => hℓ (Dvd.dvd.mul_left h _)`. Establish `heq` using `locOrder_eq_of_le OB Λ hle N₁ hN₁ hN₁Λ ℓ h₁`. Use `letI := cenAlgebra ℓ F B Λ hΛ`. Use `haveI := isScalarTower_cenAlgebra ℓ F B Λ hΛ`. Use `haveI : Module.Finite ℤ_[ℓ] (cenOrder ℓ F) := GlobalTheory.cenOrder_finite F ℓ`.

Take `⟨hF, hrank⟩` from `hfree ℓ h₂`. Use `haveI := hF`. Use `haveI := hazu ℓ h₃`. Take `⟨φ⟩` from `GlobalTheory.T.azumaya_matrix_of_finite_padic_algebra_of_local GlobalTheory.T.azumaya_free_rank_sq_equiv_matrix_over_local ℓ (cenOrder ℓ F) (locOrder ℓ Λ) n (hrank.trans hn)`. Use `⟨(Subalgebra.equivOfEq _ _ heq).trans (φ.restrictScalars ℤ_[ℓ]), fun a => ?_⟩` and prove the remaining obligations.

Use `⟨heq ▸ cenMap_mem ℓ F B Λ hΛ a.2, ?_⟩` and prove the remaining obligations. Establish `h2 : (Subalgebra.equivOfEq _ _ heq) ⟨cenMap ℓ F B a, heq ▸ cenMap_mem ℓ F B Λ hΛ a.2⟩ = algebraMap (cenOrder ℓ F) (locOrder ℓ Λ) a` using `Subtype.ext rfl`. Rewrite using `[AlgEquiv.trans_apply, h2, AlgEquiv.restrictScalars_apply, AlgEquiv.commutes]`. Use extensionality with `i j`. Simplify using `[Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply]`.
-/
theorem locOrder_matrix : ∀ (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] [Algebra.IsCentral F B] [IsSimpleRing B] [FiniteDimensional F B] (n : ℕ),
    Module.finrank F B = n ^ 2 → ∀ (OB : Subring B), Module.Finite ℤ OB →
    (∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ OB) →
    ∃ N : ℕ, 0 < N ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ N →
      ∃ ψ : locOrder ℓ OB ≃ₐ[ℤ_[ℓ]] Matrix (Fin n) (Fin n) (cenOrder ℓ F), CentreCompat ℓ OB ψ := by
  intro F B _ _ _ _ _ _ _ _ _ n hn OB hfin hspan
  obtain ⟨Λ, hle, hΛ, hΛfin, N₁, hN₁, hN₁Λ⟩ := GlobalTheory.T.exists_order_containing_integers F B OB hfin hspan
  have hspanΛ : ∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ Λ := fun b => by
    obtain ⟨m, hm, hmb⟩ := hspan b; exact ⟨m, hm, hle hmb⟩
  obtain ⟨N₂, hN₂, hfree⟩ := GlobalTheory.T.localOrderTensorPadic_free_almost_all F B Λ hΛ hΛfin hspanΛ
  obtain ⟨N₃, hN₃, hazu⟩ := GlobalTheory.T.localOrderTensorPadic_isAzumaya_almost_all F B Λ hΛ hΛfin hspanΛ
  refine ⟨N₁ * N₂ * N₃, by positivity, fun ℓ _ hℓ => ?_⟩
  have h₁ : ¬ ℓ ∣ N₁ := fun h => hℓ (Dvd.dvd.mul_right (Dvd.dvd.mul_right h _) _)
  have h₂ : ¬ ℓ ∣ N₂ := fun h => hℓ (Dvd.dvd.mul_right (Dvd.dvd.mul_left h _) _)
  have h₃ : ¬ ℓ ∣ N₃ := fun h => hℓ (Dvd.dvd.mul_left h _)
  have heq := locOrder_eq_of_le OB Λ hle N₁ hN₁ hN₁Λ ℓ h₁
  letI := cenAlgebra ℓ F B Λ hΛ
  haveI := isScalarTower_cenAlgebra ℓ F B Λ hΛ
  haveI : Module.Finite ℤ_[ℓ] (cenOrder ℓ F) := GlobalTheory.cenOrder_finite F ℓ
  obtain ⟨hF, hrank⟩ := hfree ℓ h₂
  haveI := hF
  haveI := hazu ℓ h₃
  obtain ⟨φ⟩ := GlobalTheory.T.azumaya_matrix_of_finite_padic_algebra_of_local GlobalTheory.T.azumaya_free_rank_sq_equiv_matrix_over_local ℓ (cenOrder ℓ F) (locOrder ℓ Λ) n (hrank.trans hn)
  refine ⟨(Subalgebra.equivOfEq _ _ heq).trans (φ.restrictScalars ℤ_[ℓ]), fun a => ?_⟩
  refine ⟨heq ▸ cenMap_mem ℓ F B Λ hΛ a.2, ?_⟩
  have h2 : (Subalgebra.equivOfEq _ _ heq) ⟨cenMap ℓ F B a, heq ▸ cenMap_mem ℓ F B Λ hΛ a.2⟩ =
      algebraMap (cenOrder ℓ F) (locOrder ℓ Λ) a := Subtype.ext rfl
  rw [AlgEquiv.trans_apply, h2, AlgEquiv.restrictScalars_apply, AlgEquiv.commutes]
  ext i j
  simp [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply]

end GlobalTheory.LocMatrix
