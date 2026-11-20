import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBoxRadiiAtEntry

open ValuativeRel Matrix GlobalTheory.SplitFlip GlobalTheory.FullRankCoinv GlobalTheory.RankCoinv GlobalTheory.NormalCore

noncomputable section
namespace GlobalTheory.NormalCore

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem ebox_eq_preimage {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A D : Type} (ϖ : kˣ) (C : Matrix A D k) (r : A → D → ℕ) :
    ebox ϖ C r = (fun X : Matrix A D k => Matrix.of fun i j => (((ϖ ^ r i j)⁻¹ : kˣ) : k) * (X i j - C i j)) ⁻¹'
      {Y | ∀ i j, Y i j ∈ 𝒪[k]} := by
  ext X
  simp only [ebox, Set.mem_setOf_eq, Set.mem_preimage, of_apply, Valuation.mem_integer_iff, map_mul]
  refine forall₂_congr fun i j => ?_
  have h0 : 0 < valuation k ((ϖ ^ r i j : kˣ) : k) := zero_lt_iff.2 (by simp)
  rw [Units.val_inv_eq_inv_val, map_inv₀, inv_mul_le_iff₀ h0, mul_one]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components. Simplify to obtain the desired conclusion from the available facts.
-/
theorem ebox_eq_image {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A D : Type} (ϖ : kˣ) (C : Matrix A D k) (r : A → D → ℕ) :
    ebox ϖ C r = (fun Y : Matrix A D k => Matrix.of fun i j => C i j + ((ϖ ^ r i j : kˣ) : k) * Y i j) ''
      {Y | ∀ i j, Y i j ∈ 𝒪[k]} := by
  rw [ebox_eq_preimage]
  ext X
  constructor
  · intro hX
    refine ⟨_, hX, ?_⟩
    ext i j
    simp [← mul_assoc]
  · rintro ⟨Y, hY, rfl⟩
    simpa [← mul_assoc] using hY

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isCompact_ebox {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A D : Type} [Fintype A] [Fintype D] (ϖ : kˣ) (C : Matrix A D k) (r : A → D → ℕ) :
    IsCompact (ebox ϖ C r) := by
  rw [ebox_eq_image]
  exact isCompact_intMatrix.image (by fun_prop)

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isClopen_ebox (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D : Type) [Fintype A] [Fintype D] (ϖ : kˣ) (C : Matrix A D k) (r : A → D → ℕ) :
    IsClopen (ebox ϖ C r) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have : T2Space (Matrix A D k) := inferInstanceAs (T2Space (A → D → k))
  refine ⟨(isCompact_ebox ϖ C r).isClosed, ?_⟩
  rw [ebox_eq_preimage]
  exact isOpen_intMatrix.preimage (by fun_prop)

end GlobalTheory.NormalCore
