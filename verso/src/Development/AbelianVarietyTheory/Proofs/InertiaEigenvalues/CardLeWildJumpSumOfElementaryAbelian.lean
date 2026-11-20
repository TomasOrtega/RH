import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisGroupFixedFieldBaseChangeLocalFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeWildJumpSumTotallyRamifiedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumComapInjectiveStatement

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

/- English proof (translation)
Introduce `K L _ _ _ _ _ _ _ _ _ _ _ _ p E A B hp hE hA hord hcomm hpow hnot`. Take `⟨j, hj, hrange, -, hram⟩` from `GlobalTheory.T.galoisGroup_fixedField_baseChange_localField K L A`. Establish `hmemA : ∀ σ, j σ ∈ A` using `fun σ => hrange.le ⟨σ, rfl⟩`. Establish `htop : lowerRamificationGroup (IntermediateField.fixedField A) L 0 = ⊤`. Rewrite using `[hram, eq_top_iff]`.

Introduce `σ _`. Conclude with `hA (hmemA σ)`. Establish `hcomm' : ∀ σ τ : L ≃ₐ[IntermediateField.fixedField A] L, σ * τ * σ⁻¹ * τ⁻¹ ∈ B.comap j`. Introduce `σ τ`. Rewrite using `[Subgroup.mem_comap, map_mul, map_mul, map_mul, map_inv, map_inv]`.

Conclude with `hcomm _ (hmemA σ) _ (hmemA τ)`. Establish `hpow' : ∀ σ : L ≃ₐ[IntermediateField.fixedField A] L, σ ^ p ∈ B.comap j`. Introduce `σ`. Rewrite using `[Subgroup.mem_comap, map_pow]`. Conclude with `hpow _ (hmemA σ)`.

Establish `hne : B.comap j ≠ ⊤`. Introduce `h`. Apply `hnot` to reduce the goal to its premises. Introduce `a ha`. Take `⟨σ, rfl⟩` from `hrange.ge ha`.

Establish `: σ ∈ B.comap j` using `h ▸ Subgroup.mem_top σ`. Conclude with `this`. Establish `key` using `GlobalTheory.T.card_le_wild_jumpSum_totallyRamified (IntermediateField.fixedField A) L p E (B.comap j) hp hE htop hord hcomm' hpow' hne`. Establish `hwild : wild (IntermediateField.fixedField A) L = fun t => (wild K L t).comap j`. Use function extensionality and compare the values at `t`.

Conclude with `hram _`. Establish `hcard : Nat.card (L ≃ₐ[IntermediateField.fixedField A] L) = Nat.card ↥A`. Conclude with `(Nat.card_congr (MonoidHom.ofInjective hj).toEquiv).trans (congrArg (fun H : Subgroup (L ≃ₐ[K] L) => Nat.card ↥H) hrange)`. Establish `hjs : jumpSum (wild K L) A B = jumpSum (wild (IntermediateField.fixedField A) L) ⊤ (B.comap j)`. Rewrite using `[hwild, GlobalTheory.T.ramificationJumpSum_comap_injective _ _ j (wild K L) B hj]`.

Conclude with `congrArg (fun H => jumpSum (wild K L) H B) hrange.symm`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem card_le_jumpSum_wild :
    ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E : ℕ) (A B : Subgroup (L ≃ₐ[K] L)), p.Prime → 0 < E → A ≤ lowerRamificationGroup K L 0 → OrdIs L p E → (∀ σ ∈ A, ∀ τ ∈ A, σ * τ * σ⁻¹ * τ⁻¹ ∈ B) → (∀ σ ∈ A, σ ^ p ∈ B) → ¬ A ≤ B → Nat.card ↥A ≤ jumpSum (wild K L) A B := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ p E A B hp hE hA hord hcomm hpow hnot
  obtain ⟨j, hj, hrange, -, hram⟩ := GlobalTheory.T.galoisGroup_fixedField_baseChange_localField K L A
  have hmemA : ∀ σ, j σ ∈ A := fun σ => hrange.le ⟨σ, rfl⟩
  have htop : lowerRamificationGroup (IntermediateField.fixedField A) L 0 = ⊤ := by
    rw [hram, eq_top_iff]
    intro σ _
    exact hA (hmemA σ)
  have hcomm' : ∀ σ τ : L ≃ₐ[IntermediateField.fixedField A] L,
      σ * τ * σ⁻¹ * τ⁻¹ ∈ B.comap j := by
    intro σ τ
    rw [Subgroup.mem_comap, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact hcomm _ (hmemA σ) _ (hmemA τ)
  have hpow' : ∀ σ : L ≃ₐ[IntermediateField.fixedField A] L, σ ^ p ∈ B.comap j := by
    intro σ
    rw [Subgroup.mem_comap, map_pow]
    exact hpow _ (hmemA σ)
  have hne : B.comap j ≠ ⊤ := by
    intro h
    apply hnot
    intro a ha
    obtain ⟨σ, rfl⟩ := hrange.ge ha
    have : σ ∈ B.comap j := h ▸ Subgroup.mem_top σ
    exact this
  have key := GlobalTheory.T.card_le_wild_jumpSum_totallyRamified (IntermediateField.fixedField A) L p E (B.comap j) hp hE htop hord
    hcomm' hpow' hne
  have hwild : wild (IntermediateField.fixedField A) L = fun t => (wild K L t).comap j := by
    funext t
    exact hram _
  have hcard : Nat.card (L ≃ₐ[IntermediateField.fixedField A] L) = Nat.card ↥A := by
    exact (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv).trans
      (congrArg (fun H : Subgroup (L ≃ₐ[K] L) => Nat.card ↥H) hrange)
  have hjs : jumpSum (wild K L) A B =
      jumpSum (wild (IntermediateField.fixedField A) L) ⊤ (B.comap j) := by
    rw [hwild, GlobalTheory.T.ramificationJumpSum_comap_injective _ _ j (wild K L) B hj]
    exact congrArg (fun H => jumpSum (wild K L) H B) hrange.symm
  calc Nat.card ↥A = Nat.card (L ≃ₐ[IntermediateField.fixedField A] L) := hcard.symm
    _ ≤ _ := key
    _ = jumpSum (wild K L) A B := hjs.symm

end GlobalTheory.PMon.Ram
