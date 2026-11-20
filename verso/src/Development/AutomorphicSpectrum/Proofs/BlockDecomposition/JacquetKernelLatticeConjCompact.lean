import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentTopMemParabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviBlockMemParabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicUnipotentLeviDecompStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulVecMidBlockDecompStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousLeviUnipotentProjStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothIntegralLinearChangeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompParabolicMaximalCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumOverCompactCosetsJacquetKernelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInducedSectionSupportedOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreFunctionLocallyConstantCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactCosetSet
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer.IntTwist

open ValuativeRel in
/- English proof (translation)
Take `⟨g, rfl⟩` from `hκ`. Establish `hl' : ∀ i, c * l.toAdd i ∈ 𝒪[k]` using `hl`. Establish `hent : ∀ a b, (((Matrix.GeneralLinearGroup.map (n` using `Fin n) (algebraMap 𝒪[k] k) g)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) a b ∈ 𝒪[k] := by`. Introduce `a b`. Rewrite using `[← map_inv]`.

Conclude with `(((g⁻¹ : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]) a b).2`. Use `show ∀ j, c * ((((Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k) g)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ l.toAdd) j ∈ 𝒪[k]`. Introduce `j`. Rewrite using `[Matrix.mulVec, dotProduct, Finset.mul_sum]`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[mul_left_comm]`. Conclude with `mul_mem (hent j i) (hl' i)`.
-/
theorem mulH_inv_mem_Lc {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} {c : k} {κ : GL (Fin n) k}
    (hκ : κ ∈ GlobalTheory.SplitWeil.KO k (Fin n)) {l : Multiplicative (Fin n → k)} (hl : l ∈ Lc n c) :
    mulH κ⁻¹ l ∈ Lc n c := by
  obtain ⟨g, rfl⟩ := hκ
  have hl' : ∀ i, c * l.toAdd i ∈ 𝒪[k] := hl
  have hent : ∀ a b, (((Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k) g)⁻¹ :
      GL (Fin n) k) : Matrix (Fin n) (Fin n) k) a b ∈ 𝒪[k] := by
    intro a b
    rw [← map_inv]
    exact (((g⁻¹ : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]) a b).2
  show ∀ j, c * ((((Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k) g)⁻¹ :
      GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ l.toAdd) j ∈ 𝒪[k]
  intro j
  rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine sum_mem fun i _ => ?_
  rw [mul_left_comm]
  exact mul_mem (hent j i) (hl' i)

/- English proof (translation)
Use `show Multiplicative.ofAdd ((κ : Matrix (Fin n) (Fin n) k).mulVec (((κ⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec l.toAdd)) = l`. Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`. Both sides reduce to the same expression.
-/
theorem mulH_mulH_inv {k : Type} [Field k] {n : ℕ} (κ : GL (Fin n) k)
    (l : Multiplicative (Fin n → k)) : mulH κ (mulH κ⁻¹ l) = l := by
  show Multiplicative.ofAdd ((κ : Matrix (Fin n) (Fin n) k).mulVec
    (((κ⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec l.toAdd)) = l
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  rfl

/- English proof (translation)
Introduce `k _ _ _ _ n X _ _ ρ c κ hκ x hx`. Unfold `GlobalTheory.PRep.twKer at hx ⊢`. Use `Submodule.span_le.2 ?_ hx` and prove the remaining obligations. Introduce and unpack `w ⟨m, v, rfl⟩`. Apply `Submodule.subset_span` to reduce the goal to its premises.

Use `⟨⟨mulH κ⁻¹ m, mulH_inv_mem_Lc hκ m.2⟩, v, ?_⟩` and prove the remaining obligations. Simplify using `[mulH_mulH_inv]`.
-/
theorem twKer_Lc_le_twist : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) {X : Type} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Multiplicative (Fin n → k)) X) (c : k) (κ : GL (Fin n) k), κ ∈ GlobalTheory.SplitWeil.KO k (Fin n) → ∀ x, x ∈ twKer ρ (Lc n c) 1 → x ∈ twKer (MonoidHom.comp ρ (mulH κ)) (Lc n c) 1 := by
  intro k _ _ _ _ n X _ _ ρ c κ hκ x hx
  unfold GlobalTheory.PRep.twKer at hx ⊢
  refine Submodule.span_le.2 ?_ hx
  rintro w ⟨m, v, rfl⟩
  apply Submodule.subset_span
  refine ⟨⟨mulH κ⁻¹ m, mulH_inv_mem_Lc hκ m.2⟩, v, ?_⟩
  simp [mulH_mulH_inv]

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer.IntTwist
