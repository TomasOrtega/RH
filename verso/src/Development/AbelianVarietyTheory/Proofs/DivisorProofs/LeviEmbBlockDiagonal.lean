import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockCentre
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFieldNormValuation
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
open scoped TensorProduct
open Matrix

namespace GlobalTheory.LeviBlockExponent

/- English proof (translation)
Establish `hx : (x : ℕ) = 0`. Establish `h1 : blockSizes₂ n i ⟨i, by omega⟩ = 1` using `by simp [blockSizes₂]`. Use `x.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Apply `Fin.ext` to reduce the goal to its premises.

Simplify using `only [blockIndex, Equiv.trans_apply, finCongr_apply, Fin.val_cast, finSigmaFinEquiv_apply, hx, add_zero]`. Rewrite using `[Finset.sum_congr rfl (g := fun _ => 1)]`. Simplify using the standard rewrite rules. Introduce `j _`. Use `j.2` as an intermediate fact.

Simplify using `only [blockSizes₂, Fin.val_castLE]`. Conclude with `if_pos (le_of_lt this)`.
-/
theorem blockIndex_self {n i : ℕ} (hi : i + 1 ≤ n) (x : Fin (blockSizes₂ n i ⟨i, by omega⟩)) :
    blockIndex hi ⟨⟨i, by omega⟩, x⟩ = (⟨i, by omega⟩ : Fin n) := by
  have hx : (x : ℕ) = 0 := by
    have h1 : blockSizes₂ n i ⟨i, by omega⟩ = 1 := by simp [blockSizes₂]
    have := x.2
    omega
  apply Fin.ext
  simp only [blockIndex, Equiv.trans_apply, finCongr_apply, Fin.val_cast, finSigmaFinEquiv_apply, hx, add_zero]
  rw [Finset.sum_congr rfl (g := fun _ => 1)]
  · simp
  · intro j _
    have := j.2
    simp only [blockSizes₂, Fin.val_castLE]
    exact if_pos (le_of_lt this)

/- English proof (translation)
Establish `h1 : blockSizes₂ n i ⟨i, by omega⟩ = 1` using `by simp [blockSizes₂]`. Establish `hs : Subsingleton (Fin (blockSizes₂ n i ⟨i, by omega⟩))` using `by rw [h1]; infer_instance`. Establish `x : Fin (blockSizes₂ n i ⟨i, by omega⟩)` using `⟨0, by omega⟩`. Rewrite using `[← blockIndex_self hi x]`. Use extensionality with `p q`.

Take `⟨⟨b, y⟩, rfl⟩` from `(blockIndex hi).surjective p`. Take `⟨⟨b', y'⟩, rfl⟩` from `(blockIndex hi).surjective q`. Distinguish the cases in `hb : b = b'`. Substitute `hb` using the available equality. Rewrite using `[leviEmb_apply_same]`.

Distinguish the cases in `hba : b = ⟨i, by omega⟩`. Substitute `hba` using the available equality. Rewrite using `[Subsingleton.elim y x, Subsingleton.elim y' x]`. Simplify using `[blockScalar₂, Matrix.GeneralLinearGroup.scalar]`. Establish `: blockIndex hi ⟨b, y⟩ ≠ blockIndex hi ⟨⟨i, by omega⟩, x⟩` using `fun h' => hba (congrArg Sigma.fst ((blockIndex hi).injective h'))`.

Simplify using `[blockScalar₂, Pi.mulSingle_eq_of_ne hba, Function.update_of_ne this, diagonal_apply, one_apply]`. Rewrite using `[leviEmb_apply_ne k _ _ hb, diagonal_apply_ne]`. Conclude with `fun h' => hb (congrArg Sigma.fst ((blockIndex hi).injective h'))`.
-/
theorem leviEmb_positionElt_eq_diagonal (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n i : ℕ) (hi : i + 1 ≤ n) (ϖ : kˣ) :
    ((GlobalTheory.SmGL.leviEmb k (blockIndex hi) (blockScalar₂ k n i ϖ)) : Matrix (Fin n) (Fin n) k) =
      Matrix.diagonal (Function.update 1 (⟨i, by omega⟩ : Fin n) (ϖ : k)) := by
  have h1 : blockSizes₂ n i ⟨i, by omega⟩ = 1 := by simp [blockSizes₂]
  have hs : Subsingleton (Fin (blockSizes₂ n i ⟨i, by omega⟩)) := by rw [h1]; infer_instance
  have x : Fin (blockSizes₂ n i ⟨i, by omega⟩) := ⟨0, by omega⟩
  rw [← blockIndex_self hi x]
  ext p q
  obtain ⟨⟨b, y⟩, rfl⟩ := (blockIndex hi).surjective p
  obtain ⟨⟨b', y'⟩, rfl⟩ := (blockIndex hi).surjective q
  by_cases hb : b = b'
  · subst hb
    rw [leviEmb_apply_same]
    by_cases hba : b = ⟨i, by omega⟩
    · subst hba
      rw [Subsingleton.elim y x, Subsingleton.elim y' x]
      simp [blockScalar₂, Matrix.GeneralLinearGroup.scalar]
    · have : blockIndex hi ⟨b, y⟩ ≠ blockIndex hi ⟨⟨i, by omega⟩, x⟩ :=
        fun h' => hba (congrArg Sigma.fst ((blockIndex hi).injective h'))
      simp [blockScalar₂, Pi.mulSingle_eq_of_ne hba, Function.update_of_ne this, diagonal_apply, one_apply]
  · rw [leviEmb_apply_ne k _ _ hb, diagonal_apply_ne]
    exact fun h' => hb (congrArg Sigma.fst ((blockIndex hi).injective h'))

end GlobalTheory.LeviBlockExponent
