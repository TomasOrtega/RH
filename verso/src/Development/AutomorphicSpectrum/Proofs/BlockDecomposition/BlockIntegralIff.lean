import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIntZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadMod

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CtS

/- English proof (translation)
Establish `hU : IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h)) (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val))`. Rewrite using `[Matrix.isUnit_iff_isUnit_det, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).1 m.1.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).1 m.2.isUnit)`. Unfold `blk`. Simplify using `only`.

Rewrite using `[dif_pos hU]`. Both sides reduce to the same expression.
-/
theorem blk_val_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ} (h : a + b = n) (w : Pl E)
    (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (blk h w m X).val = Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val) := by
  have hU : IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 m.1.isUnit).mul
      ((Matrix.isUnit_iff_isUnit_det _).1 m.2.isUnit)
  unfold blk
  simp only
  rw [dif_pos hU]
  rfl

/- English proof (translation)
Introduce `E _ _ _ n a b h w m X`. Rewrite using `[blk_val_eq]`. Use `set e : Fin a ⊕ Fin b ≃ Fin n := finSumFinEquiv.trans (finCongr h) with he`. Prove the components needed by the constructor for the conclusion. Introduce `H`.

Use `⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Simplify `H (e (Sum.inl i)) (e (Sum.inl j))` using `[Matrix.reindex_apply, Matrix.submatrix_apply]`. Simplify `H (e (Sum.inr i)) (e (Sum.inr j))` using `[Matrix.reindex_apply, Matrix.submatrix_apply]`. Simplify `H (e (Sum.inl i)) (e (Sum.inr j))` using `[Matrix.reindex_apply, Matrix.submatrix_apply]`. Introduce and unpack `⟨h1, h2, h3⟩ i j`.

Take `⟨i, rfl⟩` from `e.surjective i`. Take `⟨j, rfl⟩` from `e.surjective j`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j`. Simplify `h1 i j` using `[Matrix.reindex_apply, Matrix.submatrix_apply]`. Simplify `h3 i j` using `[Matrix.reindex_apply, Matrix.submatrix_apply]`.

Simplify `(Ov E w).zero_mem` using `[Matrix.reindex_apply, Matrix.submatrix_apply]`. Simplify `h2 i j` using `[Matrix.reindex_apply, Matrix.submatrix_apply]`.
-/
theorem isInt_blk_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsInt w (blk h w m X).val ↔ IsInt w m.1.val ∧ IsInt w m.2.val ∧ IsInt w (m.1.val * X) := by
  intro E _ _ _ n a b h w m X
  rw [blk_val_eq]
  set e : Fin a ⊕ Fin b ≃ Fin n := finSumFinEquiv.trans (finCongr h) with he
  constructor
  · intro H
    refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
    · simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using H (e (Sum.inl i)) (e (Sum.inl j))
    · simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using H (e (Sum.inr i)) (e (Sum.inr j))
    · simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using H (e (Sum.inl i)) (e (Sum.inr j))
  · rintro ⟨h1, h2, h3⟩ i j
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    rcases i with i | i <;> rcases j with j | j
    · simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using h1 i j
    · simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using h3 i j
    · simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using (Ov E w).zero_mem
    · simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using h2 i j

end GlobalTheory.CompanionTheory.CtS
