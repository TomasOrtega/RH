import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfValILeOne

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.IwaBlock

/- English proof (translation)
Use `set e : Fin a ⊕ Fin b ≃ Fin n := finSumFinEquiv.trans (finCongr h) with he`. Use `set M : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) K := p.val.submatrix e e with hM`. Establish `h21 : M.toBlocks₂₁ = 0`. Use `Matrix.ext fun i j => hp ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(e (Sum.inl j) : ℕ) < e (Sum.inr i)`.

Simplify using `[he]`. Use linear arithmetic over natural numbers and integers. Establish `hMb : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂`. Rewrite using `[← h21]`. Conclude with `(Matrix.fromBlocks_toBlocks M).symm`.

Establish `hdet : M.det ≠ 0`. Rewrite using `[hM, Matrix.det_submatrix_equiv_self]`. Conclude with `Matrix.GeneralLinearGroup.det_ne_zero p`. Establish `hprod : M.toBlocks₁₁.det * M.toBlocks₂₂.det ≠ 0`. Rewrite `hdet` using `[hMb, Matrix.det_fromBlocks_zero₂₁]`.

Simplify using `using hdet`. Establish `hA : IsUnit M.toBlocks₁₁` using `(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (left_ne_zero_of_mul hprod))`. Establish `hD : IsUnit M.toBlocks₂₂` using `(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (right_ne_zero_of_mul hprod))`. Use `⟨hA.unit, hD.unit, (hA.unit⁻¹ : GL (Fin a) K).val * M.toBlocks₁₂, ?_⟩` and prove the remaining obligations. Establish `hAB : hA.unit.val * ((hA.unit⁻¹ : GL (Fin a) K).val * M.toBlocks₁₂) = M.toBlocks₁₂`.

Rewrite using `[← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]`. Rewrite using `[hAB]`. Express the relevant statement in the definitionally equal form `Matrix.reindex e e (Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂) = p.val`. Rewrite using `[← hMb, hM]`. Use extensionality with `i j`.

Simplify using the standard rewrite rules.
-/
theorem exists_blocks_of_upper {K : Type} [Field K] {n a b : ℕ} (h : a + b = n) (p : GL (Fin n) K)
    (hp : p.1.BlockTriangular id) :
    ∃ (m₁ : GL (Fin a) K) (m₂ : GL (Fin b) K) (Y : Matrix (Fin a) (Fin b) K),
      Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (Matrix.fromBlocks m₁.val (m₁.val * Y) 0 m₂.val) = p.val := by
  set e : Fin a ⊕ Fin b ≃ Fin n := finSumFinEquiv.trans (finCongr h) with he
  set M : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) K := p.val.submatrix e e with hM
  have h21 : M.toBlocks₂₁ = 0 := by
    refine Matrix.ext fun i j => hp ?_
    change (e (Sum.inl j) : ℕ) < e (Sum.inr i)
    simp [he]
    omega
  have hMb : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
    rw [← h21]; exact (Matrix.fromBlocks_toBlocks M).symm
  have hdet : M.det ≠ 0 := by
    rw [hM, Matrix.det_submatrix_equiv_self]
    exact Matrix.GeneralLinearGroup.det_ne_zero p
  have hprod : M.toBlocks₁₁.det * M.toBlocks₂₂.det ≠ 0 := by
    rw [hMb, Matrix.det_fromBlocks_zero₂₁] at hdet
    simpa using hdet
  have hA : IsUnit M.toBlocks₁₁ :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (left_ne_zero_of_mul hprod))
  have hD : IsUnit M.toBlocks₂₂ :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (right_ne_zero_of_mul hprod))
  refine ⟨hA.unit, hD.unit, (hA.unit⁻¹ : GL (Fin a) K).val * M.toBlocks₁₂, ?_⟩
  have hAB : hA.unit.val * ((hA.unit⁻¹ : GL (Fin a) K).val * M.toBlocks₁₂) = M.toBlocks₁₂ := by
    rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  rw [hAB]
  change Matrix.reindex e e (Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂) = p.val
  rw [← hMb, hM]
  ext i j
  simp

/- English proof (translation)
Introduce `E _ _ _ n a b h w g`. Take `⟨k, c, hc, hg⟩` from `GlobalTheory.ValIwasawa.iwasawa (w.adicCompletionIntegers E) (w.adicCompletion E) n g⁻¹`. Establish `hk : Matrix.GeneralLinearGroup.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) k ∈ GlobalTheory.LFun.KGL w n` using `⟨k, rfl⟩`. Establish `hc' : (c⁻¹).1.BlockTriangular id` using `by haveI : Invertible c.1 := Units.invertible c`. Rewrite using `[Matrix.coe_units_inv]`.

Conclude with `Matrix.blockTriangular_inv_of_blockTriangular hc`. Take `⟨m₁, m₂, Y, hY⟩` from `exists_blocks_of_upper h c⁻¹ hc'`. Establish `hblk : blk h w (m₁, m₂) Y = c⁻¹`. Establish `hU : IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h)) (Matrix.fromBlocks m₁.val (m₁.val * Y) 0 m₂.val))`. Rewrite using `[hY]`.

Conclude with `(c⁻¹).isUnit`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [blk]`. Rewrite using `[dif_pos hU, IsUnit.unit_spec]`. Conclude with `hY`.

Use `⟨(m₁, m₂), Y, _, inv_mem hk, ?_⟩` and prove the remaining obligations. Rewrite using `[hblk, ← inv_inv g, hg, _root_.mul_inv_rev]`.
-/
theorem iwasawa_parabolic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E)
    (g : GLw n w), ∃ (m : GLw a w × GLw b w) (Y : Matrix (Fin a) (Fin b) (w.adicCompletion E)),
      ∃ k ∈ GlobalTheory.LFun.KGL w n, g = blk h w m Y * k := by
  intro E _ _ _ n a b h w g
  obtain ⟨k, c, hc, hg⟩ := GlobalTheory.ValIwasawa.iwasawa (w.adicCompletionIntegers E) (w.adicCompletion E) n g⁻¹
  have hk : Matrix.GeneralLinearGroup.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) k ∈
      GlobalTheory.LFun.KGL w n := ⟨k, rfl⟩
  have hc' : (c⁻¹).1.BlockTriangular id := by
    haveI : Invertible c.1 := Units.invertible c
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hc
  obtain ⟨m₁, m₂, Y, hY⟩ := exists_blocks_of_upper h c⁻¹ hc'
  have hblk : blk h w (m₁, m₂) Y = c⁻¹ := by
    have hU : IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (Matrix.fromBlocks m₁.val (m₁.val * Y) 0 m₂.val)) := by
      rw [hY]; exact (c⁻¹).isUnit
    apply Units.ext
    simp only [blk]
    rw [dif_pos hU, IsUnit.unit_spec]
    exact hY
  refine ⟨(m₁, m₂), Y, _, inv_mem hk, ?_⟩
  rw [hblk, ← inv_inv g, hg, _root_.mul_inv_rev]

end GlobalTheory.CompanionTheory.IwaBlock
