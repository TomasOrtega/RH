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
Establish `a1 : m.1.val * (m.1⁻¹).val = 1` using `Units.mul_inv m.1`. Establish `a2 : (m.1⁻¹).val * m.1.val = 1` using `Units.inv_mul m.1`. Establish `b1 : m.2.val * (m.2⁻¹).val = 1` using `Units.mul_inv m.2`. Establish `b2 : (m.2⁻¹).val * m.2.val = 1` using `Units.inv_mul m.2`. Establish `h1 : fromBlocks m.1.val (m.1.val * X) 0 m.2.val * fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val = 1`.

Rewrite using `[fromBlocks_multiply, ← fromBlocks_one]`. Use `congr 1`. Simplify using `[a1]`. Simplify using `[Matrix.mul_assoc]`. Simplify using the standard rewrite rules.

Simplify using `[b1]`. Establish `h2 : fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val * fromBlocks m.1.val (m.1.val * X) 0 m.2.val = 1`. Rewrite using `[fromBlocks_multiply, ← fromBlocks_one]`. Use `congr 1`. Simplify using `[a2]`.

Simplify using `[← Matrix.mul_assoc, a2, Matrix.mul_assoc, b2]`. Simplify using the standard rewrite rules. Simplify using `[b2]`. Establish `r1 : reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h)) (fromBlocks m.1.val (m.1.val * X) 0 m.2.val) * reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h)) (fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val) = 1`. Simplify using `only [reindex_apply, submatrix_mul_equiv, h1, submatrix_one_equiv]`.

Establish `r2 : reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h)) (fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val) * reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h)) (fromBlocks m.1.val (m.1.val * X) 0 m.2.val) = 1`. Simplify using `only [reindex_apply, submatrix_mul_equiv, h2, submatrix_one_equiv]`. Establish `hU : IsUnit (reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h)) (fromBlocks m.1.val (m.1.val * X) 0 m.2.val))` using `⟨⟨_, _, r1, r2⟩, rfl⟩`. Establish `hb : (blk h w m X).val = reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h)) (fromBlocks m.1.val (m.1.val * X) 0 m.2.val)`. Unfold `blk`.

Simplify using `only []`. Rewrite using `[dif_pos hU]`. Both sides reduce to the same expression. Conclude with `Units.inv_eq_of_mul_eq_one_right (by rw [hb]; exact r1)`.
-/
theorem blk_inv_val {E : Type} [Field E] [NumberField E] {n a b : ℕ} (h : a + b = n) (w : Pl E)
    (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    ((blk h w m X)⁻¹).val =
      reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val) := by
  have a1 : m.1.val * (m.1⁻¹).val = 1 := Units.mul_inv m.1
  have a2 : (m.1⁻¹).val * m.1.val = 1 := Units.inv_mul m.1
  have b1 : m.2.val * (m.2⁻¹).val = 1 := Units.mul_inv m.2
  have b2 : (m.2⁻¹).val * m.2.val = 1 := Units.inv_mul m.2
  have h1 : fromBlocks m.1.val (m.1.val * X) 0 m.2.val *
      fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val = 1 := by
    rw [fromBlocks_multiply, ← fromBlocks_one]
    congr 1
    · simp [a1]
    · simp [Matrix.mul_assoc]
    · simp
    · simp [b1]
  have h2 : fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val *
      fromBlocks m.1.val (m.1.val * X) 0 m.2.val = 1 := by
    rw [fromBlocks_multiply, ← fromBlocks_one]
    congr 1
    · simp [a2]
    · simp [← Matrix.mul_assoc, a2, Matrix.mul_assoc, b2]
    · simp
    · simp [b2]
  have r1 : reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (fromBlocks m.1.val (m.1.val * X) 0 m.2.val) *
      reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val) = 1 := by
    simp only [reindex_apply, submatrix_mul_equiv, h1, submatrix_one_equiv]
  have r2 : reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val) *
      reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (fromBlocks m.1.val (m.1.val * X) 0 m.2.val) = 1 := by
    simp only [reindex_apply, submatrix_mul_equiv, h2, submatrix_one_equiv]
  have hU : IsUnit (reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (fromBlocks m.1.val (m.1.val * X) 0 m.2.val)) := ⟨⟨_, _, r1, r2⟩, rfl⟩
  have hb : (blk h w m X).val = reindex (finSumFinEquiv.trans (finCongr h))
      (finSumFinEquiv.trans (finCongr h)) (fromBlocks m.1.val (m.1.val * X) 0 m.2.val) := by
    unfold blk
    simp only []
    rw [dif_pos hU]
    rfl
  exact Units.inv_eq_of_mul_eq_one_right (by rw [hb]; exact r1)

/- English proof (translation)
Introduce `E _ _ _ n a b h w ϖ m X`. Rewrite using `[blk_inv_val h w m X]`. Prove the components needed by the constructor for the conclusion. Introduce `H`. Establish `key : ∀ (i j : Fin a ⊕ Fin b), ϖ * fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val i j ∈ Ov E w`.

Introduce `i j`. Use `H (finSumFinEquiv.trans (finCongr h) i) (finSumFinEquiv.trans (finCongr h) j)` as an intermediate fact. Simplify `this` using `[reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul]`. Use `⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Simplify `key (Sum.inl i) (Sum.inl j)` using `[Matrix.smul_apply, smul_eq_mul]`.

Simplify `key (Sum.inr i) (Sum.inr j)` using `[Matrix.smul_apply, smul_eq_mul]`. Use `(Ov E w).neg_mem (key (Sum.inl i) (Sum.inr j))` as an intermediate fact. Simplify `this` using `[Matrix.smul_apply, smul_eq_mul]`. Introduce and unpack `⟨H1, H2, H3⟩ i j`. Establish `key : ∀ (i j : Fin a ⊕ Fin b), ϖ * fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val i j ∈ Ov E w`.

Introduce and unpack `(i | i) (j | j)`. Simplify `H1 i j` using `[Matrix.smul_apply, smul_eq_mul]`. Use `(Ov E w).neg_mem (H3 i j)` as an intermediate fact. Simplify `this` using `[Matrix.smul_apply, smul_eq_mul]`. Simplify using `using (Ov E w).zero_mem`.

Simplify `H2 i j` using `[Matrix.smul_apply, smul_eq_mul]`. Simplify `key ((finSumFinEquiv.trans (finCongr h)).symm i) ((finSumFinEquiv.trans (finCongr h)).symm j)` using `[reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul]`.
-/
theorem isInt_smul_blk_inv_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (ϖ : w.adicCompletion E) (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsInt w (ϖ • ((blk h w m X)⁻¹).val) ↔ IsInt w (ϖ • (m.1⁻¹).val) ∧ IsInt w (ϖ • (m.2⁻¹).val) ∧ IsInt w (ϖ • (X * (m.2⁻¹).val)) := by
  intro E _ _ _ n a b h w ϖ m X
  rw [blk_inv_val h w m X]
  constructor
  · intro H
    have key : ∀ (i j : Fin a ⊕ Fin b), ϖ * fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val i j ∈ Ov E w := by
      intro i j
      have := H (finSumFinEquiv.trans (finCongr h) i) (finSumFinEquiv.trans (finCongr h) j)
      simpa [reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul] using this
    refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
    · simpa [Matrix.smul_apply, smul_eq_mul] using key (Sum.inl i) (Sum.inl j)
    · simpa [Matrix.smul_apply, smul_eq_mul] using key (Sum.inr i) (Sum.inr j)
    · have := (Ov E w).neg_mem (key (Sum.inl i) (Sum.inr j))
      simpa [Matrix.smul_apply, smul_eq_mul] using this
  · rintro ⟨H1, H2, H3⟩ i j
    have key : ∀ (i j : Fin a ⊕ Fin b), ϖ * fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val i j ∈ Ov E w := by
      rintro (i | i) (j | j)
      · simpa [Matrix.smul_apply, smul_eq_mul] using H1 i j
      · have := (Ov E w).neg_mem (H3 i j)
        simpa [Matrix.smul_apply, smul_eq_mul] using this
      · simpa using (Ov E w).zero_mem
      · simpa [Matrix.smul_apply, smul_eq_mul] using H2 i j
    simpa [reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul] using
      key ((finSumFinEquiv.trans (finCongr h)).symm i) ((finSumFinEquiv.trans (finCongr h)).symm j)

end GlobalTheory.CompanionTheory.CtS
