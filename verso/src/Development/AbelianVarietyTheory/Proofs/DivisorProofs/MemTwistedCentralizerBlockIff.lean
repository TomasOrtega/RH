import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfIntertwineOfIsCoprimeCharpoly

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LeviDesc.CentPar

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.IntertwinerCoprimeCharpoly.main`. Consider the case `exact _root_.GlobalTheory.IntertwinerCoprimeCharpoly.main`. Consider the case `(apply _root_.GlobalTheory.IntertwinerCoprimeCharpoly.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.IntertwinerCoprimeCharpoly.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.IntertwinerCoprimeCharpoly.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.IntertwinerCoprimeCharpoly.main ..)`.
-/
theorem intertwiner_eq_zero {K : Type} [Field K] {a b : ℕ}
    (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K)
    (hc : IsCoprime A.charpoly B.charpoly) (hC : C * A = B * C) : C = 0 := by
  first
  | exact @_root_.GlobalTheory.IntertwinerCoprimeCharpoly.main
  | exact _root_.GlobalTheory.IntertwinerCoprimeCharpoly.main
  | (apply _root_.GlobalTheory.IntertwinerCoprimeCharpoly.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntertwinerCoprimeCharpoly.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntertwinerCoprimeCharpoly.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntertwinerCoprimeCharpoly.main ..)

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish `hM : IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h)) (Matrix.fromBlocks m.1.val (m.1.val * (0 : Matrix (Fin a) (Fin b) (w.adicCompletion E))) 0 m.2.val))`. Rewrite using `[Matrix.isUnit_iff_isUnit_det, Matrix.det_reindex_self, Matrix.mul_zero, Matrix.det_fromBlocks_zero₁₂]`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).mp m.1.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).mp m.2.isUnit)`. Simplify using `only [blk]`. Rewrite using `[dif_pos hM]`.

Simplify using the standard rewrite rules.
-/
theorem blk_zero_val {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) :
    ((blk h w m 0 : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (Matrix.fromBlocks m.1.val 0 0 m.2.val) := by
  have hM : IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * (0 : Matrix (Fin a) (Fin b) (w.adicCompletion E))) 0 m.2.val)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_reindex_self, Matrix.mul_zero, Matrix.det_fromBlocks_zero₁₂]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp m.1.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).mp m.2.isUnit)
  simp only [blk]
  rw [dif_pos hM]
  simp

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, blk_zero_val, blk_zero_val, blk_zero_val]`. Simplify using `only [Matrix.reindex_apply]`. Rewrite using `[Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]`. Simplify using `[Prod.fst_mul, Prod.snd_mul]`.
-/
theorem blk_zero_mul {n a b : ℕ} (h : a + b = n) (w : Pl E) (x y : GLw a w × GLw b w) :
    blk h w (x * y) 0 = blk h w x 0 * blk h w y 0 := by
  apply Units.ext
  rw [Units.val_mul, blk_zero_val, blk_zero_val, blk_zero_val]
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [Prod.fst_mul, Prod.snd_mul]

end GlobalTheory.LeviDesc.CentPar

open GlobalTheory.LeviDesc.CentPar in

/- English proof (translation)
Introduce `E _ _ n a b h w m hsep hγ p`. Establish `hcop` using `hsep.isCoprime`. Establish `hmem : p ∈ twCent (MonoidHom.id _) (⟨blk h w m 0, hγ⟩ : GlobalTheory.LeviDesc.parP a n w) ↔ (p : GLw n w) * blk h w m 0 = blk h w m 0 * (p : GLw n w)` using `by show p * _ = _ * MonoidHom.id _ p ↔ _`. Rewrite using `[MonoidHom.id_apply, Subtype.ext_iff]`. Both sides reduce to the same expression.

Rewrite using `[hmem]`. Prove the components needed by the constructor for the conclusion. Introduce `hc set e := finSumFinEquiv.trans (finCongr h) with he set g' := Matrix.reindex e.symm e.symm ((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hg'`. Establish `hgg : ((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.reindex e e g'`. Simplify using `[hg']`.

Establish `hcM` using `congrArg Units.val hc`. Rewrite `hcM` using `[Units.val_mul, Units.val_mul, blk_zero_val, ← he, hgg, ← Matrix.fromBlocks_toBlocks g']`. Establish `hc2` using `congrArg (Matrix.reindex e.symm e.symm) hcM`. Simplify using `only [Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_mul_equiv, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id, Matrix.fromBlocks_multiply] at hc2`. Rewrite `hc2` using `[Matrix.fromBlocks_inj]`.

Take `⟨h11, h12, h21, h22⟩` from `hc2`. Simplify using `only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at h11 h12 h21 h22`. Establish `hC0 : g'.toBlocks₂₁ = 0` using `intertwiner_eq_zero _ _ _ hcop h21`. Establish `hB0 : g'.toBlocks₁₂ = 0` using `intertwiner_eq_zero _ _ _ hcop.symm h12`. Establish `hg'2 : g' = Matrix.fromBlocks g'.toBlocks₁₁ 0 0 g'.toBlocks₂₂`.

Rewrite using `[← hB0, ← hC0, Matrix.fromBlocks_toBlocks]`. Establish `hdet : IsUnit g'.det`. Rewrite using `[hg', Matrix.det_reindex_self]`. Conclude with `(Matrix.isUnit_iff_isUnit_det _).mp (p : GLw n w).isUnit`. Rewrite `hdet` using `[hg'2, Matrix.det_fromBlocks_zero₂₁]`.

Establish `hA : IsUnit g'.toBlocks₁₁` using `(Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_of_mul_isUnit_left hdet)`. Establish `hD : IsUnit g'.toBlocks₂₂` using `(Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_of_mul_isUnit_right hdet)`. Use `⟨(hA.unit, hD.unit), ?_, ?_⟩` and prove the remaining obligations. Use `show (hA.unit, hD.unit) * m = m * MonoidHom.id _ (hA.unit, hD.unit)`. Rewrite using `[MonoidHom.id_apply]`.

Use `Prod.ext (Units.ext ?_) (Units.ext ?_)` and prove the remaining obligations. Simplify using `using h11`. Simplify using `using h22`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[blk_zero_val, ← he, hgg]`.

Use `conv_rhs => rw [hg'2]`. Both sides reduce to the same expression. Introduce and unpack `⟨t, ht, hp⟩`. Establish `ht' : t * m = m * t` using `ht`. Rewrite using `[← hp, ← blk_zero_mul, ← blk_zero_mul, ht']`.
-/
theorem GlobalTheory.LeviDesc.mem_twistedCentralizer_parabolic_iff : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E)
    (m : GLw a w × GLw b w), (m.1.val.charpoly * m.2.val.charpoly).Separable →
    ∀ (hγ : blk h w m 0 ∈ GlobalTheory.LeviDesc.parP a n w) (p : GlobalTheory.LeviDesc.parP a n w),
      p ∈ twCent (MonoidHom.id _) (⟨blk h w m 0, hγ⟩ : GlobalTheory.LeviDesc.parP a n w) ↔
        ∃ t ∈ twCent (MonoidHom.id _) m, blk h w t 0 = (p : GLw n w) := by
  intro E _ _ n a b h w m hsep hγ p
  have hcop := hsep.isCoprime
  have hmem : p ∈ twCent (MonoidHom.id _) (⟨blk h w m 0, hγ⟩ : GlobalTheory.LeviDesc.parP a n w) ↔
      (p : GLw n w) * blk h w m 0 = blk h w m 0 * (p : GLw n w) := by
    show p * _ = _ * MonoidHom.id _ p ↔ _
    rw [MonoidHom.id_apply, Subtype.ext_iff]
    rfl
  rw [hmem]
  constructor
  · intro hc
    set e := finSumFinEquiv.trans (finCongr h) with he
    set g' := Matrix.reindex e.symm e.symm ((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hg'
    have hgg : ((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.reindex e e g' := by
      simp [hg']
    have hcM := congrArg Units.val hc
    rw [Units.val_mul, Units.val_mul, blk_zero_val, ← he, hgg, ← Matrix.fromBlocks_toBlocks g'] at hcM
    have hc2 := congrArg (Matrix.reindex e.symm e.symm) hcM
    simp only [Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_mul_equiv, Matrix.submatrix_submatrix,
      Equiv.symm_comp_self, Matrix.submatrix_id_id, Matrix.fromBlocks_multiply] at hc2
    rw [Matrix.fromBlocks_inj] at hc2
    obtain ⟨h11, h12, h21, h22⟩ := hc2
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at h11 h12 h21 h22
    have hC0 : g'.toBlocks₂₁ = 0 := intertwiner_eq_zero _ _ _ hcop h21
    have hB0 : g'.toBlocks₁₂ = 0 := intertwiner_eq_zero _ _ _ hcop.symm h12
    have hg'2 : g' = Matrix.fromBlocks g'.toBlocks₁₁ 0 0 g'.toBlocks₂₂ := by
      rw [← hB0, ← hC0, Matrix.fromBlocks_toBlocks]
    have hdet : IsUnit g'.det := by
      rw [hg', Matrix.det_reindex_self]
      exact (Matrix.isUnit_iff_isUnit_det _).mp (p : GLw n w).isUnit
    rw [hg'2, Matrix.det_fromBlocks_zero₂₁] at hdet
    have hA : IsUnit g'.toBlocks₁₁ := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_of_mul_isUnit_left hdet)
    have hD : IsUnit g'.toBlocks₂₂ := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_of_mul_isUnit_right hdet)
    refine ⟨(hA.unit, hD.unit), ?_, ?_⟩
    · show (hA.unit, hD.unit) * m = m * MonoidHom.id _ (hA.unit, hD.unit)
      rw [MonoidHom.id_apply]
      refine Prod.ext (Units.ext ?_) (Units.ext ?_)
      · simpa using h11
      · simpa using h22
    · apply Units.ext
      rw [blk_zero_val, ← he, hgg]
      conv_rhs => rw [hg'2]
      rfl
  · rintro ⟨t, ht, hp⟩
    have ht' : t * m = m * t := ht
    rw [← hp, ← blk_zero_mul, ← blk_zero_mul, ht']
