import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace KLinesCoordDet

variable {K : Type} [Field K] {n m k : ℕ} (B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K))
  (b : Fin m → Fin n → K) (c : Fin k → Fin n → K)

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[toBlocks₁₁, of_apply, Module.Basis.toMatrix_apply, Sum.elim_inl, ← hb, Module.Basis.repr_self, Finsupp.single_apply, one_apply]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[if_neg (fun e => h (Sum.inl_injective e).symm), if_neg h]`.
-/
theorem toBlocks₁₁_eq (hb : ∀ i, B (Sum.inl i) = b i) :
    (B.toMatrix (Sum.elim b c)).toBlocks₁₁ = 1 := by
  ext i j
  rw [toBlocks₁₁, of_apply, Module.Basis.toMatrix_apply, Sum.elim_inl, ← hb, Module.Basis.repr_self,
    Finsupp.single_apply, one_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg (fun e => h (Sum.inl_injective e).symm), if_neg h]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[toBlocks₂₁, of_apply, Module.Basis.toMatrix_apply, Sum.elim_inl, ← hb, Module.Basis.repr_self, Finsupp.single_apply, Matrix.zero_apply, if_neg Sum.inl_ne_inr]`.
-/
theorem toBlocks₂₁_eq (hb : ∀ i, B (Sum.inl i) = b i) :
    (B.toMatrix (Sum.elim b c)).toBlocks₂₁ = 0 := by
  ext i j
  rw [toBlocks₂₁, of_apply, Module.Basis.toMatrix_apply, Sum.elim_inl, ← hb, Module.Basis.repr_self,
    Finsupp.single_apply, Matrix.zero_apply, if_neg Sum.inl_ne_inr]

/- English proof (translation)
Use `set P := B.toMatrix (Sum.elim b c) with hPdef`. Establish `hP : P = fromBlocks 1 P.toBlocks₁₂ 0 P.toBlocks₂₂`. Rewrite using `[← toBlocks₁₁_eq B b c hb, ← toBlocks₂₁_eq B b c hb, fromBlocks_toBlocks]`. Use `conv_lhs => rw [hP]`. Rewrite using `[det_fromBlocks_zero₂₁, det_one, one_mul]`.
-/
theorem det_eq (hb : ∀ i, B (Sum.inl i) = b i) :
    (B.toMatrix (Sum.elim b c)).det = (B.toMatrix (Sum.elim b c)).toBlocks₂₂.det := by
  set P := B.toMatrix (Sum.elim b c) with hPdef
  have hP : P = fromBlocks 1 P.toBlocks₁₂ 0 P.toBlocks₂₂ := by
    rw [← toBlocks₁₁_eq B b c hb, ← toBlocks₂₁_eq B b c hb, fromBlocks_toBlocks]
  conv_lhs => rw [hP]
  rw [det_fromBlocks_zero₂₁, det_one, one_mul]

/- English proof (translation)
Establish `hcard : Fintype.card (Fin m ⊕ Fin k) = Module.finrank K (Fin n → K)` using `(Module.finrank_eq_card_basis B).symm`. Set `v` to `basisOfLinearIndependentOfCardEqFinrank' (Sum.elim b c) hli hcard`. Establish `hv : (v : Fin m ⊕ Fin k → Fin n → K) = Sum.elim b c` using `coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _`. Establish `h` using `congrArg Matrix.det (Module.Basis.toMatrix_mul_toMatrix_flip B v)`. Rewrite `h` using `[det_mul, det_one, hv]`.

Conclude with `left_ne_zero_of_mul_eq_one h`.
-/
theorem det_ne_zero (hli : LinearIndependent K (Sum.elim b c)) :
    (B.toMatrix (Sum.elim b c)).det ≠ 0 := by
  have hcard : Fintype.card (Fin m ⊕ Fin k) = Module.finrank K (Fin n → K) :=
    (Module.finrank_eq_card_basis B).symm
  let v := basisOfLinearIndependentOfCardEqFinrank' (Sum.elim b c) hli hcard
  have hv : (v : Fin m ⊕ Fin k → Fin n → K) = Sum.elim b c :=
    coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  have h := congrArg Matrix.det (Module.Basis.toMatrix_mul_toMatrix_flip B v)
  rw [det_mul, det_one, hv] at h
  exact left_ne_zero_of_mul_eq_one h

end KLinesCoordDet

/- English proof (translation)
Introduce `K _ n m k B b c hb hli`. Conclude with `⟨KLinesCoordDet.det_eq B b c hb, KLinesCoordDet.det_eq B b c hb ▸ KLinesCoordDet.det_ne_zero B b c hli⟩`.
-/
theorem LinesCoordDet.proof : LinesCoordDet.Statement := by
  intro K _ n m k B b c hb hli
  exact ⟨KLinesCoordDet.det_eq B b c hb,
    KLinesCoordDet.det_eq B b c hb ▸ KLinesCoordDet.det_ne_zero B b c hli⟩

end GroundTheory.Heights₂.Heights
