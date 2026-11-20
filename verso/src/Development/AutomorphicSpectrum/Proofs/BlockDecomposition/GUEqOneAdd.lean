import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsFieldIdemOne
open MeasureTheory Topology Filter GlobalTheory.CompanionTheory.NullFr
open scoped NNReal ENNReal Matrix

namespace GlobalTheory.CompanionTheory.NullFr

/- English proof (translation)
Unfold `gU`. Use `congr 1`. Use extensionality with `k j`. Simplify using `[Matrix.mul_apply, Pi.single_apply]`.
-/
theorem gU_eq_one_add {A : Type} [CommRing A] {t : ℕ} (i : Fin t) (c₀ : Fin t → A) :
    gU i c₀ = 1 + Matrix.replicateCol Unit c₀ * Matrix.replicateRow Unit (Pi.single i (1 : A) : Fin t → A) := by
  unfold gU
  congr 1
  ext k j
  simp [Matrix.mul_apply, Pi.single_apply]

/- English proof (translation)
Rewrite using `[gU_eq_one_add, Matrix.det_one_add_replicateCol_mul_replicateRow]`. Simplify using `[h]`.
-/
theorem det_gU {A : Type} [CommRing A] {t : ℕ} (i : Fin t) (c₀ : Fin t → A) (h : c₀ i = 0) :
    (gU i c₀).det = 1 := by
  rw [gU_eq_one_add, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [h]

/- English proof (translation)
Introduce `A _ t i c₀ h`. Use `⟨Matrix.GeneralLinearGroup.mk'' (GlobalTheory.CompanionTheory.NullFr.gU i c₀) (by rw [GlobalTheory.CompanionTheory.NullFr.det_gU i c₀ h]; exact isUnit_one), rfl, ?_⟩` and prove the remaining obligations. Use `ext`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]`. Conclude with `GlobalTheory.CompanionTheory.NullFr.det_gU i c₀ h`.
-/
theorem exists_GL_gU : ∀ {A : Type} [CommRing A] {t : ℕ} (i : Fin t) (c₀ : Fin t → A) (_ : c₀ i = 0),
    ∃ g : GL (Fin t) A, g.1 = gU i c₀ ∧ Matrix.GeneralLinearGroup.det g = 1 := by
  intro A _ t i c₀ h
  refine ⟨Matrix.GeneralLinearGroup.mk'' (GlobalTheory.CompanionTheory.NullFr.gU i c₀)
    (by rw [GlobalTheory.CompanionTheory.NullFr.det_gU i c₀ h]; exact isUnit_one), rfl, ?_⟩
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  exact GlobalTheory.CompanionTheory.NullFr.det_gU i c₀ h

end GlobalTheory.CompanionTheory.NullFr
