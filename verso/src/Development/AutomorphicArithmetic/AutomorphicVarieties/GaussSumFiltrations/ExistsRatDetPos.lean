import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BasicForm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsEquivariantProjOfLeSumIrreducible
open NumberField GlobalTheory.BorelCoh UpperTheory.V.TR
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.WeakApproxGL

/- English proof (translation)
Establish `hc : Continuous (infEq F).symm` using `continuous_pi fun w => (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp (continuous_apply w)`. Conclude with `(infEq F).symm.surjective.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap F) hc`.
-/
theorem denseRange_inf (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    DenseRange ((pInf F).comp (algebraMap F (GlobalTheory.CuspRep.Ad F))) := by
  have hc : Continuous (infEq F).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      (continuous_apply w)
  exact (infEq F).symm.surjective.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap F) hc

/- English proof (translation)
Introduce `F _ _ _ a g`. Use `set φ : F →+* (InfinitePlace F → ℝ) := (pInf F).comp (algebraMap F (GlobalTheory.CuspRep.Ad F)) with hφ`. Establish `hcomp : ∀ h : GL (Fin a) F, (((Matrix.GeneralLinearGroup.map (pInf F)).comp (GlobalTheory.CuspRep.ratGL F a)) h).val = (h.val).map φ` using `fun h => by`. Use extensionality with `i j`. Both sides reduce to the same expression.

Establish `hdu : IsUnit g.val.det` using `Matrix.isUnits_det_units g`. Establish `hd : ∀ v, g.val.det v ≠ 0` using `fun v => ((Pi.isUnit_iff.1 hdu) v).ne_zero`. Establish `hopen : IsOpen {y : InfinitePlace F → ℝ | ∀ v, 0 < y v * g.val.det v}`. Simplify using `only [Set.setOf_forall]`. Conclude with `isOpen_iInter_of_finite fun v => isOpen_lt continuous_const (by fun_prop)`.

Take `⟨t, ht⟩` from `(denseRange_inf F).exists_mem_open hopen ⟨fun v => (g.val.det v)⁻¹, fun v => by simp [hd v]⟩`. Establish `ht' : ∀ v, 0 < φ t v * g.val.det v` using `ht`. Consider the cases of `a with`. Consider the case `zero`. Use `⟨1, fun v => ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.det_isEmpty]`. Conclude with `one_pos`. Consider the case `succ n`. Establish `ht0 : t ≠ 0`. Introduce and unpack `rfl`.

Take `⟨v⟩` from `(inferInstance : Nonempty (InfinitePlace F))`. Use `ht' v` as an intermediate fact. Simplify using `at this`. Set `D : Matrix (Fin (n + 1)) (Fin (n + 1)) F` to `Matrix.diagonal (Function.update 1 0 t)`. Establish `hD : D.det = t`.

Rewrite using `[Matrix.det_diagonal, Fin.prod_univ_succ]`. Simplify using the standard rewrite rules. Use `⟨Matrix.GeneralLinearGroup.mkOfDetNeZero D (hD ▸ ht0), fun v => ?_⟩` and prove the remaining obligations. Establish `e : ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) F, (M.map φ).det = φ M.det` using `fun M => (RingHom.map_det φ M).symm`. Rewrite using `[Units.val_mul, Matrix.det_mul, hcomp, e, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hD]`.

Conclude with `ht' v`.
-/
theorem exists_rat_det_pos : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ)
    (g : GL (Fin a) (InfinitePlace F → ℝ)), ∃ h : GL (Fin a) F, ∀ v, 0 < ((((Matrix.GeneralLinearGroup.map (pInf F)).comp
      (GlobalTheory.CuspRep.ratGL F a)) h) * g).val.det v := by
  intro F _ _ _ a g
  set φ : F →+* (InfinitePlace F → ℝ) := (pInf F).comp (algebraMap F (GlobalTheory.CuspRep.Ad F)) with hφ
  have hcomp : ∀ h : GL (Fin a) F, (((Matrix.GeneralLinearGroup.map (pInf F)).comp (GlobalTheory.CuspRep.ratGL F a)) h).val
      = (h.val).map φ := fun h => by
    ext i j; rfl
  have hdu : IsUnit g.val.det := Matrix.isUnits_det_units g
  have hd : ∀ v, g.val.det v ≠ 0 := fun v => ((Pi.isUnit_iff.1 hdu) v).ne_zero
  have hopen : IsOpen {y : InfinitePlace F → ℝ | ∀ v, 0 < y v * g.val.det v} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun v => isOpen_lt continuous_const (by fun_prop)
  obtain ⟨t, ht⟩ := (denseRange_inf F).exists_mem_open hopen
    ⟨fun v => (g.val.det v)⁻¹, fun v => by simp [hd v]⟩
  have ht' : ∀ v, 0 < φ t v * g.val.det v := ht
  cases a with
  | zero =>
    refine ⟨1, fun v => ?_⟩
    rw [Matrix.det_isEmpty]
    exact one_pos
  | succ n =>
    have ht0 : t ≠ 0 := by
      rintro rfl
      obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace F))
      have := ht' v
      simp at this
    let D : Matrix (Fin (n + 1)) (Fin (n + 1)) F := Matrix.diagonal (Function.update 1 0 t)
    have hD : D.det = t := by
      rw [Matrix.det_diagonal, Fin.prod_univ_succ]
      simp
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero D (hD ▸ ht0), fun v => ?_⟩
    have e : ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) F, (M.map φ).det = φ M.det := fun M => (RingHom.map_det φ M).symm
    rw [Units.val_mul, Matrix.det_mul, hcomp, e, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hD]
    exact ht' v

end GlobalTheory.WeakApproxGL
