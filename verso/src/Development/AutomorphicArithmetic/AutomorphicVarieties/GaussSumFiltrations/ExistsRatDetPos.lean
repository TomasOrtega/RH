import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BasicForm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsEquivariantProjOfLeSumIrreducible
open NumberField GlobalTheory.BorelCoh UpperTheory.V.TR
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.WeakApproxGL

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem denseRange_inf (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    DenseRange ((pInf F).comp (algebraMap F (GlobalTheory.CuspRep.Ad F))) := by
  have hc : Continuous (infEq F).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      (continuous_apply w)
  exact (infEq F).symm.surjective.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap F) hc

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components. Both sides reduce to the same expression. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Split into cases according to the possible forms of the given data. Treat this case separately. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Treat this case separately.

Establish an intermediate fact. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules.

Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
