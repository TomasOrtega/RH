import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRedMap
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitProjAdeleComponentChartProperties
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceMatrixCoordinateOnHalf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepVec.HalfCmp

variable {D : D7}

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem toEAf_surjective : Function.Surjective (toEAf D) := by
  intro y
  have hs : Function.Surjective (finPart D) := by
    have h1 : Function.Surjective (sndA D.host.F) := fun b => ⟨(0, b), rfl⟩
    exact TensorProduct.map_surjective (g := (sndA D.host.F).toLinearMap) h1
      (g' := (AlgHom.id D.host.F D.host.E).toLinearMap) Function.surjective_id
  obtain ⟨z, hz⟩ := hs ((Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm y)
  refine ⟨z, ?_⟩
  change (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E) (finPart D z) = y
  rw [hz]; exact AlgEquiv.apply_symm_apply _ _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem gl_map_val {n : ℕ} {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (g : GL (Fin n) R) :
    (Matrix.GeneralLinearGroup.map f g).val = g.val.map f := rfl

end GlobalTheory.StepVec.HalfCmp

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
open GlobalTheory.StepVec.HalfCmp in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Replace the relevant objects with their definitions. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Consider separately whether the proposition holds or fails.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem GlobalTheory.StepVec.onHalf_viaRed_eq_locFn : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (e : AE D) (PP : Formalism.L2.DIV.Pl D.host.E)
    (r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP), IsIdemOf φ e → IsProjAt φ PP → IsRedMap φ PP r →
    ∀ (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (ω : Matrix (Fin T.rank) (Fin S.rank) (Formalism.L2.DIV.kP PP) → ℂ),
      onHalf φ S T (frCo φ βS) (frCo φ βT) e (viaRed r ω) = locFn S T βS βT e PP ω := by
  intro D v φ e PP r he hP hr S T βS βT ω
  obtain ⟨hchart, hcomp, -⟩ := GlobalTheory.SplitProjChart.chart_rdA D v φ e he
  funext t
  set N := frMapO S T βS βT t with hNdef
  have h1 : mapCo φ S T (frCo φ βS) (frCo φ βT) t = N.map (rdE φ) := by
    rw [hNdef]
    unfold mapCo frCo frMapO
    rw [Matrix.map_mul, Matrix.map_mul, ← map_inv, gl_map_val, gl_map_val, Matrix.map_map]
    congr 2
    ext i j
    simp [Function.comp, hcomp]
  unfold onHalf locFn
  by_cases hh : IsHalf e t
  swap
  · rw [if_neg hh, if_neg (fun h => hh h.1)]
  rw [if_pos hh, h1]
  have hfix : ∀ i j, toEAf D e * N i j = N i j := by
    intro i j
    have : toEAf D e • N = N := by
      rw [hNdef]; unfold frMapO
      rw [← Matrix.smul_mul, ← Matrix.mul_smul]
      congr 2
      ext k l
      simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, ← map_mul, hh k l]
    exact congrFun (congrFun this i) j
  have hiff : (∀ i j, (N.map (rdE φ)) i j ∈ v.adicCompletionIntegers D.host.F) ↔ IsIntM N := by
    constructor
    · intro h i j
      obtain ⟨a, ha⟩ := toEAf_surjective (N i j)
      have h2 : GlobalTheory.SplitHecke.IsInt (GlobalTheory.SplitHecke.Ov D v) (rdA φ a) := by
        rw [GlobalTheory.SplitHecke.isInt_Ov, ← hcomp, ha]; exact h i j
      have h3 := (hchart.2.2.2 a).2 h2
      have h4 := GlobalTheory.PlaceCoord.toEAf_mem h3
      rwa [map_mul, ha, hfix] at h4
    · intro h i j
      exact (hr.2.2.2 (N i j) (h i j)).1
  unfold viaRed
  by_cases hI : IsIntM N
  · rw [dif_pos (hiff.2 hI), if_pos ⟨hh, hI⟩]
    congr 1
    ext i j
    obtain ⟨hm, hm'⟩ := hr.2.2.2 (N i j) (hI i j)
    simp only [Matrix.of_apply, Matrix.map_apply]
    unfold redM
    rw [dif_pos (hI i j), ← hm']
  · rw [dif_neg (fun h => hI (hiff.1 h)), if_neg (fun h => hI h.2)]
