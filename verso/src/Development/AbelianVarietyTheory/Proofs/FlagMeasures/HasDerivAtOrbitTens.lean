import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrbitStepSpace
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrthonormalPlaceBasis
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousMultilinearMapOfInnerProd

open Formalism.MainNotions.S NumberField GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis

namespace GlobalTheory.TensDer

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem hasDerivAt_orbit_tens : ∀ (B : RowsAut) (E : gInf B) (u u' : ∀ v, B.H v), (∀ v, HasDerivAt (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit (B.σ v) (E v).1 (u v)) (u' v) 0) → (∀ v, B.σ v 1 = 1) → open Classical in HasDerivAt (orbit B E (B.tens u)) (∑ v, B.tens (Function.update u v (u' v))) 0 := by
  intro B E u u' hd h1
  classical
  obtain ⟨m, hm, -⟩ := GlobalTheory.rowsAut_tens_continuousMultilinear B
  have hfun : orbit B E (B.tens u) =
      fun t => (m.restrictScalars ℝ) (fun v => GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit (B.σ v) (E v).1 (u v) t) := by
    funext t
    have := B.tens_spec.2.1
    rw [ContinuousMultilinearMap.coe_restrictScalars, hm]
    unfold orbit
    rw [this]
    congr 1
  have h0 : (fun v => GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit (B.σ v) (E v).1 (u v) 0) = u := by
    funext v
    simp [GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit, h1]
  have hpi : HasDerivAt (fun t v => GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit (B.σ v) (E v).1 (u v) t) u' 0 :=
    hasDerivAt_pi.2 hd
  have hF := (m.restrictScalars ℝ).hasFDerivAt (fun v => GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit (B.σ v) (E v).1 (u v) 0)
  have := hF.comp_hasDerivAt (0 : ℝ) hpi
  rw [hfun]
  rw [h0, ContinuousMultilinearMap.linearDeriv_apply] at this
  simp only [ContinuousMultilinearMap.coe_restrictScalars, Function.comp_def, hm] at this ⊢
  exact this

end GlobalTheory.TensDer
