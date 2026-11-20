import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThPDatumEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LevExt

variable {D : D7}

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem intAf_mul {a b : Af D.host.F} (ha : a ∈ intAf D.host.F) (hb : b ∈ intAf D.host.F) :
    a * b ∈ intAf D.host.F := by
  intro v
  rw [map_mul]
  exact mul_mem (ha v) (hb v)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result.

Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Treat this case separately. Treat this case separately.

Treat this case separately. A detailed English derivation is pending.
-/
theorem smul_mem_hatV {k : ℕ} (L : Lt D.host.E k) {a : Af D.host.F} (ha : a ∈ intAf D.host.F) :
    ∀ w ∈ hatV L, a • w ∈ hatV L := by
  intro w hw
  induction hw using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a', ha', x, hx, rfl⟩ := hy
    apply AddSubgroup.subset_closure
    refine ⟨a * a', intAf_mul ha ha', x, hx, ?_⟩
    funext i
    simp [TensorProduct.smul_tmul', smul_eq_mul]
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | neg y _ hy => rw [smul_neg]; exact neg_mem hy

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Treat this case separately. Treat this case separately.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Rewrite the conclusion using the stated equalities. Treat this case separately.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mulVec_sub_mem_hatV : ∀ (D : D7) {k : ℕ} (L L' : Lt D.host.E k) (m : Matrix (Fin k) (Fin k) (AfE D)),
    (∀ x ∈ L, m *ᵥ toAf x - toAf x ∈ hatV L') → ∀ u ∈ hatV L, m *ᵥ u - u ∈ hatV L' := by
  intro D k L L' m h u hu
  induction hu using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    have hy : (fun i => a ⊗ₜ[D.host.F] x i) = a • toAf (D := D) x := by
      funext i
      simp [toAf, TensorProduct.smul_tmul', smul_eq_mul]
    rw [hy, Matrix.mulVec_smul, ← smul_sub]
    exact smul_mem_hatV L' ha _ (h x hx)
  | zero => simp
  | add y z _ _ hy hz =>
    have : m *ᵥ (y + z) - (y + z) = (m *ᵥ y - y) + (m *ᵥ z - z) := by
      rw [Matrix.mulVec_add]; abel
    rw [this]; exact add_mem hy hz
  | neg y _ hy =>
    have : m *ᵥ (-y) - (-y) = -(m *ᵥ y - y) := by
      rw [Matrix.mulVec_neg]; abel
    rw [this]; exact neg_mem hy

end GlobalTheory.LevExt

end
