import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStdBaseChange
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.DualProjApply
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.ChartRestriction.G.AI.I1 NumberField Matrix

noncomputable section

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Supply the required witnesses or components. Supply the required witnesses or components. Treat this case separately.

Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Treat this case separately.

Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem single_mem_dualLattice_standard (K : Type) [Field K] [NumberField K] {i : ℕ} (j : Fin i) :
    (Pi.single j 1 : Fin i → K) ∈ dualLattice (HermLattice.standard K i) := by
  intro x hx
  rw [single_one_dotProduct]
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    by_cases h : j = k
    · subst h
      exact ⟨1, by simp⟩
    · exact ⟨0, by simp [h]⟩
  | zero => exact ⟨0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha⟩ := hy
    obtain ⟨c, hc⟩ := hz
    exact ⟨a + c, by simp [ha, hc]⟩
  | smul a y _ hy =>
    obtain ⟨c, hc⟩ := hy
    exact ⟨a * c, by simp [hc, Algebra.smul_def]⟩

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]

def dualStdCoordMat (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) :
    ∀ _ : Unit, Fin i → T → ℤ :=
  fun _ j t => b.repr ⟨Pi.single j 1, single_mem_dualLattice_standard K j⟩ t

omit [DecidableEq T] in

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem dualStdCoordMat_sum (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))) (j : Fin i) :
    ∑ t, dualStdCoordMat b () j t • (b t : Fin i → K) = Pi.single j 1 := by
  have h := congrArg (fun v : dualLattice (HermLattice.standard K i) => (v : Fin i → K))
    (b.sum_repr ⟨Pi.single j 1, single_mem_dualLattice_standard K j⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h
  exact h

def DualStdBasePtFree.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))),
    IsBasePtFree (K₂ := Unit) (ι₂ := PBlk i) (dualIdeal b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b))

def DualStdImageBot.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))),
    imageZ (inrV (ι := dualBlocks T) (ι₂ := PBlk i))
      (graphIdeal (dualIdeal b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b))) = ⊥

def DualStdGenDeg.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (G : GenFibre (inrV (ι := dualBlocks T) (ι₂ := PBlk i))
      (graphIdeal (dualIdeal b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b))))
    (J : IFamily G.Φ (fibreIdx (Sum.elim (dualBlocks T) (PBlk i)) (Sum.inr : Unit → Unit ⊕ Unit))),
    1 ≤ i → IsFieldIntersection J →
    J (fibreIdeal Sum.inr G) 0 Fin.elim0 = (Module.finrank ℚ K : ℤ)

def DualStdMetricPull.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))),
    ∀ z ∈ mcPts (dualIdeal b),
      (dualLine (HermLattice.standard K i) b hb).h z =
        (fsMulti (PBlk i)).h (linApply (ι₂ := PBlk i) (dualStdCoordMat b) z)

/- English proof (translation)
A detailed English derivation is pending.
-/
example : ∀ _ : Unit, Fin 1 → Unit → ℤ := dualStdCoordMat dualBasisStandard

/- English proof (translation)
Supply the required witnesses or components.
-/
example (hP : DualPtsOfPlane.Statement) :
    ∃ (b : Module.Basis Unit ℤ (dualLattice (HermLattice.standard ℚ 1)))
      (_ : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (z : (Σ _ : Unit, Unit) → ℂ),
      z ∈ mcPts (dualIdeal b) :=
  ⟨dualBasisStandard, dualEmbMatrix_standard_bijective, _,
    hP ℚ 1 _ Unit dualBasisStandard dualEmbMatrix_standard_bijective (Rat.castHom ℂ) (fun _ => 1)
      fun h => one_ne_zero (congrFun h 0)⟩

/- English proof (translation)
Supply the required witnesses or components.
-/
example : ∃ _ : Module.Basis Unit ℤ (dualLattice (HermLattice.standard ℚ 1)), 1 ≤ 1 :=
  ⟨dualBasisStandard, le_rfl⟩

end

end GroundTheory.Heights₂.Heights
