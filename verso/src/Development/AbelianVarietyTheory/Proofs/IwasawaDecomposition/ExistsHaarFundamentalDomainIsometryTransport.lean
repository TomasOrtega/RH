import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Isom

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Introduce a local definition for the expression. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses.

Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem haar_fd_phi : ∀ (D : D7) (V V' : HSp D) (I : GlobalTheory.Mem.Isom.IsoMat V V') (S : HSp D) (μ : Measure (WO S V')) (𝓕 : Set (WO S V')), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL V' S) 𝓕 μ → ∃ (ν : Measure (WO S V)) (𝓖 : Set (WO S V)), ν.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratL V S) 𝓖 ν ∧ ∀ u : WO S V → ENNReal, ∫⁻ w in 𝓕, u ((I.phi S).symm w) ∂μ = ∫⁻ w in 𝓖, u w ∂ν := by
  intro D V V' I S μ 𝓕 hμ h𝓕
  haveI hB : BorelSpace (WO S V) := ⟨rfl⟩
  haveI hB' : BorelSpace (WO S V') := ⟨rfl⟩
  have hc := I.continuous_phi S
  have hcs := I.continuous_phi_symm S
  have hrat : ∀ x, I.phi S x ∈ ratL V' S ↔ x ∈ ratL V S := by
    intro x
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨I.Q * z, ?_⟩
      have h1 := I.symm.phi_ratW S z
      have h2 : ratW V' S z = I.phi S x := hz
      rw [h2, ← I.phi_symm_apply, AddEquiv.symm_apply_apply] at h1
      exact h1.symm
    · rintro ⟨z, hz⟩
      refine ⟨I.P * z, ?_⟩
      have h1 := I.phi_ratW S z
      have h2 : ratW V S z = x := hz
      rw [h2] at h1
      exact h1.symm
  let m : WO S V ≃ᵐ WO S V' :=
    { toEquiv := (I.phi S).toEquiv
      measurable_toFun := hc.measurable
      measurable_invFun := hcs.measurable }
  have hmp : MeasurePreserving m (μ.map m.symm) μ :=
    (MeasurePreserving.symm m.symm ⟨m.symm.measurable, rfl⟩)
  have hmp' : MeasurePreserving (I.phi S) (μ.map (I.phi S).symm) μ := hmp
  refine ⟨μ.map (I.phi S).symm, I.phi S ⁻¹' 𝓕, AddEquiv.isAddHaarMeasure_map μ (I.phi S).symm hcs (by simpa using hc), ?_, ?_⟩
  · let f : ratL V' S → ratL V S := fun y => ⟨(I.phi S).symm y, (hrat _).1 (by simpa using y.2)⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b hab
        exact Subtype.ext ((I.phi S).symm.injective (congrArg Subtype.val hab))
      · intro x
        exact ⟨⟨I.phi S x, (hrat _).2 x.2⟩, Subtype.ext (by simp [f])⟩
    refine h𝓕.preimage_of_equiv hmp'.quasiMeasurePreserving hf ?_
    intro y x
    simp [f, AddSubgroup.vadd_def]
  · intro u
    have := hmp'.setLIntegral_comp_preimage_emb m.measurableEmbedding (fun b => u ((I.phi S).symm b)) 𝓕
    simpa using this.symm

end GlobalTheory.Mem.Isom
