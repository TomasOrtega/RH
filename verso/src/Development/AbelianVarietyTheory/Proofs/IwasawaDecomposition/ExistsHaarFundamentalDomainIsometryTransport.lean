import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Isom

/- English proof (translation)
Introduce `D V V' I S μ 𝓕 hμ h𝓕`. Use `haveI hB : BorelSpace (WO S V) := ⟨rfl⟩`. Use `haveI hB' : BorelSpace (WO S V') := ⟨rfl⟩`. Establish `hc` using `I.continuous_phi S`. Establish `hcs` using `I.continuous_phi_symm S`.

Establish `hrat : ∀ x, I.phi S x ∈ ratL V' S ↔ x ∈ ratL V S`. Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz⟩`. Use `⟨I.Q * z, ?_⟩` and prove the remaining obligations.

Establish `h1` using `I.symm.phi_ratW S z`. Establish `h2 : ratW V' S z = I.phi S x` using `hz`. Rewrite `h1` using `[h2, ← I.phi_symm_apply, AddEquiv.symm_apply_apply]`. Conclude with `h1.symm`. Introduce and unpack `⟨z, hz⟩`.

Use `⟨I.P * z, ?_⟩` and prove the remaining obligations. Establish `h1` using `I.phi_ratW S z`. Establish `h2 : ratW V S z = x` using `hz`. Rewrite `h1` using `[h2]`. Conclude with `h1.symm`.

Set `m : WO S V ≃ᵐ WO S V'` to `{ toEquiv := (I.phi S).toEquiv measurable_toFun := hc.measurable measurable_invFun := hcs.measurable }`. Establish `hmp : MeasurePreserving m (μ.map m.symm) μ` using `(MeasurePreserving.symm m.symm ⟨m.symm.measurable, rfl⟩)`. Establish `hmp' : MeasurePreserving (I.phi S) (μ.map (I.phi S).symm) μ` using `hmp`. Use `⟨μ.map (I.phi S).symm, I.phi S ⁻¹' 𝓕, AddEquiv.isAddHaarMeasure_map μ (I.phi S).symm hcs (by simpa using hc), ?_, ?_⟩` and prove the remaining obligations. Set `f : ratL V' S → ratL V S` to `fun y => ⟨(I.phi S).symm y, (hrat _).1 (by simpa using y.2)⟩`.

Establish `hf : Function.Bijective f`. Prove the components needed by the constructor for the conclusion. Introduce `a b hab`. Conclude with `Subtype.ext ((I.phi S).symm.injective (congrArg Subtype.val hab))`. Introduce `x`.

Conclude with `⟨⟨I.phi S x, (hrat _).2 x.2⟩, Subtype.ext (by simp [f])⟩`. Use `h𝓕.preimage_of_equiv hmp'.quasiMeasurePreserving hf ?_` and prove the remaining obligations. Introduce `y x`. Simplify using `[f, AddSubgroup.vadd_def]`. Introduce `u`.

Use `hmp'.setLIntegral_comp_preimage_emb m.measurableEmbedding (fun b => u ((I.phi S).symm b)) 𝓕` as an intermediate fact. Simplify using `using this.symm`.
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
