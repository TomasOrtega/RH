import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private noncomputable def dotPerp (U : Submodule ℂ (ι → ℂ)) : Submodule ℂ (ι → ℂ) :=
  U.dualAnnihilator.comap (dotProductEquiv ℂ ι).toLinearMap

/- English proof (translation)
Simplify using `[dotPerp, Submodule.mem_dualAnnihilator, dotProductEquiv]`.
-/
private theorem mem_dotPerp (U : Submodule ℂ (ι → ℂ)) (v : ι → ℂ) :
    v ∈ dotPerp U ↔ ∀ w ∈ U, v ⬝ᵥ w = 0 := by
  simp [dotPerp, Submodule.mem_dualAnnihilator, dotProductEquiv]

/- English proof (translation)
The claim follows from `(Submodule.orderIsoMapComap (dotProductEquiv ℂ ι)).symm.isCompl (Subspace.isCompl_dualAnnihilator h)`.
-/
private theorem dotPerp_isCompl {U U' : Submodule ℂ (ι → ℂ)} (h : IsCompl U U') :
    IsCompl (dotPerp U) (dotPerp U') :=
  (Submodule.orderIsoMapComap (dotProductEquiv ℂ ι)).symm.isCompl (Subspace.isCompl_dualAnnihilator h)

/- English proof (translation)
Use extensionality with `v`. Prove the components needed by the constructor for the conclusion. Introduce `hv`. Rewrite using `[← Subspace.dualAnnihilator_dualCoannihilator_eq (W := U), Submodule.mem_dualCoannihilator]`. Introduce `φ hφ`.

Take `⟨w, rfl⟩` from `(dotProductEquiv ℂ ι).surjective φ`. Establish `h` using `(mem_dotPerp _ v).1 hv w hφ`. Rewrite `h` using `[dotProduct_comm]`. Simplify `h` using `[dotProductEquiv]`. Introduce `hv`.

Rewrite using `[mem_dotPerp]`. Introduce `w hw`. Rewrite using `[dotProduct_comm]`. Conclude with `(mem_dotPerp _ w).1 hw v hv`.
-/
private theorem dotPerp_dotPerp (U : Submodule ℂ (ι → ℂ)) : dotPerp (dotPerp U) = U := by
  ext v
  constructor
  · intro hv
    rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := U), Submodule.mem_dualCoannihilator]
    intro φ hφ
    obtain ⟨w, rfl⟩ := (dotProductEquiv ℂ ι).surjective φ
    have h := (mem_dotPerp _ v).1 hv w hφ
    rw [dotProduct_comm] at h
    simpa [dotProductEquiv] using h
  · intro hv
    rw [mem_dotPerp]
    intro w hw
    rw [dotProduct_comm]
    exact (mem_dotPerp _ w).1 hw v hv

/- English proof (translation)
Introduce `v hv`. Rewrite `hv`, the goal using `[mem_dotPerp]`. Introduce `w hw`. Rewrite using `[Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]`. Conclude with `hv _ (h w hw)`.
-/
private theorem dotPerp_invariant (U : Submodule ℂ (ι → ℂ)) (g : Matrix ι ι ℂ)
    (h : ∀ v ∈ U, g *ᵥ v ∈ U) : ∀ v ∈ dotPerp U, gᵀ *ᵥ v ∈ dotPerp U := by
  intro v hv
  rw [mem_dotPerp] at hv ⊢
  intro w hw
  rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
  exact hv _ (h w hw)

/- English proof (translation)
Introduce `ι _ _ Γ hΓ W hW`. Take `⟨U', hU', hc⟩` from `hΓ (dotPerp W) (fun g hg => by`. Simplify using `using dotPerp_invariant W gᵀ (hW _ ⟨g, hg, rfl⟩))`. Use `⟨dotPerp U', ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨g, hg, rfl⟩`.

Conclude with `dotPerp_invariant U' g (hU' g hg)`. Use `dotPerp_isCompl hc` as an intermediate fact. Rewrite `this` using `[dotPerp_dotPerp]`. Then use the resulting hypothesis.
-/
theorem ss_transpose :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), SS Γ → SS (Matrix.transpose '' Γ) := by
  intro ι _ _ Γ hΓ W hW
  obtain ⟨U', hU', hc⟩ := hΓ (dotPerp W) (fun g hg => by
    simpa using dotPerp_invariant W gᵀ (hW _ ⟨g, hg, rfl⟩))
  refine ⟨dotPerp U', ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    exact dotPerp_invariant U' g (hU' g hg)
  · have := dotPerp_isCompl hc
    rwa [dotPerp_dotPerp] at this

end GlobalTheory.ClassFin
