import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.InfAdeleTensorBijective

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

/- English proof (translation)
Introduce `D`. Establish `hτ : ∀ (τ : D.host.E →+* ℂ) (x : D.host.E), τ (cF D x) = starRingEnd ℂ (τ x)` using `fun τ x => IsCMField.complexEmbedding_complexConj D.host.E τ x`. Establish `hc : cF D ≠ 1`. Introduce `h`. Establish `h0` using `conj_of_sq (d_pos D) (sq_emb D D.host.φ₀)`.

Establish `h1` using `hτ D.host.φ₀ D.host.sqrtMinusD`. Rewrite `h1` using `[h, AlgEquiv.one_apply]`. Establish `h2` using `congrArg Complex.im h1`. Rewrite `h2` using `[Complex.conj_im]`. Conclude with `h0.2.2 (by linarith)`.

Establish `H` using `GlobalTheory.InfAdeleCM.infAdele_tensor_bijective D.host.F D.host.E (cF D) D.sp.cm.deg2 hc D.sp.cm.totReal hτ`. Use `⟨?_, fun θ hθ => ?_⟩` and prove the remaining obligations. Use `choose θ hθ using H.1`. Conclude with `⟨θ, hθ⟩`. Take `⟨h1, h2, h3⟩` from `H.2 θ hθ`.

Use `⟨h1, h2, h3 {τ | τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD} fun τ => ?_⟩` and prove the remaining obligations. Use `cm_type_mem_iff_conj_not_mem D τ` as an intermediate fact. Rewrite `this` using `[mem_cm_type_iff, mem_cm_type_iff]`. Conclude with `this`.
-/
theorem infiniteAdele_bijective : ∀ (D : D7), (∃ θ : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), (∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ (θ τ))) ∧ ∀ (θ : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), (∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ (θ τ)) → (∀ τ, Continuous (θ τ)) ∧ (∀ τ z, θ τ (sigR (Ainf D.host.F) D.sp.cm.sig z) = starRingEnd ℂ (θ τ z)) ∧ Function.Bijective (fun (z : Ainf D.host.F ⊗[D.host.F] D.host.E) (τ : {τ : D.host.E →+* ℂ // τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD}) => θ τ.1 z) := by
  intro D
  have hτ : ∀ (τ : D.host.E →+* ℂ) (x : D.host.E), τ (cF D x) = starRingEnd ℂ (τ x) :=
    fun τ x => IsCMField.complexEmbedding_complexConj D.host.E τ x
  have hc : cF D ≠ 1 := by
    intro h
    have h0 := conj_of_sq (d_pos D) (sq_emb D D.host.φ₀)
    have h1 := hτ D.host.φ₀ D.host.sqrtMinusD
    rw [h, AlgEquiv.one_apply] at h1
    have h2 := congrArg Complex.im h1
    rw [Complex.conj_im] at h2
    exact h0.2.2 (by linarith)
  have H := GlobalTheory.InfAdeleCM.infAdele_tensor_bijective D.host.F D.host.E (cF D) D.sp.cm.deg2 hc D.sp.cm.totReal hτ
  refine ⟨?_, fun θ hθ => ?_⟩
  · choose θ hθ using H.1
    exact ⟨θ, hθ⟩
  · obtain ⟨h1, h2, h3⟩ := H.2 θ hθ
    refine ⟨h1, h2, h3 {τ | τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD} fun τ => ?_⟩
    have := cm_type_mem_iff_conj_not_mem D τ
    rw [mem_cm_type_iff, mem_cm_type_iff] at this
    exact this

end GlobalTheory.Member
