import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E] in

/- English proof (translation)
Use `⟨finrank_span_singleton hx, ?_⟩` and prove the remaining obligations. Introduce `a ha b hb`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 ha`. Take `⟨d, rfl⟩` from `Submodule.mem_span_singleton.1 hb`. Simplify using `only [map_smul, LinearMap.map_smulₛₗ₂, hxx, smul_zero]`.
-/
theorem isIsotropicLine_span_singleton (h : HermitianForm F E W) {x : W} (hx : x ≠ 0)
    (hxx : h.toSesq x x = 0) : IsIsotropicLine h (Submodule.span E {x}) := by
  refine ⟨finrank_span_singleton hx, ?_⟩
  intro a ha b hb
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ha
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 hb
  simp only [map_smul, LinearMap.map_smulₛₗ₂, hxx, smul_zero]

/- English proof (translation)
Introduce `D`. Take `⟨M⟩` from `h₂`. Take `⟨S₁, hS₁, K, -, hK⟩` from `h₁ M D 1 one_pos`. Take `⟨S₂, hS₂, hP⟩` from `h₄ D`. Use `⟨S₁ ∪ Prod.fst '' S₂, hS₁.union (hS₂.image _), ?_⟩` and prove the remaining obligations.

Introduce `La hLa`. Distinguish the cases in `hshort : ∃ x : W, x ∈ La ∧ x ≠ 0 ∧ M.len (invApply (1 : archUnitary h v) (vecAt v x)) < 1`. Take `⟨x, hxL, hx0, hxlt⟩` from `hshort`. Establish `hxx : h.toSesq x x = 0` using `h₃ M D La 1 x hLa hxL hxlt`. Take `⟨p, hp, g, hg, -⟩` from `hP La (Submodule.span E {x}) hLa (isIsotropicLine_span_singleton h hx0 hxx)`.

Conclude with `⟨p.1, Or.inr ⟨p, hp, rfl⟩, g, hg⟩`. Use `push Not at hshort`. Take `⟨γ, hγ, -⟩` from `hK La 1 hLa hshort`. Conclude with `⟨γ • La, Or.inl hγ, γ⁻¹, inv_smul_smul γ La⟩`.
-/
theorem LatticeOrbitsFinite.proof (h : HermitianForm F E W) (v : Basis ι E W) [FiniteDimensional E W]
    (h₁ : MahlerCompactness.Statement h v) (h₂ : MajorantExists.Statement h v)
    (h₃ : ShortVectorIsotropic.Statement h v) (h₄ : LinePairOrbitsFinite.Statement h) :
    LatticeOrbitsFinite.Statement h := by
  intro D
  obtain ⟨M⟩ := h₂
  obtain ⟨S₁, hS₁, K, -, hK⟩ := h₁ M D 1 one_pos
  obtain ⟨S₂, hS₂, hP⟩ := h₄ D
  refine ⟨S₁ ∪ Prod.fst '' S₂, hS₁.union (hS₂.image _), ?_⟩
  intro La hLa
  by_cases hshort : ∃ x : W, x ∈ La ∧ x ≠ 0 ∧ M.len (invApply (1 : archUnitary h v) (vecAt v x)) < 1
  · obtain ⟨x, hxL, hx0, hxlt⟩ := hshort
    have hxx : h.toSesq x x = 0 := h₃ M D La 1 x hLa hxL hxlt
    obtain ⟨p, hp, g, hg, -⟩ := hP La (Submodule.span E {x}) hLa
      (isIsotropicLine_span_singleton h hx0 hxx)
    exact ⟨p.1, Or.inr ⟨p, hp, rfl⟩, g, hg⟩
  · push Not at hshort
    obtain ⟨γ, hγ, -⟩ := hK La 1 hLa hshort
    exact ⟨γ • La, Or.inl hγ, γ⁻¹, inv_smul_smul γ La⟩

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
