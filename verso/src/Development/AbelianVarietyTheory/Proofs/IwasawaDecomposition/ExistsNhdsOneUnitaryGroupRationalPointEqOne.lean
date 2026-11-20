import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DiscreteTopologyRationalPointsHermitianSpace

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ M J`. Establish `hd` using `GlobalTheory.RationalDiscrete.discreteTopology_HFinIn σ J`. Establish `h1 : ({1} : Set (HFinIn (AF F) σ J)) ∈ nhds (1 : HFinIn (AF F) σ J)` using `(isOpen_discrete _).mem_nhds rfl`. Take `⟨U, hU, hsub⟩` from `(mem_nhds_subtype _ _ _).1 h1`. Use `⟨U, hU, ?_⟩` and prove the remaining obligations.

Introduce and unpack `g hg ⟨γ, rfl⟩`. Establish `hγ : γ • (1 : HA (AF F) σ J) = (γ.1 : HR (AF F) σ J)` using `mul_one (γ.1 : HR (AF F) σ J)`. Rewrite `hg`, the goal using `[hγ]`. Establish `h2 : γ = 1` using `hsub hg`. Rewrite using `[h2]`.

Both sides reduce to the same expression.
-/
theorem exists_nhds_one_rational_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), ∃ U ∈ nhds (1 : HA (AF F) σ J), ∀ g ∈ U, (∃ γ : HFinIn (AF F) σ J, γ • (1 : HA (AF F) σ J) = g) → g = 1 := by
  intro F E _ _ _ _ _ σ M J
  have hd := GlobalTheory.RationalDiscrete.discreteTopology_HFinIn σ J
  have h1 : ({1} : Set (HFinIn (AF F) σ J)) ∈ nhds (1 : HFinIn (AF F) σ J) :=
    (isOpen_discrete _).mem_nhds rfl
  obtain ⟨U, hU, hsub⟩ := (mem_nhds_subtype _ _ _).1 h1
  refine ⟨U, hU, ?_⟩
  rintro g hg ⟨γ, rfl⟩
  have hγ : γ • (1 : HA (AF F) σ J) = (γ.1 : HR (AF F) σ J) := mul_one (γ.1 : HR (AF F) σ J)
  rw [hγ] at hg ⊢
  have h2 : γ = 1 := hsub hg
  rw [h2]
  rfl

end GlobalTheory.Mem.Vol
