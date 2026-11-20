import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.CoefField

/- English proof (translation)
Introduce `l _ E Ω _ _ _ _ _ a ρ hρ`. Take `⟨L, -, hL⟩` from `GlobalTheory.CompactRepField.exists_finExt_entries_mem l (Formalism.ConjugateSelfDual.G E Ω) a ρ hρ ⟨⊥, inferInstance⟩`. Use `haveI := L.2`. Set `B` to `Module.finBasis ℚ_[l] ↥L.1`. Use `⟨Finset.univ.image (fun i => ((B i : ↥L.1) : Qbar l)), fun K hK g s t => ?_⟩` and prove the remaining obligations.

Establish `key : ∀ x : ↥L.1, (x : Qbar l) ∈ K`. Introduce `x`. Establish `hx : x ∈ Submodule.span ℚ_[l] (Set.range B)` using `B.mem_span x`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨i, rfl⟩` from `hy`. Conclude with `hK _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))`. Consider the case `zero => simpa using K.zero_mem`. Consider the case `add y z _ _ hy hz => simpa using K.add_mem hy hz`. Consider the case `smul c y _ hy => simpa using K.smul_mem hy (x := c)`.

Conclude with `key ⟨_, hL g s t⟩`.
-/
theorem entries_mem_of_finset : ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ) (ρ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)), Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l))) → ∃ S : Finset (Qbar l), ∀ K : IntermediateField ℚ_[l] (Qbar l), (∀ z ∈ S, z ∈ K) → ∀ g s t, ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) s t ∈ K := by
  intro l _ E Ω _ _ _ _ _ a ρ hρ
  obtain ⟨L, -, hL⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (Formalism.ConjugateSelfDual.G E Ω) a ρ hρ
    ⟨⊥, inferInstance⟩
  haveI := L.2
  let B := Module.finBasis ℚ_[l] ↥L.1
  classical
  refine ⟨Finset.univ.image (fun i => ((B i : ↥L.1) : Qbar l)), fun K hK g s t => ?_⟩
  have key : ∀ x : ↥L.1, (x : Qbar l) ∈ K := by
    intro x
    have hx : x ∈ Submodule.span ℚ_[l] (Set.range B) := B.mem_span x
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hK _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    | zero => simpa using K.zero_mem
    | add y z _ _ hy hz => simpa using K.add_mem hy hz
    | smul c y _ hy => simpa using K.smul_mem hy (x := c)
  exact key ⟨_, hL g s t⟩

end GlobalTheory.CoefField
