import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

/- English proof (translation)
Introduce `C _ _ V _ _ _ I T hc hs`. Establish `hmax : ∀ a μ, (T a).maxGenEigenspace μ = (T a).eigenspace μ`. Introduce `a μ`. Take `⟨f, hf, h0⟩` from `hs a`. Conclude with `(Module.End.isSemisimple_of_squarefree_aeval_eq_zero hf.squarefree h0).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ`.

Establish `hcomm : Pairwise fun i j => Commute (T i) (T j)` using `fun i j _ => hc i j`. Establish `hdiag : ∀ a, ⨆ μ, (T a).maxGenEigenspace μ = ⊤` using `fun a => Module.End.iSup_maxGenEigenspace_eq_top (T a)`. Establish `htop` using `Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute T hcomm hdiag`. Simplify `htop` using `only [hmax]`.
-/
theorem iSup_jointEigenspace_eq_top_of_separable : ∀ (C : Type) [Field C] [IsAlgClosed C] (V : Type) [AddCommGroup V] [Module C V] [FiniteDimensional C V] (I : Type) (T : I → Module.End C V), (∀ a b, Commute (T a) (T b)) → (∀ a, ∃ f : Polynomial C, f.Separable ∧ Polynomial.aeval (T a) f = 0) → (⨆ χ : I → C, ⨅ a : I, Module.End.eigenspace (T a) (χ a)) = ⊤ := by
  intro C _ _ V _ _ _ I T hc hs
  have hmax : ∀ a μ, (T a).maxGenEigenspace μ = (T a).eigenspace μ := by
    intro a μ
    obtain ⟨f, hf, h0⟩ := hs a
    exact (Module.End.isSemisimple_of_squarefree_aeval_eq_zero hf.squarefree h0).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  have hcomm : Pairwise fun i j => Commute (T i) (T j) := fun i j _ => hc i j
  have hdiag : ∀ a, ⨆ μ, (T a).maxGenEigenspace μ = ⊤ := fun a =>
    Module.End.iSup_maxGenEigenspace_eq_top (T a)
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute T hcomm hdiag
  simpa only [hmax] using htop

end GlobalTheory
