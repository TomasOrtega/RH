import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AutomorphicArithmetic.CyclotomicBounds.ZmodTwoQuadraticNeZero
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

noncomputable section

namespace GlobalTheory.HostImage

/- English proof (translation)
Introduce `D i w hw x`. Establish `h` using `UpperTheory.Small.factorization_condN_le D.host (D.nd.lPrime i).out`. Use `UpperTheory.Small.image_mem_Kur_sup D.host ((D.nbr i w hw).j.comp (algebraMap D.host.E D.nd.Om)) ?_ x` and prove the remaining obligations. Distinguish the cases in `h2 : D.nd.l i = 2`. Rewrite using `[D.nd.restNLevelExponent_of_two i h2, ← h2]`.

Conclude with `h.2 h2`. Rewrite using `[D.nd.restNLevelExponent_of_odd i h2]`. Conclude with `h.1`.
-/
theorem host_image_mem : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (x : D.host.E), (D.nbr i w hw).j (algebraMap D.host.E D.nd.Om x) ∈ MaximalUnramifiedExtension (D.nd.l i) ⊔ IntermediateField.adjoin ℚ_[D.nd.l i] {y : Om (D.nd.l i) | y ^ (D.nd.l i ^ D.nd.s0 i) = 1} := by
  intro D i w hw x
  have h := UpperTheory.Small.factorization_condN_le D.host (D.nd.lPrime i).out
  refine UpperTheory.Small.image_mem_Kur_sup D.host ((D.nbr i w hw).j.comp (algebraMap D.host.E D.nd.Om)) ?_ x
  by_cases h2 : D.nd.l i = 2
  · rw [D.nd.restNLevelExponent_of_two i h2, ← h2]
    exact h.2 h2
  · rw [D.nd.restNLevelExponent_of_odd i h2]
    exact h.1

end GlobalTheory.HostImage
