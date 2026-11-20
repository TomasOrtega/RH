import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfStabilizerTrivial
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf
open scoped Pointwise

namespace GlobalTheory.TypeSplit

/- English proof (translation)
Introduce `D k w hw`. Use `haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois`. Establish `hP` using `(GlobalTheory.Mem.Chr.splitsC_place (p := D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w hw).2.2`. Assume the negation of the conclusion as `hn`. Establish `hle : ∀ x ∈ w.asIdeal, D.host.conj • x ∈ w.asIdeal`.

Introduce `x hx`. Assume the negation of the conclusion as `hy`. Use `hn ⟨x, hx, fun y e hy' => hy ?_⟩` and prove the remaining obligations. Establish `: y = D.host.conj • x` using `Subtype.ext e`. Rewrite using `[← this]` and apply the resulting hypothesis.

Use `GlobalTheory.TypePlace.conj_ne_one D.host (hP _ ?_)` and prove the remaining obligations. Establish `h1 : D.host.conj • w.asIdeal ≤ w.asIdeal`. Introduce `y hy`. Rewrite `hy` using `[Ideal.mem_pointwise_smul_iff_inv_smul_mem]`. Simplify using `using hle _ hy`.

Establish `hm : (D.host.conj • w.asIdeal).IsMaximal` using `Ideal.map_isMaximal_of_equiv (MulSemiringAction.toRingEquiv _ (𝓞 D.host.E) D.host.conj) (hp := w.isMaximal)`. Conclude with `hm.eq_of_le w.isMaximal.ne_top h1`.
-/
theorem main : ∀ (D : D7) (k : Fin 2), ∀ w ∈ placesOver D.host.E (D.host.g k), IsSplitPl D.host w := by
  intro D k w hw
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have hP := (GlobalTheory.Mem.Chr.splitsC_place (p := D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w hw).2.2
  by_contra hn
  have hle : ∀ x ∈ w.asIdeal, D.host.conj • x ∈ w.asIdeal := by
    intro x hx
    by_contra hy
    refine hn ⟨x, hx, fun y e hy' => hy ?_⟩
    have : y = D.host.conj • x := Subtype.ext e
    rwa [← this]
  refine GlobalTheory.TypePlace.conj_ne_one D.host (hP _ ?_)
  have h1 : D.host.conj • w.asIdeal ≤ w.asIdeal := by
    intro y hy
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
    simpa using hle _ hy
  have hm : (D.host.conj • w.asIdeal).IsMaximal :=
    Ideal.map_isMaximal_of_equiv (MulSemiringAction.toRingEquiv _ (𝓞 D.host.E) D.host.conj) (hp := w.isMaximal)
  exact hm.eq_of_le w.isMaximal.ne_top h1

end GlobalTheory.TypeSplit
