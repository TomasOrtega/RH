import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRFiltrationKerThetaGeneratorFacts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiSTmul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExtFixing
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
open GlobalTheory.HodgeAt

namespace GlobalTheory

/- English proof (translation)
Introduce `l _ P AI T a m w hind hspan`. Use `haveI : Nontrivial P.R.BdR := (GlobalTheory.DRFil.isField_dR T).nontrivial`. Establish `hli : LinearIndependent P.R.BdR w`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg i`.

Conclude with `congrFun (hind g hg) i`. Establish `h1 : m ≤ a`. Use `hli.fintype_card_le_finrank` as an intermediate fact. Simplify `this` using `[Module.finrank_fin_fun]`. Establish `hsurj : Function.Surjective (Fintype.linearCombination P.R.BdR w)`.

Rewrite using `[← LinearMap.range_eq_top, Submodule.eq_top_iff']`. Introduce `x`. Establish `hj : ∀ j, Pi.single j (x j) ∈ LinearMap.range (Fintype.linearCombination P.R.BdR w)`. Introduce `j`. Take `⟨u, hu⟩` from `hspan j`.

Use `⟨x j • u, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, Fintype.linearCombination_apply, hu]`. Use extensionality with `k`. Distinguish the cases in `h : k = j`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, h]`. Rewrite using `[← Finset.univ_sum_single x]`. Conclude with `Submodule.sum_mem _ fun j _ => hj j`. Establish `h2 : a ≤ m`.

Simplify using `using card_le_of_surjective P.R.BdR _ hsurj`. Conclude with `le_antisymm h1 h2`.
-/
theorem card_eq_of_indep_spans_dR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (a m : ℕ) (w : Fin m → Fin a → P.R.BdR), (∀ β : Fin m → P.R.BdR, ∑ i, β i • w i = 0 → β = 0) → (∀ j, ∃ u : Fin m → P.R.BdR, ∑ i, u i • w i = Pi.single j 1) → m = a := by
  intro l _ P AI T a m w hind hspan
  haveI : Nontrivial P.R.BdR := (GlobalTheory.DRFil.isField_dR T).nontrivial
  have hli : LinearIndependent P.R.BdR w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    exact congrFun (hind g hg) i
  have h1 : m ≤ a := by
    have := hli.fintype_card_le_finrank
    simpa [Module.finrank_fin_fun] using this
  have hsurj : Function.Surjective (Fintype.linearCombination P.R.BdR w) := by
    rw [← LinearMap.range_eq_top, Submodule.eq_top_iff']
    intro x
    have hj : ∀ j, Pi.single j (x j) ∈ LinearMap.range (Fintype.linearCombination P.R.BdR w) := by
      intro j
      obtain ⟨u, hu⟩ := hspan j
      refine ⟨x j • u, ?_⟩
      rw [map_smul, Fintype.linearCombination_apply, hu]
      ext k
      by_cases h : k = j
      · subst h; simp
      · simp [Pi.single_apply, h]
    rw [← Finset.univ_sum_single x]
    exact Submodule.sum_mem _ fun j _ => hj j
  have h2 : a ≤ m := by
    simpa using card_le_of_surjective P.R.BdR _ hsurj
  exact le_antisymm h1 h2

end GlobalTheory
