import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleFunctorExactOnLatticesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachFunctorFullyFaithfulStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleRingFreeOverFrobeniusImageStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPsiOperatorEtalePhiGammaModuleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachFunctorRingPsiOperatorExistsOfGoodStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

/- English proof (translation)
Introduce `D HW F`. Unfold `Formalism.MainNotions.InvariantsGenerators.LitFont`. Introduce `l _ K LL hA`. Unfold `Formalism.MainNotions.InvariantsGenerators.FontCore`. Establish `hff` using `GlobalTheory.T.wachFunctor_fullyFaithful D HW F l K 1 LL hA.2.2`.

Establish `hex` using `GlobalTheory.T.etaleFunctor_exact_on_lattices D HW F l K 1 LL hA.2.2`. Establish `hpd` using `GlobalTheory.T.exists_psi_operator_etale_phiGamma_module D HW F l K 1 LL hA.2.2`. Establish `hpe` using `GlobalTheory.T.wachFunctorRing_psiOperator_exists_of_good D HW F l K 1 LL hA.2.2`. Establish `hfr` using `GlobalTheory.T.etaleRing_free_over_frobenius_image D HW F l K 1 LL hA.2.2`. Establish `hp : ((D.loc l).PD K).p = l` using `(D.loc l).PD_p K`.

Use `⟨hff, hex, ?_, hpd⟩` and prove the remaining obligations. Take `⟨ψ, h1, h2, h3⟩` from `hpe`. Use `⟨ψ, h1, h2, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hp]`. Conclude with `h3`.

Introduce `x`. Take `⟨c, hc, -⟩` from `hfr x`. Rewrite using `[hp]`. Conclude with `⟨c, hc⟩`.
-/
theorem fontaine_litFont_assembled :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.InvariantsGenerators.LitFont D HW F := by
  intro D HW F
  unfold Formalism.MainNotions.InvariantsGenerators.LitFont
  intro l _ K LL hA
  unfold Formalism.MainNotions.InvariantsGenerators.FontCore
  have hff := GlobalTheory.T.wachFunctor_fullyFaithful D HW F l K 1 LL hA.2.2
  have hex := GlobalTheory.T.etaleFunctor_exact_on_lattices D HW F l K 1 LL hA.2.2
  have hpd := GlobalTheory.T.exists_psi_operator_etale_phiGamma_module D HW F l K 1 LL hA.2.2
  have hpe := GlobalTheory.T.wachFunctorRing_psiOperator_exists_of_good D HW F l K 1 LL hA.2.2
  have hfr := GlobalTheory.T.etaleRing_free_over_frobenius_image D HW F l K 1 LL hA.2.2
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  refine ⟨hff, hex, ?_, hpd⟩
  obtain ⟨ψ, h1, h2, h3⟩ := hpe
  refine ⟨ψ, h1, h2, ?_, ?_⟩
  · rw [hp]; exact h3
  · intro x
    obtain ⟨c, hc, -⟩ := hfr x
    rw [hp]
    exact ⟨c, hc⟩

end GlobalTheory
