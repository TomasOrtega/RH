import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyBreuilKisinDatumStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticFCrystalHomExtBreuilKisinPrismStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDatumStructureMapInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemiBCInjectiveOfInjective

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

/- English proof (translation)
Introduce `l _ K T' _ _ ρ' M M' j' H u u' h`. Take `⟨bk⟩` from `GlobalTheory.T.nonempty_breuilKisinDatum l K`. Apply `GlobalTheory.T.prismaticFCrystalHom_ext_breuilKisin_prism l K bk M M' u u'` to reduce the goal to its premises. Use `haveI := M'.fin (ainfObj K)`. Use `haveI := M'.proj (ainfObj K)`.

Use `haveI := M'.fin bk.prism`. Use `haveI := M'.proj bk.prism`. Establish `hj : Function.Injective j'` using `semiBC_injective_of_injective _ _ ((inclW l).comp (ainfId K).toRingHom) (GlobalTheory.Prism.inclW_injective.comp (ainfId K).injective) _ _ j' H.bc`. Establish `ht : Function.Injective (M'.tr bk.ι)` using `semiBC_injective_of_injective _ _ bk.ι.f (GlobalTheory.T.breuilKisinDatum_structureMap_injective l K bk) _ _ (M'.tr bk.ι) (M'.tr_bc bk.ι)`. Use `LinearMap.ext fun x => ht (hj ?_)` and prove the remaining obligations.

Rewrite using `[← u.u_tr, ← u'.u_tr]`. Conclude with `h _`.
-/
theorem fHom_eq_of_realises : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (T' : Type) [AddCommGroup T'] [Module ℤ_[l] T']
    (ρ' : ↥(GK K) → (T' →ₗ[ℤ_[l]] T')) (M M' : FCrys l ↥(OL K))
    (j' : M'.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T')),
    Realises K M' (ainfObj K) (ainfId K) T' ρ' j' → ∀ u u' : FHom M M',
      (∀ x, j' (u.u (ainfObj K) x) = j' (u'.u (ainfObj K) x)) → u = u' := by
  intro l _ K T' _ _ ρ' M M' j' H u u' h
  obtain ⟨bk⟩ := GlobalTheory.T.nonempty_breuilKisinDatum l K
  apply GlobalTheory.T.prismaticFCrystalHom_ext_breuilKisin_prism l K bk M M' u u'
  haveI := M'.fin (ainfObj K)
  haveI := M'.proj (ainfObj K)
  haveI := M'.fin bk.prism
  haveI := M'.proj bk.prism
  have hj : Function.Injective j' :=
    semiBC_injective_of_injective _ _ ((inclW l).comp (ainfId K).toRingHom)
      (GlobalTheory.Prism.inclW_injective.comp (ainfId K).injective) _ _ j' H.bc
  have ht : Function.Injective (M'.tr bk.ι) :=
    semiBC_injective_of_injective _ _ bk.ι.f (GlobalTheory.T.breuilKisinDatum_structureMap_injective l K bk) _ _ (M'.tr bk.ι) (M'.tr_bc bk.ι)
  refine LinearMap.ext fun x => ht (hj ?_)
  rw [← u.u_tr, ← u'.u_tr]
  exact h _

end GlobalTheory.BSP
