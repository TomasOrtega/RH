import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemiBCInjectiveOfInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrismCoverReceivingBreuilKisinStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismCoverInjectiveAndDescentStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

variable {l : ℕ} {R : Type} [CommRing R]

/- English proof (translation)
Split into cases according to the possible forms of the given data. Split into cases according to the possible forms of the given data. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. A detailed English derivation is pending.
-/
theorem FHom.ext_u {M M' : FCrys l R} {u u' : FHom M M'} (h : ∀ P, u.u P = u'.u P) : u = u' := by
  cases u; cases u'
  congr
  funext P
  exact h P

/- English proof (translation)
Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem FHom.eq_of_tr {M M' : FCrys l R} (u u' : FHom M M') {P Q : Obj l R} (g : Hom P Q)
    (hP : u.u P = u'.u P) : u.u Q = u'.u Q := by
  let v : M.M P →ₛₗ[g.f] M'.M Q := (M'.tr g).comp (u.u P)
  obtain ⟨w, -, hw⟩ := M.tr_bc g (M'.M Q) v
  have h1 := hw (u.u Q) fun x => by simp [v, u.u_tr]
  have h2 := hw (u'.u Q) fun x => by simp [v, u'.u_tr, hP]
  rw [h1, h2]

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem FHom.eq_of_inj {M M' : FCrys l R} (u u' : FHom M M') {B C : Obj l R} (h : Hom B C)
    (hinj : Function.Injective h.f) (hC : u.u C = u'.u C) : u.u B = u'.u B := by
  haveI := M'.fin B
  haveI := M'.proj B
  have hi : Function.Injective (M'.tr h) :=
    semiBC_injective_of_injective _ _ h.f hinj _ _ (M'.tr h) (M'.tr_bc h)
  ext x
  apply hi
  rw [← u.u_tr, ← u'.u_tr, hC]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem fhom_ext_bk : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (M M' : FCrys l ↥(OL K))
    (u u' : FHom M M'), u.u bk.prism = u'.u bk.prism → u = u' := by
  intro l _ K bk M M' u u' hbk
  apply FHom.ext_u
  intro B
  obtain ⟨C, h, ⟨g⟩, hc⟩ := GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B
  have hC := FHom.eq_of_tr u u' g hbk
  exact FHom.eq_of_inj u u' h (GlobalTheory.T.prism_cover_injective_and_descent l _ B C h hc).1 hC

end GlobalTheory.BSP
