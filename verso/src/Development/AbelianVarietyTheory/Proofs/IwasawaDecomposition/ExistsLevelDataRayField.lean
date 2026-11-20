import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTiedDataReciprocityStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKerTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostPlacesRayField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TiedSKAtWitnesses
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHostDatumOfPlaceData
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Substitute using the available equality. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem WPt.exists_recPinE : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.WeberRayFieldSt → GlobalTheory.NT.RayField →
    ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Prm hL) (K : Ctx) (q : WPt p.s K), Formalism.L2.Host.LevelTied (q.w.D q.Z) →
      Formalism.L2.Rows.ZetaCompatible (q.w.D q.Z) → EntC q.x.ker → ∃ R : Formalism.L2.RecT q.O.ex, RecPinE q R := by
  intro hA hW hR hL p K q hLT hZe hE
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_tied_data_reciprocity hA hW hL p K q hLT hZe
  obtain ⟨t, hK, hstd, hrd⟩ := GlobalTheory.Mem.Top.Bl.WPt.exists_kerTie p.s K q hE
  obtain ⟨T, hTS, hTk, hcrd, hpin, hj, ⟨⟨hw⟩⟩⟩ := GlobalTheory.Mem.Top.Bl.tiedSK_at_witnesses hL p K q S t hS hK
  have hp := GlobalTheory.Mem.Top.Bl.hostPins_wpt hR p.s K q
  subst hTS hTk
  obtain ⟨hd, -⟩ := GlobalTheory.HostDatumExists.exists_hostDatum hA _ _ _ _ _ _ _ _ q.O.ex T.toTiedDataS hp q.x.pin.d3b
  exact ⟨⟨T, hpin, hj, ⟨hd⟩, hw⟩, ⟨⟨hS, hK, hcrd⟩, hE, hstd, hrd⟩⟩

end GlobalTheory.Mem.Top.Bl
