import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DsigEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistConductorNotOverLevelPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupTiedOfMuIsW
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl

/- English proof (translation)
Introduce `hR 𝒮 K q`. Take `⟨B, f, T, w, Z, O, x⟩` from `q`. Establish `hmu` using `x.what₂.mu`. Establish `key` using `GlobalTheory.Mem.Top.TupTieW.tupTied_of_muIsW (w.st Z) f T x.Wt w.I.xi hmu`. Establish `hδ : w.δ.ray ≤ B.KsC` using `w.exact.lower.1`.

Establish `hQ : ∀ v ∈ x.Wt, O.ex.nch.Q v = T.Q v` using `fun v hv => (x.n.Q v hv).1`. Use `⟨fun u i => (w.D Z).T_ne_g u i, ?_, fun v hv v' hv' u => ?_, B.galLL, GlobalTheory.Mem.HD.exists_hilbert_le_O hR B w.δ hδ⟩` and prove the remaining obligations. Conclude with `key.2.1.subset fun v hv => (key.1 v).1 hv`. Establish `hvW` using `(key.1 v).1 hv`. Rewrite `hv'` using `[hQ v hvW]`.

Establish `e : ((w.D Z).mem u).A.T = B.T u` using `(w.st Z).C.A_T u`. Establish `hp : (B.T u).Prime` using `e ▸ ((w.D Z).mem u).A.T_prime`. Rewrite using `[e]`. Conclude with `GlobalTheory.Mem.HD.twistConductor_not_over_levelPrimes B T v hv' u hp`.
-/
theorem hostPins_wpt : GlobalTheory.NT.RayField → ∀ (𝒮 : Slots) (K : Ctx) (q : WPt 𝒮 K), GlobalTheory.Mem.HD.HostPins (q.w.D q.Z) q.O.ex.nch := by
  intro hR 𝒮 K q
  obtain ⟨B, f, T, w, Z, O, x⟩ := q
  have hmu := x.what₂.mu
  have key := GlobalTheory.Mem.Top.TupTieW.tupTied_of_muIsW (w.st Z) f T x.Wt w.I.xi hmu
  have hδ : w.δ.ray ≤ B.KsC := w.exact.lower.1
  have hQ : ∀ v ∈ x.Wt, O.ex.nch.Q v = T.Q v := fun v hv => (x.n.Q v hv).1
  refine ⟨fun u i => (w.D Z).T_ne_g u i, ?_, fun v hv v' hv' u => ?_, B.galLL, GlobalTheory.Mem.HD.exists_hilbert_le_O hR B w.δ hδ⟩
  · exact key.2.1.subset fun v hv => (key.1 v).1 hv
  · have hvW := (key.1 v).1 hv
    rw [hQ v hvW] at hv'
    have e : ((w.D Z).mem u).A.T = B.T u := (w.st Z).C.A_T u
    have hp : (B.T u).Prime := e ▸ ((w.D Z).mem u).A.T_prime
    rw [e]
    exact GlobalTheory.Mem.HD.twistConductor_not_over_levelPrimes B T v hv' u hp

end GlobalTheory.Mem.Top.Bl
