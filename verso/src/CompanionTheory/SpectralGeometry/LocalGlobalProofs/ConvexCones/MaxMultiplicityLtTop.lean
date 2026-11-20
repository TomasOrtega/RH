import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MaxSimplicialCellMultiplicityLtTopOfIsPolyFan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotIsPrimZero
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.BalancedNonnegFormInPsdConeStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Fan.MaxMultiplicityFinite

open GlobalTheory.PolFan.MultBound in

/- English proof (translation)
Introduce `O _ _ _ _ bar hCM q φ hφ`. Take `⟨n, R, hR, hcls⟩` from `hCM.classes q`. Establish `hC` using `fun k : Fin n => haveI := (hR k).1 haveI := (hR k).2.1 GlobalTheory.PolFan.MultBound.perModule (hφ (R k) (hR k).2.2) (GlobalTheory.T.balanced_nonneg_form_in_psd_cone O bar hCM (R k))`. Use `choose C hC using hC`. Use `lt_of_le_of_lt (b := ((Finset.univ.sup C : ℕ) : ℕ∞)) ?_ (ENat.coe_lt_top _)` and prove the remaining obligations.

Unfold `maxMult`. Use `iSup_le fun X => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun hq => iSup_le fun m => iSup_le fun δ => iSup_le fun h => iSup_le fun hli => iSup_le fun hpr => ?_` and prove the remaining obligations. Take `⟨k, ⟨e⟩⟩` from `hcls X hq`. Use `haveI := (hR k).1`. Take `⟨h', hli', hpr', heq⟩` from `GlobalTheory.PolFan.MultBound.transport e.symm h hli hpr`.

Establish `hle` using `(hC k m _ h' hli' hpr').trans (Finset.le_sup (f := C) (Finset.mem_univ k))`. Rewrite using `[← heq]`. Conclude with `hle` after adjusting the coercions.
-/
theorem maxMult_lt_top : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O),
    CMOrd O bar → ∀ (q : ℕ) (φ : InvFun O), IsPolyFan bar q φ → maxMult bar q φ < ⊤ := by
  intro O _ _ _ _ bar hCM q φ hφ
  obtain ⟨n, R, hR, hcls⟩ := hCM.classes q
  have hC := fun k : Fin n =>
    haveI := (hR k).1
    haveI := (hR k).2.1
    GlobalTheory.PolFan.MultBound.perModule (hφ (R k) (hR k).2.2) (GlobalTheory.T.balanced_nonneg_form_in_psd_cone O bar hCM (R k))
  choose C hC using hC
  refine lt_of_le_of_lt (b := ((Finset.univ.sup C : ℕ) : ℕ∞)) ?_ (ENat.coe_lt_top _)
  unfold maxMult
  refine iSup_le fun X => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ =>
    iSup_le fun hq => iSup_le fun m => iSup_le fun δ => iSup_le fun h => iSup_le fun hli =>
      iSup_le fun hpr => ?_
  obtain ⟨k, ⟨e⟩⟩ := hcls X hq
  haveI := (hR k).1
  obtain ⟨h', hli', hpr', heq⟩ := GlobalTheory.PolFan.MultBound.transport e.symm h hli hpr
  have hle := (hC k m _ h' hli' hpr').trans (Finset.le_sup (f := C) (Finset.mem_univ k))
  rw [← heq]
  exact_mod_cast hle

end GlobalTheory.CompanionTheory.Ar.Fan.MaxMultiplicityFinite
