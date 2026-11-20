import Development.EtaleCohomology.EtaleSheaves.SheafIsomorphism.LeafShIsoOf
import Development.EtaleCohomology.EtaleSheaves.BoundaryKernel.Formal

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite
namespace LateralTheory.E.H0Kernel
open LateralTheory.E.LeafDegCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafShIsoPf

/- English proof (translation)
Establish `: EssentiallySmall.{1} B.Etale` using `inferInstance`. Establish `hSC : (EtTop B).HasSheafCompose (forget (ModuleCat.{1} (ULift.{1} (ZMod q))))` using `hasSheafComposeEssentiallySmallSite (J := EtTop B) (A := ModuleCat.{1} (ULift.{1} (ZMod q))) (F := forget _)`. Conclude with `(Sheaf.isLocallySurjective_iff_epi' _ e).2 inferInstance`.
-/
theorem locSurj (B : Scheme.{0}) (q : ℕ) {F G : SShv B q} (e : F ⟶ G) [Epi e] : Sheaf.IsLocallySurjective e := by
  have : EssentiallySmall.{1} B.Etale := inferInstance
  have hSC : (EtTop B).HasSheafCompose (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) :=
    hasSheafComposeEssentiallySmallSite (J := EtTop B) (A := ModuleCat.{1} (ULift.{1} (ZMod q))) (F := forget _)
  exact (Sheaf.isLocallySurjective_iff_epi' _ e).2 inferInstance

/- English proof (translation)
Introduce `B q M U x hx`. Take `⟨T, e, he, H⟩` from `exists_epi (C := SShv B q) (P := (presheafToSheaf (EtTop B) _).obj ((FP (ULift.{1} (ZMod q))).obj U)) x hx`. Use `locSurj B q e` as an intermediate fact. Take `⟨Z, hZ, hc⟩` from `locally_factors (EtTop B) (ULift.{1} (ZMod q)) e`. Use `⟨Z, hZ, fun U' a ha => ?_⟩` and prove the remaining obligations.

Take `⟨c, hc⟩` from `hc U' a ha`. Establish `h` using `H _ c`. Rewrite `h` using `[← hc]`. Conclude with `h`.
-/
theorem etale_sheaf_zeroth_cohomology_kernel_exact : EtaleDerivedDegreeZeroHomologyKernelLocallyVanishes := by
  intro B q M U x hx
  obtain ⟨T, e, he, H⟩ := exists_epi (C := SShv B q)
    (P := (presheafToSheaf (EtTop B) _).obj ((FP (ULift.{1} (ZMod q))).obj U)) x hx
  have := locSurj B q e
  obtain ⟨Z, hZ, hc⟩ := locally_factors (EtTop B) (ULift.{1} (ZMod q)) e
  refine ⟨Z, hZ, fun U' a ha => ?_⟩
  obtain ⟨c, hc⟩ := hc U' a ha
  have h := H _ c
  rw [← hc] at h
  exact h

end LateralTheory.E.H0Kernel
