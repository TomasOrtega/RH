import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

/- English proof (translation)
Introduce `E _ _ _ n`. Use `⟨fun u v h => ?_, fun g hg => ?_⟩` and prove the remaining obligations. Establish `h1 : GeneralLinearGroup.map (pFin E) u.1.1 = GeneralLinearGroup.map (pFin E) v.1.1` using `congrArg (fun x : GUf E n => mat x) h`. Establish `h2` using `congrArg (finGL E n) h1`. Rewrite `h2` using `[GlobalTheory.DefU.ClassFin.finGL_pFin, GlobalTheory.DefU.ClassFin.finGL_pFin]`.

Conclude with `Subtype.ext (Subtype.ext h2)`. Establish `hs : g.1.2 = 1` using `hg`. Establish `h : Formalism.UG.cT (conjFin (GlobalTheory.DefU.ClassFin.cc E)) (mat g).val * (mat g).val = 1` using `(mem_Sim.1 g.2).trans (by rw [hs]; simp)`. Use `⟨⟨⟨finGL E n (mat g), GlobalTheory.DefU.ClassFin.finGL_mem_UA _ h⟩, pInf_finGL _⟩, ?_⟩` and prove the remaining obligations. Conclude with `Subtype.ext (Prod.ext (pFin_finGL _) hs.symm)`.
-/
theorem UpperTheory.Gal.CertificateRingHomMap.pOfUBij_of :
    UpperTheory.Gal.CertificateRingHomMap.OfUBij := by
  intro E _ _ _ n
  refine ⟨fun u v h => ?_, fun g hg => ?_⟩
  · have h1 : GeneralLinearGroup.map (pFin E) u.1.1 = GeneralLinearGroup.map (pFin E) v.1.1 :=
      congrArg (fun x : GUf E n => mat x) h
    have h2 := congrArg (finGL E n) h1
    rw [GlobalTheory.DefU.ClassFin.finGL_pFin, GlobalTheory.DefU.ClassFin.finGL_pFin] at h2
    exact Subtype.ext (Subtype.ext h2)
  · have hs : g.1.2 = 1 := hg
    have h : Formalism.UG.cT (conjFin (GlobalTheory.DefU.ClassFin.cc E)) (mat g).val * (mat g).val = 1 :=
      (mem_Sim.1 g.2).trans (by rw [hs]; simp)
    refine ⟨⟨⟨finGL E n (mat g), GlobalTheory.DefU.ClassFin.finGL_mem_UA _ h⟩, pInf_finGL _⟩, ?_⟩
    exact Subtype.ext (Prod.ext (pFin_finGL _) hs.symm)
