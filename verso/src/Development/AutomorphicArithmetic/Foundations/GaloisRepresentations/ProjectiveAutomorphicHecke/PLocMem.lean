import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

/- English proof (translation)
Introduce `hIC hLC E _ _ _ n S Kw w hw hcw y`. Take `⟨-, hap, -, -, hcc, -⟩` from `hLC E n w hw`. Establish `hsim : sim (loc hw y) ∈ ZU`. Rewrite using `[sim_loc]`. Conclude with `ZU.one_mem`.

Establish `hone : ∀ u, u ≠ w → u ≠ cj w → comp u (loc hw y) = 1` using `fun u h1 h2 => comp_loc_of_apart hw ((hap u).2 ⟨h1, h2⟩) y`. Use `⟨fun hwS hy => mem_lev.2 ⟨hsim, ?_, ?_⟩, fun hwS hy => mem_lev.2 ⟨hsim, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `u hu`. Distinguish the cases in `h1 : u = w`. Substitute `h1` using the available equality.

Rewrite using `[comp_loc]`. Conclude with `hy`. Establish `h2 : u ≠ cj w` using `fun h => hcw (h ▸ hu)`. Rewrite using `[hone u h1 h2]`. Conclude with `(Kw u).one_mem`.

Introduce `u hu hcu`. Establish `h1 : u ≠ w` using `fun h => hu (h ▸ hwS)`. Establish `h2 : u ≠ cj w` using `fun h => hcu (by rw [h, hcc]; exact hwS)`. Rewrite using `[hone u h1 h2]`. Conclude with `(GlobalTheory.LFun.KGL u n).one_mem`.

Introduce `u hu`. Establish `h1 : u ≠ w` using `fun h => hwS (h ▸ hu)`. Establish `h2 : u ≠ cj w` using `fun h => hcw (h ▸ hu)`. Rewrite using `[hone u h1 h2]`. Conclude with `(Kw u).one_mem`.

Introduce `u hu hcu`. Distinguish the cases in `h1 : u = w`. Substitute `h1` using the available equality. Rewrite using `[comp_loc]`. Conclude with `hy`.

Distinguish the cases in `h2 : u = cj w`. Substitute `h2` using the available equality. Conclude with `hIC E n (loc hw y) w hsim (by rw [comp_loc]; exact hy)`. Rewrite using `[hone u h1 h2]`. Conclude with `(GlobalTheory.LFun.KGL u n).one_mem`.
-/
theorem UpperTheory.Gal.CertificateRingHomMap.pLocMem_of :
    UpperTheory.Gal.CertificateRingHomMap.IntConj → UpperTheory.Gal.CertificateRingHomMap.LocComm → UpperTheory.Gal.CertificateRingHomMap.LocMem := by
  intro hIC hLC E _ _ _ n S Kw w hw hcw y
  obtain ⟨-, hap, -, -, hcc, -⟩ := hLC E n w hw
  have hsim : sim (loc hw y) ∈ ZU := by
    rw [sim_loc]; exact ZU.one_mem
  have hone : ∀ u, u ≠ w → u ≠ cj w → comp u (loc hw y) = 1 := fun u h1 h2 =>
    comp_loc_of_apart hw ((hap u).2 ⟨h1, h2⟩) y
  refine ⟨fun hwS hy => mem_lev.2 ⟨hsim, ?_, ?_⟩, fun hwS hy => mem_lev.2 ⟨hsim, ?_, ?_⟩⟩
  · intro u hu
    by_cases h1 : u = w
    · subst h1
      rw [comp_loc]; exact hy
    · have h2 : u ≠ cj w := fun h => hcw (h ▸ hu)
      rw [hone u h1 h2]; exact (Kw u).one_mem
  · intro u hu hcu
    have h1 : u ≠ w := fun h => hu (h ▸ hwS)
    have h2 : u ≠ cj w := fun h => hcu (by rw [h, hcc]; exact hwS)
    rw [hone u h1 h2]; exact (GlobalTheory.LFun.KGL u n).one_mem
  · intro u hu
    have h1 : u ≠ w := fun h => hwS (h ▸ hu)
    have h2 : u ≠ cj w := fun h => hcw (h ▸ hu)
    rw [hone u h1 h2]; exact (Kw u).one_mem
  · intro u hu hcu
    by_cases h1 : u = w
    · subst h1
      rw [comp_loc]; exact hy
    · by_cases h2 : u = cj w
      · subst h2
        exact hIC E n (loc hw y) w hsim (by rw [comp_loc]; exact hy)
      · rw [hone u h1 h2]; exact (GlobalTheory.LFun.KGL u n).one_mem
