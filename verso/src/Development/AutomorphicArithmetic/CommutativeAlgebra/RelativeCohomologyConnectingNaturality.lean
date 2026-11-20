import Mathlib
import Development.EtaleCohomology.EtaleSheaves.NeighbourhoodKilling
import Development.EtaleCohomology.EtaleSheaves.GlueRelPfNat

open CategoryTheory GlobalTheory.EtC CochainComplex.HomComplex LateralTheory.E.E4 LateralTheory.E.LeafGhostCut in
/- English proof (translation)
Introduce `q _ U E U' E' f f' u e comm i m w`. Take `⟨w, rfl⟩` from `w.mk_surjective`. Use `congrArg CohomologyClass.mk (Cocycle.ext ?_)` and prove the remaining obligations. Simplify using `only [zcomp, Cocycle.ofHom_coe, Cocycle.mk_coe]`. Rewrite using `[← Cochain.comp_assoc_of_first_is_zero_cochain, rmap, LateralTheory.E.GlueRelPfNat.map_fst, Cochain.comp_assoc_of_second_is_zero_cochain]`.
-/
theorem UpperTheory.relativeCohomology_connecting_naturality :
    LateralTheory.E.NeighbourhoodKilling.ObsNat := by
  intro q _ U E U' E' f f' u e comm i m w
  obtain ⟨w, rfl⟩ := w.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp only [zcomp, Cocycle.ofHom_coe, Cocycle.mk_coe]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, rmap, LateralTheory.E.GlueRelPfNat.map_fst,
    Cochain.comp_assoc_of_second_is_zero_cochain]
