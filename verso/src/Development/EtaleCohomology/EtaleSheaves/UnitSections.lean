import Development.EtaleCohomology.EtaleSheaves.TwistGenerators.LeafTwGenIndepOf
import Development.EtaleCohomology.EtaleSheaves.LeafPrimCoverPf
import Development.EtaleCohomology.EtaleSheaves.LPrimLocPf
import Development.EtaleCohomology.EtaleSheaves.IsChernClassCocycle

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.UnitSections

/- English proof (translation)
Introduce `q _ U ζ ξ`. Take `⟨s, hs, hf⟩` from `LateralTheory.E.L_prim_locPf.algPow q Γ(U, ⊤) ζ ξ`. Take `⟨S, hS, hP⟩` from `LateralTheory.E.L_prim_locPf.loc_of_span s hs (P := fun V g => ∃ a : (ZMod q)ˣ, (ξ.map (Scheme.Γ.map g.op).hom).1 = (ζ.map (Scheme.Γ.map g.op).hom).1 ^ (a : ZMod q).val) (by`. Introduce `f hfs V g hu`. Take `⟨a, n, hn⟩` from `hf f hfs`.

Use `⟨a, ?_⟩` and prove the remaining obligations. Establish `h` using `LateralTheory.E.L_prim_locPf.eq_of_unit_kill g.appTop.hom hn hu`. Rewrite `h` using `[map_pow]`. Conclude with `h)`. Conclude with `⟨S, hS, hP⟩`.
-/
theorem powLocal : LateralTheory.E.LeafUnitSecPf.Indep.LeafPowLocal := by
  intro q _ U ζ ξ
  obtain ⟨s, hs, hf⟩ := LateralTheory.E.L_prim_locPf.algPow q Γ(U, ⊤) ζ ξ
  obtain ⟨S, hS, hP⟩ := LateralTheory.E.L_prim_locPf.loc_of_span s hs
    (P := fun V g => ∃ a : (ZMod q)ˣ,
      (ξ.map (Scheme.Γ.map g.op).hom).1 = (ζ.map (Scheme.Γ.map g.op).hom).1 ^ (a : ZMod q).val) (by
      intro f hfs V g hu
      obtain ⟨a, n, hn⟩ := hf f hfs
      refine ⟨a, ?_⟩
      have h := LateralTheory.E.L_prim_locPf.eq_of_unit_kill g.appTop.hom hn hu
      rw [map_pow] at h
      exact h)
  exact ⟨S, hS, hP⟩

/- English proof (translation)
The claim follows from `LateralTheory.E.LeafUnitSecPf.Indep.LeafUnitSec_of LateralTheory.E.LeafPrimCoverPf.LeafPrimCover_of powLocal`.
-/
theorem LeafUnitSec_of : LateralTheory.E.LeafOneExistsPf.LeafUnitSec :=
  LateralTheory.E.LeafUnitSecPf.Indep.LeafUnitSec_of LateralTheory.E.LeafPrimCoverPf.LeafPrimCover_of powLocal

end LateralTheory.E.UnitSections
