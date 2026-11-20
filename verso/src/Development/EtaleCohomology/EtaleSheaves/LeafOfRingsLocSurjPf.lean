import Development.EtaleCohomology.EtaleSheaves.LeafTwSecKillCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafOfRingsLocSurjPf

/- English proof (translation)
Take `⟨𝒰, h𝒰⟩` from `(Scheme.mem_grothendieckTopology_iff).1 hS`. Take `⟨i, hi⟩` from `((Scheme.presieve₀_mem_precoverage_iff _).1 𝒰.mem₀).1 x`. Conclude with `⟨𝒰.X i, 𝒰.f i, 𝒰.map_prop i, hi, h𝒰 _ _ (Presieve.ofArrows.mk i)⟩`.
-/
theorem cover_hit {X : Scheme.{0}} (S : Sieve X) (hS : S ∈ Scheme.etaleTopology X) (x : X) :
    ∃ (U : Scheme.{0}) (w : U ⟶ X), Etale w ∧ x ∈ Set.range w ∧ S.arrows w := by
  obtain ⟨𝒰, h𝒰⟩ := (Scheme.mem_grothendieckTopology_iff).1 hS
  obtain ⟨i, hi⟩ := ((Scheme.presieve₀_mem_precoverage_iff _).1 𝒰.mem₀).1 x
  exact ⟨𝒰.X i, 𝒰.f i, 𝒰.map_prop i, hi, h𝒰 _ _ (Presieve.ofArrows.mk i)⟩

/- English proof (translation)
Introduce `R _ M X s x`. Establish `hS` using `Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) (U := op X) s`. Take `⟨U, w, hw, hx, t, ht⟩` from `cover_hit _ hS x`. Conclude with `⟨U, w, hw, hx, t, ht.symm⟩`.
-/
theorem LeafOfRingsLocSurj_of : LateralTheory.E.E8.TwSec.LeafOfRingsLocSurj := by
  intro R _ M X s x
  have hS := Presheaf.imageSieve_mem Scheme.etaleTopology
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) (U := op X) s
  obtain ⟨U, w, hw, hx, t, ht⟩ := cover_hit _ hS x
  exact ⟨U, w, hw, hx, t, ht.symm⟩

end LateralTheory.E.LeafOfRingsLocSurjPf
