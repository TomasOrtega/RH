import Development.EtaleCohomology.EtaleSheaves.LeafTwSecKillCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E8.TwSec

/- English proof (translation)
The claim follows from `inferInstance`.
-/
theorem jointlySurj_prec (P : MorphismProperty Scheme.{0}) : Scheme.JointlySurjective (Scheme.precoverage P) :=
  inferInstance

/- English proof (translation)
Introduce `R _ M U t ht u`. Establish `h0 : (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).app (op U) t = (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).app (op U) 0`. Establish `: ofRings.sec M U t = 0` using `ht`. Simplify using `only [ofRings.sec] at this`. Rewrite using `[map_zero]`.

Conclude with `this`. Establish `hS` using `Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) t 0 h0`. Take `⟨𝒰, hle⟩` from `Scheme.exists_cover_of_mem_grothendieckTopology hS`. Use `jointlySurj_prec @Etale` as an intermediate fact. Take `⟨i, y, hy⟩` from `𝒰.exists_eq u`.

Use `⟨𝒰.X i, 𝒰.f i, 𝒰.map_prop i, ⟨y, hy⟩, ?_⟩` and prove the remaining obligations. Establish `hm` using `hle _ _ (Presieve.ofArrows.mk i)`. Establish `hm' : ((Scheme.Γ ⋙ M).map (𝒰.f i).op).hom t = ((Scheme.Γ ⋙ M).map (𝒰.f i).op).hom 0` using `hm`. Rewrite `hm'` using `[map_zero]`. Conclude with `hm'`.
-/
theorem LeafOfRingsLocInj_of : LeafOfRingsLocInj := by
  intro R _ M U t ht u
  have h0 : (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).app (op U) t =
      (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).app (op U) 0 := by
    have : ofRings.sec M U t = 0 := ht
    simp only [ofRings.sec] at this
    rw [map_zero]
    exact this
  have hS := Presheaf.equalizerSieve_mem Scheme.etaleTopology
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) t 0 h0
  obtain ⟨𝒰, hle⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hS
  have := jointlySurj_prec @Etale
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq u
  refine ⟨𝒰.X i, 𝒰.f i, 𝒰.map_prop i, ⟨y, hy⟩, ?_⟩
  have hm := hle _ _ (Presieve.ofArrows.mk i)
  have hm' : ((Scheme.Γ ⋙ M).map (𝒰.f i).op).hom t = ((Scheme.Γ ⋙ M).map (𝒰.f i).op).hom 0 := hm
  rw [map_zero] at hm'
  exact hm'

end LateralTheory.E.E8.TwSec
