import Development.EtaleCohomology.TateTwists.EtaleLocalIffAffineEtaleCoverPointwise

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

/- English proof (translation)
Introduce `U P hP`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨S, hS, hSP⟩ x`. Take `⟨𝒰, hle⟩` from `(Scheme.mem_grothendieckTopology_iff (P := (@Etale : MorphismProperty Scheme.{0}))).mp hS`. Take `⟨i, y, hy⟩` from `((Scheme.presieve₀_mem_precoverage_iff _).mp 𝒰.mem₀).1 x`.

Set `𝒱` to `(𝒰.X i).affineCover`. Take `⟨z, hz⟩` from `𝒱.covers y`. Use `⟨𝒱.X (𝒱.idx y), 𝒱.f (𝒱.idx y) ≫ 𝒰.f i, inferInstance, ?_, ⟨z, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `: Etale (𝒰.f i)` using `𝒰.map_prop i infer_instance`. Simplify using `only [Scheme.Hom.comp_apply, hz, hy]`.

Conclude with `hSP _ _ (S.downward_closed (hle _ _ (Presieve.ofArrows.mk i)) _)`. Introduce `h choose V g hA hE hx hPg using h`. Use `⟨{ arrows := fun W k => P W k, downward_closed := fun {Y Z f} hf k => hP Y Z f k hf }, ?_, ?_⟩` and prove the remaining obligations. Use `(Scheme.mem_grothendieckTopology_iff (P := (@Etale : MorphismProperty Scheme.{0}))).mpr ⟨Scheme.Cover.mkOfCovers (P := (@Etale : MorphismProperty Scheme.{0})) U V g (fun x => ⟨x, hx x⟩) (fun x => hE x), ?_⟩` and prove the remaining obligations. Introduce and unpack `W k ⟨x⟩`.

Conclude with `hPg x`. Introduce `W k hk`. Conclude with `hk`.
-/
theorem etale_sheaf_section_locally_iff_of_presheaf_facts : EtaleLocalIffAffineEtaleCoverPointwise := by
  intro U P hP
  constructor
  · rintro ⟨S, hS, hSP⟩ x
    obtain ⟨𝒰, hle⟩ := (Scheme.mem_grothendieckTopology_iff (P := (@Etale : MorphismProperty Scheme.{0}))).mp hS
    obtain ⟨i, y, hy⟩ := ((Scheme.presieve₀_mem_precoverage_iff _).mp 𝒰.mem₀).1 x
    let 𝒱 := (𝒰.X i).affineCover
    obtain ⟨z, hz⟩ := 𝒱.covers y
    refine ⟨𝒱.X (𝒱.idx y), 𝒱.f (𝒱.idx y) ≫ 𝒰.f i, inferInstance, ?_, ⟨z, ?_⟩, ?_⟩
    · have : Etale (𝒰.f i) := 𝒰.map_prop i
      infer_instance
    · simp only [Scheme.Hom.comp_apply, hz, hy]
    · exact hSP _ _ (S.downward_closed (hle _ _ (Presieve.ofArrows.mk i)) _)
  · intro h
    choose V g hA hE hx hPg using h
    refine ⟨{ arrows := fun W k => P W k, downward_closed := fun {Y Z f} hf k => hP Y Z f k hf }, ?_, ?_⟩
    · refine (Scheme.mem_grothendieckTopology_iff (P := (@Etale : MorphismProperty Scheme.{0}))).mpr ⟨Scheme.Cover.mkOfCovers (P := (@Etale : MorphismProperty Scheme.{0})) U V g (fun x => ⟨x, hx x⟩) (fun x => hE x), ?_⟩
      rintro W k ⟨x⟩
      exact hPg x
    · intro W k hk
      exact hk

end LateralTheory.EtaleFoundations
