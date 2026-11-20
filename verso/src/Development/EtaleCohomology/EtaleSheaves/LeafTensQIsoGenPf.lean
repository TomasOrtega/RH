import Development.EtaleCohomology.EtaleSheaves.LeafTensQIsoPf
import Development.EtaleCohomology.TateTwists.EtaleComplexAcyclicIffLocalExactness

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTensQIsoGenPf

/- English proof (translation)
Assemble the required witnesses or components as `⟨⊤, (Scheme.etaleTopology.{0}).top_mem U, fun V g _ => h V g⟩`.
-/
theorem loc_top (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, (Scheme.etaleTopology.{0}).top_mem U, fun V g _ => h V g⟩

/- English proof (translation)
Use `⟨M.obj, 𝟙 _, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `U y`. Conclude with `loc_top U _ (fun V g => ⟨Sec.res g y, rfl⟩)`. Introduce `U x hx`. Establish `hx0 : x = 0` using `hx`.

Substitute `hx0` using the available equality. Conclude with `loc_top U _ (fun V g => map_zero _)`. Introduce `U _`. Conclude with `h U`.
-/
theorem flatS_of_sec {R : Type} [CommRing R] (M : Shv R)
    (h : ∀ U : Scheme.{0}, Module.Flat (ULift.{1} R) (Sec M U)) : FlatS M := by
  refine ⟨M.obj, 𝟙 _, ?_, ?_, ?_⟩
  · intro U y
    exact loc_top U _ (fun V g => ⟨Sec.res g y, rfl⟩)
  · intro U x hx
    have hx0 : x = 0 := hx
    subst hx0
    exact loc_top U _ (fun V g => map_zero _)
  · intro U _
    exact h U

/- English proof (translation)
Introduce `R _ I I' J S T f hf hI hI' hJ hflat σ τ hσ hτ ι hι`. Conclude with `LateralTheory.Fin.EtaleTensorPairQuasiIsoOfFlatQuasiIso.intersectionNumber_baseChange R σ τ hσ hτ (fun t => flatS_of_sec _ (hflat t)) f ι (fun U s t w h a b => by rw [hι U s t w h a b]; rfl)`.
-/
theorem LeafTensQIsoGen_of : LateralTheory.E.LeafTensQIsoPf.LeafTensQIsoGen := by
  intro R _ I I' J S T f hf hI hI' hJ hflat σ τ hσ hτ ι hι
  exact LateralTheory.Fin.EtaleTensorPairQuasiIsoOfFlatQuasiIso.intersectionNumber_baseChange R σ τ hσ hτ (fun t => flatS_of_sec _ (hflat t)) f ι
    (fun U s t w h a b => by rw [hι U s t w h a b]; rfl)

end LateralTheory.E.LeafTensQIsoGenPf
