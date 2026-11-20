import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralGeometricallyConnectedOpenModuli
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompactificationOpenOfClosed
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c O _ β Y U hn _ hU`. Establish `hint` using `isIntegral_open_of_geometricallyConnected E H D l Xo c U hU`. Use `GlobalTheory.IsNormalScheme.of_pred hn` as an intermediate fact. Establish `: IsReduced (gen Y)` using `GlobalTheory.IsNormalScheme.isReduced`. Use `isProper_genStr Y` as an intermediate fact.

Establish `: IsLocallyNoetherian (gen Y)` using `LocallyOfFiniteType.isLocallyNoetherian (genStr Y)`. Use `Y.jQ_open` as an intermediate fact. Establish `hop : IsOpen (compactOf Y U)` using `GlobalTheory.FlatRow.isOpen_closure_of_isOpen_components (fun z => GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents (irreducibleComponent_mem_irreducibleComponents z)) (Y.jQ.isOpenEmbedding.isOpenMap _ U.isOpen)`. Establish `hUirr : IsIrreducible (U : Set (Xo.XF c))` using `isIrreducible_iff_irreducibleSpace.2 (inferInstanceAs (IrreducibleSpace U.toScheme))`. Establish `hirr : IsIrreducible (compactOf Y U)` using `(hUirr.image _ Y.jQ.continuous.continuousOn).closure`.

Set `V : (gen Y).Opens` to `⟨compactOf Y U, hop⟩`. Establish `: IrreducibleSpace V.toScheme` using `Subtype.irreducibleSpace hirr`. Conclude with `⟨V, rfl, isIntegral_of_irreducibleSpace_of_isReduced _⟩`.
-/
theorem exists_open_compactOf_isIntegral :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : (Xo.XF c).Opens), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (gen Y) → IsClosed (U : Set (Xo.XF c)) → GeometricallyConnected (U.ι ≫ toF Xo c) → ∃ V : (gen Y).Opens, (V : Set (gen Y)) = compactOf Y U ∧ IsIntegral V.toScheme := by
  intro E _ _ _ H D l Xo c O _ β Y U hn _ hU
  have hint := isIntegral_open_of_geometricallyConnected E H D l Xo c U hU
  have := GlobalTheory.IsNormalScheme.of_pred hn
  have : IsReduced (gen Y) := GlobalTheory.IsNormalScheme.isReduced
  have := isProper_genStr Y
  have : IsLocallyNoetherian (gen Y) := LocallyOfFiniteType.isLocallyNoetherian (genStr Y)
  have := Y.jQ_open
  have hop : IsOpen (compactOf Y U) := GlobalTheory.FlatRow.isOpen_closure_of_isOpen_components
    (fun z => GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents (irreducibleComponent_mem_irreducibleComponents z))
    (Y.jQ.isOpenEmbedding.isOpenMap _ U.isOpen)
  have hUirr : IsIrreducible (U : Set (Xo.XF c)) :=
    isIrreducible_iff_irreducibleSpace.2 (inferInstanceAs (IrreducibleSpace U.toScheme))
  have hirr : IsIrreducible (compactOf Y U) :=
    (hUirr.image _ Y.jQ.continuous.continuousOn).closure
  let V : (gen Y).Opens := ⟨compactOf Y U, hop⟩
  have : IrreducibleSpace V.toScheme := Subtype.irreducibleSpace hirr
  exact ⟨V, rfl, isIntegral_of_irreducibleSpace_of_isReduced _⟩

end GlobalTheory.DetLine
