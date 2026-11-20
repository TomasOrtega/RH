import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI

open CategoryTheory AlgebraicGeometry TopologicalSpace in

/- English proof (translation)
Introduce `X Y _ π y h hsurj c`. Establish `hcomm : ∀ b : Y.presheaf.stalk (π y), (π.stalkMap (genericPoint X)).hom ((Y.presheaf.stalkSpecializes h).hom b) = algebraMap (X.presheaf.stalk y) X.functionField ((π.stalkMap y).hom b)`. Introduce `b`. Conclude with `Scheme.Hom.stalkSpecializes_stalkMap_apply π _ _ ((genericPoint_spec X).specializes (Set.mem_univ y)) b`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨a, rfl⟩`. Take `⟨b, rfl⟩` from `hsurj a`. Conclude with `⟨(Y.presheaf.stalkSpecializes h).hom b, ⟨b, rfl⟩, hcomm b⟩`. Introduce and unpack `⟨z, ⟨b, rfl⟩, rfl⟩`. Conclude with `⟨(π.stalkMap y).hom b, (hcomm b).symm⟩`.
-/
theorem _root_.GlobalTheory.DI.mem_locRing_iff_exists_stalkIm : ∀ {X Y : Scheme.{0}} [IsIntegral X] (π : X ⟶ Y) (y : X) (h : π (genericPoint X) ⤳ π y), Function.Surjective (π.stalkMap y).hom → ∀ c : X.functionField, c ∈ _root_.GlobalTheory.LogDR.locRing y ↔ ∃ z ∈ _root_.GlobalTheory.DI.stalkIm h, (π.stalkMap (genericPoint X)).hom z = c := by
  intro X Y _ π y h hsurj c
  have hcomm : ∀ b : Y.presheaf.stalk (π y),
      (π.stalkMap (genericPoint X)).hom ((Y.presheaf.stalkSpecializes h).hom b) =
        algebraMap (X.presheaf.stalk y) X.functionField ((π.stalkMap y).hom b) := by
    intro b
    exact Scheme.Hom.stalkSpecializes_stalkMap_apply π _ _
      ((genericPoint_spec X).specializes (Set.mem_univ y)) b
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨b, rfl⟩ := hsurj a
    exact ⟨(Y.presheaf.stalkSpecializes h).hom b, ⟨b, rfl⟩, hcomm b⟩
  · rintro ⟨z, ⟨b, rfl⟩, rfl⟩
    exact ⟨(π.stalkMap y).hom b, (hcomm b).symm⟩

end GlobalTheory.DI
