import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

/- English proof (translation)
Introduce `X Y _ _ s _ U hU hiso`. Establish `hg : s (genericPoint Y) = genericPoint X`. Establish `h` using `(genericPoint_spec Y).image s.continuous`. Rewrite `h` using `[Set.image_univ, s.denseRange.closure_range]`. Conclude with `h.eq (genericPoint_spec X)`.

Establish `hmem : genericPoint Y ∈ s ⁻¹ᵁ U`. Express the relevant statement in the definitionally equal form `s (genericPoint Y) ∈ U`. Rewrite using `[hg]`. Conclude with `((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU)`. Establish `h1 : IsIso ((s ∣_ U).stalkMap ⟨genericPoint Y, hmem⟩)` using `((isIso_iff_isIso_stalkMap (s ∣_ U)).1 hiso).2 _`.

Establish `h2 : IsIso (s.stalkMap (genericPoint Y))` using `((MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff (morphismRestrictStalkMap s U ⟨genericPoint Y, hmem⟩)).mp h1`. Establish `h3 : ∀ (x y : X) (_ : x = y) (h : x ⤳ y), IsIso (X.presheaf.stalkSpecializes h)`. Introduce and unpack `x y rfl h`. Rewrite using `[TopCat.Presheaf.stalkSpecializes_refl]`. Use `infer_instance`.

Unfold `functionFieldMap`. Establish `h4` using `h3 _ _ hg (hg ▸ specializes_rfl)`. Conclude with `ConcreteCategory.bijective_of_isIso _`.
-/
theorem functionFieldMap_bijective_of_isIso_restrict : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] (U : X.Opens), (U : Set X).Nonempty → IsIso (s ∣_ U) → Function.Bijective (functionFieldMap s) := by
  intro X Y _ _ s _ U hU hiso
  have hg : s (genericPoint Y) = genericPoint X := by
    have h := (genericPoint_spec Y).image s.continuous
    rw [Set.image_univ, s.denseRange.closure_range] at h
    exact h.eq (genericPoint_spec X)
  have hmem : genericPoint Y ∈ s ⁻¹ᵁ U := by
    change s (genericPoint Y) ∈ U
    rw [hg]
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  have h1 : IsIso ((s ∣_ U).stalkMap ⟨genericPoint Y, hmem⟩) :=
    ((isIso_iff_isIso_stalkMap (s ∣_ U)).1 hiso).2 _
  have h2 : IsIso (s.stalkMap (genericPoint Y)) :=
    ((MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
      (morphismRestrictStalkMap s U ⟨genericPoint Y, hmem⟩)).mp h1
  have h3 : ∀ (x y : X) (_ : x = y) (h : x ⤳ y), IsIso (X.presheaf.stalkSpecializes h) := by
    rintro x y rfl h
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    infer_instance
  unfold functionFieldMap
  have h4 := h3 _ _ hg (hg ▸ specializes_rfl)
  exact ConcreteCategory.bijective_of_isIso _

end GlobalTheory.Discrepancy
