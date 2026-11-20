import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CodimOne

/- English proof (translation)
Introduce `X S _ f _ _ V U hV hU z hz`. Assume the negation of the conclusion as `hzm`. Establish `hzU : f z ∉ U` using `fun h => hzm (Or.inl h)`. Establish `hzV : z ∉ V` using `fun h => hzm (Or.inr h)`. Use `set s := f z with hs`.

Set `ξ : X` to `f.fiberι s (genericPoint (f.fiber s))`. Establish `hfξ : f ξ = s` using `(f.range_fiberι s).le ⟨_, rfl⟩`. Establish `hrange : ∀ y : X, f y = s → ξ ⤳ y`. Introduce `y hy`. Take `⟨w, rfl⟩ : y ∈ Set.range (f.fiberι s)` from `(f.range_fiberι s).ge hy`.

Conclude with `(genericPoint_specializes w).map (f.fiberι s).continuous`. Take `⟨x, hxV, hxs⟩` from `hV s`. Establish `hξV : ξ ∈ V` using `(hrange x hxs).mem_open V.isOpen hxV`. Establish `hξz : ξ ⤳ z` using `hrange z rfl`. Establish `hξnez : ξ ≠ z` using `fun h => hzV (h ▸ hξV)`.

Take `⟨u, huU⟩` from `hU`. Establish `hηU : genericPoint S ∈ U` using `(genericPoint_specializes u).mem_open U.isOpen huU`. Establish `hηs : genericPoint S ⤳ f ξ` using `hfξ ▸ genericPoint_specializes s`. Take `⟨ζ, hζξ, hfζ⟩` from `(Flat.generalizingMap f) hηs`. Establish `hζneξ : ζ ≠ ξ`.

Introduce `h`. Apply `hzU` to reduce the goal to its premises. Rewrite using `[← hfξ, ← h, hfζ]`. Conclude with `hηU`. Establish `h1 : z < ξ` using `lt_of_le_not_ge hξz (fun h => hξnez (hξz.antisymm h).eq)`.

Establish `h2 : ξ < ζ` using `lt_of_le_not_ge hζξ (fun h => hζneξ (hζξ.antisymm h).eq)`. Establish `hc : (2 : ℕ∞) ≤ Order.coheight z`. Establish `a` using `Order.coheight_add_one_le h1`. Establish `b` using `Order.coheight_add_one_le h2`. Establish `: (1 : ℕ∞) + 1 ≤ Order.coheight ζ + 1 + 1` using `by gcongr; exact le_add_self`.

Combine the equalities or inequalities in the displayed calculation. Rewrite `hz` using `[ringKrullDim_stalk_eq_coheight]`. Establish `: Order.coheight z ≤ 1` using `by exact_mod_cast hz`. Conclude with `absurd (hc.trans this) (by norm_num)`.
-/
theorem mem_preimage_sup_of_ringKrullDim_stalk_le_one :
    ∀ (X S : Scheme.{0}) [IsIntegral S] (f : X ⟶ S) [Flat f] [GeometricallyIntegral f] (V : X.Opens) (U : S.Opens), (∀ s : S, ∃ x ∈ V, f x = s) → (U : Set S).Nonempty → (∀ z : X, ringKrullDim ((X).presheaf.stalk z) ≤ 1 → z ∈ f ⁻¹ᵁ U ⊔ V) := by
  intro X S _ f _ _ V U hV hU z hz
  by_contra hzm
  have hzU : f z ∉ U := fun h => hzm (Or.inl h)
  have hzV : z ∉ V := fun h => hzm (Or.inr h)
  set s := f z with hs

  let ξ : X := f.fiberι s (genericPoint (f.fiber s))
  have hfξ : f ξ = s := (f.range_fiberι s).le ⟨_, rfl⟩
  have hrange : ∀ y : X, f y = s → ξ ⤳ y := by
    intro y hy
    obtain ⟨w, rfl⟩ : y ∈ Set.range (f.fiberι s) := (f.range_fiberι s).ge hy
    exact (genericPoint_specializes w).map (f.fiberι s).continuous
  obtain ⟨x, hxV, hxs⟩ := hV s
  have hξV : ξ ∈ V := (hrange x hxs).mem_open V.isOpen hxV
  have hξz : ξ ⤳ z := hrange z rfl
  have hξnez : ξ ≠ z := fun h => hzV (h ▸ hξV)

  obtain ⟨u, huU⟩ := hU
  have hηU : genericPoint S ∈ U := (genericPoint_specializes u).mem_open U.isOpen huU
  have hηs : genericPoint S ⤳ f ξ := hfξ ▸ genericPoint_specializes s
  obtain ⟨ζ, hζξ, hfζ⟩ := (Flat.generalizingMap f) hηs
  have hζneξ : ζ ≠ ξ := by
    intro h
    apply hzU
    rw [← hfξ, ← h, hfζ]
    exact hηU
  have h1 : z < ξ := lt_of_le_not_ge hξz (fun h => hξnez (hξz.antisymm h).eq)
  have h2 : ξ < ζ := lt_of_le_not_ge hζξ (fun h => hζneξ (hζξ.antisymm h).eq)
  have hc : (2 : ℕ∞) ≤ Order.coheight z := by
    have a := Order.coheight_add_one_le h1
    have b := Order.coheight_add_one_le h2
    have : (1 : ℕ∞) + 1 ≤ Order.coheight ζ + 1 + 1 := by gcongr; exact le_add_self
    calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ Order.coheight ζ + 1 + 1 := this
      _ ≤ Order.coheight ξ + 1 := by gcongr
      _ ≤ Order.coheight z := a
  rw [ringKrullDim_stalk_eq_coheight] at hz
  have : Order.coheight z ≤ 1 := by exact_mod_cast hz
  exact absurd (hc.trans this) (by norm_num)

end GlobalTheory.CodimOne
