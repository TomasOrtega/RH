import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIsIntegralNoetherianCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqDimStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

/- English proof (translation)
Introduce `K _ A B f hdim hfin`. Take `⟨hBi, -, -⟩` from `GlobalTheory.T.abelianVariety_isIntegral_noetherian_compact K B`. Use `set g := f.hom.left`. Establish `eA : topologicalKrullDim A.X.left = Order.krullDim A.X.left` using `Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := A.X.left))`. Establish `eB : topologicalKrullDim B.X.left = Order.krullDim B.X.left` using `Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := B.X.left))`.

Establish `dA` using `GlobalTheory.T.topologicalKrullDim_abVar_eq_dim K A`. Establish `dB` using `GlobalTheory.T.topologicalKrullDim_abVar_eq_dim K B`. Rewrite `dA` using `[eA]`. Rewrite `dB` using `[eB]`. Establish `hm : StrictMono (g : A.X.left → B.X.left)`.

Introduce `a b hab`. Establish `h1 : g a ≤ g b` using `(show b ⤳ a from hab.1).map g.continuous`. Use `lt_of_le_not_ge h1 fun h2 ↦ hab.2 ?_` and prove the remaining obligations. Establish `e : g b = g a` using `((show g b ⤳ g a from h1).antisymm h2).eq`. Establish `hd` using `(g.isDiscrete_preimage_singleton (g a)).to_subtype`.

Establish `: (⟨b, e⟩ : g ⁻¹' {g a}) ⤳ ⟨a, rfl⟩` using `Topology.IsInducing.subtypeVal.specializes_iff.mp hab.1`. Establish `hba : b = a` using `congrArg Subtype.val this.eq`. Rewrite using `[hba]`. Use `⟨?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hns`.

Establish `hη : genericPoint B.X.left ∉ Set.range g`. Introduce `hη`. Apply `hns` to reduce the goal to its premises. Establish `hc : IsClosed (Set.range g)` using `g.isClosedMap.isClosed_range`. Introduce `y`.

Conclude with `(genericPoint_specializes y).mem_closed hc hη`. Take `⟨l, hl⟩` from `Order.le_krullDim_iff.1 dA.ge`. Establish `hlast : (l.map g hm).last < genericPoint B.X.left`. Use `lt_of_le_not_ge (genericPoint_specializes _) fun h2 ↦ hη ?_` and prove the remaining obligations. Establish `e` using `((genericPoint_specializes ((l.map g hm).last)).antisymm h2).eq`.

Rewrite using `[e, LTSeries.last_map]`. Conclude with `⟨_, rfl⟩`. Use `Order.LTSeries.length_le_krullDim ((l.map g hm).snoc _ hlast)` as an intermediate fact. Rewrite `this` using `[dB, RelSeries.snoc_length, LTSeries.map_length, hl, ← hdim]`. Normalize the coercions in `at this`.

Use linear arithmetic over natural numbers and integers.
-/
theorem surjective_of_isFinite_of_dim_eq : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B),
    A.dim = B.dim → IsFinite f.hom.left → Surjective f.hom.left := by
  intro K _ A B f hdim hfin
  obtain ⟨hBi, -, -⟩ := GlobalTheory.T.abelianVariety_isIntegral_noetherian_compact K B
  set g := f.hom.left
  have eA : topologicalKrullDim A.X.left = Order.krullDim A.X.left :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := A.X.left))
  have eB : topologicalKrullDim B.X.left = Order.krullDim B.X.left :=
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := B.X.left))
  have dA := GlobalTheory.T.topologicalKrullDim_abVar_eq_dim K A
  have dB := GlobalTheory.T.topologicalKrullDim_abVar_eq_dim K B
  rw [eA] at dA
  rw [eB] at dB

  have hm : StrictMono (g : A.X.left → B.X.left) := by
    intro a b hab
    have h1 : g a ≤ g b := (show b ⤳ a from hab.1).map g.continuous
    refine lt_of_le_not_ge h1 fun h2 ↦ hab.2 ?_
    have e : g b = g a := ((show g b ⤳ g a from h1).antisymm h2).eq
    have hd := (g.isDiscrete_preimage_singleton (g a)).to_subtype
    have : (⟨b, e⟩ : g ⁻¹' {g a}) ⤳ ⟨a, rfl⟩ :=
      Topology.IsInducing.subtypeVal.specializes_iff.mp hab.1
    have hba : b = a := congrArg Subtype.val this.eq
    rw [hba]
  refine ⟨?_⟩
  by_contra hns
  have hη : genericPoint B.X.left ∉ Set.range g := by
    intro hη
    apply hns
    have hc : IsClosed (Set.range g) := g.isClosedMap.isClosed_range
    intro y
    exact (genericPoint_specializes y).mem_closed hc hη
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.1 dA.ge
  have hlast : (l.map g hm).last < genericPoint B.X.left := by
    refine lt_of_le_not_ge (genericPoint_specializes _) fun h2 ↦ hη ?_
    have e := ((genericPoint_specializes ((l.map g hm).last)).antisymm h2).eq
    rw [e, LTSeries.last_map]
    exact ⟨_, rfl⟩
  have := Order.LTSeries.length_le_krullDim ((l.map g hm).snoc _ hlast)
  rw [dB, RelSeries.snoc_length, LTSeries.map_length, hl, ← hdim] at this
  norm_cast at this
  omega

end GlobalTheory.AV.AbVar
