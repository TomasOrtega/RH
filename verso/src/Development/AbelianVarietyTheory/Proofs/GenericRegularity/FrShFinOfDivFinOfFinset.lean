import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.DivFinOfLawA3
import Formalism.LocalToGlobal.ProjectiveLattices.NrmContPf
import Formalism.LocalToGlobal.ProjectiveLattices.AxHSup
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c _ d δ hd hS`. Unfold `FrShFin`. Unfold `DivFin at hd`. Introduce `Z`. Take `⟨S, hS0, hSv⟩` from `hS Z`.

Use `(Set.Finite.biUnion (t := fun s => {v | d.admitted Z v ∧ v s ≠ 0}) S.finite_toSet fun s hs => hd Z s (hS0 s hs)).subset ?_` and prove the remaining obligations. Introduce and unpack `v ⟨hadm, hδ⟩`. Establish `hnot : ¬ ∀ s ∈ S, v s = 0`. Introduce `hall`. Apply `hδ` to reduce the goal to its premises.

Take `⟨hnd, hcase⟩` from `hadm`. Use `hSv v hnd ?_ hall` and prove the remaining obligations. Break down `hcase with ⟨la, hla, -⟩ | ⟨ht, -⟩` into its components or cases. Conclude with `Or.inl ⟨la, hla⟩`. Conclude with `Or.inr ht`.

Use `push_neg at hnot`. Take `⟨s, hs, hvs⟩` from `hnot`. Conclude with `Set.mem_biUnion (Finset.mem_coe.mpr hs) ⟨hadm, hvs⟩`.
-/
theorem frShFin_of_divFin_of_finset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ [Fintype (Comp Xo c)] (d : ReciprocityTheory.ChartRestriction.G.T0.Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z)) (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ), DivFin d → (∀ Z : Comp Xo c, ∃ S : Finset (Om Z), (∀ s ∈ S, s ≠ 0) ∧ ∀ v : AddValuation (Om Z) (WithTop ℤ), ReciprocityTheory.ChartRestriction.G.T0.IsNormDiscrete v → ((∃ la, ReciprocityTheory.ChartRestriction.G.T0.IsOver (K := c.F) v la) ∨ ReciprocityTheory.ChartRestriction.G.T0.IsTrivOn c.F v) → (∀ s ∈ S, v s = 0) → δ Z v = 0) → FrShFin d δ := by
  intro E _ _ _ H Dw l Xo c _ d δ hd hS
  unfold FrShFin
  unfold DivFin at hd
  intro Z
  obtain ⟨S, hS0, hSv⟩ := hS Z
  refine (Set.Finite.biUnion (t := fun s => {v | d.admitted Z v ∧ v s ≠ 0}) S.finite_toSet
    fun s hs => hd Z s (hS0 s hs)).subset ?_
  rintro v ⟨hadm, hδ⟩
  have hnot : ¬ ∀ s ∈ S, v s = 0 := by
    intro hall
    apply hδ
    obtain ⟨hnd, hcase⟩ := hadm
    refine hSv v hnd ?_ hall
    rcases hcase with ⟨la, hla, -⟩ | ⟨ht, -⟩
    · exact Or.inl ⟨la, hla⟩
    · exact Or.inr ht
  push_neg at hnot
  obtain ⟨s, hs, hvs⟩ := hnot
  exact Set.mem_biUnion (Finset.mem_coe.mpr hs) ⟨hadm, hvs⟩

end GlobalTheory.Reg
