import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulEqUnit

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.VerticalUnit

/- English proof (translation)
Take `⟨T, hT, hc, hi, hU⟩` from `NoetherianSpace.exists_finite_set_isClosed_irreducible hS.isClosed_compl`. Use `(hT.image fun Z => if h : IsIrreducible Z then h.genericPoint else genericPoint X).subset ?_` and prove the remaining obligations. Introduce and unpack `x ⟨h1, hxS⟩`. Take `⟨Z, hZ, hxZ⟩` from `hU.le hxS`. Establish `hg` using `(hi Z hZ).isGenericPoint_genericPoint (hc Z hZ)`.

Use `set z := (hi Z hZ).genericPoint`. Establish `hzS : z ∉ S` using `hU.ge (Set.subset_sUnion_of_mem hZ hg.mem)`. Establish `hxz : x ≤ z` using `hg.specializes hxZ`. Establish `hzη : z < genericPoint X` using `lt_of_le_not_ge (genericPoint_specializes z) fun h => hzS ((show z ⤳ genericPoint X from h).mem_open hS hη)`. Use `⟨Z, hZ, ?_⟩` and prove the remaining obligations.

Simplify using `only [dif_pos (hi Z hZ)]`. Assume the negation of the conclusion as `hne`. Establish `hxlt : x < z` using `lt_of_le_not_ge hxz fun h => hne ((show x ⤳ z from h).antisymm (show z ⤳ x from hxz)).eq.symm`. Establish `a1` using `Order.coheight_add_one_le hxlt`. Establish `a2` using `Order.coheight_add_one_le hzη`.

Rewrite `a1` using `[h1]`. Establish `: (2 : ℕ∞) ≤ 1`. Combine the equalities or inequalities in the displayed calculation. Conclude with `absurd this (by decide)`.
-/
theorem finite_coheight_one_notMem (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (S : Set X) (hS : IsOpen S) (hη : genericPoint X ∈ S) :
    {x : X | Order.coheight x = 1 ∧ x ∉ S}.Finite := by
  classical
  obtain ⟨T, hT, hc, hi, hU⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hS.isClosed_compl
  refine (hT.image fun Z => if h : IsIrreducible Z then h.genericPoint else genericPoint X).subset ?_
  rintro x ⟨h1, hxS⟩
  obtain ⟨Z, hZ, hxZ⟩ := hU.le hxS
  have hg := (hi Z hZ).isGenericPoint_genericPoint (hc Z hZ)
  set z := (hi Z hZ).genericPoint
  have hzS : z ∉ S := hU.ge (Set.subset_sUnion_of_mem hZ hg.mem)
  have hxz : x ≤ z := hg.specializes hxZ
  have hzη : z < genericPoint X := lt_of_le_not_ge (genericPoint_specializes z)
    fun h => hzS ((show z ⤳ genericPoint X from h).mem_open hS hη)
  refine ⟨Z, hZ, ?_⟩
  simp only [dif_pos (hi Z hZ)]
  by_contra hne
  have hxlt : x < z := lt_of_le_not_ge hxz fun h =>
    hne ((show x ⤳ z from h).antisymm (show z ⤳ x from hxz)).eq.symm
  have a1 := Order.coheight_add_one_le hxlt
  have a2 := Order.coheight_add_one_le hzη
  rw [h1] at a1
  have : (2 : ℕ∞) ≤ 1 := by
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ Order.coheight (genericPoint X) + 1 + 1 := by gcongr; exact zero_le
      _ ≤ Order.coheight z + 1 := by gcongr
      _ ≤ 1 := a1
  exact absurd this (by decide)

end GlobalTheory.VerticalUnit
