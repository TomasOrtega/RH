import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Cartier

/- English proof (translation)
Introduce `Y _ _ B hB`. Establish `hgen : genericPoint Y ∉ (B : Set Y)` using `fun h => hB (eq_top_iff.2 fun x _ => (genericPoint_specializes x).mem_closed B.isClosed h)`. Take `⟨S, hS, hc, hi, hU⟩` from `NoetherianSpace.exists_finite_set_isClosed_irreducible B.isClosed`. Use `(hS.image fun T => if h : IsIrreducible T then h.genericPoint else genericPoint Y).subset fun z hz => ?_` and prove the remaining obligations. Take `⟨T, hT, hzT⟩` from `Set.mem_sUnion.1 (hU.le hz.2)`.

Use `⟨T, hT, ?_⟩` and prove the remaining obligations. Simplify using `only [dif_pos (hi T hT)]`. Establish `hg` using `(hi T hT).isGenericPoint_genericPoint (hc T hT)`. Establish `h₁ : z ≤ (hi T hT).genericPoint` using `hg.specializes hzT`. Establish `h₂ : (hi T hT).genericPoint < genericPoint Y`.

Use `lt_of_le_not_ge (genericPoint_specializes _) fun e => ?_` and prove the remaining obligations. Establish `e' : _ = genericPoint Y` using `(Specializes.antisymm e (genericPoint_specializes _)).eq`. Conclude with `hgen (e' ▸ hU.ge (Set.mem_sUnion.2 ⟨T, hT, hg.mem⟩))`. Assume the negation of the conclusion as `hne`. Establish `h₃` using `Order.coheight_add_one_le (lt_of_le_not_ge h₁ fun e => hne (Specializes.antisymm h₁ e).eq)`.

Establish `h₄` using `Order.coheight_add_one_le h₂`. Rewrite `h₃` using `[hz.1]`. Establish `h₅ : (1 : ℕ∞) + 1 ≤ 1` using `(add_le_add_left (le_add_self.trans h₄) 1).trans h₃`. Conclude with `absurd h₅ (by decide)`.
-/
theorem finite_coheight_one_of_ne_top : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsNoetherian Y]
    (B : Closeds Y), B ≠ ⊤ → {v : Y | Order.coheight v = 1 ∧ v ∈ B}.Finite := by
  intro Y _ _ B hB
  classical
  have hgen : genericPoint Y ∉ (B : Set Y) := fun h =>
    hB (eq_top_iff.2 fun x _ => (genericPoint_specializes x).mem_closed B.isClosed h)
  obtain ⟨S, hS, hc, hi, hU⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible B.isClosed
  refine (hS.image fun T => if h : IsIrreducible T then h.genericPoint else genericPoint Y).subset
    fun z hz => ?_
  obtain ⟨T, hT, hzT⟩ := Set.mem_sUnion.1 (hU.le hz.2)
  refine ⟨T, hT, ?_⟩
  simp only [dif_pos (hi T hT)]
  have hg := (hi T hT).isGenericPoint_genericPoint (hc T hT)
  have h₁ : z ≤ (hi T hT).genericPoint := hg.specializes hzT
  have h₂ : (hi T hT).genericPoint < genericPoint Y := by
    refine lt_of_le_not_ge (genericPoint_specializes _) fun e => ?_
    have e' : _ = genericPoint Y := (Specializes.antisymm e (genericPoint_specializes _)).eq
    exact hgen (e' ▸ hU.ge (Set.mem_sUnion.2 ⟨T, hT, hg.mem⟩))
  by_contra hne
  have h₃ := Order.coheight_add_one_le (lt_of_le_not_ge h₁ fun e =>
    hne (Specializes.antisymm h₁ e).eq)
  have h₄ := Order.coheight_add_one_le h₂
  rw [hz.1] at h₃
  have h₅ : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left (le_add_self.trans h₄) 1).trans h₃
  exact absurd h₅ (by decide)

end GlobalTheory.Cartier
