import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.TraceQuot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization

open MeasureTheory NumberField IsDedekindDomain Filter ValuativeRel
open GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Loc GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open UpperTheory.Gal.LocD UpperTheory.Gal.InertialTypesAlt.G UpperTheory.Gal.Join
open scoped Classical

/- English proof (translation)
Introduce `k k' _ _ _ _ _ _ _ _ ι σ l N hN`. Use `⟨fun x => ?_, fun n t => ⟨fun ht i j hij => ?_, ?_, fun s ht hs i j hij => ?_⟩⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Apply `ι.injective` to reduce the goal to its premises. Rewrite using `[hN.prod, hN.prod]`.

Take `⟨m, hm⟩ : ∃ m, l = m + 1` from `⟨l - 1, by have := hN.cyc.pos; omega⟩`. Substitute `hm` using the available equality. Establish `hord : σ^[m + 1] (x : k') = x` using `hN.cyc.ord x`. Establish `hl : ∀ i, σ^[i] ((Units.map (σ : k' →* k') x : k'ˣ) : k') = σ^[i + 1] (x : k')` using `fun i => by`. Rewrite using `[Function.iterate_succ_apply]`.

Both sides reduce to the same expression. Simplify using `only [hl]`. Rewrite using `[Finset.prod_range_succ, Finset.prod_range_succ' (fun i => σ^[i] (x : k')), hord]`. Both sides reduce to the same expression. Use `lt_of_not_ge fun h => ?_` and prove the remaining obligations.

Establish `h1` using `(GlobalTheory.SplitWeil.nabs_le_iff (N (t j)) (N (t i))).2 h`. Rewrite `h1` using `[hN.abs, hN.abs]`. Conclude with `absurd h1 (not_le.2 (GlobalTheory.SplitWeil.nabs_lt_of_valuation_lt (ht i j hij)))`. Unfold `deltaB`. Use `Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations.

Establish `e : nT n N t i / nT n N t j = N (t i / t j)`. Rewrite using `[map_div]`. Both sides reduce to the same expression. Rewrite using `[e, hN.abs]`. Establish `hj : valuation k' (s j : k') ≠ 0` using `by simp`.

Establish `e : ∀ a, valuation k' (((t * s) a : k'ˣ) : k') = valuation k' (t a : k') * valuation k' (s a : k')` using `fun a => by`. Simplify using the standard rewrite rules. Rewrite using `[e, e]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.Gal.Join.normDom :
    UpperTheory.Gal.Join.NormDom := by
  intro k k' _ _ _ _ _ _ _ _ ι σ l N hN
  refine ⟨fun x => ?_, fun n t => ⟨fun ht i j hij => ?_, ?_, fun s ht hs i j hij => ?_⟩⟩
  · apply Units.ext
    apply ι.injective
    rw [hN.prod, hN.prod]
    obtain ⟨m, hm⟩ : ∃ m, l = m + 1 := ⟨l - 1, by have := hN.cyc.pos; omega⟩
    subst hm
    have hord : σ^[m + 1] (x : k') = x := hN.cyc.ord x
    have hl : ∀ i, σ^[i] ((Units.map (σ : k' →* k') x : k'ˣ) : k') = σ^[i + 1] (x : k') := fun i => by
      rw [Function.iterate_succ_apply]
      rfl
    simp only [hl]
    rw [Finset.prod_range_succ, Finset.prod_range_succ' (fun i => σ^[i] (x : k')), hord]
    rfl
  · refine lt_of_not_ge fun h => ?_
    have h1 := (GlobalTheory.SplitWeil.nabs_le_iff (N (t j)) (N (t i))).2 h
    rw [hN.abs, hN.abs] at h1
    exact absurd h1 (not_le.2 (GlobalTheory.SplitWeil.nabs_lt_of_valuation_lt (ht i j hij)))
  · unfold deltaB
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    have e : nT n N t i / nT n N t j = N (t i / t j) := by
      rw [map_div]
      rfl
    rw [e, hN.abs]
  · have hj : valuation k' (s j : k') ≠ 0 := by simp
    have e : ∀ a, valuation k' (((t * s) a : k'ˣ) : k') = valuation k' (t a : k') * valuation k' (s a : k') := fun a => by
      simp
    rw [e, e]
    calc valuation k' (t i : k') * valuation k' (s i : k')
        ≤ valuation k' (t i : k') * valuation k' (s j : k') := mul_le_mul' le_rfl (hs i j hij)
      _ < valuation k' (t j : k') * valuation k' (s j : k') :=
        mul_lt_mul_of_pos_right (ht i j hij) (zero_lt_iff.2 hj)
