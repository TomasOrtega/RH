import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open MeasureTheory PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1 GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

/- English proof (translation)
Introduce `hB hF hH hR hT E _ _ _ n hn D π hπ ι _ Φ₁ Φ₂ T₁ T₂ M k₁ k₂ a1 a2 hfin b1 b2 hv U Uπ Φ t c1 c2 hpi ht`. Set `s : Su E n ι` to `⟨D, π, Φ₁, Φ₂, T₁, T₂, M, k₁, k₂, hn, hπ, a1, a2, hfin, b1, b2, hv⟩`. Set `m : Mid s` to `⟨U, Uπ, Φ, c1, c2, hpi⟩`. Take `⟨p, hp⟩` from `hF E n ι s`. Take `⟨hac, hmul, -⟩` from `hB E n hn`.

Establish `hsum : lInt0 D k₁ k₂ Uπ = fun x => ∑ b, (p.w b).1 x.1 * m.G (ac E n (ldet x) * p.x b) x`. Use function extensionality and compare the values at `fun x => hp m x x`. Establish `hterm` using `fun b => hH E n ι s m (p.w b) (p.mem b) (p.x b) (p.zero b)`. Take `⟨L, hL, -, rfl⟩` from `ht`. Set `w : p.B → π.V` to `fun b => ⟨p.w b, p.mem b⟩`.

Set `e : p.B → (π.V →ₗ[ℂ] ℂ)` to `fun b => { toFun := fun ψ => ψ.1.1 (p.x b).1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }`. Establish `hcentre : ∀ (ψ : Sm E n), ψ ∈ π.V → ∀ g : GA E n, ψ.1 (ac E n (-ldet ((g, 1) : H E n 0)) * ((g, 1) : H E n 0)).1 = ψ.1 g`. Introduce `ψ hψ g`. Conclude with `hπ.1 ψ hψ _ g`. Establish `hspan : ∀ v, L v = ∑ b, e b (L v) • w b`.

Introduce `v`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Establish `h0 : ldet (ac E n (-ldet ((g, 1) : H E n 0)) * ((g, 1) : H E n 0)) = 0`.

Rewrite using `[hmul, hac]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `hR E n ι s p hp m v.1 v.2 _ h0`. Establish `h2 : (L v).1.1 g = ∑ b, (L v).1.1 (p.x b).1 * (p.w b).1 g`. Rewrite using `[← hcentre (L v).1 (L v).2 g, hL v]`.

Use `h1.trans (Finset.sum_congr rfl fun b _ => ?_)` and prove the remaining obligations. Rewrite using `[hcentre _ (p.mem b), hL v, mul_comm]`. Both sides reduce to the same expression. Set `ev : π.V →ₗ[ℂ] ℂ` to `{ toFun := fun ψ => ψ.1.1 g, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }`. Establish `h3 : (∑ b, e b (L v) • w b).1.1 g = ev (∑ b, e b (L v) • w b)` using `rfl`.

Rewrite using `[h3, map_sum]`. Conclude with `h2`. Establish `htr` using `hT π.V p.B L w e hspan`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hsum]`.

Conclude with `integrable_finset_sum _ fun b _ => (hterm b).1`. Rewrite using `[hsum, integral_finset_sum _ fun b _ => (hterm b).1, htr, Finset.sum_div]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[(hterm b).2]`. Use `congr 1`.

Conclude with `(hL (w b) (p.x b).1).symm`.
-/
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.uncutOf_pf :
    Basic → GFac → HalfTerm → RangeW → TrFin → DiscreteGroups.T1.G.UncutHalf := by
  intro hB hF hH hR hT E _ _ _ n hn D π hπ ι _ Φ₁ Φ₂ T₁ T₂ M k₁ k₂ a1 a2 hfin b1 b2 hv U Uπ Φ t c1 c2 hpi ht
  let s : Su E n ι := ⟨D, π, Φ₁, Φ₂, T₁, T₂, M, k₁, k₂, hn, hπ, a1, a2, hfin, b1, b2, hv⟩
  let m : Mid s := ⟨U, Uπ, Φ, c1, c2, hpi⟩
  obtain ⟨p, hp⟩ := hF E n ι s
  obtain ⟨hac, hmul, -⟩ := hB E n hn
  have hsum : lInt0 D k₁ k₂ Uπ = fun x => ∑ b, (p.w b).1 x.1 * m.G (ac E n (ldet x) * p.x b) x :=
    funext fun x => hp m x x
  have hterm := fun b => hH E n ι s m (p.w b) (p.mem b) (p.x b) (p.zero b)
  obtain ⟨L, hL, -, rfl⟩ := ht
  let w : p.B → π.V := fun b => ⟨p.w b, p.mem b⟩
  let e : p.B → (π.V →ₗ[ℂ] ℂ) := fun b =>
    { toFun := fun ψ => ψ.1.1 (p.x b).1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hcentre : ∀ (ψ : Sm E n), ψ ∈ π.V → ∀ g : GA E n,
      ψ.1 (ac E n (-ldet ((g, 1) : H E n 0)) * ((g, 1) : H E n 0)).1 = ψ.1 g := by
    intro ψ hψ g
    exact hπ.1 ψ hψ _ g
  have hspan : ∀ v, L v = ∑ b, e b (L v) • w b := by
    intro v
    apply Subtype.ext
    apply Subtype.ext
    funext g
    have h0 : ldet (ac E n (-ldet ((g, 1) : H E n 0)) * ((g, 1) : H E n 0)) = 0 := by
      rw [hmul, hac]; ring
    have h1 := hR E n ι s p hp m v.1 v.2 _ h0
    have h2 : (L v).1.1 g = ∑ b, (L v).1.1 (p.x b).1 * (p.w b).1 g := by
      rw [← hcentre (L v).1 (L v).2 g, hL v]
      refine h1.trans (Finset.sum_congr rfl fun b _ => ?_)
      rw [hcentre _ (p.mem b), hL v, mul_comm]
      rfl
    let ev : π.V →ₗ[ℂ] ℂ :=
      { toFun := fun ψ => ψ.1.1 g, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have h3 : (∑ b, e b (L v) • w b).1.1 g = ev (∑ b, e b (L v) • w b) := rfl
    rw [h3, map_sum]
    exact h2
  have htr := hT π.V p.B L w e hspan
  refine ⟨?_, ?_⟩
  · rw [hsum]
    exact integrable_finset_sum _ fun b _ => (hterm b).1
  · rw [hsum, integral_finset_sum _ fun b _ => (hterm b).1, htr, Finset.sum_div]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [(hterm b).2]
    congr 1
    exact (hL (w b) (p.x b).1).symm
