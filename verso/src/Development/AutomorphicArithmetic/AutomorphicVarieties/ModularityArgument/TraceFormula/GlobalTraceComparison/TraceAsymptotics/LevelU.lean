import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

/- English proof (translation)
Simplify using `[UL, hw]`.
-/
private theorem UL_top {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E)
    (hw : IsSplitAt w) : UL n w = ⊤ := by
  simp [UL, hw]

/- English proof (translation)
Apply `IsClosed.isClosedEmbedding_subtypeVal` to reduce the goal to its premises. Rewrite using `[UL_top n w hw]`. Conclude with `isClosed_univ`.
-/
private theorem val_closed {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E)
    (hw : IsSplitAt w) : IsClosedEmbedding (Subtype.val : UL n w → GLw n w) := by
  apply IsClosed.isClosedEmbedding_subtypeVal
  rw [UL_top n w hw]
  exact isClosed_univ

/- English proof (translation)
Use `⟨h.1.comp_isClosedEmbedding (val_closed n w hw), fun k hk x => ?_⟩` and prove the remaining obligations. Establish `hk' : (k : GLw n w) ∈ K'` using `Subgroup.mem_subgroupOf.mp hk`. Conclude with `⟨(h.2 _ hk' _).1, (h.2 _ hk' _).2⟩`.
-/
private theorem hecke_restrict {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E)
    (hw : IsSplitAt w) (K' : Subgroup (GLw n w)) (f : GLw n w → ℂ) (h : IsHecke K' f) :
    IsHecke (K'.subgroupOf (UL n w)) fun x : UL n w => f x.1 := by
  refine ⟨h.1.comp_isClosedEmbedding (val_closed n w hw), fun k hk x => ?_⟩
  have hk' : (k : GLw n w) ∈ K' := Subgroup.mem_subgroupOf.mp hk
  exact ⟨(h.2 _ hk' _).1, (h.2 _ hk' _).2⟩

/- English proof (translation)
Introduce `E _ _ _ n w hw`. Use `⟨?_, fun f hf => ?_⟩` and prove the remaining obligations. Introduce and unpack `f ⟨K', hop, hle, hH⟩`. Use `⟨K'.subgroupOf (UL n w), ?_, ?_, hecke_restrict n w hw K' f hH⟩` and prove the remaining obligations. Conclude with `hop.preimage continuous_subtype_val`.

Introduce `x hx`. Unfold `KL`. Conclude with `Subgroup.mem_subgroupOf.mpr (hle (Subgroup.mem_subgroupOf.mp hx))`. Conclude with `hecke_restrict n w hw _ f hf`.
-/
theorem levelU : LevelU := by
  intro E _ _ _ n w hw
  refine ⟨?_, fun f hf => ?_⟩
  · rintro f ⟨K', hop, hle, hH⟩
    refine ⟨K'.subgroupOf (UL n w), ?_, ?_, hecke_restrict n w hw K' f hH⟩
    · exact hop.preimage continuous_subtype_val
    · intro x hx
      unfold KL
      exact Subgroup.mem_subgroupOf.mpr (hle (Subgroup.mem_subgroupOf.mp hx))
  · exact hecke_restrict n w hw _ f hf

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
