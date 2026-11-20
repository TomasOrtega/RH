import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.ProbeL

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL in

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem PositivityTheory.Exh.exists_class_isLSeg (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (Δ : Segment k) : ∃ x : IrrGL k, IsLSeg Δ x.rep := by
  obtain ⟨π, hd, hc⟩ := PositivityTheory.Exh.lSegExists k Δ
  refine ⟨⟨Δ.deg, Quotient.mk (IrrRep.setoid _) π⟩, ?_⟩
  obtain ⟨e⟩ : Nonempty ((Quotient.mk (IrrRep.setoid _) π).out.ρ.Equiv π.ρ) :=
    Quotient.mk_out (s := IrrRep.setoid _) π
  exact ⟨hd, IsCosocle.of_equiv hc e.symm (Representation.Equiv.refl _)⟩
