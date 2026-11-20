import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.ProbeL

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL in

/- English proof (translation)
Take `⟨π, hd, hc⟩` from `PositivityTheory.Exh.lSegExists k Δ`. Use `⟨⟨Δ.deg, Quotient.mk (IrrRep.setoid _) π⟩, ?_⟩` and prove the remaining obligations. Take `⟨e⟩ : Nonempty ((Quotient.mk (IrrRep.setoid _) π).out.ρ.Equiv π.ρ)` from `Quotient.mk_out (s := IrrRep.setoid _) π`. Conclude with `⟨hd, IsCosocle.of_equiv hc e.symm (Representation.Equiv.refl _)⟩`.
-/
theorem PositivityTheory.Exh.exists_class_isLSeg (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (Δ : Segment k) : ∃ x : IrrGL k, IsLSeg Δ x.rep := by
  obtain ⟨π, hd, hc⟩ := PositivityTheory.Exh.lSegExists k Δ
  refine ⟨⟨Δ.deg, Quotient.mk (IrrRep.setoid _) π⟩, ?_⟩
  obtain ⟨e⟩ : Nonempty ((Quotient.mk (IrrRep.setoid _) π).out.ρ.Equiv π.ρ) :=
    Quotient.mk_out (s := IrrRep.setoid _) π
  exact ⟨hd, IsCosocle.of_equiv hc e.symm (Representation.Equiv.refl _)⟩
