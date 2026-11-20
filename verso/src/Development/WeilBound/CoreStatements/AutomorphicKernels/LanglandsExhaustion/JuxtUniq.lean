import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.JuxtDefs

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace PositivityTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Take `⟨n, cx⟩` from `x`. Take `⟨m, cy⟩` from `y`. Take `⟨hx1, hxc⟩` from `hx`. Take `⟨hy1, hyc⟩` from `hy`. Establish `hnm : n = m` using `hx1.symm.trans hy1`.

Substitute `hnm` using the available equality. Take `⟨e⟩` from `IsCosocle.unique hxc hyc`. Establish `hc : cx = cy`. Rewrite using `[← Quotient.out_eq cx, ← Quotient.out_eq cy]`. Conclude with `Quotient.sound ⟨e.symm⟩`.

Rewrite using `[hc]`.
-/
theorem eq_of_isLSeg (Δ : Segment k) (x y : IrrGL k) (hx : IsLSeg Δ x.rep) (hy : IsLSeg Δ y.rep) : x = y := by
  obtain ⟨n, cx⟩ := x
  obtain ⟨m, cy⟩ := y
  obtain ⟨hx1, hxc⟩ := hx
  obtain ⟨hy1, hyc⟩ := hy
  have hnm : n = m := hx1.symm.trans hy1
  subst hnm
  obtain ⟨e⟩ := IsCosocle.unique hxc hyc
  have hc : cx = cy := by
    rw [← Quotient.out_eq cx, ← Quotient.out_eq cy]
    exact Quotient.sound ⟨e.symm⟩
  rw [hc]

end PositivityTheory.Exh

end
