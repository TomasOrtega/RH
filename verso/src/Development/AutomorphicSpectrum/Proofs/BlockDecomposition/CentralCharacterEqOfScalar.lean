import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.TemperedProducts.CentredSegSqInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.ScalarUniq

/- English proof (translation)
Establish `hirr : x.rep.IsIrreducible` using `x.2.rep.irr`. Establish `hnt : Nontrivial x.2.rep.V`. Assume the negation of the conclusion as `hn`. Rewrite `hn` using `[not_nontrivial_iff_subsingleton]`. Take `⟨a, b, hab⟩` from `(hirr.toNontrivial : Nontrivial (Subrepresentation x.rep)).exists_pair_ne`.

Use `hab ?_` and prove the remaining obligations. Use extensionality with `v`. Simplify using `[Subsingleton.elim v 0]`. Take `⟨v, hv⟩` from `exists_ne (0 : x.2.rep.V)`. Establish `e : c • v = c' • v` using `(h v).symm.trans (h' v)`.

Conclude with `smul_left_injective ℂ hv e`.
-/
theorem scalarBy_unique (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : IrrGL k) (t : kˣ) (c c' : ℂ) (h : Zl.ScalarBy x t c) (h' : Zl.ScalarBy x t c') : c = c' := by
  have hirr : x.rep.IsIrreducible := x.2.rep.irr
  have hnt : Nontrivial x.2.rep.V := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    obtain ⟨a, b, hab⟩ := (hirr.toNontrivial : Nontrivial (Subrepresentation x.rep)).exists_pair_ne
    refine hab ?_
    ext v
    simp [Subsingleton.elim v 0]
  obtain ⟨v, hv⟩ := exists_ne (0 : x.2.rep.V)
  have e : c • v = c' • v := (h v).symm.trans (h' v)
  exact smul_left_injective ℂ hv e

end GlobalTheory.CompanionTheory.ScalarUniq
