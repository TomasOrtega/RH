import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ScaledBoundInequalityHypothesesOne

namespace PI.UnitaryGroupMassFormula.TBNum

open ComplexConjugate

/- English proof (translation)
Unfold `ReciprocityTheory.ChartRestriction.G.TB.EBasisSt`. Introduce `E _ _ W _ _ _ _ _ ι _ v hv hcard`. Use `haveI : FiniteDimensional ℚ W := Module.Finite.trans E W`. Establish `hinj : Function.Injective v` using `hv.injective`. Establish `hspanQ : Submodule.span ℚ (Set.range v) = ⊤`.

Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Rewrite using `[finrank_span_eq_card hv, hcard, Module.finrank_mul_finrank]`. Establish `hspanE : Submodule.span E (Set.range v) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `x _`.

Establish `hx : x ∈ Submodule.span ℚ (Set.range v)` using `by rw [hspanQ]; trivial`. Conclude with `Submodule.span_le_restrictScalars ℚ E (Set.range v) hx`. Take `⟨b, hbsub, hbspan, hbli⟩` from `exists_linearIndependent E (Set.range v)`. Set `s : Finset ι` to `Finset.univ.filter (fun i => v i ∈ b)`. Establish `hrange : Set.range (fun i : s => v i) = b`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, rfl⟩`. Conclude with `(Finset.mem_filter.mp i.2).2`. Introduce `hx`.

Take `⟨i, rfl⟩` from `hbsub hx`. Conclude with `⟨⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩, rfl⟩`. Establish `hli : LinearIndependent E (fun i : s => v i)`. Set `f : s → b` to `fun i => ⟨v i, (Finset.mem_filter.mp i.2).2⟩`. Establish `hf : Function.Injective f`.

Introduce `i j hij`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `hinj (congrArg Subtype.val hij)`. Conclude with `hbli.comp f hf`. Establish `hspan : Submodule.span E (Set.range fun i : s => v i) = ⊤`.

Rewrite using `[hrange, hbspan, hspanE]`. Use `⟨s, ?_, hli, hspan⟩` and prove the remaining obligations. Establish `hfr` using `finrank_span_eq_card hli`. Rewrite `hfr` using `[hspan, finrank_top, Fintype.card_coe]`. Conclude with `hfr.symm`.
-/
theorem eBasis : ReciprocityTheory.ChartRestriction.G.TB.EBasisSt := by
  unfold ReciprocityTheory.ChartRestriction.G.TB.EBasisSt
  intro E _ _ W _ _ _ _ _ ι _ v hv hcard
  classical
  haveI : FiniteDimensional ℚ W := Module.Finite.trans E W
  have hinj : Function.Injective v := hv.injective
  have hspanQ : Submodule.span ℚ (Set.range v) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hv, hcard, Module.finrank_mul_finrank]
  have hspanE : Submodule.span E (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Submodule.span ℚ (Set.range v) := by rw [hspanQ]; trivial
    exact Submodule.span_le_restrictScalars ℚ E (Set.range v) hx
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent E (Set.range v)
  let s : Finset ι := Finset.univ.filter (fun i => v i ∈ b)
  have hrange : Set.range (fun i : s => v i) = b := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (Finset.mem_filter.mp i.2).2
    · intro hx
      obtain ⟨i, rfl⟩ := hbsub hx
      exact ⟨⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩, rfl⟩
  have hli : LinearIndependent E (fun i : s => v i) := by
    let f : s → b := fun i => ⟨v i, (Finset.mem_filter.mp i.2).2⟩
    have hf : Function.Injective f := by
      intro i j hij
      apply Subtype.ext
      exact hinj (congrArg Subtype.val hij)
    exact hbli.comp f hf
  have hspan : Submodule.span E (Set.range fun i : s => v i) = ⊤ := by
    rw [hrange, hbspan, hspanE]
  refine ⟨s, ?_, hli, hspan⟩
  have hfr := finrank_span_eq_card hli
  rw [hspan, finrank_top, Fintype.card_coe] at hfr
  exact hfr.symm

end PI.UnitaryGroupMassFormula.TBNum
