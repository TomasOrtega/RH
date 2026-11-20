import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.NormLtOneOfIrreducible

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LocalIntegers

/- English proof (translation)
Use `haveI : Algebra.IsSeparable ℚ_[l] K := Algebra.IsSeparable.of_integral ℚ_[l] K`. Use `haveI : Module.Finite ℤ_[l] (integralClosure ℤ_[l] K) := IsIntegralClosure.finite ℤ_[l] ℚ_[l] K (integralClosure ℤ_[l] K)`. Take `⟨t, ht⟩` from `Module.Finite.fg_top (R := ℤ_[l]) (M := integralClosure ℤ_[l] K)`. Establish `hmem : ∀ x : K, x ∈ OK l K ↔ x ∈ integralClosure ℤ_[l] K`. Introduce `x`.

Rewrite using `[OK_eq]`. Both sides reduce to the same expression. Set `e : integralClosure ℤ_[l] K → OK l K` to `fun x => ⟨x.1, (hmem x.1).2 x.2⟩`. Establish `he : Function.Injective e`. Introduce `x y hxy`.

Conclude with `Subtype.ext (congrArg (fun z : OK l K => (z : K)) hxy)`. Use `⟨t.image e, fun a => ?_⟩` and prove the remaining obligations. Establish `ha : (⟨(a : K), (hmem _).1 a.2⟩ : integralClosure ℤ_[l] K) ∈ Submodule.span ℤ_[l] (t : Set _)`. Rewrite using `[ht]`. Discharge the goal by the elementary cases of `trivial`.

Take `⟨f, -, hf⟩` from `Submodule.mem_span_finset.mp ha`. Use `⟨fun o => f ⟨(o : K), (hmem _).1 o.2⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_image fun x _ y _ hxy => he hxy]`. Establish `h1 : (a : K) = ∑ j ∈ t, ((f j • j : integralClosure ℤ_[l] K) : K)`. Rewrite using `[← AddSubmonoidClass.coe_finsetSum, hf]`.

Rewrite using `[h1, AddSubmonoidClass.coe_finsetSum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `show (((f j • j : integralClosure ℤ_[l] K) : K) : PadicAlgCl l) = ((f j : ℚ_[l]) • ((j : K) : PadicAlgCl l))`. Rewrite using `[SetLike.val_smul, ← algebraMap_smul ℚ_[l] (f j) (j : K)]`. Both sides reduce to the same expression.
-/
theorem exists_finset_generators (l : ℕ) [Fact l.Prime]
    (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] :
    ∃ s : Finset (OK l K), ∀ a : OK l K, ∃ c : OK l K → ℤ_[l],
      (((a : K) : PadicAlgCl l)) = ∑ i ∈ s, ((c i : ℚ_[l]) • (((i : K) : PadicAlgCl l))) := by
  classical
  haveI : Algebra.IsSeparable ℚ_[l] K := Algebra.IsSeparable.of_integral ℚ_[l] K
  haveI : Module.Finite ℤ_[l] (integralClosure ℤ_[l] K) :=
    IsIntegralClosure.finite ℤ_[l] ℚ_[l] K (integralClosure ℤ_[l] K)
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := ℤ_[l]) (M := integralClosure ℤ_[l] K)
  have hmem : ∀ x : K, x ∈ OK l K ↔ x ∈ integralClosure ℤ_[l] K := by
    intro x
    rw [OK_eq]
    rfl
  let e : integralClosure ℤ_[l] K → OK l K := fun x => ⟨x.1, (hmem x.1).2 x.2⟩
  have he : Function.Injective e := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : OK l K => (z : K)) hxy)
  refine ⟨t.image e, fun a => ?_⟩
  have ha : (⟨(a : K), (hmem _).1 a.2⟩ : integralClosure ℤ_[l] K) ∈ Submodule.span ℤ_[l] (t : Set _) := by
    rw [ht]
    trivial
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.mp ha
  refine ⟨fun o => f ⟨(o : K), (hmem _).1 o.2⟩, ?_⟩
  rw [Finset.sum_image fun x _ y _ hxy => he hxy]
  have h1 : (a : K) = ∑ j ∈ t, ((f j • j : integralClosure ℤ_[l] K) : K) := by
    rw [← AddSubmonoidClass.coe_finsetSum, hf]
  rw [h1, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show (((f j • j : integralClosure ℤ_[l] K) : K) : PadicAlgCl l) = ((f j : ℚ_[l]) • ((j : K) : PadicAlgCl l))
  rw [SetLike.val_smul, ← algebraMap_smul ℚ_[l] (f j) (j : K)]
  rfl

end GlobalTheory.CompanionTheory.LocalIntegers
