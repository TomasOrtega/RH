import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc
open scoped Pointwise

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

/- English proof (translation)
Take `⟨⟨a, b⟩, hab⟩` from `γ.2`. Establish `h1 : (γ : H E n 0).1 = ratGL E n a` using `by rw [← hab]; rfl`. Express the relevant statement in the definitionally equal form `logAbs (((γ : H E n 0).1 * x.1).val.det) = logAbs x.1.val.det`. Rewrite using `[DiscreteGroups.T1.G.Dcy.logAbs_det_mul', h1, DiscreteGroups.T1.G.Dcy.logAbs_ratGL', zero_add]`.
-/
private theorem ldet_rat_mul {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    (γ : ratH E n 0) (x : H E n 0) : ldet ((γ : H E n 0) * x) = ldet x := by
  obtain ⟨⟨a, b⟩, hab⟩ := γ.2
  have h1 : (γ : H E n 0).1 = ratGL E n a := by rw [← hab]; rfl
  change logAbs (((γ : H E n 0).1 * x.1).val.det) = logAbs x.1.val.det
  rw [DiscreteGroups.T1.G.Dcy.logAbs_det_mul', h1, DiscreteGroups.T1.G.Dcy.logAbs_ratGL', zero_add]

/- English proof (translation)
Introduce `_ E _ _ _ n D f g I hf hg hfi hgi hI hae x hx`. Assume the negation of the conclusion as `hne`. Use `haveI : BorelSpace (H E n 0) := ⟨rfl⟩`. Use `set S : Set (H E n 0) := {y | ldet y ∈ I ∧ f y ≠ g y} with hS`. Establish `hSo : IsOpen S` using `(hI.preimage continuous_ldet).inter (isOpen_ne_fun hf hg)`.

Establish `hSx : S.Nonempty` using `⟨x, hx, hne⟩`. Use `haveI : Countable (ratH E n 0) := DiscreteGroups.T1.G.Dcy.countable_ratH'`. Use `haveI : D.μ.IsMulLeftInvariant := D.haar.1`. Use `haveI : D.μ.IsOpenPosMeasure := D.haar.2.2.1`. Use `haveI : MeasurableConstSMul (ratH E n 0) (H E n 0) := ⟨fun γ => (continuous_const.mul continuous_id : Continuous fun y : H E n 0 => (γ : H E n 0) * y).measurable⟩`.

Use `haveI : SMulInvariantMeasure (ratH E n 0) (H E n 0) D.μ := ⟨fun γ s _ => measure_preimage_mul D.μ (γ : H E n 0) s⟩`. Establish `key : ∀ (δ : ratH E n 0) (y : H E n 0), y ∈ S → (δ : H E n 0) * y ∈ S`. Introduce `δ y hy`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[ldet_rat_mul]`.

Conclude with `hy.1`. Rewrite using `[hfi δ y, hgi δ y]`. Conclude with `hy.2`. Establish `hinv : ∀ γ : ratH E n 0, γ • S = S`. Introduce `γ`.

Apply `Set.Subset.antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `key γ y hy`. Introduce `y hy`. Use `⟨(γ⁻¹ : ratH E n 0) • y, ?_, smul_inv_smul γ y⟩` and prove the remaining obligations.

Conclude with `key γ⁻¹ y hy`. Establish `hnull : D.μ (S ∩ D.F) = 0`. Establish `h0 : D.ν S = 0`. Use `measure_mono_null ?_ (ae_iff.1 hae)` and prove the remaining obligations. Introduce `y hy h`.

Conclude with `hy.2 (h hy.1)`. Rewrite `h0` using `[Dom.ν, Measure.restrict_apply hSo.measurableSet]`. Then use the resulting hypothesis. Establish `hz : D.μ S = 0` using `D.fd.measure_zero_of_invariant S hinv hnull`. Conclude with `(hSo.measure_pos D.μ hSx).ne' hz`.
-/
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.aeEq_pf :
    Basic → AeEq := by
  intro _ E _ _ _ n D f g I hf hg hfi hgi hI hae x hx
  by_contra hne
  haveI : BorelSpace (H E n 0) := ⟨rfl⟩
  set S : Set (H E n 0) := {y | ldet y ∈ I ∧ f y ≠ g y} with hS
  have hSo : IsOpen S :=
    (hI.preimage continuous_ldet).inter (isOpen_ne_fun hf hg)
  have hSx : S.Nonempty := ⟨x, hx, hne⟩
  haveI : Countable (ratH E n 0) := DiscreteGroups.T1.G.Dcy.countable_ratH'
  haveI : D.μ.IsMulLeftInvariant := D.haar.1
  haveI : D.μ.IsOpenPosMeasure := D.haar.2.2.1
  haveI : MeasurableConstSMul (ratH E n 0) (H E n 0) :=
    ⟨fun γ => (continuous_const.mul continuous_id : Continuous fun y : H E n 0 => (γ : H E n 0) * y).measurable⟩
  haveI : SMulInvariantMeasure (ratH E n 0) (H E n 0) D.μ :=
    ⟨fun γ s _ => measure_preimage_mul D.μ (γ : H E n 0) s⟩
  have key : ∀ (δ : ratH E n 0) (y : H E n 0), y ∈ S → (δ : H E n 0) * y ∈ S := by
    intro δ y hy
    refine ⟨?_, ?_⟩
    · rw [ldet_rat_mul]; exact hy.1
    · rw [hfi δ y, hgi δ y]; exact hy.2
  have hinv : ∀ γ : ratH E n 0, γ • S = S := by
    intro γ
    apply Set.Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact key γ y hy
    · intro y hy
      refine ⟨(γ⁻¹ : ratH E n 0) • y, ?_, smul_inv_smul γ y⟩
      exact key γ⁻¹ y hy
  have hnull : D.μ (S ∩ D.F) = 0 := by
    have h0 : D.ν S = 0 := by
      refine measure_mono_null ?_ (ae_iff.1 hae)
      intro y hy h
      exact hy.2 (h hy.1)
    rwa [Dom.ν, Measure.restrict_apply hSo.measurableSet] at h0
  have hz : D.μ S = 0 := D.fd.measure_zero_of_invariant S hinv hnull
  exact (hSo.measure_pos D.μ hSx).ne' hz
