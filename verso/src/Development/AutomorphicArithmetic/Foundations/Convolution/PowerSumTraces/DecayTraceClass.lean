import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.DecayTraceClassAlt

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.C

section

variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]

/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem rop_mem (f : CC K n) (v : L2 μ) (hv : v ∈ cuspidalL2 μ) : Rop μ f v ∈ cuspidalL2 μ :=
  UnitaryRep.IsInvariant.integrated_mem _ μ (isClosed_cuspidalL2 μ) (isInvariant_cuspidalL2 μ) _ hv

/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem pc_rop_pc (f : CC K n) : Pc μ ∘L Rop μ f ∘L Pc μ = Rop μ f ∘L Pc μ :=
  ContinuousLinearMap.ext fun v => Submodule.starProjection_eq_self_iff.2
    (rop_mem μ f _ ((cuspidalL2 μ).starProjection_apply_mem v))

/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem adjoint_pc : ContinuousLinearMap.adjoint (Pc μ) = Pc μ :=
  (isSelfAdjoint_starProjection (cuspidalL2 μ)).adjoint_eq

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
private theorem adjoint_rop (f : CC K n) :
    ContinuousLinearMap.adjoint (Rop μ f) = Rop μ (CuspidalProjection.ccStar f) := by
  have := isInvInvariant_of_isMulRightInvariant μ
  exact ((rightRegularRep (Gam K n) μ).adjoint_integrated μ (UnitaryRep.ccToL1 μ f)).trans
    (congrArg _ (CuspidalProjection.ccToL1_ccStar μ f).symm)

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
private theorem adjoint_rop_star (f : CC K n) :
    ContinuousLinearMap.adjoint (Rop μ (CuspidalProjection.ccStar f)) = Rop μ f := by
  rw [← adjoint_rop, ContinuousLinearMap.adjoint_adjoint]

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
private theorem pc_comm (f : CC K n) : Pc μ ∘L Rop μ f = Rop μ f ∘L Pc μ := by
  have h := congrArg ContinuousLinearMap.adjoint (pc_rop_pc μ (CuspidalProjection.ccStar f))
  simp only [ContinuousLinearMap.adjoint_comp, adjoint_pc, adjoint_rop_star] at h
  rw [← pc_rop_pc μ f, ← h, ContinuousLinearMap.comp_assoc]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem hs_of_decay (f : CC K n) (h : PositivityTheory.Rg.Tf.Core.CuspDecay μ f) :
    IsHilbertSchmidt (Rop μ f ∘L Pc μ) := by
  obtain ⟨C, hC⟩ := h 0
  have hT := CuspidalProjection.isHilbertSchmidt_cuspRep_of_bound μ f C
    (fun φ hφ x => by simpa using hC φ hφ x)
  have e : Rop μ f ∘L Pc μ = (cuspidalL2 μ).subtypeL ∘L
      ((cuspRep μ).integrated μ (UnitaryRep.ccToL1 μ f)) ∘L
        (cuspidalL2 μ).orthogonalProjectionOnto := by
    rw [← ContinuousLinearMap.comp_assoc, subtypeL_comp_integrated μ _]
    rfl
  rw [e]
  exact (hT.comp_right _).comp_left _

end

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.ConvolutionTheory.C.decayTraceClass :
    UpperTheory.ConvolutionTheory.C.DecayTraceClass := by
  intro K _ _ n μ _ a g M ha hg _
  have hA := hs_of_decay μ a ha
  have hB : IsHilbertSchmidt (Rop μ g ∘L Pc μ) := by
    have h := (hs_of_decay μ _ hg).adjoint
    rw [ContinuousLinearMap.adjoint_comp, adjoint_pc, adjoint_rop_star, pc_comm] at h
    exact h
  have e : Pc μ ∘L (Rop μ a ∘L M ∘L Rop μ g) ∘L Pc μ =
      (Rop μ a ∘L Pc μ) ∘L (M ∘L (Rop μ g ∘L Pc μ)) :=
    ContinuousLinearMap.ext fun v =>
      DFunLike.congr_fun (pc_comm μ a) (M (Rop μ g (Pc μ v)))
  rw [e]
  exact isTraceClass_comp hA (hB.comp_left M)
