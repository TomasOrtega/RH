import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.ThetaUnits

/- English proof (translation)
Establish `h` using `isCompact_valBall (K := Qv v) 0`. Rewrite `h` using `[coe_valBall_zero]`. Conclude with `h`.
-/
theorem isCompact_integers (v : Pl) : IsCompact ((𝒪[Qv v] : Set (Qv v))) := by
  have h := isCompact_valBall (K := Qv v) 0
  rw [coe_valBall_zero] at h
  exact h

/- English proof (translation)
Establish `hO` using `isCompact_integers v`. Establish `hP : IsCompact ((𝒪[Qv v] : Set (Qv v)) ×ˢ (MulOpposite.unop ⁻¹' (𝒪[Qv v] : Set (Qv v))))` using `hO.prod ((MulOpposite.opHomeomorph (M := Qv v)).symm.isCompact_preimage.2 hO)`. Establish `hE` using `(Units.isClosedEmbedding_embedProduct (α := Qv v))`. Conclude with `hE.isCompact_preimage hP`.
-/
theorem isCompact_unQ (v : Pl) : IsCompact (unQ v) := by
  have hO := isCompact_integers v
  have hP : IsCompact ((𝒪[Qv v] : Set (Qv v)) ×ˢ
      (MulOpposite.unop ⁻¹' (𝒪[Qv v] : Set (Qv v)))) :=
    hO.prod ((MulOpposite.opHomeomorph (M := Qv v)).symm.isCompact_preimage.2 hO)
  have hE := (Units.isClosedEmbedding_embedProduct (α := Qv v))
  exact hE.isCompact_preimage hP

/- English proof (translation)
The claim follows from `(isCompact_unQ v).isClosed.measurableSet`.
-/
theorem measurableSet_unQ (v : Pl) : MeasurableSet (unQ v) :=
  (isCompact_unQ v).isClosed.measurableSet

instance instFiniteRestrict (v : Pl) : IsFiniteMeasure ((multHaar (Qv v)).restrict (unQ v)) :=
  ⟨by simpa using (isCompact_unQ v).measure_lt_top⟩

/- English proof (translation)
Introduce `Sv`. Use `⟨?_, ?_, isCompact_unQ⟩` and prove the remaining obligations. Unfold `muU infer_instance`. Rewrite using `[ae_all_iff]`. Introduce `v`.

Unfold `muU`. Conclude with `(Measure.quasiMeasurePreserving_eval (fun w : Sv => (multHaar (Qv w.1)).restrict (unQ w.1)) v).ae (ae_restrict_mem (measurableSet_unQ v.1))`.
-/
theorem muU_finite_units : ∀ Sv : Finset Pl, IsFiniteMeasure (muU Sv) ∧ (∀ᵐ u ∂(muU Sv), ∀ v : Sv, u v ∈ unQ v.1) ∧
    ∀ v : Pl, IsCompact (unQ v) := by
  intro Sv
  refine ⟨?_, ?_, isCompact_unQ⟩
  · unfold muU
    infer_instance
  · rw [ae_all_iff]
    intro v
    unfold muU
    exact (Measure.quasiMeasurePreserving_eval
      (fun w : Sv => (multHaar (Qv w.1)).restrict (unQ w.1)) v).ae
      (ae_restrict_mem (measurableSet_unQ v.1))

end GlobalTheory.CompanionTheory.ThetaUnits
