import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.SwapLaws

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace PositivityTheory.RgBcC.CxeAvg

open PositivityTheory.RgTw (Mat)

variable {n : ℕ}

abbrev UK (n : ℕ) := Matrix.unitaryGroup (Fin n) ℂ

/- English proof (translation)
Establish `h` using `Matrix.det_of_mem_unitary k.2`. Conclude with `⟨⟨_, _, Unitary.mul_star_self_of_mem h, Unitary.star_mul_self_of_mem h⟩, rfl⟩`.
-/
theorem isUnit_det_unitary (k : UK n) : IsUnit (k.1.det) := by
  have h := Matrix.det_of_mem_unitary k.2
  exact ⟨⟨_, _, Unitary.mul_star_self_of_mem h, Unitary.star_mul_self_of_mem h⟩, rfl⟩

instance instSCMat : SecondCountableTopology (Mat n) :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))

instance instSCUK : SecondCountableTopology (UK n) :=
  TopologicalSpace.Subtype.secondCountableTopology ((unitary (Mat n)) : Set (Mat n))

/- English proof (translation)
Use `set μ : Measure (UK n) := Measure.haar`. Use `set ν : Measure (UK n) := μ.map (· * g)`. Use `haveI : ν.IsHaarMeasure := Measure.isHaarMeasure_map_mul_right μ g`. Use `haveI : ν.Regular := inferInstance`. Establish `hsm` using `Measure.isMulLeftInvariant_eq_smul_of_regular ν μ`.

Establish `huniv : ν Set.univ = μ Set.univ`. Simplify using `only [ν]`. Rewrite using `[Measure.map_apply (measurable_mul_const g) MeasurableSet.univ, Set.preimage_univ]`. Establish `hc : ν.haarScalarFactor μ = 1`. Establish `h1` using `congrArg (fun m : Measure (UK n) => m Set.univ) hsm`.

Simplify using `only [Measure.smul_apply, smul_eq_mul] at h1`. Rewrite `h1` using `[huniv]`. Establish `hne : μ Set.univ ≠ 0` using `IsOpen.measure_ne_zero μ isOpen_univ Set.univ_nonempty`. Establish `hfin : μ Set.univ ≠ ⊤` using `measure_ne_top μ _`. Establish `h2 : ((ν.haarScalarFactor μ : NNReal) : ENNReal) = 1`.

Use `(ENNReal.mul_eq_right hne hfin).mp h1.symm` as an intermediate fact. Simplify using `using this`. Conclude with `h2` after adjusting the coercions. Rewrite using `[hsm, hc, one_smul]`.
-/
theorem map_mul_right_haar (g : UK n) :
    (Measure.haar : Measure (UK n)).map (· * g) = Measure.haar := by
  set μ : Measure (UK n) := Measure.haar
  set ν : Measure (UK n) := μ.map (· * g)
  haveI : ν.IsHaarMeasure := Measure.isHaarMeasure_map_mul_right μ g
  haveI : ν.Regular := inferInstance
  have hsm := Measure.isMulLeftInvariant_eq_smul_of_regular ν μ
  have huniv : ν Set.univ = μ Set.univ := by
    simp only [ν]
    rw [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ, Set.preimage_univ]
  have hc : ν.haarScalarFactor μ = 1 := by
    have h1 := congrArg (fun m : Measure (UK n) => m Set.univ) hsm
    simp only [Measure.smul_apply, smul_eq_mul] at h1
    rw [huniv] at h1
    have hne : μ Set.univ ≠ 0 := IsOpen.measure_ne_zero μ isOpen_univ Set.univ_nonempty
    have hfin : μ Set.univ ≠ ⊤ := measure_ne_top μ _
    have h2 : ((ν.haarScalarFactor μ : NNReal) : ENNReal) = 1 := by
      have := (ENNReal.mul_eq_right hne hfin).mp h1.symm
      simpa using this
    exact_mod_cast h2
  rw [hsm, hc, one_smul]

/- English proof (translation)
Establish `hmp : MeasurePreserving (MeasurableEquiv.mulRight g) (Measure.haar : Measure (UK n)) Measure.haar` using `⟨measurable_mul_const g, map_mul_right_haar g⟩`. Conclude with `hmp.integral_comp' f`.
-/
theorem integral_mul_right_haar {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : UK n → E) (g : UK n) :
    ∫ x, f (x * g) ∂(Measure.haar : Measure (UK n)) = ∫ x, f x ∂(Measure.haar : Measure (UK n)) := by
  have hmp : MeasurePreserving (MeasurableEquiv.mulRight g)
      (Measure.haar : Measure (UK n)) Measure.haar :=
    ⟨measurable_mul_const g, map_mul_right_haar g⟩
  exact hmp.integral_comp' f

end PositivityTheory.RgBcC.CxeAvg
