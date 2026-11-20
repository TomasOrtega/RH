import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeCommonAdelicFixatorOfColumnsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeNeTopOfContinuousMulEquivSubgroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteTopologyLatR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeKernelOfSplitCentralOneParamStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeGLAdelicTensorRationalTimesExpIntStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogTensorIdeleAbsDetExpScalarCentreEqMulStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

noncomputable section

open GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.GLOneVol

namespace GlobalTheory.GLOneVol

section Help

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
The claim follows from `Units.ext (RingHom.map_det _ _).symm`.
-/
theorem det_bc {k : ℕ} (γ : GL (Fin k) E) :
    Matrix.GeneralLinearGroup.det (bc (inclR (F := F) (AF F)) γ : GL (Fin k) (AF F ⊗[F] E)) =
      Units.map (inclR (F := F) (AF F)).toMonoidHom (Matrix.GeneralLinearGroup.det γ) :=
  Units.ext (RingHom.map_det _ _).symm

/- English proof (translation)
Establish `h : absE F E x * absE F E x⁻¹ = 1` using `by rw [← map_mul, mul_inv_cancel, map_one]`. Establish `: absE F E x ≠ 0` using `fun h0 => by rw [h0, zero_mul] at h; exact zero_ne_one h`. Conclude with `pos_iff_ne_zero.2 this` after adjusting the coercions.
-/
theorem absE_pos (x : (AF F ⊗[F] E)ˣ) : 0 < (absE F E x : ℝ) := by
  have h : absE F E x * absE F E x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have : absE F E x ≠ 0 := fun h0 => by rw [h0, zero_mul] at h; exact zero_ne_one h
  exact_mod_cast pos_iff_ne_zero.2 this

end Help

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM k`. Use `haveI : IsTotallyComplex E := hCM.2.1`. Take `⟨hTR, hT2⟩` from `GlobalTheory.StdPar.ring_facts (F := F) (E := E)`. Use `set H := ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker with hHdef`. Use `set Γ := (bc (inclR (F := F) (AF F)) : GL (Fin k) E →* GL (Fin k) (AF F ⊗[F] E)).range with hΓdef`.

Establish `hemb` using `(glTens F E k).toHomeomorph.isClosedEmbedding`. Use `haveI : LocallyCompactSpace (GL (Fin k) (AF F ⊗[F] E)) := hemb.locallyCompactSpace`. Use `haveI : SecondCountableTopology (GL (Fin k) (AF F ⊗[F] E)) := hemb.isEmbedding.secondCountableTopology`. Use `haveI : T2Space (GL (Fin k) (AF F ⊗[F] E)) := hemb.isEmbedding.t2Space`. Establish `hcont : Continuous fun g : GL (Fin k) (AF F ⊗[F] E) => absE F E (Matrix.GeneralLinearGroup.det g)` using `GlobalTheory.Doubling.continuous_absE.comp Matrix.GeneralLinearGroup.continuous_det`.

Establish `hcl : IsClosed (H : Set (GL (Fin k) (AF F ⊗[F] E)))` using `isClosed_eq hcont continuous_const`. Use `haveI : LocallyCompactSpace H := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Establish `hΓH : Γ ≤ H`. Introduce and unpack `_ ⟨γ, rfl⟩`. Express the relevant statement in the definitionally equal form `absE F E (Matrix.GeneralLinearGroup.det _) = 1`.

Rewrite using `[det_bc]`. Conclude with `GlobalTheory.Doubling.absE_inclR _`. Establish `hΓΛ : Γ ≤ latR F E k` using `le_sup_left`. Use `⟨inferInstance, inferInstance, ?_, ?_⟩` and prove the remaining obligations. Conclude with `DiscreteTopology.of_continuous_injective (f := fun x : Γ.subgroupOf H => (⟨x.1.1, hΓΛ x.2⟩ : latR F E k)) ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) (fun x y h => by`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `congrArg (fun z : latR F E k => (z : GL (Fin k) (AF F ⊗[F] E))) h)`. Introduce `_ _ π DM hπ hDM`. Break down `Nat.eq_zero_or_pos k with rfl | hk` into its components or cases.

Use `haveI : Subsingleton H := inferInstance haveI : CompactSpace H := inferInstance`. Conclude with `((measure_mono (Set.subset_univ DM)).trans_lt (isCompact_univ.measure_lt_top)).ne`. Take `⟨a, ha, hs⟩` from `GlobalTheory.T.log_tensorIdeleAbs_det_expScalarCentre_eq_mul F E k hk`. Set `s : GL (Fin k) (AF F ⊗[F] E) → ℝ` to `fun g => Real.log (absE F E (Matrix.GeneralLinearGroup.det g) : ℝ) / a`. Use `GlobalTheory.T.finiteCovolume_kernel_of_split_central_oneParam _ H Γ (latR F E k) s (cR F E k) ?_ ?_ (continuous_cR k) (cR_add k) (cR_comm k) ?_ ?_ hΓH rfl inferInstance (fun ν D hν hD => GlobalTheory.T.finite_covolume_GL_adelicTensor_rationalTimesExpInt F E k ν D hν hD) π DM hπ …` and prove the remaining obligations.

Conclude with `((NNReal.continuous_coe.comp hcont).log fun g => (absE_pos _).ne').div_const _`. Introduce `g h`. Simplify using `only [s, map_mul, NNReal.coe_mul]`. Rewrite using `[Real.log_mul (absE_pos _).ne' (absE_pos _).ne', add_div]`. Introduce `t`.

Simplify using `only [s, hs t]`. Clear the denominators using the available nonvanishing facts. Introduce `g`. Simplify using `only [s, div_eq_zero_iff, ha, or_false, hHdef, MonoidHom.mem_ker, MonoidHom.comp_apply]`. Rewrite using `[Real.log_eq_zero]`.

Use `absE_pos (Matrix.GeneralLinearGroup.det g)` as an intermediate fact. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `right`. Use `left`.

Rewrite using `[h]`. Both sides reduce to the same expression. Introduce and unpack `(h | h | h)`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `h` after adjusting the coercions.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem glOne_finvol : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (k : ℕ), LocallyCompactSpace ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker ∧ SecondCountableTopology ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker ∧ DiscreteTopology ((bc (inclR (F := F) (AF F)) : GL (Fin k) E →* GL (Fin k) (AF F ⊗[F] E)).range.subgroupOf ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker) ∧ ∀ [MeasurableSpace (GL (Fin k) (AF F ⊗[F] E))] [BorelSpace (GL (Fin k) (AF F ⊗[F] E))] (π : Measure ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker) (DM : Set ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker), π.IsHaarMeasure → IsFundamentalDomain ((bc (inclR (F := F) (AF F)) : GL (Fin k) E →* GL (Fin k) (AF F ⊗[F] E)).range.subgroupOf ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker) DM π → π DM ≠ ⊤ := by
  intro F E _ _ _ _ _ σ hCM k
  haveI : IsTotallyComplex E := hCM.2.1
  obtain ⟨hTR, hT2⟩ := GlobalTheory.StdPar.ring_facts (F := F) (E := E)
  set H := ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker with hHdef
  set Γ := (bc (inclR (F := F) (AF F)) : GL (Fin k) E →* GL (Fin k) (AF F ⊗[F] E)).range with hΓdef
  have hemb := (glTens F E k).toHomeomorph.isClosedEmbedding
  haveI : LocallyCompactSpace (GL (Fin k) (AF F ⊗[F] E)) := hemb.locallyCompactSpace
  haveI : SecondCountableTopology (GL (Fin k) (AF F ⊗[F] E)) := hemb.isEmbedding.secondCountableTopology
  haveI : T2Space (GL (Fin k) (AF F ⊗[F] E)) := hemb.isEmbedding.t2Space
  have hcont : Continuous fun g : GL (Fin k) (AF F ⊗[F] E) => absE F E (Matrix.GeneralLinearGroup.det g) :=
    GlobalTheory.Doubling.continuous_absE.comp Matrix.GeneralLinearGroup.continuous_det
  have hcl : IsClosed (H : Set (GL (Fin k) (AF F ⊗[F] E))) := isClosed_eq hcont continuous_const
  haveI : LocallyCompactSpace H := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hΓH : Γ ≤ H := by
    rintro _ ⟨γ, rfl⟩
    change absE F E (Matrix.GeneralLinearGroup.det _) = 1
    rw [det_bc]
    exact GlobalTheory.Doubling.absE_inclR _
  have hΓΛ : Γ ≤ latR F E k := le_sup_left
  refine ⟨inferInstance, inferInstance, ?_, ?_⟩
  · exact DiscreteTopology.of_continuous_injective
      (f := fun x : Γ.subgroupOf H => (⟨x.1.1, hΓΛ x.2⟩ : latR F E k))
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      (fun x y h => by
        apply Subtype.ext; apply Subtype.ext
        exact congrArg (fun z : latR F E k => (z : GL (Fin k) (AF F ⊗[F] E))) h)
  · intro _ _ π DM hπ hDM
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · haveI : Subsingleton H := inferInstance
      haveI : CompactSpace H := inferInstance
      exact ((measure_mono (Set.subset_univ DM)).trans_lt (isCompact_univ.measure_lt_top)).ne
    obtain ⟨a, ha, hs⟩ := GlobalTheory.T.log_tensorIdeleAbs_det_expScalarCentre_eq_mul F E k hk
    let s : GL (Fin k) (AF F ⊗[F] E) → ℝ := fun g => Real.log (absE F E (Matrix.GeneralLinearGroup.det g) : ℝ) / a
    refine GlobalTheory.T.finiteCovolume_kernel_of_split_central_oneParam _ H Γ (latR F E k) s (cR F E k) ?_ ?_ (continuous_cR k) (cR_add k) (cR_comm k) ?_ ?_ hΓH rfl
      inferInstance (fun ν D hν hD => GlobalTheory.T.finite_covolume_GL_adelicTensor_rationalTimesExpInt F E k ν D hν hD) π DM hπ hDM
    · exact ((NNReal.continuous_coe.comp hcont).log fun g => (absE_pos _).ne').div_const _
    · intro g h
      simp only [s, map_mul, NNReal.coe_mul]
      rw [Real.log_mul (absE_pos _).ne' (absE_pos _).ne', add_div]
    · intro t
      simp only [s, hs t]
      field_simp
    · intro g
      simp only [s, div_eq_zero_iff, ha, or_false, hHdef, MonoidHom.mem_ker, MonoidHom.comp_apply]
      rw [Real.log_eq_zero]
      have := absE_pos (Matrix.GeneralLinearGroup.det g)
      constructor
      · intro h; right; left; rw [h]; rfl
      · rintro (h | h | h)
        · linarith
        · exact_mod_cast h
        · linarith

end GlobalTheory.GLOneVol
