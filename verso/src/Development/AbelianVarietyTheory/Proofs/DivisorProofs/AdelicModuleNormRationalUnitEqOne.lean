import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAdelesHaarMeasureCovolumeOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CountableOfNumberField
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

open MeasureTheory

namespace GlobalTheory.NormModule

/- English proof (translation)
Establish `e : (inclR (F` using `F) (AF F) z : AE F E) = (1 : AF F) ⊗ₜ[F] z := rfl`. Rewrite using `[e, Algebra.norm_apply, Algebra.norm_apply, ← Algebra.baseChange_lmul, LinearMap.det_baseChange]`.
-/
theorem norm_inclR (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (z : E) :
    Algebra.norm (AF F) (inclR (F := F) (AF F) z : AE F E) = algebraMap F (AF F) (Algebra.norm F z) := by
  have e : (inclR (F := F) (AF F) z : AE F E) = (1 : AF F) ⊗ₜ[F] z := rfl
  rw [e, Algebra.norm_apply, Algebra.norm_apply, ← Algebra.baseChange_lmul, LinearMap.det_baseChange]

/- English proof (translation)
Use `haveI : Nontrivial (AF F) := nontrivial_of_ne 0 1 (fun h => zero_ne_one (congrArg (fun a : AF F => a.1) h))`. Establish `ht : t ≠ 0`. Introduce and unpack `rfl`. Rewrite `hw` using `[map_zero]`. Conclude with `not_isUnit_zero (hw ▸ w.isUnit)`.

Take `⟨ν, hν⟩` from `GlobalTheory.SWQ.exists_adeles_haarMeasure_covolume_one F`. Use `haveI := hν.1`. Establish `h1` using `GlobalTheory.SWQ.modrat_main F 0 ν hν t ht`. Establish `h2` using `GlobalTheory.SWQ.map_unit_mul_eq F ν w`. Establish `e : (fun x : AF F => w • x) = fun x => algebraMap F (AF F) t * x`.

Use function extensionality and compare the values at `x`. Rewrite using `[Units.smul_def, smul_eq_mul, hw]`. Rewrite `h2` using `[e, h1]`. Take `⟨K, hKc, hK0⟩ : ∃ K : Set (AF F), IsCompact K ∧ K ∈ nhds (0 : AF F)` from `exists_compact_mem_nhds 0`. Establish `h3` using `congrArg (fun m : Measure (AF F) => m K) h2`.

Simplify using `only [Measure.smul_apply, smul_eq_mul] at h3`. Establish `h4 : ((distribHaarChar (AF F) w⁻¹ : NNReal) : ENNReal) = 1` using `((ENNReal.mul_left_inj (Measure.measure_pos_of_mem_nhds ν hK0).ne' hKc.measure_lt_top.ne).1 (h3.symm.trans (one_mul _).symm))`. Establish `h5 : distribHaarChar (AF F) w⁻¹ = 1` using `by exact_mod_cast h4`. Rewrite `h5` using `[map_inv, inv_eq_one]`. Conclude with `h5`.
-/
theorem modu_rat (F : Type) [Field F] [NumberField F] (w : (AF F)ˣ) (t : F) (hw : (w : AF F) = algebraMap F (AF F) t) :
    distribHaarChar (AdeleRing (𝓞 F) F) w = 1 := by
  haveI : Nontrivial (AF F) :=
    nontrivial_of_ne 0 1 (fun h => zero_ne_one (congrArg (fun a : AF F => a.1) h))
  have ht : t ≠ 0 := by
    rintro rfl
    rw [map_zero] at hw
    exact not_isUnit_zero (hw ▸ w.isUnit)
  obtain ⟨ν, hν⟩ := GlobalTheory.SWQ.exists_adeles_haarMeasure_covolume_one F
  haveI := hν.1
  have h1 := GlobalTheory.SWQ.modrat_main F 0 ν hν t ht
  have h2 := GlobalTheory.SWQ.map_unit_mul_eq F ν w
  have e : (fun x : AF F => w • x) = fun x => algebraMap F (AF F) t * x := by
    funext x; rw [Units.smul_def, smul_eq_mul, hw]
  rw [e, h1] at h2
  obtain ⟨K, hKc, hK0⟩ : ∃ K : Set (AF F), IsCompact K ∧ K ∈ nhds (0 : AF F) := exists_compact_mem_nhds 0
  have h3 := congrArg (fun m : Measure (AF F) => m K) h2
  simp only [Measure.smul_apply, smul_eq_mul] at h3
  have h4 : ((distribHaarChar (AF F) w⁻¹ : NNReal) : ENNReal) = 1 :=
    ((ENNReal.mul_left_inj (Measure.measure_pos_of_mem_nhds ν hK0).ne' hKc.measure_lt_top.ne).1
      (h3.symm.trans (one_mul _).symm))
  have h5 : distribHaarChar (AF F) w⁻¹ = 1 := by exact_mod_cast h4
  rw [map_inv, inv_eq_one] at h5
  exact h5

end GlobalTheory.NormModule

/- English proof (translation)
Introduce `F E _ _ _ _ _ u z hu`. Apply `GlobalTheory.NormModule.modu_rat F _ (Algebra.norm F z)` to reduce the goal to its premises. Rewrite using `[Units.coe_map, hu, GlobalTheory.NormModule.norm_inclR]`.
-/
theorem GlobalTheory.NormModule.modu_norm_rat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (u : (AE F E)ˣ) (z : E), (u : AE F E) = inclR (AF F) z → (adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) u) = 1 := by
  intro F E _ _ _ _ _ u z hu
  apply GlobalTheory.NormModule.modu_rat F _ (Algebra.norm F z)
  rw [Units.coe_map, hu, GlobalTheory.NormModule.norm_inclR]
