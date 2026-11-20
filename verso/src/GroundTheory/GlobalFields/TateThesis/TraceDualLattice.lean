import Mathlib
import GroundTheory.GlobalFields.TateThesis.TraceFourier

namespace GroundTheory.Global

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical ENNReal nonZeroDivisors

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def traceDualIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K))
    (FractionalIdeal.dual_ne_zero ℤ ℚ I.ne_zero)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_traceDualIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (traceDualIdeal K I : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) := rfl

/- English proof (translation)
The claim follows from `FractionalIdeal.coe_dual ℤ ℚ I.ne_zero`.
-/
theorem coeToSubmodule_traceDualIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((traceDualIdeal K I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) =
      Submodule.traceDual ℤ ℚ (I : Submodule (𝓞 K) K) :=
  FractionalIdeal.coe_dual ℤ ℚ I.ne_zero

/- English proof (translation)
Rewrite using `[coe_traceDualIdeal, FractionalIdeal.dual_eq_mul_inv, coeIdeal_differentIdeal (A := ℤ) (K := ℚ) (L := K) (B := 𝓞 K), mul_inv, inv_inv, mul_comm]`.
-/
theorem traceDualIdeal_eq (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (traceDualIdeal K I : FractionalIdeal (𝓞 K)⁰ K) =
      ((I : FractionalIdeal (𝓞 K)⁰ K) *
        (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K))⁻¹ := by
  rw [coe_traceDualIdeal, FractionalIdeal.dual_eq_mul_inv,
    coeIdeal_differentIdeal (A := ℤ) (K := ℚ) (L := K) (B := 𝓞 K), mul_inv, inv_inv, mul_comm]

/- English proof (translation)
Use `set b := basisOfFractionalIdeal K I`. Establish `hdual : (mixedTraceForm K).dualBasis (mixedTraceForm_nondegenerate K) (fractionalIdealLatticeBasis K I) = fun i => mixedEmbedding K (b.traceDual i)`. Rewrite using `[LinearMap.BilinForm.dualBasis_eq_iff]`. Introduce `i j`. Rewrite using `[fractionalIdealLatticeBasis_apply, mixedTraceForm_mixedEmbedding, Module.Basis.trace_traceDual_mul]`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `hspan : (Submodule.traceDual ℤ ℚ (I : Submodule (𝓞 K) K)).restrictScalars ℤ = Submodule.span ℤ (Set.range b.traceDual)` using `Submodule.traceDual_span_of_basis ℤ (I : Submodule (𝓞 K) K) b (by`. Use extensionality with `x`. Rewrite using `[Submodule.restrictScalars_mem, mem_span_basisOfFractionalIdeal]`. Use the proof step `rfl)`.

Use extensionality with `y`. Rewrite using `[← span_idealLatticeBasis, LinearMap.BilinForm.dualSubmodule_span_of_basis _ (mixedTraceForm_nondegenerate K), hdual, mem_idealLattice, show Set.range (fun i => mixedEmbedding K (b.traceDual i)) = (mixedEmbedding K).toIntAlgHom.toLinearMap '' Set.range b.traceDual by`. Rewrite using `[← Set.range_comp]`. Use the proof step `rfl,`. Use the proof step `← Submodule.map_span, Submodule.mem_map, ← hspan]`.

Simplify using `only [Submodule.restrictScalars_mem, ← coeToSubmodule_traceDualIdeal]`. Both sides reduce to the same expression.
-/
theorem dualSubmodule_idealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (mixedTraceForm K).dualSubmodule (idealLattice K I) = idealLattice K (traceDualIdeal K I) := by
  set b := basisOfFractionalIdeal K I
  have hdual : (mixedTraceForm K).dualBasis (mixedTraceForm_nondegenerate K)
      (fractionalIdealLatticeBasis K I) = fun i => mixedEmbedding K (b.traceDual i) := by
    rw [LinearMap.BilinForm.dualBasis_eq_iff]
    intro i j
    rw [fractionalIdealLatticeBasis_apply, mixedTraceForm_mixedEmbedding,
      Module.Basis.trace_traceDual_mul]
    split_ifs <;> simp
  have hspan : (Submodule.traceDual ℤ ℚ (I : Submodule (𝓞 K) K)).restrictScalars ℤ =
      Submodule.span ℤ (Set.range b.traceDual) :=
    Submodule.traceDual_span_of_basis ℤ (I : Submodule (𝓞 K) K) b (by
      ext x
      rw [Submodule.restrictScalars_mem, mem_span_basisOfFractionalIdeal]
      rfl)
  ext y
  rw [← span_idealLatticeBasis, LinearMap.BilinForm.dualSubmodule_span_of_basis _
    (mixedTraceForm_nondegenerate K), hdual, mem_idealLattice,
    show Set.range (fun i => mixedEmbedding K (b.traceDual i)) =
      (mixedEmbedding K).toIntAlgHom.toLinearMap '' Set.range b.traceDual by
        rw [← Set.range_comp]; rfl,
    ← Submodule.map_span, Submodule.mem_map, ← hspan]
  simp only [Submodule.restrictScalars_mem, ← coeToSubmodule_traceDualIdeal]
  rfl

/- English proof (translation)
Rewrite using `[← dualSubmodule_idealLattice, LinearMap.BilinForm.mem_dualSubmodule]`. Simplify using `only [Submodule.mem_one, algebraMap_int_eq, eq_intCast]`. Conclude with `forall₂_congr fun _ _ => exists_congr fun _ => eq_comm`.
-/
theorem mem_idealLattice_traceDualIdeal_iff (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (y : mixedSpace K) :
    y ∈ idealLattice K (traceDualIdeal K I) ↔
      ∀ x ∈ idealLattice K I, ∃ n : ℤ, mixedTraceForm K y x = n := by
  rw [← dualSubmodule_idealLattice, LinearMap.BilinForm.mem_dualSubmodule]
  simp only [Submodule.mem_one, algebraMap_int_eq, eq_intCast]
  exact forall₂_congr fun _ _ => exists_congr fun _ => eq_comm

/- English proof (translation)
Establish `h` using `covolume_idealLattice K I`. Rewrite `h` using `[ZLattice.covolume_eq_measure_fundamentalDomain _ _ (fundamentalDomain_idealLattice K I)]`. Establish `hF : IsAddFundamentalDomain (idealLattice K I) (ZSpan.fundamentalDomain (fractionalIdealLatticeBasis K I)) (selfDualMeasure K)` using `(fundamentalDomain_idealLattice K I).mono Measure.smul_absolutelyContinuous`. Rewrite using `[ZLattice.covolume_eq_measure_fundamentalDomain _ _ hF, selfDualMeasure, measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ← measureReal_def, h, ENNReal.toReal_pow, ENNReal.toReal_ofNat, inv_pow]`. Clear the denominators using the available nonvanishing facts.
-/
theorem covolume_idealLattice_selfDualMeasure (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (idealLattice K I) (selfDualMeasure K) =
      FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) * √|(discr K : ℝ)| := by
  have h := covolume_idealLattice K I
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ (fundamentalDomain_idealLattice K I)]
    at h
  have hF : IsAddFundamentalDomain (idealLattice K I)
      (ZSpan.fundamentalDomain (fractionalIdealLatticeBasis K I)) (selfDualMeasure K) :=
    (fundamentalDomain_idealLattice K I).mono Measure.smul_absolutelyContinuous
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ hF, selfDualMeasure, measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ← measureReal_def, h, ENNReal.toReal_pow, ENNReal.toReal_ofNat, inv_pow]
  field_simp

end

end GroundTheory.Global
