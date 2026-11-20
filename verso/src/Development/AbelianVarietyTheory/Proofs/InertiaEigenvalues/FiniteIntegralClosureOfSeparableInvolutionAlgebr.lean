import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyDvdPowOfAevalEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsAlt
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial

noncomputable section

namespace GlobalTheory.UnitLemma.IntegralFinite

open Matrix

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.TargetStatementAlt.target`. Consider the case `exact _root_.GlobalTheory.TargetStatementAlt.target`. Consider the case `(apply _root_.GlobalTheory.TargetStatementAlt.target <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.TargetStatementAlt.target <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.TargetStatementAlt.target <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.TargetStatementAlt.target ..)`.
-/
theorem isIntegral_matrix_trace {R F : Type} [CommRing R] [Field F] [Algebra R F] {n : Type}
    [Fintype n] [DecidableEq n] (M : Matrix n n F) (hM : IsIntegral R M) : IsIntegral R M.trace := by
  first
  | exact @_root_.GlobalTheory.TargetStatementAlt.target
  | exact _root_.GlobalTheory.TargetStatementAlt.target
  | (apply _root_.GlobalTheory.TargetStatementAlt.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.TargetStatementAlt.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TargetStatementAlt.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TargetStatementAlt.target ..)

variable {K : UQ} (B : InvAlg K)

/- English proof (translation)
Set `bs` to `Module.finBasis K.E B.A`. Rewrite using `[Algebra.trace_eq_matrix_trace bs]`. Conclude with `isIntegral_matrix_trace _ (hx.map ((Algebra.leftMulMatrix bs).restrictScalars K.O))`.
-/
theorem isIntegral_trace {x : B.A} (hx : IsIntegral K.O x) :
    IsIntegral K.O (Algebra.trace K.E B.A x) := by
  let bs := Module.finBasis K.E B.A
  rw [Algebra.trace_eq_matrix_trace bs]
  exact isIntegral_matrix_trace _ (hx.map ((Algebra.leftMulMatrix bs).restrictScalars K.O))

/- English proof (translation)
The claim follows from `IsIntegrallyClosed.isIntegral_iff.mp (isIntegral_trace B hx)`.
-/
theorem trace_mem_range {x : B.A} (hx : IsIntegral K.O x) :
    ∃ c : K.O, algebraMap K.O K.E c = Algebra.trace K.E B.A x :=
  IsIntegrallyClosed.isIntegral_iff.mp (isIntegral_trace B hx)

/- English proof (translation)
Introduce `K B hsep`. Set `bs` to `Module.finBasis K.E B.A`. Use `haveI : Algebra.IsAlgebraic K.O K.E := IsLocalization.isAlgebraic K.E (nonZeroDivisors K.O)`. Use `haveI : Algebra.IsAlgebraic K.O B.A := Algebra.IsAlgebraic.trans K.O K.E B.A`. Take `⟨y, hy, hint⟩` from `Algebra.IsAlgebraic.exists_integral_multiples K.O (Finset.univ.image bs)`.

Establish `hy' : algebraMap K.O K.E y ≠ 0`. Introduce `h`. Conclude with `hy (IsFractionRing.injective K.O K.E (by rw [h, map_zero]))`. Set `b` to `bs.isUnitSMul (w := fun _ => algebraMap K.O K.E y) (fun _ => (Ne.isUnit hy'))`. Establish `hbint : ∀ i, IsIntegral K.O (b i)`.

Introduce `i`. Establish `h` using `hint (bs i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))`. Simplify `h` using `[b, Module.Basis.isUnitSMul_apply, algebraMap_smul]`. Establish `hnd : (Algebra.traceForm K.E B.A).Nondegenerate`. Use `⟨fun a ha => ?_, fun a ha => ?_⟩` and prove the remaining obligations.

Conclude with `Centraliser.eq_zero_of_trace_mul B hsep a (fun z => by simpa [Algebra.traceForm_apply] using ha z)`. Conclude with `Centraliser.eq_zero_of_trace_mul B hsep a (fun z => by simpa [Algebra.traceForm_apply, mul_comm] using ha z)`. Set `d` to `(Algebra.traceForm K.E B.A).dualBasis hnd b`. Establish `hle : Subalgebra.toSubmodule (integralClosure K.O B.A) ≤ Submodule.span K.O (Set.range d)`. Introduce `x hx`.

Establish `hx' : IsIntegral K.O x` using `hx`. Rewrite using `[← d.sum_repr x]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Take `⟨c, hc⟩` from `trace_mem_range B (hx'.mul (hbint i))`. Rewrite using `[LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, ← hc, algebraMap_smul]`.

Conclude with `Submodule.smul_mem _ c (Submodule.subset_span ⟨i, rfl⟩)`. Use `haveI : IsNoetherian K.O (Submodule.span K.O (Set.range d)) := isNoetherian_span_of_finite K.O (Set.finite_range d)`. Use `haveI : IsNoetherian K.O (Subalgebra.toSubmodule (integralClosure K.O B.A)) := isNoetherian_of_le hle`. Conclude with `Module.IsNoetherian.finite K.O (Subalgebra.toSubmodule (integralClosure K.O B.A))`.
-/
theorem finite_integralClosure :
    ∀ (K : UQ) (B : InvAlg K), B.P.Separable → Module.Finite K.O (integralClosure K.O B.A) := by
  intro K B hsep
  classical
  let bs := Module.finBasis K.E B.A
  haveI : Algebra.IsAlgebraic K.O K.E := IsLocalization.isAlgebraic K.E (nonZeroDivisors K.O)
  haveI : Algebra.IsAlgebraic K.O B.A := Algebra.IsAlgebraic.trans K.O K.E B.A
  obtain ⟨y, hy, hint⟩ := Algebra.IsAlgebraic.exists_integral_multiples K.O (Finset.univ.image bs)
  have hy' : algebraMap K.O K.E y ≠ 0 := by
    intro h
    exact hy (IsFractionRing.injective K.O K.E (by rw [h, map_zero]))
  let b := bs.isUnitSMul (w := fun _ => algebraMap K.O K.E y) (fun _ => (Ne.isUnit hy'))
  have hbint : ∀ i, IsIntegral K.O (b i) := by
    intro i
    have h := hint (bs i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    simpa [b, Module.Basis.isUnitSMul_apply, algebraMap_smul] using h
  have hnd : (Algebra.traceForm K.E B.A).Nondegenerate := by
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · exact Centraliser.eq_zero_of_trace_mul B hsep a (fun z => by simpa [Algebra.traceForm_apply] using ha z)
    · exact Centraliser.eq_zero_of_trace_mul B hsep a
        (fun z => by simpa [Algebra.traceForm_apply, mul_comm] using ha z)
  let d := (Algebra.traceForm K.E B.A).dualBasis hnd b
  have hle : Subalgebra.toSubmodule (integralClosure K.O B.A) ≤ Submodule.span K.O (Set.range d) := by
    intro x hx
    have hx' : IsIntegral K.O x := hx
    rw [← d.sum_repr x]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨c, hc⟩ := trace_mem_range B (hx'.mul (hbint i))
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, ← hc, algebraMap_smul]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨i, rfl⟩)
  haveI : IsNoetherian K.O (Submodule.span K.O (Set.range d)) :=
    isNoetherian_span_of_finite K.O (Set.finite_range d)
  haveI : IsNoetherian K.O (Subalgebra.toSubmodule (integralClosure K.O B.A)) := isNoetherian_of_le hle
  exact Module.IsNoetherian.finite K.O (Subalgebra.toSubmodule (integralClosure K.O B.A))

end GlobalTheory.UnitLemma.IntegralFinite
