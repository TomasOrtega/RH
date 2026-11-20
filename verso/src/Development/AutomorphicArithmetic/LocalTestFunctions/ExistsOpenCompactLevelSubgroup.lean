import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HopBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.PrjFix
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.NormIntLe
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HomConv
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

/- English proof (translation)
Introduce `K _ _ n r w J hJ`. Set `U : Subgroup (AdelicGLn.FiniteAdelicGL K n)` to `{ carrier := {h | h ∈ AdelicGLn.integralFiniteGL K n ∧ ∀ i, finAt (w i) (finEmb K n h) ∈ J i} mul_mem' := by`. Introduce and unpack `a b ⟨ha, ha'⟩ ⟨hb, hb'⟩`. Use `⟨mul_mem ha hb, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, finAt_mul]`.

Conclude with `mul_mem (ha' i) (hb' i)`. Use the proof step `one_mem' := by`. Use `⟨one_mem _, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[map_one, finAt_one]`. Conclude with `one_mem _`.

Use the proof step `inv_mem' := by`. Introduce and unpack `a ⟨ha, ha'⟩`. Use `⟨inv_mem ha, fun i => ?_⟩` and prove the remaining obligations. Establish `h1 : finAt (w i) (finEmb K n a⁻¹) * finAt (w i) (finEmb K n a) = 1`. Rewrite using `[← finAt_mul, ← map_mul, inv_mul_cancel, map_one, finAt_one]`.

Rewrite using `[eq_inv_of_mul_eq_one_left h1]`. Conclude with `inv_mem (ha' i) }`. Establish `hmem : ∀ h, h ∈ U ↔ h ∈ AdelicGLn.integralFiniteGL K n ∧ ∀ i, finAt (w i) (finEmb K n h) ∈ J i` using `fun h => Iff.rfl`. Establish `hset : (U : Set (AdelicGLn.FiniteAdelicGL K n)) = (AdelicGLn.integralFiniteGL K n : Set (AdelicGLn.FiniteAdelicGL K n)) ∩ ⋂ i, (fun h => finAt (w i) (finEmb K n h)) ⁻¹' (J i : Set (Gw n (w i)))`. Use extensionality with `h`.

Simplify using `only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]`. Conclude with `hmem h`. Establish `hopen : IsOpen (U : Set (AdelicGLn.FiniteAdelicGL K n))`. Rewrite using `[hset]`. Use `(AdelicGLn.isOpen_integralFiniteGL K n).inter (isOpen_iInter_of_finite fun i => ?_)` and prove the remaining obligations.

Conclude with `(hJ i).2.preimage ((continuous_finAt (w i)).comp continuous_finEmb)`. Use `⟨U, hmem, hopen, ?_⟩` and prove the remaining obligations. Conclude with `(AdelicGLn.isCompact_integralFiniteGL K n).of_isClosed_subset (Subgroup.isClosed_of_isOpen U hopen) fun _ h => h.1`.
-/
theorem UpperTheory.exists_open_compact_level_subgroup :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (w : Fin r → Pl K) (J : ∀ i, Subgroup (Gw n (w i))), (∀ i, CO (J i)) →
          ∃ U : Subgroup (AdelicGLn.FiniteAdelicGL K n), (∀ h, h ∈ U ↔ h ∈ AdelicGLn.integralFiniteGL K n ∧ ∀ i, finAt (w i) (finEmb K n h) ∈ J i) ∧
            IsOpen (U : Set (AdelicGLn.FiniteAdelicGL K n)) ∧ IsCompact (U : Set (AdelicGLn.FiniteAdelicGL K n)) := by
  intro K _ _ n r w J hJ
  let U : Subgroup (AdelicGLn.FiniteAdelicGL K n) :=
    { carrier := {h | h ∈ AdelicGLn.integralFiniteGL K n ∧ ∀ i, finAt (w i) (finEmb K n h) ∈ J i}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨mul_mem ha hb, fun i => ?_⟩
        rw [map_mul, finAt_mul]
        exact mul_mem (ha' i) (hb' i)
      one_mem' := by
        refine ⟨one_mem _, fun i => ?_⟩
        rw [map_one, finAt_one]
        exact one_mem _
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨inv_mem ha, fun i => ?_⟩
        have h1 : finAt (w i) (finEmb K n a⁻¹) * finAt (w i) (finEmb K n a) = 1 := by
          rw [← finAt_mul, ← map_mul, inv_mul_cancel, map_one, finAt_one]
        rw [eq_inv_of_mul_eq_one_left h1]
        exact inv_mem (ha' i) }
  have hmem : ∀ h, h ∈ U ↔ h ∈ AdelicGLn.integralFiniteGL K n ∧ ∀ i, finAt (w i) (finEmb K n h) ∈ J i :=
    fun h => Iff.rfl
  have hset : (U : Set (AdelicGLn.FiniteAdelicGL K n)) =
      (AdelicGLn.integralFiniteGL K n : Set (AdelicGLn.FiniteAdelicGL K n)) ∩
        ⋂ i, (fun h => finAt (w i) (finEmb K n h)) ⁻¹' (J i : Set (Gw n (w i))) := by
    ext h
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    exact hmem h
  have hopen : IsOpen (U : Set (AdelicGLn.FiniteAdelicGL K n)) := by
    rw [hset]
    refine (AdelicGLn.isOpen_integralFiniteGL K n).inter (isOpen_iInter_of_finite fun i => ?_)
    exact (hJ i).2.preimage ((continuous_finAt (w i)).comp continuous_finEmb)
  refine ⟨U, hmem, hopen, ?_⟩
  exact (AdelicGLn.isCompact_integralFiniteGL K n).of_isClosed_subset
    (Subgroup.isClosed_of_isOpen U hopen) fun _ h => h.1
