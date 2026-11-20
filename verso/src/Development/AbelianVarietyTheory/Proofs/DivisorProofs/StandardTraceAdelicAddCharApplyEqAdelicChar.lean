import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct FourierTransform
open MeasureTheory GroundTheory.Automorphic.GJMatrix

namespace GlobalTheory.StdCharEq

/- English proof (translation)
Rewrite using `[← GroundTheory.Global.mixedTrace_homeomorphMixedSpace, GroundTheory.Global.homeomorphMixedSpace_apply, GroundTheory.Global.mixedTrace_apply, Algebra.trace_prod_apply, PI.ProdFormulaE.Tr.trace_pi, PI.ProdFormulaE.Tr.trace_pi]`. Simplify using `only [Algebra.trace_self_apply, Algebra.trace_complex_apply]`.
-/
theorem trace_eq_infiniteTrace (F : Type) [Field F] [NumberField F] (x : InfiniteAdeleRing F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F x) =
      GroundTheory.Global.infiniteTrace F x := by
  classical
  rw [← GroundTheory.Global.mixedTrace_homeomorphMixedSpace, GroundTheory.Global.homeomorphMixedSpace_apply,
    GroundTheory.Global.mixedTrace_apply, Algebra.trace_prod_apply, PI.ProdFormulaE.Tr.trace_pi,
    PI.ProdFormulaE.Tr.trace_pi]
  simp only [Algebra.trace_self_apply, Algebra.trace_complex_apply]

/- English proof (translation)
Introduce `F _ _ ψ hψ`. Establish `hadd : ∀ a b : AF F, (GroundTheory.Global.adelicChar F (a + b) : ℂ) = (GroundTheory.Global.adelicChar F a : ℂ) * (GroundTheory.Global.adelicChar F b : ℂ)` using `fun a b => by`. Rewrite using `[← Circle.coe_mul]`. Conclude with `congrArg _ ((GroundTheory.Global.adelicChar F).map_add_eq_mul a b)`. Establish `hinf : ∀ x : Ainf F, ψ (pairA F x 0) = (GroundTheory.Global.adelicChar F (pairA F x 0) : ℂ)` using `fun x => by`.

Establish `h : GroundTheory.Global.adelicChar F (pairA F x 0) = 𝐞 (-GroundTheory.Global.infiniteTrace F x)` using `GroundTheory.Global.adelicChar_infinite x`. Rewrite using `[GlobalTheory.StdCharFromIsStd.psi_pairA hψ, trace_eq_infiniteTrace, h, Real.fourierChar_apply]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hp : Continuous fun y : Af F => pairA F 0 y` using `continuous_const.prodMk continuous_id`. Establish `hc : Continuous fun a : AF F => (GroundTheory.Global.adelicChar F a : ℂ)` using `continuous_subtype_val.comp GroundTheory.Global.continuous_adelicChar`. Establish `hcl : IsClosed {y : Af F | ψ (pairA F 0 y) = (GroundTheory.Global.adelicChar F (pairA F 0 y) : ℂ)}` using `isClosed_eq (hψ.1.comp hp) (hc.comp hp)`. Establish `hrange : Set.range (algebraMap F (Af F)) ⊆ {y : Af F | ψ (pairA F 0 y) = (GroundTheory.Global.adelicChar F (pairA F 0 y) : ℂ)}`. Introduce and unpack `_ ⟨a, rfl⟩`.

Establish `h1` using `hψ.2.1 a`. Establish `h2 : (GroundTheory.Global.adelicChar F (algebraMap F (AF F) a) : ℂ) = 1`. Establish `h` using `GroundTheory.Global.adelicChar_algebraMap (K := F) a`. Conclude with `(congrArg (fun z : Circle => (z : ℂ)) h).trans Circle.coe_one`. Rewrite `h1` using `[GlobalTheory.AdeleCharTwist.algebraMap_eq_pairA, AddChar.map_add_eq_mul, hinf]`.

Rewrite `h2` using `[GlobalTheory.AdeleCharTwist.algebraMap_eq_pairA, hadd]`. Conclude with `mul_left_cancel₀ (Circle.coe_ne_zero _) (h1.trans h2.symm)`. Establish `hall` using `hcl.closure_subset_iff.2 hrange`. Rewrite `hall` using `[GlobalTheory.AdeleCharTwist.denseRange_fin.closure_range]`. Introduce `x`.

Rewrite using `[GlobalTheory.StdCharFromIsStd.pairA_split x, AddChar.map_add_eq_mul, hadd, hinf]`. Conclude with `congrArg _ (hall (Set.mem_univ x.2))`.
-/
theorem eq_adelicChar : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ x : AF F, ψ x = (GroundTheory.Global.adelicChar F x : ℂ) := by
  intro F _ _ ψ hψ
  have hadd : ∀ a b : AF F, (GroundTheory.Global.adelicChar F (a + b) : ℂ) =
      (GroundTheory.Global.adelicChar F a : ℂ) * (GroundTheory.Global.adelicChar F b : ℂ) := fun a b => by
    rw [← Circle.coe_mul]
    exact congrArg _ ((GroundTheory.Global.adelicChar F).map_add_eq_mul a b)
  have hinf : ∀ x : Ainf F, ψ (pairA F x 0) = (GroundTheory.Global.adelicChar F (pairA F x 0) : ℂ) := fun x => by
    have h : GroundTheory.Global.adelicChar F (pairA F x 0) = 𝐞 (-GroundTheory.Global.infiniteTrace F x) :=
      GroundTheory.Global.adelicChar_infinite x
    rw [GlobalTheory.StdCharFromIsStd.psi_pairA hψ, trace_eq_infiniteTrace, h, Real.fourierChar_apply]
    congr 1
    push_cast
    ring
  have hp : Continuous fun y : Af F => pairA F 0 y := continuous_const.prodMk continuous_id
  have hc : Continuous fun a : AF F => (GroundTheory.Global.adelicChar F a : ℂ) :=
    continuous_subtype_val.comp GroundTheory.Global.continuous_adelicChar
  have hcl : IsClosed {y : Af F | ψ (pairA F 0 y) = (GroundTheory.Global.adelicChar F (pairA F 0 y) : ℂ)} :=
    isClosed_eq (hψ.1.comp hp) (hc.comp hp)
  have hrange : Set.range (algebraMap F (Af F)) ⊆
      {y : Af F | ψ (pairA F 0 y) = (GroundTheory.Global.adelicChar F (pairA F 0 y) : ℂ)} := by
    rintro _ ⟨a, rfl⟩
    have h1 := hψ.2.1 a
    have h2 : (GroundTheory.Global.adelicChar F (algebraMap F (AF F) a) : ℂ) = 1 := by
      have h := GroundTheory.Global.adelicChar_algebraMap (K := F) a
      exact (congrArg (fun z : Circle => (z : ℂ)) h).trans Circle.coe_one
    rw [GlobalTheory.AdeleCharTwist.algebraMap_eq_pairA, AddChar.map_add_eq_mul, hinf] at h1
    rw [GlobalTheory.AdeleCharTwist.algebraMap_eq_pairA, hadd] at h2
    exact mul_left_cancel₀ (Circle.coe_ne_zero _) (h1.trans h2.symm)
  have hall := hcl.closure_subset_iff.2 hrange
  rw [GlobalTheory.AdeleCharTwist.denseRange_fin.closure_range] at hall
  intro x
  rw [GlobalTheory.StdCharFromIsStd.pairA_split x, AddChar.map_add_eq_mul, hadd, hinf]
  exact congrArg _ (hall (Set.mem_univ x.2))

end GlobalTheory.StdCharEq
