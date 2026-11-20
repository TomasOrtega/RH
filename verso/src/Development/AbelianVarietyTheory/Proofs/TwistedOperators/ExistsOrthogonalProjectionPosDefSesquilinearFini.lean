import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement
import Formalism.LocalToGlobal.IndefiniteReal.MultLemmas
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSumOfMemMultSpan
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KStableOfIsGKSub
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

namespace GlobalTheory

/- English proof (translation)
Introduce `M _ _ b F hF hpos hherm`. Use `set n := Module.finrank ℂ F`. Set `v : Module.Basis (Fin n) ℂ F` to `Module.finBasis ℂ F`. Set `A : F →ₗ[ℂ] (Fin n → ℂ)` to `LinearMap.pi (fun i => (b (v i : M)).comp F.subtype)`. Set `B : M →ₗ[ℂ] (Fin n → ℂ)` to `{ toFun := fun x i => star (b x (v i : M)) map_add' := by intro x y; funext i; simp [map_add] map_smul' := by intro c x; funext i; simp [mul_comm] }`.

Establish `key : ∀ (y : F) (x : M), (∀ i, b (v i : M) (y : M) = star (b x (v i : M))) → ∀ f ∈ F, b (y : M) f = b x f`. Introduce `y x h f hf`. Establish `hc : (b (y : M)).comp F.subtype = (b x).comp F.subtype`. Use `v.ext (fun i => ?_)` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, Submodule.coe_subtype]`.

Rewrite using `[← hherm _ (v i).2 _ y.2, h i, star_star]`. Use `LinearMap.congr_fun hc ⟨f, hf⟩` as an intermediate fact. Simplify using `using this`. Establish `hinj : Function.Injective A`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`.

Introduce `y hy`. Establish `h0 : ∀ i, b (v i : M) (y : M) = star (b (0 : M) (v i : M))`. Introduce `i`. Use `congrFun hy i` as an intermediate fact. Simplify `this` using `[A]`.

Establish `hyy` using `key y 0 h0 y y.2`. Assume the negation of the conclusion as `hne`. Establish `hne' : (y : M) ≠ 0` using `by simpa using hne`. Use `hpos y y.2 hne'` as an intermediate fact. Rewrite `this` using `[hyy]`.

Simplify using `at this`. Establish `hdim : Module.finrank ℂ F = Module.finrank ℂ (Fin n → ℂ)` using `by simp [n]`. Set `Aeq` to `LinearMap.linearEquivOfInjective A hinj hdim`. Use `⟨F.subtype.comp (Aeq.symm.toLinearMap.comp B), fun x => (Aeq.symm (B x)).2, ?_⟩` and prove the remaining obligations. Introduce `x f hf`.

Use `show b ((Aeq.symm (B x) : F) : M) f = b x f`. Use `key (Aeq.symm (B x)) x ?_ f hf` and prove the remaining obligations. Introduce `i`. Establish `h1 : A (Aeq.symm (B x)) = B x`. Conclude with `Aeq.apply_symm_apply (B x)`.

Use `congrFun h1 i` as an intermediate fact. Simplify `this` using `[A, B]`.
-/
theorem exists_proj_sesq_posDef_finiteDim : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (b : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (F : Submodule ℂ M), FiniteDimensional ℂ F →
    (∀ x ∈ F, x ≠ 0 → 0 < (b x x).re) → (∀ x ∈ F, ∀ y ∈ F, star (b x y) = b y x) →
    ∃ e : M →ₗ[ℂ] M, (∀ x, e x ∈ F) ∧ ∀ x, ∀ f ∈ F, b (e x) f = b x f := by
  intro M _ _ b F hF hpos hherm
  classical
  set n := Module.finrank ℂ F
  let v : Module.Basis (Fin n) ℂ F := Module.finBasis ℂ F
  let A : F →ₗ[ℂ] (Fin n → ℂ) := LinearMap.pi (fun i => (b (v i : M)).comp F.subtype)
  let B : M →ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := fun x i => star (b x (v i : M))
      map_add' := by intro x y; funext i; simp [map_add]
      map_smul' := by intro c x; funext i; simp [mul_comm] }
  have key : ∀ (y : F) (x : M), (∀ i, b (v i : M) (y : M) = star (b x (v i : M))) →
      ∀ f ∈ F, b (y : M) f = b x f := by
    intro y x h f hf
    have hc : (b (y : M)).comp F.subtype = (b x).comp F.subtype := by
      refine v.ext (fun i => ?_)
      simp only [LinearMap.comp_apply, Submodule.coe_subtype]
      rw [← hherm _ (v i).2 _ y.2, h i, star_star]
    have := LinearMap.congr_fun hc ⟨f, hf⟩
    simpa using this
  have hinj : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h0 : ∀ i, b (v i : M) (y : M) = star (b (0 : M) (v i : M)) := by
      intro i
      have := congrFun hy i
      simpa [A] using this
    have hyy := key y 0 h0 y y.2
    by_contra hne
    have hne' : (y : M) ≠ 0 := by simpa using hne
    have := hpos y y.2 hne'
    rw [hyy] at this
    simp at this
  have hdim : Module.finrank ℂ F = Module.finrank ℂ (Fin n → ℂ) := by simp [n]
  let Aeq := LinearMap.linearEquivOfInjective A hinj hdim
  refine ⟨F.subtype.comp (Aeq.symm.toLinearMap.comp B), fun x => (Aeq.symm (B x)).2, ?_⟩
  intro x f hf
  show b ((Aeq.symm (B x) : F) : M) f = b x f
  refine key (Aeq.symm (B x)) x ?_ f hf
  intro i
  have h1 : A (Aeq.symm (B x)) = B x := by
    exact Aeq.apply_symm_apply (B x)
  have := congrFun h1 i
  simpa [A, B] using this

end GlobalTheory
