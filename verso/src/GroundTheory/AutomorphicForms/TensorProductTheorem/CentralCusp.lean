import Mathlib
import GroundTheory.AutomorphicForms.TensorProductTheorem.NonemptyAdelicDecomposition
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsDecay
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsMeasure

noncomputable section

namespace GroundTheory.Automorphic

namespace AutomorphicForm

open NumberField MeasureTheory Filter Topology CuspidalSpectrum RightCosetSpace

set_option linter.unusedSectionVars false

attribute [local instance 100] LieRing.ofAssociativeRing

variable (K : Type*) [Field K] [NumberField K] (n : ℕ)

def centralCuspForms : Submodule ℂ (cuspForms K n) where
  carrier := {φ | ∀ (s : {r : ℝ // 0 < r}) (x : AdelicGLn.AdelicGL K n),
    (φ : AdelicGLn.AdelicGL K n → ℂ) (Reduction.centralSection K n s * x) =
      (φ : AdelicGLn.AdelicGL K n → ℂ) x}
  zero_mem' _ _ := rfl
  add_mem' {φ ψ} hφ hψ s x := by
    show (φ : AdelicGLn.AdelicGL K n → ℂ) _ + (ψ : AdelicGLn.AdelicGL K n → ℂ) _ =
      (φ : AdelicGLn.AdelicGL K n → ℂ) x + (ψ : AdelicGLn.AdelicGL K n → ℂ) x
    rw [hφ s x, hψ s x]
  smul_mem' c φ hφ s x := by
    show c * (φ : AdelicGLn.AdelicGL K n → ℂ) _ = c * (φ : AdelicGLn.AdelicGL K n → ℂ) x
    rw [hφ s x]

variable {K n}

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_centralCuspForms {φ : cuspForms K n} :
    φ ∈ centralCuspForms K n ↔ ∀ (s : {r : ℝ // 0 < r}) (x : AdelicGLn.AdelicGL K n),
      (φ : AdelicGLn.AdelicGL K n → ℂ) (Reduction.centralSection K n s * x) =
        (φ : AdelicGLn.AdelicGL K n → ℂ) x :=
  Iff.rfl

/- English proof (translation)
Rewrite using `[← Reduction.centralSection_mul_comm]`. Conclude with `hφ s x`.
-/
theorem apply_mul_centralSection_of_mem {φ : cuspForms K n} (hφ : φ ∈ centralCuspForms K n)
    (x : AdelicGLn.AdelicGL K n) (s : {r : ℝ // 0 < r}) :
    (φ : AdelicGLn.AdelicGL K n → ℂ) (x * Reduction.centralSection K n s) =
      (φ : AdelicGLn.AdelicGL K n → ℂ) x := by
  rw [← Reduction.centralSection_mul_comm]
  exact hφ s x

/- English proof (translation)
Introduce `s x`. Rewrite using `[coe_uActionCusp, coe_uAction]`. Unfold `uActFun`. Establish `e : sliceL (Reduction.centralSection K n s * x) ⟨(φ : AdelicGLn.AdelicGL K n → ℂ), φ.2.1.isSmooth.1⟩ = sliceL x ⟨(φ : AdelicGLn.AdelicGL K n → ℂ), φ.2.1.isSmooth.1⟩` using `Subtype.ext (funext fun y => by show (φ : AdelicGLn.AdelicGL K n → ℂ) (Reduction.centralSection K n s * x * infEmb K n y) = (φ : AdelicGLn.AdelicGL K n → ℂ) (x * infEmb K n y)`. Rewrite using `[mul_assoc]`.

Conclude with `hφ s _)`. Rewrite using `[e]`.
-/
theorem uActionCusp_mem_centralCuspForms (u : UEnv K n) {φ : cuspForms K n}
    (hφ : φ ∈ centralCuspForms K n) : uActionCusp K n u φ ∈ centralCuspForms K n := by
  intro s x
  rw [coe_uActionCusp, coe_uAction]
  unfold uActFun
  have e : sliceL (Reduction.centralSection K n s * x) ⟨(φ : AdelicGLn.AdelicGL K n → ℂ), φ.2.1.isSmooth.1⟩ =
      sliceL x ⟨(φ : AdelicGLn.AdelicGL K n → ℂ), φ.2.1.isSmooth.1⟩ :=
    Subtype.ext (funext fun y => by
      show (φ : AdelicGLn.AdelicGL K n → ℂ) (Reduction.centralSection K n s * x * infEmb K n y) =
        (φ : AdelicGLn.AdelicGL K n → ℂ) (x * infEmb K n y)
      rw [mul_assoc]
      exact hφ s _)
  rw [e]

/- English proof (translation)
The claim follows from `uActionCusp_mem_centralCuspForms _ hφ`.
-/
theorem ρ_mem_centralCuspForms (X : (isExpLieAlgebra K n).lieSubalgebra) {φ : cuspForms K n}
    (hφ : φ ∈ centralCuspForms K n) : (gkModuleCusp K n).ρ X φ ∈ centralCuspForms K n :=
  uActionCusp_mem_centralCuspForms _ hφ

/- English proof (translation)
Introduce `s x`. Use `show (φ : AdelicGLn.AdelicGL K n → ℂ) (Reduction.centralSection K n s * x * infEmb K n k) = (φ : AdelicGLn.AdelicGL K n → ℂ) (x * infEmb K n k)`. Rewrite using `[mul_assoc]`. Conclude with `hφ s _`.
-/
theorem σ_mem_centralCuspForms (k : archCompact K n) {φ : cuspForms K n}
    (hφ : φ ∈ centralCuspForms K n) : (gkModuleCusp K n).σ k φ ∈ centralCuspForms K n := by
  intro s x
  show (φ : AdelicGLn.AdelicGL K n → ℂ) (Reduction.centralSection K n s * x * infEmb K n k) =
    (φ : AdelicGLn.AdelicGL K n → ℂ) (x * infEmb K n k)
  rw [mul_assoc]
  exact hφ s _

/- English proof (translation)
Introduce `s x`. Use `show (φ : AdelicGLn.AdelicGL K n → ℂ) (Reduction.centralSection K n s * x * finEmb K n h) = (φ : AdelicGLn.AdelicGL K n → ℂ) (x * finEmb K n h)`. Rewrite using `[mul_assoc]`. Conclude with `hφ s _`.
-/
theorem finRepCusp_mem_centralCuspForms (h : AdelicGLn.FiniteAdelicGL K n) {φ : cuspForms K n}
    (hφ : φ ∈ centralCuspForms K n) : finRepCusp K n h φ ∈ centralCuspForms K n := by
  intro s x
  show (φ : AdelicGLn.AdelicGL K n → ℂ) (Reduction.centralSection K n s * x * finEmb K n h) =
    (φ : AdelicGLn.AdelicGL K n → ℂ) (x * finEmb K n h)
  rw [mul_assoc]
  exact hφ s _

variable (K n) in

abbrev centralCusp : AdelicGKModule K n (centralCuspForms K n) :=
  cuspSubmodule K n (centralCuspForms K n) (fun X _ hφ => ρ_mem_centralCuspForms X hφ)
    (fun k _ hφ => σ_mem_centralCuspForms k hφ) (fun h _ hφ => finRepCusp_mem_centralCuspForms h hφ)

/- English proof (translation)
Take `⟨C, hC⟩` from `exists_norm_le_of_mem_cuspForms φ.2`. Use `⟨C, fun x => ?_⟩` and prove the remaining obligations. Take `⟨s, y, hy, rfl⟩` from `exists_centralSection_mul_mem_normOneGL x`. Rewrite using `[hφ s y]`. Conclude with `hC y hy`.
-/
theorem exists_norm_le_of_mem_centralCuspForms {φ : cuspForms K n} (hφ : φ ∈ centralCuspForms K n) :
    ∃ C : ℝ, ∀ x, ‖(φ : AdelicGLn.AdelicGL K n → ℂ) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_norm_le_of_mem_cuspForms φ.2
  refine ⟨C, fun x => ?_⟩
  obtain ⟨s, y, hy, rfl⟩ := exists_centralSection_mul_mem_normOneGL x
  rw [hφ s y]
  exact hC y hy

def toOne (g : AdelicGLn.AdelicGL K n) : Reduction.normOneGL K n :=
  ⟨g * (Reduction.centralSection K n (Reduction.detModule K n g))⁻¹,
    mul_centralSection_detModule_inv_mem g⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_toOne (g : AdelicGLn.AdelicGL K n) :
    (toOne g : AdelicGLn.AdelicGL K n) =
      g * (Reduction.centralSection K n (Reduction.detModule K n g))⁻¹ := rfl

/- English proof (translation)
Rewrite using `[coe_toOne, ← map_inv, ← mul_assoc]`. Conclude with `apply_mul_centralSection_of_mem hφ _ _`.
-/
theorem apply_mul_toOne {φ : cuspForms K n} (hφ : φ ∈ centralCuspForms K n)
    (x g : AdelicGLn.AdelicGL K n) :
    (φ : AdelicGLn.AdelicGL K n → ℂ) (x * (toOne g : AdelicGLn.AdelicGL K n)) =
      (φ : AdelicGLn.AdelicGL K n → ℂ) (x * g) := by
  rw [coe_toOne, ← map_inv, ← mul_assoc]
  exact apply_mul_centralSection_of_mem hφ _ _

variable (μ : Measure (Reduction.normOneGL K n)) [μ.IsHaarMeasure]

/- English proof (translation)
The claim follows from `cuspToL2_rightTranslate μ (toOne g) φ ψ (by rw [hψ] funext x exact (apply_mul_toOne hφ x g).symm)`.
-/
theorem cuspFormLp_rightTranslate_eq_rep {φ ψ : cuspForms K n} (hφ : φ ∈ centralCuspForms K n)
    (g : AdelicGLn.AdelicGL K n)
    (hψ : (ψ : AdelicGLn.AdelicGL K n → ℂ) = Automorphic.rightTranslate g (φ : AdelicGLn.AdelicGL K n → ℂ)) :
    cuspToL2 μ ψ = cuspRep μ (toOne g) (cuspToL2 μ φ) :=
  cuspToL2_rightTranslate μ (toOne g) φ ψ (by
    rw [hψ]
    funext x
    exact (apply_mul_toOne hφ x g).symm)

/- English proof (translation)
Establish `e1` using `cuspFormLp_rightTranslate_eq_rep μ hφ (finEmb K n h) (ψ := finRepCusp K n h φ) rfl`. Establish `e2` using `cuspFormLp_rightTranslate_eq_rep μ hψ (finEmb K n h) (ψ := finRepCusp K n h ψ) rfl`. Conclude with `(congrArg₂ (inner ℂ) e1 e2).trans (UnitaryRep.inner_map_map (cuspRep μ) _ _ _)`.
-/
theorem petersson_inner_finiteAdelic_invariant (h : AdelicGLn.FiniteAdelicGL K n) {φ ψ : cuspForms K n}
    (hφ : φ ∈ centralCuspForms K n) (hψ : ψ ∈ centralCuspForms K n) :
    inner ℂ (cuspToL2 μ (finRepCusp K n h φ)) (cuspToL2 μ (finRepCusp K n h ψ)) =
      inner ℂ (cuspToL2 μ φ) (cuspToL2 μ ψ) := by
  have e1 := cuspFormLp_rightTranslate_eq_rep μ hφ (finEmb K n h) (ψ := finRepCusp K n h φ) rfl
  have e2 := cuspFormLp_rightTranslate_eq_rep μ hψ (finEmb K n h) (ψ := finRepCusp K n h ψ) rfl
  exact (congrArg₂ (inner ℂ) e1 e2).trans (UnitaryRep.inner_map_map (cuspRep μ) _ _ _)

/- English proof (translation)
Establish `e1` using `cuspFormLp_rightTranslate_eq_rep μ hφ (infEmb K n k) (ψ := (gkModuleCusp K n).σ k φ) rfl`. Establish `e2` using `cuspFormLp_rightTranslate_eq_rep μ hψ (infEmb K n k) (ψ := (gkModuleCusp K n).σ k ψ) rfl`. Conclude with `(congrArg₂ (inner ℂ) e1 e2).trans (UnitaryRep.inner_map_map (cuspRep μ) _ _ _)`.
-/
theorem petersson_inner_maximalCompact_invariant (k : archCompact K n) {φ ψ : cuspForms K n}
    (hφ : φ ∈ centralCuspForms K n) (hψ : ψ ∈ centralCuspForms K n) :
    inner ℂ (cuspToL2 μ ((gkModuleCusp K n).σ k φ)) (cuspToL2 μ ((gkModuleCusp K n).σ k ψ)) =
      inner ℂ (cuspToL2 μ φ) (cuspToL2 μ ψ) := by
  have e1 := cuspFormLp_rightTranslate_eq_rep μ hφ (infEmb K n k) (ψ := (gkModuleCusp K n).σ k φ) rfl
  have e2 := cuspFormLp_rightTranslate_eq_rep μ hψ (infEmb K n k) (ψ := (gkModuleCusp K n).σ k ψ) rfl
  exact (congrArg₂ (inner ℂ) e1 e2).trans (UnitaryRep.inner_map_map (cuspRep μ) _ _ _)

/- English proof (translation)
Establish `h0 : cuspToL2 μ φ = 0` using `inner_self_eq_zero.1 h`. Conclude with `injOn_cuspToL2 μ (hφ : _) (fun s x => rfl) (h0.trans (map_zero (cuspToL2 μ)).symm)`.
-/
theorem eq_zero_of_petersson_inner_self_eq_zero {φ : cuspForms K n} (hφ : φ ∈ centralCuspForms K n)
    (h : inner ℂ (cuspToL2 μ φ) (cuspToL2 μ φ) = 0) : φ = 0 := by
  have h0 : cuspToL2 μ φ = 0 := inner_self_eq_zero.1 h
  exact injOn_cuspToL2 μ (hφ : _) (fun s x => rfl) (h0.trans (map_zero (cuspToL2 μ)).symm)

local notation "Γ₁" => Reduction.rationalGLOne K n

/- English proof (translation)
Rewrite using `[Submodule.coe_inner, MeasureTheory.L2.inner_def]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [coeFn_cuspToL2 μ φ, coeFn_cuspToL2 μ ψ] with q h1 h2`. Rewrite using `[h1, h2, RCLike.inner_apply']`.
-/
theorem petersson_inner_eq_integral_quotient (φ ψ : cuspForms K n) :
    inner ℂ (cuspToL2 μ φ) (cuspToL2 μ ψ) =
      ∫ q, starRingEnd ℂ (cuspQuot φ.2.1.isLeftInvariant q) * cuspQuot ψ.2.1.isLeftInvariant q
        ∂(quotientMeasure Γ₁ μ) := by
  rw [Submodule.coe_inner, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_cuspToL2 μ φ, coeFn_cuspToL2 μ ψ] with q h1 h2
  rw [h1, h2, RCLike.inner_apply']

def quotTr (φ : cuspForms K n) (g : AdelicGLn.AdelicGL K n) : RightCosetSpace Γ₁ → ℂ :=
  cuspQuot (φ := fun x => (φ : AdelicGLn.AdelicGL K n → ℂ) (x * g)) fun γ x => by
    show (φ : AdelicGLn.AdelicGL K n → ℂ) (AdelicGLn.diagonal K n γ * x * g) =
      (φ : AdelicGLn.AdelicGL K n → ℂ) (x * g)
    rw [mul_assoc]
    exact φ.2.1.isLeftInvariant γ _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem quotTr_mk (φ : cuspForms K n) (g : AdelicGLn.AdelicGL K n) (y : Reduction.normOneGL K n) :
    quotTr φ g (mk Γ₁ y) = (φ : AdelicGLn.AdelicGL K n → ℂ) ((y : AdelicGLn.AdelicGL K n) * g) := rfl

/- English proof (translation)
Use function extensionality and compare the values at `q`. Take `⟨y, rfl⟩` from `mk_surjective Γ₁ q`. Rewrite using `[quotTr_mk, cuspQuot_mk, mul_one]`.
-/
theorem quotTr_one (φ : cuspForms K n) : quotTr φ 1 = cuspQuot φ.2.1.isLeftInvariant := by
  funext q
  obtain ⟨y, rfl⟩ := mk_surjective Γ₁ q
  rw [quotTr_mk, cuspQuot_mk, mul_one]

/- English proof (translation)
The claim follows from `continuous_cuspQuot _ (φ.2.1.continuous.comp (continuous_id.mul continuous_const))`.
-/
theorem continuous_quotTr (φ : cuspForms K n) (g : AdelicGLn.AdelicGL K n) : Continuous (quotTr φ g) :=
  continuous_cuspQuot _ (φ.2.1.continuous.comp (continuous_id.mul continuous_const))

/- English proof (translation)
Use function extensionality and compare the values at `q`. Take `⟨y, rfl⟩` from `mk_surjective Γ₁ q`. Rewrite using `[Function.comp_apply, rightMul_mk, quotTr_mk, quotTr_mk, Subgroup.coe_mul, mul_one, apply_mul_toOne hφ]`.
-/
theorem quotTr_eq_comp {φ : cuspForms K n} (hφ : φ ∈ centralCuspForms K n) (g : AdelicGLn.AdelicGL K n) :
    quotTr φ g = quotTr φ 1 ∘ rightMul Γ₁ (toOne g) := by
  funext q
  obtain ⟨y, rfl⟩ := mk_surjective Γ₁ q
  rw [Function.comp_apply, rightMul_mk, quotTr_mk, quotTr_mk, Subgroup.coe_mul, mul_one,
    apply_mul_toOne hφ]

/- English proof (translation)
Use `set X' := (isExpLieAlgebra K n).ofLie X with hX`. Use `set f : ℝ → ℂ := fun t => (φ : AdelicGLn.AdelicGL K n → ℂ) (g * infEmb K n ((isExpLieAlgebra K n).expG (t • X'))) with hf`. Establish `hsm : IsArchSmooth (φ : AdelicGLn.AdelicGL K n → ℂ)` using `φ.2.1.isSmooth.1`. Use `set g' := g * infEmb K n ((isExpLieAlgebra K n).expG (t • X')) with hg'`. Establish `h1` using `(isExpLieAlgebra K n).hasDerivAt_rightDeriv (hsm g') X' 1`.

Establish `hval : (isExpLieAlgebra K n).rightDeriv X' (archSlice (φ : AdelicGLn.AdelicGL K n → ℂ) g') 1 = ((gkModuleCusp K n).ρ X φ : AdelicGLn.AdelicGL K n → ℂ) g'` using `(uAction_ι_apply X ⟨φ, hsm⟩ g').symm`. Rewrite `h1` using `[hval]`. Establish `h2 : (fun u : ℝ => archSlice (φ : AdelicGLn.AdelicGL K n → ℂ) g' (1 * (isExpLieAlgebra K n).expG (u • X'))) = fun u => f (t + u)`. Use function extensionality and compare the values at `u`. Simplify using `only [archSlice_apply, one_mul, hf, hg', mul_assoc, ← map_mul, ← (isExpLieAlgebra K n).expG_add_smul]`.

Rewrite `h1` using `[h2]`. Establish `h1' : HasDerivAt (fun u => f (t + u)) (((gkModuleCusp K n).ρ X φ : AdelicGLn.AdelicGL K n → ℂ) g') (t - t)`. Rewrite using `[sub_self]`. Conclude with `h1`. Establish `h3` using `h1'.comp_sub_const t t`.

Establish `e : (fun x => f (t + (x - t))) = f`. Use function extensionality and compare the values at `x`. Simplify using `only [add_sub_cancel]`. Rewrite `h3` using `[e]`. Conclude with `h3`.
-/
theorem hasDerivAt_apply_mul_expG (φ : cuspForms K n) (X : (isExpLieAlgebra K n).lieSubalgebra)
    (g : AdelicGLn.AdelicGL K n) (t : ℝ) :
    HasDerivAt (fun t : ℝ => (φ : AdelicGLn.AdelicGL K n → ℂ)
        (g * infEmb K n ((isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie X))))
      (((gkModuleCusp K n).ρ X φ : AdelicGLn.AdelicGL K n → ℂ)
        (g * infEmb K n ((isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie X)))) t := by
  set X' := (isExpLieAlgebra K n).ofLie X with hX
  set f : ℝ → ℂ := fun t =>
    (φ : AdelicGLn.AdelicGL K n → ℂ) (g * infEmb K n ((isExpLieAlgebra K n).expG (t • X'))) with hf
  have hsm : IsArchSmooth (φ : AdelicGLn.AdelicGL K n → ℂ) := φ.2.1.isSmooth.1
  set g' := g * infEmb K n ((isExpLieAlgebra K n).expG (t • X')) with hg'
  have h1 := (isExpLieAlgebra K n).hasDerivAt_rightDeriv (hsm g') X' 1
  have hval : (isExpLieAlgebra K n).rightDeriv X' (archSlice (φ : AdelicGLn.AdelicGL K n → ℂ) g') 1 =
      ((gkModuleCusp K n).ρ X φ : AdelicGLn.AdelicGL K n → ℂ) g' :=
    (uAction_ι_apply X ⟨φ, hsm⟩ g').symm
  rw [hval] at h1
  have h2 : (fun u : ℝ => archSlice (φ : AdelicGLn.AdelicGL K n → ℂ) g'
      (1 * (isExpLieAlgebra K n).expG (u • X'))) = fun u => f (t + u) := by
    funext u
    simp only [archSlice_apply, one_mul, hf, hg', mul_assoc, ← map_mul,
      ← (isExpLieAlgebra K n).expG_add_smul]
  rw [h2] at h1
  have h1' : HasDerivAt (fun u => f (t + u))
      (((gkModuleCusp K n).ρ X φ : AdelicGLn.AdelicGL K n → ℂ) g') (t - t) := by
    rw [sub_self]; exact h1
  have h3 := h1'.comp_sub_const t t
  have e : (fun x => f (t + (x - t))) = f := by
    funext x
    simp only [add_sub_cancel]
  rw [e] at h3
  exact h3

def expPath (X : (isExpLieAlgebra K n).lieSubalgebra) (t : ℝ) : AdelicGLn.AdelicGL K n :=
  infEmb K n ((isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie X))

/- English proof (translation)
Simplify using `[expPath]`.
-/
theorem expPath_zero (X : (isExpLieAlgebra K n).lieSubalgebra) : expPath X 0 = 1 := by
  simp [expPath]

/- English proof (translation)
Use `Reduction.isFiniteMeasure_quotientMeasure (K := K) (n := n) μ` as an intermediate fact. Establish `hXφ` using `ρ_mem_centralCuspForms X hφ`. Establish `hXψ` using `ρ_mem_centralCuspForms X hψ`. Take `⟨C₁, hC₁⟩` from `exists_norm_le_of_mem_centralCuspForms hφ`. Take `⟨C₂, hC₂⟩` from `exists_norm_le_of_mem_centralCuspForms hψ`.

Take `⟨C₃, hC₃⟩` from `exists_norm_le_of_mem_centralCuspForms hXφ`. Take `⟨C₄, hC₄⟩` from `exists_norm_le_of_mem_centralCuspForms hXψ`. Establish `hb : ∀ (χ : cuspForms K n) (C : ℝ), (∀ x, ‖(χ : AdelicGLn.AdelicGL K n → ℂ) x‖ ≤ C) → ∀ g q, ‖quotTr χ g q‖ ≤ C`. Introduce `χ C hC g q`. Take `⟨y, rfl⟩` from `mk_surjective Γ₁ q`.

Rewrite using `[quotTr_mk]`. Conclude with `hC _`. Establish `hbm : ∀ (χ χ' : cuspForms K n) (C C' : ℝ), (∀ x, ‖(χ : AdelicGLn.AdelicGL K n → ℂ) x‖ ≤ C) → (∀ x, ‖(χ' : AdelicGLn.AdelicGL K n → ℂ) x‖ ≤ C') → ∀ g q, ‖starRingEnd ℂ (quotTr χ g q) * quotTr χ' g q‖ ≤ C * C'`. Introduce `χ χ' C C' hC hC' g q`. Rewrite using `[norm_mul, RCLike.norm_conj]`.

Conclude with `mul_le_mul (hb χ C hC g q) (hb χ' C' hC' g q) (norm_nonneg _) ((norm_nonneg _).trans (hb χ C hC g q))`. Establish `hcm : ∀ (χ χ' : cuspForms K n) g, Continuous fun q => starRingEnd ℂ (quotTr χ g q) * quotTr χ' g q` using `fun χ χ' g => (continuous_star.comp (continuous_quotTr χ g)).mul (continuous_quotTr χ' g)`. Establish `key` using `hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := quotientMeasure Γ₁ μ) (F := fun t q => starRingEnd ℂ (quotTr φ (expPath X t) q) * quotTr ψ (expPath X t) q) (F' := fun t q => starRingEnd ℂ (quotTr ((gkModuleCusp K n).ρ X φ) (expPath X t) q) * quotTr ψ (expPath X t) q + star …`. Take `⟨y, rfl⟩` from `mk_surjective Γ₁ q`. Simplify using `only [quotTr_mk, expPath]`.

Establish `d1` using `(hasDerivAt_apply_mul_expG φ X (y : AdelicGLn.AdelicGL K n) t).star`. Establish `d2` using `hasDerivAt_apply_mul_expG ψ X (y : AdelicGLn.AdelicGL K n) t`. Simplify using `only [← starRingEnd_apply] at d1`. Conclude with `d1.mul d2)`. Establish `hconst : (fun t => ∫ q, starRingEnd ℂ (quotTr φ (expPath X t) q) * quotTr ψ (expPath X t) q ∂(quotientMeasure Γ₁ μ)) = fun _ => ∫ q, starRingEnd ℂ (quotTr φ 1 q) * quotTr ψ 1 q ∂(quotientMeasure Γ₁ μ)`.

Use function extensionality and compare the values at `t`. Rewrite using `[quotTr_eq_comp hφ, quotTr_eq_comp hψ]`. Conclude with `(measurePreserving_rightMul μ (toOne (expPath X t))).integral_comp (rightMulHomeomorph Γ₁ (toOne (expPath X t))).measurableEmbedding (fun q => starRingEnd ℂ (quotTr φ 1 q) * quotTr ψ 1 q)`. Rewrite `key` using `[hconst]`. Establish `h0` using `key.2.unique (hasDerivAt_const (0 : ℝ) _)`.

Simplify `h0` using `only [expPath_zero]`.
-/
theorem integral_ρ_add_eq_zero (X : (isExpLieAlgebra K n).lieSubalgebra) {φ ψ : cuspForms K n}
    (hφ : φ ∈ centralCuspForms K n) (hψ : ψ ∈ centralCuspForms K n) :
    ∫ q, (starRingEnd ℂ (quotTr ((gkModuleCusp K n).ρ X φ) 1 q) * quotTr ψ 1 q +
      starRingEnd ℂ (quotTr φ 1 q) * quotTr ((gkModuleCusp K n).ρ X ψ) 1 q) ∂(quotientMeasure Γ₁ μ) = 0 := by
  have := Reduction.isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  have hXφ := ρ_mem_centralCuspForms X hφ
  have hXψ := ρ_mem_centralCuspForms X hψ
  obtain ⟨C₁, hC₁⟩ := exists_norm_le_of_mem_centralCuspForms hφ
  obtain ⟨C₂, hC₂⟩ := exists_norm_le_of_mem_centralCuspForms hψ
  obtain ⟨C₃, hC₃⟩ := exists_norm_le_of_mem_centralCuspForms hXφ
  obtain ⟨C₄, hC₄⟩ := exists_norm_le_of_mem_centralCuspForms hXψ
  have hb : ∀ (χ : cuspForms K n) (C : ℝ), (∀ x, ‖(χ : AdelicGLn.AdelicGL K n → ℂ) x‖ ≤ C) →
      ∀ g q, ‖quotTr χ g q‖ ≤ C := by
    intro χ C hC g q
    obtain ⟨y, rfl⟩ := mk_surjective Γ₁ q
    rw [quotTr_mk]
    exact hC _
  have hbm : ∀ (χ χ' : cuspForms K n) (C C' : ℝ), (∀ x, ‖(χ : AdelicGLn.AdelicGL K n → ℂ) x‖ ≤ C) →
      (∀ x, ‖(χ' : AdelicGLn.AdelicGL K n → ℂ) x‖ ≤ C') →
      ∀ g q, ‖starRingEnd ℂ (quotTr χ g q) * quotTr χ' g q‖ ≤ C * C' := by
    intro χ χ' C C' hC hC' g q
    rw [norm_mul, RCLike.norm_conj]
    exact mul_le_mul (hb χ C hC g q) (hb χ' C' hC' g q) (norm_nonneg _)
      ((norm_nonneg _).trans (hb χ C hC g q))
  have hcm : ∀ (χ χ' : cuspForms K n) g,
      Continuous fun q => starRingEnd ℂ (quotTr χ g q) * quotTr χ' g q := fun χ χ' g =>
    (continuous_star.comp (continuous_quotTr χ g)).mul (continuous_quotTr χ' g)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := quotientMeasure Γ₁ μ)
    (F := fun t q => starRingEnd ℂ (quotTr φ (expPath X t) q) * quotTr ψ (expPath X t) q)
    (F' := fun t q => starRingEnd ℂ (quotTr ((gkModuleCusp K n).ρ X φ) (expPath X t) q) *
        quotTr ψ (expPath X t) q +
      starRingEnd ℂ (quotTr φ (expPath X t) q) * quotTr ((gkModuleCusp K n).ρ X ψ) (expPath X t) q)
    (x₀ := (0 : ℝ)) (bound := fun _ => C₃ * C₂ + C₁ * C₄) Filter.univ_mem
    (Eventually.of_forall fun t => (hcm φ ψ _).aestronglyMeasurable)
    (Integrable.of_bound (hcm φ ψ _).aestronglyMeasurable (C₁ * C₂)
      (Eventually.of_forall (hbm φ ψ C₁ C₂ hC₁ hC₂ _)))
    ((hcm _ _ _).add (hcm _ _ _)).aestronglyMeasurable
    (Eventually.of_forall fun q t _ => (norm_add_le _ _).trans
      (add_le_add (hbm _ _ _ _ hC₃ hC₂ _ q) (hbm _ _ _ _ hC₁ hC₄ _ q)))
    (integrable_const _) (Eventually.of_forall fun q t _ => by
      obtain ⟨y, rfl⟩ := mk_surjective Γ₁ q
      simp only [quotTr_mk, expPath]
      have d1 := (hasDerivAt_apply_mul_expG φ X (y : AdelicGLn.AdelicGL K n) t).star
      have d2 := hasDerivAt_apply_mul_expG ψ X (y : AdelicGLn.AdelicGL K n) t
      simp only [← starRingEnd_apply] at d1
      exact d1.mul d2)

  have hconst : (fun t => ∫ q, starRingEnd ℂ (quotTr φ (expPath X t) q) * quotTr ψ (expPath X t) q
      ∂(quotientMeasure Γ₁ μ)) = fun _ => ∫ q, starRingEnd ℂ (quotTr φ 1 q) * quotTr ψ 1 q
      ∂(quotientMeasure Γ₁ μ) := by
    funext t
    rw [quotTr_eq_comp hφ, quotTr_eq_comp hψ]
    exact (measurePreserving_rightMul μ (toOne (expPath X t))).integral_comp
      (rightMulHomeomorph Γ₁ (toOne (expPath X t))).measurableEmbedding
      (fun q => starRingEnd ℂ (quotTr φ 1 q) * quotTr ψ 1 q)
  rw [hconst] at key
  have h0 := key.2.unique (hasDerivAt_const (0 : ℝ) _)
  simpa only [expPath_zero] using h0

/- English proof (translation)
Use `Reduction.isFiniteMeasure_quotientMeasure (K := K) (n := n) μ` as an intermediate fact. Establish `hI : ∀ χ χ' : cuspForms K n, Integrable (fun q => starRingEnd ℂ (cuspQuot χ.2.1.isLeftInvariant q) * cuspQuot χ'.2.1.isLeftInvariant q) (quotientMeasure Γ₁ μ)`. Introduce `χ χ'`. Take `⟨C, hC⟩` from `exists_norm_le_of_mem_cuspForms χ.2`. Take `⟨C', hC'⟩` from `exists_norm_le_of_mem_cuspForms χ'.2`.

Use `Integrable.of_bound (((continuous_star.comp (continuous_cuspQuot _ χ.2.1.continuous)).mul (continuous_cuspQuot _ χ'.2.1.continuous)).aestronglyMeasurable) (C * C') (Eventually.of_forall fun q => ?_)` and prove the remaining obligations. Take `⟨y, rfl⟩` from `mk_surjective Γ₁ q`. Rewrite using `[norm_mul, RCLike.norm_conj, cuspQuot_mk, cuspQuot_mk]`. Conclude with `mul_le_mul (hC y y.2) (hC' y y.2) (norm_nonneg _) ((norm_nonneg _).trans (hC y y.2))`. Establish `e1` using `petersson_inner_eq_integral_quotient μ ((gkModuleCusp K n).ρ X φ) ψ`.

Establish `e2` using `petersson_inner_eq_integral_quotient μ φ ((gkModuleCusp K n).ρ X ψ)`. Use `(congrArg₂ (· + ·) e1 e2).trans ?_` and prove the remaining obligations. Rewrite using `[← integral_add (hI _ _) (hI _ _)]`. Establish `h` using `integral_ρ_add_eq_zero μ X hφ hψ`. Simplify using `only [quotTr_one] at h`.

Conclude with `h`.
-/
theorem petersson_inner_lieAlgebra_skewAdjoint (X : (isExpLieAlgebra K n).lieSubalgebra) {φ ψ : cuspForms K n}
    (hφ : φ ∈ centralCuspForms K n) (hψ : ψ ∈ centralCuspForms K n) :
    inner ℂ (cuspToL2 μ ((gkModuleCusp K n).ρ X φ)) (cuspToL2 μ ψ) +
      inner ℂ (cuspToL2 μ φ) (cuspToL2 μ ((gkModuleCusp K n).ρ X ψ)) = 0 := by
  have := Reduction.isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  have hI : ∀ χ χ' : cuspForms K n, Integrable (fun q => starRingEnd ℂ (cuspQuot χ.2.1.isLeftInvariant q) *
      cuspQuot χ'.2.1.isLeftInvariant q) (quotientMeasure Γ₁ μ) := by
    intro χ χ'
    obtain ⟨C, hC⟩ := exists_norm_le_of_mem_cuspForms χ.2
    obtain ⟨C', hC'⟩ := exists_norm_le_of_mem_cuspForms χ'.2
    refine Integrable.of_bound (((continuous_star.comp (continuous_cuspQuot _ χ.2.1.continuous)).mul
      (continuous_cuspQuot _ χ'.2.1.continuous)).aestronglyMeasurable) (C * C')
      (Eventually.of_forall fun q => ?_)
    obtain ⟨y, rfl⟩ := mk_surjective Γ₁ q
    rw [norm_mul, RCLike.norm_conj, cuspQuot_mk, cuspQuot_mk]
    exact mul_le_mul (hC y y.2) (hC' y y.2) (norm_nonneg _) ((norm_nonneg _).trans (hC y y.2))
  have e1 := petersson_inner_eq_integral_quotient μ ((gkModuleCusp K n).ρ X φ) ψ
  have e2 := petersson_inner_eq_integral_quotient μ φ ((gkModuleCusp K n).ρ X ψ)
  refine (congrArg₂ (· + ·) e1 e2).trans ?_
  rw [← integral_add (hI _ _) (hI _ _)]
  have h := integral_ρ_add_eq_zero μ X hφ hψ
  simp only [quotTr_one] at h
  exact h

end AutomorphicForm

end GroundTheory.Automorphic
