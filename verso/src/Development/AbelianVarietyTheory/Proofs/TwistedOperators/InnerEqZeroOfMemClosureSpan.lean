import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HilbertTensorTraceClassHasTraceProdStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasFiniteRankTraceOfOfRangeLeFiniteDimensional
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

noncomputable section
open scoped InnerProductSpace

namespace GlobalTheory.TensorTrace

section Hilbert

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/- English proof (translation)
Establish `hle : (Submodule.span ℂ S).topologicalClosure ≤ (ℂ ∙ a)ᗮ`. Use `Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`. Introduce `y hy`. Conclude with `Submodule.mem_orthogonal_singleton_iff_inner_left.2 (h y hy)`.

Conclude with `Submodule.mem_orthogonal_singleton_iff_inner_left.1 (hle hx)`.
-/
theorem inner_eq_zero_of_mem_closure_span {S : Set H} {a : H} (h : ∀ x ∈ S, ⟪x, a⟫_ℂ = 0)
    {x : H} (hx : x ∈ (Submodule.span ℂ S).topologicalClosure) : ⟪x, a⟫_ℂ = 0 := by
  have hle : (Submodule.span ℂ S).topologicalClosure ≤ (ℂ ∙ a)ᗮ := by
    refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
    rw [Submodule.span_le]
    intro y hy
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.2 (h y hy)
  exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 (hle hx)

variable {W : Type} [AddCommGroup W] [Module ℂ W]

/- English proof (translation)
Set `LZ` to `L ∘ₗ Z.subtype`. Establish `hLZ : Function.Injective LZ` using `hL.comp Subtype.val_injective`. Set `e` to `LinearEquiv.ofInjective LZ hLZ`. Use `haveI : FiniteDimensional ℂ (LinearMap.range LZ) := LinearEquiv.finiteDimensional e`. Set `b` to `stdOrthonormalBasis ℂ (LinearMap.range LZ)`.

Establish `he : ∀ x : Z, ((e x : LinearMap.range LZ) : H) = L x` using `fun x => rfl`. Establish `hb : ∀ j, L ((e.symm (b j) : Z) : W) = (b j : H)` using `fun j => by`. Rewrite using `[← he, e.apply_symm_apply]`. Use `⟨_, fun j => ((e.symm (b j) : Z) : W), fun j => (e.symm (b j)).2, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[orthonormal_iff_ite]`.

Introduce `j k`. Simplify using `only [hb]`. Rewrite using `[← Submodule.coe_inner]`. Conclude with `orthonormal_iff_ite.1 b.orthonormal j k`. Introduce `x hx`.

Establish `h1` using `congrArg (fun v : LinearMap.range LZ => (v : H)) (b.sum_repr' (e ⟨x, hx⟩))`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, he] at h1`. Simplify using `only [hb]`. Use `conv_lhs => rw [← h1]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Submodule.coe_inner, he]`. Introduce `f hf`. Rewrite using `[← LinearMap.trace_conj' _ e, LinearMap.trace_eq_sum_inner _ b]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Submodule.coe_inner, hb, LinearEquiv.conj_apply]`.

Both sides reduce to the same expression.
-/
theorem exists_orthonormal (L : W →ₗ[ℂ] H) (hL : Function.Injective L) (Z : Submodule ℂ W)
    [FiniteDimensional ℂ Z] :
    ∃ (n : ℕ) (z : Fin n → W), (∀ j, z j ∈ Z) ∧ Orthonormal ℂ (fun j => L (z j)) ∧
      (∀ x ∈ Z, L x = ∑ j, ⟪L (z j), L x⟫_ℂ • L (z j)) ∧
      (∀ (f : W →ₗ[ℂ] W) (hf : ∀ x ∈ Z, f x ∈ Z),
        LinearMap.trace ℂ Z (f.restrict hf) = ∑ j, ⟪L (z j), L (f (z j))⟫_ℂ) := by
  let LZ := L ∘ₗ Z.subtype
  have hLZ : Function.Injective LZ := hL.comp Subtype.val_injective
  let e := LinearEquiv.ofInjective LZ hLZ
  haveI : FiniteDimensional ℂ (LinearMap.range LZ) := LinearEquiv.finiteDimensional e
  let b := stdOrthonormalBasis ℂ (LinearMap.range LZ)
  have he : ∀ x : Z, ((e x : LinearMap.range LZ) : H) = L x := fun x => rfl
  have hb : ∀ j, L ((e.symm (b j) : Z) : W) = (b j : H) := fun j => by
    rw [← he, e.apply_symm_apply]
  refine ⟨_, fun j => ((e.symm (b j) : Z) : W), fun j => (e.symm (b j)).2, ?_, ?_, ?_⟩
  · rw [orthonormal_iff_ite]
    intro j k
    simp only [hb]
    rw [← Submodule.coe_inner]
    exact orthonormal_iff_ite.1 b.orthonormal j k
  · intro x hx
    have h1 := congrArg (fun v : LinearMap.range LZ => (v : H)) (b.sum_repr' (e ⟨x, hx⟩))
    simp only [Submodule.coe_sum, Submodule.coe_smul, he] at h1
    simp only [hb]
    conv_lhs => rw [← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_inner, he]
  · intro f hf
    rw [← LinearMap.trace_conj' _ e, LinearMap.trace_eq_sum_inner _ b]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_inner, hb, LinearEquiv.conj_apply]
    rfl

end Hilbert

section Tensor

variable {ι : Type} [Fintype ι] {Hs : ι → Type} [∀ i, NormedAddCommGroup (Hs i)]
  [∀ i, InnerProductSpace ℂ (Hs i)] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def evalAt (T : W →ₗ[ℂ] ContinuousMultilinearMap ℂ Hs H) (u : ∀ i, Hs i) : W →ₗ[ℂ] H where
  toFun w := T w u
  map_add' a b := by simp
  map_smul' c a := by simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evalAt_apply (T : W →ₗ[ℂ] ContinuousMultilinearMap ℂ Hs H) (u : ∀ i, Hs i) (w : W) :
    evalAt T u w = T w u := rfl

variable {T : W →ₗ[ℂ] ContinuousMultilinearMap ℂ Hs H} {β : W → W → ℂ}

/- English proof (translation)
Rewrite using `[evalAt_apply, evalAt_apply, hβ]`. Simplify using `only [hu, Finset.prod_const_one, mul_one]`.
-/
theorem beta_eq (hβ : ∀ w w' y y', ⟪T w' y', T w y⟫_ℂ = β w w' * ∏ i, ⟪y' i, y i⟫_ℂ)
    {u : ∀ i, Hs i} (hu : ∀ i, ⟪u i, u i⟫_ℂ = 1) (w w' : W) :
    β w w' = ⟪evalAt T u w', evalAt T u w⟫_ℂ := by
  rw [evalAt_apply, evalAt_apply, hβ]
  simp only [hu, Finset.prod_const_one, mul_one]

/- English proof (translation)
Use `(injective_iff_map_eq_zero _).2 fun w hw => hT ?_` and prove the remaining obligations. Rewrite using `[map_zero]`. Use extensionality with `y`. Establish `h1 : β w w = 0` using `by rw [beta_eq hβ hu, hw, inner_zero_left]`. Establish `h2 : ⟪T w y, T w y⟫_ℂ = 0` using `by rw [hβ, h1, zero_mul]`.

Simplify using `using inner_self_eq_zero.1 h2`.
-/
theorem evalAt_injective (hβ : ∀ w w' y y', ⟪T w' y', T w y⟫_ℂ = β w w' * ∏ i, ⟪y' i, y i⟫_ℂ)
    {u : ∀ i, Hs i} (hu : ∀ i, ⟪u i, u i⟫_ℂ = 1) (hT : Function.Injective T) :
    Function.Injective (evalAt T u) := by
  refine (injective_iff_map_eq_zero _).2 fun w hw => hT ?_
  rw [map_zero]
  ext y
  have h1 : β w w = 0 := by rw [beta_eq hβ hu, hw, inner_zero_left]
  have h2 : ⟪T w y, T w y⟫_ℂ = 0 := by rw [hβ, h1, zero_mul]
  simpa using inner_self_eq_zero.1 h2

variable [CompleteSpace H]

/- English proof (translation)
Use `Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun x hx => ?_` and prove the remaining obligations. Conclude with `Submodule.smul_mem _ _ (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨y, rfl⟩))`. Rewrite using `[inner_eq_zero_symm]`. Use `inner_eq_zero_of_mem_closure_span ?_ hx` and prove the remaining obligations. Introduce and unpack `_ ⟨y', rfl⟩`.

Rewrite using `[inner_sub_right, inner_smul_right, hβ, hβ, hz, one_mul, sub_self]`.
-/
theorem starProjection_tensor
    (hβ : ∀ w w' y y', ⟪T w' y', T w y⟫_ℂ = β w w' * ∏ i, ⟪y' i, y i⟫_ℂ)
    {z : W} (hz : β z z = 1) (w : W) (y : ∀ i, Hs i) :
    (Submodule.span ℂ {x | ∃ y', x = T z y'}).topologicalClosure.starProjection (T w y) = β w z • T z y := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun x hx => ?_
  · exact Submodule.smul_mem _ _ (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨y, rfl⟩))
  · rw [inner_eq_zero_symm]
    refine inner_eq_zero_of_mem_closure_span ?_ hx
    rintro _ ⟨y', rfl⟩
    rw [inner_sub_right, inner_smul_right, hβ, hβ, hz, one_mul, sub_self]

/- English proof (translation)
Use `Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.zero_mem _) fun x hx => ?_` and prove the remaining obligations. Rewrite using `[sub_zero, inner_eq_zero_symm]`. Conclude with `inner_eq_zero_of_mem_closure_span (by rintro _ ⟨y, rfl⟩; exact hv y) hx`.
-/
theorem starProjection_eq_zero_tensor {z : W} {v : H} (hv : ∀ y, ⟪T z y, v⟫_ℂ = 0) :
    (Submodule.span ℂ {x | ∃ y', x = T z y'}).topologicalClosure.starProjection v = 0 := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.zero_mem _) fun x hx => ?_
  rw [sub_zero, inner_eq_zero_symm]
  exact inner_eq_zero_of_mem_closure_span (by rintro _ ⟨y, rfl⟩; exact hv y) hx

end Tensor

/- English proof (translation)
Introduce `ι _ _ Hs _ _ _ H _ _ _ W _ _ T β hβ hT hdense A c hA Z _ hAZ hA0 B b hB X hX`. Distinguish the cases in `hnt : ∀ i, Nontrivial (Hs i)`. Choose the witnesses or unpack the hypotheses as in `⟨u, hu⟩ : ∃ u : ∀ i, Hs i, ∀ i, ⟪u i, u i⟫_ℂ = 1 := by`. Establish `hv : ∀ i, ∃ v : Hs i, v ≠ 0` using `fun i => @exists_ne _ (hnt i) 0`. Use `choose v hv using hv`.

Use `⟨fun i => ((‖v i‖ : ℂ)⁻¹) • v i, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[inner_self_eq_norm_sq_to_K, norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 (hv i))]`. Simplify using the standard rewrite rules. Take `⟨n, z, hzZ, hon, hdec, htr⟩` from `exists_orthonormal (evalAt T u) (evalAt_injective hβ hu hT) Z`. Establish `hzz : ∀ j, β (z j) (z j) = 1` using `fun j => by`.

Use `orthonormal_iff_ite.1 hon j j` as an intermediate fact. Simplify using `only [if_pos rfl] at this`. Rewrite using `[beta_eq hβ hu]`. Conclude with `this`. Establish `hAw : ∀ w, A w = ∑ j, β w (z j) • A (z j)`.

Introduce `w`. Establish `hperp : ∀ k, ⟪evalAt T u (z k), evalAt T u (w - ∑ j, β w (z j) • z j)⟫_ℂ = 0`. Introduce `k`. Establish `h1` using `hon.inner_right_fintype (fun j => β w (z j)) k`. Rewrite using `[map_sub, map_sum, inner_sub_right]`.

Simplify using `only [map_smul]`. Rewrite using `[h1, beta_eq hβ hu, sub_self]`. Establish `h0 : A (w - ∑ j, β w (z j) • z j) = 0`. Use `hA0 _ fun x hx => ?_` and prove the remaining obligations. Rewrite using `[beta_eq hβ hu, hdec x hx, sum_inner]`.

Conclude with `Finset.sum_eq_zero fun k _ => by rw [inner_smul_left, hperp k, mul_zero]`. Rewrite `h0` using `[map_sub, map_sum, sub_eq_zero]`. Simplify `h0` using `only [map_smul]`. Set `P : Fin n → H →L[ℂ] H` to `fun j => (Submodule.span ℂ {x | ∃ y', x = T (z j) y'}).topologicalClosure.starProjection`. Establish `hXsum : X = ∑ j, X ∘L P j`.

Use `ContinuousLinearMap.ext_on (Submodule.dense_iff_topologicalClosure_eq_top.2 hdense) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨w, y, rfl⟩`. Rewrite using `[ContinuousLinearMap.sum_apply]`. Simplify using `only [ContinuousLinearMap.comp_apply, P, starProjection_tensor hβ (hzz _), map_smul, hX]`. Rewrite using `[hAw w, map_sum, ContinuousMultilinearMap.sum_apply]`.

Simplify using `only [map_smul, ContinuousMultilinearMap.smul_apply]`. Establish `hj : ∀ j, GlobalTheory.OpTrace.HasTrace (X ∘L P j) (β (A (z j)) (z j) * ∏ i, b i)` using `fun j => GlobalTheory.T.hilbertTensor_traceClass_hasTrace_prod ι Hs H (T (z j)) (T (A (z j))) (β (A (z j)) (z j)) (β (A (z j)) (A (z j))) (fun y y' => by rw [hβ, hzz, one_mul]) (fun y y' => hβ _ _ _ _) (fun y y' => hβ _ _ _ _) B b hB (X ∘L P j) (fun y => by`. Simplify using `only [ContinuousLinearMap.comp_apply, P, starProjection_tensor hβ (hzz j), hzz j, one_smul, hX])`. Use the proof step `(fun v hv => by`. Simplify using `only [ContinuousLinearMap.comp_apply, P, starProjection_eq_zero_tensor hv, map_zero])`.

Establish `hf : ∀ x ∈ Z, A x ∈ Z` using `fun x _ => hAZ (LinearMap.mem_range_self A x)`. Establish `hc : c = ∑ j, β (A (z j)) (z j)`. Establish `h1` using `GlobalTheory.IndefiniteRowSideFullHecke.RangeTrace.hasFinTrace_of_range_le W A Z hAZ`. Rewrite using `[← hA.2, h1.2, htr A hf]`. Simplify using `only [beta_eq hβ hu]`.

Rewrite using `[hXsum]`. Use `⟨GlobalTheory.OpTrace.isTraceClass_sum _ fun j _ => (hj j).1, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.OpTrace.trace_sum _ fun j _ => (hj j).1, hc, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun j _ => (hj j).2`. Use `push_neg at hnt`.

Take `⟨i0, hi0⟩` from `hnt`. Establish `hTz : ∀ w y, T w y = 0` using `fun w y => (T w).map_coord_zero i0 (Subsingleton.elim _ _)`. Establish `hH : ∀ v : H, v = 0`. Introduce `v`. Establish `hv : v ∈ (Submodule.span ℂ {v | ∃ w y, v = T w y}).topologicalClosure`.

Rewrite using `[hdense]`. Conclude with `Submodule.mem_top`. Use `inner_eq_zero_of_mem_closure_span (a := v) (by rintro _ ⟨w, y, rfl⟩; rw [hTz, inner_zero_left]) hv` as an intermediate fact. Conclude with `inner_self_eq_zero.1 this`. Establish `hX0 : X = 0` using `ContinuousLinearMap.ext fun v => hH _`.

Establish `hB0 : B i0 = 0` using `ContinuousLinearMap.ext fun v => Subsingleton.elim _ _`. Establish `hb0 : b i0 = 0` using `by rw [← (hB i0).2, hB0, GlobalTheory.OpTrace.trace_zero]`. Rewrite using `[hX0, Finset.prod_eq_zero (Finset.mem_univ i0) hb0, mul_zero]`. Conclude with `⟨GlobalTheory.OpTrace.isTraceClass_zero, GlobalTheory.OpTrace.trace_zero⟩`.
-/
theorem hasTrace_finiteRank_tensor : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Hs : ι → Type) [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)] [∀ i, CompleteSpace (Hs i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (W : Type) [AddCommGroup W] [Module ℂ W] (T : W →ₗ[ℂ] ContinuousMultilinearMap ℂ Hs H) (β : W → W → ℂ), (∀ w w' y y', inner ℂ (T w' y') (T w y) = β w w' * ∏ i, inner ℂ (y' i) (y i)) → Function.Injective T → (Submodule.span ℂ {v | ∃ w y, v = T w y}).topologicalClosure = ⊤ → ∀ (A : W →ₗ[ℂ] W) (c : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace A c → ∀ Z : Submodule ℂ W, FiniteDimensional ℂ Z → LinearMap.range A ≤ Z → (∀ w, (∀ z ∈ Z, β w z = 0) → A w = 0) → ∀ (B : ∀ i, Hs i →L[ℂ] Hs i) (b : ι → ℂ), (∀ i, HasTrace (B i) (b i)) → ∀ X : H →L[ℂ] H, (∀ w y, X (T w y) = T (A w) fun i => B i (y i)) → HasTrace X (c * ∏ i, b i) := by
  intro ι _ _ Hs _ _ _ H _ _ _ W _ _ T β hβ hT hdense A c hA Z _ hAZ hA0 B b hB X hX
  by_cases hnt : ∀ i, Nontrivial (Hs i)
  · obtain ⟨u, hu⟩ : ∃ u : ∀ i, Hs i, ∀ i, ⟪u i, u i⟫_ℂ = 1 := by
      have hv : ∀ i, ∃ v : Hs i, v ≠ 0 := fun i => @exists_ne _ (hnt i) 0
      choose v hv using hv
      refine ⟨fun i => ((‖v i‖ : ℂ)⁻¹) • v i, fun i => ?_⟩
      rw [inner_self_eq_norm_sq_to_K, norm_smul, norm_inv, Complex.norm_real, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.2 (hv i))]
      simp
    obtain ⟨n, z, hzZ, hon, hdec, htr⟩ :=
      exists_orthonormal (evalAt T u) (evalAt_injective hβ hu hT) Z
    have hzz : ∀ j, β (z j) (z j) = 1 := fun j => by
      have := orthonormal_iff_ite.1 hon j j
      simp only [if_pos rfl] at this
      rw [beta_eq hβ hu]
      exact this
    have hAw : ∀ w, A w = ∑ j, β w (z j) • A (z j) := by
      intro w
      have hperp : ∀ k, ⟪evalAt T u (z k), evalAt T u (w - ∑ j, β w (z j) • z j)⟫_ℂ = 0 := by
        intro k
        have h1 := hon.inner_right_fintype (fun j => β w (z j)) k
        rw [map_sub, map_sum, inner_sub_right]
        simp only [map_smul]
        rw [h1, beta_eq hβ hu, sub_self]
      have h0 : A (w - ∑ j, β w (z j) • z j) = 0 := by
        refine hA0 _ fun x hx => ?_
        rw [beta_eq hβ hu, hdec x hx, sum_inner]
        exact Finset.sum_eq_zero fun k _ => by rw [inner_smul_left, hperp k, mul_zero]
      rw [map_sub, map_sum, sub_eq_zero] at h0
      simpa only [map_smul] using h0
    let P : Fin n → H →L[ℂ] H := fun j =>
      (Submodule.span ℂ {x | ∃ y', x = T (z j) y'}).topologicalClosure.starProjection
    have hXsum : X = ∑ j, X ∘L P j := by
      refine ContinuousLinearMap.ext_on (Submodule.dense_iff_topologicalClosure_eq_top.2 hdense) ?_
      rintro _ ⟨w, y, rfl⟩
      rw [ContinuousLinearMap.sum_apply]
      simp only [ContinuousLinearMap.comp_apply, P, starProjection_tensor hβ (hzz _), map_smul, hX]
      rw [hAw w, map_sum, ContinuousMultilinearMap.sum_apply]
      simp only [map_smul, ContinuousMultilinearMap.smul_apply]
    have hj : ∀ j, GlobalTheory.OpTrace.HasTrace (X ∘L P j) (β (A (z j)) (z j) * ∏ i, b i) := fun j =>
      GlobalTheory.T.hilbertTensor_traceClass_hasTrace_prod ι Hs H (T (z j)) (T (A (z j))) (β (A (z j)) (z j)) (β (A (z j)) (A (z j)))
        (fun y y' => by rw [hβ, hzz, one_mul]) (fun y y' => hβ _ _ _ _) (fun y y' => hβ _ _ _ _) B b hB
        (X ∘L P j)
        (fun y => by
          simp only [ContinuousLinearMap.comp_apply, P, starProjection_tensor hβ (hzz j), hzz j, one_smul, hX])
        (fun v hv => by
          simp only [ContinuousLinearMap.comp_apply, P, starProjection_eq_zero_tensor hv, map_zero])
    have hf : ∀ x ∈ Z, A x ∈ Z := fun x _ => hAZ (LinearMap.mem_range_self A x)
    have hc : c = ∑ j, β (A (z j)) (z j) := by
      have h1 := GlobalTheory.IndefiniteRowSideFullHecke.RangeTrace.hasFinTrace_of_range_le W A Z hAZ
      rw [← hA.2, h1.2, htr A hf]
      simp only [beta_eq hβ hu]
    rw [hXsum]
    refine ⟨GlobalTheory.OpTrace.isTraceClass_sum _ fun j _ => (hj j).1, ?_⟩
    rw [GlobalTheory.OpTrace.trace_sum _ fun j _ => (hj j).1, hc, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => (hj j).2
  · push_neg at hnt
    obtain ⟨i0, hi0⟩ := hnt
    have hTz : ∀ w y, T w y = 0 := fun w y => (T w).map_coord_zero i0 (Subsingleton.elim _ _)
    have hH : ∀ v : H, v = 0 := by
      intro v
      have hv : v ∈ (Submodule.span ℂ {v | ∃ w y, v = T w y}).topologicalClosure := by
        rw [hdense]; exact Submodule.mem_top
      have := inner_eq_zero_of_mem_closure_span (a := v)
        (by rintro _ ⟨w, y, rfl⟩; rw [hTz, inner_zero_left]) hv
      exact inner_self_eq_zero.1 this
    have hX0 : X = 0 := ContinuousLinearMap.ext fun v => hH _
    have hB0 : B i0 = 0 := ContinuousLinearMap.ext fun v => Subsingleton.elim _ _
    have hb0 : b i0 = 0 := by rw [← (hB i0).2, hB0, GlobalTheory.OpTrace.trace_zero]
    rw [hX0, Finset.prod_eq_zero (Finset.mem_univ i0) hb0, mul_zero]
    exact ⟨GlobalTheory.OpTrace.isTraceClass_zero, GlobalTheory.OpTrace.trace_zero⟩

end GlobalTheory.TensorTrace
