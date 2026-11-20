import Mathlib

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

section Spec

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

/- English proof (translation)
Use `haveI := hFd`. Establish `hS : (T.restrict hF).IsSymmetric` using `LinearMap.IsSymmetric.restrict_invariant (show T.IsSymmetric from hT) hF`. Take `⟨n, hn⟩ : ∃ n, Module.finrank ℂ F = n` from `⟨_, rfl⟩`. Use `⟨n, fun i => ((inner ℂ (hS.eigenvectorBasis hn i) (⟨y, hy⟩ : F) • hS.eigenvectorBasis hn i : F) : X), fun i => hS.eigenvalues hn i, ?_, ?_⟩` and prove the remaining obligations. Establish `h2` using `congrArg (fun z : F => (z : X)) ((hS.eigenvectorBasis hn).sum_repr' (⟨y, hy⟩ : F))`.

Simplify using `only [Submodule.coe_sum] at h2`. Conclude with `h2.symm`. Introduce `i`. Use `⟨Submodule.coe_mem _, ?_⟩` and prove the remaining obligations. Establish `hev : T ((hS.eigenvectorBasis hn i : F) : X) = (hS.eigenvalues hn i : ℂ) • ((hS.eigenvectorBasis hn i : F) : X)`.

Establish `h3` using `congrArg (fun z : F => (z : X)) (hS.apply_eigenvectorBasis hn i)`. Simplify using `only [LinearMap.restrict_coe_apply, Submodule.coe_smul] at h3`. Conclude with `h3`. Use `beta_reduce`. Rewrite using `[Submodule.coe_smul, map_smul, hev, smul_comm]`.
-/
theorem coefA_decomp {T : X →ₗ[ℂ] X} (hT : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y))
    {F : Submodule ℂ X} (hFd : FiniteDimensional ℂ F) (hF : ∀ x ∈ F, T x ∈ F) {y : X} (hy : y ∈ F) :
    ∃ m : ℕ, ∃ b : Fin m → X, ∃ θ : Fin m → ℝ, y = ∑ i, b i ∧
      ∀ i, b i ∈ F ∧ T (b i) = (θ i : ℂ) • b i := by
  haveI := hFd
  have hS : (T.restrict hF).IsSymmetric :=
    LinearMap.IsSymmetric.restrict_invariant (show T.IsSymmetric from hT) hF
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank ℂ F = n := ⟨_, rfl⟩
  refine ⟨n, fun i => ((inner ℂ (hS.eigenvectorBasis hn i) (⟨y, hy⟩ : F) •
      hS.eigenvectorBasis hn i : F) : X), fun i => hS.eigenvalues hn i, ?_, ?_⟩
  · have h2 := congrArg (fun z : F => (z : X)) ((hS.eigenvectorBasis hn).sum_repr' (⟨y, hy⟩ : F))
    simp only [Submodule.coe_sum] at h2
    exact h2.symm
  · intro i
    refine ⟨Submodule.coe_mem _, ?_⟩
    have hev : T ((hS.eigenvectorBasis hn i : F) : X) =
        (hS.eigenvalues hn i : ℂ) • ((hS.eigenvectorBasis hn i : F) : X) := by
      have h3 := congrArg (fun z : F => (z : X)) (hS.apply_eigenvectorBasis hn i)
      simp only [LinearMap.restrict_coe_apply, Submodule.coe_smul] at h3
      exact h3
    beta_reduce
    rw [Submodule.coe_smul, map_smul, hev, smul_comm]

/- English proof (translation)
Establish `h` using `hT u v`. Rewrite `h` using `[hu, hv, inner_smul_left, inner_smul_right, Complex.conj_ofReal]`. Establish `hne' : (α : ℂ) - β ≠ 0` using `sub_ne_zero.mpr (by exact_mod_cast hne)`. Establish `h0 : ((α : ℂ) - β) * inner ℂ u v = 0` using `by rw [sub_mul, h, sub_self]`. Conclude with `(mul_eq_zero.mp h0).resolve_left hne'`.
-/
theorem coefA_inner_eq_zero {T : X →ₗ[ℂ] X} (hT : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y))
    {u v : X} {α β : ℝ} (hu : T u = (α : ℂ) • u) (hv : T v = (β : ℂ) • v) (hne : α ≠ β) :
    inner ℂ u v = 0 := by
  have h := hT u v
  rw [hu, hv, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h
  have hne' : (α : ℂ) - β ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
  have h0 : ((α : ℂ) - β) * inner ℂ u v = 0 := by rw [sub_mul, h, sub_self]
  exact (mul_eq_zero.mp h0).resolve_left hne'

end Spec

section Rep

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]

def CoefLocFin (T : X →ₗ[ℂ] X) (M' : Submodule ℂ X) : Prop :=
  ∀ y ∈ M', ∃ F : Submodule ℂ X, FiniteDimensional ℂ F ∧ F ≤ M' ∧ (∀ x ∈ F, T x ∈ F) ∧ y ∈ F

/- English proof (translation)
Take `⟨F, hFd, hFM, hF, hyF⟩` from `hloc y hy`. Take `⟨m, b, θ, hsum, hb⟩` from `coefA_decomp hT hFd hF hyF`. Conclude with `⟨m, b, θ, hsum, fun i => ⟨hFM (hb i).1, (hb i).2⟩⟩`.
-/
theorem coefA_decompM {T : X →ₗ[ℂ] X} (hT : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y))
    {M' : Submodule ℂ X} (hloc : CoefLocFin T M') {y : X} (hy : y ∈ M') :
    ∃ m : ℕ, ∃ b : Fin m → X, ∃ θ : Fin m → ℝ, y = ∑ i, b i ∧
      ∀ i, b i ∈ M' ∧ T (b i) = (θ i : ℂ) • b i := by
  obtain ⟨F, hFd, hFM, hF, hyF⟩ := hloc y hy
  obtain ⟨m, b, θ, hsum, hb⟩ := coefA_decomp hT hFd hF hyF
  exact ⟨m, b, θ, hsum, fun i => ⟨hFM (hb i).1, (hb i).2⟩⟩

/- English proof (translation)
Use `haveI : CompleteSpace L := FiniteDimensional.complete ℂ L`. Use `⟨(((InnerProductSpace.toDual ℂ L).symm (LinearMap.toContinuousLinearMap (ψ.comp L.subtype)) : L) : Z), Submodule.coe_mem _, fun w hw => ?_⟩` and prove the remaining obligations. Establish `h` using `InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (E := L) (x := ⟨w, hw⟩) (y := LinearMap.toContinuousLinearMap (ψ.comp L.subtype))`. Rewrite `h` using `[Submodule.coe_inner]`. Simplify using `using h`.
-/
private theorem exists_mem_inner_eq_functional_of_finiteDim {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (L : Submodule ℂ Z) [FiniteDimensional ℂ L] (ψ : Z →ₗ[ℂ] ℂ) :
    ∃ f ∈ L, ∀ w ∈ L, inner ℂ f w = ψ w := by
  haveI : CompleteSpace L := FiniteDimensional.complete ℂ L
  refine ⟨(((InnerProductSpace.toDual ℂ L).symm
      (LinearMap.toContinuousLinearMap (ψ.comp L.subtype)) : L) : Z), Submodule.coe_mem _,
      fun w hw => ?_⟩
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (E := L) (x := ⟨w, hw⟩)
    (y := LinearMap.toContinuousLinearMap (ψ.comp L.subtype))
  rw [Submodule.coe_inner] at h
  simpa using h

/- English proof (translation)
Introduce `w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨α, hα, hx'⟩` from `hs x hx`. Conclude with `coefA_inner_eq_zero hT hx' hv (ne_of_lt (lt_of_le_of_lt hα hβ))`.

Consider the case `zero => exact inner_zero_left _`. Consider the case `add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]`. Consider the case `smul a x _ hx => rw [inner_smul_left, hx, mul_zero]`.
-/
private theorem inner_span_eq_zero_of_eigenvalue_gt {T : X →ₗ[ℂ] X} (hT : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y))
    {s : Set X} {C : ℝ} (hs : ∀ u ∈ s, ∃ α : ℝ, α ≤ C ∧ T u = (α : ℂ) • u) {v : X} {β : ℝ}
    (hv : T v = (β : ℂ) • v) (hβ : C < β) : ∀ w ∈ Submodule.span ℂ s, inner ℂ w v = 0 := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, hα, hx'⟩ := hs x hx
    exact coefA_inner_eq_zero hT hx' hv (ne_of_lt (lt_of_le_of_lt hα hβ))
  | zero => exact inner_zero_left _
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]

/- English proof (translation)
Establish `hLZ : Submodule.span ℂ {y | y ∈ M' ∧ ∃ θ : ℝ, θ ≤ C ∧ T y = (θ : ℂ) • y} ≤ Z₀` using `Submodule.span_le.mpr (fun y ⟨hyM, θ, hθ, hTy⟩ => hlow y hyM θ hθ hTy)`. Use `haveI := hZ₀`. Use `haveI : FiniteDimensional ℂ (Submodule.span ℂ {y | y ∈ M' ∧ ∃ θ : ℝ, θ ≤ C ∧ T y = (θ : ℂ) • y}) := Submodule.finiteDimensional_of_le hLZ`. Take `⟨z, hzL, hz⟩` from `exists_mem_inner_eq_functional_of_finiteDim (Submodule.span ℂ {y | y ∈ M' ∧ ∃ θ : ℝ, θ ≤ C ∧ T y = (θ : ℂ) • y}) ℓ`. Use `⟨z, hZM (hLZ hzL), fun y hy => ?_⟩` and prove the remaining obligations.

Take `⟨m, b, θ, hsum, hb⟩` from `coefA_decompM hT hloc hy`. Rewrite using `[hsum, inner_sum, map_sum]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Distinguish the cases in `hθ : θ i ≤ C`. Conclude with `hz (b i) (Submodule.subset_span ⟨(hb i).1, θ i, hθ, (hb i).2⟩)`.

Use `push_neg at hθ`. Rewrite using `[hhigh (b i) (hb i).1 (θ i) hθ (hb i).2]`. Conclude with `inner_span_eq_zero_of_eigenvalue_gt hT (fun u hu => hu.2) (hb i).2 hθ z hzL`.
-/
theorem coefA_toSum {T : X →ₗ[ℂ] X} (hT : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y))
    {M' : Submodule ℂ X} (hloc : CoefLocFin T M') (ℓ : X →ₗ[ℂ] ℂ) (C : ℝ)
    {Z₀ : Submodule ℂ X} (hZ₀ : FiniteDimensional ℂ Z₀) (hZM : Z₀ ≤ M')
    (hlow : ∀ y ∈ M', ∀ θ : ℝ, θ ≤ C → T y = (θ : ℂ) • y → y ∈ Z₀)
    (hhigh : ∀ y ∈ M', ∀ θ : ℝ, C < θ → T y = (θ : ℂ) • y → ℓ y = 0) :
    ∃ z ∈ M', ∀ y ∈ M', inner ℂ z y = ℓ y := by
  classical
  have hLZ : Submodule.span ℂ {y | y ∈ M' ∧ ∃ θ : ℝ, θ ≤ C ∧ T y = (θ : ℂ) • y} ≤ Z₀ :=
    Submodule.span_le.mpr (fun y ⟨hyM, θ, hθ, hTy⟩ => hlow y hyM θ hθ hTy)
  haveI := hZ₀
  haveI : FiniteDimensional ℂ
      (Submodule.span ℂ {y | y ∈ M' ∧ ∃ θ : ℝ, θ ≤ C ∧ T y = (θ : ℂ) • y}) :=
    Submodule.finiteDimensional_of_le hLZ
  obtain ⟨z, hzL, hz⟩ := exists_mem_inner_eq_functional_of_finiteDim
    (Submodule.span ℂ {y | y ∈ M' ∧ ∃ θ : ℝ, θ ≤ C ∧ T y = (θ : ℂ) • y}) ℓ
  refine ⟨z, hZM (hLZ hzL), fun y hy => ?_⟩
  obtain ⟨m, b, θ, hsum, hb⟩ := coefA_decompM hT hloc hy
  rw [hsum, inner_sum, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hθ : θ i ≤ C
  · exact hz (b i) (Submodule.subset_span ⟨(hb i).1, θ i, hθ, (hb i).2⟩)
  · push_neg at hθ
    rw [hhigh (b i) (hb i).1 (θ i) hθ (hb i).2]
    exact inner_span_eq_zero_of_eigenvalue_gt hT (fun u hu => hu.2) (hb i).2 hθ z hzL

/- English proof (translation)
Use `haveI := hLd`. Establish `hS : (T.restrict hL).IsSymmetric` using `LinearMap.IsSymmetric.restrict_invariant (show T.IsSymmetric from hT) hL`. Take `⟨n, hn⟩ : ∃ n, Module.finrank ℂ L = n` from `⟨_, rfl⟩`. Establish `hev : ∀ i, T ((hS.eigenvectorBasis hn i : L) : Y) = (hS.eigenvalues hn i : ℂ) • ((hS.eigenvectorBasis hn i : L) : Y)`. Introduce `i`.

Establish `h3` using `congrArg (fun z : L => (z : Y)) (hS.apply_eigenvectorBasis hn i)`. Simplify using `only [LinearMap.restrict_coe_apply, Submodule.coe_smul] at h3`. Conclude with `h3`. Use `⟨∑ i, |hS.eigenvalues hn i|, ?_⟩` and prove the remaining obligations. Introduce `F hF u θ hθ hu`.

Establish `hle : ∀ i, hS.eigenvalues hn i ≤ ∑ j, |hS.eigenvalues hn j|` using `fun i => (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |hS.eigenvalues hn j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))`. Establish `horth : ∀ i, inner ℂ ((hS.eigenvectorBasis hn i : L) : Y) u = 0` using `fun i => coefA_inner_eq_zero hT (hev i) hu (ne_of_lt (lt_of_le_of_lt (hle i) hθ))`. Establish `hsum` using `congrArg (fun z : L => (z : Y)) ((hS.eigenvectorBasis hn).sum_repr' (⟨F, hF⟩ : L))`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at hsum`. Rewrite using `[← hsum, sum_inner]`.

Use `Finset.sum_eq_zero (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[inner_smul_left, horth i, mul_zero]`.
-/
theorem coefA_high {T : Y →ₗ[ℂ] Y} (hT : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y))
    {L : Submodule ℂ Y} (hLd : FiniteDimensional ℂ L) (hL : ∀ x ∈ L, T x ∈ L) :
    ∃ C : ℝ, ∀ F ∈ L, ∀ u : Y, ∀ θ : ℝ, C < θ → T u = (θ : ℂ) • u → inner ℂ F u = 0 := by
  haveI := hLd
  have hS : (T.restrict hL).IsSymmetric :=
    LinearMap.IsSymmetric.restrict_invariant (show T.IsSymmetric from hT) hL
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank ℂ L = n := ⟨_, rfl⟩
  have hev : ∀ i, T ((hS.eigenvectorBasis hn i : L) : Y) =
      (hS.eigenvalues hn i : ℂ) • ((hS.eigenvectorBasis hn i : L) : Y) := by
    intro i
    have h3 := congrArg (fun z : L => (z : Y)) (hS.apply_eigenvectorBasis hn i)
    simp only [LinearMap.restrict_coe_apply, Submodule.coe_smul] at h3
    exact h3
  refine ⟨∑ i, |hS.eigenvalues hn i|, ?_⟩
  intro F hF u θ hθ hu
  have hle : ∀ i, hS.eigenvalues hn i ≤ ∑ j, |hS.eigenvalues hn j| := fun i =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |hS.eigenvalues hn j|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i))
  have horth : ∀ i, inner ℂ ((hS.eigenvectorBasis hn i : L) : Y) u = 0 := fun i =>
    coefA_inner_eq_zero hT (hev i) hu (ne_of_lt (lt_of_le_of_lt (hle i) hθ))
  have hsum := congrArg (fun z : L => (z : Y)) ((hS.eigenvectorBasis hn).sum_repr' (⟨F, hF⟩ : L))
  simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
  rw [← hsum, sum_inner]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [inner_smul_left, horth i, mul_zero]

/- English proof (translation)
Establish `hker : LinearMap.ker (ι.comp E.subtype) = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce `w hw`. Conclude with `Subtype.ext (hinj w w.2 hw)`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective (ι.comp E.subtype) hker`.

Take `⟨f, hfR, hf⟩` from `exists_mem_inner_eq_functional_of_finiteDim (LinearMap.range (ι.comp E.subtype)) ((φ.comp E.subtype).comp g)`. Take `⟨x, rfl⟩` from `LinearMap.mem_range.mp hfR`. Use `⟨x, x.2, fun y hy => ?_⟩` and prove the remaining obligations. Establish `h1` using `hf (ι y) ⟨⟨y, hy⟩, rfl⟩`. Establish `hgy : g (ι y) = ⟨y, hy⟩`.

Establish `h2` using `LinearMap.congr_fun hg ⟨y, hy⟩`. Simplify using `using h2`. Simplify using `only [LinearMap.comp_apply, Submodule.subtype_apply] at h1`. Rewrite using `[h1, hgy]`.
-/
private theorem exists_inner_comp_eq_functional_of_injOn {E : Submodule ℂ X} [FiniteDimensional ℂ E] (ι : X →ₗ[ℂ] Y)
    (hinj : ∀ y ∈ E, ι y = 0 → y = 0) (φ : X →ₗ[ℂ] ℂ) :
    ∃ x ∈ E, ∀ y ∈ E, inner ℂ (ι x) (ι y) = φ y := by
  have hker : LinearMap.ker (ι.comp E.subtype) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    exact Subtype.ext (hinj w w.2 hw)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (ι.comp E.subtype) hker
  obtain ⟨f, hfR, hf⟩ := exists_mem_inner_eq_functional_of_finiteDim (LinearMap.range (ι.comp E.subtype))
    ((φ.comp E.subtype).comp g)
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hfR
  refine ⟨x, x.2, fun y hy => ?_⟩
  have h1 := hf (ι y) ⟨⟨y, hy⟩, rfl⟩
  have hgy : g (ι y) = ⟨y, hy⟩ := by
    have h2 := LinearMap.congr_fun hg ⟨y, hy⟩
    simpa using h2
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1
  rw [h1, hgy]

/- English proof (translation)
Introduce `z hz`. Take `⟨m, b, θ, hzs, hb⟩` from `coefA_decompM hT hloc hz`. Establish `hx : ∀ k : Fin m, ∃ x : X, x ∈ M' ∧ T x = (θ k : ℂ) • x ∧ ∀ y ∈ M', T y = (θ k : ℂ) • y → inner ℂ (ι x) (ι y) = inner ℂ (b k) y`. Introduce `k`. Take `⟨Z, hZd, hZ⟩` from `hfin (θ k)`.

Establish `hmemE : ∀ y, y ∈ M' ⊓ LinearMap.ker (T - (θ k : ℂ) • LinearMap.id) ↔ y ∈ M' ∧ T y = (θ k : ℂ) • y`. Introduce `y`. Simplify using `[Submodule.mem_inf, LinearMap.mem_ker, sub_eq_zero]`. Establish `hEZ : M' ⊓ LinearMap.ker (T - (θ k : ℂ) • LinearMap.id) ≤ Z` using `fun y hy => hZ y ((hmemE y).mp hy).1 ((hmemE y).mp hy).2`. Use `haveI := hZd`.

Use `haveI : FiniteDimensional ℂ ↥(M' ⊓ LinearMap.ker (T - (θ k : ℂ) • LinearMap.id)) := Submodule.finiteDimensional_of_le hEZ`. Take `⟨x, hxE, hxr⟩` from `exists_inner_comp_eq_functional_of_injOn ι (fun y hy => hinj y ((hmemE y).mp hy).1) (innerₛₗ ℂ (b k))`. Use `⟨x, ((hmemE x).mp hxE).1, ((hmemE x).mp hxE).2, fun y hy hTy => ?_⟩` and prove the remaining obligations. Rewrite using `[hxr y ((hmemE y).mpr ⟨hy, hTy⟩)]`. Use `first`.

Consider the case `rfl`. Consider the case `simp`. Use `choose x hxM hxT hxr using hx`. Use `⟨ι (∑ k, x k), Submodule.mem_map_of_mem (Submodule.sum_mem _ (fun k _ => hxM k)), ?_⟩` and prove the remaining obligations. Introduce `y hy`.

Take `⟨n, c, η, hys, hc⟩` from `coefA_decompM hT hloc hy`. Rewrite using `[map_sum, hzs, hys, sum_inner, sum_inner]`. Use `Finset.sum_congr rfl (fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[map_sum, inner_sum, inner_sum]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations.

Distinguish the cases in `hkj : θ k = η j`. Conclude with `hxr k (c j) (hc j).1 (by rw [hkj]; exact (hc j).2)`. Establish `h1 : inner ℂ (b k) (c j) = 0` using `coefA_inner_eq_zero hT (hb k).2 (hc j).2 hkj`. Establish `hTYx : TY (ι (x k)) = (θ k : ℂ) • ι (x k)`. Rewrite using `[← hιT _ (hxM k), hxT k, map_smul]`.

Establish `hTYc : TY (ι (c j)) = (η j : ℂ) • ι (c j)`. Rewrite using `[← hιT _ (hc j).1, (hc j).2, map_smul]`. Rewrite using `[h1, coefA_inner_eq_zero hTY hTYx hTYc hkj]`.
-/
theorem coefA_ofSum {T : X →ₗ[ℂ] X} (hT : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y))
    {TY : Y →ₗ[ℂ] Y} (hTY : ∀ x y, inner ℂ (TY x) y = inner ℂ x (TY y))
    {M' : Submodule ℂ X} (hloc : CoefLocFin T M') (ι : X →ₗ[ℂ] Y)
    (hιT : ∀ y ∈ M', ι (T y) = TY (ι y)) (hinj : ∀ y ∈ M', ι y = 0 → y = 0)
    (hfin : ∀ θ : ℝ, ∃ Z : Submodule ℂ X, FiniteDimensional ℂ Z ∧
      ∀ y ∈ M', T y = (θ : ℂ) • y → y ∈ Z) :
    ∀ z ∈ M', ∃ f ∈ M'.map ι, ∀ y ∈ M', inner ℂ f (ι y) = inner ℂ z y := by
  classical
  intro z hz
  obtain ⟨m, b, θ, hzs, hb⟩ := coefA_decompM hT hloc hz
  have hx : ∀ k : Fin m, ∃ x : X, x ∈ M' ∧ T x = (θ k : ℂ) • x ∧
      ∀ y ∈ M', T y = (θ k : ℂ) • y → inner ℂ (ι x) (ι y) = inner ℂ (b k) y := by
    intro k
    obtain ⟨Z, hZd, hZ⟩ := hfin (θ k)
    have hmemE : ∀ y, y ∈ M' ⊓ LinearMap.ker (T - (θ k : ℂ) • LinearMap.id) ↔
        y ∈ M' ∧ T y = (θ k : ℂ) • y := by
      intro y
      simp [Submodule.mem_inf, LinearMap.mem_ker, sub_eq_zero]
    have hEZ : M' ⊓ LinearMap.ker (T - (θ k : ℂ) • LinearMap.id) ≤ Z := fun y hy =>
      hZ y ((hmemE y).mp hy).1 ((hmemE y).mp hy).2
    haveI := hZd
    haveI : FiniteDimensional ℂ ↥(M' ⊓ LinearMap.ker (T - (θ k : ℂ) • LinearMap.id)) :=
      Submodule.finiteDimensional_of_le hEZ
    obtain ⟨x, hxE, hxr⟩ := exists_inner_comp_eq_functional_of_injOn ι (fun y hy => hinj y ((hmemE y).mp hy).1)
      (innerₛₗ ℂ (b k))
    refine ⟨x, ((hmemE x).mp hxE).1, ((hmemE x).mp hxE).2, fun y hy hTy => ?_⟩
    rw [hxr y ((hmemE y).mpr ⟨hy, hTy⟩)]
    first
      | rfl
      | simp
  choose x hxM hxT hxr using hx
  refine ⟨ι (∑ k, x k), Submodule.mem_map_of_mem (Submodule.sum_mem _ (fun k _ => hxM k)), ?_⟩
  intro y hy
  obtain ⟨n, c, η, hys, hc⟩ := coefA_decompM hT hloc hy
  rw [map_sum, hzs, hys, sum_inner, sum_inner]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_sum, inner_sum, inner_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hkj : θ k = η j
  · exact hxr k (c j) (hc j).1 (by rw [hkj]; exact (hc j).2)
  · have h1 : inner ℂ (b k) (c j) = 0 := coefA_inner_eq_zero hT (hb k).2 (hc j).2 hkj
    have hTYx : TY (ι (x k)) = (θ k : ℂ) • ι (x k) := by
      rw [← hιT _ (hxM k), hxT k, map_smul]
    have hTYc : TY (ι (c j)) = (η j : ℂ) • ι (c j) := by
      rw [← hιT _ (hc j).1, (hc j).2, map_smul]
    rw [h1, coefA_inner_eq_zero hTY hTYx hTYc hkj]

end Rep

end ReciprocityTheory.ChartRestriction.DS
