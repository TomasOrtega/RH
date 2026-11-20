import Mathlib
open NumberField IsDedekindDomain Matrix
open scoped BigOperators

namespace GlobalTheory

/- English proof (translation)
Use `haveI : Module.Finite (𝓞 E) (𝓞 M) := inferInstance`. Use `haveI : Module.Flat (𝓞 E) (𝓞 M) := inferInstance`. Use `haveI : Module.FinitePresentation (𝓞 E) (𝓞 M) := Module.finitePresentation_of_finite _ _`. Use `haveI : Module.Projective (𝓞 E) (𝓞 M) := Module.Flat.projective_of_finitePresentation`. Take `⟨k, π, hπ⟩` from `Module.Finite.exists_fin' (𝓞 E) (𝓞 M)`.

Take `⟨σ, hσ⟩` from `Module.projective_lifting_property π LinearMap.id hπ`. Use `haveI hL : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 M) (nonZeroDivisors (𝓞 E))) M := IsIntegralClosure.isLocalization (𝓞 E) E M (𝓞 M)`. Use `haveI hL' : IsLocalizedModule (nonZeroDivisors (𝓞 E)) (IsScalarTower.toAlgHom (𝓞 E) (𝓞 M) M).toLinearMap := isLocalizedModule_iff_isLocalization.mpr hL`. Establish `hu : ∀ x : nonZeroDivisors (𝓞 E), IsUnit (algebraMap (𝓞 E) (Module.End (𝓞 E) E) x)` using `fun x => IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 E)) (Algebra.linearMap (𝓞 E) E) x`. Set `l0 : Fin k → M →ₗ[𝓞 E] E` to `fun j => IsLocalizedModule.lift (nonZeroDivisors (𝓞 E)) (IsScalarTower.toAlgHom (𝓞 E) (𝓞 M) M).toLinearMap (Algebra.linearMap (𝓞 E) E ∘ₗ LinearMap.proj j ∘ₗ σ) hu`.

Set `l : Fin k → M →ₗ[E] E` to `fun j => (l0 j).extendScalarsOfIsLocalization (nonZeroDivisors (𝓞 E)) E`. Establish `hl : ∀ j (c : 𝓞 M), l j (c : M) = ((σ c j : 𝓞 E) : E)`. Introduce `j c`. Conclude with `IsLocalizedModule.lift_apply (nonZeroDivisors (𝓞 E)) (IsScalarTower.toAlgHom (𝓞 E) (𝓞 M) M).toLinearMap (Algebra.linearMap (𝓞 E) E ∘ₗ LinearMap.proj j ∘ₗ σ) hu c`. Use `⟨k, fun j => π (Pi.single j 1), l, fun j c => ⟨_, hl j c⟩, ?_⟩` and prove the remaining obligations.

Establish `hc : ∀ c : 𝓞 M, (c : M) = ∑ j, ((π (Pi.single j 1) : 𝓞 M) : M) * algebraMap E M (l j c)`. Introduce `c`. Establish `h1 : c = ∑ j, σ c j • π (Pi.single j 1)`. Establish `h2 : π (σ c) = c` using `LinearMap.congr_fun hσ c`. Use `conv_lhs => rw [← h2, LinearMap.pi_apply_eq_sum_univ π (σ c)]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `congr 2`. Use extensionality with `i`. Simplify using `[Pi.single_apply, eq_comm]`. Establish `h3` using `congrArg (algebraMap (𝓞 M) M) h1`.

Rewrite `h3` using `[map_sum]`. Use `h3.trans (Finset.sum_congr rfl fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[hl, Algebra.smul_def, map_mul, mul_comm, ← IsScalarTower.algebraMap_apply]`. Both sides reduce to the same expression. Introduce `y`.

Take `⟨⟨c, a⟩, ha⟩` from `IsLocalizedModule.surj (nonZeroDivisors (𝓞 E)) (IsScalarTower.toAlgHom (𝓞 E) (𝓞 M) M).toLinearMap y`. Establish `ha' : ((a : 𝓞 E) : E) • y = (c : M)`. Establish `: (a : 𝓞 E) • y = (c : M)` using `ha`. Rewrite using `[← this]`. Conclude with `algebraMap_smul E (a : 𝓞 E) y`.

Establish `hne : ((a : 𝓞 E) : E) ≠ 0`. Use `nonZeroDivisors.ne_zero a.2` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `h4` using `hc c`. Rewrite `h4` using `[← ha']`.

Apply `smul_right_injective M hne` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[h4, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul, map_mul, Algebra.smul_def]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_integral_dual_family (E M : Type) [Field E] [NumberField E] [Field M]
    [NumberField M] [Algebra E M] :
    ∃ (k : ℕ) (b : Fin k → 𝓞 M) (l : Fin k → M →ₗ[E] E),
      (∀ j (c : 𝓞 M), ∃ a : 𝓞 E, l j (c : M) = (a : E)) ∧
      ∀ y : M, y = ∑ j, (b j : M) * algebraMap E M (l j y) := by
  haveI : Module.Finite (𝓞 E) (𝓞 M) := inferInstance
  haveI : Module.Flat (𝓞 E) (𝓞 M) := inferInstance
  haveI : Module.FinitePresentation (𝓞 E) (𝓞 M) := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 E) (𝓞 M) := Module.Flat.projective_of_finitePresentation
  obtain ⟨k, π, hπ⟩ := Module.Finite.exists_fin' (𝓞 E) (𝓞 M)
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π LinearMap.id hπ
  haveI hL : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 M) (nonZeroDivisors (𝓞 E))) M :=
    IsIntegralClosure.isLocalization (𝓞 E) E M (𝓞 M)
  haveI hL' : IsLocalizedModule (nonZeroDivisors (𝓞 E))
      (IsScalarTower.toAlgHom (𝓞 E) (𝓞 M) M).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr hL
  have hu : ∀ x : nonZeroDivisors (𝓞 E), IsUnit (algebraMap (𝓞 E) (Module.End (𝓞 E) E) x) :=
    fun x => IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 E)) (Algebra.linearMap (𝓞 E) E) x
  let l0 : Fin k → M →ₗ[𝓞 E] E := fun j =>
    IsLocalizedModule.lift (nonZeroDivisors (𝓞 E))
      (IsScalarTower.toAlgHom (𝓞 E) (𝓞 M) M).toLinearMap
      (Algebra.linearMap (𝓞 E) E ∘ₗ LinearMap.proj j ∘ₗ σ) hu
  let l : Fin k → M →ₗ[E] E := fun j =>
    (l0 j).extendScalarsOfIsLocalization (nonZeroDivisors (𝓞 E)) E
  have hl : ∀ j (c : 𝓞 M), l j (c : M) = ((σ c j : 𝓞 E) : E) := by
    intro j c
    exact IsLocalizedModule.lift_apply (nonZeroDivisors (𝓞 E))
      (IsScalarTower.toAlgHom (𝓞 E) (𝓞 M) M).toLinearMap
      (Algebra.linearMap (𝓞 E) E ∘ₗ LinearMap.proj j ∘ₗ σ) hu c
  refine ⟨k, fun j => π (Pi.single j 1), l, fun j c => ⟨_, hl j c⟩, ?_⟩
  have hc : ∀ c : 𝓞 M, (c : M) = ∑ j, ((π (Pi.single j 1) : 𝓞 M) : M) * algebraMap E M (l j c) := by
    intro c
    have h1 : c = ∑ j, σ c j • π (Pi.single j 1) := by
      have h2 : π (σ c) = c := LinearMap.congr_fun hσ c
      conv_lhs => rw [← h2, LinearMap.pi_apply_eq_sum_univ π (σ c)]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 2
      ext i
      simp [Pi.single_apply, eq_comm]
    have h3 := congrArg (algebraMap (𝓞 M) M) h1
    rw [map_sum] at h3
    refine h3.trans (Finset.sum_congr rfl fun j _ => ?_)
    rw [hl, Algebra.smul_def, map_mul, mul_comm, ← IsScalarTower.algebraMap_apply]
    rfl
  intro y
  obtain ⟨⟨c, a⟩, ha⟩ := IsLocalizedModule.surj (nonZeroDivisors (𝓞 E))
      (IsScalarTower.toAlgHom (𝓞 E) (𝓞 M) M).toLinearMap y
  have ha' : ((a : 𝓞 E) : E) • y = (c : M) := by
    have : (a : 𝓞 E) • y = (c : M) := ha
    rw [← this]
    exact algebraMap_smul E (a : 𝓞 E) y
  have hne : ((a : 𝓞 E) : E) ≠ 0 := by
    have := nonZeroDivisors.ne_zero a.2
    exact_mod_cast this
  have h4 := hc c
  rw [← ha'] at h4
  apply smul_right_injective M hne
  dsimp only
  rw [h4, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, map_mul, Algebra.smul_def]
  ring

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Take `⟨k, b, l, hl, hy⟩` from `exists_integral_dual_family E M`. Establish `key : ∀ j, ∀ w ∈ Submodule.span (𝓞 M) ((fun (v : ι → E) (i : ι) => algebraMap E M (v i)) '' S), ∀ c : 𝓞 M, (fun i => l j ((c : M) * w i)) ∈ Submodule.span (𝓞 E) S`. Introduce `j w hw`. Proceed by induction on `hw using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨v, hv, rfl⟩` from `hx`. Introduce `c`. Take `⟨a, ha⟩` from `hl j c`. Establish `: (fun i => l j ((c : M) * algebraMap E M (v i))) = a • v`.

Use extensionality with `i`. Rewrite using `[mul_comm, ← Algebra.smul_def, map_smul, ha, smul_eq_mul, mul_comm]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hv)`.

Consider the case `zero`. Introduce `c`. Establish `: (fun i => l j ((c : M) * (0 : ι → M) i)) = 0` using `by ext i; simp`. Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add x y _ _ hx hy`. Introduce `c`. Establish `: (fun i => l j ((c : M) * (x + y) i)) = (fun i => l j ((c : M) * x i)) + (fun i => l j ((c : M) * y i))`. Use extensionality with `i`. Simplify using `[mul_add]`.

Rewrite using `[this]`. Conclude with `Submodule.add_mem _ (hx c) (hy c)`. Consider the case `smul a x _ hx`. Introduce `c`. Establish `: (fun i => l j ((c : M) * (a • x) i)) = (fun i => l j (((c * a : 𝓞 M) : M) * x i))`.

Use extensionality with `i`. Use `congr 1`. Rewrite using `[Pi.smul_apply, Algebra.smul_def, ← mul_assoc]`. Simplify using the standard rewrite rules. Rewrite using `[this]`.

Conclude with `hx _`. Introduce `s hs`. Rewrite using `[hy s]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Establish `h1 : ((b j : 𝓞 M) : M) * algebraMap E M (l j s) = b j • algebraMap E M (l j s)` using `rfl`.

Rewrite using `[h1]`. Use `Submodule.smul_mem _ _ (Submodule.subset_span ⟨l j s, ?_, rfl⟩)` and prove the remaining obligations. Establish `h2` using `key j _ hs 1`. Rewrite using `[SetLike.mem_coe, Submodule.mem_comap]`. Use `h2 using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `i`. Distinguish the cases in `h : i = τ`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨s, hs, rfl⟩`. Establish `key : ∀ v ∈ Submodule.span (𝓞 E) S, (fun i => algebraMap E M (v i)) ∈ Submodule.span (𝓞 M) ((fun (v : ι → E) (i : ι) => algebraMap E M (v i)) '' S)`. Introduce `v hv`. Proceed by induction on `hv using Submodule.span_induction with`.

Consider the case `mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩`. Consider the case `zero`. Establish `: (fun i => algebraMap E M ((0 : ι → E) i)) = 0` using `by ext i; simp`. Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add x y _ _ hx hy`. Establish `: (fun i => algebraMap E M ((x + y) i)) = (fun i => algebraMap E M (x i)) + (fun i => algebraMap E M (y i))`. Use extensionality with `i`. Simplify using the standard rewrite rules. Rewrite using `[this]`.

Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx`. Establish `: (fun i => algebraMap E M ((a • x) i)) = algebraMap (𝓞 E) (𝓞 M) a • (fun i => algebraMap E M (x i))`. Use extensionality with `i`. Rewrite using `[Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]`.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hx`. Establish `h2` using `key _ hs`. Rewrite using `[SetLike.mem_coe, Submodule.mem_comap]`. Use `h2 using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `i`. Distinguish the cases in `h : i = τ`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`.
-/
theorem comap_single_span_algebraMap (E M : Type) [Field E] [NumberField E] [Field M]
    [NumberField M] [Algebra E M] (ι : Type) [Fintype ι] [DecidableEq ι] (S : Set (ι → E)) (τ : ι) :
    (Submodule.span (𝓞 M) ((fun (v : ι → E) (i : ι) => algebraMap E M (v i)) '' S)).comap
      (LinearMap.single (𝓞 M) (fun _ : ι => M) τ) =
    Submodule.span (𝓞 M) (algebraMap E M '' ((Submodule.span (𝓞 E) S).comap
      (LinearMap.single (𝓞 E) (fun _ : ι => E) τ) : Set E)) := by
  apply le_antisymm
  · obtain ⟨k, b, l, hl, hy⟩ := exists_integral_dual_family E M
    have key : ∀ j, ∀ w ∈ Submodule.span (𝓞 M)
        ((fun (v : ι → E) (i : ι) => algebraMap E M (v i)) '' S), ∀ c : 𝓞 M,
        (fun i => l j ((c : M) * w i)) ∈ Submodule.span (𝓞 E) S := by
      intro j w hw
      induction hw using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨v, hv, rfl⟩ := hx
        intro c
        obtain ⟨a, ha⟩ := hl j c
        have : (fun i => l j ((c : M) * algebraMap E M (v i))) = a • v := by
          ext i
          rw [mul_comm, ← Algebra.smul_def, map_smul, ha, smul_eq_mul, mul_comm]
          rfl
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span hv)
      | zero =>
        intro c
        have : (fun i => l j ((c : M) * (0 : ι → M) i)) = 0 := by ext i; simp
        rw [this]; exact Submodule.zero_mem _
      | add x y _ _ hx hy =>
        intro c
        have : (fun i => l j ((c : M) * (x + y) i)) =
            (fun i => l j ((c : M) * x i)) + (fun i => l j ((c : M) * y i)) := by
          ext i; simp [mul_add]
        rw [this]; exact Submodule.add_mem _ (hx c) (hy c)
      | smul a x _ hx =>
        intro c
        have : (fun i => l j ((c : M) * (a • x) i)) =
            (fun i => l j (((c * a : 𝓞 M) : M) * x i)) := by
          ext i
          congr 1
          rw [Pi.smul_apply, Algebra.smul_def, ← mul_assoc]
          simp
        rw [this]; exact hx _
    intro s hs
    rw [hy s]
    refine Submodule.sum_mem _ fun j _ => ?_
    have h1 : ((b j : 𝓞 M) : M) * algebraMap E M (l j s) = b j • algebraMap E M (l j s) := rfl
    rw [h1]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨l j s, ?_, rfl⟩)
    have h2 := key j _ hs 1
    rw [SetLike.mem_coe, Submodule.mem_comap]
    convert h2 using 1
    ext i
    by_cases h : i = τ
    · subst h; simp
    · simp [h]
  · rw [Submodule.span_le]
    rintro _ ⟨s, hs, rfl⟩
    have key : ∀ v ∈ Submodule.span (𝓞 E) S, (fun i => algebraMap E M (v i)) ∈
        Submodule.span (𝓞 M) ((fun (v : ι → E) (i : ι) => algebraMap E M (v i)) '' S) := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
      | zero =>
        have : (fun i => algebraMap E M ((0 : ι → E) i)) = 0 := by ext i; simp
        rw [this]; exact Submodule.zero_mem _
      | add x y _ _ hx hy =>
        have : (fun i => algebraMap E M ((x + y) i)) =
            (fun i => algebraMap E M (x i)) + (fun i => algebraMap E M (y i)) := by
          ext i; simp
        rw [this]; exact Submodule.add_mem _ hx hy
      | smul a x _ hx =>
        have : (fun i => algebraMap E M ((a • x) i)) =
            algebraMap (𝓞 E) (𝓞 M) a • (fun i => algebraMap E M (x i)) := by
          ext i
          rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, Algebra.smul_def, map_mul,
            ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
        rw [this]; exact Submodule.smul_mem _ _ hx
    have h2 := key _ hs
    rw [SetLike.mem_coe, Submodule.mem_comap]
    convert h2 using 1
    ext i
    by_cases h : i = τ
    · subst h; simp
    · simp [h]

end GlobalTheory
