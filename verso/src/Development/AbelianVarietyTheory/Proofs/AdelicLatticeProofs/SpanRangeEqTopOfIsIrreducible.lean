import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

open scoped MonoidAlgebra

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
open scoped MonoidAlgebra in
/- English proof (translation)
Establish `schur : ∀ f : V →ₗ[A] V, ∃ c : ℂ, ∀ y, f y = c • y`. Introduce `f`. Take `⟨c, hc⟩` from `(IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := A) (V := V) ℂ).2 f`. Conclude with `⟨c, fun y => by rw [← hc]; rfl⟩`. Set `b` to `Module.finBasis ℂ V`.

Set `ι` to `Fin (Module.finrank ℂ V)`. Set `N : Submodule A (ι → V)` to `Submodule.span A {fun i => b i}`. Take `⟨W, hW⟩` from `exists_isCompl N`. Set `P : (ι → V) →ₗ[A] (ι → V)` to `N.subtype.comp (Submodule.linearProjOfIsCompl N W hW)`. Establish `hPN : ∀ x, P x ∈ N` using `fun x => (Submodule.linearProjOfIsCompl N W hW x).2`.

Establish `hPfix : ∀ x ∈ N, P x = x` using `fun x hx => by`. Simplify using `only [P, LinearMap.comp_apply, Submodule.subtype_apply]`. Conclude with `congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hW ⟨x, hx⟩)`. Establish `hcomm : ∀ (T : Module.End ℂ V) (x : ι → V), P (fun i => T (x i)) = fun i => T (P x i)`. Introduce `T x`.

Establish `hsingle : ∀ (i j : ι) (y : V), P (Pi.single j (T y)) i = T (P (Pi.single j y) i)`. Introduce `i j y`. Take `⟨c, hc⟩` from `schur ((LinearMap.proj i).comp (P.comp (LinearMap.single A (fun _ : ι => V) j)))`. Establish `h1` using `hc (T y)`. Establish `h2` using `hc y`.

Simplify using `only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.single_apply] at h1 h2`. Rewrite using `[h1, h2, map_smul]`. Use function extensionality and compare the values at `i`. Use `conv_lhs => rw [← Finset.univ_sum_single (fun i => T (x i)), map_sum]`. Use `conv_rhs => rw [← Finset.univ_sum_single x, map_sum]`.

Simplify using `only [Finset.sum_apply, map_sum, hsingle]`. Use extensionality with `T`. Simplify using `only [Algebra.mem_top, iff_true]`. Establish `hmem : (fun i => T (b i)) ∈ N`. Establish `hfix : P (fun i => T (b i)) = fun i => T (b i)`.

Rewrite using `[hcomm T (fun i => b i), hPfix _ (Submodule.mem_span_singleton_self _)]`. Rewrite using `[← hfix]`. Conclude with `hPN _`. Take `⟨a, ha⟩` from `Submodule.mem_span_singleton.1 hmem`. Establish `hT : T = (a : Module.End ℂ V)`.

Use `b.ext fun i => ?_` and prove the remaining obligations. Use `congrFun ha i` as an intermediate fact. Conclude with `this.symm`. Rewrite using `[hT]`. Conclude with `a.2`.
-/
private theorem subalgebra_end_eq_whole_of_isSimpleModule {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (A : Subalgebra ℂ (Module.End ℂ V)) [IsSimpleModule A V] :
    A = ⊤ := by
  classical
  have schur : ∀ f : V →ₗ[A] V, ∃ c : ℂ, ∀ y, f y = c • y := by
    intro f
    obtain ⟨c, hc⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := A) (V := V) ℂ).2 f
    exact ⟨c, fun y => by rw [← hc]; rfl⟩
  let b := Module.finBasis ℂ V
  let ι := Fin (Module.finrank ℂ V)
  let N : Submodule A (ι → V) := Submodule.span A {fun i => b i}
  obtain ⟨W, hW⟩ := exists_isCompl N
  let P : (ι → V) →ₗ[A] (ι → V) := N.subtype.comp (Submodule.linearProjOfIsCompl N W hW)
  have hPN : ∀ x, P x ∈ N := fun x => (Submodule.linearProjOfIsCompl N W hW x).2
  have hPfix : ∀ x ∈ N, P x = x := fun x hx => by
    simp only [P, LinearMap.comp_apply, Submodule.subtype_apply]
    exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hW ⟨x, hx⟩)
  have hcomm : ∀ (T : Module.End ℂ V) (x : ι → V), P (fun i => T (x i)) = fun i => T (P x i) := by
    intro T x
    have hsingle : ∀ (i j : ι) (y : V), P (Pi.single j (T y)) i = T (P (Pi.single j y) i) := by
      intro i j y
      obtain ⟨c, hc⟩ := schur ((LinearMap.proj i).comp (P.comp (LinearMap.single A (fun _ : ι => V) j)))
      have h1 := hc (T y)
      have h2 := hc y
      simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.single_apply] at h1 h2
      rw [h1, h2, map_smul]
    funext i
    conv_lhs => rw [← Finset.univ_sum_single (fun i => T (x i)), map_sum]
    conv_rhs => rw [← Finset.univ_sum_single x, map_sum]
    simp only [Finset.sum_apply, map_sum, hsingle]
  ext T
  simp only [Algebra.mem_top, iff_true]
  have hmem : (fun i => T (b i)) ∈ N := by
    have hfix : P (fun i => T (b i)) = fun i => T (b i) := by
      rw [hcomm T (fun i => b i), hPfix _ (Submodule.mem_span_singleton_self _)]
    rw [← hfix]
    exact hPN _
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
  have hT : T = (a : Module.End ℂ V) := by
    refine b.ext fun i => ?_
    have := congrFun ha i
    exact this.symm
  rw [hT]
  exact a.2

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
open scoped MonoidAlgebra in

/- English proof (translation)
Introduce `G _ V _ _ ρ _ h`. Set `A : Subalgebra ℂ (Module.End ℂ V)` to `Algebra.adjoin ℂ (Set.range ρ)`. Establish `hρA : ∀ g, ρ g ∈ A` using `fun g => Algebra.subset_adjoin ⟨g, rfl⟩`. Establish `hspan : Subalgebra.toSubmodule A = Submodule.span ℂ (Set.range ρ)`. Rewrite using `[Algebra.adjoin_eq_span]`.

Use `congr 1`. Establish `: Set.range ρ = ((MonoidHom.mrange ρ : Submonoid (Module.End ℂ V)) : Set (Module.End ℂ V))` using `(MonoidHom.coe_mrange ρ).symm`. Rewrite using `[this, Submonoid.closure_eq]`. Set `φ : Submodule A V → Subrepresentation ρ` to `fun M => ⟨M.restrictScalars ℂ, fun g v hv => M.smul_mem (⟨ρ g, hρA g⟩ : A) hv⟩`. Use `haveI : IsSimpleModule A V := by`.

Use `{ exists_pair_ne := ⟨⊥, ⊤, fun hbt => ?_⟩, eq_bot_or_eq_top := fun M => ?_ }` and prove the remaining obligations. Take `⟨S, S', hS'⟩` from `h.exists_pair_ne`. Establish `hzero : ∀ x : V, x = 0` using `fun x => by`. Establish `: x ∈ (⊤ : Submodule A V)` using `Submodule.mem_top`. Rewrite `this` using `[← hbt]`.

Conclude with `(Submodule.mem_bot A).1 this`. Establish `hall : ∀ T U : Subrepresentation ρ, T = U` using `fun T U => by`. Apply `Subrepresentation.ext` to reduce the goal to its premises. Use extensionality with `x`. Rewrite using `[hzero x]`.

Conclude with `⟨fun _ => U.toSubmodule.zero_mem, fun _ => T.toSubmodule.zero_mem⟩`. Conclude with `hS' (hall S S')`. Break down `h.eq_bot_or_eq_top (φ M) with hM | hM` into its components or cases. Use `left`. Use `congrArg Subrepresentation.toSubmodule hM` as an intermediate fact.

Conclude with `(Submodule.restrictScalars_eq_bot_iff ℂ A V).1 this`. Use `right`. Use `congrArg Subrepresentation.toSubmodule hM` as an intermediate fact. Conclude with `(Submodule.restrictScalars_eq_top_iff ℂ A V).1 this`. Rewrite using `[← hspan, subalgebra_end_eq_whole_of_isSimpleModule A]`.

Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
theorem _root_.GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible :
    ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) [FiniteDimensional ℂ V], ρ.IsIrreducible → Submodule.span ℂ (Set.range ρ) = ⊤ := by
  intro G _ V _ _ ρ _ h
  let A : Subalgebra ℂ (Module.End ℂ V) := Algebra.adjoin ℂ (Set.range ρ)
  have hρA : ∀ g, ρ g ∈ A := fun g => Algebra.subset_adjoin ⟨g, rfl⟩
  have hspan : Subalgebra.toSubmodule A = Submodule.span ℂ (Set.range ρ) := by
    rw [Algebra.adjoin_eq_span]
    congr 1
    have : Set.range ρ = ((MonoidHom.mrange ρ : Submonoid (Module.End ℂ V)) : Set (Module.End ℂ V)) :=
      (MonoidHom.coe_mrange ρ).symm
    rw [this, Submonoid.closure_eq]
  let φ : Submodule A V → Subrepresentation ρ := fun M =>
    ⟨M.restrictScalars ℂ, fun g v hv => M.smul_mem (⟨ρ g, hρA g⟩ : A) hv⟩
  haveI : IsSimpleModule A V := by
    refine { exists_pair_ne := ⟨⊥, ⊤, fun hbt => ?_⟩, eq_bot_or_eq_top := fun M => ?_ }
    · obtain ⟨S, S', hS'⟩ := h.exists_pair_ne
      have hzero : ∀ x : V, x = 0 := fun x => by
        have : x ∈ (⊤ : Submodule A V) := Submodule.mem_top
        rw [← hbt] at this
        exact (Submodule.mem_bot A).1 this
      have hall : ∀ T U : Subrepresentation ρ, T = U := fun T U => by
        apply Subrepresentation.ext
        ext x
        rw [hzero x]
        exact ⟨fun _ => U.toSubmodule.zero_mem, fun _ => T.toSubmodule.zero_mem⟩
      exact hS' (hall S S')
    · rcases h.eq_bot_or_eq_top (φ M) with hM | hM
      · left
        have := congrArg Subrepresentation.toSubmodule hM
        exact (Submodule.restrictScalars_eq_bot_iff ℂ A V).1 this
      · right
        have := congrArg Subrepresentation.toSubmodule hM
        exact (Submodule.restrictScalars_eq_top_iff ℂ A V).1 this
  rw [← hspan, subalgebra_end_eq_whole_of_isSimpleModule A]
  ext x
  simp

end GlobalTheory.ClassFin
