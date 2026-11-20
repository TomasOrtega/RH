import Mathlib
open IsLocalRing Matrix

namespace GlobalTheory.BurnsideMonoid

open scoped MonoidAlgebra

/- English proof (translation)
Establish `hscal : ∀ φ : Module.End K[G] τ.asModule, ∃ c : K, ∀ m, φ m = c • m`. Introduce `φ`. Take `⟨c, hc⟩` from `(IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := K[G]) (V := τ.asModule) K).2 φ`. Conclude with `⟨c, fun m => by rw [← hc]; rfl⟩`. Establish `hsurj : Function.Surjective τ.asAlgebraHom`.

Introduce `f`. Set `F : Module.End (Module.End K[G] τ.asModule) τ.asModule` to `{ toFun := fun m => τ.asModuleEquiv.symm (f (τ.asModuleEquiv m)) map_add' := fun x y => by simp map_smul' := fun φ m => by`. Take `⟨c, hc⟩` from `hscal φ`. Simplify using `only [Module.End.smul_def, RingHom.id_apply, hc, map_smul] }`. Set `b` to `Module.finBasis K V`.

Take `⟨r, hr⟩` from `jacobson_density F (Finset.univ.image fun i => τ.asModuleEquiv.symm (b i))`. Use `⟨r, b.ext fun i => ?_⟩` and prove the remaining obligations. Use `congrArg τ.asModuleEquiv (hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))` as an intermediate fact. Conclude with `this.symm`. Use `eq_top_iff.2 fun f _ => ?_` and prove the remaining obligations.

Take `⟨r, rfl⟩` from `hsurj f`. Proceed by induction on `r using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ (hx trivial) (hy trivial)`.

Consider the case `single g c`. Rewrite using `[Representation.asAlgebraHom_single]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)`.
-/
theorem span_range_eq_top_of_isIrreducible {G K V : Type} [Monoid G] [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (τ : Representation K G V)
    (h : τ.IsIrreducible) : Submodule.span K (Set.range τ) = ⊤ := by
  classical
  have hscal : ∀ φ : Module.End K[G] τ.asModule, ∃ c : K, ∀ m, φ m = c • m := by
    intro φ
    obtain ⟨c, hc⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed
      (A := K[G]) (V := τ.asModule) K).2 φ
    exact ⟨c, fun m => by rw [← hc]; rfl⟩
  have hsurj : Function.Surjective τ.asAlgebraHom := by
    intro f
    let F : Module.End (Module.End K[G] τ.asModule) τ.asModule :=
      { toFun := fun m => τ.asModuleEquiv.symm (f (τ.asModuleEquiv m))
        map_add' := fun x y => by simp
        map_smul' := fun φ m => by
          obtain ⟨c, hc⟩ := hscal φ
          simp only [Module.End.smul_def, RingHom.id_apply, hc, map_smul] }
    let b := Module.finBasis K V
    obtain ⟨r, hr⟩ := jacobson_density F
      (Finset.univ.image fun i => τ.asModuleEquiv.symm (b i))
    refine ⟨r, b.ext fun i => ?_⟩
    have := congrArg τ.asModuleEquiv (hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    exact this.symm
  refine eq_top_iff.2 fun f _ => ?_
  obtain ⟨r, rfl⟩ := hsurj f
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ (hx trivial) (hy trivial)
  | single g c =>
    rw [Representation.asAlgebraHom_single]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

/- English proof (translation)
Break down `isEmpty_or_nonempty ι with hι | hι` into its components or cases. Conclude with `eq_top_iff.2 fun x _ => by rw [Subsingleton.elim x 0]; exact Submodule.zero_mem _`. Set `τ : Representation K Γ (ι → K)` to `{ toFun := fun g => Matrix.toLin' (σ g) map_one' := by simp; rfl map_mul' := fun g g' => by simp [Matrix.toLin'_mul]; rfl }`. Establish `hτ : ∀ g v, τ g v = (σ g).mulVec v` using `fun g v => Matrix.toLin'_apply _ _`. Establish `hirr : τ.IsIrreducible`.

Establish `hnt : Nontrivial (Subrepresentation τ)`. Use `⟨⊥, ⊤, fun hbt => ?_⟩` and prove the remaining obligations. Establish `h1 : (⊥ : Submodule K (ι → K)) = ⊤` using `congrArg Subrepresentation.toSubmodule hbt`. Conclude with `bot_ne_top h1`. Use `⟨fun W => ?_⟩` and prove the remaining obligations.

Break down `h W.toSubmodule (fun g v hv => by` into its components or cases. Use `W.apply_mem_toSubmodule g hv` as an intermediate fact. Rewrite using `[hτ] at this) with h1 | h1` and apply the resulting hypothesis. Conclude with `Or.inl (Subrepresentation.toSubmodule_injective h1)`. Conclude with `Or.inr (Subrepresentation.toSubmodule_injective h1)`.

Establish `hs` using `span_range_eq_top_of_isIrreducible τ hirr`. Establish `hm : Set.range σ = (LinearMap.toMatrix' (R` using `K) (m := ι) (n := ι)) '' Set.range τ := by`. Rewrite using `[← Set.range_comp]`. Use `congr 1`. Use function extensionality and compare the values at `g`.

Conclude with `(LinearMap.toMatrix'_toLin' (σ g)).symm`. Rewrite using `[hm]`. Use `Submodule.map_span (LinearMap.toMatrix' (R := K) (m := ι) (n := ι)).toLinearMap (Set.range τ)` as an intermediate fact. Rewrite `this` using `[hs, Submodule.map_top, LinearEquiv.range]`. Conclude with `this.symm`.
-/
theorem span_matrix_eq_top_of_isAlgClosed {K : Type} [Field K] [IsAlgClosed K]
    {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Type} [Monoid Γ] (σ : Γ →* Matrix ι ι K)
    (h : ∀ W : Submodule K (ι → K), (∀ g, ∀ w ∈ W, σ g *ᵥ w ∈ W) → W = ⊥ ∨ W = ⊤) :
    Submodule.span K (Set.range σ) = ⊤ := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact eq_top_iff.2 fun x _ => by rw [Subsingleton.elim x 0]; exact Submodule.zero_mem _
  let τ : Representation K Γ (ι → K) :=
    { toFun := fun g => Matrix.toLin' (σ g)
      map_one' := by simp; rfl
      map_mul' := fun g g' => by simp [Matrix.toLin'_mul]; rfl }
  have hτ : ∀ g v, τ g v = (σ g).mulVec v := fun g v => Matrix.toLin'_apply _ _
  have hirr : τ.IsIrreducible := by
    have hnt : Nontrivial (Subrepresentation τ) := by
      refine ⟨⊥, ⊤, fun hbt => ?_⟩
      have h1 : (⊥ : Submodule K (ι → K)) = ⊤ := congrArg Subrepresentation.toSubmodule hbt
      exact bot_ne_top h1
    refine ⟨fun W => ?_⟩
    rcases h W.toSubmodule (fun g v hv => by
      have := W.apply_mem_toSubmodule g hv
      rwa [hτ] at this) with h1 | h1
    · exact Or.inl (Subrepresentation.toSubmodule_injective h1)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h1)
  have hs := span_range_eq_top_of_isIrreducible τ hirr
  have hm : Set.range σ =
      (LinearMap.toMatrix' (R := K) (m := ι) (n := ι)) '' Set.range τ := by
    rw [← Set.range_comp]
    congr 1
    funext g
    exact (LinearMap.toMatrix'_toLin' (σ g)).symm
  rw [hm]
  have := Submodule.map_span (LinearMap.toMatrix' (R := K) (m := ι) (n := ι)).toLinearMap
    (Set.range τ)
  rw [hs, Submodule.map_top, LinearEquiv.range] at this
  exact this.symm

end GlobalTheory.BurnsideMonoid
