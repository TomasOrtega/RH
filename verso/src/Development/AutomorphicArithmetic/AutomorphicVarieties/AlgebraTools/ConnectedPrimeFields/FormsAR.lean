import Mathlib
import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

/- English proof (translation)
Take `⟨r, s, hs⟩` from `Module.Finite.exists_fin (R := R) (M := M)`. Take `⟨I, indepI, hI⟩` from `exists_maximal_linearIndepOn R s`. Establish `indepI' : LinearIndependent R (fun x : I => s x)` using `indepI`. Set `N` to `Submodule.span R (Set.range fun x : I => s x)`. Set `b : Module.Basis I R N` to `Module.Basis.span indepI'`.

Establish `exists_a : ∀ i, ∃ a : R, a ≠ 0 ∧ a • s i ∈ N`. Introduce `i`. Distinguish the cases in `hi : i ∈ I`. Use `⟨1, one_ne_zero, ?_⟩` and prove the remaining obligations. Rewrite using `[one_smul]`.

Conclude with `Submodule.subset_span (Set.mem_range_self (⟨i, hi⟩ : I))`. Take `⟨a, ha, ha'⟩` from `hI i hi`. Use `⟨a, ha, ?_⟩` and prove the remaining obligations. Rewrite `ha'` using `[Set.image_eq_range s I]`. Then use the resulting hypothesis. Use `choose a ha ha' using exists_a`.

Establish `hA : (∏ i, a i) ≠ 0`. Rewrite using `[Finset.prod_ne_zero_iff]`. Conclude with `fun i _ => ha i`. Set `φ : M →ₗ[R] M` to `LinearMap.lsmul R M (∏ i, a i)`. Establish `hφ : Function.Injective φ` using `LinearMap.ker_eq_bot.mp (LinearMap.ker_lsmul hA)`.

Establish `hle : LinearMap.range φ ≤ N`. It suffices to establish `∀ i, φ (s i) ∈ N by`. Rewrite using `[LinearMap.range_eq_map, ← hs, Submodule.map_span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Apply `this` to reduce the goal to its premises.

Introduce `i`. Establish `h1` using `N.smul_mem (∏ j ∈ {i}ᶜ, a j) (ha' i)`. Rewrite `h1` using `[← mul_smul, ← Fintype.prod_eq_prod_compl_mul i]`. Conclude with `h1`. Use `⟨I, inferInstance, b.equivFun.toLinearMap ∘ₗ φ.codRestrict N (fun x => hle ⟨x, rfl⟩), ?_⟩` and prove the remaining obligations.

Introduce `x y h`. Establish `h2` using `b.equivFun.injective h`. Conclude with `hφ (congrArg Subtype.val h2)`.
-/
private theorem formsAR_embed {R M : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.IsTorsionFree R M] :
    ∃ (ι : Type) (_ : Fintype ι) (f : M →ₗ[R] (ι → R)), Function.Injective f := by
  classical
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  obtain ⟨I, indepI, hI⟩ := exists_maximal_linearIndepOn R s
  have indepI' : LinearIndependent R (fun x : I => s x) := indepI
  let N := Submodule.span R (Set.range fun x : I => s x)
  let b : Module.Basis I R N := Module.Basis.span indepI'
  have exists_a : ∀ i, ∃ a : R, a ≠ 0 ∧ a • s i ∈ N := by
    intro i
    by_cases hi : i ∈ I
    · refine ⟨1, one_ne_zero, ?_⟩
      rw [one_smul]
      exact Submodule.subset_span (Set.mem_range_self (⟨i, hi⟩ : I))
    · obtain ⟨a, ha, ha'⟩ := hI i hi
      refine ⟨a, ha, ?_⟩
      rwa [Set.image_eq_range s I] at ha'
  choose a ha ha' using exists_a
  have hA : (∏ i, a i) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    exact fun i _ => ha i
  let φ : M →ₗ[R] M := LinearMap.lsmul R M (∏ i, a i)
  have hφ : Function.Injective φ := LinearMap.ker_eq_bot.mp (LinearMap.ker_lsmul hA)
  have hle : LinearMap.range φ ≤ N := by
    suffices ∀ i, φ (s i) ∈ N by
      rw [LinearMap.range_eq_map, ← hs, Submodule.map_span_le]
      rintro _ ⟨i, rfl⟩
      apply this
    intro i
    have h1 := N.smul_mem (∏ j ∈ {i}ᶜ, a j) (ha' i)
    rw [← mul_smul, ← Fintype.prod_eq_prod_compl_mul i] at h1
    exact h1
  refine ⟨I, inferInstance,
    b.equivFun.toLinearMap ∘ₗ φ.codRestrict N (fun x => hle ⟨x, rfl⟩), ?_⟩
  intro x y h
  have h2 := b.equivFun.injective h
  exact hφ (congrArg Subtype.val h2)

/- English proof (translation)
Establish `: x = ∑ i, x i • (Pi.single i (1 : R) : ι → R)`. Use extensionality with `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) trivial`.
-/
private theorem formsAR_pi {R ι : Type} [CommRing R] [Fintype ι] (J : Ideal R) (x : ι → R)
    (hx : ∀ i, x i ∈ J) : x ∈ J • (⊤ : Submodule R (ι → R)) := by
  classical
  have : x = ∑ i, x i • (Pi.single i (1 : R) : ι → R) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) trivial

/- English proof (translation)
Introduce `A M _ _ _ _ _ _ _ I`. Take `⟨ι, _, f, hf⟩` from `formsAR_embed (R := A) (M := M)`. Take `⟨k, hk⟩` from `Ideal.exists_pow_inf_eq_pow_smul I (LinearMap.range f)`. Use `⟨k, fun n m hm => ?_⟩` and prove the remaining obligations. Establish `h1 : f m ∈ I ^ (n + k) • (⊤ : Submodule A (ι → A)) ⊓ LinearMap.range f` using `⟨formsAR_pi _ _ fun i => hm ((LinearMap.proj i) ∘ₗ f), ⟨m, rfl⟩⟩`.

Rewrite `h1` using `[hk (n + k) (Nat.le_add_left k n), Nat.add_sub_cancel]`. Establish `h2 : f m ∈ I ^ n • LinearMap.range f` using `Submodule.smul_mono le_rfl inf_le_right h1`. Rewrite `h2` using `[LinearMap.range_eq_map, ← Submodule.map_smul'']`. Take `⟨y, hy, hym⟩` from `h2`. Rewrite using `[← hf hym]`.

Conclude with `hy`.
-/
theorem UpperTheory.V.AlgebraTools.Conn.formsAR :
    ∀ {A M : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
      [Module.IsTorsionFree A M] (I : Ideal A), ∃ k : ℕ, ∀ (n : ℕ) (m : M),
        (∀ l : Module.Dual A M, l m ∈ I ^ (n + k)) → m ∈ I ^ n • (⊤ : Submodule A M) := by
  intro A M _ _ _ _ _ _ _ I
  obtain ⟨ι, _, f, hf⟩ := formsAR_embed (R := A) (M := M)
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (LinearMap.range f)
  refine ⟨k, fun n m hm => ?_⟩
  have h1 : f m ∈ I ^ (n + k) • (⊤ : Submodule A (ι → A)) ⊓ LinearMap.range f :=
    ⟨formsAR_pi _ _ fun i => hm ((LinearMap.proj i) ∘ₗ f), ⟨m, rfl⟩⟩
  rw [hk (n + k) (Nat.le_add_left k n), Nat.add_sub_cancel] at h1
  have h2 : f m ∈ I ^ n • LinearMap.range f := Submodule.smul_mono le_rfl inf_le_right h1
  rw [LinearMap.range_eq_map, ← Submodule.map_smul''] at h2
  obtain ⟨y, hy, hym⟩ := h2
  rw [← hf hym]
  exact hy
