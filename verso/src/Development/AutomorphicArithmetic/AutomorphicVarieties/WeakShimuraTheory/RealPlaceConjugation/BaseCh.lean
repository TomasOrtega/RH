import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

/- English proof (translation)
Apply `rank_le` to reduce the goal to its premises. Introduce `s hs`. Establish `hy : LinearIndependent k₀ (fun i : s => (((i : Submodule.span k₀ (Set.range z))) : k))` using `hs.map' (Submodule.span k₀ (Set.range z)).subtype (Submodule.ker_subtype _)`. Establish `hφ : ∀ j : s, ∃ φ : k →ₗ[k₀] k₀, ∀ i : s, φ (((i : Submodule.span k₀ (Set.range z))) : k) = if i = j then 1 else 0`. Introduce `j`.

Take `⟨g, hg⟩` from `LinearMap.exists_extend ((Module.Basis.span hy).coord j)`. Use `⟨g, fun i => ?_⟩` and prove the remaining obligations. Establish `h1` using `LinearMap.congr_fun hg (Module.Basis.span hy i)`. Rewrite `h1` using `[Module.Basis.span_apply]`. Rewrite `h1` using `[LinearMap.comp_apply, Submodule.subtype_apply]`.

Rewrite using `[h1, ← Module.Basis.span_apply hy i, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]`. Use `choose φ hφ using hφ`. Establish `hw : LinearIndependent k₀ (fun j : s => (⟨fun x => φ j (z x), hz (φ j)⟩ : W₀))`. Rewrite using `[linearIndependent_iff']`. Introduce `t c hc j hj`.

Establish `hψz : ∀ x, (∑ i ∈ t, c i • φ i) (z x) = 0`. Introduce `x`. Use `congrArg (fun v : W₀ => (v : X → k₀) x) hc` as an intermediate fact. Simplify `this` using `[LinearMap.sum_apply, Finset.sum_apply]`. Establish `hψL : Submodule.span k₀ (Set.range z) ≤ LinearMap.ker (∑ i ∈ t, c i • φ i)`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `hψz x`. Establish `h2` using `hψL (j : Submodule.span k₀ (Set.range z)).2`. Rewrite `h2` using `[LinearMap.mem_ker, LinearMap.sum_apply]`.

Simplify using `only [LinearMap.smul_apply, hφ, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, hj, if_true] at h2`. Conclude with `h2`. Establish `hc` using `hw.cardinal_le_rank`. Rewrite `hc` using `[Cardinal.mk_coe_finset]`. Conclude with `hc.trans hW₀` after adjusting the coercions.
-/
private theorem rank_span_range_le_of_linearForm_comp_mem {X k₀ k : Type} [Field k₀] [Field k] [Algebra k₀ k]
    (W₀ : Submodule k₀ (X → k₀)) (n : ℕ) (hW₀ : Module.rank k₀ W₀ ≤ n) (z : X → k)
    (hz : ∀ φ : k →ₗ[k₀] k₀, (fun x => φ (z x)) ∈ W₀) :
    Module.rank k₀ (Submodule.span k₀ (Set.range z)) ≤ n := by
  apply rank_le
  intro s hs
  have hy : LinearIndependent k₀ (fun i : s => (((i : Submodule.span k₀ (Set.range z))) : k)) :=
    hs.map' (Submodule.span k₀ (Set.range z)).subtype (Submodule.ker_subtype _)
  have hφ : ∀ j : s, ∃ φ : k →ₗ[k₀] k₀, ∀ i : s,
      φ (((i : Submodule.span k₀ (Set.range z))) : k) = if i = j then 1 else 0 := by
    intro j
    obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Module.Basis.span hy).coord j)
    refine ⟨g, fun i => ?_⟩
    have h1 := LinearMap.congr_fun hg (Module.Basis.span hy i)
    rw [Module.Basis.span_apply] at h1
    rw [LinearMap.comp_apply, Submodule.subtype_apply] at h1
    rw [h1, ← Module.Basis.span_apply hy i, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply]
  choose φ hφ using hφ
  have hw : LinearIndependent k₀ (fun j : s => (⟨fun x => φ j (z x), hz (φ j)⟩ : W₀)) := by
    rw [linearIndependent_iff']
    intro t c hc j hj
    have hψz : ∀ x, (∑ i ∈ t, c i • φ i) (z x) = 0 := by
      intro x
      have := congrArg (fun v : W₀ => (v : X → k₀) x) hc
      simpa [LinearMap.sum_apply, Finset.sum_apply] using this
    have hψL : Submodule.span k₀ (Set.range z) ≤ LinearMap.ker (∑ i ∈ t, c i • φ i) := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact hψz x
    have h2 := hψL (j : Submodule.span k₀ (Set.range z)).2
    rw [LinearMap.mem_ker, LinearMap.sum_apply] at h2
    simp only [LinearMap.smul_apply, hφ, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, hj, if_true] at h2
    exact h2
  have hc := hw.cardinal_le_rank
  rw [Cardinal.mk_coe_finset] at hc
  exact_mod_cast hc.trans hW₀

/- English proof (translation)
Establish `hr` using `rank_span_range_le_of_linearForm_comp_mem W₀ n hW₀ z hz`. Use `haveI : Module.Finite k₀ (Submodule.span k₀ (Set.range z)) := Module.rank_lt_aleph0_iff.1 (hr.trans_lt (Cardinal.nat_lt_aleph0 n))`. Use `set L := Submodule.span k₀ (Set.range z)`. Set `e` to `Module.finBasis k₀ L`. Establish `hext : ∀ j, ∃ φ : k →ₗ[k₀] k₀, φ ∘ₗ L.subtype = e.coord j` using `fun j => LinearMap.exists_extend (e.coord j)`.

Use `choose φ hφ using hext`. Establish `hzx : ∀ x, z x = ∑ j, φ j (z x) • ((e j : L) : k)`. Introduce `x`. Establish `hx : z x ∈ L` using `Submodule.subset_span ⟨x, rfl⟩`. Establish `h1` using `congrArg L.subtype (e.sum_repr ⟨z x, hx⟩)`.

Rewrite `h1` using `[map_sum]`. Use `show L.subtype ⟨z x, hx⟩ = _`. Rewrite using `[← h1]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, Submodule.subtype_apply]`.

Use `congr 1`. Use `LinearMap.congr_fun (hφ j) ⟨z x, hx⟩` as an intermediate fact. Rewrite `this` using `[LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.coord_apply]`. Conclude with `this.symm`. Establish `hzeq : z = ∑ j, ((e j : L) : k) • (fun x => algebraMap k₀ k (φ j (z x)))`.

Use function extensionality and compare the values at `x`. Rewrite using `[hzx x, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, smul_eq_mul, Algebra.smul_def, mul_comm]`. Rewrite using `[hzeq]`.

Use `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Conclude with `Submodule.subset_span ⟨_, hz (φ j), rfl⟩`.
-/
private theorem mem_span_image_algebraMap_of_linearForm_comp_mem {X k₀ k : Type} [Field k₀] [Field k] [Algebra k₀ k]
    (W₀ : Submodule k₀ (X → k₀)) (n : ℕ) (hW₀ : Module.rank k₀ W₀ ≤ n) (z : X → k)
    (hz : ∀ φ : k →ₗ[k₀] k₀, (fun x => φ (z x)) ∈ W₀) :
    z ∈ Submodule.span k ((fun w : X → k₀ => fun x => algebraMap k₀ k (w x)) '' (W₀ : Set (X → k₀))) := by
  have hr := rank_span_range_le_of_linearForm_comp_mem W₀ n hW₀ z hz
  haveI : Module.Finite k₀ (Submodule.span k₀ (Set.range z)) :=
    Module.rank_lt_aleph0_iff.1 (hr.trans_lt (Cardinal.nat_lt_aleph0 n))
  set L := Submodule.span k₀ (Set.range z)
  let e := Module.finBasis k₀ L
  have hext : ∀ j, ∃ φ : k →ₗ[k₀] k₀, φ ∘ₗ L.subtype = e.coord j :=
    fun j => LinearMap.exists_extend (e.coord j)
  choose φ hφ using hext
  have hzx : ∀ x, z x = ∑ j, φ j (z x) • ((e j : L) : k) := by
    intro x
    have hx : z x ∈ L := Submodule.subset_span ⟨x, rfl⟩
    have h1 := congrArg L.subtype (e.sum_repr ⟨z x, hx⟩)
    rw [map_sum] at h1
    show L.subtype ⟨z x, hx⟩ = _
    rw [← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, Submodule.subtype_apply]
    congr 1
    have := LinearMap.congr_fun (hφ j) ⟨z x, hx⟩
    rw [LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.coord_apply] at this
    exact this.symm
  have hzeq : z = ∑ j, ((e j : L) : k) • (fun x => algebraMap k₀ k (φ j (z x))) := by
    funext x
    rw [hzx x, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, Algebra.smul_def, mul_comm]
  rw [hzeq]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨_, hz (φ j), rfl⟩

/- English proof (translation)
Introduce `X k₀ k _ _ _ W₀ W n hW₀ hW`. Establish `hWS : W ≤ Submodule.span k ((fun w : X → k₀ => fun x => algebraMap k₀ k (w x)) '' (W₀ : Set (X → k₀)))` using `fun z hz => mem_span_image_algebraMap_of_linearForm_comp_mem W₀ n hW₀ z (hW z hz)`. Set `A : (X → k₀) →ₗ[k₀] (X → k)` to `LinearMap.pi fun x => (Algebra.linearMap k₀ k).comp (LinearMap.proj x)`. Set `b` to `Module.Free.chooseBasis k₀ W₀`. Establish `hsub : Submodule.span k ((fun w : X → k₀ => fun x => algebraMap k₀ k (w x)) '' (W₀ : Set (X → k₀))) ≤ Submodule.span k (Set.range fun i => A (b i : X → k₀))`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨w, hw, rfl⟩`. Establish `h1 : A w ∈ Submodule.map (A ∘ₗ W₀.subtype) ⊤` using `⟨⟨w, hw⟩, trivial, rfl⟩`. Rewrite `h1` using `[← b.span_eq, Submodule.map_span, ← Set.range_comp]`. Conclude with `Submodule.span_le_restrictScalars k₀ k _ h1`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.V.Ws.rank_le_of_linearForm_comp_mem_of_rank_le :
    ∀ (X k₀ k : Type) [Field k₀] [Field k] [Algebra k₀ k] (W₀ : Submodule k₀ (X → k₀)) (W : Submodule k (X → k)) (n : ℕ), Module.rank k₀ W₀ ≤ n → (∀ z ∈ W, ∀ φ : k →ₗ[k₀] k₀, (fun x => φ (z x)) ∈ W₀) → Module.rank k W ≤ n := by
  intro X k₀ k _ _ _ W₀ W n hW₀ hW
  have hWS : W ≤ Submodule.span k
      ((fun w : X → k₀ => fun x => algebraMap k₀ k (w x)) '' (W₀ : Set (X → k₀))) :=
    fun z hz => mem_span_image_algebraMap_of_linearForm_comp_mem W₀ n hW₀ z (hW z hz)
  let A : (X → k₀) →ₗ[k₀] (X → k) :=
    LinearMap.pi fun x => (Algebra.linearMap k₀ k).comp (LinearMap.proj x)
  let b := Module.Free.chooseBasis k₀ W₀
  have hsub : Submodule.span k
      ((fun w : X → k₀ => fun x => algebraMap k₀ k (w x)) '' (W₀ : Set (X → k₀))) ≤
      Submodule.span k (Set.range fun i => A (b i : X → k₀)) := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    have h1 : A w ∈ Submodule.map (A ∘ₗ W₀.subtype) ⊤ := ⟨⟨w, hw⟩, trivial, rfl⟩
    rw [← b.span_eq, Submodule.map_span, ← Set.range_comp] at h1
    exact Submodule.span_le_restrictScalars k₀ k _ h1
  calc Module.rank k W
      ≤ Module.rank k (Submodule.span k
          ((fun w : X → k₀ => fun x => algebraMap k₀ k (w x)) '' (W₀ : Set (X → k₀)))) :=
        Submodule.rank_mono hWS
    _ ≤ Module.rank k (Submodule.span k (Set.range fun i => A (b i : X → k₀))) :=
        Submodule.rank_mono hsub
    _ ≤ Cardinal.mk (Set.range fun i => A (b i : X → k₀)) := rank_span_le _
    _ ≤ Cardinal.mk (Module.Free.ChooseBasisIndex k₀ W₀) := Cardinal.mk_range_le
    _ = Module.rank k₀ W₀ := (Module.Free.rank_eq_card_chooseBasisIndex k₀ W₀).symm
    _ ≤ n := hW₀
