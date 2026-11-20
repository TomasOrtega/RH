import Mathlib
open scoped InnerProductSpace

namespace GlobalTheory

/- English proof (translation)
Introduce `K X Y H W _ _ _ _ _ _ _ _ _ _ σ θ j jW T hspan hind hT`. Take `⟨C, hC⟩` from `Submodule.exists_isCompl (LinearMap.ker θ)`. Set `b` to `Module.finBasis K C`. Establish `hinj : LinearMap.ker (θ ∘ₗ C.subtype) = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`.

Introduce `m hm`. Establish `h1 : (m : X) ∈ LinearMap.ker θ` using `hm`. Establish `h2 : (m : X) ∈ LinearMap.ker θ ⊓ C` using `⟨h1, m.2⟩`. Rewrite `h2` using `[hC.inf_eq_bot]`. Conclude with `Subtype.ext (by simpa using h2)`.

Establish `hli : LinearIndependent K (fun k => θ (b k : X))` using `b.linearIndependent.map' (θ ∘ₗ C.subtype) hinj`. Establish `hli2` using `hind _ _ hli`. Use `set N := Submodule.span ℂ (j '' (LinearMap.ker θ : Set X)) with hN`. Establish `hNT : N ≤ LinearMap.ker T`. Rewrite using `[hN, Submodule.span_le]`.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Establish `hx' : θ x = 0` using `hx`. Use `show T (j x) = 0`. Rewrite using `[hT, hx', map_zero]`. Establish `htop : N ⊔ Submodule.span ℂ (Set.range fun k => j (b k : X)) = ⊤`.

Rewrite using `[eq_top_iff, ← hspan, Submodule.span_le]`. Introduce and unpack `_ ⟨x, rfl⟩`. Establish `hx : x ∈ LinearMap.ker θ ⊔ C` using `by rw [hC.sup_eq_top]; trivial`. Take `⟨u, hu, c, hc, rfl⟩` from `Submodule.mem_sup.1 hx`. Rewrite using `[map_add]`.

Use `Submodule.add_mem_sup (Submodule.subset_span ⟨u, hu, rfl⟩) ?_` and prove the remaining obligations. Establish `hcs : c = ∑ k, b.repr ⟨c, hc⟩ k • (b k : X)`. Use `congrArg (fun z : C => (z : X)) (b.sum_repr ⟨c, hc⟩)` as an intermediate fact. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at this`. Conclude with `this.symm`.

Rewrite using `[hcs, map_sum]`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_smulₛₗ]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`. Introduce `h hh`.

Establish `hmem : h ∈ N ⊔ Submodule.span ℂ (Set.range fun k => j (b k : X))`. Rewrite using `[htop]`. Discharge the goal by the elementary cases of `trivial`. Take `⟨u, hu, s, hs, rfl⟩` from `Submodule.mem_sup.1 hmem`. Take `⟨a, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun ℂ).1 hs`.

Establish `hTu : T u = 0` using `hNT hu`. Establish `h0 : ∑ k, a k • jW (θ (b k : X)) = 0`. Establish `: T (u + ∑ k, a k • j (b k : X)) = 0` using `hh`. Rewrite `this` using `[map_add, hTu, zero_add, map_sum]`. Simplify `this` using `[hT]`.

Establish `ha` using `Fintype.linearIndependent_iff.1 hli2 a h0`. Simplify `hu` using `[ha]`.
-/
theorem ker_le_span_image_ker_of_semilinear :
    ∀ (K X Y H W : Type) [Field K] [AddCommGroup X] [Module K X] [FiniteDimensional K X] [AddCommGroup Y] [Module K Y] [AddCommGroup H] [Module ℂ H] [AddCommGroup W] [Module ℂ W] (σ : K →+* ℂ) (θ : X →ₗ[K] Y) (j : X →ₛₗ[σ] H) (jW : Y →ₛₗ[σ] W) (T : H →ₗ[ℂ] W), Submodule.span ℂ (Set.range j) = ⊤ → (∀ (n : ℕ) (b : Fin n → Y), LinearIndependent K b → LinearIndependent ℂ fun k => jW (b k)) → (∀ x, T (j x) = jW (θ x)) → LinearMap.ker T ≤ Submodule.span ℂ (j '' (LinearMap.ker θ : Set X)) := by
  intro K X Y H W _ _ _ _ _ _ _ _ _ _ σ θ j jW T hspan hind hT
  classical
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.ker θ)
  let b := Module.finBasis K C
  have hinj : LinearMap.ker (θ ∘ₗ C.subtype) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro m hm
    have h1 : (m : X) ∈ LinearMap.ker θ := hm
    have h2 : (m : X) ∈ LinearMap.ker θ ⊓ C := ⟨h1, m.2⟩
    rw [hC.inf_eq_bot] at h2
    exact Subtype.ext (by simpa using h2)
  have hli : LinearIndependent K (fun k => θ (b k : X)) :=
    b.linearIndependent.map' (θ ∘ₗ C.subtype) hinj
  have hli2 := hind _ _ hli
  set N := Submodule.span ℂ (j '' (LinearMap.ker θ : Set X)) with hN
  have hNT : N ≤ LinearMap.ker T := by
    rw [hN, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : θ x = 0 := hx
    show T (j x) = 0
    rw [hT, hx', map_zero]
  have htop : N ⊔ Submodule.span ℂ (Set.range fun k => j (b k : X)) = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ LinearMap.ker θ ⊔ C := by rw [hC.sup_eq_top]; trivial
    obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    refine Submodule.add_mem_sup (Submodule.subset_span ⟨u, hu, rfl⟩) ?_
    have hcs : c = ∑ k, b.repr ⟨c, hc⟩ k • (b k : X) := by
      have := congrArg (fun z : C => (z : X)) (b.sum_repr ⟨c, hc⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this.symm
    rw [hcs, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  intro h hh
  have hmem : h ∈ N ⊔ Submodule.span ℂ (Set.range fun k => j (b k : X)) := by
    rw [htop]; trivial
  obtain ⟨u, hu, s, hs, rfl⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hs
  have hTu : T u = 0 := hNT hu
  have h0 : ∑ k, a k • jW (θ (b k : X)) = 0 := by
    have : T (u + ∑ k, a k • j (b k : X)) = 0 := hh
    rw [map_add, hTu, zero_add, map_sum] at this
    simpa [hT] using this
  have ha := Fintype.linearIndependent_iff.1 hli2 a h0
  simpa [ha] using hu

end GlobalTheory
