import Mathlib

namespace GlobalTheory.EvaluationSpanTopToricGeometry

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨f, hf0, hle⟩` from `Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)`. Use `set v : V := (Module.evalEquiv ℂ V).symm f with hv`. Establish `hfv : Module.evalEquiv ℂ V v = f` using `by rw [hv, LinearEquiv.apply_symm_apply]`. Establish `hv0 : v = 0`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`. Establish `hx : (LinearMap.proj x : (X → ℂ) →ₗ[ℂ] ℂ) ∘ₗ V.subtype ∈ LinearMap.ker f` using `hle (Submodule.subset_span ⟨x, rfl⟩)`. Rewrite `hx` using `[LinearMap.mem_ker, ← hfv]`. Conclude with `hx`.

Apply `hf0` to reduce the goal to its premises. Rewrite using `[← hfv, hv0, map_zero]`.
-/
theorem span_eval_eq_top {X : Type} (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ V] :
    Submodule.span ℂ (Set.range fun x : X => ((LinearMap.proj x : (X → ℂ) →ₗ[ℂ] ℂ) ∘ₗ V.subtype))
      = ⊤ := by

  by_contra hne
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  set v : V := (Module.evalEquiv ℂ V).symm f with hv
  have hfv : Module.evalEquiv ℂ V v = f := by rw [hv, LinearEquiv.apply_symm_apply]
  have hv0 : v = 0 := by
    apply Subtype.ext
    funext x
    have hx : (LinearMap.proj x : (X → ℂ) →ₗ[ℂ] ℂ) ∘ₗ V.subtype ∈ LinearMap.ker f :=
      hle (Submodule.subset_span ⟨x, rfl⟩)
    rw [LinearMap.mem_ker, ← hfv] at hx
    exact hx
  apply hf0
  rw [← hfv, hv0, map_zero]

/- English proof (translation)
Set `Φ : Module.Dual ℂ V →ₗ[ℂ] (Y → ℂ)` to `{ toFun := fun φ y => φ ⟨fun x => F x y, hV y⟩ map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Establish `hΦ : ∀ φ, Φ φ ∈ L`. Establish `hle : Submodule.span ℂ (Set.range fun x : X => ((LinearMap.proj x : (X → ℂ) →ₗ[ℂ] ℂ) ∘ₗ V.subtype)) ≤ L.comap Φ`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, rfl⟩`.

Conclude with `hL x`. Introduce `φ`. Conclude with `hle (by rw [span_eval_eq_top V]; trivial)`. Set `b` to `Module.finBasis ℂ V`. Use `⟨Module.finrank ℂ V, fun i => (b i : X → ℂ), fun i => Φ (b.coord i), fun i => ⟨(b i).2, hΦ _⟩, ?_⟩` and prove the remaining obligations.

Introduce `x y`. Establish `hs` using `congrArg (fun w : V => (w : X → ℂ) x) (b.sum_repr ⟨fun x' => F x' y, hV y⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs`. Rewrite using `[← hs]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[mul_comm]`. Both sides reduce to the same expression.
-/
theorem exists_sum_mul {X Y : Type} (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ V]
    (L : Submodule ℂ (Y → ℂ)) (F : X → Y → ℂ) (hV : ∀ y : Y, (fun x : X => F x y) ∈ V)
    (hL : ∀ x : X, F x ∈ L) :
    ∃ (n : ℕ) (h : Fin n → X → ℂ) (k : Fin n → Y → ℂ),
      (∀ i : Fin n, h i ∈ V ∧ k i ∈ L) ∧
        ∀ (x : X) (y : Y), F x y = ∑ i : Fin n, h i x * k i y := by

  let Φ : Module.Dual ℂ V →ₗ[ℂ] (Y → ℂ) :=
    { toFun := fun φ y => φ ⟨fun x => F x y, hV y⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

  have hΦ : ∀ φ, Φ φ ∈ L := by
    have hle : Submodule.span ℂ (Set.range fun x : X => ((LinearMap.proj x : (X → ℂ) →ₗ[ℂ] ℂ) ∘ₗ V.subtype))
        ≤ L.comap Φ := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact hL x
    intro φ
    exact hle (by rw [span_eval_eq_top V]; trivial)
  let b := Module.finBasis ℂ V
  refine ⟨Module.finrank ℂ V, fun i => (b i : X → ℂ), fun i => Φ (b.coord i), fun i => ⟨(b i).2, hΦ _⟩, ?_⟩
  intro x y
  have hs := congrArg (fun w : V => (w : X → ℂ) x) (b.sum_repr ⟨fun x' => F x' y, hV y⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs
  rw [← hs]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]
  rfl

end GlobalTheory.EvaluationSpanTopToricGeometry
