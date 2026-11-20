import Mathlib

namespace GlobalTheory.EvaluationSpanTop

open Module

/- English proof (translation)
Use `set S := Submodule.span ℂ (Set.range fun k : κ => (LinearMap.proj k : (κ → ℂ) →ₗ[ℂ] ℂ).comp W.subtype)`. Establish `hco : S.dualCoannihilator = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Rewrite `hx` using `[Submodule.mem_dualCoannihilator]`.

Establish `: ∀ k, (x : κ → ℂ) k = 0` using `fun k => hx _ (Submodule.subset_span ⟨k, rfl⟩)`. Rewrite using `[Submodule.mem_bot]`. Use extensionality with `k`. Simplify using `using this k`. Use `Subspace.dualCoannihilator_dualAnnihilator_eq (W := S)` as an intermediate fact.

Rewrite using `[← this, hco, Submodule.dualAnnihilator_bot]`.
-/
theorem span_eval_eq_top {κ : Type} (W : Submodule ℂ (κ → ℂ)) [FiniteDimensional ℂ W] :
    Submodule.span ℂ (Set.range fun k : κ => (LinearMap.proj k : (κ → ℂ) →ₗ[ℂ] ℂ).comp W.subtype) = ⊤ := by
  set S := Submodule.span ℂ (Set.range fun k : κ => (LinearMap.proj k : (κ → ℂ) →ₗ[ℂ] ℂ).comp W.subtype)
  have hco : S.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_dualCoannihilator] at hx
    have : ∀ k, (x : κ → ℂ) k = 0 := fun k =>
      hx _ (Submodule.subset_span ⟨k, rfl⟩)
    rw [Submodule.mem_bot]
    ext k
    simpa using this k
  have := Subspace.dualCoannihilator_dualAnnihilator_eq (W := S)
  rw [← this, hco, Submodule.dualAnnihilator_bot]

/- English proof (translation)
Introduce `κ W _`. Set `B` to `Module.finBasis ℂ W`. Establish `hspan` using `span_eval_eq_top W`. Establish `hc : ∀ i, ∃ c : κ →₀ ℂ, Finsupp.linearCombination ℂ (fun k : κ => (LinearMap.proj k : (κ → ℂ) →ₗ[ℂ] ℂ).comp W.subtype) c = B.coord i`. Introduce `i`.

Establish `: B.coord i ∈ Submodule.span ℂ (Set.range fun k : κ => (LinearMap.proj k : (κ → ℂ) →ₗ[ℂ] ℂ).comp W.subtype)`. Rewrite using `[hspan]`. Discharge the goal by the elementary cases of `trivial`. Conclude with `(Finsupp.mem_span_range_iff_exists_finsupp.mp this).imp fun c hc => by`. Rewrite using `[Finsupp.linearCombination_apply]`.

Conclude with `hc`. Use `choose c hc using hc`. Use `⟨Module.finrank ℂ W, fun i => (B i : κ → ℂ), c, fun i => (B i).2, ?_⟩` and prove the remaining obligations. Introduce `v hv k'`. Establish `hsum` using `B.sum_repr ⟨v, hv⟩`.

Establish `key : ∀ i, (Finsupp.sum (c i) fun (k : κ) (α : ℂ) ↦ α * v k) = B.repr ⟨v, hv⟩ i`. Introduce `i`. Rewrite using `[← Basis.coord_apply, ← hc i, Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum]`. Simplify using `[LinearMap.sum_apply]`. Repeatedly rewrite using `[key]`.

Establish `h2` using `congrArg (fun w : W => (w : κ → ℂ) k') hsum`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2`. Conclude with `h2.symm`.
-/
theorem main : ∀ {κ : Type} (W : Submodule ℂ (κ → ℂ)) [FiniteDimensional ℂ ↥W], ∃ (m : ℕ) (b : Fin m → κ → ℂ) (c : Fin m → κ →₀ ℂ), (∀ (i : Fin m), b i ∈ W) ∧ ∀ v ∈ W, ∀ (k' : κ), v k' = ∑ i : Fin m, (Finsupp.sum (c i) fun (k : κ) (α : ℂ) ↦ α * v k) * b i k' := by
  intro κ W _
  let B := Module.finBasis ℂ W
  have hspan := span_eval_eq_top W
  have hc : ∀ i, ∃ c : κ →₀ ℂ, Finsupp.linearCombination ℂ
      (fun k : κ => (LinearMap.proj k : (κ → ℂ) →ₗ[ℂ] ℂ).comp W.subtype) c = B.coord i := by
    intro i
    have : B.coord i ∈ Submodule.span ℂ (Set.range fun k : κ => (LinearMap.proj k : (κ → ℂ) →ₗ[ℂ] ℂ).comp W.subtype) := by
      rw [hspan]; trivial
    exact (Finsupp.mem_span_range_iff_exists_finsupp.mp this).imp fun c hc => by
      rw [Finsupp.linearCombination_apply]; exact hc
  choose c hc using hc
  refine ⟨Module.finrank ℂ W, fun i => (B i : κ → ℂ), c, fun i => (B i).2, ?_⟩
  intro v hv k'
  have hsum := B.sum_repr ⟨v, hv⟩
  have key : ∀ i, (Finsupp.sum (c i) fun (k : κ) (α : ℂ) ↦ α * v k) = B.repr ⟨v, hv⟩ i := by
    intro i
    rw [← Basis.coord_apply, ← hc i, Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum]
    simp [LinearMap.sum_apply]
  simp_rw [key]
  have h2 := congrArg (fun w : W => (w : κ → ℂ) k') hsum
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
  exact h2.symm

end GlobalTheory.EvaluationSpanTop
