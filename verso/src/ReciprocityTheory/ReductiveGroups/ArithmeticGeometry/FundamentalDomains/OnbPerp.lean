import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis

open Complex
open scoped ComplexConjugate InnerProductSpace

/- English proof (translation)
Set `v : EuclideanSpace ℂ (Fin n)` to `WithLp.toLp 2 α`. Establish `hv : v ≠ 0`. Introduce `h`. Apply `hα` to reduce the goal to its premises. Establish `h'` using `congrArg WithLp.ofLp h`.

Simplify `h'` using `[v]`. Use `haveI : Fact (Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = (n - 1) + 1) := ⟨by rw [finrank_euclideanSpace_fin]; omega⟩`. Establish `hK : Module.finrank ℂ (ℂ ∙ v)ᗮ = n - 1` using `Submodule.finrank_orthogonal_span_singleton hv`. Set `b : OrthonormalBasis (Fin (n - 1)) ℂ (ℂ ∙ v)ᗮ` to `(stdOrthonormalBasis ℂ (ℂ ∙ v)ᗮ).reindex (finCongr hK)`. Use `⟨fun k a => ((b k : (ℂ ∙ v)ᗮ) : EuclideanSpace ℂ (Fin n)).ofLp a, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `k l`. Establish `h` using `(orthonormal_iff_ite.mp b.orthonormal) l k`. Rewrite `h` using `[Submodule.coe_inner, EuclideanSpace.inner_eq_star_dotProduct]`. Simplify using `only [dotProduct, Pi.star_apply, RCLike.star_def] at h`. Rewrite using `[h]`.

Conclude with `if_congr eq_comm rfl rfl`. Introduce `k`. Establish `h` using `Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b k).2`. Rewrite `h` using `[EuclideanSpace.inner_eq_star_dotProduct]`. Simplify `h` using `[dotProduct, v]`.

Introduce `γ hγ`. Establish `hw : (WithLp.toLp 2 γ : EuclideanSpace ℂ (Fin n)) ∈ (ℂ ∙ v)ᗮ`. Rewrite using `[Submodule.mem_orthogonal_singleton_iff_inner_right, EuclideanSpace.inner_eq_star_dotProduct]`. Simplify `hγ` using `[dotProduct, v]`. Establish `hsum` using `b.sum_repr' ⟨_, hw⟩`.

Establish `hγeq : γ = ∑ i, inner ℂ (b i) (⟨_, hw⟩ : (ℂ ∙ v)ᗮ) • (fun a => ((b i : (ℂ ∙ v)ᗮ) : EuclideanSpace ℂ (Fin n)).ofLp a)`. Use function extensionality and compare the values at `a`. Establish `h` using `congrArg (fun x : (ℂ ∙ v)ᗮ => ((x : EuclideanSpace ℂ (Fin n))).ofLp a) hsum`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at h`. Rewrite using `[Finset.sum_apply]`.

Simplify using `using h.symm`. Rewrite using `[hγeq]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem onb_perp (n : ℕ) (hn : 1 ≤ n) (α : Fin n → ℂ) (hα : α ≠ 0) :
    ∃ g : Fin (n - 1) → Fin n → ℂ,
      (∀ k l, ∑ a, g k a * conj (g l a) = if k = l then 1 else 0) ∧
      (∀ k, ∑ a, g k a * conj (α a) = 0) ∧
      (∀ γ : Fin n → ℂ, ∑ a, γ a * conj (α a) = 0 → γ ∈ Submodule.span ℂ (Set.range g)) := by
  classical
  let v : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 α
  have hv : v ≠ 0 := by
    intro h
    apply hα
    have h' := congrArg WithLp.ofLp h
    simpa [v] using h'
  haveI : Fact (Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = (n - 1) + 1) :=
    ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
  have hK : Module.finrank ℂ (ℂ ∙ v)ᗮ = n - 1 := Submodule.finrank_orthogonal_span_singleton hv
  let b : OrthonormalBasis (Fin (n - 1)) ℂ (ℂ ∙ v)ᗮ :=
    (stdOrthonormalBasis ℂ (ℂ ∙ v)ᗮ).reindex (finCongr hK)
  refine ⟨fun k a => ((b k : (ℂ ∙ v)ᗮ) : EuclideanSpace ℂ (Fin n)).ofLp a, ?_, ?_, ?_⟩
  · intro k l
    have h := (orthonormal_iff_ite.mp b.orthonormal) l k
    rw [Submodule.coe_inner, EuclideanSpace.inner_eq_star_dotProduct] at h
    simp only [dotProduct, Pi.star_apply, RCLike.star_def] at h
    rw [h]
    exact if_congr eq_comm rfl rfl
  · intro k
    have h := Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b k).2
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    simpa [dotProduct, v] using h
  · intro γ hγ
    have hw : (WithLp.toLp 2 γ : EuclideanSpace ℂ (Fin n)) ∈ (ℂ ∙ v)ᗮ := by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right, EuclideanSpace.inner_eq_star_dotProduct]
      simpa [dotProduct, v] using hγ
    have hsum := b.sum_repr' ⟨_, hw⟩
    have hγeq : γ = ∑ i, inner ℂ (b i) (⟨_, hw⟩ : (ℂ ∙ v)ᗮ) •
        (fun a => ((b i : (ℂ ∙ v)ᗮ) : EuclideanSpace ℂ (Fin n)).ofLp a) := by
      funext a
      have h := congrArg (fun x : (ℂ ∙ v)ᗮ => ((x : EuclideanSpace ℂ (Fin n))).ofLp a) hsum
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h
      rw [Finset.sum_apply]
      simpa using h.symm
    rw [hγeq]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis
