import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulTransposeInjective

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.MixedLagr

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n d X W M hE f hf hhat`. Use `haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)`. Establish `hdom : Module.finrank F (Matrix (Fin n) (Fin d) E) = n * d * 2`. Rewrite using `[Module.finrank_matrix, hE]`. Simplify using the standard rewrite rules.

Establish `hcod : Module.finrank F ((Fin n × Fin d → F) × (Fin n × Fin d → F)) = n * d * 2`. Rewrite using `[Module.finrank_prod, Module.finrank_fintype_fun_eq_card]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish `hsurj : Function.Surjective f` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hdom.trans hcod.symm)).mp hf`.

Use `set g := (LinearMap.fst F (Fin n × Fin d → F) (Fin n × Fin d → F)).comp f with hg`. Establish `gsurj : Function.Surjective g`. Introduce `y`. Take `⟨x, hx⟩` from `hsurj (y, 0)`. Conclude with `⟨x, by simp [hg, hx]⟩`.

Use `⟨LinearMap.ker g, ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `LinearMap.finrank_range_add_finrank_ker g`. Rewrite `h1` using `[LinearMap.range_eq_top.mpr gsurj, finrank_top, Module.finrank_fintype_fun_eq_card, hdom]`. Simplify using `at h1`. Establish `: Fintype.card (Fin n × Fin d) = n * d` using `by simp`.

Use linear arithmetic over natural numbers and integers. Introduce `z hz`. Rewrite `hz` using `[LinearMap.mem_ker]`. Rewrite using `[← hhat z]`. Establish `hz' : (f z).1 = 0` using `by simpa [hg] using hz`.

Use function extensionality and compare the values at `i`. Simplify using `[hat, hz']`.
-/
theorem rat_first_zero_dim : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W), Module.finrank F E = 2 →
    ∀ f : Matrix (Fin n) (Fin d) E →ₗ[F] (Fin n × Fin d → F) × (Fin n × Fin d → F),
      Function.Injective f → (∀ x, hat (f x) = M.co.e (incM F x)) →
      ∃ K : Submodule F (Matrix (Fin n) (Fin d) E), Module.finrank F K = n * d ∧ ∀ z ∈ K, (M.co.e (incM F z)).1 = 0 := by
  intro F E _ _ _ _ _ σ n d X W M hE f hf hhat
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have hdom : Module.finrank F (Matrix (Fin n) (Fin d) E) = n * d * 2 := by
    rw [Module.finrank_matrix, hE]; simp
  have hcod : Module.finrank F ((Fin n × Fin d → F) × (Fin n × Fin d → F)) = n * d * 2 := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]; simp; ring
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hdom.trans hcod.symm)).mp hf
  set g := (LinearMap.fst F (Fin n × Fin d → F) (Fin n × Fin d → F)).comp f with hg
  have gsurj : Function.Surjective g := by
    intro y
    obtain ⟨x, hx⟩ := hsurj (y, 0)
    exact ⟨x, by simp [hg, hx]⟩
  refine ⟨LinearMap.ker g, ?_, ?_⟩
  · have h1 := LinearMap.finrank_range_add_finrank_ker g
    rw [LinearMap.range_eq_top.mpr gsurj, finrank_top, Module.finrank_fintype_fun_eq_card, hdom] at h1
    simp at h1
    have : Fintype.card (Fin n × Fin d) = n * d := by simp
    omega
  · intro z hz
    rw [LinearMap.mem_ker] at hz
    rw [← hhat z]
    have hz' : (f z).1 = 0 := by simpa [hg] using hz
    funext i
    simp [hat, hz']

end GlobalTheory.MixedLagr
