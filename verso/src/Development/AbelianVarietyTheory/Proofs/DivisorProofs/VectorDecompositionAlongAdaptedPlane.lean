import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.Decomp

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B d d₁ W W₁ H' i₀ i₁ r s hW hH v`. Set `V₀ : Submodule E (Fin d → E)` to `(E ∙ H'.x) ⊔ LinearMap.range (Matrix.mulVecLin H'.ι) ⊔ (E ∙ H'.y)`. Establish `hle : Submodule.span E (W.L : Set (Fin d → E)) ≤ V₀`. Rewrite using `[Submodule.span_le]`. Introduce `z hz`.

Take `⟨s', t, u, -, -, -, rfl⟩` from `hH.split z hz`. Use `Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_` and prove the remaining obligations. Conclude with `Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))`. Conclude with `Submodule.mem_sup_left (Submodule.mem_sup_right ⟨u, rfl⟩)`. Conclude with `Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))`.

Rewrite `hle` using `[hW.lat.span_eq_top]`. Establish `hv : v ∈ V₀` using `hle Submodule.mem_top`. Take `⟨p, hp, q, hq, rfl⟩` from `Submodule.mem_sup.mp hv`. Take `⟨p1, hp1, p2, hp2, rfl⟩` from `Submodule.mem_sup.mp hp`. Take `⟨a, rfl⟩` from `Submodule.mem_span_singleton.mp hp1`.

Take `⟨u, rfl⟩` from `hp2`. Take `⟨b, rfl⟩` from `Submodule.mem_span_singleton.mp hq`. Conclude with `⟨a, b, u, by simp [Matrix.mulVecLin_apply]⟩`.
-/
theorem every_vector_adapted_plane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r s : ℕ), W.IsSkew σ B r s → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ v : Fin d → E, ∃ (a b : E) (u : Fin d₁ → E), v = a • H'.x + H'.ι *ᵥ u + b • H'.y := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H' i₀ i₁ r s hW hH v
  let V₀ : Submodule E (Fin d → E) :=
    (E ∙ H'.x) ⊔ LinearMap.range (Matrix.mulVecLin H'.ι) ⊔ (E ∙ H'.y)
  have hle : Submodule.span E (W.L : Set (Fin d → E)) ≤ V₀ := by
    rw [Submodule.span_le]
    intro z hz
    obtain ⟨s', t, u, -, -, -, rfl⟩ := hH.split z hz
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right ⟨u, rfl⟩)
    · exact Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  rw [hW.lat.span_eq_top] at hle
  have hv : v ∈ V₀ := hle Submodule.mem_top
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨p1, hp1, p2, hp2, rfl⟩ := Submodule.mem_sup.mp hp
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hp1
  obtain ⟨u, rfl⟩ := hp2
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hq
  exact ⟨a, b, u, by simp [Matrix.mulVecLin_apply]⟩

end GlobalTheory.Decomp
