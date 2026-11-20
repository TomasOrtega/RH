import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.CMArg

/- English proof (translation)
Establish `hc` using `h.2.1`. Establish `hcx : (NumberField.InfinitePlace.mk τ).IsComplex` using `hc.isComplex _`. Establish `hcx' : ¬ (NumberField.InfinitePlace.mk τ).IsReal` using `NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hcx`. Rewrite `hcx'` using `[NumberField.InfinitePlace.isReal_mk_iff]`. Assume the negation of the conclusion as `hall`.

Use `push_neg at hall`. Apply `hcx'` to reduce the goal to its premises. Use extensionality with `x`. Apply the tactic sequence `apply Complex.ext <;> simp [hall x]`.
-/
theorem exists_im_ne_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (τ : E →+* ℂ) :
    ∃ x : E, (τ x).im ≠ 0 := by
  have hc := h.2.1
  have hcx : (NumberField.InfinitePlace.mk τ).IsComplex := hc.isComplex _
  have hcx' : ¬ (NumberField.InfinitePlace.mk τ).IsReal :=
    NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hcx
  rw [NumberField.InfinitePlace.isReal_mk_iff] at hcx'
  by_contra hall
  push_neg at hall
  apply hcx'
  ext x
  apply Complex.ext <;> simp [hall x]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm τ κ hκ`. Take `⟨x, hx⟩` from `exists_im_ne_zero σ hcm τ`. Establish `hτk : ∀ k : ℕ, τ ((k : E) + x) = (k : ℂ) + τ x` using `by intro k; simp`. Establish `hne : ∀ k : ℕ, τ ((k : E) + x) ≠ 0`. Introduce `k h0`.

Apply `hx` to reduce the goal to its premises. Use `congrArg Complex.im h0` as an intermediate fact. Simplify `this` using `[hτk]`. Set `f : ℕ → ℂ` to `fun k => τ ((k : E) + x) / (‖τ ((k : E) + x)‖ : ℂ)`. Establish `hinj : Function.Injective f`.

Introduce `k l hkl`. Simplify using `only [f] at hkl`. Establish `hna : 0 < ‖τ ((k : E) + x)‖` using `norm_pos_iff.mpr (hne k)`. Establish `hnb : 0 < ‖τ ((l : E) + x)‖` using `norm_pos_iff.mpr (hne l)`. Establish `him` using `congrArg Complex.im hkl`.

Rewrite `him` using `[Complex.div_ofReal_im, Complex.div_ofReal_im, hτk, hτk]`. Simplify using `only [Complex.add_im, Complex.natCast_im, zero_add] at him`. Establish `hn : ‖τ ((k : E) + x)‖ = ‖τ ((l : E) + x)‖` using `by first`. Consider the case `exact (div_right_inj' hx).mp him`. Consider the case `(field_simp at him; simpa [one_div] using him)`.

Rewrite `hkl` using `[hn]`. Establish `hab : τ ((k : E) + x) = τ ((l : E) + x)`. Establish `hz : ((‖τ ((l : E) + x)‖ : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hnb.ne'`. Conclude with `(div_left_inj' hz).mp hkl`. Rewrite `hab` using `[hτk, hτk]`.

Use `congrArg Complex.re hab` as an intermediate fact. Simplify using `at this`. Conclude with `this` after adjusting the coercions. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Establish `hsub : Set.range f ⊆ ((Polynomial.nthRoots κ (1 : ℂ)).toFinset : Set ℂ)`. Introduce and unpack `_ ⟨k, rfl⟩`. Simplify using `only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hκ]`. Conclude with `hcon _ (fun h0 => hne k (by rw [h0, map_zero]))`. Conclude with `(Set.infinite_range_of_injective hinj) ((Finset.finite_toSet _).subset hsub)`.
-/
theorem exists_ne_zero_arg_pow_ne_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (τ : E →+* ℂ) (κ : ℕ), 0 < κ → ∃ ξ : E, ξ ≠ 0 ∧ (τ ξ / (‖τ ξ‖ : ℂ)) ^ κ ≠ 1 := by
  intro F E _ _ _ _ _ σ hcm τ κ hκ
  obtain ⟨x, hx⟩ := exists_im_ne_zero σ hcm τ
  have hτk : ∀ k : ℕ, τ ((k : E) + x) = (k : ℂ) + τ x := by intro k; simp
  have hne : ∀ k : ℕ, τ ((k : E) + x) ≠ 0 := by
    intro k h0
    apply hx
    have := congrArg Complex.im h0
    simpa [hτk] using this
  let f : ℕ → ℂ := fun k => τ ((k : E) + x) / (‖τ ((k : E) + x)‖ : ℂ)
  have hinj : Function.Injective f := by
    intro k l hkl
    simp only [f] at hkl
    have hna : 0 < ‖τ ((k : E) + x)‖ := norm_pos_iff.mpr (hne k)
    have hnb : 0 < ‖τ ((l : E) + x)‖ := norm_pos_iff.mpr (hne l)
    have him := congrArg Complex.im hkl
    rw [Complex.div_ofReal_im, Complex.div_ofReal_im, hτk, hτk] at him
    simp only [Complex.add_im, Complex.natCast_im, zero_add] at him
    have hn : ‖τ ((k : E) + x)‖ = ‖τ ((l : E) + x)‖ := by
      first
        | exact (div_right_inj' hx).mp him
        | (field_simp at him; simpa [one_div] using him)
    rw [hn] at hkl
    have hab : τ ((k : E) + x) = τ ((l : E) + x) := by
      have hz : ((‖τ ((l : E) + x)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hnb.ne'
      exact (div_left_inj' hz).mp hkl
    rw [hτk, hτk] at hab
    have := congrArg Complex.re hab
    simp at this
    exact_mod_cast this
  by_contra hcon
  push_neg at hcon
  have hsub : Set.range f ⊆ ((Polynomial.nthRoots κ (1 : ℂ)).toFinset : Set ℂ) := by
    rintro _ ⟨k, rfl⟩
    simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hκ]
    exact hcon _ (fun h0 => hne k (by rw [h0, map_zero]))
  exact (Set.infinite_range_of_injective hinj) ((Finset.finite_toSet _).subset hsub)

end GlobalTheory.CMArg
