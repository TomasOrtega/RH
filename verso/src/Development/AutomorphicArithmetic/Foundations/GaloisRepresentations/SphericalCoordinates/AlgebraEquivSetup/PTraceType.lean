import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Use `show τ ((A.bar A.ω : 𝓞 E) : E) = _`. Rewrite using `[A.bar_eq, IsCMField.complexEmbedding_complexConj]`.
-/
private theorem tau_bar (A : Arith E) (τ : E →+* ℂ) :
    τ ((algebraMap (𝓞 E) E) (A.bar A.ω)) = (starRingEnd ℂ) (τ (A.ω : E)) := by
  show τ ((A.bar A.ω : 𝓞 E) : E) = _
  rw [A.bar_eq, IsCMField.complexEmbedding_complexConj]

/- English proof (translation)
Establish `h1` using `congrArg (fun x : 𝓞 E => τ (x : E)) A.tr_eq`. Simplify using `only [map_add, map_intCast] at h1`. Rewrite `h1` using `[tau_bar A τ]`. Conclude with `h1`.
-/
private theorem tau_add (A : Arith E) (τ : E →+* ℂ) :
    τ (A.ω : E) + (starRingEnd ℂ) (τ (A.ω : E)) = (A.tr : ℂ) := by
  have h1 := congrArg (fun x : 𝓞 E => τ (x : E)) A.tr_eq
  simp only [map_add, map_intCast] at h1
  rw [tau_bar A τ] at h1
  exact h1

/- English proof (translation)
Establish `h1` using `congrArg (fun x : 𝓞 E => τ (x : E)) A.nm_eq`. Simplify using `only [map_mul, map_intCast] at h1`. Rewrite `h1` using `[tau_bar A τ]`. Conclude with `h1`.
-/
private theorem tau_mul (A : Arith E) (τ : E →+* ℂ) :
    τ (A.ω : E) * (starRingEnd ℂ) (τ (A.ω : E)) = (A.nm : ℂ) := by
  have h1 := congrArg (fun x : 𝓞 E => τ (x : E)) A.nm_eq
  simp only [map_mul, map_intCast] at h1
  rw [tau_bar A τ] at h1
  exact h1

/- English proof (translation)
Introduce `h`. Establish `hc : (starRingEnd ℂ) (τ (A.ω : E)) = τ (A.ω : E)` using `Complex.conj_eq_iff_im.2 h`. Establish `h1` using `tau_add A τ`. Establish `h2` using `tau_mul A τ`. Rewrite `h1`, `h2` using `[hc]`.

Establish `h3 : ((A.tr ^ 2 - 4 * A.nm : ℤ) : ℂ) = 0`. Use `push_cast`. Rewrite using `[← h1, ← h2]`. Expand and normalize the polynomial expressions, which then agree. Establish `h4 : A.tr ^ 2 - 4 * A.nm = 0` using `by exact_mod_cast h3`.

Use `A.disc_neg` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem tau_im (A : Arith E) (τ : E →+* ℂ) : (τ (A.ω : E)).im ≠ 0 := by
  intro h
  have hc : (starRingEnd ℂ) (τ (A.ω : E)) = τ (A.ω : E) := Complex.conj_eq_iff_im.2 h
  have h1 := tau_add A τ
  have h2 := tau_mul A τ
  rw [hc] at h1 h2
  have h3 : ((A.tr ^ 2 - 4 * A.nm : ℤ) : ℂ) = 0 := by
    push_cast
    rw [← h1, ← h2]
    ring
  have h4 : A.tr ^ 2 - 4 * A.nm = 0 := by exact_mod_cast h3
  have := A.disc_neg
  linarith

/- English proof (translation)
Establish `h : (τ (A.ω : E) - A.τ₀ (A.ω : E)) * (τ (A.ω : E) - (starRingEnd ℂ) (A.τ₀ (A.ω : E))) = 0`. Take the linear combination `τ (A.ω : E) * tau_add A τ - tau_mul A τ - τ (A.ω : E) * tau_add A A.τ₀ + tau_mul A A.τ₀`. Break down `mul_eq_zero.1 h with h | h` into its components or cases. Conclude with `Or.inl (sub_eq_zero.1 h)`. Conclude with `Or.inr (sub_eq_zero.1 h)`.
-/
private theorem tau_cases (A : Arith E) (τ : E →+* ℂ) :
    τ (A.ω : E) = A.τ₀ (A.ω : E) ∨ τ (A.ω : E) = (starRingEnd ℂ) (A.τ₀ (A.ω : E)) := by
  have h : (τ (A.ω : E) - A.τ₀ (A.ω : E)) * (τ (A.ω : E) - (starRingEnd ℂ) (A.τ₀ (A.ω : E))) = 0 := by
    linear_combination τ (A.ω : E) * tau_add A τ - tau_mul A τ - τ (A.ω : E) * tau_add A A.τ₀ + tau_mul A A.τ₀
  rcases mul_eq_zero.1 h with h | h
  · exact Or.inl (sub_eq_zero.1 h)
  · exact Or.inr (sub_eq_zero.1 h)

/- English proof (translation)
Introduce `h` and use `tau_im A A.τ₀ (Complex.conj_eq_iff_im.1 h.symm)`.
-/
private theorem rho_ne (A : Arith E) : A.τ₀ (A.ω : E) ≠ (starRingEnd ℂ) (A.τ₀ (A.ω : E)) :=
  fun h => tau_im A A.τ₀ (Complex.conj_eq_iff_im.1 h.symm)

/- English proof (translation)
The claim follows from `ComplexEmbedding.conjugate_coe_eq τ _`.
-/
private theorem conj_mem (A : Arith E) (τ : E →+* ℂ) :
    (ComplexEmbedding.conjugate τ) (A.ω : E) = (starRingEnd ℂ) (τ (A.ω : E)) :=
  ComplexEmbedding.conjugate_coe_eq τ _

/- English proof (translation)
Use `Eq.trans ?_ (Finset.sum_subtype (Finset.univ.filter (fun τ : E →+* ℂ => τ (A.ω : E) = A.τ₀ (A.ω : E))) (by simp) (fun τ => f (ComplexEmbedding.conjugate τ)))` and prove the remaining obligations. Use `Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `τ hτ`. Establish `hτ'` using `(Finset.mem_filter.1 hτ).2`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`.

Rewrite using `[conj_mem, hτ', Complex.conj_conj]`. Introduce `τ hτ`. Establish `hτ'` using `(Finset.mem_filter.1 hτ).2`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Rewrite using `[conj_mem, hτ']`.

Introduce `τ _`. Conclude with `star_star τ`. Introduce `τ _`. Conclude with `star_star τ`. Introduce `τ _`.

Rewrite using `[show ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ from star_star τ]`.
-/
private theorem sum_conj (A : Arith E) [Fintype (Phi A)]
    [DecidablePred fun τ : E →+* ℂ => τ (A.ω : E) = (starRingEnd ℂ) (A.τ₀ (A.ω : E))]
    (f : (E →+* ℂ) → ℂ) :
    ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (A.ω : E) = (starRingEnd ℂ) (A.τ₀ (A.ω : E))), f τ =
      ∑ τ : Phi A, f (ComplexEmbedding.conjugate τ.1) := by
  classical
  refine Eq.trans ?_ (Finset.sum_subtype
    (Finset.univ.filter (fun τ : E →+* ℂ => τ (A.ω : E) = A.τ₀ (A.ω : E))) (by simp)
    (fun τ => f (ComplexEmbedding.conjugate τ)))
  refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
  · intro τ hτ
    have hτ' := (Finset.mem_filter.1 hτ).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [conj_mem, hτ', Complex.conj_conj]
  · intro τ hτ
    have hτ' := (Finset.mem_filter.1 hτ).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [conj_mem, hτ']
  · intro τ _
    exact star_star τ
  · intro τ _
    exact star_star τ
  · intro τ _
    rw [show ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ from star_star τ]

/- English proof (translation)
Establish `h` using `trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := x)`. Rewrite `h` using `[eq_ratCast]`. Rewrite using `[h]`. Conclude with `Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun σ => rfl)`.
-/
private theorem trace_eq (x : E) :
    (((Algebra.trace ℚ E x : ℚ) : ℂ)) = ∑ τ : E →+* ℂ, τ x := by
  have h := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := x)
  rw [eq_ratCast] at h
  rw [h]
  exact Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun σ => rfl)

end UpperTheory.Gal.W2.Seed

open Classical in
/- English proof (translation)
Introduce `E _ _ _ A`. Establish `h2` using `fun f => sum_conj A f`. Use `⟨fun x => ?_, h2, fun v => ?_, tau_im A A.τ₀⟩` and prove the remaining obligations. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Establish `h1 : ((((Algebra.trace ℚ E x : ℚ) : ℝ)) : ℂ) = ((Algebra.trace ℚ E x : ℚ) : ℂ)` using `by push_cast; rfl`.

Rewrite using `[h1, trace_eq x, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun τ : E →+* ℂ => τ (A.ω : E) = A.τ₀ (A.ω : E))]`. Establish `h3 : Finset.univ.filter (fun τ : E →+* ℂ => ¬ τ (A.ω : E) = A.τ₀ (A.ω : E)) = Finset.univ.filter (fun τ : E →+* ℂ => τ (A.ω : E) = (starRingEnd ℂ) (A.τ₀ (A.ω : E)))`. Use extensionality with `τ`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `(tau_cases A τ).resolve_left h`. Introduce `h h'`. Conclude with `rho_ne A (h'.symm.trans h)`. Establish `h4 : ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (A.ω : E) = A.τ₀ (A.ω : E)), τ x = ∑ τ : Phi A, τ.1 x` using `Finset.sum_subtype _ (by simp) _`.

Rewrite using `[h3, h2 (fun τ => τ x), h4, ← Finset.sum_add_distrib, Complex.ofReal_sum]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[ComplexEmbedding.conjugate_coe_eq, Complex.add_conj]`. Establish `hmem : ∃ τ : Phi A, InfinitePlace.mk τ.1 = v`. Break down `tau_cases A v.embedding with h | h` into its components or cases.

Conclude with `⟨⟨v.embedding, h⟩, v.mk_embedding⟩`. Use `⟨⟨ComplexEmbedding.conjugate v.embedding, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[conj_mem, h, Complex.conj_conj]`. Rewrite using `[InfinitePlace.mk_conjugate_eq, v.mk_embedding]`. Take `⟨τ, hτ⟩` from `hmem`.

Use `⟨τ, hτ, fun σ hσ => ?_⟩` and prove the remaining obligations. Break down `InfinitePlace.mk_eq_iff.1 (hσ.trans hτ.symm) with h | h` into its components or cases. Conclude with `Subtype.ext h`. It suffices to derive a contradiction. Establish `h5 : τ.1 (A.ω : E) = (starRingEnd ℂ) (σ.1 (A.ω : E))` using `by rw [← h, conj_mem]`.

Rewrite `h5` using `[τ.2, σ.2]`. Conclude with `rho_ne A h5`.
-/
theorem UpperTheory.Gal.W2.Seed.pTraceType :
    TraceType := by
  intro E _ _ _ A
  have h2 := fun f => sum_conj A f
  refine ⟨fun x => ?_, h2, fun v => ?_, tau_im A A.τ₀⟩
  · apply Complex.ofReal_injective
    have h1 : ((((Algebra.trace ℚ E x : ℚ) : ℝ)) : ℂ) = ((Algebra.trace ℚ E x : ℚ) : ℂ) := by push_cast; rfl
    rw [h1, trace_eq x,
      ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun τ : E →+* ℂ => τ (A.ω : E) = A.τ₀ (A.ω : E))]
    have h3 : Finset.univ.filter (fun τ : E →+* ℂ => ¬ τ (A.ω : E) = A.τ₀ (A.ω : E)) =
        Finset.univ.filter (fun τ : E →+* ℂ => τ (A.ω : E) = (starRingEnd ℂ) (A.τ₀ (A.ω : E))) := by
      ext τ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        exact (tau_cases A τ).resolve_left h
      · intro h h'
        exact rho_ne A (h'.symm.trans h)
    have h4 : ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (A.ω : E) = A.τ₀ (A.ω : E)), τ x =
        ∑ τ : Phi A, τ.1 x := Finset.sum_subtype _ (by simp) _
    rw [h3, h2 (fun τ => τ x), h4, ← Finset.sum_add_distrib, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [ComplexEmbedding.conjugate_coe_eq, Complex.add_conj]
  · have hmem : ∃ τ : Phi A, InfinitePlace.mk τ.1 = v := by
      rcases tau_cases A v.embedding with h | h
      · exact ⟨⟨v.embedding, h⟩, v.mk_embedding⟩
      · refine ⟨⟨ComplexEmbedding.conjugate v.embedding, ?_⟩, ?_⟩
        · rw [conj_mem, h, Complex.conj_conj]
        · rw [InfinitePlace.mk_conjugate_eq, v.mk_embedding]
    obtain ⟨τ, hτ⟩ := hmem
    refine ⟨τ, hτ, fun σ hσ => ?_⟩
    rcases InfinitePlace.mk_eq_iff.1 (hσ.trans hτ.symm) with h | h
    · exact Subtype.ext h
    · exfalso
      have h5 : τ.1 (A.ω : E) = (starRingEnd ℂ) (σ.1 (A.ω : E)) := by rw [← h, conj_mem]
      rw [τ.2, σ.2] at h5
      exact rho_ne A h5
