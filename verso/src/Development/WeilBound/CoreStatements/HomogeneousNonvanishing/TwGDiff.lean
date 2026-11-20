import Mathlib
open NumberField TensorProduct

namespace PositivityTheory.UnitarySelfGeneration

/- English proof (translation)
Take `⟨t, ht1, ht2⟩` from `(Algebra.FormallyUnramified.iff_exists_tensorProduct (R := A) (S := B)).1 inferInstance`. Set `φ : B ⊗[A] B →ₐ[A] B` to `Algebra.TensorProduct.lift (AlgHom.id A B) σ fun _ _ => Commute.all _ _`. Take `⟨s, hs⟩` from `hσ`. Establish `h0 : φ t = 0`. Use `congrArg φ (ht1 s)` as an intermediate fact.

Rewrite `this` using `[map_mul, map_zero, map_sub]`. Simplify using `only [φ, Algebra.TensorProduct.lift_tmul, map_one, AlgHom.id_apply, one_mul, mul_one] at this`. Conclude with `(mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hs)`. Establish `h1 : ∀ u : B ⊗[A] B, Algebra.TensorProduct.lmul' A u - φ u ∈ Ideal.span (Set.range fun x : B => x - σ x)`. Introduce `u`.

Proceed by induction on `u using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b`. Simplify using `only [φ, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, Algebra.TensorProduct.lmul'_apply_tmul]`. Rewrite using `[← mul_sub]`.

Conclude with `Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨b, rfl⟩)`. Consider the case `add x y hx hy`. Rewrite using `[map_add, map_add, add_sub_add_comm]`. Conclude with `add_mem hx hy`. Use `h1 t` as an intermediate fact.

Rewrite `this` using `[ht2, h0, sub_zero]`. Conclude with `(Ideal.eq_top_iff_one _).2 this`.
-/
theorem differentiable_schwartz_translate {A B : Type} [CommRing A] [CommRing B] [IsDomain B] [Algebra A B] [Algebra.Unramified A B]
    (σ : B →ₐ[A] B) (hσ : ∃ s, σ s ≠ s) : Ideal.span (Set.range fun x : B => x - σ x) = ⊤ := by
  obtain ⟨t, ht1, ht2⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := A) (S := B)).1 inferInstance
  let φ : B ⊗[A] B →ₐ[A] B := Algebra.TensorProduct.lift (AlgHom.id A B) σ fun _ _ => Commute.all _ _
  obtain ⟨s, hs⟩ := hσ
  have h0 : φ t = 0 := by
    have := congrArg φ (ht1 s)
    rw [map_mul, map_zero, map_sub] at this
    simp only [φ, Algebra.TensorProduct.lift_tmul, map_one, AlgHom.id_apply, one_mul, mul_one] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hs)
  have h1 : ∀ u : B ⊗[A] B, Algebra.TensorProduct.lmul' A u - φ u ∈
      Ideal.span (Set.range fun x : B => x - σ x) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simp only [φ, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, Algebra.TensorProduct.lmul'_apply_tmul]
      rw [← mul_sub]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨b, rfl⟩)
    | add x y hx hy =>
      rw [map_add, map_add, add_sub_add_comm]
      exact add_mem hx hy
  have := h1 t
  rw [ht2, h0, sub_zero] at this
  exact (Ideal.eq_top_iff_one _).2 this

/- English proof (translation)
Introduce `E _ _ _ bar hbar hun`. Set `σ : 𝓞 E →ₐ[𝓞 (maximalRealSubfield E)] 𝓞 E` to `{ bar.toRingHom with commutes' := fun r => by`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Use `show ((bar _ : 𝓞 E) : E) = _`. Rewrite using `[hbar]`.

Conclude with `IsCMField.complexConj_apply_eq_self E (r : maximalRealSubfield E) }`. Use `differentiable_schwartz_translate σ ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Apply `IsCMField.complexConj_ne_one E` to reduce the goal to its premises.

Use extensionality with `x`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 E) x`. Establish `h : ∀ a : 𝓞 E, IsCMField.complexConj E (algebraMap (𝓞 E) E a) = algebraMap (𝓞 E) E a` using `fun a => by`. Establish `h1 : bar a = a` using `hne a`. Use `hbar a` as an intermediate fact.

Rewrite `this` using `[h1]`. Conclude with `this.symm`. Rewrite using `[map_div₀, h, h]`. Both sides reduce to the same expression.
-/
theorem tw_g_diff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E), (∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → Ideal.span (Set.range fun x : 𝓞 E => x - bar x) = ⊤ := by
  intro E _ _ _ bar hbar hun
  let σ : 𝓞 E →ₐ[𝓞 (maximalRealSubfield E)] 𝓞 E :=
    { bar.toRingHom with
      commutes' := fun r => by
        apply RingOfIntegers.ext
        show ((bar _ : 𝓞 E) : E) = _
        rw [hbar]
        exact IsCMField.complexConj_apply_eq_self E (r : maximalRealSubfield E) }
  refine differentiable_schwartz_translate σ ?_
  by_contra hne
  push Not at hne
  apply IsCMField.complexConj_ne_one E
  ext x
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  have h : ∀ a : 𝓞 E, IsCMField.complexConj E (algebraMap (𝓞 E) E a) = algebraMap (𝓞 E) E a := fun a => by
    have h1 : bar a = a := hne a
    have := hbar a
    rw [h1] at this
    exact this.symm
  rw [map_div₀, h, h]; rfl

end PositivityTheory.UnitarySelfGeneration
