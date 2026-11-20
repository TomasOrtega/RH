import Mathlib
import Formalism.LocalToGlobal.Columns.ScaledRamifiedLattice
open NumberField IsDedekindDomain Formalism.L2.Col

namespace GlobalTheory

/- English proof (translation)
Establish `hmax : (Ideal.span {(p : ℤ)}).IsMaximal`. Establish `: Fact p.Prime` using `⟨hp⟩`. Conclude with `Int.ideal_span_isMaximal_of_prime p`. Use `⟨hmax.eq_of_le (Ideal.comap_ne_top _ P.isPrime.ne_top) ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]`.

Conclude with `h`.
-/
theorem liesOver_span_of_natCast_mem_heightOne {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    (P : HeightOneSpectrum (𝓞 E)) (h : ((p : ℕ) : 𝓞 E) ∈ P.asIdeal) :
    P.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := by
    have : Fact p.Prime := ⟨hp⟩
    exact Int.ideal_span_isMaximal_of_prime p
  refine ⟨hmax.eq_of_le (Ideal.comap_ne_top _ P.isPrime.ne_top) ?_⟩
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
  exact h

/- English proof (translation)
Introduce `X hX p hp w P hw hP`. Use `hX.galE` as an intermediate fact. Take `⟨τ₀⟩ : Nonempty X.Tau` from `Fintype.card_pos_iff.1 hX.ok.f_pos`. Establish `h0 : ((p : ℕ) : 𝓞 X.E) ∈ (pullW τ₀ w).asIdeal`. Express the relevant statement in the definitionally equal form `((p : ℕ) : 𝓞 X.E) ∈ w.asIdeal.comap (X.embO τ₀)`.

Rewrite using `[Ideal.mem_comap, map_natCast]`. Conclude with `hw`. Take `⟨g, hg⟩` from `Ideal.exists_comap_galRestrict_eq ℤ ℚ X.E (𝓞 X.E) (p := Ideal.span {(p : ℤ)}) (P₁ := (pullW τ₀ w).asIdeal) (P₂ := P.asIdeal) ⟨(pullW τ₀ w).isPrime, liesOver_span_of_natCast_mem_heightOne hp _ h0⟩ ⟨P.isPrime, liesOver_span_of_natCast_mem_heightOne hp _ hP⟩`. Establish `key : ∀ x : 𝓞 X.E, x ∈ P.asIdeal ↔ X.embO τ₀ (galRestrict ℤ ℚ X.E (𝓞 X.E) g x) ∈ w.asIdeal`. Introduce `x`.

Rewrite using `[← hg]`. Both sides reduce to the same expression. Establish `hc : ∀ x : 𝓞 X.E, ((X.embO τ₀ (galRestrict ℤ ℚ X.E (𝓞 X.E) g x) : 𝓞 X.K) : X.K) = X.emb τ₀ (g (x : X.E))`. Introduce `x`. Conclude with `congrArg (X.emb τ₀) (algebraMap_galRestrict_apply ℤ g x)`.

Take `⟨τ, hτ | hτ⟩` from `hX.ok.emb_all ((X.emb τ₀).comp (g : X.E →+* X.E))`. Use `⟨τ, Or.inl ?_⟩` and prove the remaining obligations. Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Use extensionality with `x`. Rewrite using `[key]`.

Establish `: X.embO τ₀ (galRestrict ℤ ℚ X.E (𝓞 X.E) g x) = X.embO τ x`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[hc]`. Conclude with `RingHom.congr_fun hτ (x : X.E)`. Rewrite using `[this]`.

Both sides reduce to the same expression. Use `⟨τ, Or.inr ?_⟩` and prove the remaining obligations. Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Use extensionality with `x`. Rewrite using `[mem_conjP, key]`.

Establish `: X.embO τ₀ (galRestrict ℤ ℚ X.E (𝓞 X.E) g (cO X.E x)) = X.embO τ (cO X.E (cO X.E x))`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[hc]`. Conclude with `RingHom.congr_fun hτ ((cO X.E x : 𝓞 X.E) : X.E)`. Rewrite using `[this, cO_cO]`.

Both sides reduce to the same expression.
-/
theorem exists_comap_eq_or_eq_conj :
    ∀ (X : Fields), X.AbelianUnramifiedExtensionConditions → ∀ (p : ℕ), p.Prime → ∀ (w : HeightOneSpectrum (𝓞 X.K)) (P : HeightOneSpectrum (𝓞 X.E)),
      ((p : ℕ) : 𝓞 X.K) ∈ w.asIdeal → ((p : ℕ) : 𝓞 X.E) ∈ P.asIdeal → ∃ τ : X.Tau, SeesP w τ P ∨ SeesPbar w τ P := by
  intro X hX p hp w P hw hP
  have := hX.galE
  obtain ⟨τ₀⟩ : Nonempty X.Tau := Fintype.card_pos_iff.1 hX.ok.f_pos
  have h0 : ((p : ℕ) : 𝓞 X.E) ∈ (pullW τ₀ w).asIdeal := by
    change ((p : ℕ) : 𝓞 X.E) ∈ w.asIdeal.comap (X.embO τ₀)
    rw [Ideal.mem_comap, map_natCast]
    exact hw
  obtain ⟨g, hg⟩ := Ideal.exists_comap_galRestrict_eq ℤ ℚ X.E (𝓞 X.E) (p := Ideal.span {(p : ℤ)})
    (P₁ := (pullW τ₀ w).asIdeal) (P₂ := P.asIdeal)
    ⟨(pullW τ₀ w).isPrime, liesOver_span_of_natCast_mem_heightOne hp _ h0⟩
    ⟨P.isPrime, liesOver_span_of_natCast_mem_heightOne hp _ hP⟩
  have key : ∀ x : 𝓞 X.E, x ∈ P.asIdeal ↔ X.embO τ₀ (galRestrict ℤ ℚ X.E (𝓞 X.E) g x) ∈ w.asIdeal := by
    intro x
    rw [← hg]
    rfl
  have hc : ∀ x : 𝓞 X.E, ((X.embO τ₀ (galRestrict ℤ ℚ X.E (𝓞 X.E) g x) : 𝓞 X.K) : X.K) = X.emb τ₀ (g (x : X.E)) := by
    intro x
    exact congrArg (X.emb τ₀) (algebraMap_galRestrict_apply ℤ g x)
  obtain ⟨τ, hτ | hτ⟩ := hX.ok.emb_all ((X.emb τ₀).comp (g : X.E →+* X.E))
  · refine ⟨τ, Or.inl ?_⟩
    apply HeightOneSpectrum.ext
    ext x
    rw [key]
    have : X.embO τ₀ (galRestrict ℤ ℚ X.E (𝓞 X.E) g x) = X.embO τ x := by
      apply RingOfIntegers.ext
      rw [hc]
      exact RingHom.congr_fun hτ (x : X.E)
    rw [this]
    rfl
  · refine ⟨τ, Or.inr ?_⟩
    apply HeightOneSpectrum.ext
    ext x
    rw [mem_conjP, key]
    have : X.embO τ₀ (galRestrict ℤ ℚ X.E (𝓞 X.E) g (cO X.E x)) = X.embO τ (cO X.E (cO X.E x)) := by
      apply RingOfIntegers.ext
      rw [hc]
      exact RingHom.congr_fun hτ ((cO X.E x : 𝓞 X.E) : X.E)
    rw [this, cO_cO]
    rfl

end GlobalTheory
