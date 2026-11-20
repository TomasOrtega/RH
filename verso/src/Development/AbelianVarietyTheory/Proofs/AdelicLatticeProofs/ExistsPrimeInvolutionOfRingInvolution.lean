import Mathlib

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory

/- English proof (translation)
Establish `hm : ∀ (I : Ideal R) (x : R), s x ∈ I.map s ↔ x ∈ I`. Introduce `I x`. Rewrite using `[Ideal.mem_map_of_equiv]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, h⟩`.

Rewrite using `[← s.injective h]` and apply the resulting hypothesis. Introduce `h`. Conclude with `⟨x, h, rfl⟩`. Set `f : HeightOneSpectrum R → HeightOneSpectrum R` to `fun P => { asIdeal := P.asIdeal.map s isPrime := by`. Use `P.isPrime` as an intermediate fact.

Conclude with `Ideal.map_isPrime_of_equiv s`. Use `ne_bot := by`. Introduce `h`. Apply `P.ne_bot` to reduce the goal to its premises. Rewrite using `[eq_bot_iff]`.

Introduce `x hx`. Establish `h1` using `(hm _ x).2 hx`. Rewrite `h1` using `[h, Ideal.mem_bot]`. Rewrite using `[Ideal.mem_bot]`. Conclude with `s.injective (by simpa using h1) }`.

Establish `hf : Function.Involutive f`. Introduce `P`. Use extensionality with `x`. Use `show x ∈ (P.asIdeal.map s).map s ↔ _`. Rewrite using `[← hm P.asIdeal x, ← hm _ (s x), hs]`.

Use `⟨hf.toPerm f, hf, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `P show Ideal.absNorm (P.asIdeal.map s) = _`. Simplify using `only [Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Conclude with `(Nat.card_congr (Ideal.quotientEquiv P.asIdeal (P.asIdeal.map s) s rfl).toEquiv).symm`. Introduce `P x`.

Conclude with `hm _ x`. Introduce `P x show s x ∈ (P.asIdeal.map s) ^ 2 ↔ _`. Rewrite using `[← Ideal.map_pow, hm]`.
-/
theorem exists_primeInvolution_of_ringInvolution {R : Type} [CommRing R] [IsDedekindDomain R]
    [Module.Free ℤ R] [Module.Finite ℤ R] (s : R ≃+* R) (hs : ∀ x, s (s x) = x) :
    ∃ c : HeightOneSpectrum R ≃ HeightOneSpectrum R, (∀ P, c (c P) = P) ∧
      (∀ P, Ideal.absNorm (c P).asIdeal = Ideal.absNorm P.asIdeal) ∧
      (∀ P x, s x ∈ (c P).asIdeal ↔ x ∈ P.asIdeal) ∧
      (∀ P x, s x ∈ (c P).asIdeal ^ 2 ↔ x ∈ P.asIdeal ^ 2) := by
  have hm : ∀ (I : Ideal R) (x : R), s x ∈ I.map s ↔ x ∈ I := by
    intro I x
    rw [Ideal.mem_map_of_equiv]
    constructor
    · rintro ⟨y, hy, h⟩
      rwa [← s.injective h]
    · intro h
      exact ⟨x, h, rfl⟩
  let f : HeightOneSpectrum R → HeightOneSpectrum R := fun P =>
    { asIdeal := P.asIdeal.map s
      isPrime := by
        have := P.isPrime
        exact Ideal.map_isPrime_of_equiv s
      ne_bot := by
        intro h
        apply P.ne_bot
        rw [eq_bot_iff]
        intro x hx
        have h1 := (hm _ x).2 hx
        rw [h, Ideal.mem_bot] at h1
        rw [Ideal.mem_bot]
        exact s.injective (by simpa using h1) }
  have hf : Function.Involutive f := by
    intro P
    ext x
    show x ∈ (P.asIdeal.map s).map s ↔ _
    rw [← hm P.asIdeal x, ← hm _ (s x), hs]
  refine ⟨hf.toPerm f, hf, ?_, ?_, ?_⟩
  · intro P
    show Ideal.absNorm (P.asIdeal.map s) = _
    simp only [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact (Nat.card_congr (Ideal.quotientEquiv P.asIdeal (P.asIdeal.map s) s rfl).toEquiv).symm
  · intro P x
    exact hm _ x
  · intro P x
    show s x ∈ (P.asIdeal.map s) ^ 2 ↔ _
    rw [← Ideal.map_pow, hm]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ _ hE h2 hσ`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `hinv : ∀ x, σ (σ x) = x`. Introduce `x`. Apply `τ.injective` to reduce the goal to its premises.

Rewrite using `[hσ, hσ, star_star]`. Establish `hfix : ∀ x, σ x = x → ∃ a : F, algebraMap F E a = x`. Introduce `x hx`. Use `Subalgebra.isSimpleOrder_of_finrank h2` as an intermediate fact. Break down `eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h | h` into its components or cases.

Establish `hx' : x ∈ AlgHom.equalizer σ (AlgHom.id F E)` using `hx`. Rewrite `hx'` using `[h]`. Conclude with `hx'`. It suffices to derive a contradiction. Apply `IsTotallyComplex.complexEmbedding_not_isReal τ` to reduce the goal to its premises.

Rewrite using `[ComplexEmbedding.isReal_iff]`. Use extensionality with `y`. Establish `hy : y ∈ AlgHom.equalizer σ (AlgHom.id F E)` using `by rw [h]; trivial`. Establish `hy' : σ y = y` using `hy`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`.

Use `hσ τ y` as an intermediate fact. Rewrite `this` using `[hy']`. Conclude with `this.symm`. Set `e : E ≃+* E` to `{ toFun := σ, invFun := σ, left_inv := hinv, right_inv := hinv, map_mul' := map_mul σ, map_add' := map_add σ }`. Set `s : 𝓞 E ≃+* 𝓞 E` to `RingOfIntegers.mapRingEquiv e`.

Establish `hs : ∀ x : 𝓞 E, ((s x : 𝓞 E) : E) = σ x` using `fun x => rfl`. Establish `hss : ∀ x, s (s x) = x`. Introduce `x`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[hs, hs, hinv]`.

Establish `hsF : ∀ a : 𝓞 F, s (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap (𝓞 F) (𝓞 E) a`. Introduce `a`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[hs]`. Conclude with `σ.commutes (a : F)`.

Take `⟨c, hc1, hc2, hc3, hc4⟩` from `exists_primeInvolution_of_ringInvolution s hss`. Use `⟨hinv, c, hc1, hc2, fun x => ⟨s x, hs x⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `P x y hy`. Establish `: y = s x` using `RingOfIntegers.ext (by rw [hy, hs])`. Substitute `this` using the available equality.

Conclude with `⟨hc3 P x, hc4 P x⟩`. Introduce `P Q`. Establish `hu : ∀ (P : HeightOneSpectrum (𝓞 E)) (a : 𝓞 F), a ∈ (P.under (𝓞 F)).asIdeal ↔ algebraMap (𝓞 F) (𝓞 E) a ∈ P.asIdeal` using `fun P a => Iff.rfl`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Establish `hnot : ¬ ((Q.asIdeal : Set (𝓞 E)) ⊆ P.asIdeal ∪ (c P).asIdeal)`. Rewrite using `[Ideal.subset_union]`. Introduce and unpack `(h' | h')`.

Conclude with `hne.1 (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h'))`. Conclude with `hne.2 (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le (c P).isPrime.ne_top h'))`. Rewrite `hnot` using `[Set.not_subset]`. Take `⟨x, hxQ, hx⟩` from `hnot`. Simplify using `only [Set.mem_union, SetLike.mem_coe, not_or] at hx hxQ`.

Take `⟨a, ha⟩` from `hfix ((x * s x : 𝓞 E) : E) (by`. Rewrite using `[← hs, map_mul, hss, mul_comm])`. Establish `hai : IsIntegral ℤ a`. Establish `h1 : IsIntegral ℤ (algebraMap F E a)`. Rewrite using `[ha]`.

Conclude with `RingOfIntegers.isIntegral_coe _`. Conclude with `(isIntegral_algebraMap_iff (algebraMap F E).injective).1 h1`. Take `⟨b, hb⟩ : ∃ b : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) b = x * s x` from `⟨⟨a, hai⟩, RingOfIntegers.ext ha⟩`. Establish `h1 : b ∈ (Q.under (𝓞 F)).asIdeal`. Rewrite using `[hu, hb]`.

Conclude with `Ideal.mul_mem_right _ _ hxQ`. Rewrite `h1` using `[← h, hu, hb]`. Break down `P.isPrime.mem_or_mem h1 with h3 | h3` into its components or cases. Conclude with `hx.1 h3`. Apply `hx.2` to reduce the goal to its premises.

Use `(hc3 P _).2 h3` as an intermediate fact. Rewrite `this` using `[hss]`. Then use the resulting hypothesis. Introduce and unpack `(rfl | rfl)`. Both sides reduce to the same expression. Use extensionality with `a`.

Rewrite using `[hu, hu, ← hc3 P, hsF]`.
-/
theorem cmConjugation_on_primes : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsTotallyReal F → IsTotallyComplex E → Module.finrank F E = 2 → (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) → (∀ x, σ (σ x) = x) ∧ ∃ c : HeightOneSpectrum (𝓞 E) ≃ HeightOneSpectrum (𝓞 E), (∀ P, c (c P) = P) ∧ (∀ P, Ideal.absNorm (c P).asIdeal = Ideal.absNorm P.asIdeal) ∧ (∀ x : 𝓞 E, ∃ y : 𝓞 E, (y : E) = σ x) ∧ (∀ P (x y : 𝓞 E), (y : E) = σ x → (y ∈ (c P).asIdeal ↔ x ∈ P.asIdeal) ∧ (y ∈ (c P).asIdeal ^ 2 ↔ x ∈ P.asIdeal ^ 2)) ∧ ∀ P Q : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = Q.under (𝓞 F) ↔ Q = P ∨ Q = c P := by
  intro F E _ _ _ _ _ σ _ hE h2 hσ
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    apply τ.injective
    rw [hσ, hσ, star_star]
  have hfix : ∀ x, σ x = x → ∃ a : F, algebraMap F E a = x := by
    intro x hx
    have := Subalgebra.isSimpleOrder_of_finrank h2
    rcases eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h | h
    · have hx' : x ∈ AlgHom.equalizer σ (AlgHom.id F E) := hx
      rw [h] at hx'
      exact hx'
    · exfalso
      apply IsTotallyComplex.complexEmbedding_not_isReal τ
      rw [ComplexEmbedding.isReal_iff]
      ext y
      have hy : y ∈ AlgHom.equalizer σ (AlgHom.id F E) := by rw [h]; trivial
      have hy' : σ y = y := hy
      rw [ComplexEmbedding.conjugate_coe_eq]
      have := hσ τ y
      rw [hy'] at this
      exact this.symm
  let e : E ≃+* E :=
    { toFun := σ, invFun := σ, left_inv := hinv, right_inv := hinv,
      map_mul' := map_mul σ, map_add' := map_add σ }
  let s : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv e
  have hs : ∀ x : 𝓞 E, ((s x : 𝓞 E) : E) = σ x := fun x => rfl
  have hss : ∀ x, s (s x) = x := by
    intro x
    apply RingOfIntegers.ext
    rw [hs, hs, hinv]
  have hsF : ∀ a : 𝓞 F, s (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap (𝓞 F) (𝓞 E) a := by
    intro a
    apply RingOfIntegers.ext
    rw [hs]
    exact σ.commutes (a : F)
  obtain ⟨c, hc1, hc2, hc3, hc4⟩ := exists_primeInvolution_of_ringInvolution s hss
  refine ⟨hinv, c, hc1, hc2, fun x => ⟨s x, hs x⟩, ?_, ?_⟩
  · intro P x y hy
    have : y = s x := RingOfIntegers.ext (by rw [hy, hs])
    subst this
    exact ⟨hc3 P x, hc4 P x⟩
  · intro P Q
    have hu : ∀ (P : HeightOneSpectrum (𝓞 E)) (a : 𝓞 F),
        a ∈ (P.under (𝓞 F)).asIdeal ↔ algebraMap (𝓞 F) (𝓞 E) a ∈ P.asIdeal := fun P a => Iff.rfl
    constructor
    · intro h
      by_contra hne
      push Not at hne
      have hnot : ¬ ((Q.asIdeal : Set (𝓞 E)) ⊆ P.asIdeal ∪ (c P).asIdeal) := by
        rw [Ideal.subset_union]
        rintro (h' | h')
        · exact hne.1 (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h'))
        · exact hne.2 (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le (c P).isPrime.ne_top h'))
      rw [Set.not_subset] at hnot
      obtain ⟨x, hxQ, hx⟩ := hnot
      simp only [Set.mem_union, SetLike.mem_coe, not_or] at hx hxQ
      obtain ⟨a, ha⟩ := hfix ((x * s x : 𝓞 E) : E) (by
        rw [← hs, map_mul, hss, mul_comm])
      have hai : IsIntegral ℤ a := by
        have h1 : IsIntegral ℤ (algebraMap F E a) := by
          rw [ha]; exact RingOfIntegers.isIntegral_coe _
        exact (isIntegral_algebraMap_iff (algebraMap F E).injective).1 h1
      obtain ⟨b, hb⟩ : ∃ b : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) b = x * s x :=
        ⟨⟨a, hai⟩, RingOfIntegers.ext ha⟩
      have h1 : b ∈ (Q.under (𝓞 F)).asIdeal := by
        rw [hu, hb]; exact Ideal.mul_mem_right _ _ hxQ
      rw [← h, hu, hb] at h1
      rcases P.isPrime.mem_or_mem h1 with h3 | h3
      · exact hx.1 h3
      · apply hx.2
        have := (hc3 P _).2 h3
        rwa [hss] at this
    · rintro (rfl | rfl)
      · rfl
      · ext a
        rw [hu, hu, ← hc3 P, hsF]

end GlobalTheory
