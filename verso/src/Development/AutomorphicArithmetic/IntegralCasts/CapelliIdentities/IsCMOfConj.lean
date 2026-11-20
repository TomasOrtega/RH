import Mathlib

/- English proof (translation)
Introduce `K _ _ _ h`. Use `choose c hc using h`. Set `φ₀ : K →+* ℂ` to `Classical.choice (inferInstance : Nonempty _)`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x : K, starRingEnd ℂ (φ₀ x) ≠ φ₀ x := by`. Assume the negation of the conclusion as `hne`.

Apply `NumberField.IsTotallyComplex.complexEmbedding_not_isReal φ₀` to reduce the goal to its premises. Rewrite using `[NumberField.ComplexEmbedding.isReal_iff]`. Use extensionality with `z`. Rewrite using `[NumberField.ComplexEmbedding.conjugate_coe_eq]`. Assume the negation of the conclusion as `hz`.

Conclude with `hne ⟨z, hz⟩`. Establish `hanti : ∀ (z : K) (φ : K →+* ℂ), starRingEnd ℂ (φ (z - c z)) = -φ (z - c z)`. Introduce `z φ`. Simplify using `[hc]`. Choose the witnesses or unpack the hypotheses as in `⟨d, hd0, hd⟩ : ∃ d : K, d ≠ 0 ∧ ∀ φ : K →+* ℂ, starRingEnd ℂ (φ d) = -φ d := by`.

Use `⟨x - c x, fun h0 => hx ?_, hanti x⟩` and prove the remaining obligations. Rewrite using `[← hc, ← sub_eq_zero.mp h0]`. Establish `hli : LinearIndependent (NumberField.maximalRealSubfield K) ![(1 : K), d]`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce and unpack `⟨s, hs⟩ ⟨t, ht⟩ hst`.

Establish `h1 : s * 1 + t * d = 0` using `hst`. Establish `h2` using `congrArg φ₀ h1`. Establish `h3` using `congrArg (starRingEnd ℂ) h2`. Establish `hs' : starRingEnd ℂ (φ₀ s) = φ₀ s` using `hs φ₀`. Establish `ht' : starRingEnd ℂ (φ₀ t) = φ₀ t` using `ht φ₀`.

Simplify using `only [map_add, map_mul, map_one, map_zero, hs', ht', hd] at h2 h3`. Establish `hs0 : s = 0`. Apply `φ₀.injective` to reduce the goal to its premises. Rewrite using `[map_zero]`. Take the linear combination `(h2 + h3) / 2`.

Establish `ht0 : t = 0`. Rewrite `h1` using `[hs0, zero_mul, zero_add]`. Conclude with `(mul_eq_zero.mp h1).resolve_right hd0`. Conclude with `⟨Subtype.ext hs0, Subtype.ext ht0⟩`. Establish `hsp : ⊤ ≤ Submodule.span (NumberField.maximalRealSubfield K) (Set.range ![(1 : K), d])`.

Introduce `z _`. Establish `ha : (z + c z) / 2 ∈ NumberField.maximalRealSubfield K`. Introduce `φ`. Express the relevant statement in the definitionally equal form `starRingEnd ℂ _ = _`. Simplify using `[hc, add_comm, map_ofNat]`.

Establish `hb : (z - c z) / (2 * d) ∈ NumberField.maximalRealSubfield K`. Introduce `φ`. Express the relevant statement in the definitionally equal form `starRingEnd ℂ _ = _`. Rewrite using `[map_div₀, map_div₀, hanti, map_mul, map_mul, hd, map_ofNat, map_ofNat, mul_neg, neg_div_neg_eq]`. Rewrite using `[Matrix.range_cons_cons_empty, Submodule.mem_span_pair]`.

Use `⟨⟨_, ha⟩, ⟨_, hb⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(z + c z) / 2 * 1 + (z - c z) / (2 * d) * d = z`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hfin : Module.finrank (NumberField.maximalRealSubfield K) K = 2`.

Rewrite using `[Module.finrank_eq_card_basis (Module.Basis.mk hli hsp), Fintype.card_fin]`. Use `haveI : Algebra.IsQuadraticExtension (NumberField.maximalRealSubfield K) K := { finrank_eq_two' := hfin }`. Conclude with `⟨⟩`.
-/
theorem UpperTheory.Reformulated.B.Qh8.isCM_of_conj :
    ∀ (K : Type) [inst : Field K] [inst_1 : NumberField K]
    [NumberField.IsTotallyComplex K],
    (∀ (x : K), ∃ (y : K), ∀ (φ : K →+* ℂ), (φ : K → ℂ) y = (starRingEnd ℂ : ℂ → ℂ) ((φ : K → ℂ) x)) →
      NumberField.IsCMField K := by
  intro K _ _ _ h
  choose c hc using h
  let φ₀ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  obtain ⟨x, hx⟩ : ∃ x : K, starRingEnd ℂ (φ₀ x) ≠ φ₀ x := by
    by_contra hne
    apply NumberField.IsTotallyComplex.complexEmbedding_not_isReal φ₀
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext z
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
    by_contra hz
    exact hne ⟨z, hz⟩
  have hanti : ∀ (z : K) (φ : K →+* ℂ), starRingEnd ℂ (φ (z - c z)) = -φ (z - c z) := by
    intro z φ
    simp [hc]
  obtain ⟨d, hd0, hd⟩ : ∃ d : K, d ≠ 0 ∧ ∀ φ : K →+* ℂ, starRingEnd ℂ (φ d) = -φ d := by
    refine ⟨x - c x, fun h0 => hx ?_, hanti x⟩
    rw [← hc, ← sub_eq_zero.mp h0]
  have hli : LinearIndependent (NumberField.maximalRealSubfield K) ![(1 : K), d] := by
    rw [LinearIndependent.pair_iff]
    rintro ⟨s, hs⟩ ⟨t, ht⟩ hst
    have h1 : s * 1 + t * d = 0 := hst
    have h2 := congrArg φ₀ h1
    have h3 := congrArg (starRingEnd ℂ) h2
    have hs' : starRingEnd ℂ (φ₀ s) = φ₀ s := hs φ₀
    have ht' : starRingEnd ℂ (φ₀ t) = φ₀ t := ht φ₀
    simp only [map_add, map_mul, map_one, map_zero, hs', ht', hd] at h2 h3
    have hs0 : s = 0 := by
      apply φ₀.injective
      rw [map_zero]
      linear_combination (h2 + h3) / 2
    have ht0 : t = 0 := by
      rw [hs0, zero_mul, zero_add] at h1
      exact (mul_eq_zero.mp h1).resolve_right hd0
    exact ⟨Subtype.ext hs0, Subtype.ext ht0⟩
  have hsp : ⊤ ≤ Submodule.span (NumberField.maximalRealSubfield K)
      (Set.range ![(1 : K), d]) := by
    intro z _
    have ha : (z + c z) / 2 ∈ NumberField.maximalRealSubfield K := by
      intro φ
      change starRingEnd ℂ _ = _
      simp [hc, add_comm, map_ofNat]
    have hb : (z - c z) / (2 * d) ∈ NumberField.maximalRealSubfield K := by
      intro φ
      change starRingEnd ℂ _ = _
      rw [map_div₀, map_div₀, hanti, map_mul, map_mul, hd, map_ofNat, map_ofNat, mul_neg,
        neg_div_neg_eq]
    rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair]
    refine ⟨⟨_, ha⟩, ⟨_, hb⟩, ?_⟩
    change (z + c z) / 2 * 1 + (z - c z) / (2 * d) * d = z
    field_simp
    ring
  have hfin : Module.finrank (NumberField.maximalRealSubfield K) K = 2 := by
    rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp), Fintype.card_fin]
  haveI : Algebra.IsQuadraticExtension (NumberField.maximalRealSubfield K) K :=
    { finrank_eq_two' := hfin }
  exact ⟨⟩
