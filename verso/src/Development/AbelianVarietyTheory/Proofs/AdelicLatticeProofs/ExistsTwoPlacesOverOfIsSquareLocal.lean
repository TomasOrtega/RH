import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsQuadraticSqrtExtensionBasicFacts
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

/- English proof (translation)
Establish `h : IsIntegral u.integer (algebraMap (𝓞 E) E x)` using `(RingOfIntegers.isIntegral_coe x).tower_top`. Conclude with `(Valuation.integer.integers u).mem_of_integral h`.
-/
theorem val_integer_le_one {E Γ : Type} [Field E] [LinearOrderedCommGroupWithZero Γ]
    (u : Valuation E Γ) (x : 𝓞 E) : u (algebraMap (𝓞 E) E x) ≤ 1 := by
  have h : IsIntegral u.integer (algebraMap (𝓞 E) E x) :=
    (RingOfIntegers.isIntegral_coe x).tower_top
  exact (Valuation.integer.integers u).mem_of_integral h

/- English proof (translation)
Set `I : Ideal (𝓞 E)` to `{ carrier := {x | u (algebraMap (𝓞 E) E x) < 1} add_mem' := by`. Introduce `a b ha hb`. Simplify using `only [Set.mem_setOf_eq, map_add] at *`. Conclude with `u.map_add_lt ha hb`. Use the proof step `zero_mem' := by simp`.

Use the proof step `smul_mem' := by`. Introduce `c x hx`. Simplify using `only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at *`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (val_integer_le_one u c)) hx }`. Establish `hI : ∀ x : 𝓞 E, x ∈ I ↔ u (algebraMap (𝓞 E) E x) < 1` using `fun x => Iff.rfl`.

Establish `hp : I.IsPrime`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.ne_top_iff_one, hI]`. Simplify using the standard rewrite rules. Introduce `a b hab`.

Rewrite `hab` using `[hI, map_mul, map_mul]`. Rewrite using `[hI, hI]`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `absurd hab (not_lt.2 (one_le_mul hc.1 hc.2))`.

Establish `hc : ∀ a : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) a ∈ I ↔ a ∈ v.asIdeal`. Introduce `a`. Rewrite using `[hI, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E, hu]`. Conclude with `v.valuation_lt_one_iff_mem a`. Establish `hne : I ≠ ⊥`.

Introduce `h0`. Apply `v.ne_bot` to reduce the goal to its premises. Rewrite using `[eq_bot_iff]`. Introduce `a ha`. Use `(hc a).2 ha` as an intermediate fact.

Rewrite `this` using `[h0, Ideal.mem_bot]`. Rewrite using `[Ideal.mem_bot]`. Conclude with `(map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))).1 this`. Use `⟨⟨I, hp, hne⟩, ?_, hI⟩` and prove the remaining obligations. Use extensionality with `a`.

Conclude with `hc a`.
-/
theorem exists_centre_over {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (u : Valuation E ℤᵐ⁰)
    (hu : ∀ a : F, u (algebraMap F E a) = v.valuation F a) :
    ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v ∧
      ∀ x : 𝓞 E, x ∈ w.asIdeal ↔ u (algebraMap (𝓞 E) E x) < 1 := by
  let I : Ideal (𝓞 E) :=
    { carrier := {x | u (algebraMap (𝓞 E) E x) < 1}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_add] at *
        exact u.map_add_lt ha hb
      zero_mem' := by simp
      smul_mem' := by
        intro c x hx
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at *
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_integer_le_one u c)) hx }
  have hI : ∀ x : 𝓞 E, x ∈ I ↔ u (algebraMap (𝓞 E) E x) < 1 := fun x => Iff.rfl
  have hp : I.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one, hI]; simp
    · intro a b hab
      rw [hI, map_mul, map_mul] at hab
      rw [hI, hI]
      by_contra hc
      push Not at hc
      exact absurd hab (not_lt.2 (one_le_mul hc.1 hc.2))
  have hc : ∀ a : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) a ∈ I ↔ a ∈ v.asIdeal := by
    intro a
    rw [hI, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E, hu]
    exact v.valuation_lt_one_iff_mem a
  have hne : I ≠ ⊥ := by
    intro h0
    apply v.ne_bot
    rw [eq_bot_iff]
    intro a ha
    have := (hc a).2 ha
    rw [h0, Ideal.mem_bot] at this
    rw [Ideal.mem_bot]
    exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))).1 this
  refine ⟨⟨I, hp, hne⟩, ?_, hI⟩
  ext a
  exact hc a

/- English proof (translation)
Use `choose A B hAB using h.span`. Establish `key : ∀ (x : E) (a b : F), x = algebraMap F E a + algebraMap F E b * θ → φ (A x) + φ (B x) * r = φ a + φ b * r`. Introduce `x a b hx`. Use `h.coord_indep (A x - a) (B x - b) (by` as an intermediate fact. Rewrite using `[map_sub, map_sub]`.

Take the linear combination `hx - hAB x)`. Rewrite using `[sub_eq_zero.1 this.1, sub_eq_zero.1 this.2]`. Use `⟨{ toFun := fun x => φ (A x) + φ (B x) * r map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[key 1 1 0 (by simp)]; simp`. Introduce `x y`.

Rewrite using `[key (x * y) (A x * A y + δ * B x * B y) (A x * B y + B x * A y) (by`. Simplify using `only [map_add, map_mul, ← h.sq]`. Take the linear combination `y * hAB x + (algebraMap F E (A x) + algebraMap F E (B x) * θ) * hAB y)]`. Simplify using `only [map_add, map_mul, hr]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[key 0 0 0 (by simp)]; simp`. Introduce `x y`. Rewrite using `[key (x + y) (A x + A y) (B x + B y) (by`. Simplify using `only [map_add]`. Take the linear combination `hAB x + hAB y)]`.

Simplify using `only [map_add]`. Expand and normalize the polynomial expressions, which then agree. Introduce `a`. Express the relevant statement in the definitionally equal form `φ (A _) + φ (B _) * r = _`. Rewrite using `[key _ a 0 (by simp)]; simp`.

Express the relevant statement in the definitionally equal form `φ (A _) + φ (B _) * r = _`. Rewrite using `[key _ 0 1 (by simp)]; simp`.
-/
theorem IsQuad.exists_embedding_root {F E L : Type} [Field F] [Field E] [Algebra F E] [Field L]
    {δ : F} {θ : E} {σ : E ≃ₐ[F] E} (h : IsQuad δ θ σ) (φ : F →+* L) (r : L)
    (hr : φ δ = r * r) :
    ∃ ψ : E →+* L, (∀ a : F, ψ (algebraMap F E a) = φ a) ∧ ψ θ = r := by
  choose A B hAB using h.span
  have key : ∀ (x : E) (a b : F), x = algebraMap F E a + algebraMap F E b * θ →
      φ (A x) + φ (B x) * r = φ a + φ b * r := by
    intro x a b hx
    have := h.coord_indep (A x - a) (B x - b) (by
      rw [map_sub, map_sub]; linear_combination hx - hAB x)
    rw [sub_eq_zero.1 this.1, sub_eq_zero.1 this.2]
  refine ⟨{ toFun := fun x => φ (A x) + φ (B x) * r
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, ?_, ?_⟩
  · rw [key 1 1 0 (by simp)]; simp
  · intro x y
    rw [key (x * y) (A x * A y + δ * B x * B y) (A x * B y + B x * A y) (by
      simp only [map_add, map_mul, ← h.sq]
      linear_combination y * hAB x + (algebraMap F E (A x) + algebraMap F E (B x) * θ) * hAB y)]
    simp only [map_add, map_mul, hr]; ring
  · rw [key 0 0 0 (by simp)]; simp
  · intro x y
    rw [key (x + y) (A x + A y) (B x + B y) (by
      simp only [map_add]
      linear_combination hAB x + hAB y)]
    simp only [map_add]; ring
  · intro a
    change φ (A _) + φ (B _) * r = _
    rw [key _ a 0 (by simp)]; simp
  · change φ (A _) + φ (B _) * r = _
    rw [key _ 0 1 (by simp)]; simp

/- English proof (translation)
Establish `hopen : IsOpen {x : L | Valued.v x < (1 : Γ)}`. Simplify using `using Valued.isOpen_ball L (1 : (MonoidWithZeroHom.ofClass (Valued.v : Valuation L Γ)).ValueGroup₀)`. Establish `hcont : Continuous fun x : L => (r - x) * c` using `by fun_prop`. Conclude with `hφ.exists_mem_open (hopen.preimage hcont) ⟨r, by simp⟩`.
-/
theorem exists_val_sub_mul_lt_one {F L Γ : Type} [Field L] [LinearOrderedCommGroupWithZero Γ]
    [Valued L Γ] (φ : F → L) (hφ : DenseRange φ) (r c : L) :
    ∃ ρ : F, Valued.v ((r - φ ρ) * c) < (1 : Γ) := by
  have hopen : IsOpen {x : L | Valued.v x < (1 : Γ)} := by
    simpa using Valued.isOpen_ball L (1 : (MonoidWithZeroHom.ofClass
      (Valued.v : Valuation L Γ)).ValueGroup₀)
  have hcont : Continuous fun x : L => (r - x) * c := by fun_prop
  exact hφ.exists_mem_open (hopen.preimage hcont) ⟨r, by simp⟩

/- English proof (translation)
Introduce `F E _ _ _ _ _ δ θ σ h v ⟨r, hr⟩`. Take `⟨ψ, hψ, hθ⟩` from `h.exists_embedding_root (algebraMap F (v.adicCompletion F)) r hr`. Set `u : Valuation E ℤᵐ⁰` to `(Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).comap ψ`. Set `u' : Valuation E ℤᵐ⁰` to `u.comap (σ : E →+* E)`. Establish `hu : ∀ a : F, u (algebraMap F E a) = v.valuation F a`.

Introduce `a`. Express the relevant statement in the definitionally equal form `Valued.v (ψ _) = _`. Rewrite using `[hψ]`. Conclude with `v.valuedAdicCompletion_eq_valuation' a`. Establish `hu' : ∀ a : F, u' (algebraMap F E a) = v.valuation F a`.

Introduce `a`. Express the relevant statement in the definitionally equal form `u (σ _) = _`. Rewrite using `[AlgEquiv.commutes, hu]`. Take `⟨w, hw, hwm⟩` from `exists_centre_over v u hu`. Take `⟨w', hw', hwm'⟩` from `exists_centre_over v u' hu'`.

Use `⟨w, w', ?_, hw, hw'⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Establish `hr0 : r ≠ 0`. Rewrite using `[← hθ]`. Conclude with `(map_ne_zero ψ).2 h.root_ne_zero`.

Establish `h2 : (2 : v.adicCompletion F) ≠ 0`. Establish `: (2 : v.adicCompletion F) = algebraMap F _ 2` using `by rw [map_ofNat]`. Rewrite using `[this]`. Conclude with `(map_ne_zero _).2 two_ne_zero`. Take `⟨ρ, hρ⟩` from `exists_val_sub_mul_lt_one _ (HeightOneSpectrum.denseRange_algebraMap F v) r (2 * r)⁻¹`.

Use `set t := (r - algebraMap F (v.adicCompletion F) ρ) * (2 * r)⁻¹ with ht`. Establish `hn : θ - algebraMap F E ρ ≠ 0`. Introduce `h0`. Conclude with `one_ne_zero (h.coord_indep (-ρ) 1 (by simp; linear_combination h0)).2`. Establish `hd : -θ - algebraMap F E ρ ≠ 0`.

Introduce `h0`. Conclude with `one_ne_zero (h.coord_indep ρ 1 (by simp; linear_combination -h0)).2`. Use `set y := (θ - algebraMap F E ρ) / (-θ - algebraMap F E ρ) with hy`. Establish `hy1 : y * σ y = 1`. Rewrite using `[hy, map_div₀, map_sub, map_sub, map_neg, h.conj, AlgEquiv.commutes, neg_neg]`.

Clear the denominators using the available nonvanishing facts. Establish `huy : u y < 1`. Express the relevant statement in the definitionally equal form `Valued.v (ψ y) < 1`. Establish `e1 : r - algebraMap F (v.adicCompletion F) ρ = 2 * r * t`. Rewrite using `[ht]`.

Clear the denominators using the available nonvanishing facts. Establish `e2 : -r - algebraMap F (v.adicCompletion F) ρ = -(2 * r * (1 - t))`. Take the linear combination `e1`. Rewrite using `[hy, map_div₀, map_sub, map_sub, map_neg, hθ, hψ, e1, e2, map_div₀, Valuation.map_neg, map_mul _ _ t, map_mul _ _ (1 - t), Valuation.map_one_sub_of_lt _ hρ, mul_one, mul_div_cancel_left₀ _ ((Valuation.ne_zero_iff _).2 (mul_ne_zero h2 hr0))]`. Conclude with `hρ`.

Establish `huu : u y * u' y = 1`. Express the relevant statement in the definitionally equal form `u y * u (σ y) = 1`. Rewrite using `[← map_mul, hy1, map_one]`. Take `⟨n, ⟨d, hd'⟩, hnd | hnd⟩` from `w.exists_primeCompl_mul_eq_or_mul_eq (K := E) y`. Establish `hd1 : 1 ≤ u' (algebraMap (𝓞 E) E d)` using `not_lt.1 fun a => hd' ((hwm' d).2 a)`.

Establish `h1 : u' y ≤ 1`. Use `val_integer_le_one u' n` as an intermediate fact. Rewrite `this` using `[← hnd, map_mul]`. Conclude with `le_trans (le_mul_of_one_le_right' hd1) this`. Establish `: u y * u' y < 1` using `lt_of_le_of_lt (mul_le_of_le_one_right' h1) huy`.

Conclude with `this.ne huu`. Establish `hd1 : 1 ≤ u (algebraMap (𝓞 E) E d)` using `not_lt.1 fun a => hd' ((hwm d).2 a)`. Rewrite `hd1` using `[← hnd, map_mul]`. Conclude with `absurd (lt_of_le_of_lt (mul_le_of_le_one_right' (val_integer_le_one u n)) huy) (not_lt.2 hd1)`.
-/
theorem two_places_of_isSquare : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → ∀ v : HeightOneSpectrum (𝓞 F), IsSquare (algebraMap F (v.adicCompletion F) δ) → ∃ w w' : HeightOneSpectrum (𝓞 E), w ≠ w' ∧ w.under (𝓞 F) = v ∧ w'.under (𝓞 F) = v := by
  intro F E _ _ _ _ _ δ θ σ h v ⟨r, hr⟩
  obtain ⟨ψ, hψ, hθ⟩ := h.exists_embedding_root (algebraMap F (v.adicCompletion F)) r hr
  let u : Valuation E ℤᵐ⁰ := (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).comap ψ
  let u' : Valuation E ℤᵐ⁰ := u.comap (σ : E →+* E)
  have hu : ∀ a : F, u (algebraMap F E a) = v.valuation F a := by
    intro a
    change Valued.v (ψ _) = _
    rw [hψ]
    exact v.valuedAdicCompletion_eq_valuation' a
  have hu' : ∀ a : F, u' (algebraMap F E a) = v.valuation F a := by
    intro a
    change u (σ _) = _
    rw [AlgEquiv.commutes, hu]
  obtain ⟨w, hw, hwm⟩ := exists_centre_over v u hu
  obtain ⟨w', hw', hwm'⟩ := exists_centre_over v u' hu'
  refine ⟨w, w', ?_, hw, hw'⟩
  rintro rfl
  have hr0 : r ≠ 0 := by
    rw [← hθ]; exact (map_ne_zero ψ).2 h.root_ne_zero
  have h2 : (2 : v.adicCompletion F) ≠ 0 := by
    have : (2 : v.adicCompletion F) = algebraMap F _ 2 := by rw [map_ofNat]
    rw [this]; exact (map_ne_zero _).2 two_ne_zero
  obtain ⟨ρ, hρ⟩ := exists_val_sub_mul_lt_one _ (HeightOneSpectrum.denseRange_algebraMap F v)
    r (2 * r)⁻¹
  set t := (r - algebraMap F (v.adicCompletion F) ρ) * (2 * r)⁻¹ with ht
  have hn : θ - algebraMap F E ρ ≠ 0 := by
    intro h0
    exact one_ne_zero (h.coord_indep (-ρ) 1 (by simp; linear_combination h0)).2
  have hd : -θ - algebraMap F E ρ ≠ 0 := by
    intro h0
    exact one_ne_zero (h.coord_indep ρ 1 (by simp; linear_combination -h0)).2
  set y := (θ - algebraMap F E ρ) / (-θ - algebraMap F E ρ) with hy
  have hy1 : y * σ y = 1 := by
    rw [hy, map_div₀, map_sub, map_sub, map_neg, h.conj, AlgEquiv.commutes, neg_neg]
    field_simp
  have huy : u y < 1 := by
    change Valued.v (ψ y) < 1
    have e1 : r - algebraMap F (v.adicCompletion F) ρ = 2 * r * t := by
      rw [ht]; field_simp
    have e2 : -r - algebraMap F (v.adicCompletion F) ρ = -(2 * r * (1 - t)) := by
      linear_combination e1
    rw [hy, map_div₀, map_sub, map_sub, map_neg, hθ, hψ, e1, e2, map_div₀, Valuation.map_neg,
      map_mul _ _ t, map_mul _ _ (1 - t), Valuation.map_one_sub_of_lt _ hρ, mul_one,
      mul_div_cancel_left₀ _ ((Valuation.ne_zero_iff _).2 (mul_ne_zero h2 hr0))]
    exact hρ
  have huu : u y * u' y = 1 := by
    change u y * u (σ y) = 1
    rw [← map_mul, hy1, map_one]
  obtain ⟨n, ⟨d, hd'⟩, hnd | hnd⟩ := w.exists_primeCompl_mul_eq_or_mul_eq (K := E) y
  · have hd1 : 1 ≤ u' (algebraMap (𝓞 E) E d) := not_lt.1 fun a => hd' ((hwm' d).2 a)
    have h1 : u' y ≤ 1 := by
      have := val_integer_le_one u' n
      rw [← hnd, map_mul] at this
      exact le_trans (le_mul_of_one_le_right' hd1) this
    have : u y * u' y < 1 := lt_of_le_of_lt (mul_le_of_le_one_right' h1) huy
    exact this.ne huu
  · have hd1 : 1 ≤ u (algebraMap (𝓞 E) E d) := not_lt.1 fun a => hd' ((hwm d).2 a)
    rw [← hnd, map_mul] at hd1
    exact absurd (lt_of_le_of_lt (mul_le_of_le_one_right' (val_integer_le_one u n)) huy)
      (not_lt.2 hd1)

end GlobalTheory.QNorm
