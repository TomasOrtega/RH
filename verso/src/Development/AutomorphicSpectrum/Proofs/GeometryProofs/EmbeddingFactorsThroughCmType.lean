import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ImaginaryRootConj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LabelCover

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

/- English proof (translation)
Establish `hker : RingHom.ker τ = ⊥`. Apply `Ideal.eq_bot_of_comap_eq_bot (R := ℤ)` to reduce the goal to its premises. Rewrite using `[RingHom.comap_ker, RingHom.ker_eq_bot_iff_eq_zero]`. Introduce `n hn`. Simplify using `using hn`.

Establish `hinj : Function.Injective τ` using `(RingHom.injective_iff_ker_eq_bot τ).mpr hker`. Conclude with `⟨IsFractionRing.lift hinj, RingHom.ext fun x => IsFractionRing.lift_algebraMap hinj x⟩`.
-/
theorem exists_ext {E : Type} [Field E] [NumberField E] {K : Type} [Field K] [CharZero K] (τ : 𝓞 E →+* K) :
    ∃ ψ : E →+* K, ψ.comp (algebraMap (𝓞 E) E) = τ := by
  have hker : RingHom.ker τ = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    rw [RingHom.comap_ker, RingHom.ker_eq_bot_iff_eq_zero]
    intro n hn
    simpa using hn
  have hinj : Function.Injective τ := (RingHom.injective_iff_ker_eq_bot τ).mpr hker
  exact ⟨IsFractionRing.lift hinj, RingHom.ext fun x => IsFractionRing.lift_algebraMap hinj x⟩

/- English proof (translation)
The claim follows from `(RingHom.charZero_iff (φ.comp (algebraMap ℚ F)).injective).mp inferInstance`.
-/
theorem charZero_of_coeff {F : IntermediateField ℚ ℂ} {k : Type} [Field k] (φ : F →+* k) : CharZero k :=
  (RingHom.charZero_iff (φ.comp (algebraMap ℚ F)).injective).mp inferInstance

/- English proof (translation)
Use `haveI : CharZero k := charZero_of_coeff φ`. Set `g : (E →+* ℂ) → (E →+* k)` to `fun τ => φ.comp (τ.codRestrict c.F (c.conj τ))`. Establish `hg : Function.Injective g`. Introduce `τ τ' h`. Use extensionality with `a`.

Establish `h1` using `RingHom.congr_fun h a`. Simplify using `only [g, RingHom.comp_apply] at h1`. Conclude with `congrArg Subtype.val (φ.injective h1)`. Establish `hcard : Fintype.card (E →+* ℂ) = Fintype.card (E →+* k)`. Rewrite using `[NumberField.Embeddings.card, NumberField.Embeddings.card]`.

Take `⟨τ₁, hτ₁⟩` from `((Fintype.bijective_iff_injective_and_card g).mpr ⟨hg, hcard⟩).2 ψ`. Conclude with `⟨τ₁, hτ₁⟩`.
-/
theorem exists_factor {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    {k : Type} [Field k] [IsAlgClosed k] (φ : c.F →+* k) (ψ : E →+* k) :
    ∃ τ₁ : E →+* ℂ, φ.comp (τ₁.codRestrict c.F (c.conj τ₁)) = ψ := by
  haveI : CharZero k := charZero_of_coeff φ
  let g : (E →+* ℂ) → (E →+* k) := fun τ => φ.comp (τ.codRestrict c.F (c.conj τ))
  have hg : Function.Injective g := by
    intro τ τ' h
    ext a
    have h1 := RingHom.congr_fun h a
    simp only [g, RingHom.comp_apply] at h1
    exact congrArg Subtype.val (φ.injective h1)
  have hcard : Fintype.card (E →+* ℂ) = Fintype.card (E →+* k) := by
    rw [NumberField.Embeddings.card, NumberField.Embeddings.card]
  obtain ⟨τ₁, hτ₁⟩ := ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hg, hcard⟩).2 ψ
  exact ⟨τ₁, hτ₁⟩

/- English proof (translation)
Introduce `E _ _ _ H l c ρ₀ hρ₀ k _ _ φ τ`. Use `haveI : CharZero k := charZero_of_coeff φ`. Take `⟨ψ, hψ⟩` from `exists_ext τ`. Take `⟨τ₁, hτ₁⟩` from `exists_factor c φ ψ`. Establish `key : ∀ a : 𝓞 E, φ ⟨τ₁ (a : E), c.conj τ₁ (a : E)⟩ = τ a`.

Introduce `a`. Rewrite using `[← hψ, ← hτ₁]`. Both sides reduce to the same expression. Establish `hrt : τ₁ (H.rt : E) = H.rt0 ↔ τ H.rt = φ ρ₀`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Rewrite using `[← key]`. Use `congr 1`. Conclude with `Subtype.ext (h.trans hρ₀.symm)`. Introduce `h`.

Rewrite `h` using `[← key]`. Rewrite using `[← hρ₀]`. Conclude with `congrArg Subtype.val (φ.injective h)`. Use `⟨fun h => ⟨⟨τ₁, hrt.mpr h⟩, RingHom.ext fun a => key a⟩, fun h => ?_⟩` and prove the remaining obligations. Establish `hne : τ₁ (H.rt : E) ≠ H.rt0` using `fun h' => h (hrt.mp h')`.

Establish `hsqE : (H.rt : E) ^ 2 = -(H.d : E)`. Use `congrArg (algebraMap (𝓞 E) E) H.rt_sq` as an intermediate fact. Simplify using `using this`. Establish `hsq : τ₁ (H.rt : E) ^ 2 = H.rt0 ^ 2`. Rewrite using `[← map_pow, hsqE, map_neg, map_natCast, H.sqrt_neg_disc_sq]`.

Establish `hneg : τ₁ (H.rt : E) = -H.rt0`. Break down `sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h1 | h1` into its components or cases. Conclude with `absurd h1 hne`. Conclude with `h1`. Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`.

Establish `hre : H.rt0.re = 0`. Establish `h1` using `congrArg Complex.re H.sqrt_neg_disc_sq`. Establish `h2` using `congrArg Complex.im H.sqrt_neg_disc_sq`. Simplify using `only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re, Complex.natCast_im, neg_zero] at h1 h2`. Establish `h3 : H.rt0.re * H.rt0.im = 0` using `by linarith`.

Break down `mul_eq_zero.mp h3 with h4 | h4` into its components or cases. Conclude with `h4`. It suffices to derive a contradiction. Rewrite `h1` using `[h4]`. Use polynomial arithmetic with `[sq_nonneg H.rt0.re]`.

Establish `hconj : (starRingEnd ℂ) (-H.rt0) = H.rt0`. Apply the tactic sequence `apply Complex.ext <;> simp [hre]`. Use `⟨⟨τ₁.comp (NumberField.IsCMField.complexConj E).toRingEquiv.toRingHom, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show τ₁ (NumberField.IsCMField.complexConj E (H.rt : E)) = H.rt0`. Rewrite using `[NumberField.IsCMField.complexEmbedding_complexConj, hneg, hconj]`.

Use `RingHom.ext fun a => ?_` and prove the remaining obligations. Rewrite using `[← key a, RingHom.comp_apply]`. Use `congrArg φ (Subtype.ext ?_)` and prove the remaining obligations. Use `show τ₁ (NumberField.IsCMField.complexConj E ((H.bar a : 𝓞 E) : E)) = τ₁ (a : E)`. Rewrite using `[H.bar_eq, NumberField.IsCMField.complexConj_apply_apply]`.
-/
theorem exists_label : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l)
    (ρ₀ : c.F), (ρ₀ : ℂ) = H.rt0 → ∀ (k : Type) [Field k] [IsAlgClosed k] (φ : c.F →+* k) (τ : 𝓞 E →+* k),
    (τ H.rt = φ ρ₀ → ∃ t : CMType H, φ.comp (labelEmb c (.inl t)) = τ) ∧
    (τ H.rt ≠ φ ρ₀ → ∃ t : CMType H, φ.comp (labelEmb c (.inr t)) = τ) := by
  intro E _ _ _ H l c ρ₀ hρ₀ k _ _ φ τ
  haveI : CharZero k := charZero_of_coeff φ
  obtain ⟨ψ, hψ⟩ := exists_ext τ
  obtain ⟨τ₁, hτ₁⟩ := exists_factor c φ ψ
  have key : ∀ a : 𝓞 E, φ ⟨τ₁ (a : E), c.conj τ₁ (a : E)⟩ = τ a := by
    intro a
    rw [← hψ, ← hτ₁]
    rfl
  have hrt : τ₁ (H.rt : E) = H.rt0 ↔ τ H.rt = φ ρ₀ := by
    constructor
    · intro h
      rw [← key]
      congr 1
      exact Subtype.ext (h.trans hρ₀.symm)
    · intro h
      rw [← key] at h
      rw [← hρ₀]
      exact congrArg Subtype.val (φ.injective h)
  refine ⟨fun h => ⟨⟨τ₁, hrt.mpr h⟩, RingHom.ext fun a => key a⟩, fun h => ?_⟩
  have hne : τ₁ (H.rt : E) ≠ H.rt0 := fun h' => h (hrt.mp h')
  have hsqE : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have hsq : τ₁ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, hsqE, map_neg, map_natCast, H.sqrt_neg_disc_sq]
  have hneg : τ₁ (H.rt : E) = -H.rt0 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h1 | h1
    · exact absurd h1 hne
    · exact h1
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hre : H.rt0.re = 0 := by
    have h1 := congrArg Complex.re H.sqrt_neg_disc_sq
    have h2 := congrArg Complex.im H.sqrt_neg_disc_sq
    simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
      Complex.natCast_im, neg_zero] at h1 h2
    have h3 : H.rt0.re * H.rt0.im = 0 := by linarith
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact h4
    · exfalso
      rw [h4] at h1
      nlinarith [sq_nonneg H.rt0.re]
  have hconj : (starRingEnd ℂ) (-H.rt0) = H.rt0 := by
    apply Complex.ext <;> simp [hre]
  refine ⟨⟨τ₁.comp (NumberField.IsCMField.complexConj E).toRingEquiv.toRingHom, ?_⟩, ?_⟩
  · show τ₁ (NumberField.IsCMField.complexConj E (H.rt : E)) = H.rt0
    rw [NumberField.IsCMField.complexEmbedding_complexConj, hneg, hconj]
  · refine RingHom.ext fun a => ?_
    rw [← key a, RingHom.comp_apply]
    refine congrArg φ (Subtype.ext ?_)
    show τ₁ (NumberField.IsCMField.complexConj E ((H.bar a : 𝓞 E) : E)) = τ₁ (a : E)
    rw [H.bar_eq, NumberField.IsCMField.complexConj_apply_apply]

end GlobalTheory.CompanionTheory.Ar.LabelCover
