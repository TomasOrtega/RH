import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbBound
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

namespace GlobalTheory.CompanionTheory.Ar.QuotUnif.Dich

/- English proof (translation)
Rewrite using `[RingHom.injective_iff_ker_eq_bot]`. Use `Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_` and prove the remaining obligations. Rewrite using `[eq_bot_iff]`. Introduce `n hn`. Establish `h0 : r (algebraMap ℤ (𝓞 F) n) = 0` using `hn`.

Establish `: (n : ℂ) = 0` using `by simpa using h0`. Simplify using `using this`.
-/
theorem ringOfIntegers_hom_injective {F : Type} [Field F] [NumberField F] (r : 𝓞 F →+* ℂ) :
    Function.Injective r := by
  rw [RingHom.injective_iff_ker_eq_bot]
  refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
  rw [eq_bot_iff]
  intro n hn
  have h0 : r (algebraMap ℤ (𝓞 F) n) = 0 := hn
  have : (n : ℂ) = 0 := by simpa using h0
  simpa using this

/- English proof (translation)
Assemble the required witnesses or components as `⟨IsFractionRing.lift (K := F) (ringOfIntegers_hom_injective r), RingHom.ext fun a => by simp only [RingHom.comp_apply] exact IsFractionRing.lift_algebraMap (K := F) (ringOfIntegers_hom_injective r) a⟩`.
-/
theorem exists_extension_to_field {F : Type} [Field F] [NumberField F] (r : 𝓞 F →+* ℂ) :
    ∃ r' : F →+* ℂ, r'.comp (algebraMap (𝓞 F) F) = r :=
  ⟨IsFractionRing.lift (K := F) (ringOfIntegers_hom_injective r), RingHom.ext fun a => by
    simp only [RingHom.comp_apply]
    exact IsFractionRing.lift_algebraMap (K := F) (ringOfIntegers_hom_injective r) a⟩

/- English proof (translation)
Establish `hd : (0 : ℝ) ≤ d` using `Nat.cast_nonneg d`. Establish `hre` using `congrArg Complex.re h`. Establish `him` using `congrArg Complex.im h`. Simplify using `only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re, Complex.natCast_im, neg_zero] at hre him`. Establish `h0 : x.re = 0`.

Assume the negation of the conclusion as `hne`. Establish `: x.im = 0`. Establish `: x.re * x.im = 0` using `by linarith`. Conclude with `(mul_eq_zero.1 this).resolve_left hne`. Rewrite `hre` using `[this]`.

Use polynomial arithmetic with `[mul_self_pos.2 hne]`. Apply the tactic sequence `apply Complex.ext <;> simp [h0]`.
-/
theorem conj_eq_neg_of_sq_eq_neg_natCast {x : ℂ} {d : ℕ} (h : x ^ 2 = -(d : ℂ)) :
    starRingEnd ℂ x = -x := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
    Complex.natCast_im, neg_zero] at hre him
  have h0 : x.re = 0 := by
    by_contra hne
    have : x.im = 0 := by
      have : x.re * x.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [this] at hre
    nlinarith [mul_self_pos.2 hne]
  apply Complex.ext <;> simp [h0]

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 z`. Use `haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }`. Set `r : 𝓞 c.F →+* ℂ` to `(Spec.preimage (z ≫ 𝔐.f ≫ Y.s)).hom`. Establish `hr : z ≫ 𝔐.f ≫ Y.s = spMap r`. Simplify using `[r, spMap]`.

Take `⟨τ, hτ⟩` from `exists_extension_to_field r`. Establish `h1` using `congrArg (τ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ_sq`. Establish `h2 : ((τ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ) ^ 2 = H.rt0 ^ 2`. Rewrite using `[← map_pow, h1, H.sqrt_neg_disc_sq, map_neg, map_natCast]`. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h` into its components or cases.

Conclude with `Or.inl ⟨τ, by rw [hr, hτ], h⟩`. Use `Or.inr ⟨(starRingEnd ℂ).comp τ, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, hr, ← hτ]`. Simplify using `only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, RingHom.comp_assoc]`. Rewrite using `[RingHom.comp_assoc, RingHom.comp_apply, h, map_neg, conj_eq_neg_of_sq_eq_neg_natCast H.sqrt_neg_disc_sq, neg_neg]`.
-/
theorem goodPt_or_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X), GoodPt 𝔐 z ∨ GoodPt 𝔐 (spMap (starRingEnd ℂ) ≫ z) := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 z
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  let r : 𝓞 c.F →+* ℂ := (Spec.preimage (z ≫ 𝔐.f ≫ Y.s)).hom
  have hr : z ≫ 𝔐.f ≫ Y.s = spMap r := by
    simp [r, spMap]
  obtain ⟨τ, hτ⟩ := exists_extension_to_field r
  have h1 := congrArg (τ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ_sq
  have h2 : ((τ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, h1, H.sqrt_neg_disc_sq, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
  · exact Or.inl ⟨τ, by rw [hr, hτ], h⟩
  · refine Or.inr ⟨(starRingEnd ℂ).comp τ, ?_, ?_⟩
    · rw [Category.assoc, hr, ← hτ]
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, RingHom.comp_assoc]
    · rw [RingHom.comp_assoc, RingHom.comp_apply, h, map_neg,
        conj_eq_neg_of_sq_eq_neg_natCast H.sqrt_neg_disc_sq, neg_neg]

end GlobalTheory.CompanionTheory.Ar.QuotUnif.Dich
