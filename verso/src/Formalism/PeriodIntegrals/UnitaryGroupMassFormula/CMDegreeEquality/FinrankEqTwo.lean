import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.MassRatio

open NumberField Module

noncomputable section

namespace CMDeg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def sigma (hfix : ∀ x : F, star (algebraMap F E x) = algebraMap F E x) : E ≃ₐ[F] E :=
  AlgEquiv.ofRingEquiv (f := starRingAut) (fun x => by simpa using hfix x)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sigma_apply (hfix : ∀ x : F, star (algebraMap F E x) = algebraMap F E x) (a : E) :
    sigma hfix a = star a := rfl

/- English proof (translation)
Use extensionality with `a`. Simplify using `[pow_two, AlgEquiv.mul_apply, sigma_apply]`.
-/
theorem sigma_sq (hfix : ∀ x : F, star (algebraMap F E x) = algebraMap F E x) :
    sigma hfix ^ 2 = 1 := by
  ext a
  simp [pow_two, AlgEquiv.mul_apply, sigma_apply]

/- English proof (translation)
Assume the negation of the conclusion as `h`. Simplify using `only [not_exists, not_not] at h`. Establish `: IsTotallyComplex E` using `hE.1`. Set `φ : E →+* ℂ` to `(Classical.arbitrary (InfinitePlace E)).embedding`. Apply `IsTotallyComplex.complexEmbedding_not_isReal φ` to reduce the goal to its premises.

Rewrite using `[ComplexEmbedding.isReal_iff]`. Use extensionality with `a`. Use `show starRingEnd ℂ (φ a) = φ a`. Rewrite using `[← hE.2.1 φ a, h a]`.
-/
theorem star_ne_id (hE : Formalism.HermitianLatticesTheory.IsCMUnram E) : ∃ a : E, star a ≠ a := by
  by_contra h
  simp only [not_exists, not_not] at h
  have : IsTotallyComplex E := hE.1
  let φ : E →+* ℂ := (Classical.arbitrary (InfinitePlace E)).embedding
  apply IsTotallyComplex.complexEmbedding_not_isReal φ
  rw [ComplexEmbedding.isReal_iff]
  ext a
  show starRingEnd ℂ (φ a) = φ a
  rw [← hE.2.1 φ a, h a]

/- English proof (translation)
Introduce `h1`. Take `⟨a, ha⟩` from `star_ne_id hE`. Apply `ha` to reduce the goal to its premises. Use `congrArg (fun g : E ≃ₐ[F] E => g a) h1` as an intermediate fact. Simplify `this` using `[sigma_apply]`.
-/
theorem sigma_ne_one (hE : Formalism.HermitianLatticesTheory.IsCMUnram E)
    (hfix : ∀ x : F, star (algebraMap F E x) = algebraMap F E x) : sigma hfix ≠ 1 := by
  intro h1
  obtain ⟨a, ha⟩ := star_ne_id hE
  apply ha
  have := congrArg (fun g : E ≃ₐ[F] E => g a) h1
  simpa [sigma_apply] using this

/- English proof (translation)
Take `⟨hE, hR⟩` from `hFE`. Establish `hfix : ∀ x : F, star (algebraMap F E x) = algebraMap F E x`. Introduce `x`. Establish `: algebraMap F E x ∈ Set.range (algebraMap F E)` using `⟨x, rfl⟩`. Rewrite `this` using `[hR]`.

Conclude with `this`. Establish `: FiniteDimensional F E` using `Module.Finite.of_restrictScalars_finite ℚ F E`. Set `σ` to `sigma hfix`. Set `H : Subgroup (E ≃ₐ[F] E)` to `Subgroup.zpowers σ`. Establish `hord : orderOf σ = 2` using `orderOf_eq_prime (sigma_sq hfix) (sigma_ne_one hE hfix)`.

Establish `hcard : finrank (IntermediateField.fixedField H) E = 2`. Rewrite using `[IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers, hord]`. Establish `hbot : IntermediateField.fixedField H = ⊥`. Use `le_antisymm ?_ bot_le` and prove the remaining obligations. Introduce `x hx`.

Rewrite `hx` using `[IntermediateField.mem_fixedField_iff]`. Establish `hx' : star x = x` using `hx σ (Subgroup.mem_zpowers σ)`. Rewrite using `[IntermediateField.mem_bot, hR]`. Conclude with `hx'`. Establish `h1 : finrank F (IntermediateField.fixedField H) = 1` using `IntermediateField.finrank_eq_one_iff.mpr hbot`.

Rewrite using `[← Module.finrank_mul_finrank F (IntermediateField.fixedField H) E, h1, hcard, one_mul]`.
-/
theorem finrank_eq_two (hFE : Formalism.L2.SG.MassRatio.IsCMPair F E) : finrank F E = 2 := by
  obtain ⟨hE, hR⟩ := hFE
  have hfix : ∀ x : F, star (algebraMap F E x) = algebraMap F E x := by
    intro x
    have : algebraMap F E x ∈ Set.range (algebraMap F E) := ⟨x, rfl⟩
    rw [hR] at this
    exact this
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let σ := sigma hfix
  let H : Subgroup (E ≃ₐ[F] E) := Subgroup.zpowers σ
  have hord : orderOf σ = 2 := orderOf_eq_prime (sigma_sq hfix) (sigma_ne_one hE hfix)
  have hcard : finrank (IntermediateField.fixedField H) E = 2 := by
    rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers, hord]
  have hbot : IntermediateField.fixedField H = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    have hx' : star x = x := hx σ (Subgroup.mem_zpowers σ)
    rw [IntermediateField.mem_bot, hR]
    exact hx'
  have h1 : finrank F (IntermediateField.fixedField H) = 1 :=
    IntermediateField.finrank_eq_one_iff.mpr hbot
  rw [← Module.finrank_mul_finrank F (IntermediateField.fixedField H) E, h1, hcard, one_mul]

end CMDeg

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ hFE`. Establish `: IsTotallyComplex E` using `hFE.1.1`. Establish `h2` using `CMDeg.finrank_eq_two hFE`. Establish `hQ : finrank ℚ F * finrank F E = finrank ℚ E` using `Module.finrank_mul_finrank ℚ F E`. Establish `hC` using `IsTotallyComplex.finrank (K := E)`.

Establish `hP` using `InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := E)`. Rewrite `hP` using `[IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]`. Unfold `Formalism.L2.SG.MassRatio.fF Formalism.HermitianLatticesTheory.fDeg`. Rewrite using `[hP]`. Rewrite `hQ` using `[h2]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem CMDeg.degEq : Formalism.L2.SG.MassRatio.DegEq := by
  intro F E _ _ _ _ _ _ hFE
  have : IsTotallyComplex E := hFE.1.1
  have h2 := CMDeg.finrank_eq_two hFE
  have hQ : finrank ℚ F * finrank F E = finrank ℚ E := Module.finrank_mul_finrank ℚ F E
  have hC := IsTotallyComplex.finrank (K := E)
  have hP := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := E)
  rw [IsTotallyComplex.nrRealPlaces_eq_zero, zero_add] at hP
  unfold Formalism.L2.SG.MassRatio.fF Formalism.HermitianLatticesTheory.fDeg
  rw [hP]
  rw [h2] at hQ
  omega
