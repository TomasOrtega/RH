import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertSplitAlt
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjOfSq

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

/- English proof (translation)
Use `haveI : Normal ℚ Ω := normal_iff.2 fun x => ⟨Algebra.IsIntegral.isIntegral x, IsAlgClosed.splits _⟩`. Use `haveI : IsGalois ℚ Ω := ⟨⟩`. Set `j : Ω →+* ℂ` to `(IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := Ω) : Ω →ₐ[ℚ] ℂ).toRingHom`. Take `⟨σ, hσ⟩` from `ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) j (ComplexEmbedding.conjugate j) (Subsingleton.elim _ _)`. Conclude with `⟨j, σ.symm.toRingEquiv, fun x => DFunLike.congr_fun hσ x⟩`.
-/
private theorem exists_conj (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic ℚ Ω] :
    ∃ (j : Ω →+* ℂ) (c : Ω ≃+* Ω), ∀ z, j (c z) = starRingEnd ℂ (j z) := by
  haveI : Normal ℚ Ω := normal_iff.2 fun x => ⟨Algebra.IsIntegral.isIntegral x, IsAlgClosed.splits _⟩
  haveI : IsGalois ℚ Ω := ⟨⟩
  let j : Ω →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := Ω) : Ω →ₐ[ℚ] ℂ).toRingHom
  obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) j
    (ComplexEmbedding.conjugate j) (Subsingleton.elim _ _)
  exact ⟨j, σ.symm.toRingEquiv, fun x => DFunLike.congr_fun hσ x⟩

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qh56.conj_of_sq hq h`.
-/
private theorem conj_of_sq {w : ℂ} {q : ℕ} (hq : 0 < q) (h : w ^ 2 = (q : ℂ)) :
    starRingEnd ℂ w = w :=
  _root_.UpperTheory.Reformulated.B.Qh56.conj_of_sq hq h

/- English proof (translation)
Establish `h2 : (j δ) ^ 2 = (algebraMap Y Ω δ) ^ 2`. Rewrite using `[← map_pow, ← map_pow, hq, map_natCast, map_natCast]`. Establish `hfix : g (g (j δ)) = j δ`. Apply the tactic sequence `rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h <;> rw [h] <;> simp [hδ]`. Take `⟨a, b, rfl⟩` from `hspan y`.

Establish `ha` using `hE (j.comp (algebraMap E Y)) a`. Establish `hb` using `hE (j.comp (algebraMap E Y)) b`. Simplify using `only [RingHom.comp_apply] at ha hb`. Simplify using `only [map_add, map_mul, ha, hb, hfix]`.
-/
private theorem sq_fix {E Y Ω : Type} [Field E] [Field Y] [Field Ω] [Algebra E Y] [Algebra Y Ω]
    (δ : Y) (q : ℕ) (hq : δ ^ 2 = (q : Y))
    (hspan : ∀ y : Y, ∃ a b : E, y = algebraMap E Y a + algebraMap E Y b * δ)
    (g : Ω ≃+* Ω) (hδ : g (algebraMap Y Ω δ) = -algebraMap Y Ω δ)
    (hE : ∀ (j : E →+* Ω) (x : E), g (g (j x)) = j x) (j : Y →+* Ω) (y : Y) :
    g (g (j y)) = j y := by
  have h2 : (j δ) ^ 2 = (algebraMap Y Ω δ) ^ 2 := by
    rw [← map_pow, ← map_pow, hq, map_natCast, map_natCast]
  have hfix : g (g (j δ)) = j δ := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h <;> rw [h] <;> simp [hδ]
  obtain ⟨a, b, rfl⟩ := hspan y
  have ha := hE (j.comp (algebraMap E Y)) a
  have hb := hE (j.comp (algebraMap E Y)) b
  simp only [RingHom.comp_apply] at ha hb
  simp only [map_add, map_mul, ha, hb, hfix]

/- English proof (translation)
Introduce `PW E Y Ω _ _ _ _ _ _ _ _ δ hδ M B hM`. Take `⟨⟨q, hq0, hq⟩, hspan, s, hsE, hsδ⟩` from `hδ`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap Y Ω).injective`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed Y`. Use `haveI : Algebra.IsAlgebraic Y Ω := IsAlgClosure.isAlgebraic`.

Use `haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ Y Ω`. Take `⟨j0, c, hc⟩` from `exists_conj Ω`. Establish `hδ2 : (algebraMap Y Ω δ) ^ 2 = (q : Ω)` using `by rw [← map_pow, hq, map_natCast]`. Establish `hcc : ∀ z, c (c z) = z` using `fun z => j0.injective (by rw [hc, hc, Complex.conj_conj])`. Establish `hcδ : c (algebraMap Y Ω δ) = algebraMap Y Ω δ` using `j0.injective (by`.

Rewrite using `[hc]`. Conclude with `conj_of_sq hq0 (by rw [← map_pow, hδ2, map_natCast]))`. Establish `hcroot : ∀ ξ : Ω, ξ ^ M = 1 → c ξ = ξ⁻¹` using `fun ξ h => j0.injective (by`. Establish `h1 : (j0 ξ) ^ M = 1` using `by rw [← map_pow, h, map_one]`. Rewrite using `[hc, map_inv₀, Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one h1 hM.ne')])`.

Use `haveI : NeZero (M : Ω) := ⟨Nat.cast_ne_zero.2 hM.ne'⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω M`. Establish `hsc : ∀ (j : E →+* Ω) (x : E), s (c (j x)) = c (j x)` using `fun j x => hsE ((c : Ω →+* Ω).comp j) x`. Establish `hsinv : ∀ (j : E →+* Ω) (x : E), s.symm (j x) = j x` using `fun j x => by`. Rewrite using `[RingEquiv.symm_apply_eq, hsE]`.

Establish `hsinvδ : s.symm (algebraMap Y Ω δ) = -algebraMap Y Ω δ`. Rewrite using `[RingEquiv.symm_apply_eq, map_neg, hsδ, neg_neg]`. Establish `h1δ : (s.trans c) (algebraMap Y Ω δ) = -algebraMap Y Ω δ` using `by show c (s _) = _`. Rewrite using `[hsδ, map_neg, hcδ]`. Establish `h11 : ∀ (j : Y →+* Ω) (y : Y), (s.trans c) ((s.trans c) (j y)) = j y` using `sq_fix (E := E) δ q hq hspan (s.trans c) h1δ (fun j x => by show c (s (c (s (j x)))) = j x`.

Rewrite using `[hsE j x, hsc j x, hcc])`. Establish `h22 : ∀ (j : Y →+* Ω) (y : Y), s.symm (s.symm (j y)) = j y` using `sq_fix (E := E) δ q hq hspan s.symm hsinvδ (fun j x => by rw [hsinv, hsinv])`. Take `⟨p₁, hp₁, hB, hz₁, hA₁⟩` from `PW Y Ω (algebraMap Y Ω δ) q hq0 hδ2 (s.trans c) h1δ h11 M ζ hM hζ B`. Take `⟨p₂, hp₂, hB₂, hz₂, hA₂⟩` from `PW Y Ω (algebraMap Y Ω δ) q hq0 hδ2 s.symm hsinvδ h22 M ζ hM hζ p₁`. Establish `hsζ : (s ζ) ^ M = 1` using `by rw [← map_pow, hζ.pow_eq_one, map_one]`.

Establish `e1 : (s ζ)⁻¹ = ζ ^ p₁` using `by rw [← hcroot _ hsζ]; exact hz₁`. Establish `e2 : ζ = (s ζ) ^ p₂`. Rewrite using `[← map_pow, ← hz₂, RingEquiv.apply_symm_apply]`. Establish `hζ0 : ζ ≠ 0` using `hζ.ne_zero hM.ne'`. Establish `hdvd : M ∣ p₁ * p₂ + 1`.

Use `hζ.dvd_of_pow_eq_one _ ?_` and prove the remaining obligations. Rewrite using `[pow_succ, pow_mul, ← e1, inv_pow, ← e2, inv_mul_cancel₀ hζ0]`. Use `⟨p₁, p₂, hp₁, hp₂, hB, hB₂, hdvd, fun A hA h hh hδh y => ?_⟩` and prove the remaining obligations. Establish `hle : ∀ n : ℕ, A.valuation (n : Ω) ≤ 1` using `fun n => (A.valuation_le_one_iff _).2 (natCast_mem A n)`. Rewrite `hA` using `[Nat.cast_mul, map_mul]`.

Distinguish the cases in `h₁ : A.valuation (p₁ : Ω) < 1`. Conclude with `hA₁ A h₁ h hh hδh y`. Establish `e : A.valuation (p₁ : Ω) = 1` using `le_antisymm (hle _) (not_lt.1 h₁)`. Rewrite `hA` using `[e, one_mul]`. Conclude with `hA₂ A hA h hh hδh y`.
-/
theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.twoPrimes :
    PrimeWith → TwoPrimes := by
  intro PW E Y Ω _ _ _ _ _ _ _ _ δ hδ M B hM
  obtain ⟨⟨q, hq0, hq⟩, hspan, s, hsE, hsδ⟩ := hδ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap Y Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed Y
  haveI : Algebra.IsAlgebraic Y Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ Y Ω
  obtain ⟨j0, c, hc⟩ := exists_conj Ω
  have hδ2 : (algebraMap Y Ω δ) ^ 2 = (q : Ω) := by rw [← map_pow, hq, map_natCast]
  have hcc : ∀ z, c (c z) = z := fun z => j0.injective (by rw [hc, hc, Complex.conj_conj])
  have hcδ : c (algebraMap Y Ω δ) = algebraMap Y Ω δ := j0.injective (by
    rw [hc]
    exact conj_of_sq hq0 (by rw [← map_pow, hδ2, map_natCast]))
  have hcroot : ∀ ξ : Ω, ξ ^ M = 1 → c ξ = ξ⁻¹ := fun ξ h => j0.injective (by
    have h1 : (j0 ξ) ^ M = 1 := by rw [← map_pow, h, map_one]
    rw [hc, map_inv₀, Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one h1 hM.ne')])
  haveI : NeZero (M : Ω) := ⟨Nat.cast_ne_zero.2 hM.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  have hsc : ∀ (j : E →+* Ω) (x : E), s (c (j x)) = c (j x) :=
    fun j x => hsE ((c : Ω →+* Ω).comp j) x
  have hsinv : ∀ (j : E →+* Ω) (x : E), s.symm (j x) = j x := fun j x => by
    rw [RingEquiv.symm_apply_eq, hsE]
  have hsinvδ : s.symm (algebraMap Y Ω δ) = -algebraMap Y Ω δ := by
    rw [RingEquiv.symm_apply_eq, map_neg, hsδ, neg_neg]
  have h1δ : (s.trans c) (algebraMap Y Ω δ) = -algebraMap Y Ω δ := by
    show c (s _) = _
    rw [hsδ, map_neg, hcδ]
  have h11 : ∀ (j : Y →+* Ω) (y : Y), (s.trans c) ((s.trans c) (j y)) = j y :=
    sq_fix (E := E) δ q hq hspan (s.trans c) h1δ (fun j x => by
      show c (s (c (s (j x)))) = j x
      rw [hsE j x, hsc j x, hcc])
  have h22 : ∀ (j : Y →+* Ω) (y : Y), s.symm (s.symm (j y)) = j y :=
    sq_fix (E := E) δ q hq hspan s.symm hsinvδ (fun j x => by rw [hsinv, hsinv])
  obtain ⟨p₁, hp₁, hB, hz₁, hA₁⟩ := PW Y Ω (algebraMap Y Ω δ) q hq0 hδ2 (s.trans c) h1δ h11 M ζ hM hζ B
  obtain ⟨p₂, hp₂, hB₂, hz₂, hA₂⟩ := PW Y Ω (algebraMap Y Ω δ) q hq0 hδ2 s.symm hsinvδ h22 M ζ hM hζ p₁
  have hsζ : (s ζ) ^ M = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have e1 : (s ζ)⁻¹ = ζ ^ p₁ := by rw [← hcroot _ hsζ]; exact hz₁
  have e2 : ζ = (s ζ) ^ p₂ := by
    rw [← map_pow, ← hz₂, RingEquiv.apply_symm_apply]
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hM.ne'
  have hdvd : M ∣ p₁ * p₂ + 1 := by
    refine hζ.dvd_of_pow_eq_one _ ?_
    rw [pow_succ, pow_mul, ← e1, inv_pow, ← e2, inv_mul_cancel₀ hζ0]
  refine ⟨p₁, p₂, hp₁, hp₂, hB, hB₂, hdvd, fun A hA h hh hδh y => ?_⟩
  have hle : ∀ n : ℕ, A.valuation (n : Ω) ≤ 1 := fun n =>
    (A.valuation_le_one_iff _).2 (natCast_mem A n)
  rw [Nat.cast_mul, map_mul] at hA
  by_cases h₁ : A.valuation (p₁ : Ω) < 1
  · exact hA₁ A h₁ h hh hδh y
  · have e : A.valuation (p₁ : Ω) = 1 := le_antisymm (hle _) (not_lt.1 h₁)
    rw [e, one_mul] at hA
    exact hA₂ A hA h hh hδh y
