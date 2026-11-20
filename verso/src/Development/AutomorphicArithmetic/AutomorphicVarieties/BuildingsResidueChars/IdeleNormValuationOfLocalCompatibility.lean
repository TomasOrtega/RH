import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

/- English proof (translation)
Introduce `hN`. Unfold `UpperTheory.V.Af.Bc.NormLoc at hN`. Unfold `UpperTheory.V.Af.Bc.NormVal`. Introduce `E _ _ _ χ w f hf hχ`. Use `set u := HeightOneSpectrum.under (𝓞 ↥(maximalRealSubfield E)) w with hu`.

Establish `hunr : ∀ x : (HeightOneSpectrum.adicCompletion _ u)ˣ, IsUnitAt u x → χ.loc u x = 1`. Unfold `HChar.UnrAt at hχ`. Conclude with `hχ`. Establish `hloc : ∀ x : (HeightOneSpectrum.adicCompletion E w)ˣ, ((compNorm E) χ).loc w x = (χ : Ideles _ →* ℂˣ) (ideleNorm E (localIdele E w x))` using `fun x => rfl`. Establish `hlocF : ∀ y : (HeightOneSpectrum.adicCompletion _ u)ˣ, χ.loc u y = (χ : Ideles _ →* ℂˣ) (localIdele _ u y)` using `fun y => rfl`.

Prove the components needed by the constructor for the conclusion. Unfold `HChar.UnrAt`. Introduce `x hx`. Take `⟨y, hy, hv⟩` from `hN E w x`. Rewrite using `[hloc, hy, ← hlocF]`.

Apply `hunr` to reduce the goal to its premises. Unfold `IsUnitAt at hx ⊢`. Rewrite using `[hv f hf, hx, one_pow]`. Establish `hvw : ((compNorm E) χ).val w = ((compNorm E) χ).loc w (atFin w (unif w))` using `rfl`. Establish `hvu : χ.val u = χ.loc u (atFin u (unif u))` using `rfl`.

Establish `hpw : IsUnifAt w (atFin w (unif w))` using `Classical.choose_spec (exists_unif w)`. Establish `hpu : IsUnifAt u (atFin u (unif u))` using `Classical.choose_spec (exists_unif u)`. Unfold `IsUnifAt at hpw hpu`. Take `⟨y, hy, hv⟩` from `hN E w (atFin w (unif w))`. Rewrite using `[hvw, hvu, hloc, hy, ← hlocF, ← map_pow]`.

Establish `hone : χ.loc u (y * ((atFin u (unif u)) ^ f)⁻¹) = 1`. Apply `hunr` to reduce the goal to its premises. Unfold `IsUnitAt`. Rewrite using `[Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, Units.val_pow_eq_pow_val, map_pow, hv f hf, hpw, hpu, mul_inv_cancel₀]`. Conclude with `pow_ne_zero _ (by simp)`.

Rewrite `hone` using `[map_mul, map_inv, mul_inv_eq_one]`. Conclude with `hone`.
-/
theorem UpperTheory.ideleNorm_valuation_of_local_compatibility :
    UpperTheory.V.Af.Bc.NormLoc → UpperTheory.V.Af.Bc.NormVal := by
  intro hN
  unfold UpperTheory.V.Af.Bc.NormLoc at hN
  unfold UpperTheory.V.Af.Bc.NormVal
  intro E _ _ _ χ w f hf hχ
  set u := HeightOneSpectrum.under (𝓞 ↥(maximalRealSubfield E)) w with hu
  have hunr : ∀ x : (HeightOneSpectrum.adicCompletion _ u)ˣ, IsUnitAt u x → χ.loc u x = 1 := by
    unfold HChar.UnrAt at hχ
    exact hχ
  have hloc : ∀ x : (HeightOneSpectrum.adicCompletion E w)ˣ,
      ((compNorm E) χ).loc w x = (χ : Ideles _ →* ℂˣ) (ideleNorm E (localIdele E w x)) := fun x => rfl
  have hlocF : ∀ y : (HeightOneSpectrum.adicCompletion _ u)ˣ,
      χ.loc u y = (χ : Ideles _ →* ℂˣ) (localIdele _ u y) := fun y => rfl
  constructor
  · unfold HChar.UnrAt
    intro x hx
    obtain ⟨y, hy, hv⟩ := hN E w x
    rw [hloc, hy, ← hlocF]
    apply hunr
    unfold IsUnitAt at hx ⊢
    rw [hv f hf, hx, one_pow]
  · have hvw : ((compNorm E) χ).val w = ((compNorm E) χ).loc w (atFin w (unif w)) := rfl
    have hvu : χ.val u = χ.loc u (atFin u (unif u)) := rfl
    have hpw : IsUnifAt w (atFin w (unif w)) := Classical.choose_spec (exists_unif w)
    have hpu : IsUnifAt u (atFin u (unif u)) := Classical.choose_spec (exists_unif u)
    unfold IsUnifAt at hpw hpu
    obtain ⟨y, hy, hv⟩ := hN E w (atFin w (unif w))
    rw [hvw, hvu, hloc, hy, ← hlocF, ← map_pow]
    have hone : χ.loc u (y * ((atFin u (unif u)) ^ f)⁻¹) = 1 := by
      apply hunr
      unfold IsUnitAt
      rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, Units.val_pow_eq_pow_val, map_pow,
        hv f hf, hpw, hpu, mul_inv_cancel₀]
      exact pow_ne_zero _ (by simp)
    rw [map_mul, map_inv, mul_inv_eq_one] at hone
    exact hone
