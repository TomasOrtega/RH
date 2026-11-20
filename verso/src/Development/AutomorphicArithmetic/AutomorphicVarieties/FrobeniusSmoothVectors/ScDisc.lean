import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.UnramIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

/- English proof (translation)
Introduce `Ω _ _ _ l _ K _ _ _ h2 hB`. Use `haveI : Algebra.IsQuadraticExtension ℚ K := ⟨h2⟩`. Use `haveI : IsGalois ℚ K := {}`. Establish `hl : l.Prime` using `Fact.out`. Rewrite using `[← (UpperTheory.V.CF.unramIff).2.1 K l hl, (UpperTheory.V.CF.unramIff).1 K l hl]`.

Introduce `w hw`. Take `⟨A, hA⟩` from `ReciprocityTheory.Gal.exists_isPlaceOver (F := K) Ω w`. Establish `hv : A.valuation (l : Ω) < 1`. Establish `h` using `(hA (l : 𝓞 K)).2 hw`. Simplify using `using h`.

Establish `hI` using `hB A hv`. Rewrite using `[← UpperTheory.V.CF.ineAbs ℚ K Ω A w hA, Subgroup.eq_bot_iff_forall]`. Introduce and unpack `_ ⟨σ, hσ, rfl⟩`. Establish `hσ' : ∀ x : K, σ (algebraMap K Ω x) = algebraMap K Ω x` using `hI hσ`. Use extensionality with `x`.

Apply `(algebraMap K Ω).injective` to reduce the goal to its premises. Use `show algebraMap K Ω (σ.restrictNormal K x) = algebraMap K Ω x`. Rewrite using `[AlgEquiv.restrictNormal_commutes]`. Conclude with `hσ' x`.
-/
theorem UpperTheory.V.Fr.sc_disc :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [NumberField K] [Algebra K Ω], Module.finrank ℚ K = 2 → (∀ B : ValuationSubring Ω, B.valuation (l : Ω) < 1 → Ine (F := ℚ) B ≤ galOf ℚ K Ω) → ¬ (l : ℤ) ∣ discr K := by
  intro Ω _ _ _ l _ K _ _ _ h2 hB
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨h2⟩
  haveI : IsGalois ℚ K := {}
  have hl : l.Prime := Fact.out
  rw [← (UpperTheory.V.CF.unramIff).2.1 K l hl, (UpperTheory.V.CF.unramIff).1 K l hl]
  intro w hw
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver (F := K) Ω w
  have hv : A.valuation (l : Ω) < 1 := by
    have h := (hA (l : 𝓞 K)).2 hw
    simpa using h
  have hI := hB A hv
  rw [← UpperTheory.V.CF.ineAbs ℚ K Ω A w hA, Subgroup.eq_bot_iff_forall]
  rintro _ ⟨σ, hσ, rfl⟩
  have hσ' : ∀ x : K, σ (algebraMap K Ω x) = algebraMap K Ω x := hI hσ
  ext x
  apply (algebraMap K Ω).injective
  show algebraMap K Ω (σ.restrictNormal K x) = algebraMap K Ω x
  rw [AlgEquiv.restrictNormal_commutes]
  exact hσ' x
