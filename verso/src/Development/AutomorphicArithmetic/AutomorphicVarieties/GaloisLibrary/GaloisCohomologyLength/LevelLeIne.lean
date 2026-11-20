import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDecompositionGroupCyclotomicCharacterZpowN
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.IneFixRoots
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ClassIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ClassFix

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ N _ K _ _ _ φ l _ v A hv hA u hu`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F`. Use `haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic`. Use `haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω`.

Use `haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩`. Take `⟨h, ⟨hF, hI⟩, hh⟩` from `KStar.TotallyRealRoots.mem_levelGroup.mp hu`. Establish `hl : A.valuation (l : Ω) < 1`. Use `(hA (l : 𝓞 F)).mpr hv` as an intermediate fact. Simplify using `using this`.

Take `⟨σ, hσI, hσu⟩` from `GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hl u`. Establish `hcop : (N / l ^ N.factorization l).Coprime l` using `(Nat.coprime_ordCompl (Fact.out : l.Prime) (NeZero.ne N)).symm`. Establish `hpos : 0 < N / l ^ N.factorization l` using `Nat.ordCompl_pos l (NeZero.ne N)`. Establish `hfixm : ∀ ζ : Ω, ζ ^ (N / l ^ N.factorization l) = 1 → σ ζ = ζ` using `fun ζ hζ => (ineFixRoots ℚ Ω l A hl _ hcop ζ hζ).2 σ hσI`. Establish `hroots : ∀ ζ : Ω, ζ ^ N = 1 → σ.toRingEquiv ζ = ζ ^ (h : ZMod N).val`.

Rewrite using `[classIff Ω l N σ.toRingEquiv h]`. Use `⟨fun ζ hζ => ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : (ZMod.unitsMap (Nat.ordCompl_dvd N l)) h = 1` using `hI`. Establish `e : σ.toRingEquiv ζ = ζ` using `hfixm ζ hζ`. Rewrite using `[e, h1, Units.val_one]`.

Break down `Nat.lt_or_ge 1 (N / l ^ N.factorization l) with hm | hm` into its components or cases. Use `haveI : Fact (1 < N / l ^ N.factorization l) := ⟨hm⟩`. Rewrite using `[ZMod.val_one, pow_one]`. Establish `hm1 : N / l ^ N.factorization l = 1` using `by omega`. Rewrite `hζ` using `[hm1, pow_one]`.

Rewrite using `[hζ, one_pow]`. Rewrite using `[hh]`. Use `congr 1`. Conclude with `hσu.symm`. Establish `hfixF : ∀ x : F, σ.toRingEquiv (algebraMap F Ω x) = algebraMap F Ω x` using `(classFix F Ω N K φ σ.toRingEquiv h hroots).mpr hF`.

Set `τ : Ω ≃ₐ[F] Ω` to `{ σ.toRingEquiv with commutes' := hfixF }`. Use `⟨τ, ⟨?_, fun x hx => hσI.2 x hx⟩, ?_⟩` and prove the remaining obligations. Conclude with `hσI.1`. Rewrite using `[← hσu]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.LDataCardLeFinrank.levelLeIne :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (N : ℕ) [NeZero N] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {N} ℚ K] (φ : F →ₐ[ℚ] K) (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), v ∈ Above F l → IsPlaceOver A v → KStar.TotallyRealRoots.levelGroup l N (KStar.TotallyRealRoots.fieldSubgroup N K φ.fieldRange ⊓ KStar.TotallyRealRoots.levelInertia l N) ≤ ineImage F l A := by
  intro F Ω _ _ _ _ _ N _ K _ _ _ φ l _ v A hv hA u hu
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω
  haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  obtain ⟨h, ⟨hF, hI⟩, hh⟩ := KStar.TotallyRealRoots.mem_levelGroup.mp hu
  have hl : A.valuation (l : Ω) < 1 := by
    have := (hA (l : 𝓞 F)).mpr hv
    simpa using this
  obtain ⟨σ, hσI, hσu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hl u
  have hcop : (N / l ^ N.factorization l).Coprime l :=
    (Nat.coprime_ordCompl (Fact.out : l.Prime) (NeZero.ne N)).symm
  have hpos : 0 < N / l ^ N.factorization l := Nat.ordCompl_pos l (NeZero.ne N)
  have hfixm : ∀ ζ : Ω, ζ ^ (N / l ^ N.factorization l) = 1 → σ ζ = ζ := fun ζ hζ =>
    (ineFixRoots ℚ Ω l A hl _ hcop ζ hζ).2 σ hσI
  have hroots : ∀ ζ : Ω, ζ ^ N = 1 → σ.toRingEquiv ζ = ζ ^ (h : ZMod N).val := by
    rw [classIff Ω l N σ.toRingEquiv h]
    refine ⟨fun ζ hζ => ?_, ?_⟩
    · have h1 : (ZMod.unitsMap (Nat.ordCompl_dvd N l)) h = 1 := hI
      have e : σ.toRingEquiv ζ = ζ := hfixm ζ hζ
      rw [e, h1, Units.val_one]
      rcases Nat.lt_or_ge 1 (N / l ^ N.factorization l) with hm | hm
      · haveI : Fact (1 < N / l ^ N.factorization l) := ⟨hm⟩
        rw [ZMod.val_one, pow_one]
      · have hm1 : N / l ^ N.factorization l = 1 := by omega
        rw [hm1, pow_one] at hζ
        rw [hζ, one_pow]
    · rw [hh]
      congr 1
      exact hσu.symm
  have hfixF : ∀ x : F, σ.toRingEquiv (algebraMap F Ω x) = algebraMap F Ω x :=
    (classFix F Ω N K φ σ.toRingEquiv h hroots).mpr hF
  let τ : Ω ≃ₐ[F] Ω := { σ.toRingEquiv with commutes' := hfixF }
  refine ⟨τ, ⟨?_, fun x hx => hσI.2 x hx⟩, ?_⟩
  · exact hσI.1
  · rw [← hσu]
    rfl
