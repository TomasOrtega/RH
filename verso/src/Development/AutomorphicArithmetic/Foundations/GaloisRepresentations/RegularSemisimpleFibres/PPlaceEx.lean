import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRationalLocalOperators
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KroneckerRatioReducesToConstModValuation
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `K M Ω _ _ _ _ _ _ _ _ A v hv n P`. Set `f : 𝓞 M →+* A` to `((algebraMap M Ω).comp (algebraMap (𝓞 M) M)).codRestrict A fun x => ReciprocityTheory.Gal.mem_of_isIntegral_int A (map_isIntegral_int (algebraMap M Ω) x.isIntegral_coe)`. Set `I : Ideal (𝓞 M)` to `(IsLocalRing.maximalIdeal A).comap f`. Establish `hmem : ∀ x : 𝓞 M, x ∈ I ↔ A.valuation (algebraMap M Ω (x : M)) < 1` using `fun x => ValuationSubring.valuation_lt_one_iff A (f x)`. Establish `hN0 : Ideal.absNorm v.asIdeal ≠ 0` using `Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot`.

Establish `hval : A.valuation ((Ideal.absNorm v.asIdeal : ℕ) : Ω) < 1`. Establish `h` using `(hv ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 K)).2 (Ideal.absNorm_mem v.asIdeal)`. Simplify using `using h`. Establish `hne : I ≠ ⊥`. Introduce `h0`.

Establish `h1 : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 M) ∈ I` using `(hmem _).2 (by simpa using hval)`. Rewrite `h1` using `[h0, Ideal.mem_bot]`. Conclude with `Nat.cast_ne_zero.2 hN0 h1`. Take `⟨τ, hτ, -⟩` from `GlobalTheory.CuspRep.LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL M n P ⟨I, Ideal.comap_isPrime _ _, hne⟩`. Conclude with `⟨⟨I, Ideal.comap_isPrime _ _, hne⟩, fun x => (hmem x).symm, τ, hτ⟩`.
-/
theorem UpperTheory.Gal.InertialTypesAlt.placeEx :
    PlaceEx := by
  intro K M Ω _ _ _ _ _ _ _ _ A v hv n P
  let f : 𝓞 M →+* A := ((algebraMap M Ω).comp (algebraMap (𝓞 M) M)).codRestrict A fun x =>
    ReciprocityTheory.Gal.mem_of_isIntegral_int A (map_isIntegral_int (algebraMap M Ω) x.isIntegral_coe)
  let I : Ideal (𝓞 M) := (IsLocalRing.maximalIdeal A).comap f
  have hmem : ∀ x : 𝓞 M, x ∈ I ↔ A.valuation (algebraMap M Ω (x : M)) < 1 := fun x =>
    ValuationSubring.valuation_lt_one_iff A (f x)
  have hN0 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  have hval : A.valuation ((Ideal.absNorm v.asIdeal : ℕ) : Ω) < 1 := by
    have h := (hv ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 K)).2 (Ideal.absNorm_mem v.asIdeal)
    simpa using h
  have hne : I ≠ ⊥ := by
    intro h0
    have h1 : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 M) ∈ I := (hmem _).2 (by simpa using hval)
    rw [h0, Ideal.mem_bot] at h1
    exact Nat.cast_ne_zero.2 hN0 h1
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL M n P
    ⟨I, Ideal.comap_isPrime _ _, hne⟩
  exact ⟨⟨I, Ideal.comap_isPrime _ _, hne⟩, fun x => (hmem x).symm, τ, hτ⟩
