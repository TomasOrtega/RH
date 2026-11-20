import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.IneFixRoots

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ l _ A hA m hm g hg`. Establish `hl : l.Prime` using `Fact.out`. Establish `hm0 : m ≠ 0`. Introduce and unpack `rfl`. Rewrite `hm` using `[Nat.coprime_zero_left]`.

Conclude with `hl.one_lt.ne' hm`. Use `haveI : NeZero m := ⟨hm0⟩`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F`. Use `haveI : NeZero (m : Ω) := ⟨Nat.cast_ne_zero.mpr hm0⟩`.

Take `⟨ζ0, hζ0⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω m`. Establish `hmemA : ∀ ξ : Ω, ξ ^ m = 1 → ξ ∈ A`. Introduce `ξ hξ`. Rewrite using `[← ValuationSubring.valuation_le_one_iff]`. Conclude with `(pow_le_one_iff hm0).mp (by rw [← map_pow, hξ, map_one])`.

Establish `hgm : (g ζ0) ^ m = 1` using `by rw [← map_pow, hζ0.pow_eq_one, map_one]`. Take `⟨a, -, ha⟩` from `hζ0.eq_pow_of_pow_eq_one hgm`. Set `g' : A.decompositionSubgroup F` to `⟨g, hg⟩`. Establish `hlm : ((l : A)) ∈ IsLocalRing.maximalIdeal A`. Rewrite using `[ValuationSubring.valuation_lt_one_iff]`.

Simplify using `using hA`. Use `haveI : CharP (IsLocalRing.ResidueField A) l := by`. Rewrite using `[CharP.charP_iff_prime_eq_zero hl]`. Rewrite using `[← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff]`. Conclude with `hlm`.

Use `letI : Algebra (ZMod l) (IsLocalRing.ResidueField A) := ZMod.algebra _ l`. Set `z0 : A` to `⟨ζ0, hmemA ζ0 hζ0.pow_eq_one⟩`. Set `ω : IsLocalRing.ResidueField A` to `IsLocalRing.residue A z0`. Establish `hσω : g' • ω = ω ^ a`. Establish `hz : g' • z0 = z0 ^ a` using `Subtype.ext (by`.

Express the relevant statement in the definitionally equal form `g ζ0 = ζ0 ^ a`. Conclude with `ha.symm)`. Simplify using `only [ω]`. Rewrite using `[← IsLocalRing.ResidueField.residue_smul, hz, map_pow]`. Set `σ : IsLocalRing.ResidueField A →ₐ[ZMod l] IsLocalRing.ResidueField A` to `{ MulSemiringAction.toRingHom _ (IsLocalRing.ResidueField A) g' with commutes' := fun r => RingHom.congr_fun (RingHom.ext_zmod ((MulSemiringAction.toRingHom _ (IsLocalRing.ResidueField A) g').comp (algebraMap (ZMod l) (IsLocalRing.ResidueField A))) (algebraMap (ZMod l) (IsLocalRi …`.

Establish `hσ : ∀ x, σ x = g' • x` using `fun x => rfl`. Set `E` to `IntermediateField.adjoin (ZMod l) ({ω} : Set (IsLocalRing.ResidueField A))`. Establish `hωE : ω ∈ E` using `IntermediateField.mem_adjoin_simple_self _ _`. Establish `hint : IsIntegral (ZMod l) ω`. Use `IsIntegral.of_pow (Nat.pos_of_ne_zero hm0) ?_` and prove the remaining obligations.

Establish `h1 : ω ^ m = 1`. Simplify using `only [ω]`. Rewrite using `[← map_pow]`. Establish `: z0 ^ m = 1` using `Subtype.ext (by`. Express the relevant statement in the definitionally equal form `ζ0 ^ m = 1`.

Conclude with `hζ0.pow_eq_one)`. Rewrite using `[this, map_one]`. Rewrite using `[h1]`. Conclude with `isIntegral_one`. Use `haveI : FiniteDimensional (ZMod l) E := IntermediateField.adjoin.finiteDimensional hint`.

Use `haveI : Finite E := Module.finite_of_finite (ZMod l)`. Establish `hEle : E ≤ IntermediateField.comap σ E`. Rewrite using `[IntermediateField.adjoin_simple_le_iff]`. Use `show σ ω ∈ E`. Rewrite using `[hσ, hσω]`.

Conclude with `pow_mem hωE a`. Establish `hmapE : ∀ x ∈ E, σ x ∈ E` using `fun x hx => hEle hx`. Set `τ : E →ₐ[ZMod l] E` to `{ toFun := fun x => ⟨σ x, hmapE x.1 x.2⟩ map_one' := Subtype.ext (map_one σ) map_mul' := fun x y => Subtype.ext (map_mul σ x.1 y.1) map_zero' := Subtype.ext (map_zero σ) map_add' := fun x y => Subtype.ext (map_add σ x.1 y.1) commutes' := fun r => Subtype.ext (σ.commutes r) }`. Take `⟨n, hn⟩` from `(FiniteField.bijective_frobeniusAlgHom_pow (ZMod l) E).2 τ`. Establish `hτω : τ ⟨ω, hωE⟩ = ⟨ω, hωE⟩ ^ (l ^ (n : ℕ))`.

Rewrite using `[← hn]`. Simplify using `only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card]`. Establish `hres : ω ^ a = ω ^ (l ^ (n : ℕ))`. Establish `h2 : ((τ ⟨ω, hωE⟩ : E) : IsLocalRing.ResidueField A) = σ ω` using `rfl`. Use `congrArg Subtype.val hτω` as an intermediate fact.

Rewrite `this` using `[h2]`. Rewrite using `[← hσω, ← hσ]`. Simplify using `using this`. Establish `hfin : g ζ0 = ζ0 ^ (l ^ (n : ℕ))`. Rewrite using `[← ha]`.

Establish `hroot : (ζ0 ^ (l ^ (n : ℕ))) ^ m = 1`. Rewrite using `[← pow_mul, mul_comm, pow_mul, hζ0.pow_eq_one, one_pow]`. Establish `hroota : (ζ0 ^ a) ^ m = 1`. Rewrite using `[← pow_mul, mul_comm, pow_mul, hζ0.pow_eq_one, one_pow]`. Use `(UpperTheory.V.LDataCardLeFinrank.ineFixRoots F Ω l A hA m hm _ hroot).1 _ hroota ?_` and prove the remaining obligations.

Establish `hsub : (z0 ^ a - z0 ^ (l ^ (n : ℕ))) ∈ IsLocalRing.maximalIdeal A`. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, map_pow, sub_eq_zero]`. Conclude with `hres`. Rewrite `hsub` using `[ValuationSubring.valuation_lt_one_iff]`. Simplify using `using hsub`.

Use `⟨n, fun ζ hζ => ?_⟩` and prove the remaining obligations. Take `⟨j, -, rfl⟩` from `hζ0.eq_pow_of_pow_eq_one hζ`. Rewrite using `[map_pow, hfin, ← pow_mul, ← pow_mul, mul_comm]`.
-/
theorem UpperTheory.V.LDataCardLeFinrank.decActRoots :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∀ (m : ℕ), m.Coprime l → ∀ g ∈ Dec (F := F) A, ∃ k : ℕ, ∀ ζ : Ω, ζ ^ m = 1 → g ζ = ζ ^ l ^ k := by
  intro F Ω _ _ _ _ _ l _ A hA m hm g hg
  have hl : l.Prime := Fact.out
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hm
    exact hl.one_lt.ne' hm
  haveI : NeZero m := ⟨hm0⟩
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : NeZero (m : Ω) := ⟨Nat.cast_ne_zero.mpr hm0⟩
  obtain ⟨ζ0, hζ0⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  have hmemA : ∀ ξ : Ω, ξ ^ m = 1 → ξ ∈ A := by
    intro ξ hξ
    rw [← ValuationSubring.valuation_le_one_iff]
    exact (pow_le_one_iff hm0).mp (by rw [← map_pow, hξ, map_one])
  have hgm : (g ζ0) ^ m = 1 := by rw [← map_pow, hζ0.pow_eq_one, map_one]
  obtain ⟨a, -, ha⟩ := hζ0.eq_pow_of_pow_eq_one hgm
  let g' : A.decompositionSubgroup F := ⟨g, hg⟩
  have hlm : ((l : A)) ∈ IsLocalRing.maximalIdeal A := by
    rw [ValuationSubring.valuation_lt_one_iff]
    simpa using hA
  haveI : CharP (IsLocalRing.ResidueField A) l := by
    rw [CharP.charP_iff_prime_eq_zero hl]
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff]
    exact hlm
  letI : Algebra (ZMod l) (IsLocalRing.ResidueField A) := ZMod.algebra _ l
  let z0 : A := ⟨ζ0, hmemA ζ0 hζ0.pow_eq_one⟩
  let ω : IsLocalRing.ResidueField A := IsLocalRing.residue A z0
  have hσω : g' • ω = ω ^ a := by
    have hz : g' • z0 = z0 ^ a := Subtype.ext (by
      change g ζ0 = ζ0 ^ a
      exact ha.symm)
    simp only [ω]
    rw [← IsLocalRing.ResidueField.residue_smul, hz, map_pow]
  let σ : IsLocalRing.ResidueField A →ₐ[ZMod l] IsLocalRing.ResidueField A :=
    { MulSemiringAction.toRingHom _ (IsLocalRing.ResidueField A) g' with
      commutes' := fun r => RingHom.congr_fun (RingHom.ext_zmod
        ((MulSemiringAction.toRingHom _ (IsLocalRing.ResidueField A) g').comp
          (algebraMap (ZMod l) (IsLocalRing.ResidueField A)))
        (algebraMap (ZMod l) (IsLocalRing.ResidueField A))) r }
  have hσ : ∀ x, σ x = g' • x := fun x => rfl
  let E := IntermediateField.adjoin (ZMod l) ({ω} : Set (IsLocalRing.ResidueField A))
  have hωE : ω ∈ E := IntermediateField.mem_adjoin_simple_self _ _
  have hint : IsIntegral (ZMod l) ω := by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero hm0) ?_
    have h1 : ω ^ m = 1 := by
      simp only [ω]
      rw [← map_pow]
      have : z0 ^ m = 1 := Subtype.ext (by
        change ζ0 ^ m = 1
        exact hζ0.pow_eq_one)
      rw [this, map_one]
    rw [h1]
    exact isIntegral_one
  haveI : FiniteDimensional (ZMod l) E := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite E := Module.finite_of_finite (ZMod l)
  have hEle : E ≤ IntermediateField.comap σ E := by
    rw [IntermediateField.adjoin_simple_le_iff]
    show σ ω ∈ E
    rw [hσ, hσω]
    exact pow_mem hωE a
  have hmapE : ∀ x ∈ E, σ x ∈ E := fun x hx => hEle hx
  let τ : E →ₐ[ZMod l] E :=
    { toFun := fun x => ⟨σ x, hmapE x.1 x.2⟩
      map_one' := Subtype.ext (map_one σ)
      map_mul' := fun x y => Subtype.ext (map_mul σ x.1 y.1)
      map_zero' := Subtype.ext (map_zero σ)
      map_add' := fun x y => Subtype.ext (map_add σ x.1 y.1)
      commutes' := fun r => Subtype.ext (σ.commutes r) }
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod l) E).2 τ
  have hτω : τ ⟨ω, hωE⟩ = ⟨ω, hωE⟩ ^ (l ^ (n : ℕ)) := by
    rw [← hn]
    simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card]
  have hres : ω ^ a = ω ^ (l ^ (n : ℕ)) := by
    have h2 : ((τ ⟨ω, hωE⟩ : E) : IsLocalRing.ResidueField A) = σ ω := rfl
    have := congrArg Subtype.val hτω
    rw [h2] at this
    rw [← hσω, ← hσ]
    simpa using this
  have hfin : g ζ0 = ζ0 ^ (l ^ (n : ℕ)) := by
    rw [← ha]
    have hroot : (ζ0 ^ (l ^ (n : ℕ))) ^ m = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ0.pow_eq_one, one_pow]
    have hroota : (ζ0 ^ a) ^ m = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ0.pow_eq_one, one_pow]
    refine (UpperTheory.V.LDataCardLeFinrank.ineFixRoots F Ω l A hA m hm _ hroot).1 _ hroota ?_
    have hsub : (z0 ^ a - z0 ^ (l ^ (n : ℕ))) ∈ IsLocalRing.maximalIdeal A := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, map_pow, sub_eq_zero]
      exact hres
    rw [ValuationSubring.valuation_lt_one_iff] at hsub
    simpa using hsub
  refine ⟨n, fun ζ hζ => ?_⟩
  obtain ⟨j, -, rfl⟩ := hζ0.eq_pow_of_pow_eq_one hζ
  rw [map_pow, hfin, ← pow_mul, ← pow_mul, mul_comm]
