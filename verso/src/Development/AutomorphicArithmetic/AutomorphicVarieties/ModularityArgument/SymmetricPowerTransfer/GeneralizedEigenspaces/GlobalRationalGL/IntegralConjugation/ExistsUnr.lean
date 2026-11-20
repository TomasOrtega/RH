import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.LocBase
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.HsLaw

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.Dict.Br.QuadraticCharacterExistence

open scoped WithZero

/- English proof (translation)
Set `w : HeightOneSpectrum O` to `IsDiscreteValuationRing.maximalIdeal O`. Set `f : Kˣ →* Multiplicative ℤ` to `(WithZero.unitsWithZeroEquiv (α := Multiplicative ℤ)).toMonoidHom.comp (Units.map ((w.valuation K : Valuation K ℤᵐ⁰) : K →* ℤᵐ⁰))`. Establish `hf : ∀ (x : Kˣ) (n : Multiplicative ℤ), w.valuation K (x : K) = (n : ℤᵐ⁰) → f x = n`. Introduce `x n h`. Apply `WithZero.coe_injective` to reduce the goal to its premises.

Conclude with `(WithZero.coe_unitsWithZeroEquiv_eq_units_val _).trans h`. Use `⟨(zpowersHom ℂˣ c⁻¹).comp f, fun u => ?_, fun ϖ x hϖ hx => ?_⟩` and prove the remaining obligations. Establish `h1 : w.valuation K (Units.map (algebraMap O K : O →* K) u : K) = ((1 : Multiplicative ℤ) : ℤᵐ⁰)`. Rewrite using `[Units.coe_map, MonoidHom.coe_coe, HeightOneSpectrum.valuation_of_algebraMap, WithZero.coe_one, HeightOneSpectrum.intValuation_eq_one_iff]`. Conclude with `fun h => (IsLocalRing.mem_maximalIdeal _).1 h u.isUnit`.

Rewrite using `[MonoidHom.comp_apply, hf _ _ h1, map_one]`. Establish `h1 : w.valuation K (x : K) = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : ℤᵐ⁰)`. Rewrite using `[hx, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_singleton _ hϖ.ne_zero hϖ.maximalIdeal_eq]`. Both sides reduce to the same expression. Rewrite using `[MonoidHom.comp_apply, hf _ _ h1]`.

Simplify using `[zpowersHom_apply]`.
-/
private theorem exists_unr {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] (c : ℂˣ) :
    ∃ χ : Kˣ →* ℂˣ, (∀ u : Oˣ, χ (Units.map (algebraMap O K : O →* K) u) = 1) ∧
      ∀ (ϖ : O) (x : Kˣ), Irreducible ϖ → (x : K) = algebraMap O K ϖ → χ x = c := by
  let w : HeightOneSpectrum O := IsDiscreteValuationRing.maximalIdeal O
  let f : Kˣ →* Multiplicative ℤ :=
    (WithZero.unitsWithZeroEquiv (α := Multiplicative ℤ)).toMonoidHom.comp
      (Units.map ((w.valuation K : Valuation K ℤᵐ⁰) : K →* ℤᵐ⁰))
  have hf : ∀ (x : Kˣ) (n : Multiplicative ℤ), w.valuation K (x : K) = (n : ℤᵐ⁰) → f x = n := by
    intro x n h
    apply WithZero.coe_injective
    exact (WithZero.coe_unitsWithZeroEquiv_eq_units_val _).trans h
  refine ⟨(zpowersHom ℂˣ c⁻¹).comp f, fun u => ?_, fun ϖ x hϖ hx => ?_⟩
  · have h1 : w.valuation K (Units.map (algebraMap O K : O →* K) u : K) = ((1 : Multiplicative ℤ) : ℤᵐ⁰) := by
      rw [Units.coe_map, MonoidHom.coe_coe, HeightOneSpectrum.valuation_of_algebraMap, WithZero.coe_one,
        HeightOneSpectrum.intValuation_eq_one_iff]
      exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h u.isUnit
    rw [MonoidHom.comp_apply, hf _ _ h1, map_one]
  · have h1 : w.valuation K (x : K) = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : ℤᵐ⁰) := by
      rw [hx, HeightOneSpectrum.valuation_of_algebraMap,
        HeightOneSpectrum.intValuation_singleton _ hϖ.ne_zero hϖ.maximalIdeal_eq]
      rfl
    rw [MonoidHom.comp_apply, hf _ _ h1]
    simp [zpowersHom_apply]

/- English proof (translation)
Introduce `h`. Establish `h1 : (QuadraticAlgebra.omega : Lsq (Lp L) R.Δ) * QuadraticAlgebra.omega = 0`. Apply the tactic sequence `ext <;> simp [h]`. Establish `h2 : R.e QuadraticAlgebra.omega = 0`. Use `congrArg R.e h1` as an intermediate fact.

Rewrite `this` using `[map_mul, map_zero]`. Conclude with `mul_self_eq_zero.1 this`. Establish `h3 : (QuadraticAlgebra.omega : Lsq (Lp L) R.Δ) = 0`. Conclude with `(map_eq_zero_iff R.e R.e.injective).1 h2`. Use `congrArg QuadraticAlgebra.im h3` as an intermediate fact.

Simplify using `at this`.
-/
private theorem delta_ne {L : Type} [Field L] [NumberField L] [IsCMField L] (R : RingBr L) : R.Δ ≠ 0 := by
  intro h
  have h1 : (QuadraticAlgebra.omega : Lsq (Lp L) R.Δ) * QuadraticAlgebra.omega = 0 := by
    ext <;> simp [h]
  have h2 : R.e QuadraticAlgebra.omega = 0 := by
    have := congrArg R.e h1
    rw [map_mul, map_zero] at this
    exact mul_self_eq_zero.1 this
  have h3 : (QuadraticAlgebra.omega : Lsq (Lp L) R.Δ) = 0 := by
    exact (map_eq_zero_iff R.e R.e.injective).1 h2
  have := congrArg QuadraticAlgebra.im h3
  simp at this

/- English proof (translation)
Take `⟨r, rfl⟩` from `h`. Establish `hr : r ≠ 0` using `fun e => h0 (by rw [e, mul_zero])`. Use `if_pos ⟨(x + 1) / 2, (x - 1) / (2 * r), ?_⟩` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem hs_one {K : Type} [Field K] [CharZero K] {D : K} (h0 : D ≠ 0) (h : IsSquare D) (x : K) : hs D x = 1 := by
  obtain ⟨r, rfl⟩ := h
  have hr : r ≠ 0 := fun e => h0 (by rw [e, mul_zero])
  refine if_pos ⟨(x + 1) / 2, (x - 1) / (2 * r), ?_⟩
  field_simp
  ring

/- English proof (translation)
Use `haveI := L.frac`. Take `⟨ε, s, hs0, rfl⟩` from `L.even`. Establish `hp' : algebraMap O K p ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hp.ne_zero`. Use `if_neg fun ⟨a, b, e⟩ => L.not_even hp ?_` and prove the remaining obligations. Establish `e' : a ^ 2 - algebraMap O K ε * (s * b) ^ 2 = algebraMap O K p` using `by rw [← e]; ring`.

Conclude with `e' ▸ L.even_of_norm ε (fun ⟨r, hr⟩ => hD ⟨r * s, by rw [hr]; ring⟩) (e' ▸ hp')`.
-/
private theorem hs_neg {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    {D : K} (L : IsLoc O D) (hD : ¬ IsSquare D) {p : O} (hp : Irreducible p) : hs D (algebraMap O K p) = -1 := by
  haveI := L.frac
  obtain ⟨ε, s, hs0, rfl⟩ := L.even
  have hp' : algebraMap O K p ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hp.ne_zero
  refine if_neg fun ⟨a, b, e⟩ => L.not_even hp ?_
  have e' : a ^ 2 - algebraMap O K ε * (s * b) ^ 2 = algebraMap O K p := by rw [← e]; ring
  exact e' ▸ L.even_of_norm ε (fun ⟨r, hr⟩ => hD ⟨r * s, by rw [hr]; ring⟩) (e' ▸ hp')

end UpperTheory.V.Z.Sym.Dict.Br.QuadraticCharacterExistence

open UpperTheory.V.Z.Sym.Dict.Br.QuadraticCharacterExistence in
/- English proof (translation)
Introduce `L _ _ _ R`. Establish `key : ∀ v : Pl (Lp L), ∃ χ : (Kv v)ˣ →* ℂˣ, (2 : 𝓞 (Lp L)) ∉ v.asIdeal ∨ IsSquare (cv v R.Δ) → IsChi (Ov v) (cv v R.Δ) χ`. Introduce `v`. Take `⟨hf, -, hfin, -⟩` from `locBase (Lp L) v`. Use `haveI := hf`.

Use `haveI := hfin`. Establish `hq : (Nat.card (IsLocalRing.ResidueField (Ov v)) : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Nat.card_pos.ne'`. Distinguish the cases in `hsq : IsSquare (cv v R.Δ)`. Use `haveI : CharZero (Kv v) := charZero_of_injective_ringHom (cv v).injective`. Establish `hΔ : cv v R.Δ ≠ 0` using `(map_ne_zero _).2 (delta_ne R)`.

Take `⟨χ, h1, h2⟩` from `exists_unr (O := Ov v) (K := Kv v) (Units.mk0 _ (div_ne_zero one_ne_zero hq))`. Use `⟨χ, fun _ => ⟨h1, fun ϖ x hϖ hx => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[h2 ϖ x hϖ hx, hs_one hΔ hsq]`. Both sides reduce to the same expression. Take `⟨χ, h1, h2⟩` from `exists_unr (O := Ov v) (K := Kv v) (Units.mk0 _ (div_ne_zero (neg_ne_zero.2 one_ne_zero) hq))`.

Use `⟨χ, fun h => ⟨h1, fun ϖ x hϖ hx => ?_⟩⟩` and prove the remaining obligations. Establish `hL` using `R.loc v (h.resolve_right hsq)`. Rewrite using `[h2 ϖ x hϖ hx, hx, hs_neg hL hsq hϖ]`. Both sides reduce to the same expression. Use `choose χ hχ using key`.

Conclude with `⟨χ, hχ⟩`.
-/
theorem UpperTheory.V.Z.Sym.Dict.Br.chiEx :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (R : RingBr L), ∃ χ : ∀ v : Pl (Lp L), (Kv v)ˣ →* ℂˣ, (∀ v : Pl (Lp L), (2 : 𝓞 (Lp L)) ∉ v.asIdeal ∨ IsSquare (cv v R.Δ) → IsChi (Ov v) (cv v R.Δ) (χ v)) := by
  intro L _ _ _ R
  have key : ∀ v : Pl (Lp L), ∃ χ : (Kv v)ˣ →* ℂˣ,
      (2 : 𝓞 (Lp L)) ∉ v.asIdeal ∨ IsSquare (cv v R.Δ) → IsChi (Ov v) (cv v R.Δ) χ := by
    intro v
    obtain ⟨hf, -, hfin, -⟩ := locBase (Lp L) v
    haveI := hf
    haveI := hfin
    have hq : (Nat.card (IsLocalRing.ResidueField (Ov v)) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 Nat.card_pos.ne'
    by_cases hsq : IsSquare (cv v R.Δ)
    · haveI : CharZero (Kv v) := charZero_of_injective_ringHom (cv v).injective
      have hΔ : cv v R.Δ ≠ 0 := (map_ne_zero _).2 (delta_ne R)
      obtain ⟨χ, h1, h2⟩ := exists_unr (O := Ov v) (K := Kv v) (Units.mk0 _ (div_ne_zero one_ne_zero hq))
      refine ⟨χ, fun _ => ⟨h1, fun ϖ x hϖ hx => ?_⟩⟩
      rw [h2 ϖ x hϖ hx, hs_one hΔ hsq]
      rfl
    · obtain ⟨χ, h1, h2⟩ := exists_unr (O := Ov v) (K := Kv v)
        (Units.mk0 _ (div_ne_zero (neg_ne_zero.2 one_ne_zero) hq))
      refine ⟨χ, fun h => ⟨h1, fun ϖ x hϖ hx => ?_⟩⟩
      have hL := R.loc v (h.resolve_right hsq)
      rw [h2 ϖ x hϖ hx, hx, hs_neg hL hsq hϖ]
      rfl
  choose χ hχ using key
  exact ⟨χ, hχ⟩
