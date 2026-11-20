import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.LocallyConstantFinite.LcFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpec

open GlobalTheory.KZ GlobalTheory.K4 Polynomial UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PE

/- English proof (translation)
Introduce `Ω _ _ _ ε X`. Establish `hinj : Function.Injective (pj X)` using `(io X).injective.comp (transcendental_iff_injective.1 (jK_transcendental X))`. Set `φ : RatFunc Ω →+* Kb X` to `IsFractionRing.lift hinj`. Establish `hφ : ∀ p : Polynomial Ω, φ (algebraMap (Polynomial Ω) (RatFunc Ω) p) = pj X p` using `fun p => IsFractionRing.lift_algebraMap hinj p`. Use `⟨φ, hφ, ?_⟩` and prove the remaining obligations.

Establish `hinj0 : Function.Injective (aeval X.jK : Polynomial Ω →ₐ[Ω] X.K).toRingHom` using `transcendental_iff_injective.1 (jK_transcendental X)`. Set `ψ : RatFunc Ω →+* X.K` to `IsFractionRing.lift hinj0`. Establish `hψ : ∀ p : Polynomial Ω, ψ (algebraMap (Polynomial Ω) (RatFunc Ω) p) = aeval X.jK p` using `fun p => IsFractionRing.lift_algebraMap hinj0 p`. Use `letI : Algebra (RatFunc Ω) X.K := ψ.toAlgebra`. Establish `hc : φ = algebraMap (RatFunc Ω) (Kb X)` using `RingHom.ext fun z => by`.

Express the relevant statement in the definitionally equal form `φ z = io X (ψ z)`. Rewrite using `[← RatFunc.num_div_denom z, map_div₀, map_div₀, map_div₀, hφ, hφ, hψ, hψ]`. Both sides reduce to the same expression. Establish `hle : ∀ y ∈ IntermediateField.adjoin Ω {X.jK}, y ∈ ψ.fieldRange` using `fun y hy => by`. Take `⟨r, s, rfl⟩` from `(IntermediateField.mem_adjoin_simple_iff Ω y).1 hy`.

Conclude with `⟨algebraMap _ _ r / algebraMap _ _ s, by rw [map_div₀, hψ, hψ]⟩`. Use `haveI : Algebra.IsAlgebraic (RatFunc Ω) X.K := ⟨fun f => by`. Take `⟨p, hp, he⟩` from `X.alg_j f`. Establish `hl : p.map (algebraMap _ X.K) ∈ lifts ψ`. Rewrite using `[lifts_iff_coeff_lifts]`.

Introduce `n`. Rewrite using `[coeff_map]`. Conclude with `hle _ (p.coeff n).2`. Take `⟨q, hq⟩` from `(mem_lifts _).1 hl`. Use `⟨q, ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `rfl`. Rewrite `hq` using `[Polynomial.map_zero]`. Conclude with `hp ((Polynomial.map_eq_zero _).1 hq.symm)`. Express the relevant statement in the definitionally equal form `eval₂ ψ f q = 0`. Rewrite using `[← eval_map, hq, eval_map]`.

Conclude with `he⟩`. Establish `hA` using `Algebra.IsAlgebraic.trans (RatFunc Ω) X.K (Kb X)`. Use `@Algebra.IsAlgebraic.mk _ _ _ _ φ.toAlgebra fun z => ?_` and prove the remaining obligations. Take `⟨p, hp, he⟩` from `hA.isAlgebraic z`. Use `⟨p, hp, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `eval₂ φ z p = 0`. Rewrite using `[hc]`. Conclude with `he`.
-/
theorem UpperTheory.V.Z.Kato.Sym.PE.alg :
    UpperTheory.V.Z.Kato.Sym.PE.Alg := by
  intro Ω _ _ _ ε X
  have hinj : Function.Injective (pj X) :=
    (io X).injective.comp (transcendental_iff_injective.1 (jK_transcendental X))
  let φ : RatFunc Ω →+* Kb X := IsFractionRing.lift hinj
  have hφ : ∀ p : Polynomial Ω, φ (algebraMap (Polynomial Ω) (RatFunc Ω) p) = pj X p := fun p => IsFractionRing.lift_algebraMap hinj p
  refine ⟨φ, hφ, ?_⟩
  have hinj0 : Function.Injective (aeval X.jK : Polynomial Ω →ₐ[Ω] X.K).toRingHom := transcendental_iff_injective.1 (jK_transcendental X)
  let ψ : RatFunc Ω →+* X.K := IsFractionRing.lift hinj0
  have hψ : ∀ p : Polynomial Ω, ψ (algebraMap (Polynomial Ω) (RatFunc Ω) p) = aeval X.jK p := fun p => IsFractionRing.lift_algebraMap hinj0 p
  letI : Algebra (RatFunc Ω) X.K := ψ.toAlgebra
  have hc : φ = algebraMap (RatFunc Ω) (Kb X) := RingHom.ext fun z => by
    change φ z = io X (ψ z)
    rw [← RatFunc.num_div_denom z, map_div₀, map_div₀, map_div₀, hφ, hφ, hψ, hψ]
    rfl
  have hle : ∀ y ∈ IntermediateField.adjoin Ω {X.jK}, y ∈ ψ.fieldRange := fun y hy => by
    obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff Ω y).1 hy
    exact ⟨algebraMap _ _ r / algebraMap _ _ s, by rw [map_div₀, hψ, hψ]⟩
  haveI : Algebra.IsAlgebraic (RatFunc Ω) X.K := ⟨fun f => by
    obtain ⟨p, hp, he⟩ := X.alg_j f
    have hl : p.map (algebraMap _ X.K) ∈ lifts ψ := by
      rw [lifts_iff_coeff_lifts]
      intro n
      rw [coeff_map]
      exact hle _ (p.coeff n).2
    obtain ⟨q, hq⟩ := (mem_lifts _).1 hl
    refine ⟨q, ?_, ?_⟩
    · rintro rfl
      rw [Polynomial.map_zero] at hq
      exact hp ((Polynomial.map_eq_zero _).1 hq.symm)
    · change eval₂ ψ f q = 0
      rw [← eval_map, hq, eval_map]
      exact he⟩
  have hA := Algebra.IsAlgebraic.trans (RatFunc Ω) X.K (Kb X)
  refine @Algebra.IsAlgebraic.mk _ _ _ _ φ.toAlgebra fun z => ?_
  obtain ⟨p, hp, he⟩ := hA.isAlgebraic z
  refine ⟨p, hp, ?_⟩
  change eval₂ φ z p = 0
  rw [hc]
  exact he
