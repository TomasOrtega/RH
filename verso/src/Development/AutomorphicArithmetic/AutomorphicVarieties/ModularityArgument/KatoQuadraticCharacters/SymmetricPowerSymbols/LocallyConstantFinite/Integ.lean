import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.LocallyConstantFinite.LcFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpec

open GlobalTheory.KZ GlobalTheory.K4 Polynomial UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PE

/- English proof (translation)
Introduce `Ω _ _ _ ε X m hm u z hu hz`. Establish `key : ∀ w : X.K, IsU X w → (pj X).IsIntegralElem (io X w)`. Introduce `w hw`. Set `φ : Polynomial Ω →+* X.K` to `(aeval X.jK).toRingHom`. Establish `hmem : w ∈ (integralClosure (Subring.closure (φ.range : Set X.K)) X.K).toSubring`.

Rewrite using `[← iInf_valuationSubring_superset, Subring.mem_iInf]`. Introduce and unpack `⟨V, hV⟩`. Establish `hov : X.OverY V` using `⟨fun c => hV ⟨C c, by simp [φ]⟩, hV ⟨Polynomial.X, by simp [φ]⟩⟩`. Conclude with `(V.valuation_le_one_iff w).1 (hw.2 V hov).le`. Take `⟨p, hp, hpw⟩` from `hmem`.

Establish `hle : Subring.closure (φ.range : Set X.K) ≤ φ.range` using `Subring.closure_le.2 subset_rfl`. Establish `hlift : p.map (algebraMap (Subring.closure (φ.range : Set X.K)) X.K) ∈ lifts φ`. Rewrite using `[lifts_iff_coeff_lifts]`. Introduce `n`. Rewrite using `[coeff_map]`.

Conclude with `RingHom.mem_range.1 (hle (p.coeff n).2)`. Take `⟨Q, hQ, -, hQm⟩` from `lifts_and_degree_eq_and_monic hlift (hp.map _)`. Use `⟨Q, hQm, ?_⟩` and prove the remaining obligations. Use `show eval₂ ((io X).comp φ) (io X w) Q = 0`. Rewrite using `[← hom_eval₂, ← eval_map, hQ, eval_map, hpw, _root_.map_zero]`.

Establish `hu0 : io X u ≠ 0` using `(_root_.map_ne_zero _).2 hu.1`. Establish `hz0 : z ≠ 0`. Introduce and unpack `rfl`. Rewrite `hz` using `[zero_pow hm.ne']`. Conclude with `hu0 hz.symm`.

Establish `hinv : IsU X u⁻¹` using `⟨inv_ne_zero hu.1, fun W hW => by rw [map_inv₀, hu.2 W hW, inv_one]⟩`. Use `⟨hz0, ?_, ?_⟩` and prove the remaining obligations. Use `letI := (pj X).toAlgebra`. Use `IsIntegral.of_pow hm ?_` and prove the remaining obligations. Rewrite using `[hz]`.

Conclude with `key u hu`. Use `letI := (pj X).toAlgebra`. Use `IsIntegral.of_pow hm ?_` and prove the remaining obligations. Rewrite using `[inv_pow, hz, ← map_inv₀]`. Conclude with `key _ hinv`.
-/
theorem UpperTheory.V.Z.Kato.Sym.PE.integ :
    UpperTheory.V.Z.Kato.Sym.PE.Integ := by
  intro Ω _ _ _ ε X m hm u z hu hz
  have key : ∀ w : X.K, IsU X w → (pj X).IsIntegralElem (io X w) := by
    intro w hw
    let φ : Polynomial Ω →+* X.K := (aeval X.jK).toRingHom
    have hmem : w ∈ (integralClosure (Subring.closure (φ.range : Set X.K)) X.K).toSubring := by
      rw [← iInf_valuationSubring_superset, Subring.mem_iInf]
      rintro ⟨V, hV⟩
      have hov : X.OverY V := ⟨fun c => hV ⟨C c, by simp [φ]⟩, hV ⟨Polynomial.X, by simp [φ]⟩⟩
      exact (V.valuation_le_one_iff w).1 (hw.2 V hov).le
    obtain ⟨p, hp, hpw⟩ := hmem
    have hle : Subring.closure (φ.range : Set X.K) ≤ φ.range := Subring.closure_le.2 subset_rfl
    have hlift : p.map (algebraMap (Subring.closure (φ.range : Set X.K)) X.K) ∈ lifts φ := by
      rw [lifts_iff_coeff_lifts]
      intro n
      rw [coeff_map]
      exact RingHom.mem_range.1 (hle (p.coeff n).2)
    obtain ⟨Q, hQ, -, hQm⟩ := lifts_and_degree_eq_and_monic hlift (hp.map _)
    refine ⟨Q, hQm, ?_⟩
    show eval₂ ((io X).comp φ) (io X w) Q = 0
    rw [← hom_eval₂, ← eval_map, hQ, eval_map, hpw, _root_.map_zero]
  have hu0 : io X u ≠ 0 := (_root_.map_ne_zero _).2 hu.1
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hz
    exact hu0 hz.symm
  have hinv : IsU X u⁻¹ := ⟨inv_ne_zero hu.1, fun W hW => by rw [map_inv₀, hu.2 W hW, inv_one]⟩
  refine ⟨hz0, ?_, ?_⟩
  · letI := (pj X).toAlgebra
    refine IsIntegral.of_pow hm ?_
    rw [hz]
    exact key u hu
  · letI := (pj X).toAlgebra
    refine IsIntegral.of_pow hm ?_
    rw [inv_pow, hz, ← map_inv₀]
    exact key _ hinv
