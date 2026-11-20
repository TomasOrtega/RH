import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `L _ _ _ P hU v`. Establish `hval : ∀ x : Lp L, Valued.v (cv v x) = v.valuation (Lp L) x` using `fun x => IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x`. Establish `hδ : P.e QuadraticAlgebra.omega * P.e QuadraticAlgebra.omega = algebraMap (Lp L) L P.Δ`. Rewrite using `[← map_mul, QuadraticAlgebra.omega_mul_omega_eq_algebraMap, map_zero, zero_mul, add_zero, P.e_alg]`. Establish `hδ0 : P.e QuadraticAlgebra.omega ≠ 0`.

Introduce `h0`. Establish `h1 : (QuadraticAlgebra.omega : Lsq (Lp L) P.Δ) = 0` using `P.e.injective (by rw [h0, map_zero])`. Establish `h2` using `congrArg QuadraticAlgebra.im h1`. Simplify using `at h2`. Use `haveI := v.isMaximal`.

Take `⟨Q, hQm, hQl⟩` from `Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) v.asIdeal`. Establish `hQ0 : Q ≠ ⊥`. Introduce and unpack `rfl`. Apply `v.ne_bot` to reduce the goal to its premises. Rewrite using `[hQl.over, Ideal.under, Ideal.comap_bot_of_injective]`.

Conclude with `FaithfulSMul.algebraMap_injective _ _`. Set `w : HeightOneSpectrum (𝓞 L)` to `⟨Q, hQm.isPrime, hQ0⟩`. Use `haveI : w.asIdeal.LiesOver v.asIdeal := hQl`. Establish `hr : v.asIdeal.ramificationIdx' w.asIdeal = 1` using `by haveI := hU w haveI : w.asIdeal.IsPrime := w.isPrime`. Rewrite using `[Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot]`.

Conclude with `Ideal.ramificationIdx_eq_one_of_isUnramifiedAt`. Establish `hv` using `IsDedekindDomain.HeightOneSpectrum.valuation_liesOver L v w P.Δ`. Rewrite `hv` using `[hr, pow_one, ← hδ, map_mul]`. Establish `hw0 : w.valuation L (P.e QuadraticAlgebra.omega) ≠ 0` using `by simpa using hδ0`. Take `⟨π, hπ⟩` from `v.valuation_exists_uniformizer (Lp L)`.

Establish `hπ0 : π ≠ 0`. Introduce `h0`. Rewrite `hπ` using `[h0, map_zero]`. Conclude with `WithZero.zero_ne_coe hπ`. Set `t : Lp L` to `π ^ (-WithZero.log (w.valuation L (P.e QuadraticAlgebra.omega)))`.

Establish `ht0 : t ≠ 0` using `zpow_ne_zero _ hπ0`. Establish `ht : v.valuation (Lp L) t = w.valuation L (P.e QuadraticAlgebra.omega)`. Simplify using `only [t, map_zpow₀, hπ, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one, neg_neg]`. Conclude with `WithZero.exp_log hw0`. Establish `hu1 : Valued.v (cv v (P.Δ / t ^ 2)) = 1`.

Rewrite using `[hval, map_div₀, map_pow, ht, hv, sq]`. Conclude with `div_self (mul_ne_zero hw0 hw0)`. Establish `hu2 : Valued.v (cv v (P.Δ / t ^ 2)⁻¹) = 1`. Rewrite using `[hval, map_inv₀, ← hval, hu1, inv_one]`. Establish `hne : P.Δ / t ^ 2 ≠ 0` using `div_ne_zero (by`.

Introduce `h0`. Apply `hδ0` to reduce the goal to its premises. Conclude with `mul_self_eq_zero.mp (by rw [hδ, h0, map_zero])) (pow_ne_zero _ ht0)`. Use `⟨⟨⟨cv v (P.Δ / t ^ 2), le_of_eq hu1⟩, ⟨cv v (P.Δ / t ^ 2)⁻¹, le_of_eq hu2⟩, ?_, ?_⟩, cv v t, (map_ne_zero (cv v)).2 ht0, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext show cv v (P.Δ / t ^ 2) * cv v (P.Δ / t ^ 2)⁻¹ = 1` to reduce the goal to its premises.

Rewrite using `[← map_mul, mul_inv_cancel₀ hne, map_one]`. Apply `Subtype.ext show cv v (P.Δ / t ^ 2)⁻¹ * cv v (P.Δ / t ^ 2) = 1` to reduce the goal to its premises. Rewrite using `[← map_mul, inv_mul_cancel₀ hne, map_one]`. Use `show cv v P.Δ = cv v (P.Δ / t ^ 2) * cv v t ^ 2`. Rewrite using `[← map_pow, ← map_mul, div_mul_cancel₀ _ (pow_ne_zero _ ht0)]`.
-/
theorem UpperTheory.V.Z.Sym.Dict.Br.evenVal :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (P : Pre L), Dict.Unr L → ∀ v : Pl (Lp L), EvenVal (Ov v) (cv v P.Δ) := by
  intro L _ _ _ P hU v
  have hval : ∀ x : Lp L, Valued.v (cv v x) = v.valuation (Lp L) x := fun x =>
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  have hδ : P.e QuadraticAlgebra.omega * P.e QuadraticAlgebra.omega = algebraMap (Lp L) L P.Δ := by
    rw [← map_mul, QuadraticAlgebra.omega_mul_omega_eq_algebraMap, map_zero, zero_mul, add_zero,
      P.e_alg]
  have hδ0 : P.e QuadraticAlgebra.omega ≠ 0 := by
    intro h0
    have h1 : (QuadraticAlgebra.omega : Lsq (Lp L) P.Δ) = 0 := P.e.injective (by rw [h0, map_zero])
    have h2 := congrArg QuadraticAlgebra.im h1
    simp at h2
  haveI := v.isMaximal
  obtain ⟨Q, hQm, hQl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) v.asIdeal
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [hQl.over, Ideal.under, Ideal.comap_bot_of_injective]
    exact FaithfulSMul.algebraMap_injective _ _
  let w : HeightOneSpectrum (𝓞 L) := ⟨Q, hQm.isPrime, hQ0⟩
  haveI : w.asIdeal.LiesOver v.asIdeal := hQl
  have hr : v.asIdeal.ramificationIdx' w.asIdeal = 1 := by
    haveI := hU w
    haveI : w.asIdeal.IsPrime := w.isPrime
    rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot]
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  have hv := IsDedekindDomain.HeightOneSpectrum.valuation_liesOver L v w P.Δ
  rw [hr, pow_one, ← hδ, map_mul] at hv
  have hw0 : w.valuation L (P.e QuadraticAlgebra.omega) ≠ 0 := by simpa using hδ0
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer (Lp L)
  have hπ0 : π ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hπ
    exact WithZero.zero_ne_coe hπ
  let t : Lp L := π ^ (-WithZero.log (w.valuation L (P.e QuadraticAlgebra.omega)))
  have ht0 : t ≠ 0 := zpow_ne_zero _ hπ0
  have ht : v.valuation (Lp L) t = w.valuation L (P.e QuadraticAlgebra.omega) := by
    simp only [t, map_zpow₀, hπ, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one, neg_neg]
    exact WithZero.exp_log hw0
  have hu1 : Valued.v (cv v (P.Δ / t ^ 2)) = 1 := by
    rw [hval, map_div₀, map_pow, ht, hv, sq]
    exact div_self (mul_ne_zero hw0 hw0)
  have hu2 : Valued.v (cv v (P.Δ / t ^ 2)⁻¹) = 1 := by
    rw [hval, map_inv₀, ← hval, hu1, inv_one]
  have hne : P.Δ / t ^ 2 ≠ 0 := div_ne_zero (by
      intro h0
      apply hδ0
      exact mul_self_eq_zero.mp (by rw [hδ, h0, map_zero])) (pow_ne_zero _ ht0)
  refine ⟨⟨⟨cv v (P.Δ / t ^ 2), le_of_eq hu1⟩, ⟨cv v (P.Δ / t ^ 2)⁻¹, le_of_eq hu2⟩, ?_, ?_⟩,
    cv v t, (map_ne_zero (cv v)).2 ht0, ?_⟩
  · apply Subtype.ext
    show cv v (P.Δ / t ^ 2) * cv v (P.Δ / t ^ 2)⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hne, map_one]
  · apply Subtype.ext
    show cv v (P.Δ / t ^ 2)⁻¹ * cv v (P.Δ / t ^ 2) = 1
    rw [← map_mul, inv_mul_cancel₀ hne, map_one]
  · show cv v P.Δ = cv v (P.Δ / t ^ 2) * cv v t ^ 2
    rw [← map_pow, ← map_mul, div_mul_cancel₀ _ (pow_ne_zero _ ht0)]
