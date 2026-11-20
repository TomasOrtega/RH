import Mathlib
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataHost
import Formalism.LocalRingCardinality.Params
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralImagQuadraticHalfInt

@[reducible] noncomputable def UpperTheory.Reformulated.B.IntegralClosureCriterionSecond.be :
    Formalism.BasicNotions.D7 → ℂ :=
    fun (D : Formalism.BasicNotions.D7) ↦ Complex.I * (↑√(↑D.host.d : ℝ) : ℂ)

/- English proof (translation)
Conclude with `⟨le_rfl⟩`.
-/
theorem UpperTheory.Reformulated.B.IntegralClosureCriterionSecond.aux2 :
    ((1 : ℕ) + (1 : ℕ)).AtLeastTwo := by
  exact ⟨le_rfl⟩

noncomputable def UpperTheory.Reformulated.B.IntegralClosureCriterionSecond.OKc :
    Formalism.BasicNotions.D7 → ℂ → Prop :=
    fun (D : Formalism.BasicNotions.D7) (z : ℂ) ↦
      ∃ (x : ℤ) (y : ℤ), Even (x - y) ∧ z = ((↑x : ℂ) + (↑y : ℂ) * UpperTheory.Reformulated.B.IntegralClosureCriterionSecond.be D) / (2 : ℂ)

/- English proof (translation)
Introduce `D u`. Establish `hd : Nat.Prime D.host.d` using `D.host.hyp.2.1`. Establish `hint : IsIntegral ℤ ((u : D.host.K) : D.host.E)` using `(NumberField.RingOfIntegers.isIntegral_coe u).map (D.host.K.val.toRingHom.toIntAlgHom)`. Take `⟨x, y, hxy, hz⟩` from `UpperTheory.integral_imag_quadratic_half_int D.host.E D.host.d D.host.sqd hd.squarefree D.host.sqd_sq _ (u : D.host.K).2 hint`. Establish `hs : D.host.φ₀ D.host.sqd = UpperTheory.Reformulated.B.IntegralClosureCriterionSecond.be D` using `D.host.φ₀_mem`.

Use `⟨x, y, hxy, ?_⟩` and prove the remaining obligations. Rewrite using `[hz, map_div₀, map_add, map_mul, map_intCast, map_intCast, hs, map_ofNat]`.
-/
theorem UpperTheory.Reformulated.B.IntegralClosureCriterionSecond.okc_of :
    ∀ (D : Formalism.BasicNotions.D7) (u : NumberField.RingOfIntegers ↥D.host.K),
      UpperTheory.Reformulated.B.IntegralClosureCriterionSecond.OKc D ((D.host.φ₀ : D.host.E → ℂ) (↑(↑u : ↥D.host.K) : D.host.E)) := by
  intro D u
  have hd : Nat.Prime D.host.d := D.host.hyp.2.1
  have hint : IsIntegral ℤ ((u : D.host.K) : D.host.E) :=
    (NumberField.RingOfIntegers.isIntegral_coe u).map (D.host.K.val.toRingHom.toIntAlgHom)
  obtain ⟨x, y, hxy, hz⟩ := UpperTheory.integral_imag_quadratic_half_int D.host.E D.host.d D.host.sqd hd.squarefree
    D.host.sqd_sq _ (u : D.host.K).2 hint
  have hs : D.host.φ₀ D.host.sqd = UpperTheory.Reformulated.B.IntegralClosureCriterionSecond.be D := D.host.φ₀_mem
  refine ⟨x, y, hxy, ?_⟩
  rw [hz, map_div₀, map_add, map_mul, map_intCast, map_intCast, hs, map_ofNat]
