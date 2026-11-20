import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.PsCycloStatement

noncomputable section

namespace LevelStatements.Lv

open PowerSeries

/- English proof (translation)
Rewrite using `[Polynomial.aeval_def]`. Conclude with `Polynomial.eval₂_C_X_eq_coe.symm`.
-/
theorem polynomial_coe_powerSeries_eq_aeval_X {O : Type*} [CommRing O] (P : Polynomial O) :
    (P : PowerSeries O) = Polynomial.aeval (X : PowerSeries O) P := by
  rw [Polynomial.aeval_def]
  exact Polynomial.eval₂_C_X_eq_coe.symm

/- English proof (translation)
Rewrite using `[polynomial_coe_powerSeries_eq_aeval_X P]`. Conclude with `(Polynomial.aeval_algHom_apply φ X P).symm`.
-/
theorem psCyclo_algHom_coe {O : Type*} [CommRing O] (φ : PowerSeries O →ₐ[O] PowerSeries O)
    (P : Polynomial O) : φ (P : PowerSeries O) = Polynomial.aeval (φ X) P := by
  rw [polynomial_coe_powerSeries_eq_aeval_X P]
  exact (Polynomial.aeval_algHom_apply φ X P).symm

/- English proof (translation)
Rewrite using `[psCyclo_algHom_coe, polynomial_coe_powerSeries_eq_aeval_X, ← Polynomial.cyclotomic_expand_eq_cyclotomic hl hm]`. Simplify using `only [Polynomial.aeval_comp, Polynomial.expand_aeval, hφ, map_add, Polynomial.aeval_X, map_one]`. Conclude with `congrArg (fun y => Polynomial.aeval y (Polynomial.cyclotomic m O)) (by ring)`.
-/
theorem psCyclo_step {O : Type*} [CommRing O] (l : ℕ) (hl : l.Prime)
    (φ : PowerSeries O →ₐ[O] PowerSeries O) (hφ : φ X = (1 + X) ^ l - 1) (m : ℕ) (hm : l ∣ m) :
    φ (((Polynomial.cyclotomic m O).comp (Polynomial.X + 1) : Polynomial O) : PowerSeries O) =
      (((Polynomial.cyclotomic (m * l) O).comp (Polynomial.X + 1) : Polynomial O) :
        PowerSeries O) := by
  rw [psCyclo_algHom_coe, polynomial_coe_powerSeries_eq_aeval_X,
    ← Polynomial.cyclotomic_expand_eq_cyclotomic hl hm]
  simp only [Polynomial.aeval_comp, Polynomial.expand_aeval, hφ, map_add, Polynomial.aeval_X,
    map_one]
  exact congrArg (fun y => Polynomial.aeval y (Polynomial.cyclotomic m O)) (by ring)

/- English proof (translation)
Unfold `PsCycloStatement`. Introduce `O _ l hl φ hφ q w hq s`. Proceed by induction on `s with`. Consider the case `zero => exact ⟨w, by rw [Function.iterate_zero_apply, zero_add, pow_one]; exact hq⟩`. Consider the case `succ s ih`.

Take `⟨w', hw'⟩` from `ih`. Use `⟨Units.map (φ : PowerSeries O →* PowerSeries O) w', ?_⟩` and prove the remaining obligations. Rewrite using `[Function.iterate_succ_apply', hw', map_mul, psCyclo_step l hl φ hφ (l ^ (s + 1)) (dvd_pow_self l (Nat.succ_ne_zero s)), ← pow_succ]`. Apply the tactic sequence `all_goals simp`.
-/
theorem psCyclo : PsCycloStatement := by
  unfold PsCycloStatement
  intro O _ l hl φ hφ q w hq s
  induction s with
  | zero => exact ⟨w, by rw [Function.iterate_zero_apply, zero_add, pow_one]; exact hq⟩
  | succ s ih =>
    obtain ⟨w', hw'⟩ := ih
    refine ⟨Units.map (φ : PowerSeries O →* PowerSeries O) w', ?_⟩
    rw [Function.iterate_succ_apply', hw', map_mul,
      psCyclo_step l hl φ hφ (l ^ (s + 1)) (dvd_pow_self l (Nat.succ_ne_zero s)),
      ← pow_succ]
    all_goals simp

end LevelStatements.Lv
