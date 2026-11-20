import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAuslanderBuchsbaumProjDimUpper
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.AuslanderBuchsbaumDepthBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing CategoryTheory RingTheory.Sequence

universe u

/- English proof (translation)
Proceed by induction on `ms with`. Consider the case `nil`. Introduce `M _ _ _ _ n hM _ _`. Simplify using `using hasProjectiveDimensionLE_of_forall_isWeaklyRegular_length_le d R hd M n hM`. Consider the case `cons x ms ih`.

Introduce `M _ _ _ _ n hM hms hreg`. Simplify using `only [List.mem_cons, forall_eq_or_imp] at hms`. Rewrite `hreg` using `[isWeaklyRegular_cons_iff]`. Establish `: Nontrivial (QuotSMulTop x M)` using `nontrivial_quotSMulTop_of_mem_maximalIdeal M hms.1`. Establish `heq : projectiveDimension (ModuleCat.of R (QuotSMulTop x M)) = projectiveDimension (ModuleCat.of R M) + 1` using `ModuleCat.projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular (ModuleCat.of R M) x hreg.1 hms.1`.

Establish `hQ : HasProjectiveDimensionLE (ModuleCat.of R (QuotSMulTop x M)) (n + 1)`. Rewrite using `[← projectiveDimension_le_iff, heq, Nat.cast_add, Nat.cast_one]`. Use `gcongr`. Conclude with `(projectiveDimension_le_iff _ _).mpr hM`. Establish `hih` using `ih (QuotSMulTop x M) (n + 1) hQ hms.2 hreg.2`.

Rewrite `hih` using `[← projectiveDimension_le_iff, heq]`. Rewrite using `[← projectiveDimension_le_iff, List.length_cons]`. Break down `Nat.eq_zero_or_pos (d - ms.length) with h0 | hpos` into its components or cases. Rewrite `hih` using `[h0, Nat.cast_zero, ENat.WithBot.add_one_le_zero_iff, projectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton]`. Conclude with `absurd hih (not_subsingleton M)`.

Establish `hsplit : d - ms.length = (d - (ms.length + 1)) + 1` using `by omega`. Rewrite `hih` using `[hsplit, Nat.cast_add, ← Nat.cast_one (R := WithBot ℕ∞)]`. Conclude with `ENat.WithBot.add_le_add_natCast_right_iff.mp hih`.
-/
theorem hasProjectiveDimensionLE_sub_length_of_isWeaklyRegular (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (d : ℕ)
    (hd : ∀ rs : List R, (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular R rs → rs.length ≤ d)
    (ms : List R) : ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] (n : ℕ),
      HasProjectiveDimensionLE (ModuleCat.of R M) n → (∀ r ∈ ms, r ∈ maximalIdeal R) →
        IsWeaklyRegular M ms → HasProjectiveDimensionLE (ModuleCat.of R M) (d - ms.length) := by
  induction ms with
  | nil =>
    intro M _ _ _ _ n hM _ _
    simpa using hasProjectiveDimensionLE_of_forall_isWeaklyRegular_length_le d R hd M n hM
  | cons x ms ih =>
    intro M _ _ _ _ n hM hms hreg
    simp only [List.mem_cons, forall_eq_or_imp] at hms
    rw [isWeaklyRegular_cons_iff] at hreg
    have : Nontrivial (QuotSMulTop x M) := nontrivial_quotSMulTop_of_mem_maximalIdeal M hms.1
    have heq : projectiveDimension (ModuleCat.of R (QuotSMulTop x M)) =
        projectiveDimension (ModuleCat.of R M) + 1 :=
      ModuleCat.projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular (ModuleCat.of R M) x hreg.1 hms.1
    have hQ : HasProjectiveDimensionLE (ModuleCat.of R (QuotSMulTop x M)) (n + 1) := by
      rw [← projectiveDimension_le_iff, heq, Nat.cast_add, Nat.cast_one]
      gcongr
      exact (projectiveDimension_le_iff _ _).mpr hM
    have hih := ih (QuotSMulTop x M) (n + 1) hQ hms.2 hreg.2
    rw [← projectiveDimension_le_iff, heq] at hih
    rw [← projectiveDimension_le_iff, List.length_cons]
    rcases Nat.eq_zero_or_pos (d - ms.length) with h0 | hpos
    · rw [h0, Nat.cast_zero, ENat.WithBot.add_one_le_zero_iff, projectiveDimension_eq_bot_iff,
        ModuleCat.isZero_iff_subsingleton] at hih
      exact absurd hih (not_subsingleton M)
    · have hsplit : d - ms.length = (d - (ms.length + 1)) + 1 := by omega
      rw [hsplit, Nat.cast_add, ← Nat.cast_one (R := WithBot ℕ∞)] at hih
      exact ENat.WithBot.add_le_add_natCast_right_iff.mp hih

/- English proof (translation)
Introduce `R _ _ _ M _ _ _ _ n d ms hM hd hms hreg`. Conclude with `hasProjectiveDimensionLE_sub_length_of_isWeaklyRegular R d hd ms M n hM hms hreg`.
-/
theorem AuslanderBuchsbaumProjDimUpper.proof : AuslanderBuchsbaumProjDimUpper.Statement := by
  intro R _ _ _ M _ _ _ _ n d ms hM hd hms hreg
  exact hasProjectiveDimensionLE_sub_length_of_isWeaklyRegular R d hd ms M n hM hms hreg

end GroundTheory.Heights₂.Heights
