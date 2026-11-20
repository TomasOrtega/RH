import Mathlib
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ASWitt
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ASRoot
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ASSmall
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ASGlue

namespace GlobalTheory.ArtinSchreierTilt

open Formalism.BasicNotions.Loc

namespace Div

open scoped NNReal
open Ideal

section General

variable {K : Type*} [Field K] {v : Valuation K ℝ≥0} {O : Type*} [CommRing O] [Algebra O K]
  {p : ℕ} [Fact p.Prime] [Fact (¬ IsUnit (p : O))] [IsAdicComplete (span {(p : O)}) O]

noncomputable def lift (u : PreTilt O p) (m : ℕ) : O :=
  PreTilt.untilt (((frobeniusEquiv (PreTilt O p) p).symm^[m]) u)

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem mk_lift (u : PreTilt O p) (m : ℕ) :
    Ideal.Quotient.mk (span {(p : O)}) (lift u m) = PreTilt.coeff m u := by
  rw [lift, PreTilt.mk_untilt_eq_coeff_zero, PreTilt.coeff_iterate_frobeniusEquiv_symm, zero_add]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem lift_succ_pow (u : PreTilt O p) (m : ℕ) : lift u (m + 1) ^ p = lift u m := by
  rw [lift, lift, ← map_pow, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lift_pow (u : PreTilt O p) (m : ℕ) : lift u m ^ p ^ m = PreTilt.untilt u :=
  PreTilt.untilt_iterate_frobeniusEquiv_symm_pow u m

variable (hv : v.Integers O)
include hv

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem val_eq_untilt (u : PreTilt O p) (hu : u ≠ 0) :
    PreTilt.val K v O hv p u = v (algebraMap O K (PreTilt.untilt u)) := by
  obtain ⟨n, hn⟩ : ∃ n, PreTilt.coeff n u ≠ 0 := not_forall.1 fun h => hu (Perfection.ext h)
  have hn' : (Ideal.Quotient.mk (span {(p : O)}) (lift u n) : ModP O p) ≠ 0 := by rwa [mk_lift]
  change PreTilt.valAux K v O p u = _
  rw [PreTilt.valAux_eq hv hn, ← mk_lift, ModP.preVal_mk hv hn', ← lift_pow u n, map_pow, map_pow]

/- English proof (translation)
Consider separately whether the proposition holds or fails. Consider separately whether the proposition holds or fails. It suffices to derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Introduce a local definition for the expression. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem dvd_of_val_le (x y : PreTilt O p)
    (h : PreTilt.val K v O hv p x ≤ PreTilt.val K v O hv p y) : y ∣ x := by
  by_cases hx : x = 0
  · exact hx ▸ dvd_zero y
  by_cases hy : y = 0
  · exfalso
    apply hx
    rw [← PreTilt.map_eq_zero hv]
    rw [hy, map_zero] at h
    exact le_antisymm h zero_le
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hinj : Function.Injective (algebraMap O K) := hv.hom_inj
  rw [val_eq_untilt hv x hx, val_eq_untilt hv y hy] at h
  have hY : ∀ m, lift y m ≠ 0 := by
    intro m h0
    apply hy
    rw [← PreTilt.map_eq_zero hv, val_eq_untilt hv y hy, ← lift_pow y m, h0,
      zero_pow (pow_ne_zero _ hp0), map_zero, map_zero]
  have hle : ∀ m, v (algebraMap O K (lift x m)) ≤ v (algebraMap O K (lift y m)) := by
    intro m
    have h' := h
    rw [← lift_pow x m, ← lift_pow y m, map_pow, map_pow, map_pow, map_pow] at h'
    exact (pow_le_pow_iff_left₀ zero_le zero_le (pow_ne_zero _ hp0)).1 h'
  choose q hq using fun m => hv.dvd_of_le (hle m)
  have hqs : ∀ m, q (m + 1) ^ p = q m := by
    intro m
    have h1 : lift y m * q (m + 1) ^ p = lift y m * q m := by
      rw [← hq m, ← lift_succ_pow y m, ← mul_pow, ← hq (m + 1), lift_succ_pow]
    have hK : algebraMap O K (lift y m) ≠ 0 := fun h0 => hY m (hinj (h0.trans (map_zero _).symm))
    apply hinj
    have h2 := congrArg (algebraMap O K) h1
    rw [map_mul, map_mul] at h2
    exact mul_left_cancel₀ hK h2
  let e : PreTilt O p :=
    (⟨fun m => Ideal.Quotient.mk (span {(p : O)}) (q m), fun m => by
      simp only
      rw [← map_pow, hqs]⟩ : Perfection (ModP O p) p)
  refine ⟨e, Perfection.ext fun n => ?_⟩
  change PreTilt.coeff n x = PreTilt.coeff n (y * e)
  rw [map_mul, ← mk_lift, ← mk_lift, hq n, map_mul]
  rfl

end General

end Div

section Complete

open scoped NNReal
open Ideal

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem norm_eq_val (x : ℂ_[p]) : ‖x‖ = ((Valued.v x : ℝ≥0) : ℝ) := by
  first | exact GlobalTheory.RingBasics.norm_eq_val .. | exact GlobalTheory.RingBasics.norm_eq_val | exact @GlobalTheory.RingBasics.norm_eq_val _ _ | simpa using GlobalTheory.RingBasics.norm_eq_val .. | (intros; exact GlobalTheory.RingBasics.norm_eq_val ..)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mem_OC (x : ℂ_[p]) : x ∈ 𝓞_ℂ_[p] ↔ ‖x‖ ≤ 1 := by
  first | exact GlobalTheory.RingBasics.mem_OC .. | exact GlobalTheory.RingBasics.mem_OC | exact @GlobalTheory.RingBasics.mem_OC _ _ | simpa using GlobalTheory.RingBasics.mem_OC .. | (intros; exact GlobalTheory.RingBasics.mem_OC ..)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem norm_p_lt : ‖(p : ℂ_[p])‖ < 1 := by
  first | exact GlobalTheory.RingBasics.norm_p_lt .. | exact GlobalTheory.RingBasics.norm_p_lt | exact @GlobalTheory.RingBasics.norm_p_lt _ _ | simpa using GlobalTheory.RingBasics.norm_p_lt .. | (intros; exact GlobalTheory.RingBasics.norm_p_lt ..)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem p_ne_zero : (p : ℂ_[p]) ≠ 0 := by
  first | exact GlobalTheory.RingBasics.p_ne_zero .. | exact GlobalTheory.RingBasics.p_ne_zero | exact @GlobalTheory.RingBasics.p_ne_zero _ _ | simpa using GlobalTheory.RingBasics.p_ne_zero ..

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mem_span_pow_OC (n : ℕ) (x : OC p) :
    x ∈ (span {(p : OC p)}) ^ n ↔ ‖(x : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ ^ n := by
  first | exact GlobalTheory.RingBasics.mem_span_pow_OC .. | exact GlobalTheory.RingBasics.mem_span_pow_OC | exact @GlobalTheory.RingBasics.mem_span_pow_OC _ _ | simpa using GlobalTheory.RingBasics.mem_span_pow_OC .. | (intros; exact GlobalTheory.RingBasics.mem_span_pow_OC ..)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isAdicComplete_OC : IsAdicComplete (span {(p : OC p)}) (OC p) := by
  first | infer_instance | exact Formalism.Per.instIsAdicCompleteOCSpanSingletonSetCast _

end Complete

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem tiltDiv : PI.ArtSch.TiltDiv := by
  intro l _ x y h
  have := isAdicComplete_OC (p := l)
  exact Div.dvd_of_val_le (PadicComplexInt.integers l) x y h

end GlobalTheory.ArtinSchreierTilt

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem frobSubOne_onto : Formalism.MainNotions.ElementDenominator.ArtinSchreierWittOnto := by
  intro l _ x
  exact PI.ArtSch.main_of witt_lift
    (tiltSurjectiveOfParts rootModP_holds ArtinSchreierTilt.tiltDiv smallSurjective) l x

end GlobalTheory
