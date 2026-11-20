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
Rewrite using `[lift, PreTilt.mk_untilt_eq_coeff_zero, PreTilt.coeff_iterate_frobeniusEquiv_symm, zero_add]`.
-/
theorem mk_lift (u : PreTilt O p) (m : ℕ) :
    Ideal.Quotient.mk (span {(p : O)}) (lift u m) = PreTilt.coeff m u := by
  rw [lift, PreTilt.mk_untilt_eq_coeff_zero, PreTilt.coeff_iterate_frobeniusEquiv_symm, zero_add]

/- English proof (translation)
Rewrite using `[lift, lift, ← map_pow, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]`.
-/
theorem lift_succ_pow (u : PreTilt O p) (m : ℕ) : lift u (m + 1) ^ p = lift u m := by
  rw [lift, lift, ← map_pow, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]

/- English proof (translation)
The claim follows from `PreTilt.untilt_iterate_frobeniusEquiv_symm_pow u m`.
-/
theorem lift_pow (u : PreTilt O p) (m : ℕ) : lift u m ^ p ^ m = PreTilt.untilt u :=
  PreTilt.untilt_iterate_frobeniusEquiv_symm_pow u m

variable (hv : v.Integers O)
include hv

/- English proof (translation)
Take `⟨n, hn⟩ : ∃ n, PreTilt.coeff n u ≠ 0` from `not_forall.1 fun h => hu (Perfection.ext h)`. Establish `hn' : (Ideal.Quotient.mk (span {(p : O)}) (lift u n) : ModP O p) ≠ 0` using `by rwa [mk_lift]`. Express the relevant statement in the definitionally equal form `PreTilt.valAux K v O p u = _`. Rewrite using `[PreTilt.valAux_eq hv hn, ← mk_lift, ModP.preVal_mk hv hn', ← lift_pow u n, map_pow, map_pow]`.
-/
theorem val_eq_untilt (u : PreTilt O p) (hu : u ≠ 0) :
    PreTilt.val K v O hv p u = v (algebraMap O K (PreTilt.untilt u)) := by
  obtain ⟨n, hn⟩ : ∃ n, PreTilt.coeff n u ≠ 0 := not_forall.1 fun h => hu (Perfection.ext h)
  have hn' : (Ideal.Quotient.mk (span {(p : O)}) (lift u n) : ModP O p) ≠ 0 := by rwa [mk_lift]
  change PreTilt.valAux K v O p u = _
  rw [PreTilt.valAux_eq hv hn, ← mk_lift, ModP.preVal_mk hv hn', ← lift_pow u n, map_pow, map_pow]

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Conclude with `hx ▸ dvd_zero y`. Distinguish the cases in `hy : y = 0`. It suffices to derive a contradiction. Apply `hx` to reduce the goal to its premises.

Rewrite using `[← PreTilt.map_eq_zero hv]`. Rewrite `h` using `[hy, map_zero]`. Conclude with `le_antisymm h zero_le`. Establish `hp0 : p ≠ 0` using `(Fact.out : p.Prime).ne_zero`. Establish `hinj : Function.Injective (algebraMap O K)` using `hv.hom_inj`.

Rewrite `h` using `[val_eq_untilt hv x hx, val_eq_untilt hv y hy]`. Establish `hY : ∀ m, lift y m ≠ 0`. Introduce `m h0`. Apply `hy` to reduce the goal to its premises. Rewrite using `[← PreTilt.map_eq_zero hv, val_eq_untilt hv y hy, ← lift_pow y m, h0, zero_pow (pow_ne_zero _ hp0), map_zero, map_zero]`.

Establish `hle : ∀ m, v (algebraMap O K (lift x m)) ≤ v (algebraMap O K (lift y m))`. Introduce `m`. Establish `h'` using `h`. Rewrite `h'` using `[← lift_pow x m, ← lift_pow y m, map_pow, map_pow, map_pow, map_pow]`. Conclude with `(pow_le_pow_iff_left₀ zero_le zero_le (pow_ne_zero _ hp0)).1 h'`.

Use `choose q hq using fun m => hv.dvd_of_le (hle m)`. Establish `hqs : ∀ m, q (m + 1) ^ p = q m`. Introduce `m`. Establish `h1 : lift y m * q (m + 1) ^ p = lift y m * q m`. Rewrite using `[← hq m, ← lift_succ_pow y m, ← mul_pow, ← hq (m + 1), lift_succ_pow]`.

Establish `hK : algebraMap O K (lift y m) ≠ 0` using `fun h0 => hY m (hinj (h0.trans (map_zero _).symm))`. Apply `hinj` to reduce the goal to its premises. Establish `h2` using `congrArg (algebraMap O K) h1`. Rewrite `h2` using `[map_mul, map_mul]`. Conclude with `mul_left_cancel₀ hK h2`.

Set `e : PreTilt O p` to `(⟨fun m => Ideal.Quotient.mk (span {(p : O)}) (q m), fun m => by`. Simplify using `only`. Rewrite using `[← map_pow, hqs]⟩ : Perfection (ModP O p) p)`. Use `⟨e, Perfection.ext fun n => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `PreTilt.coeff n x = PreTilt.coeff n (y * e)`.

Rewrite using `[map_mul, ← mk_lift, ← mk_lift, hq n, map_mul]`. Both sides reduce to the same expression.
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
Apply the tactic sequence `first | exact GlobalTheory.RingBasics.norm_eq_val .. | exact GlobalTheory.RingBasics.norm_eq_val | exact @GlobalTheory.RingBasics.norm_eq_val _ _ | simpa using GlobalTheory.RingBasics.norm_eq_val .. | (intros; exact GlobalTheory.RingBasics.norm_eq_val ..)`.
-/
theorem norm_eq_val (x : ℂ_[p]) : ‖x‖ = ((Valued.v x : ℝ≥0) : ℝ) := by
  first | exact GlobalTheory.RingBasics.norm_eq_val .. | exact GlobalTheory.RingBasics.norm_eq_val | exact @GlobalTheory.RingBasics.norm_eq_val _ _ | simpa using GlobalTheory.RingBasics.norm_eq_val .. | (intros; exact GlobalTheory.RingBasics.norm_eq_val ..)

/- English proof (translation)
Apply the tactic sequence `first | exact GlobalTheory.RingBasics.mem_OC .. | exact GlobalTheory.RingBasics.mem_OC | exact @GlobalTheory.RingBasics.mem_OC _ _ | simpa using GlobalTheory.RingBasics.mem_OC .. | (intros; exact GlobalTheory.RingBasics.mem_OC ..)`.
-/
theorem mem_OC (x : ℂ_[p]) : x ∈ 𝓞_ℂ_[p] ↔ ‖x‖ ≤ 1 := by
  first | exact GlobalTheory.RingBasics.mem_OC .. | exact GlobalTheory.RingBasics.mem_OC | exact @GlobalTheory.RingBasics.mem_OC _ _ | simpa using GlobalTheory.RingBasics.mem_OC .. | (intros; exact GlobalTheory.RingBasics.mem_OC ..)

/- English proof (translation)
Apply the tactic sequence `first | exact GlobalTheory.RingBasics.norm_p_lt .. | exact GlobalTheory.RingBasics.norm_p_lt | exact @GlobalTheory.RingBasics.norm_p_lt _ _ | simpa using GlobalTheory.RingBasics.norm_p_lt .. | (intros; exact GlobalTheory.RingBasics.norm_p_lt ..)`.
-/
theorem norm_p_lt : ‖(p : ℂ_[p])‖ < 1 := by
  first | exact GlobalTheory.RingBasics.norm_p_lt .. | exact GlobalTheory.RingBasics.norm_p_lt | exact @GlobalTheory.RingBasics.norm_p_lt _ _ | simpa using GlobalTheory.RingBasics.norm_p_lt .. | (intros; exact GlobalTheory.RingBasics.norm_p_lt ..)

/- English proof (translation)
Apply the tactic sequence `first | exact GlobalTheory.RingBasics.p_ne_zero .. | exact GlobalTheory.RingBasics.p_ne_zero | exact @GlobalTheory.RingBasics.p_ne_zero _ _ | simpa using GlobalTheory.RingBasics.p_ne_zero ..`.
-/
theorem p_ne_zero : (p : ℂ_[p]) ≠ 0 := by
  first | exact GlobalTheory.RingBasics.p_ne_zero .. | exact GlobalTheory.RingBasics.p_ne_zero | exact @GlobalTheory.RingBasics.p_ne_zero _ _ | simpa using GlobalTheory.RingBasics.p_ne_zero ..

/- English proof (translation)
Apply the tactic sequence `first | exact GlobalTheory.RingBasics.mem_span_pow_OC .. | exact GlobalTheory.RingBasics.mem_span_pow_OC | exact @GlobalTheory.RingBasics.mem_span_pow_OC _ _ | simpa using GlobalTheory.RingBasics.mem_span_pow_OC .. | (intros; exact GlobalTheory.RingBasics.mem_span_pow_OC ..)`.
-/
theorem mem_span_pow_OC (n : ℕ) (x : OC p) :
    x ∈ (span {(p : OC p)}) ^ n ↔ ‖(x : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ ^ n := by
  first | exact GlobalTheory.RingBasics.mem_span_pow_OC .. | exact GlobalTheory.RingBasics.mem_span_pow_OC | exact @GlobalTheory.RingBasics.mem_span_pow_OC _ _ | simpa using GlobalTheory.RingBasics.mem_span_pow_OC .. | (intros; exact GlobalTheory.RingBasics.mem_span_pow_OC ..)

/- English proof (translation)
Apply the tactic sequence `first | infer_instance | exact Formalism.Per.instIsAdicCompleteOCSpanSingletonSetCast _`.
-/
theorem isAdicComplete_OC : IsAdicComplete (span {(p : OC p)}) (OC p) := by
  first | infer_instance | exact Formalism.Per.instIsAdicCompleteOCSpanSingletonSetCast _

end Complete

/- English proof (translation)
Introduce `l _ x y h`. Use `isAdicComplete_OC (p := l)` as an intermediate fact. Conclude with `Div.dvd_of_val_le (PadicComplexInt.integers l) x y h`.
-/
theorem tiltDiv : PI.ArtSch.TiltDiv := by
  intro l _ x y h
  have := isAdicComplete_OC (p := l)
  exact Div.dvd_of_val_le (PadicComplexInt.integers l) x y h

end GlobalTheory.ArtinSchreierTilt

namespace GlobalTheory

/- English proof (translation)
Introduce `l _ x`. Conclude with `PI.ArtSch.main_of witt_lift (tiltSurjectiveOfParts rootModP_holds ArtinSchreierTilt.tiltDiv smallSurjective) l x`.
-/
theorem frobSubOne_onto : Formalism.MainNotions.ElementDenominator.ArtinSchreierWittOnto := by
  intro l _ x
  exact PI.ArtSch.main_of witt_lift
    (tiltSurjectiveOfParts rootModP_holds ArtinSchreierTilt.tiltDiv smallSurjective) l x

end GlobalTheory
