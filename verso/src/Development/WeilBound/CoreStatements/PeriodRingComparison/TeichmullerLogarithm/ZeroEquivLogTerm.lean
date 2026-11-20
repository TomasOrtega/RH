import Mathlib
import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.GammaEqDpow
import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.AcrisNAlgebraMapAinf
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.EqZeroOfPMulEqZero
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.ExistsMapEqOfPowMul
import GroundTheory.PAdicHodge.ACrisLog

noncomputable section

open GroundTheory.PAdicHodge
open _root_.WittVector

namespace Cmp6

variable (l : ℕ) [Fact l.Prime]

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem periodT_congr {ε ε' : PreTilt (normInteger ℂ_[l]) l} (hε : PreTilt.untilt ε = 1)
    (hε' : PreTilt.untilt ε' = 1) (h : ε = ε') :
    ACris.periodT (K := ℂ_[l]) hε = ACris.periodT (K := ℂ_[l]) hε' := by
  subst h; rfl

/- English proof (translation)
Rewrite using `[ACris.logTermZero, map_mul, map_mul, map_pow, map_neg, map_one, map_natCast]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Reformulated.AutPerF.AinfInv.gamma (n + 1) (algebraMap (Reformulated.AutPerF.Ainf l (NC l)) (Reformulated.AutPerF.AinfInv l (NC l)) (u - 1)) = ACris.dpow (n + 1) (u - 1)`. Conclude with `gamma_eq_dpow l (n + 1) (u - 1)`.
-/
theorem zeroEquiv_logTerm (u : Reformulated.AutPerF.Ainf l (NC l))
    (hu : Reformulated.AutPerF.Ainf.theta l (NC l) u = 1)
    (hx : u - 1 ∈ RingHom.ker (fontaineTheta (normInteger ℂ_[l]) l)) (n : ℕ) :
    zeroEquiv l (((-1) ^ n * (n.factorial : Reformulated.AutPerF.AcrisZero l (NC l))) *
        Reformulated.AutPerF.AcrisZero.gamma (n + 1) (u - 1) (by rw [map_sub, hu, map_one, sub_self])) =
      ACris.logTermZero hx n := by
  rw [ACris.logTermZero, map_mul, map_mul, map_pow, map_neg, map_one, map_natCast]
  congr 1
  apply Subtype.ext
  change Reformulated.AutPerF.AinfInv.gamma (n + 1)
      (algebraMap (Reformulated.AutPerF.Ainf l (NC l)) (Reformulated.AutPerF.AinfInv l (NC l)) (u - 1)) =
    ACris.dpow (n + 1) (u - 1)
  exact gamma_eq_dpow l (n + 1) (u - 1)

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Use `symm`. Apply `ACris.log_eq_of_isAdicSum` to reduce the goal to its premises. Introduce `k`. Use `⟨l ^ k, fun M hM => ?_⟩` and prove the remaining obligations. Establish `hsum : ∑ n ∈ Finset.range M, ACris.logTerm hx n = acrisNHom l (algebraMap _ (Reformulated.AutPerF.Acris l (NC l)) (Reformulated.AutPerF.Acris.logPartial M u hu))`.

Rewrite using `[acrisNHom_algebraMap, Reformulated.AutPerF.Acris.logPartial, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Rewrite using `[ACris.logTerm, zeroEquiv_logTerm l u hu hx n]`. Rewrite using `[hsum, ← map_sub]`. Take `⟨y, hy⟩` from `(Reformulated.AutPerF.Acris.eval_eq_zero_iff k (Reformulated.AutPerF.Acris.log u hu - algebraMap _ (Reformulated.AutPerF.Acris l (NC l)) (Reformulated.AutPerF.Acris.logPartial M u hu))).1 (by`.

Rewrite using `[map_sub, Reformulated.AutPerF.Acris.eval_algebraMap, Reformulated.AutPerF.Acris.eval_log u hu hM, sub_self])`. Rewrite using `[hy, map_mul, map_pow, map_natCast, Ideal.span_singleton_pow]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)`.
-/
theorem acrisNHom_log (u : Reformulated.AutPerF.Ainf l (NC l))
    (hu : Reformulated.AutPerF.Ainf.theta l (NC l) u = 1)
    (hx : u - 1 ∈ RingHom.ker (fontaineTheta (normInteger ℂ_[l]) l)) :
    acrisNHom l (Reformulated.AutPerF.Acris.log u hu) = ACris.log hx := by
  symm
  apply ACris.log_eq_of_isAdicSum
  intro k
  refine ⟨l ^ k, fun M hM => ?_⟩
  have hsum : ∑ n ∈ Finset.range M, ACris.logTerm hx n =
      acrisNHom l (algebraMap _ (Reformulated.AutPerF.Acris l (NC l))
        (Reformulated.AutPerF.Acris.logPartial M u hu)) := by
    rw [acrisNHom_algebraMap, Reformulated.AutPerF.Acris.logPartial, map_sum, map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [ACris.logTerm, zeroEquiv_logTerm l u hu hx n]
  rw [hsum, ← map_sub]
  obtain ⟨y, hy⟩ := (Reformulated.AutPerF.Acris.eval_eq_zero_iff k (Reformulated.AutPerF.Acris.log u hu -
      algebraMap _ (Reformulated.AutPerF.Acris l (NC l)) (Reformulated.AutPerF.Acris.logPartial M u hu))).1 (by
    rw [map_sub, Reformulated.AutPerF.Acris.eval_algebraMap, Reformulated.AutPerF.Acris.eval_log u hu hM, sub_self])
  rw [hy, map_mul, map_pow, map_natCast, Ideal.span_singleton_pow]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

/- English proof (translation)
Establish `hu : Reformulated.AutPerF.Ainf.theta l (NC l) (Reformulated.AutPerF.Ainf.teich l (Formalism.Per6.tiltMap l η.1)) = 1`. Rewrite using `[Reformulated.AutPerF.Ainf.theta_teich]`. Conclude with `h`. Rewrite using `[cA_apply, Reformulated.AutPerF.Acris.map_logTeich, Reformulated.AutPerF.Acris.logTeich, Reformulated.AutPerF.Acris.log_congr _ hu (by rw [Reformulated.AutPerF.tateModule.coe_map, tiltMap_eq])]`. Conclude with `acrisNHom_log l _ hu (ACris.mu_mem_ker h)`.
-/
theorem cA_logTeich (η : Reformulated.AutPerF.tateModule l (OC l))
    (h : PreTilt.untilt (Formalism.Per6.tiltMap l η.1) = 1) :
    cA l (Reformulated.AutPerF.Acris.logTeich η) = ACris.periodT h := by
  have hu : Reformulated.AutPerF.Ainf.theta l (NC l)
      (Reformulated.AutPerF.Ainf.teich l (Formalism.Per6.tiltMap l η.1)) = 1 := by
    rw [Reformulated.AutPerF.Ainf.theta_teich]; exact h
  rw [cA_apply, Reformulated.AutPerF.Acris.map_logTeich, Reformulated.AutPerF.Acris.logTeich,
    Reformulated.AutPerF.Acris.log_congr _ hu (by rw [Reformulated.AutPerF.tateModule.coe_map, tiltMap_eq])]
  exact acrisNHom_log l _ hu (ACris.mu_mem_ker h)

/- English proof (translation)
Establish `h1 : Formalism.Per6.tiltMap l (PositivityTheory.LocInh.εO l) = epsilon l` using `PositivityTheory.LocInh.tiltMap_tiltInv l _`. Establish `h2` using `Reformulated.AutPerF.Tilt.untilt_map (e l).toRingHom (PositivityTheory.LocInh.εO l)`. Rewrite `h2` using `[tiltMap_eq, h1, untilt_epsilon]`. Apply `(e l).injective` to reduce the goal to its premises. Rewrite using `[map_one]`.

Conclude with `h2.symm`.
-/
theorem untilt_εO : PreTilt.untilt (PositivityTheory.LocInh.εO l) = 1 := by
  have h1 : Formalism.Per6.tiltMap l (PositivityTheory.LocInh.εO l) = epsilon l := PositivityTheory.LocInh.tiltMap_tiltInv l _
  have h2 := Reformulated.AutPerF.Tilt.untilt_map (e l).toRingHom (PositivityTheory.LocInh.εO l)
  rw [tiltMap_eq, h1, untilt_epsilon] at h2
  apply (e l).injective
  rw [map_one]
  exact h2.symm

/- English proof (translation)
Establish `h1 : Formalism.Per6.tiltMap l (PositivityTheory.LocInh.εO l) = epsilon l` using `PositivityTheory.LocInh.tiltMap_tiltInv l _`. Establish `h : PreTilt.untilt (Formalism.Per6.tiltMap l (PositivityTheory.LocInh.εO l)) = 1`. Rewrite using `[h1]`. Conclude with `untilt_epsilon (p := l)`. Rewrite using `[cA_logTeich l ⟨PositivityTheory.LocInh.εO l, h0⟩ h]`.

Conclude with `periodT_congr l h (untilt_epsilon (p := l)) h1`.
-/
theorem cA_logTeich_eps (h0 : PreTilt.untilt (PositivityTheory.LocInh.εO l) = 1) :
    cA l (Reformulated.AutPerF.Acris.logTeich ⟨PositivityTheory.LocInh.εO l, h0⟩) = Formalism.Per6.tA l := by
  have h1 : Formalism.Per6.tiltMap l (PositivityTheory.LocInh.εO l) = epsilon l := PositivityTheory.LocInh.tiltMap_tiltInv l _
  have h : PreTilt.untilt (Formalism.Per6.tiltMap l (PositivityTheory.LocInh.εO l)) = 1 := by
    rw [h1]; exact untilt_epsilon (p := l)
  rw [cA_logTeich l ⟨PositivityTheory.LocInh.εO l, h0⟩ h]
  exact periodT_congr l h (untilt_epsilon (p := l)) h1

end Cmp6
