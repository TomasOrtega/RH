import Formalism.LatticeSlopes.CovolAntiSameRank
import Formalism.LatticeSlopes.LatticeSlopesProofs.DiscreteTopologyOfLe
import Formalism.LatticeSlopes.LatticeSlopesProofs.MuMaxAttained

open Module

namespace Formalism.F

universe u

/- English proof (translation)
Introduce `E _ _ _ L hL hL0 r hr hmin`. Use `haveI := hL`. Establish `hne : (slopes L).Nonempty` using `⟨slope L, L, le_rfl, hL0, rfl⟩`. Unfold `muMax`. Apply `csSup_le hne` to reduce the goal to its premises.

Introduce and unpack `t ⟨N, hNL, hN0, rfl⟩`. Use `haveI : DiscreteTopology N := discreteTopology_of_le hNL`. Establish `hk : 0 < rk N` using `att_rk_pos hN0`. Establish `hkL : rk N ≤ rk L` using `att_rk_le hNL`. Establish `hc : 0 < covol N` using `hP E N inferInstance`.

Take `⟨v, hvN, hv0, hvle⟩` from `hS E N inferInstance hN0`. Establish `hrv : r ≤ ‖v‖` using `hmin v (hNL hvN) hv0`. Establish `hk' : (0 : ℝ) < (rk N : ℝ)` using `by exact_mod_cast hk`. Establish `h1 : Real.log r ≤ Real.log (rk N : ℝ) / 2 + Real.log (covol N) / (rk N : ℝ)`. Establish `hpow : 0 < covol N ^ ((1 : ℝ) / (rk N : ℝ))` using `Real.rpow_pos_of_pos hc _`.

Establish `hsq : 0 < Real.sqrt (rk N : ℝ)` using `Real.sqrt_pos.mpr hk'`. Establish `h` using `Real.log_le_log hr (hrv.trans hvle)`. Rewrite `h` using `[Real.log_mul hsq.ne' hpow.ne', Real.log_sqrt hk'.le, Real.log_rpow hc]`. Establish `e : (1 : ℝ) / (rk N : ℝ) * Real.log (covol N) = Real.log (covol N) / (rk N : ℝ)` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h2 : Real.log (rk N : ℝ) ≤ Real.log (rk L : ℝ)` using `Real.log_le_log hk' (by exact_mod_cast hkL)`. Establish `h3 : slope N = -(Real.log (covol N) / (rk N : ℝ))`. Unfold `slope deg`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h3]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem muMaxLeMin_of (hP : CovolPos.{u}) (hS : ShortVector.{u}) : MuMaxLeMin.{u} := by
  intro E _ _ _ L hL hL0 r hr hmin
  haveI := hL
  have hne : (slopes L).Nonempty := ⟨slope L, L, le_rfl, hL0, rfl⟩
  unfold muMax
  apply csSup_le hne
  rintro t ⟨N, hNL, hN0, rfl⟩
  haveI : DiscreteTopology N := discreteTopology_of_le hNL
  have hk : 0 < rk N := att_rk_pos hN0
  have hkL : rk N ≤ rk L := att_rk_le hNL
  have hc : 0 < covol N := hP E N inferInstance
  obtain ⟨v, hvN, hv0, hvle⟩ := hS E N inferInstance hN0
  have hrv : r ≤ ‖v‖ := hmin v (hNL hvN) hv0
  have hk' : (0 : ℝ) < (rk N : ℝ) := by exact_mod_cast hk

  have h1 : Real.log r ≤ Real.log (rk N : ℝ) / 2 + Real.log (covol N) / (rk N : ℝ) := by
    have hpow : 0 < covol N ^ ((1 : ℝ) / (rk N : ℝ)) := Real.rpow_pos_of_pos hc _
    have hsq : 0 < Real.sqrt (rk N : ℝ) := Real.sqrt_pos.mpr hk'
    have h := Real.log_le_log hr (hrv.trans hvle)
    rw [Real.log_mul hsq.ne' hpow.ne', Real.log_sqrt hk'.le, Real.log_rpow hc] at h
    have e : (1 : ℝ) / (rk N : ℝ) * Real.log (covol N) = Real.log (covol N) / (rk N : ℝ) := by ring
    linarith
  have h2 : Real.log (rk N : ℝ) ≤ Real.log (rk L : ℝ) :=
    Real.log_le_log hk' (by exact_mod_cast hkL)
  have h3 : slope N = -(Real.log (covol N) / (rk N : ℝ)) := by
    unfold slope deg; ring
  rw [h3]
  linarith

end Formalism.F
