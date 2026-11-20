import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordBoxStatement
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

/- English proof (translation)
Establish `hk` using `D.R.m_add_three_le_k`. Establish `hm` using `D.R.two_le_m`. Use `set τ := D.eTau.symm ⟨plc (1 : D.R.GG), plc_mem 1⟩`. Use `set P := D.hc τ`. Establish `h1` using `P.u_gt_v ⟨1, by omega⟩`.

Establish `h2` using `P.v_gt_u ⟨0, by omega⟩`. Take `⟨z0, hz0⟩` from `P.v_int ⟨0, by omega⟩`. Take `⟨z1, hz1⟩` from `P.v_int ⟨1, by omega⟩`. Establish `c0` using `(L.cloud_v τ ⟨0, by omega⟩).2`. Establish `c1` using `(L.cloud_v τ ⟨1, by omega⟩).1`.

Simplify using `only at h1 h2`. Establish `hlt : P.v ⟨1, by omega⟩ < P.v ⟨0, by omega⟩` using `lt_trans h1 h2`. Rewrite `hlt` using `[hz0, hz1]`. Establish `hz : z1 < z0` using `by exact_mod_cast hlt`. Establish `hz1' : (0 : ℝ) ≤ (z1 : ℝ)`.

Establish `: (((P.v ⟨1, by omega⟩ : ℚ) : ℝ)) = (z1 : ℝ)` using `by rw [hz1]; push_cast; rfl`. Rewrite using `[← this]`. Conclude with `c1`. Establish `hz0' : (z0 : ℝ) ≤ L.Sc`. Establish `: (((P.v ⟨0, by omega⟩ : ℚ) : ℝ)) = (z0 : ℝ)` using `by rw [hz0]; push_cast; rfl`.

Rewrite using `[← this]`. Conclude with `c0`. Establish `: (0 : ℤ) ≤ z1` using `by exact_mod_cast hz1'`. Establish `: (1 : ℝ) ≤ (z0 : ℝ)` using `by exact_mod_cast (show (1 : ℤ) ≤ z0 by omega)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem one_le_Sc {D : D7} (L : SizeData₂ D) : (1 : ℝ) ≤ L.Sc := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  set τ := D.eTau.symm ⟨plc (1 : D.R.GG), plc_mem 1⟩
  set P := D.hc τ
  have h1 := P.u_gt_v ⟨1, by omega⟩
  have h2 := P.v_gt_u ⟨0, by omega⟩
  obtain ⟨z0, hz0⟩ := P.v_int ⟨0, by omega⟩
  obtain ⟨z1, hz1⟩ := P.v_int ⟨1, by omega⟩
  have c0 := (L.cloud_v τ ⟨0, by omega⟩).2
  have c1 := (L.cloud_v τ ⟨1, by omega⟩).1
  simp only at h1 h2
  have hlt : P.v ⟨1, by omega⟩ < P.v ⟨0, by omega⟩ := lt_trans h1 h2
  rw [hz0, hz1] at hlt
  have hz : z1 < z0 := by exact_mod_cast hlt
  have hz1' : (0 : ℝ) ≤ (z1 : ℝ) := by
    have : (((P.v ⟨1, by omega⟩ : ℚ) : ℝ)) = (z1 : ℝ) := by rw [hz1]; push_cast; rfl
    rw [← this]; exact c1
  have hz0' : (z0 : ℝ) ≤ L.Sc := by
    have : (((P.v ⟨0, by omega⟩ : ℚ) : ℝ)) = (z0 : ℝ) := by rw [hz0]; push_cast; rfl
    rw [← this]; exact c0
  have : (0 : ℤ) ≤ z1 := by exact_mod_cast hz1'
  have : (1 : ℝ) ≤ (z0 : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ z0 by omega)
  linarith

/- English proof (translation)
Introduce `D L C j ε n g ψ hR _`. Establish `hB` using `GlobalTheory.T.twistedDualOrbitPageWord_box L C j ε (1 : D.R.GG) (1 : D.R.GG) hR`. Take `⟨b1, w1, bw, bη, bS, hsz⟩` from `hB`. Use `⟨⟨b1, w1, bw, bη, bS, fun a => ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Establish `hB'` using `GlobalTheory.T.twistedDualOrbitPageWord_box L C j ε (g a) (1 : D.R.GG) hR`.

Establish `h` using `hB'.2.2.2.2.2 (0 : ZMod (orderOf (1 : D.R.GG)))`. Simplify using `only [pageWord, letter, one_pow, mul_one] at h`. Use `show etaHat L < (szT (hcAt D (g a)) j (pos ε (g a))).toNat`. Conclude with `Int.lt_toNat.mpr h`. Use `show 1 ≤ sHat L`.

Unfold `sHat`. Conclude with `Nat.le_floor (by exact_mod_cast one_le_Sc L)`. Use `show 1 ≤ etaHat L`. Unfold `etaHat`. Use linear arithmetic over natural numbers and integers.
-/
theorem recWord_small_pos : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {n : ℕ}
    (g : ZMod n → D.R.GG) (ψ : D.R.GG), Roomy L C → IsOrbit g ψ →
    Small (recWord L j ε g) ∧ 1 ≤ (recWord L j ε g).S ∧ 1 ≤ (recWord L j ε g).η := by
  intro D L C j ε n g ψ hR _
  have hB := GlobalTheory.T.twistedDualOrbitPageWord_box L C j ε (1 : D.R.GG) (1 : D.R.GG) hR
  obtain ⟨b1, w1, bw, bη, bS, hsz⟩ := hB
  refine ⟨⟨b1, w1, bw, bη, bS, fun a => ?_⟩, ?_, ?_⟩
  · have hB' := GlobalTheory.T.twistedDualOrbitPageWord_box L C j ε (g a) (1 : D.R.GG) hR
    have h := hB'.2.2.2.2.2 (0 : ZMod (orderOf (1 : D.R.GG)))
    simp only [pageWord, letter, one_pow, mul_one] at h
    show etaHat L < (szT (hcAt D (g a)) j (pos ε (g a))).toNat
    exact Int.lt_toNat.mpr h
  · show 1 ≤ sHat L
    unfold sHat
    exact Nat.le_floor (by exact_mod_cast one_le_Sc L)
  · show 1 ≤ etaHat L
    unfold etaHat; omega

end GlobalTheory.HTW.Rec
