import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.SegStartSpec
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.OddTops

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

/- English proof (translation)
Unfold `Cst.TLP`. Conclude with `lt_of_lt_of_le (by norm_num : (0 : ℝ) < 108) (le_trans (le_max_left _ _) (le_max_left _ _))`.
-/
theorem TLP_pos (K : Cst) : 0 < K.TLP := by
  unfold Cst.TLP
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 108) (le_trans (le_max_left _ _) (le_max_left _ _))

/- English proof (translation)
Establish `hK'` using `hK`. Unfold `Cst.Pos at hK'`. Establish `hCt : 0 < K.Ct` using `hK'.2.2.2.2.2.2.2.1`. Use `⟨K.TLP, 4 * K.Ct + 4, TLP_pos K, by linarith, ?_⟩` and prove the remaining obligations. Introduce `CH hCH C hC X h`.

Establish `B` using `base_of K hK CH hCH X h`. Establish `h'` using `h`. Unfold `Dat.Hyp HypI at h'`. Take `⟨-, -, -, -, -, -, hm, -, hb, -, -, -, -, -, -, -, -, -, -, -, -, -, hcs, -⟩` from `h'`. Establish `hd` using `dle_of hK hCH h B`.

Establish `hp` using `B.hp25`. Conclude with `{ cst := hcs bpos := hb ppos := by exact_mod_cast (show (0 : ℝ) < X.p by linarith) m2 := by omega D1nn := D1nn_of hK B four_depth_lt_conductor := four_depth_lt_conductor_of_bounds hd hcs dle := hd a8 := second_moment_of_columns hCH B eps := eps_of hCH B lowa := lowa_of B lowb := …`.
-/
theorem thrLP_of (hO : RestOddTops) (K : Cst) (hK : K.Pos) : TransportedAlt K (FactsLP K) := by
  have hK' := hK
  unfold Cst.Pos at hK'
  have hCt : 0 < K.Ct := hK'.2.2.2.2.2.2.2.1
  refine ⟨K.TLP, 4 * K.Ct + 4, TLP_pos K, by linarith, ?_⟩
  intro CH hCH C hC X h
  have B := base_of K hK CH hCH X h
  have h' := h
  unfold Dat.Hyp HypI at h'
  obtain ⟨-, -, -, -, -, -, hm, -, hb, -, -, -, -, -, -, -, -, -, -, -, -, -, hcs, -⟩ := h'
  have hd := dle_of hK hCH h B
  have hp := B.hp25
  exact
    { cst := hcs
      bpos := hb
      ppos := by exact_mod_cast (show (0 : ℝ) < X.p by linarith)
      m2 := by omega
      D1nn := D1nn_of hK B
      four_depth_lt_conductor := four_depth_lt_conductor_of_bounds hd hcs
      dle := hd
      a8 := second_moment_of_columns hCH B
      eps := eps_of hCH B
      lowa := lowa_of B
      lowb := lowb_of h
      tle := fun aw bw hw => tle_of hO hK hC h B aw bw hw }

/- English proof (translation)
Conclude with `thrLP_of restOddTops K hK`.
-/
theorem thrLP (K : Cst) (hK : K.Pos) : TransportedAlt K (FactsLP K) := by
  exact thrLP_of restOddTops K hK

end Formalism.MainNotions.flipOneThree.Pf

end
