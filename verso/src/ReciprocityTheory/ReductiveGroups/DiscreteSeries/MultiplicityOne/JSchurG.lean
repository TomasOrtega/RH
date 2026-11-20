import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSchurGA

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

/- English proof (translation)
Introduce `k r Wp _ _ _ D X _ hX`. Use `letI := X.hN`. Use `letI := X.hI`. Use `letI := X.hC`. Use `haveI : Nontrivial X.Hs := ⟨⟨X.w, 0, fun h => by`.

Establish `hw` using `X.w_norm`. Rewrite `hw` using `[h, norm_zero]`. Conclude with `zero_ne_one hw⟩⟩`. Take `⟨d, hd, h⟩` from `schur_GV D.haarG X.rep X.irr (fun v w => hX v w)`. Conclude with `⟨d, hd, fun v w v' w' => h v w v' w'⟩`.
-/
theorem stSchurG : StSchurG := by
  intro k r Wp _ _ _ D X _ hX
  letI := X.hN
  letI := X.hI
  letI := X.hC

  haveI : Nontrivial X.Hs := ⟨⟨X.w, 0, fun h => by
    have hw := X.w_norm
    rw [h, norm_zero] at hw
    exact zero_ne_one hw⟩⟩
  obtain ⟨d, hd, h⟩ := schur_GV D.haarG X.rep X.irr (fun v w => hX v w)
  exact ⟨d, hd, fun v w v' w' => h v w v' w'⟩

end ReciprocityTheory.ChartRestriction.DS.Mult1
