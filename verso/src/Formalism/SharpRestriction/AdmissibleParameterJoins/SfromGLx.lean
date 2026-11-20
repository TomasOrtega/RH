import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLu
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker

noncomputable section

namespace Formalism.MainNotions.J

open NumberField Formalism.BasicNotions

/- English proof (translation)
Establish `hF` using `BridgeLemma.splitsCompl_down D.host.F D.host.E p hp h`. Use `⟨?_, fun v hv => ?_⟩` and prove the remaining obligations. Conclude with `(Nat.card_coe_set_eq _).trans ((BridgeLemma.ncard_plOver D.host.F hp hF).trans (finrank_F_eq D))`. Establish `h1` using `(hF v.asIdeal v.isMaximal hv).1`. Rewrite `h1` using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Then use the resulting hypothesis.
-/
theorem splitsF_of_splitsE (D : D7) (p : ℕ) (hp : p.Prime) (h : S.SplitsE D p) : StandardLattice.SplitsF D p := by
  have hF := BridgeLemma.splitsCompl_down D.host.F D.host.E p hp h
  refine ⟨?_, fun v hv => ?_⟩
  · exact (Nat.card_coe_set_eq _).trans ((BridgeLemma.ncard_plOver D.host.F hp hF).trans (finrank_F_eq D))
  · have h1 := (hF v.asIdeal v.isMaximal hv).1
    rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h1

/- English proof (translation)
The claim follows from `column_row_ranks_of_weak_columns D Lv h4 h2 hD ⟨hG, fun u => ⟨splitsF_of_splitsE D _ (D.mem u).A.T_prime (hT u), hM u⟩⟩`.
-/
theorem column_row_ranks_of_split (D : D7) (Lv : LevelData D) (h4 : StandardLattice.Conclusion4f D Lv) (h2 : StandardLattice.VolumeEqMass₂ D)
    (hD : StandardLattice.FactDstar D) (hG : StandardLattice.GBig D) (hT : ∀ u, S.SplitsE D (D.mem u).A.T) (hM : ∀ u, StandardLattice.Mu0Tie D u) :
    LocalBesselAndTopKernel.FamilyMidVolume D :=
  column_row_ranks_of_weak_columns D Lv h4 h2 hD ⟨hG, fun u => ⟨splitsF_of_splitsE D _ (D.mem u).A.T_prime (hT u), hM u⟩⟩

end Formalism.MainNotions.J

end
