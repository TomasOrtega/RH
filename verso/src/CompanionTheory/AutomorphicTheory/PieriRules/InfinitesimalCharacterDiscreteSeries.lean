import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
import CompanionTheory.AutomorphicTheory.RankOneEstimates.DecSender
import CompanionTheory.AutomorphicTheory.RankOneEstimates.RankOne
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.AdmissibleOfIwasawa
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.HaarBumpFunctions.PoulsenSmoothVectorsDense
import CompanionTheory.AutomorphicTheory.PieriRules.HarishChandraFormalDegree
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyclicVectors
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory

namespace CompanionTheory.PieriExpansion

/- English proof (translation)
Introduce `k r ε lam R Wp _ _ _ _ z u π μW μN hR hz hT hπ hW hN`. Take `⟨h, hg, hok⟩` from `hR.gap`. Conclude with `CompanionTheory.FamilyDerivativeExpansion.M1.be_rank_one hok.1 hR.hc hR.ds hg hok.2.1 hz hT hπ hW hN`.
-/
theorem rank_one_pieri : RankOneG := by
  intro k r ε lam R Wp _ _ _ _ z u π μW μN hR hz hT hπ hW hN
  obtain ⟨h, hg, hok⟩ := hR.gap
  exact CompanionTheory.FamilyDerivativeExpansion.M1.be_rank_one hok.1 hR.hc hR.ds hg hok.2.1 hz hT hπ hW hN

/- English proof (translation)
Introduce `_ _ ε lam H _ _ σ _ _ hl hσ` and use `CompanionTheory.D.DSIC.discrete_series_infinitesimal_character _ ε lam H σ hl hσ`.
-/
theorem infinitesimal_character_discrete_series : InfCharG := fun _ _ ε lam H _ _ σ _ _ hl hσ =>
  CompanionTheory.D.DSIC.discrete_series_infinitesimal_character _ ε lam H σ hl hσ

/- English proof (translation)
The claim follows from `Fd.thrS_lt ε (by omega) (by have h1 := hok.2.1 have h2 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 _ nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg ((2 * r + k + 1 : ℕ) : ℝ)), sq_nonneg ((2 * r + k + 1 : ℕ) : ℝ)])`.
-/
theorem thrS_lt_of_gapOK {k r : ℕ} (ε : Fin (2 * r + k + 1) → Bool) {h : ℝ} (hok : GapOK k r h) :
    ReciprocityTheory.ChartRestriction.DS.G2.thrS ε + 1 < h :=
  Fd.thrS_lt ε (by omega) (by
    have h1 := hok.2.1
    have h2 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 _
    nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg ((2 * r + k + 1 : ℕ) : ℝ)), sq_nonneg ((2 * r + k + 1 : ℕ) : ℝ)])

/- English proof (translation)
Introduce and unpack `k r ε mu hm ⟨P, hP⟩ ⟨h, hg, hok⟩`. Take `⟨H, _, _, _, σ, hσ⟩` from `Fd.dsExistsHpkG hP mu hm hg (by linarith [thrS_lt_of_gapOK ε hok])`. Conclude with `⟨{ H := H, σ := σ }, hm, hσ, h, hg, hok⟩`.
-/
theorem discrete_series_exist : DSExistG := by
  rintro k r ε mu hm ⟨P, hP⟩ ⟨h, hg, hok⟩
  obtain ⟨H, _, _, _, σ, hσ⟩ := Fd.dsExistsHpkG hP mu hm hg
    (by linarith [thrS_lt_of_gapOK ε hok])
  exact ⟨{ H := H, σ := σ }, hm, hσ, h, hg, hok⟩

/- English proof (translation)
Introduce `k r ε mu mu' R R' h h'` and use `CompanionTheory.D.gk.Poul.poulsen_smooth_vectors_dense k r ε mu mu' R R' (GlobalTheory.isDS_of_isDG h) (GlobalTheory.isDS_of_isDG h')`.
-/
theorem poulsen_discrete_series : PoulsenG := fun k r ε mu mu' R R' h h' =>
  CompanionTheory.D.gk.Poul.poulsen_smooth_vectors_dense k r ε mu mu' R R' (GlobalTheory.isDS_of_isDG h) (GlobalTheory.isDS_of_isDG h')

/- English proof (translation)
Introduce and unpack `k r ε ⟨Q, hQ⟩`. Distinguish the cases in `hk : 1 ≤ k`. Take `⟨c, hc, h⟩` from `Fd.harish_chandra_formal_degree _ ε (Fd.one_le_pOf hk hQ) (Fd.one_le_qOf hQ)`. Use `⟨c, hc, ?_⟩` and prove the remaining obligations. Introduce and unpack `lam H _ _ _ σ ⟨g, hg, hok⟩ hl hσ`.

Conclude with `h lam H σ hl hσ g hg (thrS_lt_of_gapOK ε hok)`. Use `⟨1, one_pos, ?_⟩` and prove the remaining obligations. Introduce and unpack `lam H _ _ _ σ ⟨g, -, hok⟩`. Conclude with `absurd hok.1 hk`.
-/
theorem harish_chandra_formal_degree : HCFdegG := by
  rintro k r ε ⟨Q, hQ⟩
  by_cases hk : 1 ≤ k
  · obtain ⟨c, hc, h⟩ := Fd.harish_chandra_formal_degree _ ε (Fd.one_le_pOf hk hQ)
      (Fd.one_le_qOf hQ)
    refine ⟨c, hc, ?_⟩
    rintro lam H _ _ _ σ ⟨g, hg, hok⟩ hl hσ
    exact h lam H σ hl hσ g hg (thrS_lt_of_gapOK ε hok)
  · refine ⟨1, one_pos, ?_⟩
    rintro lam H _ _ _ σ ⟨g, -, hok⟩
    exact absurd hok.1 hk

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨CompanionTheory.FamilyDerivativeExpansion.DecS.decay_low_range, CompanionTheory.FamilyDerivativeExpansion.DecS.decay_infinite_range, CompanionTheory.D.gk.admitted.k_finite_smooth, rank_one_pieri⟩, CompanionTheory.D.Upq.Sm.smooth_cyclic_vectors, infinitesimal_character_discrete_ …`.
-/
theorem hypsG_of_zuck (hZ : ZuckG) : HypsG :=
  ⟨⟨CompanionTheory.FamilyDerivativeExpansion.DecS.decay_low_range, CompanionTheory.FamilyDerivativeExpansion.DecS.decay_infinite_range, CompanionTheory.D.gk.admitted.k_finite_smooth, rank_one_pieri⟩,
    CompanionTheory.D.Upq.Sm.smooth_cyclic_vectors, infinitesimal_character_discrete_series, discrete_series_exist, hZ, poulsen_discrete_series, harish_chandra_formal_degree⟩

end CompanionTheory.PieriExpansion
