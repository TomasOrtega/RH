import Mathlib
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.AmapsShExists
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ContractionMapsAtRepresentatives
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryMeasureDatumProductMeasureEqOfSameVectors
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormAdjointCompIsometryEquiv

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.CutBP2

namespace GlobalTheory.WigSh

/- English proof (translation)
Introduce `i hi`. Establish `hi'` using `Finset.mem_Icc.mp hi`. Take `⟨a, ha⟩` from `hP.int_u' i (Finset.mem_Icc.mpr ⟨hi'.1, by omega⟩)`. Take `⟨c, hc⟩` from `hP.int_u' (i + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)`. Establish `hg` using `hP.gap i hi`.

Unfold `M.Par.lo M.Par.hi at hg`. Establish `h1` using `le_max_right (P.u (i + 1)) (P.u' (i + 1))`. Establish `h2` using `min_le_right (P.u i) (P.u' i)`. Establish `h3 : ((1 : ℤ) : ℝ) ≤ ((a - c : ℤ) : ℝ)` using `by push_cast; linarith`. Establish `h4 : (1 : ℤ) ≤ a - c` using `by exact_mod_cast h3`.

Take `⟨N, hN⟩ : ∃ N : ℕ, a - c - 1 = (N : ℤ)` from `⟨(a - c - 1).toNat, by omega⟩`. Use `⟨N, ?_⟩` and prove the remaining obligations. Establish `h5 : ((a - c - 1 : ℤ) : ℝ) = ((N : ℤ) : ℝ)` using `by rw [hN]`. Move the coercions through the operations in `at h5`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem par_gap_right (P : M.Par) (hP : P.OK) :
    ∀ i ∈ Finset.Icc 1 (P.k - 1), ∃ N : ℕ, P.u' i - P.u' (i + 1) = (N : ℝ) + 1 := by
  intro i hi
  have hi' := Finset.mem_Icc.mp hi
  obtain ⟨a, ha⟩ := hP.int_u' i (Finset.mem_Icc.mpr ⟨hi'.1, by omega⟩)
  obtain ⟨c, hc⟩ := hP.int_u' (i + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have hg := hP.gap i hi
  unfold M.Par.lo M.Par.hi at hg
  have h1 := le_max_right (P.u (i + 1)) (P.u' (i + 1))
  have h2 := min_le_right (P.u i) (P.u' i)
  have h3 : ((1 : ℤ) : ℝ) ≤ ((a - c : ℤ) : ℝ) := by push_cast; linarith
  have h4 : (1 : ℤ) ≤ a - c := by exact_mod_cast h3
  obtain ⟨N, hN⟩ : ∃ N : ℕ, a - c - 1 = (N : ℤ) := ⟨(a - c - 1).toNat, by omega⟩
  refine ⟨N, ?_⟩
  have h5 : ((a - c - 1 : ℤ) : ℝ) = ((N : ℤ) : ℝ) := by rw [hN]
  push_cast at h5
  linarith

/- English proof (translation)
Take `⟨c₃, hc⟩` from `GlobalTheory.WigSh.contraction_maps_at_representatives`. Use `⟨c₃, ?_⟩` and prove the remaining obligations. Introduce `P Wp Wq Wqp Wqm _ _ _ _ _ _ _ _ _ _ _ _ up up' um um' p pp pm l n₀ b hpz hpz' hmz hmz' hpπ hmπ hpν hpm hmν hmm hl hlk hn hb hnb h1b hup hum`. Establish `h0` using `p.hT 0 (Nat.zero_le _)`. Establish `h1` using `pp.hT 0 (Nat.zero_le _)`.

Establish `h2` using `pm.hT 0 (Nat.zero_le _)`. Establish `hp : Q.IsType P.k P.r p.T.base.z' pp.T.base.π' up'` using `hpz' ▸ pp.hP.2.2.2.2.2.2`. Establish `hm : Q.IsType P.k P.r p.T.base.z' pm.T.base.π' um'` using `hmz' ▸ pm.hP.2.2.2.2.2.2`. Establish `hμp : pp.T.base.μSS = p.T.base.μSS` using `GlobalTheory.unitaryMeasureDatum_productMeasure_eq_of_same_vectors Wp Wq Wqp P.k P.r p.T.base pp.T.base hpz hpz' h0.1 h0.2.1 h1.1 h1.2.1 (h1.2.2.trans h0.2.2.symm)`. Establish `hμm : pm.T.base.μSS = p.T.base.μSS` using `GlobalTheory.unitaryMeasureDatum_productMeasure_eq_of_same_vectors Wp Wq Wqm P.k P.r p.T.base pm.T.base hmz hmz' h0.1 h0.2.1 h2.1 h2.2.1 (h2.2.2.trans h0.2.2.symm)`.

Take `⟨Ap', Am', hAp, hAm, hlow⟩` from `GlobalTheory.WigSh.exists_wigMap_pair_of_isType Wq Wqp Wqm P.k P.r p.T.base.z' p.T.base.π' pp.T.base.π' pm.T.base.π' P.u' up' um' l n₀ b p.T.base.z'_mem p.T.base.T'_pos p.hP.2.2.2.2.2.2 (par_gap_right P p.hP.1) hl hlk hn hb hnb h1b hp hm hup hum`. Take `⟨Ap, Am, ApPt, AmPt, hPp, hPm, hrep, -, hfac, he, hbp, hbm⟩` from `hc Wp Wq Wqp Wqm P.k P.r p.T.base pp.T.base pm.T.base p.ν' p.m₀ n₀ b Ap' Am' hpz hpz' hpπ hμp hmz hmz' hmπ hμm p.hF hAp hAm hlow`. Use `⟨Ap, Am, ApPt, AmPt, hPp, hPm, hrep, ?_⟩` and prove the remaining obligations. Introduce `A₀ f hA₀ hf`. Take `⟨hfp, hfm⟩` from `hfac A₀ f hA₀ hf`.

Use `⟨?_, ?_, he, hbp, hbm⟩` and prove the remaining obligations. Introduce `γ hγ hG`. Establish `h` using `hfp γ hγ hG`. Unfold `KB.Pl.V`. Rewrite using `[hpν, hpm]`.

Conclude with `h`. Introduce `γ hγ hG`. Establish `h` using `hfm γ hγ hG`. Unfold `KB.Pl.V`. Rewrite using `[hmν, hmm]`.

Conclude with `h`.
-/
theorem amapsShExists : GlobalTheory.WigSh.AmapsShExists := by
  obtain ⟨c₃, hc⟩ := GlobalTheory.WigSh.contraction_maps_at_representatives
  refine ⟨c₃, ?_⟩
  intro P Wp Wq Wqp Wqm _ _ _ _ _ _ _ _ _ _ _ _ up up' um um' p pp pm l n₀ b hpz hpz' hmz hmz' hpπ hmπ
    hpν hpm hmν hmm hl hlk hn hb hnb h1b hup hum
  have h0 := p.hT 0 (Nat.zero_le _)
  have h1 := pp.hT 0 (Nat.zero_le _)
  have h2 := pm.hT 0 (Nat.zero_le _)
  have hp : Q.IsType P.k P.r p.T.base.z' pp.T.base.π' up' := hpz' ▸ pp.hP.2.2.2.2.2.2
  have hm : Q.IsType P.k P.r p.T.base.z' pm.T.base.π' um' := hmz' ▸ pm.hP.2.2.2.2.2.2
  have hμp : pp.T.base.μSS = p.T.base.μSS :=
    GlobalTheory.unitaryMeasureDatum_productMeasure_eq_of_same_vectors Wp Wq Wqp P.k P.r p.T.base pp.T.base hpz hpz' h0.1 h0.2.1 h1.1 h1.2.1
      (h1.2.2.trans h0.2.2.symm)
  have hμm : pm.T.base.μSS = p.T.base.μSS :=
    GlobalTheory.unitaryMeasureDatum_productMeasure_eq_of_same_vectors Wp Wq Wqm P.k P.r p.T.base pm.T.base hmz hmz' h0.1 h0.2.1 h2.1 h2.2.1
      (h2.2.2.trans h0.2.2.symm)
  obtain ⟨Ap', Am', hAp, hAm, hlow⟩ := GlobalTheory.WigSh.exists_wigMap_pair_of_isType Wq Wqp Wqm P.k P.r p.T.base.z'
    p.T.base.π' pp.T.base.π' pm.T.base.π' P.u' up' um' l n₀ b p.T.base.z'_mem p.T.base.T'_pos
    p.hP.2.2.2.2.2.2 (par_gap_right P p.hP.1) hl hlk hn hb hnb h1b hp hm hup hum
  obtain ⟨Ap, Am, ApPt, AmPt, hPp, hPm, hrep, -, hfac, he, hbp, hbm⟩ :=
    hc Wp Wq Wqp Wqm P.k P.r p.T.base pp.T.base pm.T.base p.ν' p.m₀ n₀ b Ap' Am' hpz hpz' hpπ hμp hmz hmz' hmπ hμm
      p.hF hAp hAm hlow
  refine ⟨Ap, Am, ApPt, AmPt, hPp, hPm, hrep, ?_⟩
  intro A₀ f hA₀ hf
  obtain ⟨hfp, hfm⟩ := hfac A₀ f hA₀ hf
  refine ⟨?_, ?_, he, hbp, hbm⟩
  · intro γ hγ hG
    have h := hfp γ hγ hG
    unfold KB.Pl.V
    rw [hpν, hpm]
    exact h
  · intro γ hγ hG
    have h := hfm γ hγ hG
    unfold KB.Pl.V
    rw [hmν, hmm]
    exact h

end GlobalTheory.WigSh
