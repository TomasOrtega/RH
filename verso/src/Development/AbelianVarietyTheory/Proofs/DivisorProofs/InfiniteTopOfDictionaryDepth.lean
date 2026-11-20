import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbLLMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMeanLogAreaLogThetaNormLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingsCurveFieldAboveFiniteNonemptyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalEqualSignKernelsLargeConstantsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTopBoundOfInputsStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat

open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

namespace GlobalTheory.KerConjMean

/- English proof (translation)
Introduce `D large₂ Γ _ _ Pl0 T A Ks _ _ _ R F hS`. Take `⟨-, hSz, -, -, -, -, -, -, -, hrd, hcond, -⟩` from `hS.size`. Establish `hb : Real.log large₂.sc.b = large₂.sc.x ^ large₂.sc.eps`. Simplify using `[Formalism.BasicNotions.Scale.b, Formalism.BasicNotions.Scale.L]`. Establish `hL1 : 1 ≤ large₂.sc.x ^ large₂.sc.eps` using `Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le`.

Establish `hqd : |large₂.logDerivativeAtOne| ≤ large₂.sc.x ^ large₂.sc.eps` using `hSz.2.2.2.2.2.2.1.2.2.2.2.2.1`. Establish `he : large₂.logDerivativeAtOne = logDerivativeAtOne D`. Rewrite using `[large₂.logDerivative_at_one_eq]`. Both sides reduce to the same expression. Rewrite using `[hb]`.

Use `⟨hL1, ?_, he ▸ hqd⟩` and prove the remaining obligations. Establish `: Real.log D.host.rdE ≤ large₂.sc.L / 100` using `hrd.trans hcond`. Simplify using `only [Formalism.BasicNotions.Scale.L] at this`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sizes : ∀ (D : D7) (large₂ : SizeData₂ D) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
    1 ≤ Real.log large₂.sc.b ∧ Real.log D.host.rdE ≤ Real.log large₂.sc.b ∧ |logDerivativeAtOne D| ≤ Real.log large₂.sc.b := by
  intro D large₂ Γ _ _ Pl0 T A Ks _ _ _ R F hS
  obtain ⟨-, hSz, -, -, -, -, -, -, -, hrd, hcond, -⟩ := hS.size
  have hb : Real.log large₂.sc.b = large₂.sc.x ^ large₂.sc.eps := by
    simp [Formalism.BasicNotions.Scale.b, Formalism.BasicNotions.Scale.L]
  have hL1 : 1 ≤ large₂.sc.x ^ large₂.sc.eps := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hqd : |large₂.logDerivativeAtOne| ≤ large₂.sc.x ^ large₂.sc.eps := hSz.2.2.2.2.2.2.1.2.2.2.2.2.1
  have he : large₂.logDerivativeAtOne = logDerivativeAtOne D := by
    rw [large₂.logDerivative_at_one_eq]
    rfl
  rw [hb]
  refine ⟨hL1, ?_, he ▸ hqd⟩
  have : Real.log D.host.rdE ≤ large₂.sc.L / 100 := hrd.trans hcond
  simp only [Formalism.BasicNotions.Scale.L] at this
  linarith

/- English proof (translation)
Unfold `Formalism.PairingDivisionLocalBalance.meanInf`. Rewrite using `[Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Establish `hn : (0 : ℝ) < Module.finrank ℚ K` using `by exact_mod_cast Module.finrank_pos`. Establish `hc : (Fintype.card (InfinitePlace K) : ℝ) ≤ Module.finrank ℚ K`. Establish `h1` using `InfinitePlace.card_add_two_mul_card_eq_rank K`.

Establish `h2` using `InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := K)`. Conclude with `(by omega : Fintype.card (InfinitePlace K) ≤ Module.finrank ℚ K)` after adjusting the coercions. Establish `h3 : 2 / (Module.finrank ℚ K : ℝ) * ((Fintype.card (InfinitePlace K) : ℝ) * a0) ≤ 2 * a0`. Rewrite using `[div_mul_eq_mul_div, div_le_iff₀ hn]`. Use the polynomial consequences of the given equalities and inequalities.

Use polynomial arithmetic with `[h3]`.
-/
theorem meanInf_affine (K : Type) [Field K] [NumberField K] (a0 nD Gd : ℝ) (f g : InfinitePlace K → ℝ) (ha0 : 0 ≤ a0) :
    Formalism.PairingDivisionLocalBalance.meanInf K (fun v => a0 + nD * f v + Gd * g v) ≤
      2 * a0 + nD * Formalism.PairingDivisionLocalBalance.meanInf K f + Gd * Formalism.PairingDivisionLocalBalance.meanInf K g := by
  unfold Formalism.PairingDivisionLocalBalance.meanInf
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  have hn : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hc : (Fintype.card (InfinitePlace K) : ℝ) ≤ Module.finrank ℚ K := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank K
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := K)
    exact_mod_cast (by omega : Fintype.card (InfinitePlace K) ≤ Module.finrank ℚ K)
  have h3 : 2 / (Module.finrank ℚ K : ℝ) * ((Fintype.card (InfinitePlace K) : ℝ) * a0) ≤ 2 * a0 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hn]
    nlinarith
  nlinarith [h3]

/- English proof (translation)
Use `set s := hS.toFinset with hs`. Establish `hsne : s.Nonempty` using `by rwa [hs, Set.Finite.toFinset_nonempty]`. Establish `hcard : (Nat.card S : ℝ) = s.card`. Rewrite using `[hs, Nat.card_eq_card_finite_toFinset hS]`. Establish `hs1 : ∑ᶠ ρ ∈ S, h1 ρ = ∑ ρ ∈ s, h1 ρ` using `finsum_mem_eq_finite_toFinset_sum _ hS`.

Establish `hs2 : ∑ᶠ ρ ∈ S, h2 ρ = ∑ ρ ∈ s, h2 ρ` using `finsum_mem_eq_finite_toFinset_sum _ hS`. Establish `hc0 : (0 : ℝ) < s.card` using `by exact_mod_cast hsne.card_pos`. Use `set m := a0 + nD * ((∑ᶠ ρ ∈ S, h1 ρ) / Nat.card S) + Gd * ((∑ᶠ ρ ∈ S, h2 ρ) / Nat.card S) with hm`. Establish `key : ∑ ρ ∈ s, (a0 + nD * h1 ρ + Gd * h2 ρ) = ∑ _ρ ∈ s, m`. Rewrite using `[Finset.sum_const, nsmul_eq_mul, hm, hs1, hs2, hcard, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]`.

Clear the denominators using the available nonvanishing facts. Prove the components needed by the constructor for the conclusion. Take `⟨ρ, hρ, h⟩` from `Finset.exists_le_of_sum_le hsne key.le`. Conclude with `⟨ρ, by rwa [hs, Set.Finite.mem_toFinset] at hρ, h⟩`. Take `⟨ρ, hρ, h⟩` from `Finset.exists_le_of_sum_le hsne key.ge`.

Conclude with `⟨ρ, by rwa [hs, Set.Finite.mem_toFinset] at hρ, h⟩`.
-/
theorem exists_avg {α : Type} (S : Set α) (hS : S.Finite) (hne : S.Nonempty) (a0 nD Gd : ℝ) (h1 h2 : α → ℝ) :
    (∃ ρ ∈ S, a0 + nD * h1 ρ + Gd * h2 ρ ≤
      a0 + nD * ((∑ᶠ ρ ∈ S, h1 ρ) / Nat.card S) + Gd * ((∑ᶠ ρ ∈ S, h2 ρ) / Nat.card S)) ∧
    (∃ ρ ∈ S, a0 + nD * ((∑ᶠ ρ ∈ S, h1 ρ) / Nat.card S) + Gd * ((∑ᶠ ρ ∈ S, h2 ρ) / Nat.card S) ≤
      a0 + nD * h1 ρ + Gd * h2 ρ) := by
  set s := hS.toFinset with hs
  have hsne : s.Nonempty := by rwa [hs, Set.Finite.toFinset_nonempty]
  have hcard : (Nat.card S : ℝ) = s.card := by
    rw [hs, Nat.card_eq_card_finite_toFinset hS]
  have hs1 : ∑ᶠ ρ ∈ S, h1 ρ = ∑ ρ ∈ s, h1 ρ := finsum_mem_eq_finite_toFinset_sum _ hS
  have hs2 : ∑ᶠ ρ ∈ S, h2 ρ = ∑ ρ ∈ s, h2 ρ := finsum_mem_eq_finite_toFinset_sum _ hS
  have hc0 : (0 : ℝ) < s.card := by exact_mod_cast hsne.card_pos
  set m := a0 + nD * ((∑ᶠ ρ ∈ S, h1 ρ) / Nat.card S) + Gd * ((∑ᶠ ρ ∈ S, h2 ρ) / Nat.card S) with hm
  have key : ∑ ρ ∈ s, (a0 + nD * h1 ρ + Gd * h2 ρ) = ∑ _ρ ∈ s, m := by
    rw [Finset.sum_const, nsmul_eq_mul, hm, hs1, hs2, hcard, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    field_simp
  constructor
  · obtain ⟨ρ, hρ, h⟩ := Finset.exists_le_of_sum_le hsne key.le
    exact ⟨ρ, by rwa [hs, Set.Finite.mem_toFinset] at hρ, h⟩
  · obtain ⟨ρ, hρ, h⟩ := Finset.exists_le_of_sum_le hsne key.ge
    exact ⟨ρ, by rwa [hs, Set.Finite.mem_toFinset] at hρ, h⟩

/- English proof (translation)
Introduce `hP hI hD hDp`. Take `⟨C1, hC1, hmean⟩` from `GlobalTheory.T.exists_const_mean_logArea_logThetaNorm_le`. Take `⟨CF0, hCF⟩` from `GlobalTheory.T.conjugate_top_bound_of_inputs hP hI hD hDp C1 hC1`. Take `⟨CF0', hCF'⟩` from `GlobalTheory.T.rationalEqualSignKernels_largeConstants`. Use `⟨max CF0 CF0', fun CF hCF0 => ?_⟩` and prove the remaining obligations.

Take `⟨C0, hC0⟩` from `hCF CF (le_trans (le_max_left _ _) hCF0)`. Take `⟨C0', hC0'⟩` from `hCF' CF (le_trans (le_max_right _ _) hCF0)`. Use `⟨max C0 C0', fun ε C hC => ?_⟩` and prove the remaining obligations. Take `⟨x0, hx0⟩` from `hC0 ε C (le_trans (le_max_left _ _) hC)`. Take `⟨x0', hx0'⟩` from `hC0' ε C (le_trans (le_max_right _ _) hC)`.

Use `⟨max x0 x0', fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt hF => ?_⟩` and prove the remaining obligations. Take `⟨a0, nD, Gd, ha0, hnD, hGd, hsum, hbound⟩` from `hx0 D large₂ hε (le_trans (le_max_left _ _) hx) Γ Pl0 T A Ks R F hS ch hIs hAt hF`. Establish `hrat` using `hx0' D large₂ hε (le_trans (le_max_right _ _) hx) Γ Pl0 T A Ks R F hS ch hIs hAt hF`. Take `⟨hL1, hLrd, hLd⟩` from `sizes D large₂ Γ Pl0 T A Ks R F hS`. Take `⟨hmA, hmT⟩` from `hmean D (hI D) ch.S.Z.δ ch.S.Z.t0 ch.S.Z.crv ch.S.Z.pt0 _ hL1 hLrd hLd`.

Use `⟨fun p => a0 + nD * avg D ch.S.Z.δ ch.S.Z.t0 p.embedding (hArea D ch.S.Z.δ ch.S.Z.t0) + Gd * avg D ch.S.Z.δ ch.S.Z.t0 p.embedding (hTh D ch.S.Z.δ ch.S.Z.t0), ?_, ?_⟩` and prove the remaining obligations. Use `(meanInf_affine _ a0 nD Gd _ _ ha0).trans (le_trans ?_ hsum)` and prove the remaining obligations. Establish `e1` using `mul_le_mul_of_nonneg_left hmA hnD`. Establish `e2` using `mul_le_mul_of_nonneg_left hmT hGd`. Use the polynomial consequences of the given equalities and inequalities.

Introduce `p Φ β d hocc c j B v hv`. Take `⟨f, hf⟩` from `hrat Φ β d hocc c j`. Take `⟨u, rfl, hu⟩` from `hv`. Use `⟨f u, (hf u).symm, ?_⟩` and prove the remaining obligations. Take `⟨hfin, hne⟩` from `GlobalTheory.T.embeddingsCurveFieldAbove_finite_nonempty D (hI D) ch.S.Z.δ ch.S.Z.t0 ch.S.Z.crv ch.S.Z.pt0 p.embedding`.

Take `⟨⟨ρ₁, hρ₁, h₁⟩, ⟨ρ₂, hρ₂, h₂⟩⟩` from `exists_avg _ hfin hne a0 nD Gd (hArea D ch.S.Z.δ ch.S.Z.t0) (hTh D ch.S.Z.δ ch.S.Z.t0)`. Break down `le_or_gt 0 B with hB | hB` into its components or cases. Conclude with `(hbound Φ β d hocc c j f hf p.embedding ρ₁ hρ₁ u B hu).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 h₁) hB)`. Conclude with `(hbound Φ β d hocc c j f hf p.embedding ρ₂ hρ₂ u B hu).trans (mul_le_mul_of_nonpos_right (Real.exp_le_exp.2 h₂) hB.le)`.
-/
theorem infTopK : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → InfTopK := by
  intro hP hI hD hDp
  obtain ⟨C1, hC1, hmean⟩ := GlobalTheory.T.exists_const_mean_logArea_logThetaNorm_le
  obtain ⟨CF0, hCF⟩ := GlobalTheory.T.conjugate_top_bound_of_inputs hP hI hD hDp C1 hC1
  obtain ⟨CF0', hCF'⟩ := GlobalTheory.T.rationalEqualSignKernels_largeConstants
  refine ⟨max CF0 CF0', fun CF hCF0 => ?_⟩
  obtain ⟨C0, hC0⟩ := hCF CF (le_trans (le_max_left _ _) hCF0)
  obtain ⟨C0', hC0'⟩ := hCF' CF (le_trans (le_max_right _ _) hCF0)
  refine ⟨max C0 C0', fun ε C hC => ?_⟩
  obtain ⟨x0, hx0⟩ := hC0 ε C (le_trans (le_max_left _ _) hC)
  obtain ⟨x0', hx0'⟩ := hC0' ε C (le_trans (le_max_right _ _) hC)
  refine ⟨max x0 x0', fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt hF => ?_⟩
  obtain ⟨a0, nD, Gd, ha0, hnD, hGd, hsum, hbound⟩ :=
    hx0 D large₂ hε (le_trans (le_max_left _ _) hx) Γ Pl0 T A Ks R F hS ch hIs hAt hF
  have hrat := hx0' D large₂ hε (le_trans (le_max_right _ _) hx) Γ Pl0 T A Ks R F hS ch hIs hAt hF
  obtain ⟨hL1, hLrd, hLd⟩ := sizes D large₂ Γ Pl0 T A Ks R F hS
  obtain ⟨hmA, hmT⟩ := hmean D (hI D) ch.S.Z.δ ch.S.Z.t0 ch.S.Z.crv ch.S.Z.pt0 _ hL1 hLrd hLd
  refine ⟨fun p => a0 + nD * avg D ch.S.Z.δ ch.S.Z.t0 p.embedding (hArea D ch.S.Z.δ ch.S.Z.t0) +
    Gd * avg D ch.S.Z.δ ch.S.Z.t0 p.embedding (hTh D ch.S.Z.δ ch.S.Z.t0), ?_, ?_⟩
  · refine (meanInf_affine _ a0 nD Gd _ _ ha0).trans (le_trans ?_ hsum)
    have e1 := mul_le_mul_of_nonneg_left hmA hnD
    have e2 := mul_le_mul_of_nonneg_left hmT hGd
    nlinarith
  · intro p Φ β d hocc c j B v hv
    obtain ⟨f, hf⟩ := hrat Φ β d hocc c j
    obtain ⟨u, rfl, hu⟩ := hv
    refine ⟨f u, (hf u).symm, ?_⟩
    obtain ⟨hfin, hne⟩ := GlobalTheory.T.embeddingsCurveFieldAbove_finite_nonempty D (hI D) ch.S.Z.δ ch.S.Z.t0 ch.S.Z.crv ch.S.Z.pt0 p.embedding
    obtain ⟨⟨ρ₁, hρ₁, h₁⟩, ⟨ρ₂, hρ₂, h₂⟩⟩ := exists_avg _ hfin hne a0 nD Gd
      (hArea D ch.S.Z.δ ch.S.Z.t0) (hTh D ch.S.Z.δ ch.S.Z.t0)
    rcases le_or_gt 0 B with hB | hB
    · exact (hbound Φ β d hocc c j f hf p.embedding ρ₁ hρ₁ u B hu).trans
        (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 h₁) hB)
    · exact (hbound Φ β d hocc c j f hf p.embedding ρ₂ hρ₂ u B hu).trans
        (mul_le_mul_of_nonpos_right (Real.exp_le_exp.2 h₂) hB.le)

end GlobalTheory.KerConjMean
end
