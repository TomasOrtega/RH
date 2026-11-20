import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.ThmFD
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdegTransfer
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdConsA

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

/- English proof (translation)
Establish `hsa : StrictAnti lam` using `(fdc_stdGap hlam hgap hh).1`. Establish `key : ∀ t : ℕ, ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (T : KType ε (lowK ε (lamT lam t))) (j : T.V →L[ℂ] H), FData ε (lamT lam t) σ T j ∧ (∃ (H' : Type) (_ : NormedAddCommGroup H') (_ …`. Introduce `t`. Establish `hμ` using `isHCParam_lamT hlam t`. Establish `hg : GapAtLeast ε (lamT lam t) (h + t)` using `gap_lamT hsa hgap t`.

Establish `ht : (0 : ℝ) ≤ t` using `Nat.cast_nonneg t`. Establish `hh' : thrStar ε + 1 < h + t` using `by linarith`. Establish `hstd` using `fdc_stdGap hμ hg hh'`. Set `T : KType ε (lowK ε (lamT lam t))` to `(HW.kType_exists ε _ hμ).some`. Take `⟨m, hm, hP⟩` from `fdc_model hp hq hμ hg hh' T`.

Take `⟨d, H, i1, i2, σ, hDS, hd⟩` from `fdc_ds_exists hp hq hμ hg hh'`. Use `haveI : CompleteSpace H := hDS.1`. Take `⟨j, hiso, hk, -, hform⟩` from `anyF hDS hstd hP`. Establish `hΨ : ∀ z : PCoord ε → ℂ, PsiM T m (NormedSpace.exp (pmat z)) = fF ε (lamT lam t) T (pmat z)`. Introduce `z`.

Rewrite using `[psiM_exp_pmat, psM_exp_pmat hm T z]`. Take `⟨H', i1', i2', σ', w', hsm, hlink⟩` from `Lap.Base.link n ε _ T (PsiM T m) hstd hP`. Use `⟨H, i1, i2, inferInstance, σ, T, j, ⟨hDS.2.2.1, hiso, hk, fun z => ?_⟩, ⟨H', i1', i2', σ', w', hsm, fun z => ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hform _ (exp_pmat_inUJ z), hΨ]`. Rewrite using `[hlink _ (exp_pmat_inUJ z), hΨ]`.

Rewrite using `[fdcD_eq hμ hg hh' ⟨H, i1, i2, σ, hDS, hd⟩]`. Conclude with `hd`. Use `choose H i1 i2 i3 σ T j hF hsm hd using key`. Conclude with `thmFD Lap.Base.b3 hp hq hlam hgap hh (fdcD ε) (fdc_step hp hq hh) H σ T j (Filter.Eventually.of_forall hF) (Filter.Eventually.of_forall hsm) (Filter.Eventually.of_forall hd)`.
-/
theorem fdc_cd {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) {lam : Fin n → ℝ} (hlam : IsHCParam lam)
    {h : ℝ} (hgap : GapAtLeast ε lam h) (hh : thrStar ε + 1 < h) : fdcD ε lam = dimVlam lam := by
  have hsa : StrictAnti lam := (fdc_stdGap hlam hgap hh).1
  have key : ∀ t : ℕ, ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
      (T : KType ε (lowK ε (lamT lam t))) (j : T.V →L[ℂ] H),
      FData ε (lamT lam t) σ T j ∧
      (∃ (H' : Type) (_ : NormedAddCommGroup H') (_ : InnerProductSpace ℂ H')
        (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) (w' : H'), Lap.Base.IsHWSmooth ε σ' (lamT lam t) w' ∧
          ∀ z : PCoord ε → ℂ, ⟪w', σ' (NormedSpace.exp (pmat z)) w'⟫_ℂ =
            ⟪T.w, fF ε (lamT lam t) T (pmat z) T.w⟫_ℂ) ∧
      Formalism.MainNotions.S.IsFdeg (muCD ε) σ (fdcD ε (lamT lam t)) := by
    intro t
    have hμ := isHCParam_lamT hlam t
    have hg : GapAtLeast ε (lamT lam t) (h + t) := gap_lamT hsa hgap t
    have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    have hh' : thrStar ε + 1 < h + t := by linarith
    have hstd := fdc_stdGap hμ hg hh'
    let T : KType ε (lowK ε (lamT lam t)) := (HW.kType_exists ε _ hμ).some
    obtain ⟨m, hm, hP⟩ := fdc_model hp hq hμ hg hh' T
    obtain ⟨d, H, i1, i2, σ, hDS, hd⟩ := fdc_ds_exists hp hq hμ hg hh'
    haveI : CompleteSpace H := hDS.1
    obtain ⟨j, hiso, hk, -, hform⟩ := anyF hDS hstd hP
    have hΨ : ∀ z : PCoord ε → ℂ, PsiM T m (NormedSpace.exp (pmat z)) = fF ε (lamT lam t) T (pmat z) := by
      intro z
      rw [psiM_exp_pmat, psM_exp_pmat hm T z]
    obtain ⟨H', i1', i2', σ', w', hsm, hlink⟩ := Lap.Base.link n ε _ T (PsiM T m) hstd hP
    refine ⟨H, i1, i2, inferInstance, σ, T, j, ⟨hDS.2.2.1, hiso, hk, fun z => ?_⟩,
      ⟨H', i1', i2', σ', w', hsm, fun z => ?_⟩, ?_⟩
    · rw [hform _ (exp_pmat_inUJ z), hΨ]
    · rw [hlink _ (exp_pmat_inUJ z), hΨ]
    · rw [fdcD_eq hμ hg hh' ⟨H, i1, i2, σ, hDS, hd⟩]
      exact hd
  choose H i1 i2 i3 σ T j hF hsm hd using key
  exact thmFD Lap.Base.b3 hp hq hlam hgap hh (fdcD ε) (fdc_step hp hq hh) H σ T j
    (Filter.Eventually.of_forall hF) (Filter.Eventually.of_forall hsm) (Filter.Eventually.of_forall hd)

/- English proof (translation)
Take `⟨d, hd⟩` from `fdcGood_of_isDS hσ`. Establish `hgood : FdcGood ε lam d` using `⟨H, inferInstance, inferInstance, σ, hσ, hd⟩`. Establish `h1 : fdcD ε lam = d` using `fdcD_eq hlam hgap hh hgood`. Rewrite using `[← fdc_cd hp hq hlam hgap hh, h1]`. Take `⟨hdpos, hint⟩` from `hd`.

Take `⟨-, hI⟩` from `hint v v v v`. Establish `h3 : (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.coefOn σ v v g * star (Formalism.MainNotions.S.coefOn σ v v g)) = fun g : Formalism.REAL.UJ ε => ((‖Formalism.MainNotions.S.coefOn σ v v g‖ ^ 2 : ℝ) : ℂ)`. Use function extensionality and compare the values at `g`. Use `first`. Consider the case `(rw [RCLike.star_def, RCLike.mul_conj]; push_cast; ring_nf; done)`.

Consider the case `(rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring_nf; done)`. Consider the case `(simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]; done)`. Consider the case `(simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.sq_norm]; done)`. Consider the case `(simp [RCLike.mul_conj]; done)`. Rewrite `hI` using `[h3]`.

Apply the tactic sequence `first | rw [integral_complex_ofReal] at hI | rw [integral_ofReal] at hI`. Rewrite `hI` using `[inner_self_eq_norm_sq_to_K]`. Establish `hJ : ∫ g, ‖Formalism.MainNotions.S.coefOn σ v v g‖ ^ 2 ∂(muCD ε) = ‖v‖ ^ 4 / d`. Establish `h4 : ((∫ g, ‖Formalism.MainNotions.S.coefOn σ v v g‖ ^ 2 ∂(muCD ε) : ℝ) : ℂ) = ((‖v‖ ^ 4 / d : ℝ) : ℂ)`. Rewrite using `[hI]`.

Apply the tactic sequence `first | (push_cast; ring_nf; done) | (simp; done) | (norm_cast; ring_nf; done) | (simp; ring_nf; done)`. Conclude with `h4` after adjusting the coercions. Establish `hv4 : ‖v‖ ^ 4 ≠ 0` using `pow_ne_zero _ (norm_ne_zero_iff.2 hv)`. Unfold `Formalism.MainNotions.S.fdegOf`. Rewrite using `[hJ]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem fdCons_cd {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) {lam : Fin n → ℝ} (hlam : IsHCParam lam)
    {h : ℝ} (hgap : GapAtLeast ε lam h) (hh : thrStar ε + 1 < h)
    (hΨ : ∀ μ : Fin n → ℝ, IsHCParam μ → GapAtLeast ε μ h →
      ∃ (T : KType ε (lowK ε μ)) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), IsPsiFor ε μ T Ψ)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsDS ε lam σ) {v : H} (hv : v ≠ 0) :
    Formalism.MainNotions.S.fdegOf (muCD ε) σ v = dimVlam lam := by
  obtain ⟨d, hd⟩ := fdcGood_of_isDS hσ
  have hgood : FdcGood ε lam d := ⟨H, inferInstance, inferInstance, σ, hσ, hd⟩
  have h1 : fdcD ε lam = d := fdcD_eq hlam hgap hh hgood
  rw [← fdc_cd hp hq hlam hgap hh, h1]
  obtain ⟨hdpos, hint⟩ := hd
  obtain ⟨-, hI⟩ := hint v v v v
  have h3 : (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.coefOn σ v v g * star (Formalism.MainNotions.S.coefOn σ v v g)) =
      fun g : Formalism.REAL.UJ ε => ((‖Formalism.MainNotions.S.coefOn σ v v g‖ ^ 2 : ℝ) : ℂ) := by
    funext g
    first
      | (rw [RCLike.star_def, RCLike.mul_conj]; push_cast; ring_nf; done)
      | (rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring_nf; done)
      | (simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]; done)
      | (simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.sq_norm]; done)
      | (simp [RCLike.mul_conj]; done)
  rw [h3] at hI
  first | rw [integral_complex_ofReal] at hI | rw [integral_ofReal] at hI
  rw [inner_self_eq_norm_sq_to_K] at hI
  have hJ : ∫ g, ‖Formalism.MainNotions.S.coefOn σ v v g‖ ^ 2 ∂(muCD ε) = ‖v‖ ^ 4 / d := by
    have h4 : ((∫ g, ‖Formalism.MainNotions.S.coefOn σ v v g‖ ^ 2 ∂(muCD ε) : ℝ) : ℂ) = ((‖v‖ ^ 4 / d : ℝ) : ℂ) := by
      rw [hI]
      first | (push_cast; ring_nf; done) | (simp; done) | (norm_cast; ring_nf; done) | (simp; ring_nf; done)
    exact_mod_cast h4
  have hv4 : ‖v‖ ^ 4 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hv)
  unfold Formalism.MainNotions.S.fdegOf
  rw [hJ]
  field_simp

/- English proof (translation)
Use `haveI := muCD_isHaar ε`. Take `⟨κ, hκ0, hκtop, hκ⟩ : ∃ κ : ENNReal, κ ≠ 0 ∧ κ ≠ ⊤ ∧ muCD ε = κ • Formalism.REAL.muG ε` from `by first`. Consider the case `exact MeasureTheory.Measure.isHaarMeasure_eq_smul_isHaarMeasure _ _`. Consider the case `exact ⟨muCD ε (Classical.arbitrary (TopologicalSpace.PositiveCompacts (Formalism.REAL.UJ ε))), (MeasureTheory.Measure.measure_pos_of_nonempty_interior _ (Classical.arbitrary (TopologicalSpace.PositiveCompacts (Formalism.REAL.UJ ε))).interior_nonempty).ne', (Classical.arbitrary (T …`. Use `⟨κ.toReal, ENNReal.toReal_pos hκ0 hκtop, ?_⟩` and prove the remaining obligations.

Introduce `lam H _ _ _ σ v hlam hσ h hgap hh hp hq hΨ hv`. Establish `hcd` using `fdCons_cd hp hq hlam hgap hh hΨ hσ hv`. Establish `hfd : Formalism.QuantumDeterminants.fdegHC lam = dimVlam lam` using `rfl`. Rewrite `hcd` using `[hκ]`. Unfold `Formalism.MainNotions.S.fdegOf at hcd ⊢`.

Rewrite `hcd` using `[MeasureTheory.integral_smul_measure, smul_eq_mul]`. Rewrite using `[hfd, ← hcd]`. Establish `hκ' : κ.toReal ≠ 0` using `(ENNReal.toReal_pos hκ0 hκtop).ne'`. Distinguish the cases in `hI : ∫ g, ‖Formalism.MainNotions.S.coefOn σ v v g‖ ^ 2 ∂(Formalism.REAL.muG ε) = 0`. Rewrite using `[hI]`.

Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts.
-/
theorem fdCons_muG (n : ℕ) (ε : Fin n → Bool) : ∃ c : ℝ, 0 < c ∧
    ∀ (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H),
      Formalism.QuantumDeterminants.IsHCParam lam → Formalism.MainNotions.S.IsDS ε lam σ → ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h →
      thrStar ε + 1 < h → 1 ≤ pOf ε → 1 ≤ qOf ε →
      (∀ μ : Fin n → ℝ, IsHCParam μ → GapAtLeast ε μ h →
        ∃ (T : KType ε (lowK ε μ)) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), IsPsiFor ε μ T Ψ) →
      v ≠ 0 → Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) σ v = c * Formalism.QuantumDeterminants.fdegHC lam := by
  haveI := muCD_isHaar ε
  obtain ⟨κ, hκ0, hκtop, hκ⟩ : ∃ κ : ENNReal, κ ≠ 0 ∧ κ ≠ ⊤ ∧ muCD ε = κ • Formalism.REAL.muG ε := by
    first
      | exact MeasureTheory.Measure.isHaarMeasure_eq_smul_isHaarMeasure _ _
      | exact ⟨muCD ε (Classical.arbitrary (TopologicalSpace.PositiveCompacts (Formalism.REAL.UJ ε))),
          (MeasureTheory.Measure.measure_pos_of_nonempty_interior _
            (Classical.arbitrary (TopologicalSpace.PositiveCompacts (Formalism.REAL.UJ ε))).interior_nonempty).ne',
          (Classical.arbitrary (TopologicalSpace.PositiveCompacts (Formalism.REAL.UJ ε))).isCompact.measure_lt_top.ne,
          MeasureTheory.Measure.haarMeasure_unique _ _⟩
  refine ⟨κ.toReal, ENNReal.toReal_pos hκ0 hκtop, ?_⟩
  intro lam H _ _ _ σ v hlam hσ h hgap hh hp hq hΨ hv
  have hcd := fdCons_cd hp hq hlam hgap hh hΨ hσ hv
  have hfd : Formalism.QuantumDeterminants.fdegHC lam = dimVlam lam := rfl
  rw [hκ] at hcd
  unfold Formalism.MainNotions.S.fdegOf at hcd ⊢
  rw [MeasureTheory.integral_smul_measure, smul_eq_mul] at hcd
  rw [hfd, ← hcd]
  have hκ' : κ.toReal ≠ 0 := (ENNReal.toReal_pos hκ0 hκtop).ne'
  by_cases hI : ∫ g, ‖Formalism.MainNotions.S.coefOn σ v v g‖ ^ 2 ∂(Formalism.REAL.muG ε) = 0
  · rw [hI]; simp
  · field_simp

end ReciprocityTheory.ChartRestriction.DS
