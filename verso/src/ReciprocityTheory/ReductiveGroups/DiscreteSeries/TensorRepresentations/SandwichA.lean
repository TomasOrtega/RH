import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CcARatioZero
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Weighted
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EquivSigLamOfIsDS
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.IsDSSigLam
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.InfChar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PsiPos
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdegTransfer
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Integr
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.GelfandG
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiMExpFormula
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExistsMu
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur

noncomputable section

open Finset MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

/- English proof (translation)
Assemble the required witnesses or components as `⟨lt_of_le_of_lt (le_max_left _ _) hth, lt_of_le_of_lt (le_max_right _ _) hth⟩`.
-/
theorem swA_thr {ε : Fin n → Bool} {h : ℝ} (hth : thrStar ε < h) :
    (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h ∧
      16 * (n : ℝ) * (S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (S7.q0 ε : ℝ)) < h :=
  ⟨lt_of_le_of_lt (le_max_left _ _) hth, lt_of_le_of_lt (le_max_right _ _) hth⟩

/- English proof (translation)
Take `⟨m, hm⟩` from `S7.exists_mu hlam`. Take `⟨h1, h2⟩` from `swA_thr hth`. Establish `hq1 : (0 : ℝ) ≤ (S7.q0 ε : ℝ)` using `Nat.cast_nonneg _`. Establish `hn0 : (0 : ℝ) ≤ (n : ℝ)` using `Nat.cast_nonneg _`. Establish `hsq : 0 ≤ Real.sqrt (2 * (S7.q0 ε : ℝ))` using `Real.sqrt_nonneg _`.

Establish `hnq : 0 ≤ (n : ℝ) * (S7.q0 ε : ℝ)` using `mul_nonneg hn0 hq1`. Establish `h8 : 8 * (n : ℝ) * S7.q0 ε < h` using `by nlinarith`. Establish `hs2 : 8 * (n : ℝ) * S7.q0 ε + 4 * 2 * Real.sqrt (2 * S7.q0 ε) < h` using `by nlinarith`. Establish `hgap : StdGap ε lam` using `⟨hlam.1, h, hh, h1⟩`. Establish `hP : IsPsiFor ε lam T (S7.PsiM T m)` using `⟨fun k₁ k₂ g hg => S7.psiM_equiv T m k₁ k₂ hg, S7.psiM_one T m, S7.psiM_smooth T m hm, fun g hg => S7.psiM_casimir T m hm hg, fun ν hν => by`.

Use `hν` as an intermediate fact. Conclude with `(S7.psiM_integrable T m hm hlam hh hq ν).2.1 h8⟩`. Establish `hv₀ : T.w ≠ 0` using `fun h0 => by simpa [h0] using T.w_norm`. Use `⟨S7.PsiM T m, hgap, hP, psi_exp_isPositive T (S7.PsiM T m) m hm (fun X hX => S7.psiM_exp_formula T m hX), weighted_datum hgap hP hv₀ (fun ν hν => ?_), hasGelfandChar_sigLam hgap hP hv₀ (fun k g hg => S7.psiM_gelfand T m hm k hg)⟩` and prove the remaining obligations. Use `hν` as an intermediate fact.

Conclude with `(S7.psiM_integrable T m hm hlam hh hq ν).2.2 2 (by norm_num) hs2`.
-/
theorem swA_model {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : S7.IsHCParam lam) (hq : 1 ≤ S7.q0 ε) {h : ℝ}
    (hh : GapAtLeast ε lam h) (hth : thrStar ε < h) (T : S7.KType ε (lowK ε lam)) :
    ∃ Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V), StdGap ε lam ∧ IsPsiFor ε lam T Ψ ∧
      (∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive) ∧
      (∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ T.w), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ T.w),
        MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
          inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε)))
          2 (Formalism.REAL.muG ε)) ∧
      HasGelfandChar (smE ε (rreg ε)) lam (genSub (smE ε (rreg ε)) (datumV ε Ψ T.w)) := by
  obtain ⟨m, hm⟩ := S7.exists_mu hlam
  obtain ⟨h1, h2⟩ := swA_thr hth
  have hq1 : (0 : ℝ) ≤ (S7.q0 ε : ℝ) := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hsq : 0 ≤ Real.sqrt (2 * (S7.q0 ε : ℝ)) := Real.sqrt_nonneg _
  have hnq : 0 ≤ (n : ℝ) * (S7.q0 ε : ℝ) := mul_nonneg hn0 hq1
  have h8 : 8 * (n : ℝ) * S7.q0 ε < h := by nlinarith
  have hs2 : 8 * (n : ℝ) * S7.q0 ε + 4 * 2 * Real.sqrt (2 * S7.q0 ε) < h := by nlinarith
  have hgap : StdGap ε lam := ⟨hlam.1, h, hh, h1⟩
  have hP : IsPsiFor ε lam T (S7.PsiM T m) :=
    ⟨fun k₁ k₂ g hg => S7.psiM_equiv T m k₁ k₂ hg, S7.psiM_one T m, S7.psiM_smooth T m hm,
      fun g hg => S7.psiM_casimir T m hm hg, fun ν hν => by
        have := hν
        exact (S7.psiM_integrable T m hm hlam hh hq ν).2.1 h8⟩
  have hv₀ : T.w ≠ 0 := fun h0 => by simpa [h0] using T.w_norm
  refine ⟨S7.PsiM T m, hgap, hP, psi_exp_isPositive T (S7.PsiM T m) m hm (fun X hX => S7.psiM_exp_formula T m hX),
    weighted_datum hgap hP hv₀ (fun ν hν => ?_), hasGelfandChar_sigLam hgap hP hv₀ (fun k g hg => S7.psiM_gelfand T m hm k hg)⟩
  have := hν
  exact (S7.psiM_integrable T m hm hlam hh hq ν).2.2 2 (by norm_num) hs2

/- English proof (translation)
Take `⟨hd0, h⟩` from `hd`. Establish `hc : ∀ v w : A, Formalism.MainNotions.S.coefOn (ε` using `ε) τA v w = Formalism.MainNotions.S.coefOn (ε := ε) τB (U v) (U w) := by`. Introduce `v w`. Use function extensionality and compare the values at `g`. Simplify using `only [Formalism.MainNotions.S.coefOn]`.

Rewrite using `[← hU _ g.2, LinearIsometryEquiv.inner_map_map]`. Use `⟨hd0, fun v w v' w' => ?_⟩` and prove the remaining obligations. Take `⟨hi, he⟩` from `h (U v) (U w) (U v') (U w')`. Rewrite using `[hc v w, hc v' w']`. Use `⟨hi, ?_⟩` and prove the remaining obligations.

Rewrite using `[he, LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map]`.
-/
theorem swB_isFdeg_pull {ε : Fin n → Bool} {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] {τA : Matrix (Fin n) (Fin n) ℂ → (A →L[ℂ] A)}
    {τB : Matrix (Fin n) (Fin n) ℂ → (B →L[ℂ] B)} (U : A ≃ₗᵢ[ℂ] B)
    (hU : ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ x : A, U (τA g x) = τB g (U x)) {ν : Measure (Formalism.REAL.UJ ε)} {d : ℝ}
    (hd : Formalism.MainNotions.S.IsFdeg ν τB d) : Formalism.MainNotions.S.IsFdeg ν τA d := by
  obtain ⟨hd0, h⟩ := hd
  have hc : ∀ v w : A, Formalism.MainNotions.S.coefOn (ε := ε) τA v w = Formalism.MainNotions.S.coefOn (ε := ε) τB (U v) (U w) := by
    intro v w
    funext g
    simp only [Formalism.MainNotions.S.coefOn]
    rw [← hU _ g.2, LinearIsometryEquiv.inner_map_map]
  refine ⟨hd0, fun v w v' w' => ?_⟩
  obtain ⟨hi, he⟩ := h (U v) (U w) (U v') (U w')
  rw [hc v w, hc v' w']
  refine ⟨hi, ?_⟩
  rw [he, LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map]

/- English proof (translation)
Use `swB_isFdeg_pull U.symm (fun g hg y => ?_) hd` and prove the remaining obligations. Apply `U.injective` to reduce the goal to its premises. Rewrite using `[LinearIsometryEquiv.apply_symm_apply, hU g hg, LinearIsometryEquiv.apply_symm_apply]`.
-/
theorem swB_isFdeg_push {ε : Fin n → Bool} {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] {τA : Matrix (Fin n) (Fin n) ℂ → (A →L[ℂ] A)}
    {τB : Matrix (Fin n) (Fin n) ℂ → (B →L[ℂ] B)} (U : A ≃ₗᵢ[ℂ] B)
    (hU : ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ x : A, U (τA g x) = τB g (U x)) {ν : Measure (Formalism.REAL.UJ ε)} {d : ℝ}
    (hd : Formalism.MainNotions.S.IsFdeg ν τA d) : Formalism.MainNotions.S.IsFdeg ν τB d := by
  refine swB_isFdeg_pull U.symm (fun g hg y => ?_) hd
  apply U.injective
  rw [LinearIsometryEquiv.apply_symm_apply, hU g hg, LinearIsometryEquiv.apply_symm_apply]

/- English proof (translation)
Rewrite using `[← fdegOf_of_isFdeg' hd hw, ← fdegOf_of_isFdeg' hd' hw]`.
-/
theorem swB_isFdeg_unique {ε : Fin n → Bool} {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    {τ : Matrix (Fin n) (Fin n) ℂ → (A →L[ℂ] A)} {ν : Measure (Formalism.REAL.UJ ε)} {d d' : ℝ} {w : A} (hw : w ≠ 0)
    (hd : Formalism.MainNotions.S.IsFdeg ν τ d) (hd' : Formalism.MainNotions.S.IsFdeg ν τ d') : d = d' := by
  rw [← fdegOf_of_isFdeg' hd hw, ← fdegOf_of_isFdeg' hd' hw]

/- English proof (translation)
Establish `hs` using `Measure.haarScalarFactor_pos_of_isHaarMeasure ν (Formalism.REAL.muG ε)`. Establish `heq` using `Measure.isMulLeftInvariant_eq_smul ν (Formalism.REAL.muG ε)`. Establish `hc : (0 : ℝ) < (Measure.haarScalarFactor ν (Formalism.REAL.muG ε) : ℝ)` using `by exact_mod_cast hs`. Conclude with `⟨_, hc, by rw [ENNReal.ofReal_coe_nnreal]; exact heq⟩`.
-/
theorem swB_haar_eq {ε : Fin n → Bool} (ν : Measure (Formalism.REAL.UJ ε)) [ν.IsHaarMeasure] :
    ∃ c : ℝ, 0 < c ∧ ν = ENNReal.ofReal c • Formalism.REAL.muG ε := by
  have hs := Measure.haarScalarFactor_pos_of_isHaarMeasure ν (Formalism.REAL.muG ε)
  have heq := Measure.isMulLeftInvariant_eq_smul ν (Formalism.REAL.muG ε)
  have hc : (0 : ℝ) < (Measure.haarScalarFactor ν (Formalism.REAL.muG ε) : ℝ) := by exact_mod_cast hs
  exact ⟨_, hc, by rw [ENNReal.ofReal_coe_nnreal]; exact heq⟩

/- English proof (translation)
Establish `key : ∀ c : Fin n → ℝ, (∀ a b : Fin n, a ≠ b → |c a - c b| ≤ 1) → GapAtLeast ε (μ + c) (h - 1)`. Introduce `c hc a b hab`. Establish `hne : a ≠ b` using `fun e => hab (e ▸ rfl)`. Establish `h1` using `hμ a b hab`. Establish `h2` using `hc a b hne`.

Establish `h3 : |μ a - μ b| ≤ |(μ + c) a - (μ + c) b| + |c a - c b|`. Establish `: μ a - μ b = ((μ + c) a - (μ + c) b) - (c a - c b)` using `by simp only [Pi.add_apply]; ring`. Rewrite using `[this]`. Conclude with `abs_sub _ _`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hsingle : ∀ t : ℝ, |t| ≤ 1 → ∀ a b : Fin n, a ≠ b → |Pi.single (M` using `fun _ => ℝ) s t a - Pi.single (M := fun _ => ℝ) s t b| ≤ 1 := by`. Introduce `t ht a b hab`. Distinguish the cases in `ha : a = s`. Substitute `ha` using the available equality. Rewrite using `[Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hab), sub_zero]`.

Conclude with `ht`. Distinguish the cases in `hb : b = s`. Substitute `hb` using the available equality. Rewrite using `[Pi.single_eq_same, Pi.single_eq_of_ne ha, zero_sub, abs_neg]`. Conclude with `ht`.

Rewrite using `[Pi.single_eq_of_ne ha, Pi.single_eq_of_ne hb]`. Simplify using the standard rewrite rules. Consider the cases of `dual`. Conclude with `key _ (hsingle 1 (by simp))`. Establish `: shiftF true μ s = μ + Pi.single s (-1)`.

Simplify using `only [shiftF, cond_true]`. Rewrite using `[sub_eq_add_neg, Pi.single_neg]`. Rewrite using `[this]`. Conclude with `key _ (hsingle (-1) (by simp))`.
-/
theorem swC_gap_shift {ε : Fin n → Bool} {μ : Fin n → ℝ} {h : ℝ} (hμ : GapAtLeast ε μ h) (dual : Bool)
    (s : Fin n) : GapAtLeast ε (shiftF dual μ s) (h - 1) := by
  have key : ∀ c : Fin n → ℝ, (∀ a b : Fin n, a ≠ b → |c a - c b| ≤ 1) → GapAtLeast ε (μ + c) (h - 1) := by
    intro c hc a b hab
    have hne : a ≠ b := fun e => hab (e ▸ rfl)
    have h1 := hμ a b hab
    have h2 := hc a b hne
    have h3 : |μ a - μ b| ≤ |(μ + c) a - (μ + c) b| + |c a - c b| := by
      have : μ a - μ b = ((μ + c) a - (μ + c) b) - (c a - c b) := by simp only [Pi.add_apply]; ring
      rw [this]
      exact abs_sub _ _
    linarith
  have hsingle : ∀ t : ℝ, |t| ≤ 1 → ∀ a b : Fin n, a ≠ b → |Pi.single (M := fun _ => ℝ) s t a - Pi.single (M := fun _ => ℝ) s t b| ≤ 1 := by
    intro t ht a b hab
    by_cases ha : a = s
    · subst ha
      rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hab), sub_zero]
      exact ht
    · by_cases hb : b = s
      · subst hb
        rw [Pi.single_eq_same, Pi.single_eq_of_ne ha, zero_sub, abs_neg]
        exact ht
      · rw [Pi.single_eq_of_ne ha, Pi.single_eq_of_ne hb]
        simp
  cases dual
  · exact key _ (hsingle 1 (by simp))
  · have : shiftF true μ s = μ + Pi.single s (-1) := by
      simp only [shiftF, cond_true]
      rw [sub_eq_add_neg, Pi.single_neg]
    rw [this]
    exact key _ (hsingle (-1) (by simp))

/- English proof (translation)
Use `⟨hs, fun a => ?_⟩` and prove the remaining obligations. Take `⟨m, hm⟩` from `hμ.2 a`. Distinguish the cases in `ha : a = s`. Substitute `ha` using the available equality. Consider the cases of `dual`.

Conclude with `⟨m + 1, by simp only [shiftF, cond_false, Pi.add_apply, Pi.single_eq_same]; push_cast; linarith⟩`. Conclude with `⟨m - 1, by simp only [shiftF, cond_true, Pi.sub_apply, Pi.single_eq_same]; push_cast; linarith⟩`. Consider the cases of `dual`. Conclude with `⟨m, by simp only [shiftF, cond_false, Pi.add_apply, Pi.single_eq_of_ne ha, add_zero]; exact hm⟩`. Conclude with `⟨m, by simp only [shiftF, cond_true, Pi.sub_apply, Pi.single_eq_of_ne ha, sub_zero]; exact hm⟩`.
-/
theorem swC_hc_shift {μ : Fin n → ℝ} (hμ : S7.IsHCParam μ) (dual : Bool) (s : Fin n)
    (hs : StrictAnti (shiftF dual μ s)) : S7.IsHCParam (shiftF dual μ s) := by
  refine ⟨hs, fun a => ?_⟩
  obtain ⟨m, hm⟩ := hμ.2 a
  by_cases ha : a = s
  · subst ha
    cases dual
    · exact ⟨m + 1, by simp only [shiftF, cond_false, Pi.add_apply, Pi.single_eq_same]; push_cast; linarith⟩
    · exact ⟨m - 1, by simp only [shiftF, cond_true, Pi.sub_apply, Pi.single_eq_same]; push_cast; linarith⟩
  · cases dual
    · exact ⟨m, by simp only [shiftF, cond_false, Pi.add_apply, Pi.single_eq_of_ne ha, add_zero]; exact hm⟩
    · exact ⟨m, by simp only [shiftF, cond_true, Pi.sub_apply, Pi.single_eq_of_ne ha, sub_zero]; exact hm⟩

/- English proof (translation)
Use `hσ.1` as an intermediate fact. Use `hσ'.1` as an intermediate fact. Establish `hq0 : 1 ≤ S7.q0 ε` using `le_min hp hq`. Establish `hth : thrStar ε < h` using `by linarith`. Establish `hth' : thrStar ε < h - 1` using `by linarith`.

Establish `hlam'` using `swC_hc_shift hμ dual s hs`. Establish `hgap'` using `swC_gap_shift hgap dual s`. Take `⟨T⟩` from `HW.kType_exists ε μ hμ`. Take `⟨T'⟩` from `HW.kType_exists ε (shiftF dual μ s) hlam'`. Take `⟨Ψ, hS, hP, hpos, hW, hG⟩` from `swA_model hμ hq0 hgap hth T`.

Take `⟨Ψ', hS', hP', hpos', hW', hG'⟩` from `swA_model hlam' hq0 hgap' hth' T'`. Establish `hv₀ : T.w ≠ 0` using `fun h0 => by simpa [h0] using T.w_norm`. Establish `hv₀' : T'.w ≠ 0` using `fun h0 => by simpa [h0] using T'.w_norm`. Establish `hDS` using `isDS_sigLam hS hP hv₀`. Establish `hDS'` using `isDS_sigLam hS' hP' hv₀'`.

Use `hDS.2.1` as an intermediate fact. Use `hDS'.2.1` as an intermediate fact. Take `⟨w, hw⟩` from `exists_ne (0 : Hlam ε Ψ T.w)`. Take `⟨w', hw'⟩` from `exists_ne (0 : Hlam ε Ψ' T'.w)`. Establish `hcc` using `(cc_gk dual hS hP hv₀ hS' hP' hv₀' hgap hth hgap' hth' hpos hpos' hW hW' hG hG' s rfl hw hw').2`.

Take `⟨U, hU⟩` from `equiv_sigLam_of_isDS hσ hS hP hv₀`. Take `⟨U', hU'⟩` from `equiv_sigLam_of_isDS hσ' hS' hP' hv₀'`. Establish `hdL : Formalism.MainNotions.S.IsFdeg ν (sigLam ε Ψ T.w) d` using `swB_isFdeg_pull U hU hd`. Take `⟨d1, hd1⟩` from `Formalism.MainNotions.BridgeCSchur.fdeg_of_DS μ (sigLam ε Ψ T.w) hDS`. Take `⟨d2, hd2⟩` from `Formalism.MainNotions.BridgeCSchur.fdeg_of_DS (shiftF dual μ s) (sigLam ε Ψ' T'.w) hDS'`.

Rewrite `hcc` using `[fdegOf_of_isFdeg' hd1 hw, fdegOf_of_isFdeg' hd2 hw']`. Use `hν` as an intermediate fact. Take `⟨c, hc, hνeq⟩` from `swB_haar_eq ν`. Establish `hd1' : Formalism.MainNotions.S.IsFdeg ν (sigLam ε Ψ T.w) (d1 / c)` using `hνeq ▸ isFdeg_smul hc hd1`. Establish `hd2' : Formalism.MainNotions.S.IsFdeg ν (sigLam ε Ψ' T'.w) (d2 / c)` using `hνeq ▸ isFdeg_smul hc hd2`.

Establish `hdd : d = d1 / c` using `swB_isFdeg_unique hw hdL hd1'`. Establish `hd10 : d1 ≠ 0` using `hd1.1.ne'`. Establish `hval : d * ratioF dual μ s = d2 / c`. Rewrite using `[hdd, ← hcc]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[hval]`. Conclude with `swB_isFdeg_push U' hU' hd2'`.
-/
theorem swC_main (dual : Bool) {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) {μ : Fin n → ℝ}
    (hμ : S7.IsHCParam μ) {h : ℝ} (hgap : GapAtLeast ε μ h) (hh : thrStar ε + 1 < h) (s : Fin n)
    (hs : StrictAnti (shiftF dual μ s))
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : Formalism.MainNotions.S.IsDS ε μ σ)
    {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] {σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}
    (hσ' : Formalism.MainNotions.S.IsDS ε (shiftF dual μ s) σ')
    (ν : Measure (Formalism.REAL.UJ ε)) (hν : ν.IsHaarMeasure) {d : ℝ} (hd : Formalism.MainNotions.S.IsFdeg ν σ d) :
    Formalism.MainNotions.S.IsFdeg ν σ' (d * ratioF dual μ s) := by
  have := hσ.1
  have := hσ'.1
  have hq0 : 1 ≤ S7.q0 ε := le_min hp hq
  have hth : thrStar ε < h := by linarith
  have hth' : thrStar ε < h - 1 := by linarith
  have hlam' := swC_hc_shift hμ dual s hs
  have hgap' := swC_gap_shift hgap dual s
  obtain ⟨T⟩ := HW.kType_exists ε μ hμ
  obtain ⟨T'⟩ := HW.kType_exists ε (shiftF dual μ s) hlam'
  obtain ⟨Ψ, hS, hP, hpos, hW, hG⟩ := swA_model hμ hq0 hgap hth T
  obtain ⟨Ψ', hS', hP', hpos', hW', hG'⟩ := swA_model hlam' hq0 hgap' hth' T'
  have hv₀ : T.w ≠ 0 := fun h0 => by simpa [h0] using T.w_norm
  have hv₀' : T'.w ≠ 0 := fun h0 => by simpa [h0] using T'.w_norm
  have hDS := isDS_sigLam hS hP hv₀
  have hDS' := isDS_sigLam hS' hP' hv₀'
  have := hDS.2.1
  have := hDS'.2.1
  obtain ⟨w, hw⟩ := exists_ne (0 : Hlam ε Ψ T.w)
  obtain ⟨w', hw'⟩ := exists_ne (0 : Hlam ε Ψ' T'.w)
  have hcc := (cc_gk dual hS hP hv₀ hS' hP' hv₀' hgap hth hgap' hth' hpos hpos' hW hW' hG hG' s rfl hw hw').2
  obtain ⟨U, hU⟩ := equiv_sigLam_of_isDS hσ hS hP hv₀
  obtain ⟨U', hU'⟩ := equiv_sigLam_of_isDS hσ' hS' hP' hv₀'
  have hdL : Formalism.MainNotions.S.IsFdeg ν (sigLam ε Ψ T.w) d := swB_isFdeg_pull U hU hd
  obtain ⟨d1, hd1⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS μ (sigLam ε Ψ T.w) hDS
  obtain ⟨d2, hd2⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS (shiftF dual μ s) (sigLam ε Ψ' T'.w) hDS'
  rw [fdegOf_of_isFdeg' hd1 hw, fdegOf_of_isFdeg' hd2 hw'] at hcc
  have := hν
  obtain ⟨c, hc, hνeq⟩ := swB_haar_eq ν
  have hd1' : Formalism.MainNotions.S.IsFdeg ν (sigLam ε Ψ T.w) (d1 / c) := hνeq ▸ isFdeg_smul hc hd1
  have hd2' : Formalism.MainNotions.S.IsFdeg ν (sigLam ε Ψ' T'.w) (d2 / c) := hνeq ▸ isFdeg_smul hc hd2
  have hdd : d = d1 / c := swB_isFdeg_unique hw hdL hd1'
  have hd10 : d1 ≠ 0 := hd1.1.ne'
  have hval : d * ratioF dual μ s = d2 / c := by
    rw [hdd, ← hcc]
    field_simp
  rw [hval]
  exact swB_isFdeg_push U' hU' hd2'

end ReciprocityTheory.ChartRestriction.DS
