import Formalism.SharpRestriction.GlobalSchurBounds.Joints

noncomputable section

namespace Formalism.MainNotions.GlobalTheoryTheory

open Formalism.BasicNotions Formalism.MainNotions

/- English proof (translation)
The claim follows from `lt_of_lt_of_le one_lt_two (le_max_left _ _)`.
-/
theorem jntF_one_lt (a : ℝ) : (1 : ℝ) < max 2 (a + 1) :=
  lt_of_lt_of_le one_lt_two (le_max_left _ _)

/- English proof (translation)
Establish `h'` using `le_trans (le_max_right 2 (a + 1)) h`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem jntF_lt {a x : ℝ} (h : max 2 (a + 1) ≤ x) : a < x := by
  have h' := le_trans (le_max_right 2 (a + 1)) h
  linarith

def Gram0Def (D : D7) : Prop :=
  letI := D.host.cmStar
  UnusedSlot33.IsDef D.sp.cm.sig D.sp.gram0

/- English proof (translation)
Introduce `ε h0 h1 _`. Use `⟨max 2 ((Fm ε h0 h1).x1 + 1), Formalism.MainNotions.GlobalTheoryTheory.jntF_one_lt _, ?_⟩` and prove the remaining obligations. Introduce `x hx i`. Conclude with `ZetaZeroFreeRegion.first_hypothesis_of_lifting _ (h ε h0 h1 x (Formalism.MainNotions.GlobalTheoryTheory.jntF_lt hx) i).1`.
-/
theorem _root_.Formalism.MainNotions.ZetaZeroFreeRegion.column_lemma_one_family (Fm : DFamP) (ε0 C₄ C₅ : ℝ)
    (h : ∀ ε h0 h1, UnusedSlot33.ConclusionOnFamily (Fm ε h0 h1) C₄ C₅) : ZetaZeroFreeRegion.FamilyLemmaOneOne Fm ε0 := by
  intro ε h0 h1 _
  refine ⟨max 2 ((Fm ε h0 h1).x1 + 1), Formalism.MainNotions.GlobalTheoryTheory.jntF_one_lt _, ?_⟩
  intro x hx i
  exact ZetaZeroFreeRegion.first_hypothesis_of_lifting _ (h ε h0 h1 x (Formalism.MainNotions.GlobalTheoryTheory.jntF_lt hx) i).1

/- English proof (translation)
Introduce `ε h0 h1 _`. Use `⟨max 2 ((Fm ε h0 h1).x1 + 1), Formalism.MainNotions.GlobalTheoryTheory.jntF_one_lt _, ?_⟩` and prove the remaining obligations. Introduce `x hx i`. Conclude with `ZetaZeroFreeRegion.second_hypothesis_of_lifting _ (h ε h0 h1 x (Formalism.MainNotions.GlobalTheoryTheory.jntF_lt hx) i).2.1`.
-/
theorem _root_.Formalism.MainNotions.ZetaZeroFreeRegion.column_lemma_two_family (Fm : DFamP) (ε0 C₄ C₅ : ℝ)
    (h : ∀ ε h0 h1, UnusedSlot33.ConclusionOnFamily (Fm ε h0 h1) C₄ C₅) : ZetaZeroFreeRegion.FamilyLemmaOneTwo Fm ε0 := by
  intro ε h0 h1 _
  refine ⟨max 2 ((Fm ε h0 h1).x1 + 1), Formalism.MainNotions.GlobalTheoryTheory.jntF_one_lt _, ?_⟩
  intro x hx i
  exact ZetaZeroFreeRegion.second_hypothesis_of_lifting _ (h ε h0 h1 x (Formalism.MainNotions.GlobalTheoryTheory.jntF_lt hx) i).2.1

/- English proof (translation)
Introduce `ε h0 h1 _`. Conclude with `⟨2, one_lt_two, fun x _ i => ZetaZeroFreeRegion.subgroup_admissible_holds _⟩`.
-/
theorem _root_.Formalism.MainNotions.ZetaZeroFreeRegion.facts_after_lemma_family_holds (Fm : DFamP) (ε0 : ℝ) : ZetaZeroFreeRegion.FamilyFactsAfterLemmaOneTwo Fm ε0 := by
  intro ε h0 h1 _
  exact ⟨2, one_lt_two, fun x _ i => ZetaZeroFreeRegion.subgroup_admissible_holds _⟩

/- English proof (translation)
Introduce `ε h0 h1 _`. Take `⟨C, hC, hp⟩` from `h ε h0 h1`. Use `⟨C, 2, hC, one_lt_two, ?_⟩` and prove the remaining obligations. Introduce `x hx i`. Conclude with `ZetaZeroFreeRegion.fourth_hypothesis_of_lifting _ _ _ (hp x (by linarith) i)`.
-/
theorem _root_.Formalism.MainNotions.ZetaZeroFreeRegion.chebyshev_family_of_lemma (Fm : DFamP) (ε0 : ℝ)
    (h : ∀ ε h0 h1, ShortIntervalPrimes.Conclusion1Family (Fm ε h0 h1)) : ZetaZeroFreeRegion.FamilyLemmaTwoOne Fm ε0 := by
  intro ε h0 h1 _
  obtain ⟨C, hC, hp⟩ := h ε h0 h1
  refine ⟨C, 2, hC, one_lt_two, ?_⟩
  intro x hx i
  exact ZetaZeroFreeRegion.fourth_hypothesis_of_lifting _ _ _ (hp x (by linarith) i)

/- English proof (translation)
Introduce `ε h0 h1 _`. Take `⟨C5, -, xa, hxa, ha⟩` from `h5 ε h0 h1`. Take `⟨c, hc, xb, -, hb⟩` from `h6 ε h0 h1`. Use `⟨c, max (max xa xb) ((Fm ε h0 h1).x1 + 1), hc, lt_of_lt_of_le hxa (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩` and prove the remaining obligations. Introduce `x hx i`.

Establish `hxa' : xa ≤ x` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx`. Establish `hxb' : xb ≤ x` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx`. Establish `hx1 : (Fm ε h0 h1).x1 < x`. Use `le_trans (le_max_right _ _) hx` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `ex : ((Fm ε h0 h1).L x i).sc.x = x` using `(Fm ε h0 h1).L_x x i hx1`. Establish `ee : ((Fm ε h0 h1).L x i).sc.eps = ε` using `(Fm ε h0 h1).L_eps x i`. Apply `ZetaZeroFreeRegion.sizes_bound_of_log_estimates _ _ c C5` to reduce the goal to its premises. Rewrite using `[ex, ee]`. Conclude with `ha x hxa' i`.

Rewrite using `[ex, ee]`. Conclude with `hb x hxb' i`.
-/
theorem _root_.Formalism.MainNotions.ZetaZeroFreeRegion.proposition_six_family_of_bounds (Fm : DFamP) (ε0 : ℝ)
    (h5 : ∀ ε h0 h1, ShortIntervalPrimes.FamilyPrimesAsPropTwoFive (Fm ε h0 h1)) (h6 : ∀ ε h0 h1, ShortIntervalPrimes.Conclusion6Family (Fm ε h0 h1)) :
    ZetaZeroFreeRegion.FamilyPropTwoSix Fm ε0 := by
  intro ε h0 h1 _
  obtain ⟨C5, -, xa, hxa, ha⟩ := h5 ε h0 h1
  obtain ⟨c, hc, xb, -, hb⟩ := h6 ε h0 h1
  refine ⟨c, max (max xa xb) ((Fm ε h0 h1).x1 + 1), hc,
    lt_of_lt_of_le hxa (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro x hx i
  have hxa' : xa ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxb' : xb ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx1 : (Fm ε h0 h1).x1 < x := by
    have := le_trans (le_max_right _ _) hx
    linarith
  have ex : ((Fm ε h0 h1).L x i).sc.x = x := (Fm ε h0 h1).L_x x i hx1
  have ee : ((Fm ε h0 h1).L x i).sc.eps = ε := (Fm ε h0 h1).L_eps x i
  apply ZetaZeroFreeRegion.sizes_bound_of_log_estimates _ _ c C5
  · rw [ex, ee]
    exact ha x hxa' i
  · rw [ex, ee]
    exact hb x hxb' i

/- English proof (translation)
Introduce `ε h0 h1 _`. Take `⟨C, hC, xa, hxa, ha⟩` from `h5 ε h0 h1`. Use `⟨C, max xa ((Fm ε h0 h1).x1 + 1), hC, lt_of_lt_of_le hxa (le_max_left _ _), ?_⟩` and prove the remaining obligations. Introduce `x hx i`. Establish `hxa' : xa ≤ x` using `le_trans (le_max_left _ _) hx`.

Establish `hx1 : (Fm ε h0 h1).x1 < x`. Use `le_trans (le_max_right _ _) hx` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Apply `ZetaZeroFreeRegion.restriction_dimension_of_division` to reduce the goal to its premises. Rewrite using `[(Fm ε h0 h1).L_x x i hx1, (Fm ε h0 h1).L_eps x i]`.

Conclude with `ha x hxa' i`.
-/
theorem _root_.Formalism.MainNotions.ZetaZeroFreeRegion.character_bounds_family_of_proposition (Fm : DFamP) (ε0 : ℝ)
    (h5 : ∀ ε h0 h1, ShortIntervalPrimes.FamilyPrimesAsPropTwoFive (Fm ε h0 h1)) : ZetaZeroFreeRegion.FamilyCharacterSumBounds Fm ε0 := by
  intro ε h0 h1 _
  obtain ⟨C, hC, xa, hxa, ha⟩ := h5 ε h0 h1
  refine ⟨C, max xa ((Fm ε h0 h1).x1 + 1), hC, lt_of_lt_of_le hxa (le_max_left _ _), ?_⟩
  intro x hx i
  have hxa' : xa ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : (Fm ε h0 h1).x1 < x := by
    have := le_trans (le_max_right _ _) hx
    linarith
  apply ZetaZeroFreeRegion.restriction_dimension_of_division
  rw [(Fm ε h0 h1).L_x x i hx1, (Fm ε h0 h1).L_eps x i]
  exact ha x hxa' i

/- English proof (translation)
Introduce `ε h0 h1 _`. Conclude with `⟨2, one_lt_two, fun x _ i => ZetaZeroFreeRegion.primitive_reading_holds _⟩`.
-/
theorem _root_.Formalism.MainNotions.ZetaZeroFreeRegion.primitive_reading_family_holds (Fm : DFamP) (ε0 : ℝ) : ZetaZeroFreeRegion.FamilyCharacterReading Fm ε0 := by
  intro ε h0 h1 _
  exact ⟨2, one_lt_two, fun x _ i => ZetaZeroFreeRegion.primitive_reading_holds _⟩

/- English proof (translation)
Introduce `ε h0 h1 _`. Conclude with `⟨2, one_lt_two, fun x _ i => ZetaZeroFreeRegion.zero_window_bound_holds _⟩`.
-/
theorem _root_.Formalism.MainNotions.ZetaZeroFreeRegion.ramified_values_family_holds (Fm : DFamP) (ε0 : ℝ) : ZetaZeroFreeRegion.FamilyRamifiedPrimeValues Fm ε0 := by
  intro ε h0 h1 _
  exact ⟨2, one_lt_two, fun x _ i => ZetaZeroFreeRegion.zero_window_bound_holds _⟩

/- English proof (translation)
Introduce `x hx i`. Conclude with `StandardLattice.column_lemma_of_definite_form _ _ (h x hx i).2.2.2.2.2.2.2.1 (hD x i)`.
-/
theorem _root_.Formalism.MainNotions.StandardLattice.column_lemma_family_of_definite {eps : ℝ} (Fm : FamP eps) (C₄ C₅ : ℝ) (h : UnusedSlot33.ConclusionOnFamily Fm C₄ C₅)
    (hD : ∀ x (i : Fm.Ix x), Gram0Def (Fm.D x i)) : StandardLattice.FamilyLevelConditionAdmitted Fm := by
  intro x hx i
  exact StandardLattice.column_lemma_of_definite_form _ _ (h x hx i).2.2.2.2.2.2.2.1 (hD x i)

/- English proof (translation)
Introduce `x i`. Conclude with `StandardLattice.baseChange_preserves_unitary_of _ h hb2`.
-/
theorem _root_.Formalism.MainNotions.StandardLattice.shintani_weight_family_of_b2 {eps : ℝ} (Fm : FamP eps) (h : UnusedSlot34.Conclusion₂)
    (hb2 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (σ : E →ₐ[F] E), GenusMassVolumes.IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E),
      GenusMassVolumes.IsHermND σ J → StandardLattice.SW1b2 F E σ M J) : StandardLattice.FamilyPartOne Fm := by
  intro x i
  exact StandardLattice.baseChange_preserves_unitary_of _ h hb2

/- English proof (translation)
Introduce `Cn`. Use `⟨Cn + 4, 0, ?_⟩` and prove the remaining obligations. Introduce `x _ _ i`. Take `⟨δ, hδ, hl'⟩` from `hl x i`. Establish `hcc : TaylorLogMetric.IsCurveIdeal (Fm.D x i) (Fm.D x i).host.ccK`.

Use `⟨(Fm.D x i).host.ccK_ne_bot, Nat.Coprime.mul_right ?_ ?_⟩` and prove the remaining obligations. Conclude with `(Fm.D x i).host.ccK_coprime 2 (by simp)`. Conclude with `(Fm.D x i).host.ccK_coprime _ (by simp)`. Conclude with `flipTwoThree.first_hypothesis_of_lifting _ Cn x _ ((h x i) _ hcc δ hδ).1 hl'`.
-/
theorem _root_.Formalism.MainNotions.flipTwoThree.theta_norm_family_of_linked {eps : ℝ} (Fm : FamP eps) (C : ℝ) (h : TaylorLogMetric.ConclusionOnFamily Fm C)
    (hl : ∀ x (i : Fm.Ix x), ∃ δ : ℂ, TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice (Fm.D x i) (Fm.D x i).host.ccK δ ∧
      OmLink (Fm.D x i) (TaylorLogMetric.tor0 (Fm.D x i) (Fm.D x i).host.ccK δ)) : flipTwoThree.admF1 Fm := by
  intro Cn
  refine ⟨Cn + 4, 0, ?_⟩
  intro x _ _ i
  obtain ⟨δ, hδ, hl'⟩ := hl x i
  have hcc : TaylorLogMetric.IsCurveIdeal (Fm.D x i) (Fm.D x i).host.ccK := by
    refine ⟨(Fm.D x i).host.ccK_ne_bot, Nat.Coprime.mul_right ?_ ?_⟩
    · exact (Fm.D x i).host.ccK_coprime 2 (by simp)
    · exact (Fm.D x i).host.ccK_coprime _ (by simp)
  exact flipTwoThree.first_hypothesis_of_lifting _ Cn x _ ((h x i) _ hcc δ hδ).1 hl'

/- English proof (translation)
Introduce `Cn`. Use `⟨C * (1 + Cn), 0, ?_⟩` and prove the remaining obligations. Introduce `x _ _ i`. Take `⟨δ, -, χ, -, e, hcl, hl⟩` from `hT x i`. Take `⟨-, hth, -⟩` from `hcl`.

Conclude with `flipTwoThree.second_hypothesis_of_lifting _ Cn C x _ e hth (hfree x i) hl`.
-/
theorem _root_.Formalism.MainNotions.flipTwoThree.theta_condition_family_of_linked {eps : ℝ} (Fm : FamP eps) (C : ℝ)
    (hfree : ∀ x (i : Fm.Ix x), ThFree (Fm.D x i))
    (hT : ∀ x (i : Fm.Ix x), ExistsTwelfthRootCharacterThetaFamily (Fm.D x i) C) : flipTwoThree.admF2 Fm := by
  intro Cn
  refine ⟨C * (1 + Cn), 0, ?_⟩
  intro x _ _ i
  obtain ⟨δ, -, χ, -, e, hcl, hl⟩ := hT x i
  obtain ⟨-, hth, -⟩ := hcl
  exact flipTwoThree.second_hypothesis_of_lifting _ Cn C x _ e hth (hfree x i) hl

/- English proof (translation)
Take `⟨x0, hg⟩` from `hg`. Conclude with `⟨x0, fun x hx hx1 i => flipTwoThree.stabiliser_condition_of_level _ (Fm.ex x hx1 i).lev (h x hx1 i).2.2.2.2.2.2.2.1 (hD x i) (hP x hx1 i) (hg x hx hx1 i)⟩`.
-/
theorem _root_.Formalism.MainNotions.flipTwoThree.stabiliser_family_of_definite {eps : ℝ} (Fm : FamP eps) (C₄ C₅ : ℝ) (h : UnusedSlot33.ConclusionOnFamily Fm C₄ C₅)
    (hD : ∀ x (i : Fm.Ix x), Gram0Def (Fm.D x i))
    (hP : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), StandardLattice.Conclusion4p (Fm.D x i) (Fm.ex x hx i).lev)
    (hg : ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, StandardLattice.GBig (Fm.D x i)) :
    flipTwoThree.admF3 Fm := by
  obtain ⟨x0, hg⟩ := hg
  exact ⟨x0, fun x hx hx1 i => flipTwoThree.stabiliser_condition_of_level _ (Fm.ex x hx1 i).lev
    (h x hx1 i).2.2.2.2.2.2.2.1 (hD x i) (hP x hx1 i) (hg x hx hx1 i)⟩

def SettingEventually {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word),
    product_first_zeroth_parts.HidaSetting (Fm.D x i) u

/- English proof (translation)
Take `⟨xa, ha⟩` from `h`. Take `⟨xb, hb⟩` from `hS`. Use `⟨max xa xb, ?_⟩` and prove the remaining obligations. Introduce `x hx hx1 i`. Conclude with `flipTwoThree.fourth_hypothesis_of_lifting _ (fun u => (ha x (le_trans (le_max_left _ _) hx) i u (hb x (le_trans (le_max_right _ _) hx) hx1 i u)).2.2.2.2.2.1)`.
-/
theorem _root_.Formalism.MainNotions.flipTwoThree.injectivity_family_of_theorem {eps : ℝ} (Fm : FamP eps) (C : ℝ) (h : product_first_zeroth_parts.ConclusionOnFamily Fm C)
    (hS : SettingEventually Fm) : flipTwoThree.admF4 Fm := by
  obtain ⟨xa, ha⟩ := h
  obtain ⟨xb, hb⟩ := hS
  refine ⟨max xa xb, ?_⟩
  intro x hx hx1 i
  exact flipTwoThree.fourth_hypothesis_of_lifting _ (fun u => (ha x (le_trans (le_max_left _ _) hx) i u
    (hb x (le_trans (le_max_right _ _) hx) hx1 i u)).2.2.2.2.2.1)

/- English proof (translation)
Take `⟨xa, ha⟩` from `h`. Take `⟨xb, hb⟩` from `hS`. Use `⟨max xa xb, ?_⟩` and prove the remaining obligations. Introduce `x hx hx1 i`. Conclude with `flipTwoThree.restriction_dimension_of_division _ (fun u => (ha x (le_trans (le_max_left _ _) hx) i u (hb x (le_trans (le_max_right _ _) hx) hx1 i u)).2.2.2.2.2.1)`.
-/
theorem _root_.Formalism.MainNotions.flipTwoThree.norm_bound_family_of_theorem {eps : ℝ} (Fm : FamP eps) (C : ℝ) (h : product_first_zeroth_parts.ConclusionOnFamily Fm C)
    (hS : SettingEventually Fm) : flipTwoThree.admF6 Fm := by
  obtain ⟨xa, ha⟩ := h
  obtain ⟨xb, hb⟩ := hS
  refine ⟨max xa xb, ?_⟩
  intro x hx hx1 i
  exact flipTwoThree.restriction_dimension_of_division _ (fun u => (ha x (le_trans (le_max_left _ _) hx) i u
    (hb x (le_trans (le_max_right _ _) hx) hx1 i u)).2.2.2.2.2.1)

/- English proof (translation)
Introduce `x i`. Conclude with `TaylorLogMetric.first_hypothesis_of_lifting _ (h x i)`.
-/
theorem _root_.Formalism.MainNotions.TaylorLogMetric.AdmF_of {eps : ℝ} (Fm : FamP eps)
    (h : ∀ x (i : Fm.Ix x), UnusedSlot33.Conclusion1 (Fm.D x i)) : TaylorLogMetric.AdmF Fm := by
  intro x i
  exact TaylorLogMetric.first_hypothesis_of_lifting _ (h x i)

/- English proof (translation)
Take `⟨C, xa, ha⟩` from `h C0`. Take `⟨xb, hb⟩` from `hB`. Take `⟨xc, hc⟩` from `hm |C|`. Use `⟨max (max xa xb) (max xc (Fm.x1 + 1)), ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `Fm.one_lt_family_threshold`.

Establish `h2 : Fm.x1 + 1 ≤ max (max xa xb) (max xc (Fm.x1 + 1))` using `le_trans (le_max_right _ _) (le_max_right _ _)`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `x hx i`. Establish `hxa : xa ≤ x` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx`. Establish `hxb : xb ≤ x` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx`.

Establish `hxc : xc ≤ x` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx`. Establish `hx1 : Fm.x1 < x`. Use `le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨Δ, w, hdb⟩` from `hb x hxb hx1 i`.

Establish `hmm` using `hc x hxc hx1 i`. Establish `hL : (1 : ℝ) ≤ (Fm.L x i).sc.L` using `Real.one_le_rpow (le_of_lt (Fm.L x i).sc.one_lt_alt) (le_of_lt (Fm.L x i).sc.eps_pos)`. Establish `hC : C * ((Fm.L x i).sc.L + 1) ≤ 31 / 2 * ((Fm.D x i).R.m : ℝ) * (Fm.L x i).sc.L`. Establish `h1` using `mul_nonneg (sub_nonneg.2 (le_abs_self C)) (by linarith : (0 : ℝ) ≤ (Fm.L x i).sc.L + 1)`. Establish `h2` using `mul_nonneg (abs_nonneg C) (by linarith : (0 : ℝ) ≤ (Fm.L x i).sc.L - 1)`.

Establish `h3` using `mul_nonneg (abs_nonneg C) (by linarith : (0 : ℝ) ≤ (Fm.L x i).sc.L)`. Establish `h4` using `mul_nonneg (sub_nonneg.2 hmm) (by linarith : (0 : ℝ) ≤ (Fm.L x i).sc.L)`. Use polynomial arithmetic with `[h1, h2, h3, h4]`. Establish `key` using `ShortIntervalPrimes.crystalline_lift_of_theorem_c (Fm.D x i) (Fm.L x i).sc C0 C (ha x hxa hx1 i).1 Δ w hdb (Fm.ex x hx1 i).duStar_def (Fm.ex x hx1 i).Dstar_def hC`. Rewrite `key` using `[Fm.L_x x i hx1, Fm.L_eps x i]`.

Conclude with `key`.
-/
theorem _root_.Formalism.MainNotions.ShortIntervalPrimes.log_height_family_of_data {eps : ℝ} (Fm : FamP eps) (C0 : ℝ) (h : StandardLattice.PartFiveFamilyBounds Fm)
    (hB : ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x,
      ∃ (Δ : ℝ) (w : ℕ → (Fm.D x i).what₂.Tau → ℝ), StandardLattice.DataB (Fm.D x i) (Fm.L x i).sc C0 Δ w)
    (hm : ∀ K : ℝ, ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, K ≤ ((Fm.D x i).R.m : ℝ)) :
    ShortIntervalPrimes.proportionalityInputFamily Fm := by
  obtain ⟨C, xa, ha⟩ := h C0
  obtain ⟨xb, hb⟩ := hB
  obtain ⟨xc, hc⟩ := hm |C|
  refine ⟨max (max xa xb) (max xc (Fm.x1 + 1)), ?_, ?_⟩
  · have h1 := Fm.one_lt_family_threshold
    have h2 : Fm.x1 + 1 ≤ max (max xa xb) (max xc (Fm.x1 + 1)) :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    linarith
  intro x hx i
  have hxa : xa ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxb : xb ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxc : xc ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx1 : Fm.x1 < x := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
    linarith
  obtain ⟨Δ, w, hdb⟩ := hb x hxb hx1 i
  have hmm := hc x hxc hx1 i
  have hL : (1 : ℝ) ≤ (Fm.L x i).sc.L :=
    Real.one_le_rpow (le_of_lt (Fm.L x i).sc.one_lt_alt) (le_of_lt (Fm.L x i).sc.eps_pos)
  have hC : C * ((Fm.L x i).sc.L + 1) ≤ 31 / 2 * ((Fm.D x i).R.m : ℝ) * (Fm.L x i).sc.L := by
    have h1 := mul_nonneg (sub_nonneg.2 (le_abs_self C)) (by linarith : (0 : ℝ) ≤ (Fm.L x i).sc.L + 1)
    have h2 := mul_nonneg (abs_nonneg C) (by linarith : (0 : ℝ) ≤ (Fm.L x i).sc.L - 1)
    have h3 := mul_nonneg (abs_nonneg C) (by linarith : (0 : ℝ) ≤ (Fm.L x i).sc.L)
    have h4 := mul_nonneg (sub_nonneg.2 hmm) (by linarith : (0 : ℝ) ≤ (Fm.L x i).sc.L)
    nlinarith [h1, h2, h3, h4]
  have key := ShortIntervalPrimes.crystalline_lift_of_theorem_c (Fm.D x i) (Fm.L x i).sc C0 C (ha x hxa hx1 i).1 Δ w hdb
    (Fm.ex x hx1 i).duStar_def (Fm.ex x hx1 i).Dstar_def hC
  rw [Fm.L_x x i hx1, Fm.L_eps x i] at key
  exact key

end Formalism.MainNotions.GlobalTheoryTheory

end
