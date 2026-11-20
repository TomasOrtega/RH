import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.MeasureConditions.Cnd
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensEProd
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open UpperTheory.ConvolutionTheory.GM.TE

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} {v : Pl F}

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem cmp_val (w : PlacesOver E v) (g : GL (Fin n) (CompletionsOver E v)) (i j : Fin n) :
    (UpperTheory.ConvolutionTheory.GM.cmp w g).val i j = g.val i j w := rfl

/- English proof (translation)
Establish `hv : Continuous fun g : GL (Fin n) (CompletionsOver E v) => (UpperTheory.ConvolutionTheory.GM.cmp w g).val`. Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Simplify using `only [cmp_val]`. Conclude with `(continuous_apply w).comp (Units.continuous_val.matrix_elem i j)`. Use `Units.continuous_iff.mpr ⟨hv, ?_⟩` and prove the remaining obligations.

Establish `: (fun g : GL (Fin n) (CompletionsOver E v) => ((UpperTheory.ConvolutionTheory.GM.cmp w g)⁻¹ : GL (Fin n) (w.1.adicCompletion E)).val) = (fun g => (UpperTheory.ConvolutionTheory.GM.cmp w g).val) ∘ fun g => g⁻¹`. Use function extensionality and compare the values at `g`. Simplify using `[map_inv]`. Conclude with `this ▸ hv.comp continuous_inv`.
-/
private theorem cmp_continuous (w : PlacesOver E v) :
    Continuous (UpperTheory.ConvolutionTheory.GM.cmp (n := n) w) := by
  have hv : Continuous fun g : GL (Fin n) (CompletionsOver E v) => (UpperTheory.ConvolutionTheory.GM.cmp w g).val := by
    refine continuous_matrix fun i j => ?_
    simp only [cmp_val]
    exact (continuous_apply w).comp (Units.continuous_val.matrix_elem i j)
  refine Units.continuous_iff.mpr ⟨hv, ?_⟩
  have : (fun g : GL (Fin n) (CompletionsOver E v) => ((UpperTheory.ConvolutionTheory.GM.cmp w g)⁻¹ : GL (Fin n) (w.1.adicCompletion E)).val)
      = (fun g => (UpperTheory.ConvolutionTheory.GM.cmp w g).val) ∘ fun g => g⁻¹ := by
    funext g
    simp [map_inv]
  exact this ▸ hv.comp continuous_inv

/- English proof (translation)
Establish `hc : Continuous (locHeight : GL (Fin n) (w.adicCompletion E) → ℝ)`. Unfold `locHeight`. Use `continuous_const.max (NNReal.continuous_coe.comp (Continuous.finset_sup_apply (fun p _ => Continuous.max ?_ ?_)))` and prove the remaining obligations. Conclude with `(Units.continuous_val.matrix_elem _ _).nnnorm`. Conclude with `(Units.continuous_coe_inv.matrix_elem _ _).nnnorm`.

Take `⟨B, hB⟩` from `(hC.image hc).bddAbove`. Conclude with `⟨max 1 B, le_max_left _ _, fun g hg => (hB ⟨g, hg, rfl⟩).trans (le_max_right _ _)⟩`.
-/
private theorem loc_bd (w : Pl E) {C : Set (GL (Fin n) (w.adicCompletion E))} (hC : IsCompact C) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ g ∈ C, locHeight g ≤ B := by
  have hc : Continuous (locHeight : GL (Fin n) (w.adicCompletion E) → ℝ) := by
    unfold locHeight
    refine continuous_const.max (NNReal.continuous_coe.comp (Continuous.finset_sup_apply (fun p _ => Continuous.max ?_ ?_)))
    · exact (Units.continuous_val.matrix_elem _ _).nnnorm
    · exact (Units.continuous_coe_inv.matrix_elem _ _).nnnorm
  obtain ⟨B, hB⟩ := (hC.image hc).bddAbove
  exact ⟨max 1 B, le_max_left _ _, fun g hg => (hB ⟨g, hg, rfl⟩).trans (le_max_right _ _)⟩

/- English proof (translation)
Use `show (AdelicGLn.infiniteEquiv E n (AdelicGLn.prodEquiv E n (finEmb E n x)).1) w = 1`. Rewrite using `[AutomorphicForm.prodEquiv_finEmb, map_one]`. Both sides reduce to the same expression.
-/
private theorem infAt_finEmb' (w : InfinitePlace E) (x : AdelicGLn.FiniteAdelicGL E n) : infAt w (finEmb E n x) = 1 := by
  show (AdelicGLn.infiniteEquiv E n (AdelicGLn.prodEquiv E n (finEmb E n x)).1) w = 1
  rw [AutomorphicForm.prodEquiv_finEmb, map_one]
  rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨rfl⟩`.
-/
private theorem lies_under (w : Pl E) : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩

/- English proof (translation)
Use `ext1`. Conclude with `(hl.over).symm`.
-/
private theorem under_of_lies {w : Pl E} {v : Pl F} (hl : w.asIdeal.LiesOver v.asIdeal) : w.under (𝓞 F) = v := by
  ext1
  exact (hl.over).symm

end

/- English proof (translation)
Introduce `F E _ _ _ _ _ n S q κ ψ h hψ hh`. Establish `key : ∀ w : Pl E, ∃ M : ℝ, 1 ≤ M ∧ ∀ x : AdelicGLn.FiniteAdelicGL E n, (∀ v ∈ S, ψ v (mapGL n (atFin v) (finEmb E n x)) ≠ 0) → (∀ w ∈ κ, h w (cf w x) ≠ 0) → (w ∈ κ ∨ w.under (𝓞 F) ∈ S) → locHeight (cf w x) ≤ M`. Introduce `w`. Distinguish the cases in `hk : w ∈ κ`. Take `⟨B, hB1, hB⟩` from `loc_bd w (hh w hk).isCompact`.

Conclude with `⟨B, hB1, fun x _ h2 _ => hB _ (subset_tsupport _ (Function.mem_support.2 (h2 w hk)))⟩`. Distinguish the cases in `hs : w.under (𝓞 F) ∈ S`. Establish `hc` using `(hψ _ hs).isCompact.image (cmp_continuous (n := n) (⟨w, lies_under w⟩ : PlacesOver E (w.under (𝓞 F))))`. Take `⟨B, hB1, hB⟩` from `loc_bd w hc`. Use `⟨B, hB1, fun x h1 _ _ => ?_⟩` and prove the remaining obligations.

Establish `e : UpperTheory.ConvolutionTheory.GM.cmp (⟨w, lies_under w⟩ : PlacesOver E (w.under (𝓞 F))) (mapGL n (atFin (w.under (𝓞 F))) (finEmb E n x)) = cf w x`. Use extensionality with `i j`. Both sides reduce to the same expression. Rewrite using `[← e]`. Conclude with `hB _ ⟨_, subset_tsupport _ (Function.mem_support.2 (h1 _ hs)), rfl⟩`.

Conclude with `⟨1, le_rfl, fun x _ _ hd => absurd hd (by simp [hk, hs])⟩`. Use `choose M hM1 hM using key`. Set `W : Finset (Pl E)` to `κ ∪ S.biUnion fun v => (Finset.univ : Finset (PlacesOver E v)).image Subtype.val`. Establish `hW : ∀ w, w ∈ W ↔ (w ∈ κ ∨ w.under (𝓞 F) ∈ S)`. Introduce `w`.

Simplify using `only [W, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]`. Use `or_congr Iff.rfl ⟨?_, fun hs => ⟨_, hs, ⟨w, lies_under w⟩, rfl⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨v, hv, p, rfl⟩`. Rewrite using `[under_of_lies p.2]` and apply the resulting hypothesis. Use `⟨∏ w ∈ W, M w, Finset.prod_induction _ (fun y : ℝ => 1 ≤ y) (fun _ _ hx hy => one_le_mul_of_one_le_of_one_le hx hy) le_rfl fun w _ => hM1 w, ?_⟩` and prove the remaining obligations.

Introduce `x h1 h2 hx`. Unfold `heightOff`. Establish `hi : (∏ w : InfinitePlace E, locHeight (infAt w (finEmb E n x)) ^ w.mult) = 1` using `Finset.prod_eq_one fun w _ => by rw [infAt_finEmb', locHeight_one, one_pow]`. Rewrite using `[hi, one_mul]`. Establish `hg : ∀ w : Pl E, (∏ᶠ (_ : AdeleBaseChange.below F w ≠ q), locHeight (finAt w (finEmb E n x))) = if w.under (𝓞 F) ≠ q then locHeight (cf w x) else 1`.

Introduce `w`. Rewrite using `[finprod_eq_if]`. Both sides reduce to the same expression. Simplify using `only [hg]`. Rewrite using `[finprod_eq_prod_of_mulSupport_subset (s := W)]`.

Use `Finset.prod_le_prod (fun w _ => ?_) fun w hw => ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `(locHeight_pos _).le`. Conclude with `zero_le_one`. Use `split_ifs with hq`.

Conclude with `hM w x h1 h2 ((hW w).1 hw)`. Conclude with `hM1 w`. Introduce `w hw`. Assume the negation of the conclusion as `hc`. Apply `hw` to reduce the goal to its premises.

Establish `hc' : w ∉ W` using `hc`. Rewrite `hc'` using `[hW, not_or]`. Distinguish the cases in `hq : w.under (𝓞 F) = q`. Simplify using `[hq]`. Simplify using `only [ne_eq, hq, not_false_eq_true, if_true]`.

Conclude with `locHeight_eq_one_of_mem_integralGL (hx w hc'.1 hc'.2 hq)`.
-/
theorem UpperTheory.height_bounded_on_support_of_compact_test_functions :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (S : Finset (Pl F)) (q : Pl F) (κ : Finset (Pl E))
        (ψ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ) (h : ∀ w : Pl E, GL (Fin n) (w.adicCompletion E) → ℂ),
        (∀ v ∈ S, HasCompactSupport (ψ v)) → (∀ w ∈ κ, HasCompactSupport (h w)) →
        ∃ Yf : ℝ, 1 ≤ Yf ∧ ∀ x : AdelicGLn.FiniteAdelicGL E n, (∀ v ∈ S, ψ v (mapGL n (atFin v) (finEmb E n x)) ≠ 0) →
          (∀ w ∈ κ, h w (cf w x) ≠ 0) → x ∈ Cnd S q κ → heightOff q (finEmb E n x) ≤ Yf := by
  classical
  intro F E _ _ _ _ _ n S q κ ψ h hψ hh
  have key : ∀ w : Pl E, ∃ M : ℝ, 1 ≤ M ∧ ∀ x : AdelicGLn.FiniteAdelicGL E n,
      (∀ v ∈ S, ψ v (mapGL n (atFin v) (finEmb E n x)) ≠ 0) → (∀ w ∈ κ, h w (cf w x) ≠ 0) →
      (w ∈ κ ∨ w.under (𝓞 F) ∈ S) → locHeight (cf w x) ≤ M := by
    intro w
    by_cases hk : w ∈ κ
    · obtain ⟨B, hB1, hB⟩ := loc_bd w (hh w hk).isCompact
      exact ⟨B, hB1, fun x _ h2 _ => hB _ (subset_tsupport _ (Function.mem_support.2 (h2 w hk)))⟩
    · by_cases hs : w.under (𝓞 F) ∈ S
      · have hc := (hψ _ hs).isCompact.image (cmp_continuous (n := n) (⟨w, lies_under w⟩ : PlacesOver E (w.under (𝓞 F))))
        obtain ⟨B, hB1, hB⟩ := loc_bd w hc
        refine ⟨B, hB1, fun x h1 _ _ => ?_⟩
        have e : UpperTheory.ConvolutionTheory.GM.cmp (⟨w, lies_under w⟩ : PlacesOver E (w.under (𝓞 F)))
            (mapGL n (atFin (w.under (𝓞 F))) (finEmb E n x)) = cf w x := by
          ext i j
          rfl
        rw [← e]
        exact hB _ ⟨_, subset_tsupport _ (Function.mem_support.2 (h1 _ hs)), rfl⟩
      · exact ⟨1, le_rfl, fun x _ _ hd => absurd hd (by simp [hk, hs])⟩
  choose M hM1 hM using key
  let W : Finset (Pl E) := κ ∪ S.biUnion fun v => (Finset.univ : Finset (PlacesOver E v)).image Subtype.val
  have hW : ∀ w, w ∈ W ↔ (w ∈ κ ∨ w.under (𝓞 F) ∈ S) := by
    intro w
    simp only [W, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]
    refine or_congr Iff.rfl ⟨?_, fun hs => ⟨_, hs, ⟨w, lies_under w⟩, rfl⟩⟩
    rintro ⟨v, hv, p, rfl⟩
    rwa [under_of_lies p.2]
  refine ⟨∏ w ∈ W, M w, Finset.prod_induction _ (fun y : ℝ => 1 ≤ y)
    (fun _ _ hx hy => one_le_mul_of_one_le_of_one_le hx hy) le_rfl fun w _ => hM1 w, ?_⟩
  intro x h1 h2 hx
  unfold heightOff
  have hi : (∏ w : InfinitePlace E, locHeight (infAt w (finEmb E n x)) ^ w.mult) = 1 :=
    Finset.prod_eq_one fun w _ => by rw [infAt_finEmb', locHeight_one, one_pow]
  rw [hi, one_mul]
  have hg : ∀ w : Pl E, (∏ᶠ (_ : AdeleBaseChange.below F w ≠ q), locHeight (finAt w (finEmb E n x))) =
      if w.under (𝓞 F) ≠ q then locHeight (cf w x) else 1 := by
    intro w
    rw [finprod_eq_if]
    rfl
  simp only [hg]
  rw [finprod_eq_prod_of_mulSupport_subset (s := W)]
  · refine Finset.prod_le_prod (fun w _ => ?_) fun w hw => ?_
    · split_ifs
      · exact (locHeight_pos _).le
      · exact zero_le_one
    · split_ifs with hq
      · exact hM w x h1 h2 ((hW w).1 hw)
      · exact hM1 w
  · intro w hw
    by_contra hc
    apply hw
    have hc' : w ∉ W := hc
    rw [hW, not_or] at hc'
    by_cases hq : w.under (𝓞 F) = q
    · simp [hq]
    · simp only [ne_eq, hq, not_false_eq_true, if_true]
      exact locHeight_eq_one_of_mem_integralGL (hx w hc'.1 hc'.2 hq)
