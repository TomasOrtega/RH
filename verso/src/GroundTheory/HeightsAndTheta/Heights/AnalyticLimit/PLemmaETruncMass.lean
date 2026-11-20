import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETruncMass
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.IntegrableOfTendstoOfIntegralLe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh locDens mInt MIntegrable integralWith)

noncomputable section

/- English proof (translation)
Distinguish the cases in `hx : x ∈ Yo`. Take `⟨N, hN⟩` from `exists_nat_gt (r x - R₀) filter_upwards [eventually_ge_atTop N] with n hn`. Establish `hn' : (N : ℝ) ≤ n` using `Nat.cast_le.2 hn`. Establish `hlt : r x < R₀ + n` using `by linarith`. Distinguish the cases in `h : R₀ ≤ r x`.

Rewrite using `[Set.indicator_of_mem, Set.indicator_of_mem]`. Conclude with `show x ∈ Yo ∧ R₀ ≤ r x from ⟨hx, h⟩`. Rewrite using `[Set.mem_sdiff, hO, hO]`. Conclude with `⟨⟨hx, hlt⟩, fun h' => absurd h'.2 (not_lt.2 h)⟩`. Rewrite using `[Set.indicator_of_notMem, Set.indicator_of_notMem]`.

Conclude with `fun h' => h (show x ∈ Yo ∧ R₀ ≤ r x from h').2`. Rewrite using `[Set.mem_sdiff, hO, hO]`. Conclude with `fun h' => h'.2 ⟨hx, lt_of_not_ge h⟩`. Use `Eventually.of_forall fun n => ?_` and prove the remaining obligations. Rewrite using `[Set.indicator_of_notMem, Set.indicator_of_notMem]`.

Conclude with `fun h' => hx (show x ∈ Yo ∧ R₀ ≤ r x from h').1`. Rewrite using `[Set.mem_sdiff, hO]`. Conclude with `fun h' => hx h'.1.1`.
-/
theorem indicator_band_eventually {X : Type} (Yo : Set X) (r : X → ℝ) (R₀ : ℝ) (O : ℝ → Set X)
    (hO : ∀ R x, x ∈ O R ↔ x ∈ Yo ∧ r x < R) (x : X) :
    ∀ᶠ n : ℕ in atTop, (O (R₀ + n) \ O R₀).indicator (1 : X → ℝ) x = (tail Yo r R₀).indicator 1 x := by
  by_cases hx : x ∈ Yo
  · obtain ⟨N, hN⟩ := exists_nat_gt (r x - R₀)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (N : ℝ) ≤ n := Nat.cast_le.2 hn
    have hlt : r x < R₀ + n := by linarith
    by_cases h : R₀ ≤ r x
    · rw [Set.indicator_of_mem, Set.indicator_of_mem]
      · exact show x ∈ Yo ∧ R₀ ≤ r x from ⟨hx, h⟩
      · rw [Set.mem_sdiff, hO, hO]
        exact ⟨⟨hx, hlt⟩, fun h' => absurd h'.2 (not_lt.2 h)⟩
    · rw [Set.indicator_of_notMem, Set.indicator_of_notMem]
      · exact fun h' => h (show x ∈ Yo ∧ R₀ ≤ r x from h').2
      · rw [Set.mem_sdiff, hO, hO]
        exact fun h' => h'.2 ⟨hx, lt_of_not_ge h⟩
  · refine Eventually.of_forall fun n => ?_
    rw [Set.indicator_of_notMem, Set.indicator_of_notMem]
    · exact fun h' => hx (show x ∈ Yo ∧ R₀ ≤ r x from h').1
    · rw [Set.mem_sdiff, hO]
      exact fun h' => hx h'.1.1

/- English proof (translation)
Introduce `X _ _ _ D A Om Yo r u v hYo hr hu hnn hv R₀ hR₀`. Take `⟨O, hOdef⟩ : ∃ O : ℝ → Set X, O = fun R => Yo ∩ r ⁻¹' Set.Iio R` from `⟨_, rfl⟩`. Establish `hOmem : ∀ R x, x ∈ O R ↔ x ∈ Yo ∧ r x < R` using `fun R x => by subst hOdef; exact Iff.rfl`. Establish `hO : ∀ R, IsOpen (O R)` using `fun R => by subst hOdef; exact hr.isOpen_inter_preimage hYo isOpen_Iio`. Establish `hOm : ∀ R j, MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' O R)` using `fun R j => measurableSet_chart_of_isOpen A (hO R) j`.

Establish `hRn : ∀ n : ℕ, Real.exp 1 ≤ R₀ + n` using `fun n => by`. Use `Nat.cast_nonneg (α := ℝ) n` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hBO : ∀ n : ℕ, O R₀ ⊆ O (R₀ + n)` using `fun n x hx => by`. Rewrite `hx`, the goal using `[hOmem]`.

Use `Nat.cast_nonneg (α := ℝ) n` as an intermediate fact. Conclude with `⟨hx.1, by linarith [hx.2]⟩`. Establish `hEm : ∀ (n : ℕ) j, MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (O (R₀ + n) \ O R₀))` using `fun n j => measurableSet_chart_diff A j (hOm _ j) (hOm _ j)`. Establish `hEt : ∀ n : ℕ, O (R₀ + n) \ O R₀ ⊆ tail Yo r R₀` using `fun n x hx => by`. Rewrite `hx` using `[Set.mem_sdiff, hOmem, hOmem]`.

Conclude with `show x ∈ Yo ∧ R₀ ≤ r x from ⟨hx.1.1, not_lt.1 fun h => hx.2 ⟨hx.1.1, h⟩⟩`. Establish `hpot : ∀ R, Real.exp 1 ≤ R → ∀ i, IsPotential A (potForm Om.pot (v R i))` using `fun R hR i => ReciprocityTheory.AnForm.M.isPotentialAdd A _ _ Om.isPot (ReciprocityTheory.AnForm.M.isPotential_ofFun A _ (hv R hR i).1)`. Establish `hpsh : ∀ R, Real.exp 1 ≤ R → ∀ i, IsPsh A (potForm Om.pot (v R i))` using `fun R hR i => (hv R hR i).2.1`. Establish `hvol : ∀ R, Real.exp 1 ≤ R → mInt A (fun i => potForm Om.pot (v R i)) (fun _ => 1) = Om.vol` using `fun R hR => ReciprocityTheory.AnForm.M.massIndep A (fun _ => Om.pot) (v R) (fun _ => Om.isPot) fun i => (hv R hR i).1`. Establish `hdens : ∀ R, Real.exp 1 ≤ R → ∀ j y, y ∈ (A.chart j).target → (A.chart j).symm y ∈ O R → locDens A (fun i => potForm Om.pot (u i)) j y = locDens A (fun i => potForm Om.pot (v R i)) j y`.

Introduce `R hR j y hy hyO`. Use `(locDens_potForm_congr A Om.pot u (v R) (O R) (hO R) j hy hyO fun i => ?_).symm` and prove the remaining obligations. Take `⟨c, hc⟩` from `(hv R hR i).2.2`. Conclude with `⟨c, fun x hx => hc x ((hOmem R x).1 hx).1 ((hOmem R x).1 hx).2⟩`. Establish `hnn0 : ∀ j y, y ∈ (A.chart j).target → (A.chart j).symm y ∈ Yo → 0 ≤ locDens A (fun i => potForm Om.pot (u i)) j y`.

Introduce `j y hy hyY`. Establish `hR : Real.exp 1 ≤ max (Real.exp 1) (r ((A.chart j).symm y) + 1)` using `le_max_left _ _`. Rewrite using `[hdens _ hR j y hy ((hOmem _ _).2 ⟨hyY, lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)⟩)]`. Conclude with `ReciprocityTheory.AnForm.M.locDens_nonneg_of_psh A _ (hpot _ hR) (hpsh _ hR) j hy`. Establish `hband : ∀ (n : ℕ) j y, y ∈ (A.chart j).target → (O (R₀ + n) \ O R₀).indicator (1 : X → ℝ) ((A.chart j).symm y) * locDens A (fun i => potForm Om.pot (u i)) j y = (O (R₀ + n) \ O R₀).indicator (1 : X → ℝ) ((A.chart j).symm y) * locDens A (fun i => potForm Om.pot (v (R₀ + n) i)) j y`.

Introduce `n j y hy`. Distinguish the cases in `hE : (A.chart j).symm y ∈ O (R₀ + n) \ O R₀`. Rewrite using `[hdens _ (hRn n) j y hy hE.1]`. Simplify using `[Set.indicator_of_notMem hE]`. Establish `hI : MIntegrable A (fun i => potForm Om.pot (u i)) ((tail Yo r R₀).indicator 1)`.

Introduce `j K hKt hK`. Establish `hG : ∀ n : ℕ, IntegrableOn (fun y => (O (R₀ + n) \ O R₀).indicator (1 : X → ℝ) ((A.chart j).symm y) * locDens A (fun i => potForm Om.pot (u i)) j y) K` using `fun n => (mIntegrable_indicator A _ (hpot _ (hRn n)) _ (hEm n) j K hKt hK).congr_fun (fun y hy => (hband n j y (hKt hy)).symm) hK.measurableSet`. Use `integrable_of_tendsto_of_integral_le hG (fun n => ?_) ?_ Om.vol fun n => ?_` and prove the remaining obligations. Use `filter_upwards [ae_restrict_mem hK.measurableSet] with y hy`. Distinguish the cases in `hE : (A.chart j).symm y ∈ O (R₀ + n) \ O R₀`.

Rewrite using `[Set.indicator_of_mem hE, Pi.one_apply, one_mul]`. Conclude with `hnn0 j y (hKt hy) ((hOmem _ _).1 hE.1).1`. Simplify using `[Set.indicator_of_notMem hE]`. Use `ae_of_all _ fun y => tendsto_const_nhds.congr' ?_ filter_upwards [indicator_band_eventually Yo r R₀ O hOmem ((A.chart j).symm y)] with n hn` and prove the remaining obligations. Rewrite using `[hn]`.

Establish `hd : IntegrableOn (locDens A (fun i => potForm Om.pot (v (R₀ + n) i)) j) K` using `((ReciprocityTheory.AnForm.M.locDensCont A _ (hpot _ (hRn n)) j).mono hKt).integrableOn_compact hK`. Combine the equalities or inequalities in the displayed calculation. Use `setIntegral_mono_on ((hG n).congr_fun (fun y hy => hband n j y (hKt hy)) hK.measurableSet) hd hK.measurableSet fun y hy => ?_` and prove the remaining obligations. Establish `h0` using `ReciprocityTheory.AnForm.M.locDens_nonneg_of_psh A _ (hpot _ (hRn n)) (hpsh _ (hRn n)) j (hKt hy)`. Distinguish the cases in `hE : (A.chart j).symm y ∈ O (R₀ + n) \ O R₀`.

Rewrite using `[Set.indicator_of_mem hE, Pi.one_apply, one_mul]`. Rewrite using `[Set.indicator_of_notMem hE, zero_mul]`. Conclude with `h0`. Use `_ ≤ mInt A (fun i => potForm Om.pot (v (R₀ + n) i)) (fun _ => 1) := setIntegral_locDens_le_mInt A _ (hpot _ (hRn n)) (hpsh _ (hRn n)) j K hKt hK`. Use `_ = Om.vol := hvol _ (hRn n)`.

Use `⟨hI, ?_⟩` and prove the remaining obligations. Establish `hIn : ∀ n : ℕ, mInt A (fun i => potForm Om.pot (u i)) ((O (R₀ + n) \ O R₀).indicator 1) ≤ mInt A (fun i => potForm Om.pot (v R₀ i)) ({x | x ∉ Yo ∨ R₀ ≤ r x}.indicator 1)`. Introduce `n`. Establish `e1 : mInt A (fun i => potForm Om.pot (u i)) ((O (R₀ + n) \ O R₀).indicator 1) = mInt A (fun i => potForm Om.pot (v (R₀ + n) i)) ((O (R₀ + n) \ O R₀).indicator 1)` using `ReciprocityTheory.AnForm.M.PLAux.mInt_congr fun j y hy => hband n j y hy`. Establish `e2 : ∀ R, Real.exp 1 ≤ R → O R₀ ⊆ O R → mInt A (fun i => potForm Om.pot (u i)) ((O R₀).indicator 1) = mInt A (fun i => potForm Om.pot (v R i)) ((O R₀).indicator 1)`.

Introduce `R hR hsub`. Use `ReciprocityTheory.AnForm.M.PLAux.mInt_congr fun j y hy => ?_` and prove the remaining obligations. Distinguish the cases in `hB : (A.chart j).symm y ∈ O R₀`. Rewrite using `[hdens R hR j y hy (hsub hB)]`. Simplify using `[Set.indicator_of_notMem hB]`.

Establish `e3` using `e2 _ (hRn n) (hBO n)`. Establish `e4` using `e2 _ hR₀ subset_rfl`. Establish `e5` using `mInt_indicator_union A _ (hpot _ (hRn n)) _ _ (hEm n) (hOm R₀) Set.disjoint_sdiff_left`. Rewrite `e5` using `[Set.sdiff_union_of_subset (hBO n)]`. Establish `e6` using `mInt_one_split A _ (hpot _ (hRn n)) _ (hOm (R₀ + n))`.

Establish `e7` using `mInt_one_split A _ (hpot _ hR₀) _ (hOm R₀)`. Establish `e8 : 0 ≤ mInt A (fun i => potForm Om.pot (v (R₀ + n) i)) ((O (R₀ + n))ᶜ.indicator 1)` using `ReciprocityTheory.AnForm.M.mIntNonneg A _ (hpot _ (hRn n)) (hpsh _ (hRn n)) _ (Set.indicator_nonneg fun _ _ => zero_le_one)`. Establish `e9 : {x | x ∉ Yo ∨ R₀ ≤ r x} = (O R₀)ᶜ`. Use extensionality with `x`. Rewrite using `[Set.mem_compl_iff, hOmem, Set.mem_ofPred_eq, not_and, not_lt]`.

The claim follows by propositional logic. Rewrite using `[e9]`. Use `hvol _ (hRn n)` as an intermediate fact. Use `hvol _ hR₀` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hne` using `ReciprocityTheory.AnForm.M.existsPartition A`. Establish `hm : ∀ g, mInt A (fun i => potForm Om.pot (u i)) g = integralWith A hne.some (fun i => potForm Om.pot (u i)) g` using `fun g => ReciprocityTheory.AnForm.M.mInt_eq_integralWith A _ hne g`. Establish `hlim : Tendsto (fun n : ℕ => mInt A (fun i => potForm Om.pot (u i)) ((O (R₀ + n) \ O R₀).indicator 1)) atTop (𝓝 (mInt A (fun i => potForm Om.pot (u i)) ((tail Yo r R₀).indicator 1)))`. Simplify using `only [hm]`. Unfold `ReciprocityTheory.AnForm.M.integralWith`.

Use `tendsto_finsetSum _ fun j _ => ?_` and prove the remaining obligations. Take `⟨hc, hsub⟩` from `ReciprocityTheory.AnForm.M.image_closed_compact (A.chart j) (isClosed_tsupport (hne.some.χ j)) (hne.some.tsupport_subset j)`. Establish `hχc` using `ReciprocityTheory.AnForm.M.PLAux.smooth_continuous (hne.some.smooth j)`. Establish `hbd : IntegrableOn (fun y => hne.some.χ j ((A.chart j).symm y) * (tail Yo r R₀).indicator 1 ((A.chart j).symm y) * locDens A (fun i => potForm Om.pot (u i)) j y) (A.chart j).target` using `ReciprocityTheory.AnForm.M.integrableOn_target_of_closed (A.chart j) (Z := tsupport (hne.some.χ j)) (fun y _ hy => by rw [image_eq_zero_of_notMem_tsupport hy, zero_mul, zero_mul]) (ReciprocityTheory.AnForm.M.mIntegrableMul A _ _ _ hI hχc j _ hsub hc)`. Establish `hFn : ∀ n : ℕ, IntegrableOn (fun y => hne.some.χ j ((A.chart j).symm y) * (O (R₀ + n) \ O R₀).indicator 1 ((A.chart j).symm y) * locDens A (fun i => potForm Om.pot (u i)) j y) (A.chart j).target` using `fun n => (ReciprocityTheory.AnForm.M.integrableOn_target_of_closed (A.chart j) (Z := tsupport (hne.some.χ j)) (fun y _ hy => by beta_reduce; rw [image_eq_zero_of_notMem_tsupport hy, zero_mul, zero_mul]) (ReciprocityTheory.AnForm.M.mIntegrableMul A _ _ _ (mIntegrable_indicator A _ …`.

Use `tendsto_integral_of_dominated_convergence _ (fun n => (hFn n).aestronglyMeasurable) hbd (fun n => ?_) ?_` and prove the remaining obligations. Use `filter_upwards [ae_restrict_mem (A.chart j).open_target.measurableSet] with y hy`. Establish `hχ` using `hne.some.nonneg j ((A.chart j).symm y)`. Distinguish the cases in `hY : (A.chart j).symm y ∈ Yo`. Establish `hd` using `hnn0 j y hy hY`.

Establish `hi0 : 0 ≤ (O (R₀ + n) \ O R₀).indicator (1 : X → ℝ) ((A.chart j).symm y)` using `Set.indicator_nonneg (fun _ _ => zero_le_one) _`. Establish `hi : (O (R₀ + n) \ O R₀).indicator (1 : X → ℝ) ((A.chart j).symm y) ≤ (tail Yo r R₀).indicator 1 ((A.chart j).symm y)` using `Set.indicator_le_indicator_of_subset (hEt n) (fun _ => zero_le_one) _`. Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg hχ hi0) hd)]`. Conclude with `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi hχ) hd`. Establish `h1 : (A.chart j).symm y ∉ O (R₀ + n) \ O R₀` using `fun h => hY ((hOmem _ _).1 h.1).1`.

Establish `h2 : (A.chart j).symm y ∉ tail Yo r R₀` using `fun h => hY (show (A.chart j).symm y ∈ Yo ∧ R₀ ≤ r ((A.chart j).symm y) from h).1`. Simplify using `[Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]`. Use `ae_of_all _ fun y => tendsto_const_nhds.congr' ?_ filter_upwards [indicator_band_eventually Yo r R₀ O hOmem ((A.chart j).symm y)] with n hn` and prove the remaining obligations. Rewrite using `[hn]`. Conclude with `le_of_tendsto' hlim hIn`.
-/
theorem LemmaETruncMass.proof : LemmaETruncMass.Statement := by
  intro X _ _ _ D A Om Yo r u v hYo hr hu hnn hv R₀ hR₀
  obtain ⟨O, hOdef⟩ : ∃ O : ℝ → Set X, O = fun R => Yo ∩ r ⁻¹' Set.Iio R := ⟨_, rfl⟩
  have hOmem : ∀ R x, x ∈ O R ↔ x ∈ Yo ∧ r x < R := fun R x => by subst hOdef; exact Iff.rfl
  have hO : ∀ R, IsOpen (O R) := fun R => by subst hOdef; exact hr.isOpen_inter_preimage hYo isOpen_Iio
  have hOm : ∀ R j, MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' O R) :=
    fun R j => measurableSet_chart_of_isOpen A (hO R) j
  have hRn : ∀ n : ℕ, Real.exp 1 ≤ R₀ + n := fun n => by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hBO : ∀ n : ℕ, O R₀ ⊆ O (R₀ + n) := fun n x hx => by
    rw [hOmem] at hx ⊢
    have := Nat.cast_nonneg (α := ℝ) n
    exact ⟨hx.1, by linarith [hx.2]⟩
  have hEm : ∀ (n : ℕ) j, MeasurableSet ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (O (R₀ + n) \ O R₀)) :=
    fun n j => measurableSet_chart_diff A j (hOm _ j) (hOm _ j)
  have hEt : ∀ n : ℕ, O (R₀ + n) \ O R₀ ⊆ tail Yo r R₀ := fun n x hx => by
    rw [Set.mem_sdiff, hOmem, hOmem] at hx
    exact show x ∈ Yo ∧ R₀ ≤ r x from ⟨hx.1.1, not_lt.1 fun h => hx.2 ⟨hx.1.1, h⟩⟩
  have hpot : ∀ R, Real.exp 1 ≤ R → ∀ i, IsPotential A (potForm Om.pot (v R i)) := fun R hR i =>
    ReciprocityTheory.AnForm.M.isPotentialAdd A _ _ Om.isPot
      (ReciprocityTheory.AnForm.M.isPotential_ofFun A _ (hv R hR i).1)
  have hpsh : ∀ R, Real.exp 1 ≤ R → ∀ i, IsPsh A (potForm Om.pot (v R i)) :=
    fun R hR i => (hv R hR i).2.1
  have hvol : ∀ R, Real.exp 1 ≤ R →
      mInt A (fun i => potForm Om.pot (v R i)) (fun _ => 1) = Om.vol := fun R hR =>
    ReciprocityTheory.AnForm.M.massIndep A (fun _ => Om.pot) (v R) (fun _ => Om.isPot) fun i => (hv R hR i).1
  have hdens : ∀ R, Real.exp 1 ≤ R → ∀ j y, y ∈ (A.chart j).target → (A.chart j).symm y ∈ O R →
      locDens A (fun i => potForm Om.pot (u i)) j y =
        locDens A (fun i => potForm Om.pot (v R i)) j y := by
    intro R hR j y hy hyO
    refine (locDens_potForm_congr A Om.pot u (v R) (O R) (hO R) j hy hyO fun i => ?_).symm
    obtain ⟨c, hc⟩ := (hv R hR i).2.2
    exact ⟨c, fun x hx => hc x ((hOmem R x).1 hx).1 ((hOmem R x).1 hx).2⟩
  have hnn0 : ∀ j y, y ∈ (A.chart j).target → (A.chart j).symm y ∈ Yo →
      0 ≤ locDens A (fun i => potForm Om.pot (u i)) j y := by
    intro j y hy hyY
    have hR : Real.exp 1 ≤ max (Real.exp 1) (r ((A.chart j).symm y) + 1) := le_max_left _ _
    rw [hdens _ hR j y hy ((hOmem _ _).2 ⟨hyY, lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)⟩)]
    exact ReciprocityTheory.AnForm.M.locDens_nonneg_of_psh A _ (hpot _ hR) (hpsh _ hR) j hy

  have hband : ∀ (n : ℕ) j y, y ∈ (A.chart j).target →
      (O (R₀ + n) \ O R₀).indicator (1 : X → ℝ) ((A.chart j).symm y) *
          locDens A (fun i => potForm Om.pot (u i)) j y =
        (O (R₀ + n) \ O R₀).indicator (1 : X → ℝ) ((A.chart j).symm y) *
          locDens A (fun i => potForm Om.pot (v (R₀ + n) i)) j y := by
    intro n j y hy
    by_cases hE : (A.chart j).symm y ∈ O (R₀ + n) \ O R₀
    · rw [hdens _ (hRn n) j y hy hE.1]
    · simp [Set.indicator_of_notMem hE]

  have hI : MIntegrable A (fun i => potForm Om.pot (u i)) ((tail Yo r R₀).indicator 1) := by
    intro j K hKt hK
    have hG : ∀ n : ℕ, IntegrableOn (fun y => (O (R₀ + n) \ O R₀).indicator (1 : X → ℝ)
        ((A.chart j).symm y) * locDens A (fun i => potForm Om.pot (u i)) j y) K := fun n =>
      (mIntegrable_indicator A _ (hpot _ (hRn n)) _ (hEm n) j K hKt hK).congr_fun
        (fun y hy => (hband n j y (hKt hy)).symm) hK.measurableSet
    refine integrable_of_tendsto_of_integral_le hG (fun n => ?_) ?_ Om.vol fun n => ?_
    · filter_upwards [ae_restrict_mem hK.measurableSet] with y hy
      by_cases hE : (A.chart j).symm y ∈ O (R₀ + n) \ O R₀
      · rw [Set.indicator_of_mem hE, Pi.one_apply, one_mul]
        exact hnn0 j y (hKt hy) ((hOmem _ _).1 hE.1).1
      · simp [Set.indicator_of_notMem hE]
    · refine ae_of_all _ fun y => tendsto_const_nhds.congr' ?_
      filter_upwards [indicator_band_eventually Yo r R₀ O hOmem ((A.chart j).symm y)] with n hn
      rw [hn]
    · have hd : IntegrableOn (locDens A (fun i => potForm Om.pot (v (R₀ + n) i)) j) K :=
        ((ReciprocityTheory.AnForm.M.locDensCont A _ (hpot _ (hRn n)) j).mono hKt).integrableOn_compact hK
      calc ∫ y in K, (O (R₀ + n) \ O R₀).indicator (1 : X → ℝ) ((A.chart j).symm y) *
            locDens A (fun i => potForm Om.pot (u i)) j y
          = ∫ y in K, (O (R₀ + n) \ O R₀).indicator (1 : X → ℝ) ((A.chart j).symm y) *
            locDens A (fun i => potForm Om.pot (v (R₀ + n) i)) j y :=
            setIntegral_congr_fun hK.measurableSet fun y hy => hband n j y (hKt hy)
        _ ≤ ∫ y in K, locDens A (fun i => potForm Om.pot (v (R₀ + n) i)) j y := by
            refine setIntegral_mono_on ((hG n).congr_fun (fun y hy => hband n j y (hKt hy))
              hK.measurableSet) hd hK.measurableSet fun y hy => ?_
            have h0 := ReciprocityTheory.AnForm.M.locDens_nonneg_of_psh A _ (hpot _ (hRn n))
              (hpsh _ (hRn n)) j (hKt hy)
            by_cases hE : (A.chart j).symm y ∈ O (R₀ + n) \ O R₀
            · rw [Set.indicator_of_mem hE, Pi.one_apply, one_mul]
            · rw [Set.indicator_of_notMem hE, zero_mul]
              exact h0
        _ ≤ mInt A (fun i => potForm Om.pot (v (R₀ + n) i)) (fun _ => 1) :=
            setIntegral_locDens_le_mInt A _ (hpot _ (hRn n)) (hpsh _ (hRn n)) j K hKt hK
        _ = Om.vol := hvol _ (hRn n)
  refine ⟨hI, ?_⟩

  have hIn : ∀ n : ℕ, mInt A (fun i => potForm Om.pot (u i)) ((O (R₀ + n) \ O R₀).indicator 1) ≤
      mInt A (fun i => potForm Om.pot (v R₀ i)) ({x | x ∉ Yo ∨ R₀ ≤ r x}.indicator 1) := by
    intro n
    have e1 : mInt A (fun i => potForm Om.pot (u i)) ((O (R₀ + n) \ O R₀).indicator 1) =
        mInt A (fun i => potForm Om.pot (v (R₀ + n) i)) ((O (R₀ + n) \ O R₀).indicator 1) :=
      ReciprocityTheory.AnForm.M.PLAux.mInt_congr fun j y hy => hband n j y hy
    have e2 : ∀ R, Real.exp 1 ≤ R → O R₀ ⊆ O R →
        mInt A (fun i => potForm Om.pot (u i)) ((O R₀).indicator 1) =
          mInt A (fun i => potForm Om.pot (v R i)) ((O R₀).indicator 1) := by
      intro R hR hsub
      refine ReciprocityTheory.AnForm.M.PLAux.mInt_congr fun j y hy => ?_
      by_cases hB : (A.chart j).symm y ∈ O R₀
      · rw [hdens R hR j y hy (hsub hB)]
      · simp [Set.indicator_of_notMem hB]
    have e3 := e2 _ (hRn n) (hBO n)
    have e4 := e2 _ hR₀ subset_rfl
    have e5 := mInt_indicator_union A _ (hpot _ (hRn n)) _ _ (hEm n) (hOm R₀)
      Set.disjoint_sdiff_left
    rw [Set.sdiff_union_of_subset (hBO n)] at e5
    have e6 := mInt_one_split A _ (hpot _ (hRn n)) _ (hOm (R₀ + n))
    have e7 := mInt_one_split A _ (hpot _ hR₀) _ (hOm R₀)
    have e8 : 0 ≤ mInt A (fun i => potForm Om.pot (v (R₀ + n) i)) ((O (R₀ + n))ᶜ.indicator 1) :=
      ReciprocityTheory.AnForm.M.mIntNonneg A _ (hpot _ (hRn n)) (hpsh _ (hRn n)) _
        (Set.indicator_nonneg fun _ _ => zero_le_one)
    have e9 : {x | x ∉ Yo ∨ R₀ ≤ r x} = (O R₀)ᶜ := by
      ext x
      rw [Set.mem_compl_iff, hOmem, Set.mem_ofPred_eq, not_and, not_lt]
      tauto
    rw [e9]
    have := hvol _ (hRn n)
    have := hvol _ hR₀
    linarith

  have hne := ReciprocityTheory.AnForm.M.existsPartition A
  have hm : ∀ g, mInt A (fun i => potForm Om.pot (u i)) g =
      integralWith A hne.some (fun i => potForm Om.pot (u i)) g := fun g =>
    ReciprocityTheory.AnForm.M.mInt_eq_integralWith A _ hne g
  have hlim : Tendsto (fun n : ℕ => mInt A (fun i => potForm Om.pot (u i))
      ((O (R₀ + n) \ O R₀).indicator 1)) atTop
      (𝓝 (mInt A (fun i => potForm Om.pot (u i)) ((tail Yo r R₀).indicator 1))) := by
    simp only [hm]
    unfold ReciprocityTheory.AnForm.M.integralWith
    refine tendsto_finsetSum _ fun j _ => ?_
    obtain ⟨hc, hsub⟩ := ReciprocityTheory.AnForm.M.image_closed_compact (A.chart j)
      (isClosed_tsupport (hne.some.χ j)) (hne.some.tsupport_subset j)
    have hχc := ReciprocityTheory.AnForm.M.PLAux.smooth_continuous (hne.some.smooth j)
    have hbd : IntegrableOn (fun y => hne.some.χ j ((A.chart j).symm y) *
        (tail Yo r R₀).indicator 1 ((A.chart j).symm y) *
        locDens A (fun i => potForm Om.pot (u i)) j y) (A.chart j).target :=
      ReciprocityTheory.AnForm.M.integrableOn_target_of_closed (A.chart j) (Z := tsupport (hne.some.χ j))
        (fun y _ hy => by rw [image_eq_zero_of_notMem_tsupport hy, zero_mul, zero_mul])
        (ReciprocityTheory.AnForm.M.mIntegrableMul A _ _ _ hI hχc j _ hsub hc)
    have hFn : ∀ n : ℕ, IntegrableOn (fun y => hne.some.χ j ((A.chart j).symm y) *
        (O (R₀ + n) \ O R₀).indicator 1 ((A.chart j).symm y) *
        locDens A (fun i => potForm Om.pot (u i)) j y) (A.chart j).target := fun n =>
      (ReciprocityTheory.AnForm.M.integrableOn_target_of_closed (A.chart j) (Z := tsupport (hne.some.χ j))
        (fun y _ hy => by beta_reduce; rw [image_eq_zero_of_notMem_tsupport hy, zero_mul, zero_mul])
        (ReciprocityTheory.AnForm.M.mIntegrableMul A _ _ _
          (mIntegrable_indicator A _ (hpot _ (hRn n)) _ (hEm n)) hχc j _ hsub hc)).congr_fun
        (fun y hy => by beta_reduce; rw [mul_assoc, mul_assoc, hband n j y hy]) (A.chart j).open_target.measurableSet
    refine tendsto_integral_of_dominated_convergence _ (fun n => (hFn n).aestronglyMeasurable) hbd
      (fun n => ?_) ?_
    · filter_upwards [ae_restrict_mem (A.chart j).open_target.measurableSet] with y hy
      have hχ := hne.some.nonneg j ((A.chart j).symm y)
      by_cases hY : (A.chart j).symm y ∈ Yo
      · have hd := hnn0 j y hy hY
        have hi0 : 0 ≤ (O (R₀ + n) \ O R₀).indicator (1 : X → ℝ) ((A.chart j).symm y) :=
          Set.indicator_nonneg (fun _ _ => zero_le_one) _
        have hi : (O (R₀ + n) \ O R₀).indicator (1 : X → ℝ) ((A.chart j).symm y) ≤
            (tail Yo r R₀).indicator 1 ((A.chart j).symm y) :=
          Set.indicator_le_indicator_of_subset (hEt n) (fun _ => zero_le_one) _
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg hχ hi0) hd)]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi hχ) hd
      · have h1 : (A.chart j).symm y ∉ O (R₀ + n) \ O R₀ := fun h => hY ((hOmem _ _).1 h.1).1
        have h2 : (A.chart j).symm y ∉ tail Yo r R₀ := fun h =>
          hY (show (A.chart j).symm y ∈ Yo ∧ R₀ ≤ r ((A.chart j).symm y) from h).1
        simp [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
    · refine ae_of_all _ fun y => tendsto_const_nhds.congr' ?_
      filter_upwards [indicator_band_eventually Yo r R₀ O hOmem ((A.chart j).symm y)] with n hn
      rw [hn]
  exact le_of_tendsto' hlim hIn

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
