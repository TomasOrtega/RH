import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4 GlobalTheory.Mean4O
open MeasureTheory
open scoped ComplexOrder Matrix

namespace GlobalTheory.Mean4O.CombInt

/- English proof (translation)
Establish `h0 : ∀ x : Fin D → ℂ, star x ⬝ᵥ (M *ᵥ x) = 0` using `fun x => by`. Establish `h1 : star (star x ⬝ᵥ (M *ᵥ x)) = star x ⬝ᵥ (M *ᵥ x)` using `by conv_lhs => rw [Matrix.star_dotProduct, Matrix.star_mulVec, star_star, hM.eq, dotProduct_comm]`. Rewrite using `[Matrix.dotProduct_mulVec]`. Conclude with `dotProduct_comm _ _`. Conclude with `Complex.ext (by simpa using h x) (by simpa using Complex.conj_eq_iff_im.1 h1)`.

Establish `hp : M.PosSemidef` using `Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hM fun x => (h0 x).ge`. Use extensionality with `i j`. Use `congrFun ((hp.dotProduct_mulVec_zero_iff (Pi.single j 1)).1 (h0 _)) i` as an intermediate fact. Simplify using `using this`.
-/
theorem herm_eq_zero {D : ℕ} {M : Matrix (Fin D) (Fin D) ℂ} (hM : M.IsHermitian)
    (h : ∀ x : Fin D → ℂ, (star x ⬝ᵥ (M *ᵥ x)).re = 0) : M = 0 := by
  have h0 : ∀ x : Fin D → ℂ, star x ⬝ᵥ (M *ᵥ x) = 0 := fun x => by
    have h1 : star (star x ⬝ᵥ (M *ᵥ x)) = star x ⬝ᵥ (M *ᵥ x) := by
      conv_lhs => rw [Matrix.star_dotProduct, Matrix.star_mulVec, star_star, hM.eq, dotProduct_comm]
      rw [Matrix.dotProduct_mulVec]
      exact dotProduct_comm _ _
    exact Complex.ext (by simpa using h x) (by simpa using Complex.conj_eq_iff_im.1 h1)
  have hp : M.PosSemidef := Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hM fun x => (h0 x).ge
  ext i j
  have := congrFun ((hp.dotProduct_mulVec_zero_iff (Pi.single j 1)).1 (h0 _)) i
  simpa using this

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Apply `herm_eq_zero` to reduce the goal to its premises. Use `(hessC_isHermitian' φ z hφ).sub ?_` and prove the remaining obligations. Unfold `Matrix.IsHermitian`. Rewrite using `[Matrix.conjTranspose_sum]`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.conjTranspose_smul, (hessC_isHermitian' _ z (hψ l)).eq]`. Simplify using the standard rewrite rules. Introduce `x`. Rewrite using `[Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, re_star_dot_hessC, h, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum, sub_eq_zero]`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul, re_star_dot_hessC]`.
-/
theorem hessC_comb {D m : ℕ} (φ : (Fin D → ℂ) → ℝ) (ψ : Fin m → (Fin D → ℂ) → ℝ) (c : Fin m → ℝ) (z : Fin D → ℂ)
    (hφ : ContDiffAt ℝ 2 φ z) (hψ : ∀ l, ContDiffAt ℝ 2 (ψ l) z)
    (h : ∀ w, levi φ z w = ∑ l, c l * levi (ψ l) z w) :
    hessC φ z = ∑ l, (c l : ℂ) • hessC (ψ l) z := by
  rw [← sub_eq_zero]
  apply herm_eq_zero
  · refine (hessC_isHermitian' φ z hφ).sub ?_
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.conjTranspose_smul, (hessC_isHermitian' _ z (hψ l)).eq]
    simp
  · intro x
    rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, re_star_dot_hessC, h, Matrix.sum_mulVec,
      dotProduct_sum, Complex.re_sum, sub_eq_zero]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul, re_star_dot_hessC]

/- English proof (translation)
Take `⟨M, hM⟩` from `ReciprocityTheory.AnForm.A.exists_multilinearMap_eq_mdisc (D := D)`. Unfold `maDens`. Simplify using `only [h, ← hM]`. Rewrite using `[M.map_sum, Complex.re_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations.

Rewrite using `[M.map_smul_univ, smul_eq_mul, ← Complex.ofReal_prod, Complex.re_ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem maDens_comb {D m : ℕ} (φ : Fin D → (Fin D → ℂ) → ℝ) (ψ : Fin D → Fin m → (Fin D → ℂ) → ℝ)
    (c : Fin D → Fin m → ℝ) (z : Fin D → ℂ)
    (h : ∀ i, hessC (φ i) z = ∑ l, (c i l : ℂ) • hessC (ψ i l) z) :
    maDens φ z = ∑ s : Fin D → Fin m, (∏ i, c i (s i)) * maDens (fun i => ψ i (s i)) z := by
  obtain ⟨M, hM⟩ := ReciprocityTheory.AnForm.A.exists_multilinearMap_eq_mdisc (D := D)
  unfold maDens
  simp only [h, ← hM]
  rw [M.map_sum, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [M.map_smul_univ, smul_eq_mul, ← Complex.ofReal_prod, Complex.re_ofReal_mul]
  ring

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {Z : Set X} {r : X → ℝ} {Om : LocPot X}

/- English proof (translation)
Take `⟨θ, u, rfl, hθ, -, -, hu, -⟩` from `hT`. Establish `h1` using `potential_contDiffAt A θ hθ j hy`. Establish `h2 : ContDiffAt ℝ 2 (u ∘ (A.chart j).symm) y` using `((hu j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm hZ.isOpen_compl).mem_nhds ⟨hy, hyZ⟩)).of_le (by norm_cast)`. Conclude with `h1.add h2`.
-/
theorem listForm_contDiffAt (hZ : IsClosed Z) {K : ℝ} {T : LocPot X} (hT : ListForm A Z r Om K T) (j : Fin A.n)
    {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) (hyZ : (A.chart j).symm y ∉ Z) :
    ContDiffAt ℝ 2 (fun y' => T.φ ((A.chart j).symm y) ((A.chart j).symm y')) y := by
  obtain ⟨θ, u, rfl, hθ, -, -, hu, -⟩ := hT
  have h1 := potential_contDiffAt A θ hθ j hy
  have h2 : ContDiffAt ℝ 2 (u ∘ (A.chart j).symm) y :=
    ((hu j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm hZ.isOpen_compl).mem_nhds ⟨hy, hyZ⟩)).of_le
      (by norm_cast)
  exact h1.add h2

/- English proof (translation)
Unfold `locDens`. Use `ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun k => ?_` and prove the remaining obligations. Use `hessC_posSemidef _ _ (listForm_contDiffAt hZ (hT k) j hy hyZ) fun w => ?_` and prove the remaining obligations. Take `⟨θ, u, -, -, -, -, -, -, -, h⟩` from `hT k`. Conclude with `h j y hy hyZ w`.
-/
theorem listForm_dens_nonneg (hZ : IsClosed Z) {K : ℝ} {T : Fin e → LocPot X} (hT : ∀ i, ListForm A Z r Om K (T i))
    (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) (hyZ : (A.chart j).symm y ∉ Z) :
    0 ≤ locDens A T j y := by
  unfold locDens
  refine ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun k => ?_
  refine hessC_posSemidef _ _ (listForm_contDiffAt hZ (hT k) j hy hyZ) fun w => ?_
  obtain ⟨θ, u, -, -, -, -, -, -, -, h⟩ := hT k
  exact h j y hy hyZ w

/- English proof (translation)
Rewrite using `[ae_restrict_iff' (A.chart j).open_target.measurableSet]`. Use `hb.2.1 j` as an intermediate fact. Rewrite `this` using `[← compl_mem_ae_iff]`. Use `filter_upwards [this] with y hy hyt`. Conclude with `⟨hyt, fun h => hy ⟨hyt, h⟩⟩`.
-/
theorem ae_notMem (hb : IsBd A Z r Om) (j : Fin A.n) :
    ∀ᵐ y ∂(volume.restrict (A.chart j).target), y ∈ (A.chart j).target ∧ (A.chart j).symm y ∉ Z := by
  rw [ae_restrict_iff' (A.chart j).open_target.measurableSet]
  have := hb.2.1 j
  rw [← compl_mem_ae_iff] at this
  filter_upwards [this] with y hy hyt
  exact ⟨hyt, fun h => hy ⟨hyt, h⟩⟩

/- English proof (translation)
Establish `hU` using `((A.chart j).isOpen_inter_preimage_symm hb.1.isOpen_compl).measurableSet`. Establish `h1 : AEMeasurable (r ∘ (A.chart j).symm) (volume.restrict ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Zᶜ))` using `(hb.2.2.2.2.1 j).continuousOn.aemeasurable hU`. Establish `h2 : (volume.restrict (A.chart j).target).restrict ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Zᶜ) = volume.restrict (A.chart j).target` using `Measure.restrict_eq_self_of_ae_mem (ae_notMem hb j)`. Rewrite `h2` using `[Measure.restrict_restrict hU, Set.inter_eq_left.2 Set.inter_subset_left]`. Rewrite using `[← h2]`.

Conclude with `h1`.
-/
theorem aemeasurable_r (hb : IsBd A Z r Om) (j : Fin A.n) :
    AEMeasurable (fun y => r ((A.chart j).symm y)) (volume.restrict (A.chart j).target) := by
  have hU := ((A.chart j).isOpen_inter_preimage_symm hb.1.isOpen_compl).measurableSet
  have h1 : AEMeasurable (r ∘ (A.chart j).symm)
      (volume.restrict ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Zᶜ)) :=
    (hb.2.2.2.2.1 j).continuousOn.aemeasurable hU
  have h2 : (volume.restrict (A.chart j).target).restrict ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Zᶜ) =
      volume.restrict (A.chart j).target :=
    Measure.restrict_eq_self_of_ae_mem (ae_notMem hb j)
  rw [Measure.restrict_restrict hU, Set.inter_eq_left.2 Set.inter_subset_left] at h2
  rw [← h2]
  exact h1

/- English proof (translation)
Establish `h1` using `integrableOn_weight A Q T _ hT j`. Establish `hl : ∀ x, x ∉ Z → 1 ≤ Real.log (r x)` using `fun x hx => (Real.le_log_iff_exp_le ((Real.exp_pos 1).trans_le (hb.2.2.2.2.2.1 x hx))).2 (hb.2.2.2.2.2.1 x hx)`. Establish `h2` using `Integrable.bdd_mul (c := 1) h1 (f := fun y => (Real.log (r ((A.chart j).symm y)))⁻¹) ((Real.measurable_log.inv.comp_aemeasurable (aemeasurable_r hb j)).aestronglyMeasurable) (by filter_upwards [ae_notMem hb j] with y hy`. Use `hl _ hy.2` as an intermediate fact. Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (by positivity)]`.

Conclude with `inv_le_one_of_one_le₀ this)`. Use `h2.congr ?_` and prove the remaining obligations. Use `filter_upwards [ae_notMem hb j] with y hy`. Use `hl _ hy.2` as an intermediate fact. Establish `hm : (A.chart j).symm y ∈ Set.univ ∩ Zᶜ` using `⟨trivial, hy.2⟩`.

Simplify using `only [cut, Set.indicator_of_mem hm]`. Clear the denominators using the available nonvanishing facts.
-/
theorem integrable_mass [CompactSpace X] [T2Space X] (hb : IsBd A Z r Om) (Q : ChartPartition A)
    {T : Fin e → LocPot X} (hT : MIntegrable A T (cut Z Set.univ fun x => Real.log (r x))) (j : Fin A.n) :
    IntegrableOn (fun y => Q.χ j ((A.chart j).symm y) * cut Z Set.univ (fun _ => 1) ((A.chart j).symm y) *
      locDens A T j y) (A.chart j).target := by
  have h1 := integrableOn_weight A Q T _ hT j
  have hl : ∀ x, x ∉ Z → 1 ≤ Real.log (r x) := fun x hx =>
    (Real.le_log_iff_exp_le ((Real.exp_pos 1).trans_le (hb.2.2.2.2.2.1 x hx))).2 (hb.2.2.2.2.2.1 x hx)
  have h2 := Integrable.bdd_mul (c := 1) h1
    (f := fun y => (Real.log (r ((A.chart j).symm y)))⁻¹)
    ((Real.measurable_log.inv.comp_aemeasurable (aemeasurable_r hb j)).aestronglyMeasurable) (by
      filter_upwards [ae_notMem hb j] with y hy
      have := hl _ hy.2
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact inv_le_one_of_one_le₀ this)
  refine h2.congr ?_
  filter_upwards [ae_notMem hb j] with y hy
  have := hl _ hy.2
  have hm : (A.chart j).symm y ∈ Set.univ ∩ Zᶜ := ⟨trivial, hy.2⟩
  simp only [cut, Set.indicator_of_mem hm]
  field_simp

/- English proof (translation)
Establish `h1` using `integrableOn_weight A Q T _ hT j`. Establish `h2` using `Integrable.bdd_mul (c := 1) h1 (f := fun y => (Set.Ici R).indicator (fun _ => (1 : ℝ)) (r ((A.chart j).symm y))) (((measurable_const.indicator measurableSet_Ici).comp_aemeasurable (aemeasurable_r hb j)).aestronglyMeasurable) (by filter_upwards with y`. Apply the tactic sequence `by_cases h : r ((A.chart j).symm y) ∈ Set.Ici R <;> simp [h])`. Use `h2.congr ?_` and prove the remaining obligations. Use `filter_upwards [ae_notMem hb j] with y hy`.

Use `hy.2` as an intermediate fact. Apply the tactic sequence `by_cases h : R ≤ r ((A.chart j).symm y) <;> simp [cut, h, this]`.
-/
theorem integrable_tail [CompactSpace X] [T2Space X] (hb : IsBd A Z r Om) (Q : ChartPartition A)
    {T : Fin e → LocPot X} (hT : MIntegrable A T (cut Z Set.univ fun x => Real.log (r x))) (R : ℝ) (j : Fin A.n) :
    IntegrableOn (fun y => Q.χ j ((A.chart j).symm y) *
      cut Z {x | R ≤ r x} (fun x => Real.log (r x)) ((A.chart j).symm y) * locDens A T j y) (A.chart j).target := by
  have h1 := integrableOn_weight A Q T _ hT j
  have h2 := Integrable.bdd_mul (c := 1) h1
    (f := fun y => (Set.Ici R).indicator (fun _ => (1 : ℝ)) (r ((A.chart j).symm y)))
    (((measurable_const.indicator measurableSet_Ici).comp_aemeasurable
      (aemeasurable_r hb j)).aestronglyMeasurable) (by
      filter_upwards with y
      by_cases h : r ((A.chart j).symm y) ∈ Set.Ici R <;> simp [h])
  refine h2.congr ?_
  filter_upwards [ae_notMem hb j] with y hy
  have := hy.2
  by_cases h : R ≤ r ((A.chart j).symm y) <;> simp [cut, h, this]

/- English proof (translation)
Introduce `e X _ _ _ A Z r Om hb K C hK hTail P g ε a R hP _ hε ha hR hg1 hg2`. Use `choose T c hTc hlev using fun i => (hP i).2`. Establish `hT : ∀ s : Fin e → Fin 3, ∀ i, ListForm A Z r Om K (T i (s i))` using `fun s i => (hTc i (s i)).1`. Establish `key : |mInt A P g| ≤ ∑ s : Fin e → Fin 3, K ^ e * (ε * mInt A (fun i => T i (s i)) (cut Z Set.univ fun _ => 1) + a * mInt A (fun i => T i (s i)) (cut Z {x | R ≤ r x} fun x => Real.log (r x)))`. Unfold `mInt`.

Use `split_ifs with h`. Use `swap`. Simplify using the standard rewrite rules. Unfold `integralWith`. Simplify using `only [Finset.mul_sum, ← Finset.sum_add_distrib]`.

Rewrite using `[Finset.sum_comm]`. Use `(Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)` and prove the remaining obligations. Establish `i0` using `fun s => integrable_mass hb h.some (hTail _ (hT s)).1 j`. Establish `i1` using `fun s => integrable_tail hb h.some (hTail _ (hT s)).1 R j`. Establish `i2` using `fun s => (((i0 s).const_mul ε).add ((i1 s).const_mul a)).const_mul (K ^ e)`.

Rewrite using `[← Real.norm_eq_abs]`. Use `(norm_integral_le_of_norm_le (integrable_finset_sum Finset.univ fun s _ => i2 s) ?_).trans (le_of_eq ?_)` and prove the remaining obligations. Use `filter_upwards [ae_notMem hb j] with y hy`. Establish `hd : locDens A P j y = ∑ s : Fin e → Fin 3, (∏ i, c i (s i)) * locDens A (fun i => T i (s i)) j y` using `maDens_comb _ (fun i l y' => (T i l).φ ((A.chart j).symm y) ((A.chart j).symm y')) c y fun i => hessC_comb _ _ _ _ (potential_contDiffAt A _ (hP i).1 j hy.1) (fun l => listForm_contDiffAt hb.1 (hTc i l).1 j hy.1 hy.2) (hlev i j y hy.1 hy.2)`. Rewrite using `[hd, Finset.mul_sum, Real.norm_eq_abs]`.

Use `(Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => ?_)` and prove the remaining obligations. Establish `hd0` using `listForm_dens_nonneg hb.1 (hT s) j hy.1 hy.2`. Establish `hχ` using `h.some.nonneg j ((A.chart j).symm y)`. Establish `hc : |∏ i, c i (s i)| ≤ K ^ e`. Rewrite using `[Finset.abs_prod]`.

Use `(Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ => (hTc i (s i)).2).trans (by simp)` and prove the remaining obligations. Establish `hg : |g ((A.chart j).symm y)| ≤ ε * cut Z Set.univ (fun _ => 1) ((A.chart j).symm y) + a * cut Z {x | R ≤ r x} (fun x => Real.log (r x)) ((A.chart j).symm y)`. Use `hy.2` as an intermediate fact. Distinguish the cases in `hr : R ≤ r ((A.chart j).symm y)`. Use `hg2 _ hy.2 hr` as an intermediate fact.

Simplify using `[cut, *]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `hg1 _ hy.2 (le_of_not_ge hr)` as an intermediate fact. Simplify using `[cut, *]`. Simplify using `only [Pi.add_apply]`.

Rewrite using `[abs_mul, abs_mul, abs_mul, abs_of_nonneg hd0, abs_of_nonneg hχ]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `mul_nonneg hχ ((abs_nonneg _).trans hg)`. Use `_ = _ := by ring`. Rewrite using `[integral_finset_sum _ fun s _ => i2 s]`.

Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[integral_const_mul]`. Simplify using `only [Pi.add_apply]`. Rewrite using `[integral_add ((i0 s).const_mul ε) ((i1 s).const_mul a), integral_const_mul, integral_const_mul]`. Use `key.trans ?_` and prove the remaining obligations.

Use `(Finset.sum_le_sum (g := fun _ => K ^ e * (ε * C + a * (C * Real.log R ^ (e + 1) / R))) fun s _ => ?_).trans (le_of_eq ?_)` and prove the remaining obligations. Establish `h1` using `(hTail _ (hT s)).2.1`. Establish `h2` using `(hTail _ (hT s)).2.2 R hR`. Use `gcongr`. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_fin, Finset.prod_const, nsmul_eq_mul, mul_pow]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem abs_mInt_comb_le : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Z : Set X) (r : X → ℝ) (Om : LocPot X), IsBd A Z r Om → ∀ (K C : ℝ), 0 ≤ K → Tail A Z r Om K C → ∀ (P : Fin e → LocPot X) (g : X → ℝ) (ε a R : ℝ), (∀ i, Comb A Z r Om K (P i)) → Continuous g → 0 ≤ ε → 0 ≤ a → Real.exp 1 ≤ R → (∀ x, x ∉ Z → r x ≤ R → |g x| ≤ ε) → (∀ x, x ∉ Z → R ≤ r x → |g x| ≤ a * Real.log (r x)) → |mInt A P g| ≤ (3 * K) ^ e * (ε * C + a * (C * Real.log R ^ (e + 1) / R)) := by
  intro e X _ _ _ A Z r Om hb K C hK hTail P g ε a R hP _ hε ha hR hg1 hg2
  choose T c hTc hlev using fun i => (hP i).2
  have hT : ∀ s : Fin e → Fin 3, ∀ i, ListForm A Z r Om K (T i (s i)) := fun s i => (hTc i (s i)).1
  have key : |mInt A P g| ≤ ∑ s : Fin e → Fin 3, K ^ e *
      (ε * mInt A (fun i => T i (s i)) (cut Z Set.univ fun _ => 1) +
        a * mInt A (fun i => T i (s i)) (cut Z {x | R ≤ r x} fun x => Real.log (r x))) := by
    unfold mInt
    split_ifs with h
    swap
    · simp
    unfold integralWith
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [Finset.sum_comm]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    have i0 := fun s => integrable_mass hb h.some (hTail _ (hT s)).1 j
    have i1 := fun s => integrable_tail hb h.some (hTail _ (hT s)).1 R j
    have i2 := fun s => (((i0 s).const_mul ε).add ((i1 s).const_mul a)).const_mul (K ^ e)
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (integrable_finset_sum Finset.univ fun s _ => i2 s) ?_).trans (le_of_eq ?_)
    · filter_upwards [ae_notMem hb j] with y hy
      have hd : locDens A P j y = ∑ s : Fin e → Fin 3, (∏ i, c i (s i)) * locDens A (fun i => T i (s i)) j y :=
        maDens_comb _ (fun i l y' => (T i l).φ ((A.chart j).symm y) ((A.chart j).symm y')) c y fun i =>
          hessC_comb _ _ _ _ (potential_contDiffAt A _ (hP i).1 j hy.1)
            (fun l => listForm_contDiffAt hb.1 (hTc i l).1 j hy.1 hy.2) (hlev i j y hy.1 hy.2)
      rw [hd, Finset.mul_sum, Real.norm_eq_abs]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => ?_)
      have hd0 := listForm_dens_nonneg hb.1 (hT s) j hy.1 hy.2
      have hχ := h.some.nonneg j ((A.chart j).symm y)
      have hc : |∏ i, c i (s i)| ≤ K ^ e := by
        rw [Finset.abs_prod]
        refine (Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ => (hTc i (s i)).2).trans (by simp)
      have hg : |g ((A.chart j).symm y)| ≤ ε * cut Z Set.univ (fun _ => 1) ((A.chart j).symm y) +
          a * cut Z {x | R ≤ r x} (fun x => Real.log (r x)) ((A.chart j).symm y) := by
        have := hy.2
        by_cases hr : R ≤ r ((A.chart j).symm y)
        · have := hg2 _ hy.2 hr
          simp [cut, *]
          linarith
        · have := hg1 _ hy.2 (le_of_not_ge hr)
          simp [cut, *]
      simp only [Pi.add_apply]
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hd0, abs_of_nonneg hχ]
      calc _ ≤ h.some.χ j ((A.chart j).symm y) * (ε * cut Z Set.univ (fun _ => 1) ((A.chart j).symm y) +
          a * cut Z {x | R ≤ r x} (fun x => Real.log (r x)) ((A.chart j).symm y)) *
            (K ^ e * locDens A (fun i => T i (s i)) j y) := by
            gcongr
            exact mul_nonneg hχ ((abs_nonneg _).trans hg)
        _ = _ := by ring
    · rw [integral_finset_sum _ fun s _ => i2 s]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [integral_const_mul]
      simp only [Pi.add_apply]
      rw [integral_add ((i0 s).const_mul ε) ((i1 s).const_mul a), integral_const_mul, integral_const_mul]
  refine key.trans ?_
  refine (Finset.sum_le_sum (g := fun _ => K ^ e * (ε * C + a * (C * Real.log R ^ (e + 1) / R))) fun s _ => ?_).trans
    (le_of_eq ?_)
  · have h1 := (hTail _ (hT s)).2.1
    have h2 := (hTail _ (hT s)).2.2 R hR
    gcongr
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_fin, Finset.prod_const, nsmul_eq_mul,
      mul_pow]
    push_cast
    ring

end GlobalTheory.Mean4O.CombInt
