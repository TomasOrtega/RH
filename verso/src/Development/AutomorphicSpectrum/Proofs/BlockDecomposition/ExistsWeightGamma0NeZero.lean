import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc

open UpperHalfPlane ModularGroup CongruenceSubgroup Complex
open scoped MatrixGroups Modular Pointwise ENNReal

namespace GlobalTheory.CompanionTheory.ModularTiling

/- English proof (translation)
Establish `hP : {p : Fin 2 → ℤ | normSq ((p 0 : ℂ) * z + p 1) ≤ 2 * z.im}.Finite`. Use `(tendsto_normSq_coprime_pair z).eventually (Filter.eventually_gt_atTop (2 * z.im))` as an intermediate fact. Rewrite `this` using `[Filter.eventually_cofinite]`. Use `this.subset fun p hp => ?_` and prove the remaining obligations. Simplify using `using hp`.

Establish `hfib : ∀ p : Fin 2 → ℤ, {g : SL(2, ℤ) | g 1 = p ∧ |(g • z).re| ≤ 1 / 2}.Finite`. Introduce `p`. Distinguish the cases in `hne : ∃ g : SL(2, ℤ), g 1 = p`. Take `⟨g₀, rfl⟩` from `hne`. Establish `hcop : IsCoprime (g₀ 1 0) (g₀ 1 1)` using `bottom_row_coprime g₀`.

Use `(tendsto_abs_re_smul z hcop).eventually (Filter.eventually_gt_atTop ((1 : ℝ) / 2))` as an intermediate fact. Rewrite `this` using `[Filter.eventually_cofinite]`. Use `(this.image Subtype.val).subset fun g hg => ?_` and prove the remaining obligations. Conclude with `⟨⟨g, hg.1⟩, by simpa using hg.2, rfl⟩`. Use `Set.Finite.subset Set.finite_empty fun g hg => ?_` and prove the remaining obligations.

Conclude with `(hne ⟨g, hg.1⟩).elim`. Use `(hP.biUnion fun p _ => hfib p).subset fun g hg => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_iUnion, Set.mem_setOf_eq]`. Use `⟨g 1, ?_, rfl, hg.2⟩` and prove the remaining obligations. Establish `him` using `three_le_four_mul_im_sq_of_mem_fd hg`.

Establish `hpos` using `(g • z).im_pos`. Establish `h12 : 1 / 2 ≤ (g • z).im` using `by nlinarith`. Establish `hz` using `z.im_pos`. Establish `heq` using `ModularGroup.im_smul_eq_div_normSq g z`. Establish `hN : 0 < normSq (denom g z)` using `normSq_pos.2 (denom_ne_zero _ _)`.

Rewrite `h12` using `[heq, denom_apply]`. Rewrite `hN` using `[denom_apply]`. Rewrite `h12` using `[le_div_iff₀ hN]`. Establish `: normSq (((g 1 0 : ℤ) : ℂ) * z + ((g 1 1 : ℤ) : ℂ)) ≤ 2 * z.im` using `by linarith`. Conclude with `this`.
-/
theorem finite_smul_mem_fd (z : ℍ) : {g : SL(2, ℤ) | g • z ∈ 𝒟}.Finite := by
  have hP : {p : Fin 2 → ℤ | normSq ((p 0 : ℂ) * z + p 1) ≤ 2 * z.im}.Finite := by
    have := (tendsto_normSq_coprime_pair z).eventually (Filter.eventually_gt_atTop (2 * z.im))
    rw [Filter.eventually_cofinite] at this
    refine this.subset fun p hp => ?_
    simpa using hp
  have hfib : ∀ p : Fin 2 → ℤ, {g : SL(2, ℤ) | g 1 = p ∧ |(g • z).re| ≤ 1 / 2}.Finite := by
    intro p
    by_cases hne : ∃ g : SL(2, ℤ), g 1 = p
    · obtain ⟨g₀, rfl⟩ := hne
      have hcop : IsCoprime (g₀ 1 0) (g₀ 1 1) := bottom_row_coprime g₀
      have := (tendsto_abs_re_smul z hcop).eventually (Filter.eventually_gt_atTop ((1 : ℝ) / 2))
      rw [Filter.eventually_cofinite] at this
      refine (this.image Subtype.val).subset fun g hg => ?_
      exact ⟨⟨g, hg.1⟩, by simpa using hg.2, rfl⟩
    · refine Set.Finite.subset Set.finite_empty fun g hg => ?_
      exact (hne ⟨g, hg.1⟩).elim
  refine (hP.biUnion fun p _ => hfib p).subset fun g hg => ?_
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  refine ⟨g 1, ?_, rfl, hg.2⟩
  have him := three_le_four_mul_im_sq_of_mem_fd hg
  have hpos := (g • z).im_pos
  have h12 : 1 / 2 ≤ (g • z).im := by nlinarith
  have hz := z.im_pos
  have heq := ModularGroup.im_smul_eq_div_normSq g z
  have hN : 0 < normSq (denom g z) := normSq_pos.2 (denom_ne_zero _ _)
  rw [heq, denom_apply] at h12
  rw [denom_apply] at hN
  rw [le_div_iff₀ hN] at h12
  have : normSq (((g 1 0 : ℤ) : ℂ) * z + ((g 1 1 : ℤ) : ℂ)) ≤ 2 * z.im := by linarith
  exact this

/- English proof (translation)
Establish `: Countable (Matrix (Fin 2) (Fin 2) ℤ)`. Unfold `Matrix`. Use `infer_instance`. Conclude with `Subtype.countable`.
-/
theorem countableSL : Countable SL(2, ℤ) := by
  have : Countable (Matrix (Fin 2) (Fin 2) ℤ) := by
    unfold Matrix
    infer_instance
  exact Subtype.countable

attribute [local instance] countableSL

/- English proof (translation)
The claim follows from `continuous_const_smul (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g))`.
-/
theorem continuous_smul_const (g : SL(2, ℤ)) : Continuous fun z : ℍ => g • z :=
  continuous_const_smul
    (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g))

/- English proof (translation)
Establish `h1 : IsClosed {z : ℍ | 1 ≤ normSq (z : ℂ)}` using `isClosed_le continuous_const (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe)`. Establish `h2 : IsClosed {z : ℍ | |z.re| ≤ (1 : ℝ) / 2}` using `isClosed_le (continuous_abs.comp UpperHalfPlane.continuous_re) continuous_const`. Conclude with `h1.inter h2`.
-/
theorem isClosed_fd : IsClosed (𝒟 : Set ℍ) := by
  have h1 : IsClosed {z : ℍ | 1 ≤ normSq (z : ℂ)} :=
    isClosed_le continuous_const (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe)
  have h2 : IsClosed {z : ℍ | |z.re| ≤ (1 : ℝ) / 2} :=
    isClosed_le (continuous_abs.comp UpperHalfPlane.continuous_re) continuous_const
  exact h1.inter h2

variable (Γ : Subgroup SL(2, ℤ))

def tile : Set ℍ := ⋃ x : SL(2, ℤ) ⧸ Γ, {z : ℍ | (Quotient.out x : SL(2, ℤ)) • z ∈ 𝒟}

noncomputable def mult (z : ℍ) : ℝ≥0∞ :=
  ∑' γ : Γ, (tile Γ).indicator (fun _ => (1 : ℝ≥0∞)) ((γ : SL(2, ℤ)) • z)

noncomputable def weight (z : ℍ) : ℝ :=
  (tile Γ).indicator (fun z => 2 / (mult Γ z).toReal) z

variable {Γ}

/- English proof (translation)
Simplify using `[tile]`.
-/
theorem mem_tile_iff {z : ℍ} :
    z ∈ tile Γ ↔ ∃ x : SL(2, ℤ) ⧸ Γ, (Quotient.out x : SL(2, ℤ)) • z ∈ 𝒟 := by
  simp [tile]

/- English proof (translation)
Establish `: Finite (SL(2, ℤ) ⧸ Γ)` using `Subgroup.finite_quotient_of_finiteIndex`. Conclude with `isClosed_iUnion_of_finite fun x => isClosed_fd.preimage (continuous_smul_const _)`.
-/
theorem isClosed_tile [Γ.FiniteIndex] : IsClosed (tile Γ) := by
  have : Finite (SL(2, ℤ) ⧸ Γ) := Subgroup.finite_quotient_of_finiteIndex
  exact isClosed_iUnion_of_finite fun x => isClosed_fd.preimage (continuous_smul_const _)

/- English proof (translation)
Establish `: Finite (SL(2, ℤ) ⧸ Γ)` using `Subgroup.finite_quotient_of_finiteIndex`. Establish `h : {g : SL(2, ℤ) | g • z ∈ tile Γ}.Finite`. Establish `: {g : SL(2, ℤ) | g • z ∈ tile Γ} = ⋃ x : SL(2, ℤ) ⧸ Γ, (fun g => (Quotient.out x : SL(2, ℤ)) * g) ⁻¹' {g | g • z ∈ 𝒟}`. Use extensionality with `g`. Simplify using `[mem_tile_iff, mul_smul]`.

Rewrite using `[this]`. Conclude with `Set.finite_iUnion fun x => (finite_smul_mem_fd z).preimage (mul_right_injective _).injOn`. Conclude with `h.preimage (f := (Subtype.val : Γ → SL(2, ℤ))) Subtype.val_injective.injOn`.
-/
theorem finite_smul_mem_tile [Γ.FiniteIndex] (z : ℍ) :
    {γ : Γ | (γ : SL(2, ℤ)) • z ∈ tile Γ}.Finite := by
  have : Finite (SL(2, ℤ) ⧸ Γ) := Subgroup.finite_quotient_of_finiteIndex
  have h : {g : SL(2, ℤ) | g • z ∈ tile Γ}.Finite := by
    have : {g : SL(2, ℤ) | g • z ∈ tile Γ} =
        ⋃ x : SL(2, ℤ) ⧸ Γ, (fun g => (Quotient.out x : SL(2, ℤ)) * g) ⁻¹' {g | g • z ∈ 𝒟} := by
      ext g
      simp [mem_tile_iff, mul_smul]
    rw [this]
    exact Set.finite_iUnion fun x =>
      (finite_smul_mem_fd z).preimage (mul_right_injective _).injOn
  exact h.preimage (f := (Subtype.val : Γ → SL(2, ℤ))) Subtype.val_injective.injOn

/- English proof (translation)
Take `⟨g, hg⟩` from `exists_smul_mem_fd z`. Establish `hmem : (Quotient.out (QuotientGroup.mk g : SL(2, ℤ) ⧸ Γ) : SL(2, ℤ))⁻¹ * g ∈ Γ`. Rewrite using `[← QuotientGroup.eq, QuotientGroup.out_eq']`. Use `⟨⟨_, hmem⟩, mem_tile_iff.2 ⟨QuotientGroup.mk g, ?_⟩⟩` and prove the remaining obligations. Use `show Quotient.out (QuotientGroup.mk g : SL(2, ℤ) ⧸ Γ) • ((Quotient.out (QuotientGroup.mk g : SL(2, ℤ) ⧸ Γ) : SL(2, ℤ))⁻¹ * g) • z ∈ 𝒟`.

Rewrite using `[smul_smul, mul_inv_cancel_left]`. Conclude with `hg`.
-/
theorem exists_smul_mem_tile (z : ℍ) : ∃ γ : Γ, (γ : SL(2, ℤ)) • z ∈ tile Γ := by
  obtain ⟨g, hg⟩ := exists_smul_mem_fd z
  have hmem : (Quotient.out (QuotientGroup.mk g : SL(2, ℤ) ⧸ Γ) : SL(2, ℤ))⁻¹ * g ∈ Γ := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
  refine ⟨⟨_, hmem⟩, mem_tile_iff.2 ⟨QuotientGroup.mk g, ?_⟩⟩
  show Quotient.out (QuotientGroup.mk g : SL(2, ℤ) ⧸ Γ) •
    ((Quotient.out (QuotientGroup.mk g : SL(2, ℤ) ⧸ Γ) : SL(2, ℤ))⁻¹ * g) • z ∈ 𝒟
  rw [smul_smul, mul_inv_cancel_left]
  exact hg

/- English proof (translation)
Establish `hf` using `finite_smul_mem_tile (Γ := Γ) z`. Rewrite using `[mult, tsum_eq_sum (s := hf.toFinset), Set.ncard_eq_toFinset_card _ hf]`. Rewrite using `[Finset.sum_congr rfl (g := fun _ => (1 : ℝ≥0∞))]`. Simplify using the standard rewrite rules. Introduce `γ hγ`.

Conclude with `Set.indicator_of_mem (by simpa using hγ) _`. Introduce `γ hγ`. Conclude with `Set.indicator_of_notMem (by simpa using hγ) _`.
-/
theorem mult_eq_ncard [Γ.FiniteIndex] (z : ℍ) :
    mult Γ z = ({γ : Γ | (γ : SL(2, ℤ)) • z ∈ tile Γ}.ncard : ℝ≥0∞) := by
  classical
  have hf := finite_smul_mem_tile (Γ := Γ) z
  rw [mult, tsum_eq_sum (s := hf.toFinset), Set.ncard_eq_toFinset_card _ hf]
  · rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ≥0∞))]
    · simp
    · intro γ hγ
      exact Set.indicator_of_mem (by simpa using hγ) _
  · intro γ hγ
    exact Set.indicator_of_notMem (by simpa using hγ) _

/- English proof (translation)
Unfold `mult`. Rewrite using `[← (Equiv.mulRight γ₀).tsum_eq (fun γ : Γ => (tile Γ).indicator (fun _ => (1 : ℝ≥0∞)) ((γ : SL(2, ℤ)) • z))]`. Simplify using `[mul_smul]`.
-/
theorem mult_smul (γ₀ : Γ) (z : ℍ) : mult Γ ((γ₀ : SL(2, ℤ)) • z) = mult Γ z := by
  unfold mult
  rw [← (Equiv.mulRight γ₀).tsum_eq
    (fun γ : Γ => (tile Γ).indicator (fun _ => (1 : ℝ≥0∞)) ((γ : SL(2, ℤ)) • z))]
  simp [mul_smul]

/- English proof (translation)
Use `Measurable.ennreal_tsum fun γ => ?_` and prove the remaining obligations. Conclude with `(measurable_const.indicator isClosed_tile.measurableSet).comp (continuous_smul_const _).measurable`.
-/
theorem measurable_mult [Γ.FiniteIndex] : Measurable (mult Γ) := by
  refine Measurable.ennreal_tsum fun γ => ?_
  exact (measurable_const.indicator isClosed_tile.measurableSet).comp
    (continuous_smul_const _).measurable

/- English proof (translation)
The claim follows from `(measurable_const.div measurable_mult.ennreal_toReal).indicator isClosed_tile.measurableSet`.
-/
theorem measurable_weight [Γ.FiniteIndex] : Measurable (weight Γ) :=
  (measurable_const.div measurable_mult.ennreal_toReal).indicator isClosed_tile.measurableSet

/- English proof (translation)
Unfold `weight`. Conclude with `Set.indicator_nonneg (fun _ _ => by positivity) z`.
-/
theorem weight_nonneg (z : ℍ) : 0 ≤ weight Γ z := by
  unfold weight
  exact Set.indicator_nonneg (fun _ _ => by positivity) z

/- English proof (translation)
Establish `hf` using `finite_smul_mem_tile (Γ := Γ) z`. Take `⟨γ₁, hγ₁⟩` from `exists_smul_mem_tile (Γ := Γ) z`. Establish `hcard : hf.toFinset.card ≠ 0` using `Finset.card_ne_zero.2 ⟨γ₁, by simpa using hγ₁⟩`. Establish `hm : (mult Γ z).toReal = hf.toFinset.card`. Rewrite using `[mult_eq_ncard, Set.ncard_eq_toFinset_card _ hf]`.

Simplify using the standard rewrite rules. Establish `hsum : ∑ γ ∈ hf.toFinset, weight Γ ((γ : SL(2, ℤ)) • z) = 2`. Rewrite using `[Finset.sum_congr rfl (g := fun _ => 2 / (hf.toFinset.card : ℝ))]`. Establish `: (hf.toFinset.card : ℝ) ≠ 0` using `by exact_mod_cast hcard`. Simplify using `only [Finset.sum_const, nsmul_eq_mul]`.

Clear the denominators using the available nonvanishing facts. Introduce `γ hγ`. Establish `: (γ : SL(2, ℤ)) • z ∈ tile Γ` using `by simpa using hγ`. Rewrite using `[weight, Set.indicator_of_mem this, mult_smul, hm]`. Rewrite using `[← hsum]`.

Use `hasSum_sum_of_ne_finset_zero fun γ hγ => ?_` and prove the remaining obligations. Conclude with `Set.indicator_of_notMem (by simpa using hγ) _`.
-/
theorem hasSum_weight [Γ.FiniteIndex] (z : ℍ) :
    HasSum (fun γ : Γ => weight Γ ((γ : SL(2, ℤ)) • z)) 2 := by
  classical
  have hf := finite_smul_mem_tile (Γ := Γ) z
  obtain ⟨γ₁, hγ₁⟩ := exists_smul_mem_tile (Γ := Γ) z
  have hcard : hf.toFinset.card ≠ 0 :=
    Finset.card_ne_zero.2 ⟨γ₁, by simpa using hγ₁⟩
  have hm : (mult Γ z).toReal = hf.toFinset.card := by
    rw [mult_eq_ncard, Set.ncard_eq_toFinset_card _ hf]
    simp
  have hsum : ∑ γ ∈ hf.toFinset, weight Γ ((γ : SL(2, ℤ)) • z) = 2 := by
    rw [Finset.sum_congr rfl (g := fun _ => 2 / (hf.toFinset.card : ℝ))]
    · have : (hf.toFinset.card : ℝ) ≠ 0 := by exact_mod_cast hcard
      simp only [Finset.sum_const, nsmul_eq_mul]
      field_simp
    · intro γ hγ
      have : (γ : SL(2, ℤ)) • z ∈ tile Γ := by simpa using hγ
      rw [weight, Set.indicator_of_mem this, mult_smul, hm]
  rw [← hsum]
  refine hasSum_sum_of_ne_finset_zero fun γ hγ => ?_
  exact Set.indicator_of_notMem (by simpa using hγ) _

/- English proof (translation)
Take `⟨γ, hγ⟩` from `exists_smul_mem_tile (Γ := Γ) z`. Establish `hf` using `finite_smul_mem_tile (Γ := Γ) z`. Use `(Set.one_lt_ncard_iff hf).2 ⟨γ, ⟨-1, hneg⟩ * γ, hγ, ?_, ?_⟩` and prove the remaining obligations. Use `show ((-1 : SL(2, ℤ)) * (γ : SL(2, ℤ))) • z ∈ tile Γ`. Rewrite using `[neg_one_mul, ModularGroup.SL_neg_smul]`.

Conclude with `hγ`. Introduce `h`. Establish `h' : (γ : SL(2, ℤ)) = (-1 : SL(2, ℤ)) * (γ : SL(2, ℤ))` using `congrArg Subtype.val h`. Establish `h1 : (-1 : SL(2, ℤ)) = 1` using `mul_right_cancel (b := (γ : SL(2, ℤ))) (by rw [one_mul]; exact h'.symm)`. Use `congrArg (fun g : SL(2, ℤ) => (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h1` as an intermediate fact.

Simplify using `at this`.
-/
theorem two_le_ncard (hneg : (-1 : SL(2, ℤ)) ∈ Γ) [Γ.FiniteIndex] (z : ℍ) :
    2 ≤ {γ : Γ | (γ : SL(2, ℤ)) • z ∈ tile Γ}.ncard := by
  obtain ⟨γ, hγ⟩ := exists_smul_mem_tile (Γ := Γ) z
  have hf := finite_smul_mem_tile (Γ := Γ) z
  refine (Set.one_lt_ncard_iff hf).2 ⟨γ, ⟨-1, hneg⟩ * γ, hγ, ?_, ?_⟩
  · show ((-1 : SL(2, ℤ)) * (γ : SL(2, ℤ))) • z ∈ tile Γ
    rw [neg_one_mul, ModularGroup.SL_neg_smul]
    exact hγ
  · intro h
    have h' : (γ : SL(2, ℤ)) = (-1 : SL(2, ℤ)) * (γ : SL(2, ℤ)) := congrArg Subtype.val h
    have h1 : (-1 : SL(2, ℤ)) = 1 :=
      mul_right_cancel (b := (γ : SL(2, ℤ))) (by rw [one_mul]; exact h'.symm)
    have := congrArg (fun g : SL(2, ℤ) => (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h1
    simp at this

/- English proof (translation)
Unfold `weight`. Distinguish the cases in `hz : z ∈ tile Γ`. Rewrite using `[Set.indicator_of_mem hz, mult_eq_ncard]`. Establish `h2 : (2 : ℝ) ≤ ({γ : Γ | (γ : SL(2, ℤ)) • z ∈ tile Γ}.ncard : ℝ)`. Conclude with `two_le_ncard hneg z` after adjusting the coercions.

Simplify using `only [ENNReal.toReal_natCast]`. Rewrite using `[div_le_one (by linarith)]`. Conclude with `h2`. Rewrite using `[Set.indicator_of_notMem hz]`. Conclude with `zero_le_one`.
-/
theorem weight_le_one (hneg : (-1 : SL(2, ℤ)) ∈ Γ) [Γ.FiniteIndex] (z : ℍ) : weight Γ z ≤ 1 := by
  unfold weight
  by_cases hz : z ∈ tile Γ
  · rw [Set.indicator_of_mem hz, mult_eq_ncard]
    have h2 : (2 : ℝ) ≤ ({γ : Γ | (γ : SL(2, ℤ)) • z ∈ tile Γ}.ncard : ℝ) := by
      exact_mod_cast two_le_ncard hneg z
    simp only [ENNReal.toReal_natCast]
    rw [div_le_one (by linarith)]
    exact h2
  · rw [Set.indicator_of_notMem hz]
    exact zero_le_one

/- English proof (translation)
Establish `: Fintype (SL(2, ℤ) ⧸ Γ)` using `@Fintype.ofFinite _ Subgroup.finite_quotient_of_finiteIndex`. Use `⟨Finset.univ.image fun x : SL(2, ℤ) ⧸ Γ => (Quotient.out x : SL(2, ℤ))⁻¹, weight Γ, measurable_weight, weight_nonneg, weight_le_one hneg, ?_, hasSum_weight⟩` and prove the remaining obligations. Introduce `z hz`. Establish `hzt : z ∈ tile Γ`. Assume the negation of the conclusion as `h`.

Conclude with `hz (Set.indicator_of_notMem h _)`. Take `⟨x, hx⟩` from `mem_tile_iff.1 hzt`. Simplify using `only [Set.mem_iUnion]`. Use `⟨(Quotient.out x : SL(2, ℤ))⁻¹, Finset.mem_image_of_mem _ (Finset.mem_univ x), ?_⟩` and prove the remaining obligations. Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem, inv_inv]`.

Conclude with `hx`.
-/
theorem exists_weight (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ) :
    ∃ (T : Finset SL(2, ℤ)) (β : ℍ → ℝ), Measurable β ∧ (∀ z, 0 ≤ β z) ∧ (∀ z, β z ≤ 1) ∧
      Function.support β ⊆ ⋃ σ ∈ T, σ • (𝒟 : Set ℍ) ∧
      ∀ z, HasSum (fun γ : Γ => β ((γ : SL(2, ℤ)) • z)) 2 := by
  classical
  have : Fintype (SL(2, ℤ) ⧸ Γ) :=
    @Fintype.ofFinite _ Subgroup.finite_quotient_of_finiteIndex
  refine ⟨Finset.univ.image fun x : SL(2, ℤ) ⧸ Γ => (Quotient.out x : SL(2, ℤ))⁻¹, weight Γ,
    measurable_weight, weight_nonneg, weight_le_one hneg, ?_, hasSum_weight⟩
  intro z hz
  have hzt : z ∈ tile Γ := by
    by_contra h
    exact hz (Set.indicator_of_notMem h _)
  obtain ⟨x, hx⟩ := mem_tile_iff.1 hzt
  simp only [Set.mem_iUnion]
  refine ⟨(Quotient.out x : SL(2, ℤ))⁻¹, Finset.mem_image_of_mem _ (Finset.mem_univ x), ?_⟩
  rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
  exact hx

/- English proof (translation)
The claim follows from `exists_weight (Gamma0 L) (by simp [Gamma0_mem])`.
-/
theorem exists_weight_Gamma0_neZero (L : ℕ) [NeZero L] :
    ∃ (T : Finset SL(2, ℤ)) (β : ℍ → ℝ), Measurable β ∧ (∀ z, 0 ≤ β z) ∧ (∀ z, β z ≤ 1) ∧
      Function.support β ⊆ ⋃ σ ∈ T, σ • (𝒟 : Set ℍ) ∧
      ∀ z, HasSum (fun γ : Gamma0 L => β ((γ : SL(2, ℤ)) • z)) 2 :=
  exists_weight (Gamma0 L) (by simp [Gamma0_mem])

/- English proof (translation)
Introduce `L hL`. Use `haveI : NeZero L := ⟨hL.ne'⟩`. Take `⟨T, β, hm, h0, h1, hs, hsum⟩` from `exists_weight_Gamma0_neZero L`. Use `⟨β, ⟨hm, fun z => ⟨h0 z, h1 z⟩, hsum⟩, T, fun z hz => ?_⟩` and prove the remaining obligations. Establish `h` using `hs (Function.mem_support.2 hz)`.

Simplify using `only [Set.mem_iUnion] at h`. Take `⟨σ, hσ, hz'⟩` from `h`. Conclude with `⟨σ, hσ, Set.mem_smul_set_iff_inv_smul_mem.1 hz'⟩`.
-/
theorem exists_weight_Gamma0 : Ad3.S.U0 := by
  intro L hL
  haveI : NeZero L := ⟨hL.ne'⟩
  obtain ⟨T, β, hm, h0, h1, hs, hsum⟩ := exists_weight_Gamma0_neZero L
  refine ⟨β, ⟨hm, fun z => ⟨h0 z, h1 z⟩, hsum⟩, T, fun z hz => ?_⟩
  have h := hs (Function.mem_support.2 hz)
  simp only [Set.mem_iUnion] at h
  obtain ⟨σ, hσ, hz'⟩ := h
  exact ⟨σ, hσ, Set.mem_smul_set_iff_inv_smul_mem.1 hz'⟩

end GlobalTheory.CompanionTheory.ModularTiling
