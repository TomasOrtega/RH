import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.UnitarizeA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ConjTransposeEqOfInG

noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.UnitB

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def sg (ε : Fin n → Bool) (c : Fin n) : ℂ := if ε c then 1 else -1

/- English proof (translation)
Unfold `sg`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
theorem sg_mul_self (ε : Fin n → Bool) (c : Fin n) : sg ε c * sg ε c = 1 := by
  unfold sg
  split_ifs <;> norm_num

/- English proof (translation)
Unfold `sg`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem star_sg (ε : Fin n → Bool) (c : Fin n) : star (sg ε c) = sg ε c := by
  unfold sg
  split_ifs <;> simp

/- English proof (translation)
Unfold `sg`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem norm_sg (ε : Fin n → Bool) (c : Fin n) : ‖sg ε c‖ = 1 := by
  unfold sg
  split_ifs <;> simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Jm_eq (ε : Fin n → Bool) : Jm ε = Matrix.diagonal (sg ε) := rfl

def wt (dual : Bool) (ε : Fin n → Bool) (ξ : Fin n) (x : Matrix (Fin n) (Fin n) ℂ) (c : Fin n) : ℂ :=
  cond dual (sg ε c * star (x ξ c)) (x ξ c)

/- English proof (translation)
Consider the cases of `dual`. Both sides reduce to the same expression. Simplify using `only [wt, cond_true, norm_mul, norm_sg, norm_star, one_mul]`.
-/
theorem norm_wt (dual : Bool) (ε : Fin n → Bool) (ξ : Fin n) (x : Matrix (Fin n) (Fin n) ℂ) (c : Fin n) :
    ‖wt dual ε ξ x c‖ = ‖x ξ c‖ := by
  cases dual
  · rfl
  · simp only [wt, cond_true, norm_mul, norm_sg, norm_star, one_mul]

/- English proof (translation)
Establish `h1 : ‖x i j‖ ^ 2 ≤ ∑ j', ‖x i j'‖ ^ 2` using `Finset.single_le_sum (f := fun j' => ‖x i j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)`. Establish `h2 : ∑ j', ‖x i j'‖ ^ 2 ≤ ∑ i', ∑ j', ‖x i' j'‖ ^ 2` using `Finset.single_le_sum (f := fun i' => ∑ j', ‖x i' j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)`. Establish `h3 : ‖x i j‖ ^ 2 ≤ S7.hs x`. Simplify using `only [S7.hs, Formalism.REAL.hs]`. Conclude with `h1.trans h2`.

Establish `h4` using `Real.abs_le_sqrt h3`. Rewrite `h4` using `[abs_of_nonneg (norm_nonneg _)]`. Then use the resulting hypothesis.
-/
theorem norm_entry_le (x : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : ‖x i j‖ ≤ Real.sqrt (S7.hs x) := by
  have h1 : ‖x i j‖ ^ 2 ≤ ∑ j', ‖x i j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun j' => ‖x i j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
  have h2 : ∑ j', ‖x i j'‖ ^ 2 ≤ ∑ i', ∑ j', ‖x i' j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', ‖x i' j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)
  have h3 : ‖x i j‖ ^ 2 ≤ S7.hs x := by
    simp only [S7.hs, Formalism.REAL.hs]
    exact h1.trans h2
  have h4 := Real.abs_le_sqrt h3
  rwa [abs_of_nonneg (norm_nonneg _)] at h4

/- English proof (translation)
Establish `he : Continuous (fun x : Matrix (Fin n) (Fin n) ℂ => x ξ c)` using `(continuous_apply c).comp (continuous_apply ξ)`. Consider the cases of `dual`. Conclude with `he`. Conclude with `continuous_const.mul he.star`.
-/
theorem continuous_wt (dual : Bool) (ε : Fin n → Bool) (ξ c : Fin n) :
    Continuous (fun x : Matrix (Fin n) (Fin n) ℂ => wt dual ε ξ x c) := by
  have he : Continuous (fun x : Matrix (Fin n) (Fin n) ℂ => x ξ c) :=
    (continuous_apply c).comp (continuous_apply ξ)
  cases dual
  · exact he
  · exact continuous_const.mul he.star

def wtLin (dual : Bool) (ε : Fin n → Bool) (ξ c : Fin n) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ where
  toFun x := wt dual ε ξ x c
  map_add' x y := by cases dual <;> simp [wt, mul_add]
  map_smul' r x := by
    cases dual <;> simp [wt, Complex.real_smul, Complex.conj_ofReal]; ring

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def cf (dual : Bool) (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (y : H) (ξ : Fin n)
    (F : Fin n → H) : Formalism.REAL.UJ ε → ℂ :=
  fun g => ∑ c, wt dual ε ξ (Formalism.MainNotions.S.umat g) c * inner ℂ y (σ (Formalism.MainNotions.S.umat g) (F c))

/- English proof (translation)
Use function extensionality and compare the values at `g`. Simplify using `only [cf, Pi.add_apply, map_add, inner_add_right, mul_add, Finset.sum_add_distrib]`.
-/
theorem cf_add (dual : Bool) (y : H) (ξ : Fin n) (F F' : Fin n → H) :
    cf dual ε σ y ξ (F + F') = cf dual ε σ y ξ F + cf dual ε σ y ξ F' := by
  funext g
  simp only [cf, Pi.add_apply, map_add, inner_add_right, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Use function extensionality and compare the values at `g`. Simplify using `only [cf, Pi.smul_apply, map_smul, inner_smul_right, smul_eq_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun c _ => by ring`.
-/
theorem cf_smul (dual : Bool) (y : H) (ξ : Fin n) (a : ℂ) (F : Fin n → H) :
    cf dual ε σ y ξ (a • F) = a • cf dual ε σ y ξ F := by
  funext g
  simp only [cf, Pi.smul_apply, map_smul, inner_smul_right, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

/- English proof (translation)
The claim follows from `Units.continuous_val.comp continuous_subtype_val`.
-/
theorem continuous_umat : Continuous (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g) := Units.continuous_val.comp continuous_subtype_val

/- English proof (translation)
The claim follows from `(hσ.2.2 v).comp_continuous continuous_umat fun g => g.2`.
-/
theorem continuous_orbit (hσ : IsURepOn (UJset ε) σ) (v : H) :
    Continuous (fun g : Formalism.REAL.UJ ε => σ (Formalism.MainNotions.S.umat g) v) := (hσ.2.2 v).comp_continuous continuous_umat fun g => g.2

/- English proof (translation)
Unfold `cf`. Conclude with `continuous_finset_sum _ fun c _ => ((continuous_wt dual ε ξ c).comp continuous_umat).mul (continuous_const.inner (continuous_orbit hσ (F c)))`.
-/
theorem continuous_cf (hσ : IsURepOn (UJset ε) σ) (dual : Bool) (y : H) (ξ : Fin n) (F : Fin n → H) :
    Continuous (cf dual ε σ y ξ F) := by
  unfold cf
  exact continuous_finset_sum _ fun c _ => ((continuous_wt dual ε ξ c).comp continuous_umat).mul
    (continuous_const.inner (continuous_orbit hσ (F c)))

/- English proof (translation)
Unfold `cf`. Use `memLp_finset_sum _ fun c _ => ?_` and prove the remaining obligations. Use `MemLp.of_le (hW c) ?_ (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Conclude with `(((continuous_wt dual ε ξ c).comp continuous_umat).mul (continuous_const.inner (continuous_orbit hσ (F c)))).aestronglyMeasurable`. Rewrite using `[norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), norm_wt]`.

Conclude with `mul_le_mul_of_nonneg_right (norm_entry_le _ ξ c) (norm_nonneg _)`.
-/
theorem memLp_cf (hσ : IsURepOn (UJset ε) σ) (dual : Bool) (y : H) (ξ : Fin n) (F : Fin n → H)
    (hW : ∀ c, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ y (σ (Formalism.MainNotions.S.umat g) (F c)))
      2 (Formalism.REAL.muG ε)) :
    MemLp (cf dual ε σ y ξ F) 2 (Formalism.REAL.muG ε) := by
  unfold cf
  refine memLp_finset_sum _ fun c _ => ?_
  refine MemLp.of_le (hW c) ?_ (Filter.Eventually.of_forall fun g => ?_)
  · exact (((continuous_wt dual ε ξ c).comp continuous_umat).mul
      (continuous_const.inner (continuous_orbit hσ (F c)))).aestronglyMeasurable
  · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), norm_wt]
    exact mul_le_mul_of_nonneg_right (norm_entry_le _ ξ c) (norm_nonneg _)

end Rep

end ReciprocityTheory.ChartRestriction.DS.UnitB
