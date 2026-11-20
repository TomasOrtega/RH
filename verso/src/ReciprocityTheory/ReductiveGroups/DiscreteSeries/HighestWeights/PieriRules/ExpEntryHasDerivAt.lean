import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.KTypeIntDomStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Weight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.CountNotTwoOfFinrankLeOne
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.WeylSum
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.InnerLowerSelf
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.TensHW

noncomputable section

open Matrix Finset

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

abbrev conjMat : Matrix (Fin n) (Fin n) ℂ →+* Matrix (Fin n) (Fin n) ℂ := (starRingEnd ℂ).mapMatrix

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.star_apply, RingHom.mapMatrix_apply]`.
-/
theorem conjMat_star (g : Matrix (Fin n) (Fin n) ℂ) : star (conjMat g) = conjMat (star g) := by
  ext i j
  simp [Matrix.star_apply, RingHom.mapMatrix_apply]

/- English proof (translation)
Rewrite `hg`, the goal using `[Unitary.mem_iff]`. Rewrite using `[conjMat_star, ← map_mul, ← map_mul, hg.1, hg.2, map_one]`. Conclude with `⟨rfl, rfl⟩`.
-/
theorem conjMat_mem_unitary {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ unitary (Matrix (Fin n) (Fin n) ℂ)) :
    conjMat g ∈ unitary (Matrix (Fin n) (Fin n) ℂ) := by
  rw [Unitary.mem_iff] at hg ⊢
  rw [conjMat_star, ← map_mul, ← map_mul, hg.1, hg.2, map_one]
  exact ⟨rfl, rfl⟩

def rhoDual (ε : Fin n → Bool) : KG ε →* unitary (Matrix (Fin n) (Fin n) ℂ) where
  toFun k := ⟨conjMat (toMK k), conjMat_mem_unitary k.2.1⟩
  map_one' := by
    apply Subtype.ext
    show conjMat (toMK (1 : KG ε)) = 1
    rw [show toMK (1 : KG ε) = 1 from rfl, map_one]
  map_mul' k l := by
    apply Subtype.ext
    show conjMat (toMK (k * l)) = conjMat (toMK k) * conjMat (toMK l)
    rw [show toMK (k * l) = toMK k * toMK l from rfl, map_mul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rhoDual_apply (ε : Fin n → Bool) (k : KG ε) (i j : Fin n) :
    ((rhoDual ε k : unitary (Matrix (Fin n) (Fin n) ℂ)) : Matrix (Fin n) (Fin n) ℂ) i j =
      star (toMK k i j) := rfl

def dualD : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun X := -Xᵀ
  map_add' X Y := by rw [Matrix.transpose_add, neg_add]
  map_smul' c X := by rw [Matrix.transpose_smul, RingHom.id_apply, smul_neg]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dualD_apply (X : Matrix (Fin n) (Fin n) ℂ) : dualD X = -Xᵀ := rfl

/- English proof (translation)
Rewrite using `[dualD_apply, Matrix.transpose_single]`. Both sides reduce to the same expression.
-/
theorem dualD_single (a b : Fin n) : dualD (Matrix.single a b (1 : ℂ)) = dualM n a b := by
  rw [dualD_apply, Matrix.transpose_single]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `a b`. Conclude with `dualD_single a b`.
-/
theorem dualD_units : (fun a b : Fin n => dualD (Matrix.single a b (1 : ℂ))) = dualM n := by
  funext a b
  exact dualD_single a b

/- English proof (translation)
Establish `hK : Continuous (fun k : KG ε => toMK k)` using `Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)`. Conclude with `(continuous_id.matrix_map continuous_star).comp hK`.
-/
theorem continuous_rhoDual (ε : Fin n → Bool) :
    Continuous (fun k : KG ε => ((rhoDual ε k : unitary (Matrix (Fin n) (Fin n) ℂ)) :
      Matrix (Fin n) (Fin n) ℂ)) := by
  have hK : Continuous (fun k : KG ε => toMK k) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  exact (continuous_id.matrix_map continuous_star).comp hK

section Deriv

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/- English proof (translation)
Establish `h0` using `hasDerivAt_exp_smul_const' (𝕂 := ℝ) X (0 : ℝ)`. Rewrite `h0` using `[zero_smul, NormedSpace.exp_zero, mul_one]`. Set `L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ` to `{ toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }`. Establish `h1` using `(LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h0`. Establish `e : (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) = fun t : ℝ => LinearMap.toContinuousLinearMap L (NormedSpace.exp (t • X))`.

Use function extensionality and compare the values at `t`. Rewrite using `[Complex.coe_smul]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `h1`.
-/
theorem exp_entry_hasDerivAt (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) (X i j) 0 := by
  have h0 := hasDerivAt_exp_smul_const' (𝕂 := ℝ) X (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, mul_one] at h0
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have h1 := (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h0
  have e : (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) =
      fun t : ℝ => LinearMap.toContinuousLinearMap L (NormedSpace.exp (t • X)) := by
    funext t
    rw [Complex.coe_smul]
    rfl
  rw [e]
  exact h1

end Deriv

/- English proof (translation)
Introduce `X hX γ hγ i j`. Establish `hskew : Xᴴ = -X` using `((inK_iff' ε X).1 hX).1`. Establish `hval : star (X i j) = -X j i`. Use `congrFun (congrFun hskew j) i` as an intermediate fact. Simplify `this` using `[Matrix.conjTranspose_apply]`.

Establish `h` using `(exp_entry_hasDerivAt X i j).star`. Rewrite using `[dualD_apply, Matrix.neg_apply, Matrix.transpose_apply, ← hval]`. Establish `e : (fun t : ℝ => ((rhoDual ε (γ t) : unitary (Matrix (Fin n) (Fin n) ℂ)) : Matrix (Fin n) (Fin n) ℂ) i j) = fun t : ℝ => star (NormedSpace.exp ((t : ℂ) • X) i j)`. Use function extensionality and compare the values at `t`. Rewrite using `[rhoDual_apply, hγ t]`.

Rewrite using `[e]`. Conclude with `h`.
-/
theorem hasDeriv_rhoDual (ε : Fin n → Bool) :
    ∀ X, inK ε X → ∀ γ : ℝ → KG ε, (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      ∀ i j, HasDerivAt (fun t : ℝ => ((rhoDual ε (γ t) : unitary (Matrix (Fin n) (Fin n) ℂ)) :
        Matrix (Fin n) (Fin n) ℂ) i j) (dualD X i j) 0 := by
  intro X hX γ hγ i j
  have hskew : Xᴴ = -X := ((inK_iff' ε X).1 hX).1
  have hval : star (X i j) = -X j i := by
    have := congrFun (congrFun hskew j) i
    simpa [Matrix.conjTranspose_apply] using this
  have h := (exp_entry_hasDerivAt X i j).star
  rw [dualD_apply, Matrix.neg_apply, Matrix.transpose_apply, ← hval]
  have e : (fun t : ℝ => ((rhoDual ε (γ t) : unitary (Matrix (Fin n) (Fin n) ℂ)) :
      Matrix (Fin n) (Fin n) ℂ) i j) = fun t : ℝ => star (NormedSpace.exp ((t : ℂ) • X) i j) := by
    funext t
    rw [rhoDual_apply, hγ t]
  rw [e]
  exact h

/- English proof (translation)
Introduce `a b c d _ _`. Simplify using `only [dualM, neg_mul_neg]`. Apply the tactic sequence `rcases eq_or_ne a d with rfl | hda <;> rcases eq_or_ne c b with rfl | hcb`. Simplify using `only [Matrix.single_mul_single_same, mul_one, if_true]`. Normalize the expressions using the abelian group laws.

Simplify using `[hcb.symm]`. Conclude with `Matrix.single_mul_single_of_ne (h := hcb) ..`. Simplify using `[hda.symm]`. Conclude with `Matrix.single_mul_single_of_ne (h := hda) ..`. Simplify using `only [hda.symm, hcb.symm, if_false, sub_zero]`.

Rewrite using `[Matrix.single_mul_single_of_ne (h := hda) .., Matrix.single_mul_single_of_ne (h := hcb) .., sub_zero]`.
-/
theorem kRel_dualM (ε : Fin n → Bool) : Formalism.REAL.KRel ε (dualM n) := by
  intro a b c d _ _
  simp only [dualM, neg_mul_neg]
  rcases eq_or_ne a d with rfl | hda <;> rcases eq_or_ne c b with rfl | hcb
  · simp only [Matrix.single_mul_single_same, mul_one, if_true]
    abel
  · simp [hcb.symm]
    exact Matrix.single_mul_single_of_ne (h := hcb) ..
  · simp [hda.symm]
    exact Matrix.single_mul_single_of_ne (h := hda) ..
  · simp only [hda.symm, hcb.symm, if_false, sub_zero]
    rw [Matrix.single_mul_single_of_ne (h := hda) .., Matrix.single_mul_single_of_ne (h := hcb) .., sub_zero]

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Distinguish the cases in `hai : a = i`. Substitute `hai` using the available equality.

Simplify using `[dualM, dualWt]`. Simplify using `[dualM, dualWt, hai, Pi.single_apply]`. Simplify using `[dualM, Matrix.single_apply, hij]`. Introduce `h1 h2`. Conclude with `hij (h1.symm.trans h2)`.
-/
theorem dualM_diag (a : Fin n) :
    dualM n a a = Matrix.diagonal fun i => ((dualWt n i a : ℝ) : ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases hai : a = i
    · subst hai
      simp [dualM, dualWt]
    · simp [dualM, dualWt, hai, Pi.single_apply]
  · simp [dualM, Matrix.single_apply, hij]
    intro h1 h2
    exact hij (h1.symm.trans h2)

/- English proof (translation)
Introduce `i j h`. Establish `h'` using `congrFun h i`. Assume the negation of the conclusion as `hne`. Simplify using `[dualWt, Ne.symm hne] at h'`.
-/
theorem dualWt_injective : Function.Injective (dualWt n) := by
  intro i j h
  have h' := congrFun h i
  by_contra hne
  simp [dualWt, Ne.symm hne] at h'

/- English proof (translation)
Introduce `n ε Λ T`. Take `⟨hint, hdom⟩` from `hkt n ε Λ T`. Take `⟨hsum, hvan⟩` from `hws n ε Λ hint hdom`. Establish `hdiag : ∀ a, dualD (Matrix.single a a (1 : ℂ)) = Matrix.diagonal fun i => ((dualWt n i a : ℝ) : ℂ)` using `fun a => by`. Rewrite using `[dualD_single, dualM_diag]`.

Establish `hrel : Formalism.REAL.KRel ε (fun a b => dualD (Matrix.single a b (1 : ℂ)))`. Rewrite using `[dualD_units]`. Conclude with `kRel_dualM ε`. Establish `hsum' : ∑ i, weylK ε (Λ + dualWt n i) = (Fintype.card (Fin n) : ℝ) * weylK ε Λ`. Rewrite using `[Fintype.card_fin]`.

Conclude with `hsum`. Take `⟨hex, hall⟩` from `hcount n ε Λ T (Fin n) (rhoDual ε) dualD (dualWt n) (continuous_rhoDual ε) (hasDeriv_rhoDual ε) hrel hdiag dualWt_injective hsum' hvan`. Rewrite `hex`, `hall` using `[dualD_units]`. Establish `hfin` using `(hth T.V n ε (kunits T) Λ T.w (Fin n) (dualM n) (dualWt n) (KType.kRel T) (KType.kUnit T) (KType.kHighest_w T) (KType.kSpan_eq_top T) (kRel_dualM ε) dualM_diag).2`. Use `⟨hall, fun s => ?_, hex⟩` and prove the remaining obligations.

Use `(hfin (Λ + dualWt n s)).2.trans (le_of_eq ?_)` and prove the remaining obligations. Establish `hiff : ∀ i, (Λ + dualWt n s = Λ + dualWt n i) ↔ i = s` using `fun i => ⟨fun h => (dualWt_injective (add_left_cancel h)).symm, fun h => h ▸ rfl⟩`. Repeatedly rewrite using `[hiff]`. Simplify using the standard rewrite rules.
-/
theorem pieriDual_of_st (hcount : PieriCountStatement) (hws : WeylSumDualStatement)
    (hkt : KTypeIntDomStatement) (hth : TensHWStatement) : PieriDualStatement := by
  intro n ε Λ T
  obtain ⟨hint, hdom⟩ := hkt n ε Λ T
  obtain ⟨hsum, hvan⟩ := hws n ε Λ hint hdom
  have hdiag : ∀ a, dualD (Matrix.single a a (1 : ℂ)) =
      Matrix.diagonal fun i => ((dualWt n i a : ℝ) : ℂ) := fun a => by
    rw [dualD_single, dualM_diag]
  have hrel : Formalism.REAL.KRel ε (fun a b => dualD (Matrix.single a b (1 : ℂ))) := by
    rw [dualD_units]
    exact kRel_dualM ε
  have hsum' : ∑ i, weylK ε (Λ + dualWt n i) = (Fintype.card (Fin n) : ℝ) * weylK ε Λ := by
    rw [Fintype.card_fin]
    exact hsum
  obtain ⟨hex, hall⟩ := hcount n ε Λ T (Fin n) (rhoDual ε) dualD (dualWt n) (continuous_rhoDual ε)
    (hasDeriv_rhoDual ε) hrel hdiag dualWt_injective hsum' hvan
  rw [dualD_units] at hex hall
  have hfin := (hth T.V n ε (kunits T) Λ T.w (Fin n) (dualM n) (dualWt n) (KType.kRel T)
    (KType.kUnit T) (KType.kHighest_w T) (KType.kSpan_eq_top T) (kRel_dualM ε) dualM_diag).2
  refine ⟨hall, fun s => ?_, hex⟩
  refine (hfin (Λ + dualWt n s)).2.trans (le_of_eq ?_)
  have hiff : ∀ i, (Λ + dualWt n s = Λ + dualWt n i) ↔ i = s := fun i =>
    ⟨fun h => (dualWt_injective (add_left_cancel h)).symm, fun h => h ▸ rfl⟩
  simp_rw [hiff]
  simp

/- English proof (translation)
The claim follows from `pieriDual_of_st (pieriCount_of hc hr) weylSumDual kTypeIntDom tensHW`.
-/
theorem pieriDual_of (hc : CompRedStatement) (hr : KRepRelStatement) : PieriDualStatement :=
  pieriDual_of_st (pieriCount_of hc hr) weylSumDual kTypeIntDom tensHW

end ReciprocityTheory.ChartRestriction.DS.HW
