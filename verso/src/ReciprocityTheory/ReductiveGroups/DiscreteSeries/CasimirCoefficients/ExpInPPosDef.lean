import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.PolarJmConjTranspose

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {ε : Fin n → Bool}

open PolarDecomposition

/- English proof (translation)
Unfold `Jm`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
private lemma Jm_mul_self_eq_one' : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

/- English proof (translation)
Unfold `Jm`. Rewrite using `[Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Simplify using `only [Pi.star_apply]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
private lemma Jm_conjTranspose_eq_self' : (Jm ε)ᴴ = Jm ε := by
  unfold Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  simp only [Pi.star_apply]
  split_ifs <;> simp

/- English proof (translation)
Take `⟨hG, hXJ⟩` from `hX`. Establish `hJ` using `Jm_mul_self_eq_one' (ε := ε)`. Establish `h1 : Xᴴ * Jm ε = X * Jm ε`. Rewrite using `[hXJ]`. Unfold `inG at hG`.

Conclude with `eq_neg_of_add_eq_zero_left hG`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma isHermitian_of_mem_noncompactPart' {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) : Xᴴ = X := by
  obtain ⟨hG, hXJ⟩ := hX
  have hJ := Jm_mul_self_eq_one' (ε := ε)
  have h1 : Xᴴ * Jm ε = X * Jm ε := by
    rw [hXJ]
    unfold inG at hG
    exact eq_neg_of_add_eq_zero_left hG
  calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [mul_assoc, hJ, mul_one]
    _ = X * Jm ε * Jm ε := by rw [h1]
    _ = X := by rw [mul_assoc, hJ, mul_one]

/- English proof (translation)
Rewrite using `[mul_assoc, hX.2, mul_neg, ← mul_assoc, Jm_mul_self_eq_one', one_mul]`.
-/
lemma inP_JXJ {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) : Jm ε * X * Jm ε = -X := by
  rw [mul_assoc, hX.2, mul_neg, ← mul_assoc, Jm_mul_self_eq_one', one_mul]

/- English proof (translation)
Establish `hk : toMK k ∈ Kset ε` using `k.2`. Take `⟨hu, hc⟩` from `hk`. Use `⟨?_, ?_, hc⟩` and prove the remaining obligations. Establish `h` using `Matrix.mem_unitaryGroup_iff'.1 hu`. Rewrite `h` using `[Matrix.star_eq_conjTranspose]`. Then use the resulting hypothesis.

Establish `h` using `Matrix.mem_unitaryGroup_iff.1 hu`. Rewrite `h` using `[Matrix.star_eq_conjTranspose]`. Then use the resulting hypothesis.
-/
lemma toMK_facts (k : KG ε) : (toMK k)ᴴ * toMK k = 1 ∧ toMK k * (toMK k)ᴴ = 1 ∧
    toMK k * Jm ε = Jm ε * toMK k := by
  have hk : toMK k ∈ Kset ε := k.2
  obtain ⟨hu, hc⟩ := hk
  refine ⟨?_, ?_, hc⟩
  · have h := Matrix.mem_unitaryGroup_iff'.1 hu
    rwa [Matrix.star_eq_conjTranspose] at h
  · have h := Matrix.mem_unitaryGroup_iff.1 hu
    rwa [Matrix.star_eq_conjTranspose] at h

/- English proof (translation)
Establish `h1 : toMK k⁻¹ * toMK k = 1`. Unfold `toMK toM`. Simplify using the standard rewrite rules. Establish `h2` using `(toMK_facts k).2.1`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma toMK_inv (k : KG ε) : toMK k⁻¹ = (toMK k)ᴴ := by
  have h1 : toMK k⁻¹ * toMK k = 1 := by
    unfold toMK toM
    simp
  have h2 := (toMK_facts k).2.1
  calc toMK k⁻¹ = toMK k⁻¹ * (toMK k * (toMK k)ᴴ) := by rw [h2, mul_one]
    _ = (toMK k)ᴴ := by rw [← mul_assoc, h1, one_mul]

/- English proof (translation)
Take `⟨hu, hc⟩` from `hk`. Establish `h1 : k * kᴴ = 1`. Establish `h` using `Matrix.mem_unitaryGroup_iff.1 hu`. Rewrite `h` using `[Matrix.star_eq_conjTranspose]`. Then use the resulting hypothesis. Establish `h2 : kᴴ * k = 1`.

Establish `h` using `Matrix.mem_unitaryGroup_iff'.1 hu`. Rewrite `h` using `[Matrix.star_eq_conjTranspose]`. Then use the resulting hypothesis. Establish `hUJ : inUJ ε k`. Unfold `inUJ`. Rewrite using `[mul_assoc, ← hc, ← mul_assoc, h2, one_mul]`.

Use `⟨⟨⟨⟨k, kᴴ, h1, h2⟩, ?_⟩, ?_⟩, rfl⟩` and prove the remaining obligations. Conclude with `hUJ`. Conclude with `(⟨hu, hc⟩ : k ∈ Kset ε)`.
-/
lemma exists_toMK {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : ∃ u : KG ε, toMK u = k := by
  obtain ⟨hu, hc⟩ := hk
  have h1 : k * kᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.1 hu
    rwa [Matrix.star_eq_conjTranspose] at h
  have h2 : kᴴ * k = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.1 hu
    rwa [Matrix.star_eq_conjTranspose] at h
  have hUJ : inUJ ε k := by
    unfold inUJ
    rw [mul_assoc, ← hc, ← mul_assoc, h2, one_mul]
  refine ⟨⟨⟨⟨k, kᴴ, h1, h2⟩, ?_⟩, ?_⟩, rfl⟩
  · exact hUJ
  · exact (⟨hu, hc⟩ : k ∈ Kset ε)

/- English proof (translation)
Rewrite using `[Matrix.conjTranspose_mul, ← Matrix.exp_conjTranspose, hH, mul_assoc, ← mul_assoc (toMK k)ᴴ, (toMK_facts k).1, one_mul, ← Matrix.exp_add_of_commute _ _ (Commute.refl _)]`.
-/
lemma kexp_sq (k : KG ε) {X : Matrix (Fin n) (Fin n) ℂ} (hH : Xᴴ = X) :
    (toMK k * NormedSpace.exp X)ᴴ * (toMK k * NormedSpace.exp X) = NormedSpace.exp (X + X) := by
  rw [Matrix.conjTranspose_mul, ← Matrix.exp_conjTranspose, hH, mul_assoc, ← mul_assoc (toMK k)ᴴ,
    (toMK_facts k).1, one_mul, ← Matrix.exp_add_of_commute _ _ (Commute.refl _)]

/- English proof (translation)
Take `⟨k, hk, Y, hY, hgk⟩` from `polar_UJ (ε := ε) (g := g) hg`. Take `⟨u, hu⟩` from `exists_toMK hk`. Conclude with `⟨u, Y, hY, by rw [hu]; exact hgk⟩`.
-/
theorem polar_exists {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    ∃ (k : KG ε) (X : Matrix (Fin n) (Fin n) ℂ), inP ε X ∧ g = toMK k * NormedSpace.exp X := by
  obtain ⟨k, hk, Y, hY, hgk⟩ := polar_UJ (ε := ε) (g := g) hg
  obtain ⟨u, hu⟩ := exists_toMK hk
  exact ⟨u, Y, hY, by rw [hu]; exact hgk⟩

/- English proof (translation)
Establish `hH` using `isHermitian_of_mem_noncompactPart' hX`. Establish `hH'` using `isHermitian_of_mem_noncompactPart' hX'`. Establish `hXX : X + X = X' + X'`. Use `polar_exp_inj (by rw [conjTranspose_add, hH]) (by rw [conjTranspose_add, hH']) ?_` and prove the remaining obligations. Rewrite using `[← kexp_sq k hH, ← kexp_sq k' hH', h]`.

Establish `hXe : X = X'` using `polar_half hXX`. Substitute `hXe` using the available equality. Use `⟨?_, rfl⟩` and prove the remaining obligations. Establish `hm : toMK k = toMK k'`. Use `congrArg (· * NormedSpace.exp (-X)) h` as an intermediate fact.

Simplify using `only [Matrix.mul_assoc, polar_exp_mul_neg, Matrix.mul_one] at this`. Conclude with `this`. Conclude with `Subtype.ext (Subtype.ext (Units.ext hm))`.
-/
theorem polar_unique {k k' : KG ε} {X X' : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) (hX' : inP ε X')
    (h : toMK k * NormedSpace.exp X = toMK k' * NormedSpace.exp X') : k = k' ∧ X = X' := by
  have hH := isHermitian_of_mem_noncompactPart' hX
  have hH' := isHermitian_of_mem_noncompactPart' hX'
  have hXX : X + X = X' + X' := by
    refine polar_exp_inj (by rw [conjTranspose_add, hH]) (by rw [conjTranspose_add, hH']) ?_
    rw [← kexp_sq k hH, ← kexp_sq k' hH', h]
  have hXe : X = X' := polar_half hXX
  subst hXe
  refine ⟨?_, rfl⟩
  have hm : toMK k = toMK k' := by
    have := congrArg (· * NormedSpace.exp (-X)) h
    simp only [Matrix.mul_assoc, polar_exp_mul_neg, Matrix.mul_one] at this
    exact this
  exact Subtype.ext (Subtype.ext (Units.ext hm))

/- English proof (translation)
Establish `hJ` using `Jm_mul_self_eq_one' (ε := ε)`. Establish `hJinv : (Jm ε)⁻¹ = Jm ε` using `Matrix.inv_eq_left_inv hJ`. Establish `hJu : IsUnit (Jm ε)` using `⟨⟨Jm ε, Jm ε, hJ, hJ⟩, rfl⟩`. Establish `hconj : Jm ε * NormedSpace.exp X * Jm ε = NormedSpace.exp (-X)`. Establish `h` using `Matrix.exp_conj (Jm ε) X hJu`.

Rewrite `h` using `[hJinv, inP_JXJ hX]`. Conclude with `h.symm`. Establish `hf` using `toMK_facts k`. Unfold `inUJ`. Rewrite using `[Matrix.conjTranspose_mul, ← Matrix.exp_conjTranspose, isHermitian_of_mem_noncompactPart' hX]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`. Use `_ = NormedSpace.exp X * ((toMK k)ᴴ * (toMK k * Jm ε)) * NormedSpace.exp X := by`. Rewrite using `[← hf.2.2]`. Use `_ = NormedSpace.exp X * Jm ε * NormedSpace.exp X := by`.

Rewrite using `[← mul_assoc (toMK k)ᴴ, hf.1, one_mul]`. Use `_ = Jm ε * (Jm ε * NormedSpace.exp X * Jm ε) * NormedSpace.exp X := by`. Simplify using `only [← mul_assoc, hJ, one_mul]`. Use `_ = Jm ε * NormedSpace.exp (-X) * NormedSpace.exp X := by rw [hconj]`. Use `_ = Jm ε := by`.

Rewrite using `[mul_assoc, ← Matrix.exp_add_of_commute _ _ ((Commute.refl X).neg_left), neg_add_cancel, NormedSpace.exp_zero, mul_one]`.
-/
theorem inUJ_kexp (k : KG ε) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) : inUJ ε (toMK k * NormedSpace.exp X) := by
  have hJ := Jm_mul_self_eq_one' (ε := ε)
  have hJinv : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv hJ
  have hJu : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, hJ, hJ⟩, rfl⟩
  have hconj : Jm ε * NormedSpace.exp X * Jm ε = NormedSpace.exp (-X) := by
    have h := Matrix.exp_conj (Jm ε) X hJu
    rw [hJinv, inP_JXJ hX] at h
    exact h.symm
  have hf := toMK_facts k
  unfold inUJ
  rw [Matrix.conjTranspose_mul, ← Matrix.exp_conjTranspose, isHermitian_of_mem_noncompactPart' hX]
  calc NormedSpace.exp X * (toMK k)ᴴ * Jm ε * (toMK k * NormedSpace.exp X)
      = NormedSpace.exp X * ((toMK k)ᴴ * (Jm ε * toMK k)) * NormedSpace.exp X := by
        simp only [mul_assoc]
    _ = NormedSpace.exp X * ((toMK k)ᴴ * (toMK k * Jm ε)) * NormedSpace.exp X := by
        rw [← hf.2.2]
    _ = NormedSpace.exp X * Jm ε * NormedSpace.exp X := by
        rw [← mul_assoc (toMK k)ᴴ, hf.1, one_mul]
    _ = Jm ε * (Jm ε * NormedSpace.exp X * Jm ε) * NormedSpace.exp X := by
        simp only [← mul_assoc, hJ, one_mul]
    _ = Jm ε * NormedSpace.exp (-X) * NormedSpace.exp X := by rw [hconj]
    _ = Jm ε := by
        rw [mul_assoc, ← Matrix.exp_add_of_commute _ _ ((Commute.refl X).neg_left), neg_add_cancel,
          NormedSpace.exp_zero, mul_one]

/- English proof (translation)
Establish `hf` using `toMK_facts k`. Establish `hinv : (toMK k)⁻¹ = (toMK k)ᴴ` using `Matrix.inv_eq_right_inv hf.2.1`. Establish `hu : IsUnit (toMK k)` using `⟨⟨toMK k, (toMK k)ᴴ, hf.2.1, hf.1⟩, rfl⟩`. Establish `hcJ : (toMK k)ᴴ * Jm ε = Jm ε * (toMK k)ᴴ`. Establish `h` using `congrArg Matrix.conjTranspose hf.2.2`.

Simplify using `only [Matrix.conjTranspose_mul, Jm_conjTranspose_eq_self'] at h`. Conclude with `h.symm`. Establish `h2 : toMK k * X * (toMK k)ᴴ * Jm ε = -(Jm ε * (toMK k * X * (toMK k)ᴴ))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc _ (toMK k)ᴴ, hcJ]`.

Simplify using `only [mul_assoc]`. Use `_ = toMK k * (-(Jm ε * X)) * (toMK k)ᴴ := by rw [hX.2]`. Use `_ = -(Jm ε * (toMK k * X * (toMK k)ᴴ)) := by`. Rewrite using `[mul_neg, neg_mul, ← mul_assoc (toMK k) (Jm ε) X, hf.2.2]`. Simplify using `only [mul_assoc]`.

Rewrite using `[toMK_inv]`. Use `⟨⟨?_, h2⟩, ?_⟩` and prove the remaining obligations. Unfold `inG`. Rewrite using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, isHermitian_of_mem_noncompactPart' hX, ← mul_assoc (toMK k) X, h2, neg_add_cancel]`. Establish `h` using `Matrix.exp_conj (toMK k) X hu`.

Rewrite `h` using `[hinv]`. Then use the resulting hypothesis.
-/
theorem inP_conj (k : KG ε) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) :
    inP ε (toMK k * X * toMK k⁻¹) ∧
      NormedSpace.exp (toMK k * X * toMK k⁻¹) = toMK k * NormedSpace.exp X * toMK k⁻¹ := by
  have hf := toMK_facts k
  have hinv : (toMK k)⁻¹ = (toMK k)ᴴ := Matrix.inv_eq_right_inv hf.2.1
  have hu : IsUnit (toMK k) := ⟨⟨toMK k, (toMK k)ᴴ, hf.2.1, hf.1⟩, rfl⟩
  have hcJ : (toMK k)ᴴ * Jm ε = Jm ε * (toMK k)ᴴ := by
    have h := congrArg Matrix.conjTranspose hf.2.2
    simp only [Matrix.conjTranspose_mul, Jm_conjTranspose_eq_self'] at h
    exact h.symm
  have h2 : toMK k * X * (toMK k)ᴴ * Jm ε = -(Jm ε * (toMK k * X * (toMK k)ᴴ)) := by
    calc toMK k * X * (toMK k)ᴴ * Jm ε = toMK k * (X * Jm ε) * (toMK k)ᴴ := by
          rw [mul_assoc _ (toMK k)ᴴ, hcJ]
          simp only [mul_assoc]
      _ = toMK k * (-(Jm ε * X)) * (toMK k)ᴴ := by rw [hX.2]
      _ = -(Jm ε * (toMK k * X * (toMK k)ᴴ)) := by
          rw [mul_neg, neg_mul, ← mul_assoc (toMK k) (Jm ε) X, hf.2.2]
          simp only [mul_assoc]
  rw [toMK_inv]
  refine ⟨⟨?_, h2⟩, ?_⟩
  · unfold inG
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      isHermitian_of_mem_noncompactPart' hX, ← mul_assoc (toMK k) X, h2, neg_add_cancel]
  · have h := Matrix.exp_conj (toMK k) X hu
    rwa [hinv] at h

/- English proof (translation)
Establish `hH : Xᴴ = X` using `isHermitian_of_mem_noncompactPart' hX`. Establish `hYH : ((1 / 2 : ℂ) • X)ᴴ = (1 / 2 : ℂ) • X`. Rewrite using `[Matrix.conjTranspose_smul, hH]`. Evaluate the numerical expressions. Establish `hsplit : NormedSpace.exp X = (NormedSpace.exp ((1 / 2 : ℂ) • X))ᴴ * NormedSpace.exp ((1 / 2 : ℂ) • X)`.

Rewrite using `[← Matrix.exp_conjTranspose, hYH, ← Matrix.exp_add_of_commute _ _ (Commute.refl _), ← add_smul]`. Evaluate the numerical expressions. Rewrite using `[hsplit]`. Apply `Matrix.PosDef.conjTranspose_mul_self` to reduce the goal to its premises. Conclude with `Matrix.mulVec_injective_iff_isUnit.2 (Matrix.isUnit_exp _)`.
-/
theorem exp_noncompactPart_posDef {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) : (NormedSpace.exp X).PosDef := by
  have hH : Xᴴ = X := isHermitian_of_mem_noncompactPart' hX
  have hYH : ((1 / 2 : ℂ) • X)ᴴ = (1 / 2 : ℂ) • X := by
    rw [Matrix.conjTranspose_smul, hH]
    norm_num
  have hsplit : NormedSpace.exp X =
      (NormedSpace.exp ((1 / 2 : ℂ) • X))ᴴ * NormedSpace.exp ((1 / 2 : ℂ) • X) := by
    rw [← Matrix.exp_conjTranspose, hYH, ← Matrix.exp_add_of_commute _ _ (Commute.refl _), ← add_smul]
    norm_num
  rw [hsplit]
  apply Matrix.PosDef.conjTranspose_mul_self
  exact Matrix.mulVec_injective_iff_isUnit.2 (Matrix.isUnit_exp _)

end ReciprocityTheory.ChartRestriction.DS.S7
