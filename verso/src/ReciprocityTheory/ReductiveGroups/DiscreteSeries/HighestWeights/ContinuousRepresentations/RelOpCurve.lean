import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.DerivExistsAllPosStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.HasDerivAtRealOfComplex

noncomputable section

open Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

/- English proof (translation)
Establish `hmul : ∀ a b : KG ε, toMK (a * b) = toMK a * toMK b` using `fun a b => rfl`. Establish `hinj : ∀ a b : KG ε, toMK a = toMK b → a = b` using `fun a b h => Subtype.ext (Subtype.ext (Units.ext h))`. Establish `hexp : ∀ s u : ℝ, NormedSpace.exp (((s + u : ℝ) : ℂ) • X) = NormedSpace.exp ((s : ℂ) • X) * NormedSpace.exp ((u : ℂ) • X)`. Introduce `s u`. Rewrite using `[Complex.ofReal_add, add_smul]`.

Conclude with `Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _)`. Establish `hγadd : ∀ s u : ℝ, γ (s + u) = γ s * γ u` using `fun s u => hinj _ _ (by rw [hmul, hγ, hγ, hγ, hexp])`. Establish `hγ0 : γ 0 = 1` using `hinj _ _ (by rw [hγ, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero]; rfl)`. Establish `hop_mul : ∀ a b : KG ε, R.op (a * b) = R.op a * R.op b`. Introduce `a b`.

Simplify using `[KRep.op, map_mul]`. Establish `hop_one : R.op 1 = 1` using `by simp [KRep.op]`. Use `set A := R.dτ X with hA`. Establish `hd0 : HasDerivAt (fun s => R.op (γ s)) A 0` using `R.hasDeriv X hX γ hγ`. Establish `hd : ∀ s : ℝ, HasDerivAt (fun u => R.op (γ u)) (R.op (γ s) * A) s`.

Introduce `s`. Establish `h1 : HasDerivAt (fun u => R.op (γ s) * R.op (γ u)) (R.op (γ s) * A) (s - s)`. Rewrite using `[sub_self]`. Conclude with `hd0.const_mul _`. Use `(h1.comp_sub_const s s).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations.

Use `show R.op (γ x) = R.op (γ s) * R.op (γ (x - s))`. Rewrite using `[← hop_mul, ← hγadd]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Establish `hE : ∀ s : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp ((u : ℂ) • (-A))) (NormedSpace.exp ((s : ℂ) • (-A)) * (-A)) s`.

Introduce `s`. Use `first`. Consider the case `exact (hasDerivAt_exp_smul_const (𝕂 := ℂ) (-A) (s : ℂ)).comp_ofReal`. Consider the case `exact HasDerivAt.comp_ofReal (e := fun u : ℂ => NormedSpace.exp (u • (-A))) (hasDerivAt_exp_smul_const (-A) (s : ℂ))`. Consider the case `(simp only [← Complex.coe_smul]; exact hasDerivAt_exp_smul_const (𝕂 := ℝ) (-A) s)`.

Consider the case `(simp only [Complex.coe_smul]; exact hasDerivAt_exp_smul_const (𝕂 := ℝ) (-A) s)`. Establish `hcomm : ∀ s : ℝ, A * NormedSpace.exp ((s : ℂ) • (-A)) = NormedSpace.exp ((s : ℂ) • (-A)) * A` using `fun s => (((Commute.refl A).neg_right.smul_right (s : ℂ)).exp_right).eq`. Establish `hg : ∀ s : ℝ, HasDerivAt (fun u => R.op (γ u) * NormedSpace.exp ((u : ℂ) • (-A))) 0 s`. Introduce `s`. Establish `h` using `(hd s).mul (hE s)`.

Use `h.congr_deriv ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, hcomm, mul_neg, mul_neg, add_neg_cancel]`. Establish `hconst` using `is_const_of_deriv_eq_zero (fun s => (hg s).differentiableAt) (fun s => (hg s).deriv)`. Establish `hg0 : R.op (γ 0) * NormedSpace.exp (((0 : ℝ) : ℂ) • (-A)) = 1`. Rewrite using `[hγ0, hop_one, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, one_mul]`.

Establish `hEE : NormedSpace.exp ((t : ℂ) • (-A)) * NormedSpace.exp ((t : ℂ) • A) = 1`. Use `letI : NormedAlgebra ℚ (R.V →L[ℂ] R.V) := by first`. Consider the case `exact NormedAlgebra.restrictScalars ℚ ℂ _`. Consider the case `exact NormedAlgebra.restrictScalars ℚ ℝ _`. Rewrite using `[← NormedSpace.exp_add_of_commute ((Commute.refl A).neg_left.smul_left _ |>.smul_right _), smul_neg, neg_add_cancel, NormedSpace.exp_zero]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hEE, mul_one]`. Use `_ = (R.op (γ t) * NormedSpace.exp ((t : ℂ) • (-A))) * NormedSpace.exp ((t : ℂ) • A) := by`. Rewrite using `[mul_assoc]`. Use `_ = NormedSpace.exp ((t : ℂ) • A) := by`.

Rewrite using `[hconst t 0, hg0, one_mul]`.
-/
private theorem KRep.rel_op_curve {ε : Fin n → Bool} (R : KRep ε)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) (t : ℝ) :
    R.op (γ t) = NormedSpace.exp ((t : ℂ) • R.dτ X) := by
  have hmul : ∀ a b : KG ε, toMK (a * b) = toMK a * toMK b := fun a b => rfl
  have hinj : ∀ a b : KG ε, toMK a = toMK b → a = b := fun a b h =>
    Subtype.ext (Subtype.ext (Units.ext h))
  have hexp : ∀ s u : ℝ, NormedSpace.exp (((s + u : ℝ) : ℂ) • X) =
      NormedSpace.exp ((s : ℂ) • X) * NormedSpace.exp ((u : ℂ) • X) := by
    intro s u
    rw [Complex.ofReal_add, add_smul]
    exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _)
  have hγadd : ∀ s u : ℝ, γ (s + u) = γ s * γ u := fun s u =>
    hinj _ _ (by rw [hmul, hγ, hγ, hγ, hexp])
  have hγ0 : γ 0 = 1 := hinj _ _ (by rw [hγ, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero]; rfl)
  have hop_mul : ∀ a b : KG ε, R.op (a * b) = R.op a * R.op b := by
    intro a b; simp [KRep.op, map_mul]
  have hop_one : R.op 1 = 1 := by simp [KRep.op]
  set A := R.dτ X with hA
  have hd0 : HasDerivAt (fun s => R.op (γ s)) A 0 := R.hasDeriv X hX γ hγ
  have hd : ∀ s : ℝ, HasDerivAt (fun u => R.op (γ u)) (R.op (γ s) * A) s := by
    intro s
    have h1 : HasDerivAt (fun u => R.op (γ s) * R.op (γ u)) (R.op (γ s) * A) (s - s) := by
      rw [sub_self]; exact hd0.const_mul _
    refine (h1.comp_sub_const s s).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
    show R.op (γ x) = R.op (γ s) * R.op (γ (x - s))
    rw [← hop_mul, ← hγadd]
    congr 2
    ring
  have hE : ∀ s : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp ((u : ℂ) • (-A)))
      (NormedSpace.exp ((s : ℂ) • (-A)) * (-A)) s := by
    intro s
    first
      | exact (hasDerivAt_exp_smul_const (𝕂 := ℂ) (-A) (s : ℂ)).comp_ofReal
      | exact HasDerivAt.comp_ofReal (e := fun u : ℂ => NormedSpace.exp (u • (-A)))
          (hasDerivAt_exp_smul_const (-A) (s : ℂ))
      | (simp only [← Complex.coe_smul]; exact hasDerivAt_exp_smul_const (𝕂 := ℝ) (-A) s)
      | (simp only [Complex.coe_smul]; exact hasDerivAt_exp_smul_const (𝕂 := ℝ) (-A) s)
  have hcomm : ∀ s : ℝ, A * NormedSpace.exp ((s : ℂ) • (-A)) = NormedSpace.exp ((s : ℂ) • (-A)) * A :=
    fun s => (((Commute.refl A).neg_right.smul_right (s : ℂ)).exp_right).eq
  have hg : ∀ s : ℝ, HasDerivAt (fun u => R.op (γ u) * NormedSpace.exp ((u : ℂ) • (-A))) 0 s := by
    intro s
    have h := (hd s).mul (hE s)
    refine h.congr_deriv ?_
    rw [mul_assoc, hcomm, mul_neg, mul_neg, add_neg_cancel]
  have hconst := is_const_of_deriv_eq_zero (fun s => (hg s).differentiableAt) (fun s => (hg s).deriv)
  have hg0 : R.op (γ 0) * NormedSpace.exp (((0 : ℝ) : ℂ) • (-A)) = 1 := by
    rw [hγ0, hop_one, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, one_mul]
  have hEE : NormedSpace.exp ((t : ℂ) • (-A)) * NormedSpace.exp ((t : ℂ) • A) = 1 := by
    letI : NormedAlgebra ℚ (R.V →L[ℂ] R.V) := by
      first
        | exact NormedAlgebra.restrictScalars ℚ ℂ _
        | exact NormedAlgebra.restrictScalars ℚ ℝ _
    rw [← NormedSpace.exp_add_of_commute ((Commute.refl A).neg_left.smul_left _ |>.smul_right _),
      smul_neg, neg_add_cancel, NormedSpace.exp_zero]
  calc R.op (γ t) = R.op (γ t) * (NormedSpace.exp ((t : ℂ) • (-A)) * NormedSpace.exp ((t : ℂ) • A)) := by
        rw [hEE, mul_one]
    _ = (R.op (γ t) * NormedSpace.exp ((t : ℂ) • (-A))) * NormedSpace.exp ((t : ℂ) • A) := by
        rw [mul_assoc]
    _ = NormedSpace.exp ((t : ℂ) • A) := by
        rw [hconst t 0, hg0, one_mul]

/- English proof (translation)
Use `show ((R.τ k⁻¹ : unitary (R.V →L[ℂ] R.V)) : R.V →L[ℂ] R.V) = star ((R.τ k : unitary (R.V →L[ℂ] R.V)) : R.V →L[ℂ] R.V)`. Rewrite using `[map_inv]`. Use `first`. Consider the case `rfl`. Consider the case `simp [Unitary.coe_star]`.

Consider the case `simp [Unitary.coe_inv]`.
-/
private theorem KRep.rel_op_inv {ε : Fin n → Bool} (R : KRep ε) (k : KG ε) :
    R.op k⁻¹ = star (R.op k) := by
  show ((R.τ k⁻¹ : unitary (R.V →L[ℂ] R.V)) : R.V →L[ℂ] R.V) = star ((R.τ k : unitary (R.V →L[ℂ] R.V)) : R.V →L[ℂ] R.V)
  rw [map_inv]
  first
    | rfl
    | simp [Unitary.coe_star]
    | simp [Unitary.coe_inv]

/- English proof (translation)
Take `⟨hG, hJ⟩` from `hX`. Establish `hJJ : Jm ε * Jm ε = 1`. Rewrite using `[Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Apply the tactic sequence `split_ifs <;> norm_num`. Establish `hskew : Xᴴ = -X`. Establish `h1 : Xᴴ * Jm ε = -(X * Jm ε)` using `by rw [hJ]; exact eq_neg_of_add_eq_zero_left hG`. Combine the equalities or inequalities in the displayed calculation. Establish `hE : ∀ t : ℝ, (NormedSpace.exp ((t : ℂ) • X))ᴴ = NormedSpace.exp ((t : ℂ) • (-X))`.

Introduce `t`. Rewrite using `[← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hskew, Complex.star_def, Complex.conj_ofReal]`. Establish `hinv1 : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • (-X)) * NormedSpace.exp ((t : ℂ) • X) = 1`. Introduce `t`. Rewrite using `[← Matrix.exp_add_of_commute _ _ (((Commute.refl X).neg_left.smul_left _).smul_right _), smul_neg, neg_add_cancel, NormedSpace.exp_zero]`.

Establish `hinv2 : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((t : ℂ) • (-X)) = 1`. Introduce `t`. Rewrite using `[← Matrix.exp_add_of_commute _ _ (((Commute.refl X).neg_right.smul_left _).smul_right _), smul_neg, add_neg_cancel, NormedSpace.exp_zero]`. Establish `hcJ : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) * Jm ε = Jm ε * NormedSpace.exp ((t : ℂ) • X)`. Introduce `t`.

Establish `hJi : (Jm ε)⁻¹ = Jm ε` using `Matrix.inv_eq_right_inv hJJ`. Establish `hJu : IsUnit (Jm ε)` using `⟨⟨Jm ε, Jm ε, hJJ, hJJ⟩, rfl⟩`. Establish `hXc : Jm ε * ((t : ℂ) • X) * (Jm ε)⁻¹ = (t : ℂ) • X`. Rewrite using `[hJi, Matrix.mul_smul, Matrix.smul_mul, ← hJ, Matrix.mul_assoc, hJJ, Matrix.mul_one]`. Establish `h` using `Matrix.exp_conj (Jm ε) ((t : ℂ) • X) hJu`.

Rewrite `h` using `[hXc, hJi]`. Combine the equalities or inequalities in the displayed calculation. Set `u : ℝ → (Matrix (Fin n) (Fin n) ℂ)ˣ` to `fun t => ⟨NormedSpace.exp ((t : ℂ) • X), NormedSpace.exp ((t : ℂ) • (-X)), hinv2 t, hinv1 t⟩`. Establish `hU : ∀ t : ℝ, u t ∈ UJ ε`. Introduce `t`.

Use `show (NormedSpace.exp ((t : ℂ) • X))ᴴ * Jm ε * NormedSpace.exp ((t : ℂ) • X) = Jm ε`. Rewrite using `[Matrix.mul_assoc, ← hcJ, ← Matrix.mul_assoc, hE, hinv1, Matrix.one_mul]`. Establish `hK : ∀ t : ℝ, (⟨u t, hU t⟩ : UJ ε) ∈ KG ε`. Introduce `t`. Use `⟨?_, hcJ t⟩` and prove the remaining obligations.

Rewrite using `[Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]`. Use `show NormedSpace.exp ((t : ℂ) • X) * (NormedSpace.exp ((t : ℂ) • X))ᴴ = 1`. Rewrite using `[hE, hinv2]`. Conclude with `⟨fun t => ⟨⟨u t, hU t⟩, hK t⟩, fun t => rfl⟩`.
-/
private theorem exists_curve_toMK_eq_exp_smul_of_inK {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) :
    ∃ γ : ℝ → KG ε, ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X) := by
  obtain ⟨hG, hJ⟩ := hX
  have hJJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hskew : Xᴴ = -X := by
    have h1 : Xᴴ * Jm ε = -(X * Jm ε) := by rw [hJ]; exact eq_neg_of_add_eq_zero_left hG
    calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = -X := by rw [h1, Matrix.neg_mul, Matrix.mul_assoc, hJJ, Matrix.mul_one]
  have hE : ∀ t : ℝ, (NormedSpace.exp ((t : ℂ) • X))ᴴ = NormedSpace.exp ((t : ℂ) • (-X)) := by
    intro t
    rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hskew, Complex.star_def, Complex.conj_ofReal]
  have hinv1 : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • (-X)) * NormedSpace.exp ((t : ℂ) • X) = 1 := by
    intro t
    rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl X).neg_left.smul_left _).smul_right _),
      smul_neg, neg_add_cancel, NormedSpace.exp_zero]
  have hinv2 : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((t : ℂ) • (-X)) = 1 := by
    intro t
    rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl X).neg_right.smul_left _).smul_right _),
      smul_neg, add_neg_cancel, NormedSpace.exp_zero]
  have hcJ : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) * Jm ε = Jm ε * NormedSpace.exp ((t : ℂ) • X) := by
    intro t
    have hJi : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_right_inv hJJ
    have hJu : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, hJJ, hJJ⟩, rfl⟩
    have hXc : Jm ε * ((t : ℂ) • X) * (Jm ε)⁻¹ = (t : ℂ) • X := by
      rw [hJi, Matrix.mul_smul, Matrix.smul_mul, ← hJ, Matrix.mul_assoc, hJJ, Matrix.mul_one]
    have h := Matrix.exp_conj (Jm ε) ((t : ℂ) • X) hJu
    rw [hXc, hJi] at h
    calc NormedSpace.exp ((t : ℂ) • X) * Jm ε
        = Jm ε * NormedSpace.exp ((t : ℂ) • X) * Jm ε * Jm ε := by rw [← h]
      _ = Jm ε * NormedSpace.exp ((t : ℂ) • X) := by rw [Matrix.mul_assoc _ (Jm ε), hJJ, Matrix.mul_one]
  let u : ℝ → (Matrix (Fin n) (Fin n) ℂ)ˣ := fun t =>
    ⟨NormedSpace.exp ((t : ℂ) • X), NormedSpace.exp ((t : ℂ) • (-X)), hinv2 t, hinv1 t⟩
  have hU : ∀ t : ℝ, u t ∈ UJ ε := by
    intro t
    show (NormedSpace.exp ((t : ℂ) • X))ᴴ * Jm ε * NormedSpace.exp ((t : ℂ) • X) = Jm ε
    rw [Matrix.mul_assoc, ← hcJ, ← Matrix.mul_assoc, hE, hinv1, Matrix.one_mul]
  have hK : ∀ t : ℝ, (⟨u t, hU t⟩ : UJ ε) ∈ KG ε := by
    intro t
    refine ⟨?_, hcJ t⟩
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    show NormedSpace.exp ((t : ℂ) • X) * (NormedSpace.exp ((t : ℂ) • X))ᴴ = 1
    rw [hE, hinv2]
  exact ⟨fun t => ⟨⟨u t, hU t⟩, hK t⟩, fun t => rfl⟩

/- English proof (translation)
Take `⟨γ, hγ⟩` from `exists_curve_toMK_eq_exp_smul_of_inK hX`. Use `set A := R.dτ X with hA`. Establish `hf : ∀ s : ℝ, R.op (γ s) = NormedSpace.exp ((s : ℂ) • A)` using `R.rel_op_curve hX γ hγ`. Establish `hEE : ∀ s : ℝ, NormedSpace.exp ((s : ℂ) • (-A)) * NormedSpace.exp ((s : ℂ) • A) = 1`. Introduce `s`.

Use `letI : NormedAlgebra ℚ (R.V →L[ℂ] R.V) := by first`. Consider the case `exact NormedAlgebra.restrictScalars ℚ ℂ _`. Consider the case `exact NormedAlgebra.restrictScalars ℚ ℝ _`. Rewrite using `[← NormedSpace.exp_add_of_commute ((Commute.refl A).neg_left.smul_left _ |>.smul_right _), smul_neg, neg_add_cancel, NormedSpace.exp_zero]`. Establish `hU : ∀ s : ℝ, R.op (γ s) * star (R.op (γ s)) = 1` using `fun s => (R.τ (γ s)).2.2`.

Establish `hstar : ∀ s : ℝ, star (NormedSpace.exp ((s : ℂ) • A)) = NormedSpace.exp ((s : ℂ) • (-A))`. Introduce `s`. Combine the equalities or inequalities in the displayed calculation. Establish `hfun : (fun s : ℝ => NormedSpace.exp ((s : ℂ) • star A)) = fun s : ℝ => NormedSpace.exp ((s : ℂ) • (-A))`. Use function extensionality and compare the values at `s`.

Rewrite using `[← hstar]`. Use `first`. Consider the case `rw [NormedSpace.star_exp, star_smul, Complex.star_def, Complex.conj_ofReal]`. Consider the case `rw [← NormedSpace.exp_star, star_smul, Complex.star_def, Complex.conj_ofReal]`. Consider the case `rw [star_exp, star_smul, Complex.star_def, Complex.conj_ofReal]`.

Establish `d1 : HasDerivAt (fun s : ℝ => NormedSpace.exp ((s : ℂ) • star A)) (NormedSpace.exp (((0 : ℝ) : ℂ) • star A) * star A) 0` using `by first`. Consider the case `exact (hasDerivAt_exp_smul_const (𝕂 := ℂ) (star A) ((0 : ℝ) : ℂ)).comp_ofReal`. Consider the case `(simp only [← Complex.coe_smul]; exact hasDerivAt_exp_smul_const (𝕂 := ℝ) (star A) (0 : ℝ))`. Consider the case `(simp only [Complex.coe_smul]; exact hasDerivAt_exp_smul_const (𝕂 := ℝ) (star A) (0 : ℝ))`. Establish `d2 : HasDerivAt (fun s : ℝ => NormedSpace.exp ((s : ℂ) • (-A))) (NormedSpace.exp (((0 : ℝ) : ℂ) • (-A)) * (-A)) 0` using `by first`.

Consider the case `exact (hasDerivAt_exp_smul_const (𝕂 := ℂ) (-A) ((0 : ℝ) : ℂ)).comp_ofReal`. Consider the case `(simp only [← Complex.coe_smul]; exact hasDerivAt_exp_smul_const (𝕂 := ℝ) (-A) (0 : ℝ))`. Consider the case `(simp only [Complex.coe_smul]; exact hasDerivAt_exp_smul_const (𝕂 := ℝ) (-A) (0 : ℝ))`. Rewrite `d1` using `[hfun]`. Establish `h` using `d1.unique d2`.

Simplify using `using h`.
-/
private theorem KRep.rel_star_dτ {ε : Fin n → Bool} (R : KRep ε)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) : star (R.dτ X) = -R.dτ X := by
  obtain ⟨γ, hγ⟩ := exists_curve_toMK_eq_exp_smul_of_inK hX
  set A := R.dτ X with hA
  have hf : ∀ s : ℝ, R.op (γ s) = NormedSpace.exp ((s : ℂ) • A) := R.rel_op_curve hX γ hγ
  have hEE : ∀ s : ℝ, NormedSpace.exp ((s : ℂ) • (-A)) * NormedSpace.exp ((s : ℂ) • A) = 1 := by
    intro s
    letI : NormedAlgebra ℚ (R.V →L[ℂ] R.V) := by
      first
        | exact NormedAlgebra.restrictScalars ℚ ℂ _
        | exact NormedAlgebra.restrictScalars ℚ ℝ _
    rw [← NormedSpace.exp_add_of_commute ((Commute.refl A).neg_left.smul_left _ |>.smul_right _),
      smul_neg, neg_add_cancel, NormedSpace.exp_zero]
  have hU : ∀ s : ℝ, R.op (γ s) * star (R.op (γ s)) = 1 := fun s => (R.τ (γ s)).2.2
  have hstar : ∀ s : ℝ, star (NormedSpace.exp ((s : ℂ) • A)) = NormedSpace.exp ((s : ℂ) • (-A)) := by
    intro s
    calc star (NormedSpace.exp ((s : ℂ) • A))
        = (NormedSpace.exp ((s : ℂ) • (-A)) * NormedSpace.exp ((s : ℂ) • A)) *
            star (NormedSpace.exp ((s : ℂ) • A)) := by rw [hEE, one_mul]
      _ = NormedSpace.exp ((s : ℂ) • (-A)) := by rw [mul_assoc, ← hf, hU, mul_one]
  have hfun : (fun s : ℝ => NormedSpace.exp ((s : ℂ) • star A)) =
      fun s : ℝ => NormedSpace.exp ((s : ℂ) • (-A)) := by
    funext s
    rw [← hstar]
    first
      | rw [NormedSpace.star_exp, star_smul, Complex.star_def, Complex.conj_ofReal]
      | rw [← NormedSpace.exp_star, star_smul, Complex.star_def, Complex.conj_ofReal]
      | rw [star_exp, star_smul, Complex.star_def, Complex.conj_ofReal]
  have d1 : HasDerivAt (fun s : ℝ => NormedSpace.exp ((s : ℂ) • star A))
      (NormedSpace.exp (((0 : ℝ) : ℂ) • star A) * star A) 0 := by
    first
      | exact (hasDerivAt_exp_smul_const (𝕂 := ℂ) (star A) ((0 : ℝ) : ℂ)).comp_ofReal
      | (simp only [← Complex.coe_smul]; exact hasDerivAt_exp_smul_const (𝕂 := ℝ) (star A) (0 : ℝ))
      | (simp only [Complex.coe_smul]; exact hasDerivAt_exp_smul_const (𝕂 := ℝ) (star A) (0 : ℝ))
  have d2 : HasDerivAt (fun s : ℝ => NormedSpace.exp ((s : ℂ) • (-A)))
      (NormedSpace.exp (((0 : ℝ) : ℂ) • (-A)) * (-A)) 0 := by
    first
      | exact (hasDerivAt_exp_smul_const (𝕂 := ℂ) (-A) ((0 : ℝ) : ℂ)).comp_ofReal
      | (simp only [← Complex.coe_smul]; exact hasDerivAt_exp_smul_const (𝕂 := ℝ) (-A) (0 : ℝ))
      | (simp only [Complex.coe_smul]; exact hasDerivAt_exp_smul_const (𝕂 := ℝ) (-A) (0 : ℝ))
  rw [hfun] at d1
  have h := d1.unique d2
  simpa using h

/- English proof (translation)
Take `⟨γ, hγ⟩` from `exists_curve_toMK_eq_exp_smul_of_inK hY`. Establish `hmul : ∀ a b : KG ε, toMK (a * b) = toMK a * toMK b` using `fun a b => rfl`. Establish `hone : toMK (1 : KG ε) = 1` using `rfl`. Establish `hop_mul : ∀ a b : KG ε, R.op (a * b) = R.op a * R.op b`. Introduce `a b`.

Simplify using `[KRep.op, map_mul]`. Establish `hopinv : R.op k⁻¹ = star (R.op k)` using `by show ((R.τ k⁻¹ : unitary (R.V →L[ℂ] R.V)) : R.V →L[ℂ] R.V) = star ((R.τ k : unitary _) : R.V →L[ℂ] R.V)`. Rewrite using `[map_inv]`. Both sides reduce to the same expression. Use `set K := toMK k with hKdef`.

Establish `hkK : K ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ K * Jm ε = Jm ε * K` using `k.2`. Establish `hKs : star K * K = 1` using `(Matrix.mem_unitaryGroup_iff').mp hkK.1`. Establish `hKs' : K * star K = 1` using `(Matrix.mem_unitaryGroup_iff).mp hkK.1`. Establish `hkinv : toMK k⁻¹ = star K`. Establish `h1 : K * toMK k⁻¹ = 1` using `by rw [hKdef, ← hmul, mul_inv_cancel, hone]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hJh : (Jm ε)ᴴ = Jm ε`. Rewrite using `[Jm, Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Apply the tactic sequence `split_ifs with h <;> simp [h]`. Establish `hJs : star K * Jm ε = Jm ε * star K`. Establish `h` using `congrArg Matrix.conjTranspose hkK.2`. Rewrite `h` using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJh]`. Rewrite using `[Matrix.star_eq_conjTranspose]`.

Conclude with `h.symm`. Use `set Z := K * Y * star K with hZ`. Establish `hZK : inK ε Z`. Take `⟨hG, hJ⟩` from `hY`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Unfold `inG at hG ⊢`. Establish `hZh : Zᴴ = K * Yᴴ * star K`. Rewrite using `[hZ, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]`. Establish `e1 : K * Yᴴ * star K * Jm ε = K * (Yᴴ * Jm ε) * star K`. Simplify using `only [Matrix.mul_assoc, hJs]`.

Establish `e2 : Jm ε * (K * Y * star K) = K * (Jm ε * Y) * star K`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hkK.2]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[hZh, e1, e2, ← Matrix.add_mul, ← Matrix.mul_add, hG, Matrix.mul_zero, Matrix.zero_mul]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hKi : K⁻¹ = star K` using `Matrix.inv_eq_right_inv hKs'`. Establish `hKu : IsUnit K` using `⟨⟨K, star K, hKs', hKs⟩, rfl⟩`. Establish `hδ : ∀ t : ℝ, toMK (k * γ t * k⁻¹) = NormedSpace.exp ((t : ℂ) • Z)`. Introduce `t`. Establish `h` using `Matrix.exp_conj K ((t : ℂ) • Y) hKu`.

Rewrite `h` using `[hKi]`. Rewrite using `[hmul, hmul, hγ, hkinv, ← hKdef, ← h, hZ, Matrix.mul_smul, Matrix.smul_mul]`. Establish `hd1 : HasDerivAt (fun t => R.op (k * γ t * k⁻¹)) (R.dτ Z) 0` using `R.hasDeriv Z hZK _ hδ`. Establish `hd2 : HasDerivAt (fun t => R.op (k * γ t * k⁻¹)) (R.op k * R.dτ Y * R.op k⁻¹) 0`. Establish `h` using `((R.hasDeriv Y hY γ hγ).const_mul (R.op k)).mul_const (R.op k⁻¹)`.

Use `h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Use `show R.op (k * γ t * k⁻¹) = R.op k * R.op (γ t) * R.op k⁻¹`. Rewrite using `[hop_mul, hop_mul]`. Rewrite using `[← hopinv]`. Conclude with `hd2.unique hd1`.
-/
private theorem KRep.rel_conj_dτ {ε : Fin n → Bool} (R : KRep ε) (k : KG ε)
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) :
    R.op k * R.dτ Y * star (R.op k) = R.dτ (toMK k * Y * star (toMK k)) := by
  obtain ⟨γ, hγ⟩ := exists_curve_toMK_eq_exp_smul_of_inK hY
  have hmul : ∀ a b : KG ε, toMK (a * b) = toMK a * toMK b := fun a b => rfl
  have hone : toMK (1 : KG ε) = 1 := rfl
  have hop_mul : ∀ a b : KG ε, R.op (a * b) = R.op a * R.op b := by
    intro a b; simp [KRep.op, map_mul]
  have hopinv : R.op k⁻¹ = star (R.op k) := by
    show ((R.τ k⁻¹ : unitary (R.V →L[ℂ] R.V)) : R.V →L[ℂ] R.V) = star ((R.τ k : unitary _) : R.V →L[ℂ] R.V)
    rw [map_inv]
    rfl
  set K := toMK k with hKdef
  have hkK : K ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ K * Jm ε = Jm ε * K := k.2
  have hKs : star K * K = 1 := (Matrix.mem_unitaryGroup_iff').mp hkK.1
  have hKs' : K * star K = 1 := (Matrix.mem_unitaryGroup_iff).mp hkK.1
  have hkinv : toMK k⁻¹ = star K := by
    have h1 : K * toMK k⁻¹ = 1 := by rw [hKdef, ← hmul, mul_inv_cancel, hone]
    calc toMK k⁻¹ = (star K * K) * toMK k⁻¹ := by rw [hKs, Matrix.one_mul]
      _ = star K := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have hJh : (Jm ε)ᴴ = Jm ε := by
    rw [Jm, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    split_ifs with h <;> simp [h]
  have hJs : star K * Jm ε = Jm ε * star K := by
    have h := congrArg Matrix.conjTranspose hkK.2
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJh] at h
    rw [Matrix.star_eq_conjTranspose]
    exact h.symm
  set Z := K * Y * star K with hZ
  have hZK : inK ε Z := by
    obtain ⟨hG, hJ⟩ := hY
    refine ⟨?_, ?_⟩
    · unfold inG at hG ⊢
      have hZh : Zᴴ = K * Yᴴ * star K := by
        rw [hZ, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose,
          Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      have e1 : K * Yᴴ * star K * Jm ε = K * (Yᴴ * Jm ε) * star K := by
        simp only [Matrix.mul_assoc, hJs]
      have e2 : Jm ε * (K * Y * star K) = K * (Jm ε * Y) * star K := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hkK.2]
        simp only [Matrix.mul_assoc]
      rw [hZh, e1, e2, ← Matrix.add_mul, ← Matrix.mul_add, hG, Matrix.mul_zero, Matrix.zero_mul]
    · calc Z * Jm ε = K * (Y * Jm ε) * star K := by simp only [hZ, Matrix.mul_assoc, hJs]
        _ = K * (Jm ε * Y) * star K := by rw [hJ]
        _ = Jm ε * Z := by rw [hZ]; simp only [← Matrix.mul_assoc, hkK.2]
  have hKi : K⁻¹ = star K := Matrix.inv_eq_right_inv hKs'
  have hKu : IsUnit K := ⟨⟨K, star K, hKs', hKs⟩, rfl⟩
  have hδ : ∀ t : ℝ, toMK (k * γ t * k⁻¹) = NormedSpace.exp ((t : ℂ) • Z) := by
    intro t
    have h := Matrix.exp_conj K ((t : ℂ) • Y) hKu
    rw [hKi] at h
    rw [hmul, hmul, hγ, hkinv, ← hKdef, ← h, hZ, Matrix.mul_smul, Matrix.smul_mul]
  have hd1 : HasDerivAt (fun t => R.op (k * γ t * k⁻¹)) (R.dτ Z) 0 := R.hasDeriv Z hZK _ hδ
  have hd2 : HasDerivAt (fun t => R.op (k * γ t * k⁻¹)) (R.op k * R.dτ Y * R.op k⁻¹) 0 := by
    have h := ((R.hasDeriv Y hY γ hγ).const_mul (R.op k)).mul_const (R.op k⁻¹)
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    show R.op (k * γ t * k⁻¹) = R.op k * R.op (γ t) * R.op k⁻¹
    rw [hop_mul, hop_mul]
  rw [← hopinv]
  exact hd2.unique hd1

section MatDeriv

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/- English proof (translation)
Set `L : Matrix (Fin n) (Fin n) ℂ →L[ℂ] (R.V →L[ℂ] R.V)` to `LinearMap.toContinuousLinearMap R.dτ`. Establish `he : ∀ Z : Matrix (Fin n) (Fin n) ℂ, HasDerivAt (fun y : ℝ => NormedSpace.exp ((y : ℂ) • Z)) (NormedSpace.exp (((0 : ℝ) : ℂ) • Z) * Z) 0`. Introduce `Z`. Use `first`. Consider the case `exact (hasDerivAt_exp_smul_const (𝕂 := ℂ) Z ((0 : ℝ) : ℂ)).comp_ofReal`.

Consider the case `(simp only [← Complex.coe_smul]; exact hasDerivAt_exp_smul_const (𝕂 := ℝ) Z 0)`. Consider the case `(simp only [Complex.coe_smul]; exact hasDerivAt_exp_smul_const (𝕂 := ℝ) Z 0)`. Establish `hf : HasDerivAt (fun y : ℝ => NormedSpace.exp ((y : ℂ) • X) * Y * NormedSpace.exp ((y : ℂ) • (-X))) (X * Y - Y * X) 0`. Establish `h` using `((he X).mul_const Y).mul (he (-X))`. Use `h.congr_deriv ?_` and prove the remaining obligations.

Simplify using `only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, one_mul, mul_one, mul_neg]`. Normalize the expressions using the abelian group laws. Establish `hL` using `(L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hf`. Conclude with `hL`.
-/
private theorem KRep.rel_dτ_conj_hasDerivAt {ε : Fin n → Bool} (R : KRep ε)
    (X Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun y : ℝ => R.dτ (NormedSpace.exp ((y : ℂ) • X) * Y *
      NormedSpace.exp ((y : ℂ) • (-X)))) (R.dτ (X * Y - Y * X)) 0 := by
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℂ] (R.V →L[ℂ] R.V) := LinearMap.toContinuousLinearMap R.dτ
  have he : ∀ Z : Matrix (Fin n) (Fin n) ℂ, HasDerivAt (fun y : ℝ => NormedSpace.exp ((y : ℂ) • Z))
      (NormedSpace.exp (((0 : ℝ) : ℂ) • Z) * Z) 0 := by
    intro Z
    first
      | exact (hasDerivAt_exp_smul_const (𝕂 := ℂ) Z ((0 : ℝ) : ℂ)).comp_ofReal
      | (simp only [← Complex.coe_smul]; exact hasDerivAt_exp_smul_const (𝕂 := ℝ) Z 0)
      | (simp only [Complex.coe_smul]; exact hasDerivAt_exp_smul_const (𝕂 := ℝ) Z 0)
  have hf : HasDerivAt (fun y : ℝ => NormedSpace.exp ((y : ℂ) • X) * Y * NormedSpace.exp ((y : ℂ) • (-X)))
      (X * Y - Y * X) 0 := by
    have h := ((he X).mul_const Y).mul (he (-X))
    refine h.congr_deriv ?_
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, one_mul, mul_one, mul_neg]
    abel
  have hL := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hf
  exact hL

end MatDeriv

/- English proof (translation)
Take `⟨γ, hγ⟩` from `exists_curve_toMK_eq_exp_smul_of_inK hX`. Establish `hJJ : Jm ε * Jm ε = 1`. Rewrite using `[Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Apply the tactic sequence `split_ifs <;> norm_num`. Establish `hskew : Xᴴ = -X`. Take `⟨hG, hJ⟩` from `hX`. Establish `h1 : Xᴴ * Jm ε = -(X * Jm ε)` using `by rw [hJ]; exact eq_neg_of_add_eq_zero_left hG`. Combine the equalities or inequalities in the displayed calculation.

Establish `hstarM : ∀ y : ℝ, star (NormedSpace.exp ((y : ℂ) • X)) = NormedSpace.exp ((y : ℂ) • (-X))`. Introduce `y`. Rewrite using `[Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hskew, Complex.star_def, Complex.conj_ofReal]`. Establish `hsA : star (R.dτ X) = -R.dτ X` using `R.rel_star_dτ hX`. Establish `hstarO : ∀ y : ℝ, star (NormedSpace.exp ((y : ℂ) • R.dτ X)) = NormedSpace.exp ((y : ℂ) • (-R.dτ X))`.

Introduce `y`. Use `first`. Consider the case `rw [NormedSpace.star_exp, star_smul, Complex.star_def, Complex.conj_ofReal, hsA]`. Consider the case `rw [← NormedSpace.exp_star, star_smul, Complex.star_def, Complex.conj_ofReal, hsA]`. Consider the case `rw [star_exp, star_smul, Complex.star_def, Complex.conj_ofReal, hsA]`.

Establish `hG : ∀ y : ℝ, R.dτ (NormedSpace.exp ((y : ℂ) • X) * Y * NormedSpace.exp ((y : ℂ) • (-X))) = NormedSpace.exp ((y : ℂ) • R.dτ X) * R.dτ Y * NormedSpace.exp ((y : ℂ) • (-R.dτ X))`. Introduce `y`. Establish `h` using `R.rel_conj_dτ (γ y) hY`. Rewrite `h` using `[hγ, hstarM, R.rel_op_curve hX γ hγ, hstarO]`. Conclude with `h.symm`.

Establish `he : ∀ Z : R.V →L[ℂ] R.V, HasDerivAt (fun y : ℝ => NormedSpace.exp ((y : ℂ) • Z)) (NormedSpace.exp (((0 : ℝ) : ℂ) • Z) * Z) 0`. Introduce `Z`. Use `first`. Consider the case `exact (hasDerivAt_exp_smul_const (𝕂 := ℂ) Z ((0 : ℝ) : ℂ)).comp_ofReal`. Consider the case `(simp only [← Complex.coe_smul]; exact hasDerivAt_exp_smul_const (𝕂 := ℝ) Z 0)`.

Consider the case `(simp only [Complex.coe_smul]; exact hasDerivAt_exp_smul_const (𝕂 := ℝ) Z 0)`. Establish `hd : HasDerivAt (fun y : ℝ => NormedSpace.exp ((y : ℂ) • R.dτ X) * R.dτ Y * NormedSpace.exp ((y : ℂ) • (-R.dτ X))) (R.dτ X * R.dτ Y - R.dτ Y * R.dτ X) 0`. Establish `h` using `((he (R.dτ X)).mul_const (R.dτ Y)).mul (he (-R.dτ X))`. Use `h.congr_deriv ?_` and prove the remaining obligations. Simplify using `only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, one_mul, mul_one, mul_neg]`.

Normalize the expressions using the abelian group laws. Establish `hd'` using `R.rel_dτ_conj_hasDerivAt X Y`. Establish `hfun : (fun y : ℝ => R.dτ (NormedSpace.exp ((y : ℂ) • X) * Y * NormedSpace.exp ((y : ℂ) • (-X)))) = fun y : ℝ => NormedSpace.exp ((y : ℂ) • R.dτ X) * R.dτ Y * NormedSpace.exp ((y : ℂ) • (-R.dτ X))`. Use function extensionality and compare the values at `hG`. Rewrite `hd'` using `[hfun]`.

Conclude with `hd.unique hd'`.
-/
private theorem KRep.rel_dτ_bracket {ε : Fin n → Bool} (R : KRep ε)
    {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (hY : inK ε Y) :
    R.dτ X * R.dτ Y - R.dτ Y * R.dτ X = R.dτ (X * Y - Y * X) := by
  obtain ⟨γ, hγ⟩ := exists_curve_toMK_eq_exp_smul_of_inK hX
  have hJJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hskew : Xᴴ = -X := by
    obtain ⟨hG, hJ⟩ := hX
    have h1 : Xᴴ * Jm ε = -(X * Jm ε) := by rw [hJ]; exact eq_neg_of_add_eq_zero_left hG
    calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = -X := by rw [h1, Matrix.neg_mul, Matrix.mul_assoc, hJJ, Matrix.mul_one]
  have hstarM : ∀ y : ℝ, star (NormedSpace.exp ((y : ℂ) • X)) = NormedSpace.exp ((y : ℂ) • (-X)) := by
    intro y
    rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hskew,
      Complex.star_def, Complex.conj_ofReal]
  have hsA : star (R.dτ X) = -R.dτ X := R.rel_star_dτ hX
  have hstarO : ∀ y : ℝ, star (NormedSpace.exp ((y : ℂ) • R.dτ X)) =
      NormedSpace.exp ((y : ℂ) • (-R.dτ X)) := by
    intro y
    first
      | rw [NormedSpace.star_exp, star_smul, Complex.star_def, Complex.conj_ofReal, hsA]
      | rw [← NormedSpace.exp_star, star_smul, Complex.star_def, Complex.conj_ofReal, hsA]
      | rw [star_exp, star_smul, Complex.star_def, Complex.conj_ofReal, hsA]
  have hG : ∀ y : ℝ, R.dτ (NormedSpace.exp ((y : ℂ) • X) * Y * NormedSpace.exp ((y : ℂ) • (-X))) =
      NormedSpace.exp ((y : ℂ) • R.dτ X) * R.dτ Y * NormedSpace.exp ((y : ℂ) • (-R.dτ X)) := by
    intro y
    have h := R.rel_conj_dτ (γ y) hY
    rw [hγ, hstarM, R.rel_op_curve hX γ hγ, hstarO] at h
    exact h.symm
  have he : ∀ Z : R.V →L[ℂ] R.V, HasDerivAt (fun y : ℝ => NormedSpace.exp ((y : ℂ) • Z))
      (NormedSpace.exp (((0 : ℝ) : ℂ) • Z) * Z) 0 := by
    intro Z
    first
      | exact (hasDerivAt_exp_smul_const (𝕂 := ℂ) Z ((0 : ℝ) : ℂ)).comp_ofReal
      | (simp only [← Complex.coe_smul]; exact hasDerivAt_exp_smul_const (𝕂 := ℝ) Z 0)
      | (simp only [Complex.coe_smul]; exact hasDerivAt_exp_smul_const (𝕂 := ℝ) Z 0)
  have hd : HasDerivAt (fun y : ℝ => NormedSpace.exp ((y : ℂ) • R.dτ X) * R.dτ Y *
      NormedSpace.exp ((y : ℂ) • (-R.dτ X))) (R.dτ X * R.dτ Y - R.dτ Y * R.dτ X) 0 := by
    have h := ((he (R.dτ X)).mul_const (R.dτ Y)).mul (he (-R.dτ X))
    refine h.congr_deriv ?_
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, one_mul, mul_one, mul_neg]
    abel
  have hd' := R.rel_dτ_conj_hasDerivAt X Y
  have hfun : (fun y : ℝ => R.dτ (NormedSpace.exp ((y : ℂ) • X) * Y * NormedSpace.exp ((y : ℂ) • (-X)))) =
      fun y : ℝ => NormedSpace.exp ((y : ℂ) • R.dτ X) * R.dτ Y * NormedSpace.exp ((y : ℂ) • (-R.dτ X)) :=
    funext hG
  rw [hfun] at hd'
  exact hd.unique hd'

/- English proof (translation)
Establish `hc : X * Jm ε = Jm ε * X`. Use extensionality with `i j`. Simplify using `only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]`. Distinguish the cases in `h : X i j = 0`. Simplify using `[h]`.

Rewrite using `[hX i j h, mul_comm]`. Use `⟨?_, hc⟩` and prove the remaining obligations. Unfold `inG`. Rewrite using `[hs, neg_mul, hc, neg_add_cancel]`.
-/
private theorem inK_of_support_sign_eq_of_skewAdjoint {ε : Fin n → Bool} (X : Matrix (Fin n) (Fin n) ℂ)
    (hX : ∀ i j, X i j ≠ 0 → ε i = ε j) (hs : Xᴴ = -X) : inK ε X := by
  have hc : X * Jm ε = Jm ε * X := by
    ext i j
    simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases h : X i j = 0
    · simp [h]
    · rw [hX i j h, mul_comm]
  refine ⟨?_, hc⟩
  unfold inG
  rw [hs, neg_mul, hc, neg_add_cancel]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Apply `inK_of_support_sign_eq_of_skewAdjoint` to reduce the goal to its premises. Introduce `i j h`. Simplify using `only [Matrix.sub_apply, Matrix.single_apply] at h`. Distinguish the cases in `e1 : a = i ∧ b = j`.

Take `⟨rfl, rfl⟩` from `e1`. Conclude with `hab`. Distinguish the cases in `e2 : b = i ∧ a = j`. Take `⟨rfl, rfl⟩` from `e2`. Conclude with `hab.symm`.

Simplify using `[e1, e2] at h`. Use extensionality with `i j`. Simplify using `only [Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.single_apply, show (a = j ∧ b = i) ↔ (b = i ∧ a = j) from and_comm, show (b = j ∧ a = i) ↔ (a = i ∧ b = j) from and_comm]`. Apply the tactic sequence `by_cases e1 : a = i ∧ b = j <;> by_cases e2 : b = i ∧ a = j <;> simp [e1, e2]`. Apply `inK_of_support_sign_eq_of_skewAdjoint` to reduce the goal to its premises.

Introduce `i j h`. Simplify using `only [Matrix.smul_apply, Matrix.add_apply, Matrix.single_apply] at h`. Distinguish the cases in `e1 : a = i ∧ b = j`. Take `⟨rfl, rfl⟩` from `e1`. Conclude with `hab`.

Distinguish the cases in `e2 : b = i ∧ a = j`. Take `⟨rfl, rfl⟩` from `e2`. Conclude with `hab.symm`. Simplify using `[e1, e2] at h`. Use extensionality with `i j`.

Simplify using `only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.neg_apply, Matrix.single_apply, smul_eq_mul, show (a = j ∧ b = i) ↔ (b = i ∧ a = j) from and_comm, show (b = j ∧ a = i) ↔ (a = i ∧ b = j) from and_comm]`. Apply the tactic sequence `by_cases e1 : a = i ∧ b = j <;> by_cases e2 : b = i ∧ a = j <;>`. Apply the tactic sequence `simp [e1, e2, Complex.conj_I, map_ofNat] <;> ring`.
-/
private theorem inK_single_sub_single_and_I_smul_add_of_sign_eq {ε : Fin n → Bool} {a b : Fin n} (hab : ε a = ε b) :
    inK ε (Matrix.single a b (1 : ℂ) - Matrix.single b a 1) ∧
      inK ε (Complex.I • (Matrix.single a b (1 : ℂ) + Matrix.single b a 1)) := by
  constructor
  · apply inK_of_support_sign_eq_of_skewAdjoint
    · intro i j h
      simp only [Matrix.sub_apply, Matrix.single_apply] at h
      by_cases e1 : a = i ∧ b = j
      · obtain ⟨rfl, rfl⟩ := e1; exact hab
      · by_cases e2 : b = i ∧ a = j
        · obtain ⟨rfl, rfl⟩ := e2; exact hab.symm
        · simp [e1, e2] at h
    · ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.single_apply,
        show (a = j ∧ b = i) ↔ (b = i ∧ a = j) from and_comm, show (b = j ∧ a = i) ↔ (a = i ∧ b = j) from and_comm]
      by_cases e1 : a = i ∧ b = j <;> by_cases e2 : b = i ∧ a = j <;> simp [e1, e2]
  · apply inK_of_support_sign_eq_of_skewAdjoint
    · intro i j h
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.single_apply] at h
      by_cases e1 : a = i ∧ b = j
      · obtain ⟨rfl, rfl⟩ := e1; exact hab
      · by_cases e2 : b = i ∧ a = j
        · obtain ⟨rfl, rfl⟩ := e2; exact hab.symm
        · simp [e1, e2] at h
    · ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.neg_apply,
        Matrix.single_apply, smul_eq_mul,
        show (a = j ∧ b = i) ↔ (b = i ∧ a = j) from and_comm, show (b = j ∧ a = i) ↔ (a = i ∧ b = j) from and_comm]
      by_cases e1 : a = i ∧ b = j <;> by_cases e2 : b = i ∧ a = j <;>
        simp [e1, e2, Complex.conj_I, map_ofNat] <;> ring

/- English proof (translation)
Use `set D : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ → (R.V →L[ℂ] R.V) := fun X Y => R.dτ X * R.dτ Y - R.dτ Y * R.dτ X - R.dτ (X * Y - Y * X) with hD`. Establish `Dal : ∀ X X' Y, D (X + X') Y = D X Y + D X' Y`. Introduce `X X' Y`. Simplify using `only [hD, map_add, add_mul, mul_add, map_sub]`. Normalize the expressions using the abelian group laws.

Establish `Dar : ∀ X Y Y', D X (Y + Y') = D X Y + D X Y'`. Introduce `X Y Y'`. Simplify using `only [hD, map_add, add_mul, mul_add, map_sub]`. Normalize the expressions using the abelian group laws. Establish `Dsl : ∀ (c : ℂ) X Y, D (c • X) Y = c • D X Y`.

Introduce `c X Y`. Simplify using `only [hD, map_smul, smul_mul_assoc, mul_smul_comm, smul_sub, map_sub]`. Establish `Dsr : ∀ (c : ℂ) X Y, D X (c • Y) = c • D X Y`. Introduce `c X Y`. Simplify using `only [hD, map_smul, smul_mul_assoc, mul_smul_comm, smul_sub, map_sub]`.

Establish `base : ∀ X Y, inK ε X → inK ε Y → D X Y = 0` using `fun X Y hX hY => sub_eq_zero.mpr (R.rel_dτ_bracket hX hY)`. Take `⟨hX1, hZ1⟩` from `inK_single_sub_single_and_I_smul_add_of_sign_eq (ε := ε) hab`. Take `⟨hY1, hW1⟩` from `inK_single_sub_single_and_I_smul_add_of_sign_eq (ε := ε) hcd`. Establish `hI : Complex.I ≠ 0` using `Complex.I_ne_zero`. Establish `h12 : D (Matrix.single a b 1 - Matrix.single b a 1) (Matrix.single c d 1 + Matrix.single d c 1) = 0`.

Use `base _ _ hX1 hW1` as an intermediate fact. Rewrite `this` using `[Dsr]`. Conclude with `(smul_eq_zero.mp this).resolve_left hI`. Establish `h21 : D (Matrix.single a b 1 + Matrix.single b a 1) (Matrix.single c d 1 - Matrix.single d c 1) = 0`. Use `base _ _ hZ1 hY1` as an intermediate fact.

Rewrite `this` using `[Dsl]`. Conclude with `(smul_eq_zero.mp this).resolve_left hI`. Establish `h22 : D (Matrix.single a b 1 + Matrix.single b a 1) (Matrix.single c d 1 + Matrix.single d c 1) = 0`. Use `base _ _ hZ1 hW1` as an intermediate fact. Rewrite `this` using `[Dsl, Dsr, smul_smul]`.

Conclude with `(smul_eq_zero.mp this).resolve_left (mul_ne_zero hI hI)`. Establish `h11` using `base _ _ hX1 hY1`. Establish `split : ∀ u v : Fin n, Matrix.single u v (1 : ℂ) = (1 / 2 : ℂ) • ((Matrix.single u v 1 - Matrix.single v u 1) + (Matrix.single u v 1 + Matrix.single v u 1))`. Introduce `u v`. Rewrite using `[show (Matrix.single u v (1 : ℂ) - Matrix.single v u 1) + (Matrix.single u v 1 + Matrix.single v u 1) = (2 : ℂ) • Matrix.single u v 1 by rw [two_smul]; abel, smul_smul]`.

Evaluate the numerical expressions. Establish `key : D (Matrix.single a b 1) (Matrix.single c d 1) = 0`. Rewrite using `[split a b, split c d, Dsl, Dsr, Dal, Dar (Matrix.single a b 1 - Matrix.single b a 1), Dar (Matrix.single a b 1 + Matrix.single b a 1), h11, h12, h21, h22]`. Simplify using the standard rewrite rules. Conclude with `sub_eq_zero.mp key`.
-/
private theorem KRep.rel_dτ_bracket_single {ε : Fin n → Bool} (R : KRep ε)
    {a b c d : Fin n} (hab : ε a = ε b) (hcd : ε c = ε d) :
    R.dτ (Matrix.single a b 1) * R.dτ (Matrix.single c d 1) -
        R.dτ (Matrix.single c d 1) * R.dτ (Matrix.single a b 1) =
      R.dτ (Matrix.single a b 1 * Matrix.single c d 1 -
        Matrix.single c d 1 * Matrix.single a b 1) := by
  set D : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ → (R.V →L[ℂ] R.V) :=
    fun X Y => R.dτ X * R.dτ Y - R.dτ Y * R.dτ X - R.dτ (X * Y - Y * X) with hD
  have Dal : ∀ X X' Y, D (X + X') Y = D X Y + D X' Y := by
    intro X X' Y; simp only [hD, map_add, add_mul, mul_add, map_sub]; abel
  have Dar : ∀ X Y Y', D X (Y + Y') = D X Y + D X Y' := by
    intro X Y Y'; simp only [hD, map_add, add_mul, mul_add, map_sub]; abel
  have Dsl : ∀ (c : ℂ) X Y, D (c • X) Y = c • D X Y := by
    intro c X Y; simp only [hD, map_smul, smul_mul_assoc, mul_smul_comm, smul_sub, map_sub]
  have Dsr : ∀ (c : ℂ) X Y, D X (c • Y) = c • D X Y := by
    intro c X Y; simp only [hD, map_smul, smul_mul_assoc, mul_smul_comm, smul_sub, map_sub]
  have base : ∀ X Y, inK ε X → inK ε Y → D X Y = 0 := fun X Y hX hY =>
    sub_eq_zero.mpr (R.rel_dτ_bracket hX hY)
  obtain ⟨hX1, hZ1⟩ := inK_single_sub_single_and_I_smul_add_of_sign_eq (ε := ε) hab
  obtain ⟨hY1, hW1⟩ := inK_single_sub_single_and_I_smul_add_of_sign_eq (ε := ε) hcd
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have h12 : D (Matrix.single a b 1 - Matrix.single b a 1) (Matrix.single c d 1 + Matrix.single d c 1) = 0 := by
    have := base _ _ hX1 hW1; rw [Dsr] at this; exact (smul_eq_zero.mp this).resolve_left hI
  have h21 : D (Matrix.single a b 1 + Matrix.single b a 1) (Matrix.single c d 1 - Matrix.single d c 1) = 0 := by
    have := base _ _ hZ1 hY1; rw [Dsl] at this; exact (smul_eq_zero.mp this).resolve_left hI
  have h22 : D (Matrix.single a b 1 + Matrix.single b a 1) (Matrix.single c d 1 + Matrix.single d c 1) = 0 := by
    have := base _ _ hZ1 hW1; rw [Dsl, Dsr, smul_smul] at this
    exact (smul_eq_zero.mp this).resolve_left (mul_ne_zero hI hI)
  have h11 := base _ _ hX1 hY1
  have split : ∀ u v : Fin n, Matrix.single u v (1 : ℂ) =
      (1 / 2 : ℂ) • ((Matrix.single u v 1 - Matrix.single v u 1) + (Matrix.single u v 1 + Matrix.single v u 1)) := by
    intro u v
    rw [show (Matrix.single u v (1 : ℂ) - Matrix.single v u 1) + (Matrix.single u v 1 + Matrix.single v u 1) =
      (2 : ℂ) • Matrix.single u v 1 by rw [two_smul]; abel, smul_smul]
    norm_num
  have key : D (Matrix.single a b 1) (Matrix.single c d 1) = 0 := by
    rw [split a b, split c d, Dsl, Dsr, Dal, Dar (Matrix.single a b 1 - Matrix.single b a 1),
      Dar (Matrix.single a b 1 + Matrix.single b a 1), h11, h12, h21, h22]
    simp
  exact sub_eq_zero.mp key

/- English proof (translation)
Establish `h1` using `(inK_single_sub_single_and_I_smul_add_of_sign_eq (ε := ε) hab).1`. Establish `h2` using `(inK_single_sub_single_and_I_smul_add_of_sign_eq (ε := ε) hab).2`. Establish `s1` using `R.rel_star_dτ h1`. Establish `s2` using `R.rel_star_dτ h2`. Simplify using `only [map_sub, map_add, map_smul, star_sub, star_add, star_smul, Complex.star_def, Complex.conj_I] at s1 s2`.

Use `set A := R.dτ (Matrix.single a b 1)`. Use `set B := R.dτ (Matrix.single b a 1)`. Establish `h3 : star A - star B = B - A` using `by rw [s1]; abel`. Establish `h4 : star A + star B = A + B`. Use `congrArg (fun x => Complex.I • x) s2` as an intermediate fact.

Conclude with `(by simpa [smul_add, smul_smul, Complex.I_mul_I, neg_smul, smul_neg, mul_neg] using this : star A + star B = B + A).trans (add_comm B A)`. Establish `h5 : (2 : ℂ) • star A = (2 : ℂ) • B`. Rewrite using `[two_smul, two_smul]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `smul_right_injective _ two_ne_zero h5`.
-/
private theorem KRep.rel_star_dτ_single {ε : Fin n → Bool} (R : KRep ε)
    {a b : Fin n} (hab : ε a = ε b) :
    star (R.dτ (Matrix.single a b 1)) = R.dτ (Matrix.single b a 1) := by
  have h1 := (inK_single_sub_single_and_I_smul_add_of_sign_eq (ε := ε) hab).1
  have h2 := (inK_single_sub_single_and_I_smul_add_of_sign_eq (ε := ε) hab).2
  have s1 := R.rel_star_dτ h1
  have s2 := R.rel_star_dτ h2
  simp only [map_sub, map_add, map_smul, star_sub, star_add, star_smul, Complex.star_def, Complex.conj_I] at s1 s2
  set A := R.dτ (Matrix.single a b 1)
  set B := R.dτ (Matrix.single b a 1)
  have h3 : star A - star B = B - A := by rw [s1]; abel
  have h4 : star A + star B = A + B := by
    have := congrArg (fun x => Complex.I • x) s2
    exact (by simpa [smul_add, smul_smul, Complex.I_mul_I, neg_smul, smul_neg, mul_neg] using this :
      star A + star B = B + A).trans (add_comm B A)
  have h5 : (2 : ℂ) • star A = (2 : ℂ) • B := by
    rw [two_smul, two_smul]
    calc star A + star A = (star A - star B) + (star A + star B) := by abel
      _ = (B - A) + (A + B) := by rw [h3, h4]
      _ = B + B := by abel
  exact smul_right_injective _ two_ne_zero h5

/- English proof (translation)
Introduce `a b hab x y`. Establish `h` using `R.rel_star_dτ_single hab`. Simplify using `only [KRep.units, ContinuousLinearMap.coe_coe]`. Rewrite using `[← h, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]`.
-/
theorem KRep.kUnit_units {ε : Fin n → Bool} (R : KRep ε) : Formalism.REAL.KUnit ε R.units := by
  intro a b hab x y
  have h := R.rel_star_dτ_single hab
  simp only [KRep.units, ContinuousLinearMap.coe_coe]
  rw [← h, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

/- English proof (translation)
Introduce `a b c d hab hcd`. Establish `h` using `R.rel_dτ_bracket_single hab hcd`. Establish `key : Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 = (if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0)`. Apply the tactic sequence `by_cases hbc : b = c <;> by_cases hda : d = a <;> simp only [hbc, hda, if_true, if_false] <;> first`. Consider the case `simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, hbc, hda, Ne.symm hda]`.

Consider the case `(subst hbc; subst hda; simp [Matrix.single_mul_single_same])`. Consider the case `(subst hbc; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, hda, Ne.symm hda])`. Consider the case `(subst hda; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, hbc, Ne.symm hbc])`. Establish `e : ∀ P Q : R.V →L[ℂ] R.V, ((P * Q - Q * P : R.V →L[ℂ] R.V) : Module.End ℂ R.V) = (P : Module.End ℂ R.V) * Q - (Q : Module.End ℂ R.V) * P`. Introduce `P Q`.

Use extensionality with `x`. Simplify using the standard rewrite rules. Simplify using `only [KRep.units]`. Rewrite using `[← e, h, key, map_sub]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem KRep.kRel_units {ε : Fin n → Bool} (R : KRep ε) : Formalism.REAL.KRel ε R.units := by
  intro a b c d hab hcd
  have h := R.rel_dτ_bracket_single hab hcd
  have key : Matrix.single a b (1 : ℂ) * Matrix.single c d 1 - Matrix.single c d 1 * Matrix.single a b 1 =
      (if b = c then Matrix.single a d 1 else 0) - (if d = a then Matrix.single c b 1 else 0) := by
    by_cases hbc : b = c <;> by_cases hda : d = a <;> simp only [hbc, hda, if_true, if_false] <;>
      first
      | simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, hbc, hda, Ne.symm hda]
      | (subst hbc; subst hda; simp [Matrix.single_mul_single_same])
      | (subst hbc; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, hda, Ne.symm hda])
      | (subst hda; simp [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, hbc, Ne.symm hbc])
  have e : ∀ P Q : R.V →L[ℂ] R.V, ((P * Q - Q * P : R.V →L[ℂ] R.V) : Module.End ℂ R.V) =
      (P : Module.End ℂ R.V) * Q - (Q : Module.End ℂ R.V) * P := by
    intro P Q; ext x; simp
  simp only [KRep.units]
  rw [← e, h, key, map_sub]
  split_ifs <;> simp

/- English proof (translation)
Introduce `_ _ R` and use `⟨R.kRel_units, R.kUnit_units⟩`.
-/
theorem kRepRel : KRepRelStatement := fun _ _ R => ⟨R.kRel_units, R.kUnit_units⟩

end ReciprocityTheory.ChartRestriction.DS.HW
