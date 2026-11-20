import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt
open MvPolynomial

set_option maxHeartbeats 400000 in
/- English proof (translation)
Establish `hg : (fun v : Fin a × Fin a => ∑ b, MvPolynomial.C (Matrix.diagonal t v.1 b) * MvPolynomial.X (b, v.2)) = fun v => MvPolynomial.C (t v.1) * MvPolynomial.X v`. Use function extensionality and compare the values at `v`. Rewrite using `[Finset.sum_eq_single v.1]`. Simplify using the standard rewrite rules. Introduce `b _ hb`.

Rewrite using `[Matrix.diagonal_apply_ne t (Ne.symm hb), map_zero, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Use `show MvPolynomial.coeff m (MvPolynomial.aeval (fun v : Fin a × Fin a => ∑ b, MvPolynomial.C (Matrix.diagonal t v.1 b) * MvPolynomial.X (b, v.2)) f) = _`. Rewrite using `[hg]`.

Proceed by induction on `f using MvPolynomial.induction_on' with`. Consider the case `monomial n c`. Rewrite using `[aeval_monomial, MvPolynomial.algebraMap_eq, Finsupp.prod]`. Simplify using `only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]`. Rewrite using `[MvPolynomial.prod_X_pow_eq_monomial, ← mul_assoc, ← map_mul, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]`.

Use `split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[mul_one, mul_comm]`. Use `congr 1`. Use `Finset.prod_subset (Finset.subset_univ _) ?_` and prove the remaining obligations.

Introduce `v _ hv`. Simplify using `only [Finsupp.mem_support_iff, not_not] at hv`. Rewrite using `[hv, pow_zero]`. Simplify using the standard rewrite rules. Consider the case `add p q hp hq`.

Rewrite using `[map_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]`.
-/
private theorem coeff_diag {a : ℕ} (t : Fin a → ℂ) (f : MvPolynomial (Fin a × Fin a) ℂ) (m : Fin a × Fin a →₀ ℕ) :
    MvPolynomial.coeff m (Formalism.GradedWeylDivisibility.rowAct ℂ (n := a) (Matrix.diagonal t) f) = (∏ v : Fin a × Fin a, t v.1 ^ m v) * MvPolynomial.coeff m f := by
  have hg : (fun v : Fin a × Fin a => ∑ b, MvPolynomial.C (Matrix.diagonal t v.1 b) * MvPolynomial.X (b, v.2))
      = fun v => MvPolynomial.C (t v.1) * MvPolynomial.X v := by
    funext v
    rw [Finset.sum_eq_single v.1]
    · simp
    · intro b _ hb
      rw [Matrix.diagonal_apply_ne t (Ne.symm hb), map_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  show MvPolynomial.coeff m (MvPolynomial.aeval
      (fun v : Fin a × Fin a => ∑ b, MvPolynomial.C (Matrix.diagonal t v.1 b) * MvPolynomial.X (b, v.2)) f) = _
  rw [hg]
  induction f using MvPolynomial.induction_on' with
  | monomial n c =>
    rw [aeval_monomial, MvPolynomial.algebraMap_eq, Finsupp.prod]
    simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
    rw [MvPolynomial.prod_X_pow_eq_monomial, ← mul_assoc, ← map_mul, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    split_ifs with h
    · subst h
      rw [mul_one, mul_comm]
      congr 1
      refine Finset.prod_subset (Finset.subset_univ _) ?_
      intro v _ hv
      simp only [Finsupp.mem_support_iff, not_not] at hv
      rw [hv, pow_zero]
    · simp
  | add p q hp hq =>
    rw [map_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

/- English proof (translation)
Introduce `hE hEv hDom a k κ w L`. Take `⟨_, _, hle, hmon, _, _⟩` from `hE`. Take `⟨D, hD⟩ : ∃ D : ℕ, D = (Finset.univ.filter fun i : Fin a => (i : ℕ) < k).card` from `⟨_, rfl⟩`. Take `⟨e, he⟩ : ∃ e : (Fin a × Fin a →₀ ℕ) → ℕ, e = fun m => ∑ i ∈ Finset.univ.filter (fun i : Fin a => (i : ℕ) < k), Formalism.GradedWeylDivisibility.rowDeg m i` from `⟨_, rfl⟩`. Establish `hdet : ∀ z : Circle, detPow ℂ a (tor a k z) κ.detShift = (z : ℂ) ^ ((D : ℤ) * κ.detShift)`.

Introduce `z`. Simplify using `only [detPow]`. Rewrite using `[Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, tor_coe, Matrix.det_diagonal, ← Finset.prod_filter, Finset.prod_const, zpow_mul, zpow_natCast, hD]`. Establish `hprod : ∀ (z : Circle) (m : Fin a × Fin a →₀ ℕ), (∏ v : Fin a × Fin a, (if ((v.1 : Fin a) : ℕ) < k then (z : ℂ) else 1) ^ m v) = (z : ℂ) ^ e m`. Introduce `z m`.

Establish `hin : ∀ i : Fin a, (∏ s : Fin a, (if (i : ℕ) < k then (z : ℂ) else 1) ^ m (i, s)) = if (i : ℕ) < k then (z : ℂ) ^ Formalism.GradedWeylDivisibility.rowDeg m i else 1`. Introduce `i`. Use `split_ifs`. Rewrite using `[Finset.prod_pow_eq_pow_sum]`. Both sides reduce to the same expression.

Simplify using the standard rewrite rules. Rewrite using `[Fintype.prod_prod_type]`. Simplify using `only`. Simplify using `only [hin]`. Rewrite using `[← Finset.prod_filter, Finset.prod_pow_eq_pow_sum, he]`.

Establish `hcoeff : ∀ (z : Circle) (m : Fin a × Fin a →₀ ℕ), MvPolynomial.coeff m ((sqRep ℂ a κ (tor a k z) w : nablaSq ℂ a κ) : MvPolynomial (Fin a × Fin a) ℂ) = MvPolynomial.coeff m (w : MvPolynomial (Fin a × Fin a) ℂ) * (z : ℂ) ^ ((D : ℤ) * κ.detShift + (e m : ℤ))`. Introduce `z m`. Use `show MvPolynomial.coeff m (sqAct ℂ a κ (tor a k z) (w : MvPolynomial (Fin a × Fin a) ℂ)) = _`. Rewrite using `[sqAct, MvPolynomial.coeff_smul, hdet, tor_coe, Matrix.diagonal_transpose, coeff_diag]`. Use `beta_reduce`.

Rewrite using `[hprod, smul_eq_mul, zpow_add₀ (Circle.coe_ne_zero z), zpow_natCast]`. Expand and normalize the polynomial expressions, which then agree. Set `ev : (Fin a × Fin a →₀ ℕ) → nablaSq ℂ a κ →ₗ[ℂ] ℂ` to `fun x => (MvPolynomial.lcoeff ℂ x).comp (nablaSq ℂ a κ).subtype`. Establish `hsep : ∀ p : nablaSq ℂ a κ, (∀ x, ev x p = 0) → p = 0`. Introduce `p hp`.

Apply `Subtype.ext` to reduce the goal to its premises. Use extensionality with `x`. Simplify `hp x` using `[ev]`. Establish `hterm : ∀ T : Submodule ℂ (Circle → ℂ), (∀ x, MvPolynomial.coeff x (w : MvPolynomial (Fin a × Fin a) ℂ) ≠ 0 → (fun z : Circle => MvPolynomial.coeff x (w : MvPolynomial (Fin a × Fin a) ℂ) * (z : ℂ) ^ ((D : ℤ) * κ.detShift + (e x : ℤ))) ∈ T) → (fun z => L (sqRep ℂ a κ (tor a k z) w …`. Introduce `T hT`.

Use `hEv (nablaSq ℂ a κ) (Fin a × Fin a →₀ ℕ) Circle ev hsep T (fun z => sqRep ℂ a κ (tor a k z) w) ?_ L` and prove the remaining obligations. Introduce `x`. Establish `hfun : (fun z => ev x (sqRep ℂ a κ (tor a k z) w)) = fun z : Circle => MvPolynomial.coeff x (w : MvPolynomial (Fin a × Fin a) ℂ) * (z : ℂ) ^ ((D : ℤ) * κ.detShift + (e x : ℤ))` using `funext fun z => hcoeff z x`. Rewrite using `[hfun]`. Distinguish the cases in `hx : MvPolynomial.coeff x (w : MvPolynomial (Fin a × Fin a) ℂ) = 0`.

Establish `h0 : (fun z : Circle => MvPolynomial.coeff x (w : MvPolynomial (Fin a × Fin a) ℂ) * (z : ℂ) ^ ((D : ℤ) * κ.detShift + (e x : ℤ))) = 0`. Use function extensionality and compare the values at `z`. Simplify using `[hx]`. Rewrite using `[h0]`. Conclude with `T.zero_mem`.

Conclude with `hT x hx`. Establish `hds : ∀ i : Fin a, κ.detShift ≤ κ.w i`. Introduce `i`. Simplify using `only [DomWeight.detShift, dif_pos (Fin.pos i)]`. Conclude with `κ.anti (Fin.le_iff_val_le_val.mpr (by simp only; omega))`.

Establish `hnat : ∀ i : Fin a, ((κ.natW i : ℕ) : ℤ) = κ.w i - κ.detShift` using `fun i => Int.toNat_of_nonneg (sub_nonneg.mpr (hds i))`. Establish `hDa : D ≤ a`. Rewrite using `[hD]`. Conclude with `(Finset.card_filter_le _ _).trans (Finset.card_fin a).le`. Use `⟨hterm _ fun x hx => ?_, hterm _ fun x _ => ?_⟩` and prove the remaining obligations.

Establish `hxs : x ∈ (w : MvPolynomial (Fin a × Fin a) ℂ).support` using `MvPolynomial.mem_support_iff.mpr hx`. Establish `hbound` using `hDom a κ _ w.2 x hxs k`. Establish `hup : (D : ℤ) * κ.detShift + (e x : ℤ) ≤ psum κ k`. Establish `h1 : (e x : ℤ) ≤ ((∑ i ∈ Finset.univ.filter (fun i : Fin a => (i : ℕ) < k), κ.natW i : ℕ) : ℤ)`. Rewrite using `[he]`.

Conclude with `hbound` after adjusting the coercions. Establish `h2 : (D : ℤ) * κ.detShift + ((∑ i ∈ Finset.univ.filter (fun i : Fin a => (i : ℕ) < k), κ.natW i : ℕ) : ℤ) = psum κ k`. Rewrite using `[Nat.cast_sum]`. Simplify using `only [hnat]`. Rewrite using `[Finset.sum_sub_distrib, hD, psum]`.

Rewrite using `[Finset.sum_const, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(hle _ _ hup).1 (hmon _ _).1`. Establish `hlow : -((a * κ.detShift.natAbs : ℕ) : ℤ) ≤ (D : ℤ) * κ.detShift + (e x : ℤ)`.

Establish `hD0 : (0 : ℤ) ≤ D` using `Int.natCast_nonneg D`. Establish `hDa' : (D : ℤ) ≤ a` using `by exact_mod_cast hDa`. Establish `he0 : (0 : ℤ) ≤ (e x : ℤ)` using `Int.natCast_nonneg _`. Establish `habs : 0 ≤ κ.detShift + |κ.detShift|` using `by linarith [neg_abs_le κ.detShift]`. Use `push_cast`.

Use polynomial arithmetic with `[mul_nonneg hD0 habs, mul_nonneg (sub_nonneg.mpr hDa') (abs_nonneg κ.detShift)]`. Conclude with `(hle _ _ hlow).2 (hmon _ _).2`.
-/
theorem UpperTheory.Gal.Wt.sqExp_h : ExpBasic → EvLem → Dom → SqExp := by
  intro hE hEv hDom a k κ w L
  obtain ⟨_, _, hle, hmon, _, _⟩ := hE
  obtain ⟨D, hD⟩ : ∃ D : ℕ, D = (Finset.univ.filter fun i : Fin a => (i : ℕ) < k).card := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : (Fin a × Fin a →₀ ℕ) → ℕ,
      e = fun m => ∑ i ∈ Finset.univ.filter (fun i : Fin a => (i : ℕ) < k), Formalism.GradedWeylDivisibility.rowDeg m i := ⟨_, rfl⟩
  have hdet : ∀ z : Circle, detPow ℂ a (tor a k z) κ.detShift = (z : ℂ) ^ ((D : ℤ) * κ.detShift) := by
    intro z
    simp only [detPow]
    rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, tor_coe, Matrix.det_diagonal,
      ← Finset.prod_filter, Finset.prod_const, zpow_mul, zpow_natCast, hD]
  have hprod : ∀ (z : Circle) (m : Fin a × Fin a →₀ ℕ),
      (∏ v : Fin a × Fin a, (if ((v.1 : Fin a) : ℕ) < k then (z : ℂ) else 1) ^ m v) = (z : ℂ) ^ e m := by
    intro z m
    have hin : ∀ i : Fin a, (∏ s : Fin a, (if (i : ℕ) < k then (z : ℂ) else 1) ^ m (i, s))
        = if (i : ℕ) < k then (z : ℂ) ^ Formalism.GradedWeylDivisibility.rowDeg m i else 1 := by
      intro i
      split_ifs
      · rw [Finset.prod_pow_eq_pow_sum]
        rfl
      · simp
    rw [Fintype.prod_prod_type]
    dsimp only
    simp only [hin]
    rw [← Finset.prod_filter, Finset.prod_pow_eq_pow_sum, he]
  have hcoeff : ∀ (z : Circle) (m : Fin a × Fin a →₀ ℕ),
      MvPolynomial.coeff m ((sqRep ℂ a κ (tor a k z) w : nablaSq ℂ a κ) : MvPolynomial (Fin a × Fin a) ℂ)
        = MvPolynomial.coeff m (w : MvPolynomial (Fin a × Fin a) ℂ)
          * (z : ℂ) ^ ((D : ℤ) * κ.detShift + (e m : ℤ)) := by
    intro z m
    show MvPolynomial.coeff m (sqAct ℂ a κ (tor a k z) (w : MvPolynomial (Fin a × Fin a) ℂ)) = _
    rw [sqAct, MvPolynomial.coeff_smul, hdet, tor_coe, Matrix.diagonal_transpose, coeff_diag]
    beta_reduce
    rw [hprod, smul_eq_mul, zpow_add₀ (Circle.coe_ne_zero z), zpow_natCast]
    ring
  let ev : (Fin a × Fin a →₀ ℕ) → nablaSq ℂ a κ →ₗ[ℂ] ℂ :=
    fun x => (MvPolynomial.lcoeff ℂ x).comp (nablaSq ℂ a κ).subtype
  have hsep : ∀ p : nablaSq ℂ a κ, (∀ x, ev x p = 0) → p = 0 := by
    intro p hp
    apply Subtype.ext
    ext x
    simpa [ev] using hp x
  have hterm : ∀ T : Submodule ℂ (Circle → ℂ),
      (∀ x, MvPolynomial.coeff x (w : MvPolynomial (Fin a × Fin a) ℂ) ≠ 0 →
        (fun z : Circle => MvPolynomial.coeff x (w : MvPolynomial (Fin a × Fin a) ℂ)
          * (z : ℂ) ^ ((D : ℤ) * κ.detShift + (e x : ℤ))) ∈ T) →
      (fun z => L (sqRep ℂ a κ (tor a k z) w)) ∈ T := by
    intro T hT
    refine hEv (nablaSq ℂ a κ) (Fin a × Fin a →₀ ℕ) Circle ev hsep T (fun z => sqRep ℂ a κ (tor a k z) w) ?_ L
    intro x
    have hfun : (fun z => ev x (sqRep ℂ a κ (tor a k z) w))
        = fun z : Circle => MvPolynomial.coeff x (w : MvPolynomial (Fin a × Fin a) ℂ)
          * (z : ℂ) ^ ((D : ℤ) * κ.detShift + (e x : ℤ)) := funext fun z => hcoeff z x
    rw [hfun]
    by_cases hx : MvPolynomial.coeff x (w : MvPolynomial (Fin a × Fin a) ℂ) = 0
    · have h0 : (fun z : Circle => MvPolynomial.coeff x (w : MvPolynomial (Fin a × Fin a) ℂ)
          * (z : ℂ) ^ ((D : ℤ) * κ.detShift + (e x : ℤ))) = 0 := by
        funext z
        simp [hx]
      rw [h0]
      exact T.zero_mem
    · exact hT x hx
  have hds : ∀ i : Fin a, κ.detShift ≤ κ.w i := by
    intro i
    simp only [DomWeight.detShift, dif_pos (Fin.pos i)]
    exact κ.anti (Fin.le_iff_val_le_val.mpr (by simp only; omega))
  have hnat : ∀ i : Fin a, ((κ.natW i : ℕ) : ℤ) = κ.w i - κ.detShift :=
    fun i => Int.toNat_of_nonneg (sub_nonneg.mpr (hds i))
  have hDa : D ≤ a := by
    rw [hD]
    exact (Finset.card_filter_le _ _).trans (Finset.card_fin a).le
  refine ⟨hterm _ fun x hx => ?_, hterm _ fun x _ => ?_⟩
  · have hxs : x ∈ (w : MvPolynomial (Fin a × Fin a) ℂ).support := MvPolynomial.mem_support_iff.mpr hx
    have hbound := hDom a κ _ w.2 x hxs k
    have hup : (D : ℤ) * κ.detShift + (e x : ℤ) ≤ psum κ k := by
      have h1 : (e x : ℤ) ≤ ((∑ i ∈ Finset.univ.filter (fun i : Fin a => (i : ℕ) < k), κ.natW i : ℕ) : ℤ) := by
        rw [he]
        exact_mod_cast hbound
      have h2 : (D : ℤ) * κ.detShift
          + ((∑ i ∈ Finset.univ.filter (fun i : Fin a => (i : ℕ) < k), κ.natW i : ℕ) : ℤ) = psum κ k := by
        rw [Nat.cast_sum]
        simp only [hnat]
        rw [Finset.sum_sub_distrib, hD, psum]
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
      linarith
    exact (hle _ _ hup).1 (hmon _ _).1
  · have hlow : -((a * κ.detShift.natAbs : ℕ) : ℤ) ≤ (D : ℤ) * κ.detShift + (e x : ℤ) := by
      have hD0 : (0 : ℤ) ≤ D := Int.natCast_nonneg D
      have hDa' : (D : ℤ) ≤ a := by exact_mod_cast hDa
      have he0 : (0 : ℤ) ≤ (e x : ℤ) := Int.natCast_nonneg _
      have habs : 0 ≤ κ.detShift + |κ.detShift| := by linarith [neg_abs_le κ.detShift]
      push_cast
      nlinarith [mul_nonneg hD0 habs, mul_nonneg (sub_nonneg.mpr hDa') (abs_nonneg κ.detShift)]
    exact (hle _ _ hlow).2 (hmon _ _).2
