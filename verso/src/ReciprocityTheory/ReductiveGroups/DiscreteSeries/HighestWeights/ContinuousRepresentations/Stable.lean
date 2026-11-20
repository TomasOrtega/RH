import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.DerivExistsAllPosStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.SingleMulJmComm

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

/- English proof (translation)
Use `set A := R.dτ X with hA`. Establish `hmulK : ∀ a b : KG ε, toMK (a * b) = toMK a * toMK b` using `fun a b => rfl`. Establish `honeK : toMK (1 : KG ε) = 1` using `rfl`. Establish `hγadd : ∀ s u : ℝ, γ (s + u) = γ s * γ u`. Introduce `s u`.

Apply `onep_KG_ext` to reduce the goal to its premises. Rewrite using `[hmulK, hγ, hγ, hγ, Complex.ofReal_add, add_smul]`. Conclude with `Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _)`. Establish `hop : ∀ a b : KG ε, R.op (a * b) = R.op a * R.op b`. Introduce `a b`.

Simplify using `[KRep.op]`. Establish `hγ0 : γ 0 = 1`. Apply `onep_KG_ext` to reduce the goal to its premises. Rewrite using `[hγ, honeK]`. Simplify using the standard rewrite rules.

Establish `hd0 : HasDerivAt (fun t => R.op (γ t)) A 0` using `R.hasDeriv X hX γ hγ`. Establish `hd : ∀ s : ℝ, HasDerivAt (fun t => R.op (γ t)) (R.op (γ s) * A) s`. Introduce `s`. Establish `h1 : HasDerivAt (fun t => R.op (γ (t - s))) A s` using `HasDerivAt.comp_sub_const (f := fun t => R.op (γ t)) s s (by rwa [sub_self])`. Use `(h1.const_mul (R.op (γ s))).congr_of_eventuallyEq ?_` and prove the remaining obligations.

Use `filter_upwards with u`. Rewrite using `[← hop, ← hγadd, add_sub_cancel]`. Establish `hE : ∀ s : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp (u • -A)) (NormedSpace.exp (s • -A) * -A) s` using `fun s => hasDerivAt_exp_smul_const (-A) s`. Establish `hcomm : ∀ s : ℝ, Commute A (NormedSpace.exp (s • -A))` using `fun s => (((Commute.refl A).neg_right).smul_right s).exp_right`. Establish `hh : ∀ s : ℝ, HasDerivAt (fun u => R.op (γ u) * NormedSpace.exp (u • -A)) 0 s`.

Introduce `s`. Use `(hd s).mul (hE s)` as an intermediate fact. Establish `key : R.op (γ s) * A * NormedSpace.exp (s • -A) + R.op (γ s) * (NormedSpace.exp (s • -A) * -A) = 0`. Rewrite using `[mul_assoc, (hcomm s).eq, mul_neg, mul_neg, add_neg_cancel]`. Rewrite `this` using `[key]`.

Conclude with `this`. Establish `hconst : ∀ u : ℝ, R.op (γ u) * NormedSpace.exp (u • -A) = 1`. Introduce `u`. Use `is_const_of_deriv_eq_zero (f := fun u => R.op (γ u) * NormedSpace.exp (u • -A)) (fun s => (hh s).differentiableAt) (fun s => (hh s).deriv) u 0` as an intermediate fact. Rewrite using `[this]`.

Simplify using `[hγ0, KRep.op]`. Establish `hinv : NormedSpace.exp (t • -A) * NormedSpace.exp (t • A) = 1`. Establish `hk : ∀ s : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp (u • -A) * NormedSpace.exp (u • A)) 0 s`. Introduce `s`. Use `(hE s).mul (hasDerivAt_exp_smul_const A s)` as an intermediate fact.

Establish `hcF : Commute (NormedSpace.exp (s • A)) A` using `((Commute.refl A).smul_left s).exp_left`. Establish `key : NormedSpace.exp (s • -A) * -A * NormedSpace.exp (s • A) + NormedSpace.exp (s • -A) * (NormedSpace.exp (s • A) * A) = 0`. Rewrite using `[mul_assoc, neg_mul, mul_neg, hcF.eq, neg_add_cancel]`. Rewrite `this` using `[key]`. Conclude with `this`.

Use `is_const_of_deriv_eq_zero (f := fun u : ℝ => NormedSpace.exp (u • -A) * NormedSpace.exp (u • A)) (fun s => (hk s).differentiableAt) (fun s => (hk s).deriv) t 0` as an intermediate fact. Rewrite using `[this]`. Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hinv, mul_one]`.

Use `_ = NormedSpace.exp (t • A) := by rw [← mul_assoc, hconst, one_mul]`. Use `_ = NormedSpace.exp ((t : ℂ) • A) := by rw [Complex.coe_smul]`.
-/
theorem KRep.op_curve {ε : Fin n → Bool} (R : KRep ε)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) (t : ℝ) :
    R.op (γ t) = NormedSpace.exp ((t : ℂ) • R.dτ X) := by
  set A := R.dτ X with hA
  have hmulK : ∀ a b : KG ε, toMK (a * b) = toMK a * toMK b := fun a b => rfl
  have honeK : toMK (1 : KG ε) = 1 := rfl
  have hγadd : ∀ s u : ℝ, γ (s + u) = γ s * γ u := by
    intro s u
    apply onep_KG_ext
    rw [hmulK, hγ, hγ, hγ, Complex.ofReal_add, add_smul]
    exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _)
  have hop : ∀ a b : KG ε, R.op (a * b) = R.op a * R.op b := by
    intro a b
    simp [KRep.op]
  have hγ0 : γ 0 = 1 := by
    apply onep_KG_ext
    rw [hγ, honeK]
    simp
  have hd0 : HasDerivAt (fun t => R.op (γ t)) A 0 := R.hasDeriv X hX γ hγ
  have hd : ∀ s : ℝ, HasDerivAt (fun t => R.op (γ t)) (R.op (γ s) * A) s := by
    intro s
    have h1 : HasDerivAt (fun t => R.op (γ (t - s))) A s :=
      HasDerivAt.comp_sub_const (f := fun t => R.op (γ t)) s s (by rwa [sub_self])
    refine (h1.const_mul (R.op (γ s))).congr_of_eventuallyEq ?_
    filter_upwards with u
    rw [← hop, ← hγadd, add_sub_cancel]
  have hE : ∀ s : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp (u • -A))
      (NormedSpace.exp (s • -A) * -A) s := fun s => hasDerivAt_exp_smul_const (-A) s
  have hcomm : ∀ s : ℝ, Commute A (NormedSpace.exp (s • -A)) := fun s =>
    (((Commute.refl A).neg_right).smul_right s).exp_right
  have hh : ∀ s : ℝ, HasDerivAt (fun u => R.op (γ u) * NormedSpace.exp (u • -A)) 0 s := by
    intro s
    have := (hd s).mul (hE s)
    have key : R.op (γ s) * A * NormedSpace.exp (s • -A) +
        R.op (γ s) * (NormedSpace.exp (s • -A) * -A) = 0 := by
      rw [mul_assoc, (hcomm s).eq, mul_neg, mul_neg, add_neg_cancel]
    rw [key] at this
    exact this
  have hconst : ∀ u : ℝ, R.op (γ u) * NormedSpace.exp (u • -A) = 1 := by
    intro u
    have := is_const_of_deriv_eq_zero (f := fun u => R.op (γ u) * NormedSpace.exp (u • -A))
      (fun s => (hh s).differentiableAt) (fun s => (hh s).deriv) u 0
    rw [this]
    simp [hγ0, KRep.op]
  have hinv : NormedSpace.exp (t • -A) * NormedSpace.exp (t • A) = 1 := by
    have hk : ∀ s : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp (u • -A) * NormedSpace.exp (u • A))
        0 s := by
      intro s
      have := (hE s).mul (hasDerivAt_exp_smul_const A s)
      have hcF : Commute (NormedSpace.exp (s • A)) A := ((Commute.refl A).smul_left s).exp_left
      have key : NormedSpace.exp (s • -A) * -A * NormedSpace.exp (s • A) +
          NormedSpace.exp (s • -A) * (NormedSpace.exp (s • A) * A) = 0 := by
        rw [mul_assoc, neg_mul, mul_neg, hcF.eq, neg_add_cancel]
      rw [key] at this
      exact this
    have := is_const_of_deriv_eq_zero
      (f := fun u : ℝ => NormedSpace.exp (u • -A) * NormedSpace.exp (u • A))
      (fun s => (hk s).differentiableAt) (fun s => (hk s).deriv) t 0
    rw [this]
    simp
  calc R.op (γ t) = R.op (γ t) * (NormedSpace.exp (t • -A) * NormedSpace.exp (t • A)) := by
        rw [hinv, mul_one]
    _ = NormedSpace.exp (t • A) := by rw [← mul_assoc, hconst, one_mul]
    _ = NormedSpace.exp ((t : ℂ) • A) := by rw [Complex.coe_smul]

/- English proof (translation)
Take `⟨Y, hY, hk⟩` from `exists_log ε k`. Take `⟨γ, hγ⟩` from `exists_curve ε hY`. Establish `h1 : γ 1 = k`. Apply `onep_KG_ext` to reduce the goal to its premises. Rewrite using `[hγ 1, hk, Complex.ofReal_one, one_smul]`.

Use `⟨Y, hY, ?_⟩` and prove the remaining obligations. Rewrite using `[← h1, R.op_curve hY γ hγ 1, Complex.ofReal_one, one_smul]`.
-/
theorem KRep.op_eq_exp {ε : Fin n → Bool} (R : KRep ε) (k : KG ε) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, inK ε Y ∧ R.op k = NormedSpace.exp (R.dτ Y) := by
  obtain ⟨Y, hY, hk⟩ := exists_log ε k
  obtain ⟨γ, hγ⟩ := exists_curve ε hY
  have h1 : γ 1 = k := by
    apply onep_KG_ext
    rw [hγ 1, hk, Complex.ofReal_one, one_smul]
  refine ⟨Y, hY, ?_⟩
  rw [← h1, R.op_curve hY γ hγ 1, Complex.ofReal_one, one_smul]

/- English proof (translation)
Establish `hK : ∀ X, inK ε X → ∀ v ∈ W, R.dτ X v ∈ W`. Introduce `X hX v hv`. Take `⟨γ, hγ⟩` from `exists_curve ε hX`. Establish `hd` using `R.hasDeriv X hX γ hγ`. Set `L : (R.V →L[ℂ] R.V) →L[ℝ] R.V` to `(ContinuousLinearMap.apply ℂ R.V v).restrictScalars ℝ`.

Establish `hdv : HasDerivAt (fun t => R.op (γ t) v) (R.dτ X v) 0` using `L.hasFDerivAt.comp_hasDerivAt 0 hd`. Establish `hclosed : IsClosed (W : Set R.V)` using `W.closed_of_finiteDimensional`. Use `hclosed.mem_of_tendsto hdv.tendsto_slope_zero (Filter.Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Conclude with `W.smul_of_tower_mem _ (W.sub_mem (hW _ v hv) (hW _ v hv))`. Introduce `a b hab v hv`.

Establish `hX1 : inK ε (Matrix.single a b (1 : ℂ) - Matrix.single b a 1)`. Apply `inK_of_skew_comm` to reduce the goal to its premises. Simplify using `[Matrix.conjTranspose_sub, Matrix.conjTranspose_single]`. Rewrite using `[sub_mul, mul_sub, single_mul_Jm_comm hab, single_mul_Jm_comm hab.symm]`. Establish `hX2 : inK ε (Complex.I • (Matrix.single a b (1 : ℂ) + Matrix.single b a 1))`.

Apply `inK_of_skew_comm` to reduce the goal to its premises. Simplify using `[Matrix.conjTranspose_add, Matrix.conjTranspose_single, add_comm, Matrix.single_neg]`. Rewrite using `[smul_mul_assoc, mul_smul_comm, add_mul, mul_add, single_mul_Jm_comm hab, single_mul_Jm_comm hab.symm]`. Establish `hI : -Complex.I / 2 * Complex.I = 1 / 2`. Rewrite using `[div_mul_eq_mul_div, neg_mul, Complex.I_mul_I]`.

Evaluate the numerical expressions. Establish `hdec : Matrix.single a b (1 : ℂ) = (1 / 2 : ℂ) • (Matrix.single a b (1 : ℂ) - Matrix.single b a 1) + (-Complex.I / 2) • (Complex.I • (Matrix.single a b (1 : ℂ) + Matrix.single b a 1))`. Rewrite using `[smul_smul, hI]`. Use `module`. Rewrite using `[hdec, map_add, map_smul, map_smul, _root_.add_apply, _root_.smul_apply, _root_.smul_apply]`.

Conclude with `W.add_mem (W.smul_mem _ (hK _ hX1 v hv)) (W.smul_mem _ (hK _ hX2 v hv))`.
-/
theorem KRep.dτ_stable_of_stable {ε : Fin n → Bool} (R : KRep ε)
    (W : Submodule ℂ R.V) (hW : ∀ k : KG ε, ∀ v ∈ W, R.op k v ∈ W) :
    ∀ a b, ε a = ε b → ∀ v ∈ W, R.dτ (Matrix.single a b 1) v ∈ W := by
  have hK : ∀ X, inK ε X → ∀ v ∈ W, R.dτ X v ∈ W := by
    intro X hX v hv
    obtain ⟨γ, hγ⟩ := exists_curve ε hX
    have hd := R.hasDeriv X hX γ hγ
    let L : (R.V →L[ℂ] R.V) →L[ℝ] R.V := (ContinuousLinearMap.apply ℂ R.V v).restrictScalars ℝ
    have hdv : HasDerivAt (fun t => R.op (γ t) v) (R.dτ X v) 0 :=
      L.hasFDerivAt.comp_hasDerivAt 0 hd
    have hclosed : IsClosed (W : Set R.V) := W.closed_of_finiteDimensional
    refine hclosed.mem_of_tendsto hdv.tendsto_slope_zero (Filter.Eventually.of_forall fun t => ?_)
    exact W.smul_of_tower_mem _ (W.sub_mem (hW _ v hv) (hW _ v hv))
  intro a b hab v hv
  have hX1 : inK ε (Matrix.single a b (1 : ℂ) - Matrix.single b a 1) := by
    apply inK_of_skew_comm
    · simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_single]
    · rw [sub_mul, mul_sub, single_mul_Jm_comm hab, single_mul_Jm_comm hab.symm]
  have hX2 : inK ε (Complex.I • (Matrix.single a b (1 : ℂ) + Matrix.single b a 1)) := by
    apply inK_of_skew_comm
    · simp [Matrix.conjTranspose_add, Matrix.conjTranspose_single, add_comm,
        Matrix.single_neg]
    · rw [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, single_mul_Jm_comm hab,
        single_mul_Jm_comm hab.symm]
  have hI : -Complex.I / 2 * Complex.I = 1 / 2 := by
    rw [div_mul_eq_mul_div, neg_mul, Complex.I_mul_I]
    norm_num
  have hdec : Matrix.single a b (1 : ℂ) =
      (1 / 2 : ℂ) • (Matrix.single a b (1 : ℂ) - Matrix.single b a 1) +
        (-Complex.I / 2) • (Complex.I • (Matrix.single a b (1 : ℂ) + Matrix.single b a 1)) := by
    rw [smul_smul, hI]
    module
  rw [hdec, map_add, map_smul, map_smul, _root_.add_apply,
    _root_.smul_apply, _root_.smul_apply]
  exact W.add_mem (W.smul_mem _ (hK _ hX1 v hv)) (W.smul_mem _ (hK _ hX2 v hv))

/- English proof (translation)
Introduce `k v hv`. Take `⟨Y, hY, hk⟩` from `R.op_eq_exp k`. Rewrite using `[hk]`. Use `exp_mem_of_stable W (R.dτ Y) ?_ v hv` and prove the remaining obligations. Introduce `w hw`.

Rewrite using `[Matrix.matrix_eq_sum_single Y]`. Simplify using `only [map_sum, FunLike.coe_sum, Finset.sum_apply]`. Use `W.sum_mem fun a _ => W.sum_mem fun b _ => ?_` and prove the remaining obligations. Distinguish the cases in `hab : ε a = ε b`. Rewrite using `[show Matrix.single a b (Y a b) = Y a b • Matrix.single a b 1 by`.

Rewrite using `[Matrix.smul_single, smul_eq_mul, mul_one],`. Use the proof step `map_smul, _root_.smul_apply]`. Conclude with `W.smul_mem _ (hW a b hab w hw)`. Rewrite using `[inK_entry_eq_zero hY hab, Matrix.single_zero, map_zero]`. Conclude with `W.zero_mem`.
-/
theorem KRep.stable_of_dτ_stable {ε : Fin n → Bool} (R : KRep ε) (W : Submodule ℂ R.V)
    (hW : ∀ a b, ε a = ε b → ∀ v ∈ W, R.dτ (Matrix.single a b 1) v ∈ W) :
    ∀ k : KG ε, ∀ v ∈ W, R.op k v ∈ W := by
  intro k v hv
  obtain ⟨Y, hY, hk⟩ := R.op_eq_exp k
  rw [hk]
  refine exp_mem_of_stable W (R.dτ Y) ?_ v hv
  intro w hw
  rw [Matrix.matrix_eq_sum_single Y]
  simp only [map_sum, FunLike.coe_sum, Finset.sum_apply]
  refine W.sum_mem fun a _ => W.sum_mem fun b _ => ?_
  by_cases hab : ε a = ε b
  · rw [show Matrix.single a b (Y a b) = Y a b • Matrix.single a b 1 by
        rw [Matrix.smul_single, smul_eq_mul, mul_one],
      map_smul, _root_.smul_apply]
    exact W.smul_mem _ (hW a b hab w hw)
  · rw [inK_entry_eq_zero hY hab, Matrix.single_zero, map_zero]
    exact W.zero_mem

/- English proof (translation)
Introduce `n ε R W`. Prove the components needed by the constructor for the conclusion. Introduce `h a b hab x hx`. Conclude with `R.dτ_stable_of_stable W h a b hab x hx`. Introduce `h`.

Conclude with `R.stable_of_dτ_stable W (fun a b hab x hx => h a b hab x hx)`.
-/
theorem kRepStable : KRepStableStatement := by
  intro n ε R W
  constructor
  · intro h a b hab x hx
    exact R.dτ_stable_of_stable W h a b hab x hx
  · intro h
    exact R.stable_of_dτ_stable W (fun a b hab x hx => h a b hab x hx)

end ReciprocityTheory.ChartRestriction.DS.HW
