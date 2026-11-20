import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushLoc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushQ

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace GlobalTheory.HypChartPf

open PI.RhsWLim PI.RhsWLim.W

/- English proof (translation)
Use extensionality with `a`. Simplify using `[qFw, kapT, Complex.re_add_im]`. Simplify using `[qFw, kapT]`.
-/
private lemma ofLp_qFw_kapT (k : ℕ) (v : (Fin k → ℂ) × ℂ) :
    WithLp.ofLp (qFw k (kapT k v)) = (WithLp.toLp 2 v.1, Complex.arg v.2) := by
  ext a
  · simp [qFw, kapT, Complex.re_add_im]
  · simp [qFw, kapT]

/- English proof (translation)
Simplify using `only [hypS, Set.mem_ofPred_eq] at hv`. Establish `hn : ‖(WithLp.toLp 2 v.1 : EuclideanSpace ℂ (Fin k))‖ ^ 2 + T' = ‖v.2‖ ^ 2`. Rewrite using `[← normSq_sum_eq, ← Complex.normSq_eq_norm_sq]`. Simplify using `only []`. Combine the linear equalities and inequalities to obtain the conclusion.

Simplify using `only [hypPar, hn, Real.sqrt_sq (norm_nonneg _), Complex.norm_mul_exp_arg_mul_I, ]`.
-/
private lemma hypPar_toLp_arg_of_mem_hypS (k : ℕ) (T' : ℝ) (v : (Fin k → ℂ) × ℂ) (hv : v ∈ hypS k T') :
    hypPar k T' (WithLp.toLp 2 v.1, Complex.arg v.2) = v := by
  simp only [hypS, Set.mem_ofPred_eq] at hv
  have hn : ‖(WithLp.toLp 2 v.1 : EuclideanSpace ℂ (Fin k))‖ ^ 2 + T' = ‖v.2‖ ^ 2 := by
    rw [← normSq_sum_eq, ← Complex.normSq_eq_norm_sq]
    simp only []
    linarith
  simp only [hypPar, hn, Real.sqrt_sq (norm_nonneg _), Complex.norm_mul_exp_arg_mul_I, ]

/- English proof (translation)
Use extensionality with `o`. Break down `o with _ | ⟨a, b⟩` into its components or cases. Simplify using `only [kapT, hypPar]`. Simplify using `only [qFw] at hx ⊢`. Simplify using `only [WithLp.equiv_symm_apply, WithLp.ofLp_toLp]`.

Rewrite using `[Complex.arg_real_mul _ (Real.sqrt_pos.2 (add_pos_of_nonneg_of_pos (sq_nonneg _) hT')), Complex.exp_mul_I, Complex.arg_cos_add_sin_mul_I hx]`. Apply the tactic sequence `cases b <;> simp [kapT, hypPar, qFw]`.
-/
private lemma kapT_hypPar_ofLp_qFw (k : ℕ) (T' : ℝ) (hT' : 0 < T') (x : TrE k)
    (hx : (WithLp.ofLp (qFw k x)).2 ∈ Set.Ioc (-Real.pi) Real.pi) :
    kapT k (hypPar k T' (WithLp.ofLp (qFw k x))) = x := by
  ext o
  rcases o with _ | ⟨a, b⟩
  · simp only [kapT, hypPar]
    simp only [qFw] at hx ⊢
    simp only [WithLp.equiv_symm_apply, WithLp.ofLp_toLp]
    rw [Complex.arg_real_mul _ (Real.sqrt_pos.2 (add_pos_of_nonneg_of_pos (sq_nonneg _) hT')),
      Complex.exp_mul_I, Complex.arg_cos_add_sin_mul_I hx]
  · cases b <;> simp [kapT, hypPar, qFw]

/- English proof (translation)
Establish `hpos : (0 : ℝ) < 2 * Real.pi` using `by positivity`. Establish `h1` using `isAddFundamentalDomain_Ioc hpos 0 (volume : Measure ℝ)`. Establish `h2` using `isAddFundamentalDomain_Ioc hpos (-Real.pi) (volume : Measure ℝ)`. Rewrite `h1` using `[zero_add]`. Rewrite `h2` using `[show -Real.pi + 2 * Real.pi = Real.pi by ring]`.

Establish `key : ∀ n : ℤ, ∀ x, n • (2 * Real.pi) + x ∈ A ↔ x ∈ A`. Introduce `n`. Proceed by induction on `n using Int.induction_on with`. Consider the case `zero => intro x`. Simplify using the standard rewrite rules.

Consider the case `succ m ih`. Introduce `x`. Rewrite using `[← ih x, ← hp ((m : ℤ) • (2 * Real.pi) + x)]`. Rewrite using `[show ((m : ℤ) + 1) • (2 * Real.pi) + x = (m : ℤ) • (2 * Real.pi) + x + 2 * Real.pi by`. Rewrite using `[add_smul, one_smul]`.

Use the proof step `abel]`. Consider the case `pred m ih`. Introduce `x`. Establish `h` using `hp ((-(m : ℤ) - 1) • (2 * Real.pi) + x)`. Rewrite using `[show (-(m : ℤ) - 1) • (2 * Real.pi) + x + 2 * Real.pi = (-(m : ℤ)) • (2 * Real.pi) + x by`.

Rewrite using `[sub_smul, one_smul]`. Use the proof step `abel, ih x] at h`. Conclude with `h.symm`. Rewrite using `[Measure.restrict_apply hA, Measure.restrict_apply hA]`. Use `h1.measure_set_eq h2 hA ?_` and prove the remaining obligations.

Introduce and unpack `⟨g, hg⟩`. Take `⟨n, rfl⟩` from `AddSubgroup.mem_zmultiples_iff.mp hg`. Use extensionality with `x`. Conclude with `key n x`.
-/
theorem restrict_periodic (A : Set ℝ) (hA : MeasurableSet A) (hp : ∀ x, x + 2 * Real.pi ∈ A ↔ x ∈ A) :
    volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)) A = volume.restrict (Set.Ioc (-Real.pi) Real.pi) A := by
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h1 := isAddFundamentalDomain_Ioc hpos 0 (volume : Measure ℝ)
  have h2 := isAddFundamentalDomain_Ioc hpos (-Real.pi) (volume : Measure ℝ)
  rw [zero_add] at h1
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at h2
  have key : ∀ n : ℤ, ∀ x, n • (2 * Real.pi) + x ∈ A ↔ x ∈ A := by
    intro n
    induction n using Int.induction_on with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [← ih x, ← hp ((m : ℤ) • (2 * Real.pi) + x)]
      rw [show ((m : ℤ) + 1) • (2 * Real.pi) + x = (m : ℤ) • (2 * Real.pi) + x + 2 * Real.pi by
        rw [add_smul, one_smul]; abel]
    | pred m ih =>
      intro x
      have h := hp ((-(m : ℤ) - 1) • (2 * Real.pi) + x)
      rw [show (-(m : ℤ) - 1) • (2 * Real.pi) + x + 2 * Real.pi = (-(m : ℤ)) • (2 * Real.pi) + x by
        rw [sub_smul, one_smul]; abel, ih x] at h
      exact h.symm
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
  refine h1.measure_set_eq h2 hA ?_
  rintro ⟨g, hg⟩
  obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hg
  ext x
  exact key n x

/- English proof (translation)
Establish `hmeas : Measurable (hypPar k T')` using `(continuous_hypPar k T').measurable`. Establish `hP : MeasurableSet (hypPar k T' ⁻¹' E)` using `hmeas hE`. Unfold `hypM`. Rewrite using `[Measure.smul_apply, Measure.map_apply hmeas hE, smul_eq_mul]`. Use `congr 1`.

Rewrite using `[Measure.prod_apply hP, Measure.prod_apply (hP.inter (MeasurableSet.univ.prod measurableSet_Ioc))]`. Use `lintegral_congr (fun y => ?_)` and prove the remaining obligations. Establish `hs : MeasurableSet (Prod.mk y ⁻¹' (hypPar k T' ⁻¹' E))` using `measurable_prodMk_left hP`. Rewrite using `[restrict_periodic _ hs ?_, Measure.restrict_apply hs]`. Use `congr 1`.

Use extensionality with `θ`. Simplify using the standard rewrite rules. Introduce `x`. Establish `e : hypPar k T' (y, x + 2 * Real.pi) = hypPar k T' (y, x)`. Simplify using `only [hypPar, Prod.mk.injEq, true_and]`.

Rewrite using `[show ((x + 2 * Real.pi : ℝ) : ℂ) * Complex.I = (x : ℂ) * Complex.I + 2 * Real.pi * Complex.I by push_cast; ring, Complex.exp_periodic]`. Simplify using `only [Set.mem_preimage]`. Rewrite using `[e]`.
-/
theorem hypM_eq (k : ℕ) (T' : ℝ) (E : Set ((Fin k → ℂ) × ℂ)) (hE : MeasurableSet E) :
    hypM k T' E = (1 / 2) * (volume.prod volume)
      (hypPar k T' ⁻¹' E ∩ Set.univ ×ˢ Set.Ioc (-Real.pi) Real.pi) := by
  have hmeas : Measurable (hypPar k T') := (continuous_hypPar k T').measurable
  have hP : MeasurableSet (hypPar k T' ⁻¹' E) := hmeas hE
  unfold hypM
  rw [Measure.smul_apply, Measure.map_apply hmeas hE, smul_eq_mul]
  congr 1
  rw [Measure.prod_apply hP, Measure.prod_apply (hP.inter (MeasurableSet.univ.prod measurableSet_Ioc))]
  refine lintegral_congr (fun y => ?_)
  have hs : MeasurableSet (Prod.mk y ⁻¹' (hypPar k T' ⁻¹' E)) := measurable_prodMk_left hP
  rw [restrict_periodic _ hs ?_, Measure.restrict_apply hs]
  · congr 1
    ext θ
    simp
  · intro x
    have e : hypPar k T' (y, x + 2 * Real.pi) = hypPar k T' (y, x) := by
      simp only [hypPar, Prod.mk.injEq, true_and]
      rw [show ((x + 2 * Real.pi : ℝ) : ℂ) * Complex.I = (x : ℂ) * Complex.I + 2 * Real.pi * Complex.I by
        push_cast; ring, Complex.exp_periodic]
    simp only [Set.mem_preimage]
    rw [e]

/- English proof (translation)
Rewrite using `[hypM_eq k T' E hE]`. Use `congr 1`. Establish `hFm : MeasurableSet (hypPar k T' ⁻¹' E ∩ Set.univ ×ˢ Set.Ioc (-Real.pi) Real.pi)` using `((continuous_hypPar k T').measurable hE).inter (MeasurableSet.univ.prod measurableSet_Ioc)`. Establish `hset : kapT k '' E = (fun x : TrE k => WithLp.ofLp (qFw k x)) ⁻¹' (hypPar k T' ⁻¹' E ∩ Set.univ ×ˢ Set.Ioc (-Real.pi) Real.pi)`. Use extensionality with `x`.

Simplify using `only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, rfl⟩`. Rewrite using `[ofLp_qFw_kapT k v, hypPar_toLp_arg_of_mem_hypS k T' v (hS hv)]`. Conclude with `⟨hv, Complex.arg_mem_Ioc _⟩`.

Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨_, h1, kapT_hypPar_ofLp_qFw k T' hT' x h2⟩`. Rewrite using `[hset, (qIso_measurePreserving k).measure_preimage hFm.nullMeasurableSet]`.
-/
theorem hypM_eq_kapT (k : ℕ) (T' : ℝ) (hT' : 0 < T') (E : Set ((Fin k → ℂ) × ℂ)) (hE : MeasurableSet E)
    (hS : E ⊆ hypS k T') : hypM k T' E = (1 / 2) * volume (kapT k '' E) := by
  rw [hypM_eq k T' E hE]
  congr 1
  have hFm : MeasurableSet (hypPar k T' ⁻¹' E ∩ Set.univ ×ˢ Set.Ioc (-Real.pi) Real.pi) :=
    ((continuous_hypPar k T').measurable hE).inter (MeasurableSet.univ.prod measurableSet_Ioc)
  have hset : kapT k '' E =
      (fun x : TrE k => WithLp.ofLp (qFw k x)) ⁻¹' (hypPar k T' ⁻¹' E ∩ Set.univ ×ˢ Set.Ioc (-Real.pi) Real.pi) := by
    ext x
    simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and]
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [ofLp_qFw_kapT k v, hypPar_toLp_arg_of_mem_hypS k T' v (hS hv)]
      exact ⟨hv, Complex.arg_mem_Ioc _⟩
    · rintro ⟨h1, h2⟩
      exact ⟨_, h1, kapT_hypPar_ofLp_qFw k T' hT' x h2⟩
  rw [hset, (qIso_measurePreserving k).measure_preimage hFm.nullMeasurableSet]

def sgn (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if r ≤ i.val ∧ i.val < r + k then 1 else if i.val = r + k then -1 else 0

/- English proof (translation)
Use `show _ = _`. Use extensionality with `i j`. Rewrite using `[Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.neg_apply]`. Unfold `opGen sgn`. Apply the tactic sequence `split_ifs <;> (try (exfalso; omega)) <;> simp`.
-/
theorem gen_semiconj (k r : ℕ) (q : TrE k) :
    SemiconjBy (Matrix.diagonal (sgn k r)) (-opGen k r q) (opGen k r q)ᴴ := by
  show _ = _
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.neg_apply]
  unfold opGen sgn
  split_ifs <;> (try (exfalso; omega)) <;> simp

/- English proof (translation)
Establish `hdet : IsUnit U.det` using `(Matrix.isUnit_iff_isUnit_det U).mp hU`. Establish `h1 : Xᴴ = U * -X * U⁻¹` using `by rw [h, Matrix.mul_nonsing_inv_cancel_right _ _ hdet]`. Establish `h3 : NormedSpace.exp (-X) * NormedSpace.exp X = 1`. Rewrite using `[← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl X)), neg_add_cancel, NormedSpace.exp_zero]`. Rewrite using `[← Matrix.exp_conjTranspose, h1, Matrix.exp_conj _ _ hU]`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[Matrix.nonsing_inv_mul_cancel_left _ _ hdet, h3, Matrix.mul_one]`.
-/
private lemma exp_conjTranspose_mul_mul_exp_of_skew {n : Type*} [Fintype n] [DecidableEq n] (U X : Matrix n n ℂ)
    (hU : IsUnit U) (h : U * -X = Xᴴ * U) : (NormedSpace.exp X)ᴴ * U * NormedSpace.exp X = U := by
  have hdet : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det U).mp hU
  have h1 : Xᴴ = U * -X * U⁻¹ := by rw [h, Matrix.mul_nonsing_inv_cancel_right _ _ hdet]
  have h3 : NormedSpace.exp (-X) * NormedSpace.exp X = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl X)), neg_add_cancel,
      NormedSpace.exp_zero]
  rw [← Matrix.exp_conjTranspose, h1, Matrix.exp_conj _ _ hU]
  simp only [Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ hdet, h3, Matrix.mul_one]

/- English proof (translation)
Establish `hsemi` using `gen_semiconj k r q`. Unfold `SemiconjBy at hsemi`. Establish `hent : ∀ i j, sgn k r i * -opGen k r q i j = star (opGen k r q j i) * sgn k r j`. Introduce `i j`. Use `congrFun (congrFun hsemi i) j` as an intermediate fact.

Rewrite `this` using `[Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.neg_apply]`. Then use the resulting hypothesis. Establish `hz : ∀ i j, sgn k r i = 0 → opGen k r q i j = 0 ∧ opGen k r q j i = 0`. Introduce `i j hi`. Unfold `sgn at hi`. Use `split_ifs at hi with h1 h2`.

Evaluate the numerical expressions using `at hi`. Evaluate the numerical expressions using `at hi`. Unfold `opGen`. Apply the tactic sequence `constructor <;> split_ifs <;> rfl`. Apply `exp_conjTranspose_mul_mul_exp_of_skew` to reduce the goal to its premises.

Use `(Matrix.isUnit_iff_isUnit_det _).2 ?_` and prove the remaining obligations. Rewrite using `[Matrix.det_diagonal]`. Use `isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => ?_)` and prove the remaining obligations. Use `split_ifs with h`. Conclude with `hu`.

Conclude with `h`. Use extensionality with `i j`. Rewrite using `[Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.neg_apply]`. Distinguish the cases in `hi : sgn k r i = 0`. Take `⟨h1, h2⟩` from `hz i j hi`.

Simplify using `[h1, h2]`. Distinguish the cases in `hj : sgn k r j = 0`. Take `⟨h1, h2⟩` from `hz j i hj`. Simplify using `[h1, h2]`. Simplify using `only [if_neg hi, if_neg hj]`.

Conclude with `hent i j`.
-/
private lemma exp_opGen_conjTranspose_mul_diagonal_mul (k r : ℕ) (q : TrE k) (u : ℂ) (hu : u ≠ 0) :
    (NormedSpace.exp (opGen k r q))ᴴ * Matrix.diagonal (fun i => if sgn k r i = 0 then u else sgn k r i) *
      NormedSpace.exp (opGen k r q) = Matrix.diagonal (fun i => if sgn k r i = 0 then u else sgn k r i) := by
  have hsemi := gen_semiconj k r q
  unfold SemiconjBy at hsemi
  have hent : ∀ i j, sgn k r i * -opGen k r q i j = star (opGen k r q j i) * sgn k r j := by
    intro i j
    have := congrFun (congrFun hsemi i) j
    rwa [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.neg_apply] at this
  have hz : ∀ i j, sgn k r i = 0 → opGen k r q i j = 0 ∧ opGen k r q j i = 0 := by
    intro i j hi
    unfold sgn at hi
    split_ifs at hi with h1 h2
    · norm_num at hi
    · norm_num at hi
    · unfold opGen
      constructor <;> split_ifs <;> rfl
  apply exp_conjTranspose_mul_mul_exp_of_skew
  · refine (Matrix.isUnit_iff_isUnit_det _).2 ?_
    rw [Matrix.det_diagonal]
    refine isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => ?_)
    split_ifs with h
    · exact hu
    · exact h
  · ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.neg_apply]
    by_cases hi : sgn k r i = 0
    · obtain ⟨h1, h2⟩ := hz i j hi
      simp [h1, h2]
    by_cases hj : sgn k r j = 0
    · obtain ⟨h1, h2⟩ := hz j i hj
      simp [h1, h2]
    simp only [if_neg hi, if_neg hj]
    exact hent i j

/- English proof (translation)
Establish `hD : Matrix.diagonal (sgn k r) = (1 / 2 : ℂ) • (Matrix.diagonal (fun i => if sgn k r i = 0 then 1 else sgn k r i) + Matrix.diagonal (fun i => if sgn k r i = 0 then -1 else sgn k r i))`. Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `only [Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]`.

Apply the tactic sequence `split_ifs with h <;> [rw [h]; skip] <;> ring`. Simplify using `[Matrix.diagonal_apply_ne _ hij]`. Rewrite using `[hD, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, exp_opGen_conjTranspose_mul_diagonal_mul k r q 1 one_ne_zero, exp_opGen_conjTranspose_mul_diagonal_mul k r q (-1) (neg_ne_zero.2 one_ne_zero)]`.
-/
theorem exp_form (k r : ℕ) (q : TrE k) :
    (NormedSpace.exp (opGen k r q))ᴴ * Matrix.diagonal (sgn k r) * NormedSpace.exp (opGen k r q) =
      Matrix.diagonal (sgn k r) := by
  have hD : Matrix.diagonal (sgn k r) = (1 / 2 : ℂ) •
      (Matrix.diagonal (fun i => if sgn k r i = 0 then 1 else sgn k r i) +
        Matrix.diagonal (fun i => if sgn k r i = 0 then -1 else sgn k r i)) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
      split_ifs with h <;> [rw [h]; skip] <;> ring
    · simp [Matrix.diagonal_apply_ne _ hij]
  rw [hD, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
    exp_opGen_conjTranspose_mul_diagonal_mul k r q 1 one_ne_zero, exp_opGen_conjTranspose_mul_diagonal_mul k r q (-1) (neg_ne_zero.2 one_ne_zero)]

/- English proof (translation)
Introduce `a b h`. Use `ext`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `[wI] at this`. Use linear arithmetic over natural numbers and integers.
-/
private lemma wI_injective' (k r : ℕ) : Function.Injective (wI k r) := by
  intro a b h
  ext
  have := congrArg Fin.val h
  simp [wI] at this
  omega

/- English proof (translation)
Establish `hs : star v ⬝ᵥ (Matrix.diagonal (sgn k r) *ᵥ v) = ∑ j : Fin (k + 1), star (v (wI k r j)) * (sgn k r (wI k r j) * v (wI k r j))`. Simplify using `only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]`. Use `symm`. Use `Fintype.sum_of_injective _ (wI_injective' k r) _ (fun i => star (v i) * (sgn k r i * v i)) ?_ (fun _ => rfl)` and prove the remaining obligations. Introduce `i hi`.

Establish `: sgn k r i = 0`. Unfold `sgn`. Rewrite using `[if_neg, if_neg]`. Introduce `h; exact hi ⟨⟨i.val - r, by omega⟩, by ext; simp [wI]; omega⟩`. Introduce and unpack `⟨h1, h2⟩; exact hi ⟨⟨i.val - r, by omega⟩, by ext; simp [wI]; omega⟩`.

Simplify using `[this]`. Establish `h1 : ∀ j : Fin k, sgn k r (wI k r j.castSucc) = 1`. Introduce `j`. Unfold `sgn`. Rewrite using `[if_pos]`.

Simplify using `[wI]`. Establish `h2 : sgn k r (wI k r (Fin.last k)) = -1`. Apply the tactic sequence `unfold sgn; rw [if_neg, if_pos] <;> simp [wI]`. Rewrite using `[hs, Fin.sum_univ_castSucc, h2]`. Simplify using `only [h1, opCo]`.

Use `push_cast`. Simplify using `[Complex.normSq_eq_conj_mul_self, sub_eq_add_neg]`.
-/
theorem form_eq (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) :
    star v ⬝ᵥ (Matrix.diagonal (sgn k r) *ᵥ v) =
      ((∑ i, Complex.normSq ((opCo k r v).1 i) - Complex.normSq (opCo k r v).2 : ℝ) : ℂ) := by
  have hs : star v ⬝ᵥ (Matrix.diagonal (sgn k r) *ᵥ v) =
      ∑ j : Fin (k + 1), star (v (wI k r j)) * (sgn k r (wI k r j) * v (wI k r j)) := by
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
    symm
    refine Fintype.sum_of_injective _ (wI_injective' k r) _ (fun i => star (v i) * (sgn k r i * v i)) ?_ (fun _ => rfl)
    intro i hi
    have : sgn k r i = 0 := by
      unfold sgn
      rw [if_neg, if_neg]
      · intro h; exact hi ⟨⟨i.val - r, by omega⟩, by ext; simp [wI]; omega⟩
      · rintro ⟨h1, h2⟩; exact hi ⟨⟨i.val - r, by omega⟩, by ext; simp [wI]; omega⟩
    simp [this]
  have h1 : ∀ j : Fin k, sgn k r (wI k r j.castSucc) = 1 := by
    intro j; unfold sgn; rw [if_pos]; simp [wI]
  have h2 : sgn k r (wI k r (Fin.last k)) = -1 := by
    unfold sgn; rw [if_neg, if_pos] <;> simp [wI]
  rw [hs, Fin.sum_univ_castSucc, h2]
  simp only [h1, opCo]
  push_cast
  simp [Complex.normSq_eq_conj_mul_self, sub_eq_add_neg]

/- English proof (translation)
Introduce and unpack `p ⟨q, -, rfl⟩`. Establish `hq : star (NormedSpace.exp (opGen k r q) *ᵥ opBase k r T') ⬝ᵥ (Matrix.diagonal (sgn k r) *ᵥ (NormedSpace.exp (opGen k r q) *ᵥ opBase k r T')) = star (opBase k r T') ⬝ᵥ (Matrix.diagonal (sgn k r) *ᵥ opBase k r T')`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, exp_form]`. Rewrite `hq` using `[form_eq, form_eq]`. Establish `hb : ∀ i : Fin k, opBase k r T' (wI k r i.castSucc) = 0`.

Introduce `i`. Establish `hne : wI k r i.castSucc ≠ wI k r (Fin.last k)` using `fun h => (Fin.castSucc_lt_last i).ne (wI_injective' k r h)`. Simplify using `[opBase, wLast, bvec, hne]`. Establish `hl : opBase k r T' (wI k r (Fin.last k)) = (Real.sqrt T' : ℂ)`. Simplify using `[opBase, wLast, bvec]`.

Simplify using `only [opCo, hb, hl, map_zero, Finset.sum_const_zero, Complex.normSq_ofReal, Real.mul_self_sqrt hT'.le] at hq`. Simplify using `only [hypS, Set.mem_ofPred_eq, opCo]`. Combine the linear relations using `[Complex.ofReal_injective hq]`.
-/
theorem opE_subset (k r : ℕ) (T' : ℝ) (hT' : 0 < T') (ρ : ℝ) : opE k r T' ρ ⊆ hypS k T' := by
  rintro p ⟨q, -, rfl⟩
  have hq : star (NormedSpace.exp (opGen k r q) *ᵥ opBase k r T') ⬝ᵥ
      (Matrix.diagonal (sgn k r) *ᵥ (NormedSpace.exp (opGen k r q) *ᵥ opBase k r T')) =
      star (opBase k r T') ⬝ᵥ (Matrix.diagonal (sgn k r) *ᵥ opBase k r T') := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, exp_form]
  rw [form_eq, form_eq] at hq
  have hb : ∀ i : Fin k, opBase k r T' (wI k r i.castSucc) = 0 := by
    intro i
    have hne : wI k r i.castSucc ≠ wI k r (Fin.last k) := fun h => (Fin.castSucc_lt_last i).ne (wI_injective' k r h)
    simp [opBase, wLast, bvec, hne]
  have hl : opBase k r T' (wI k r (Fin.last k)) = (Real.sqrt T' : ℂ) := by
    simp [opBase, wLast, bvec]
  simp only [opCo, hb, hl, map_zero, Finset.sum_const_zero, Complex.normSq_ofReal,
    Real.mul_self_sqrt hT'.le] at hq
  simp only [hypS, Set.mem_ofPred_eq, opCo]
  linarith [Complex.ofReal_injective hq]

/- English proof (translation)
Unfold `HypChart`. Introduce `k r T' hk hT'`. Use `⟨1, one_pos, fun ρ _ _ => ?_⟩` and prove the remaining obligations. Establish `himg : phiT k r T' '' Metric.ball 0 ρ = kapT k '' opE k r T' ρ`. Rewrite using `[opE, Set.image_image]`.

Both sides reduce to the same expression. Rewrite using `[himg, hypM_eq_kapT k T' hT' _ (opEMeas k r T' ρ) (opE_subset k r T' hT' ρ)]`.
-/
theorem hypChart : HypChart := by
  unfold HypChart
  intro k r T' hk hT'
  refine ⟨1, one_pos, fun ρ _ _ => ?_⟩
  have himg : phiT k r T' '' Metric.ball 0 ρ = kapT k '' opE k r T' ρ := by
    rw [opE, Set.image_image]; rfl
  rw [himg, hypM_eq_kapT k T' hT' _ (opEMeas k r T' ρ) (opE_subset k r T' hT' ρ)]

end GlobalTheory.HypChartPf
