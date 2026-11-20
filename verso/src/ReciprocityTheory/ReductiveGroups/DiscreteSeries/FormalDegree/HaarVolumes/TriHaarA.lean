import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriDens

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.UpperTriangularMatrices

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

def IsUpT (M : Matrix (Fin N) (Fin N) ℂ) : Prop := ∀ a b, b < a → M a b = 0

/- English proof (translation)
Introduce `a b h`. Simplify using `[upMat, ne_of_gt h, not_lt.mpr h.le]`.
-/
theorem upMat_isUpT (t : TriCo N) : IsUpT (upMat t) := by
  intro a b h
  simp [upMat, ne_of_gt h, not_lt.mpr h.le]

/- English proof (translation)
Simplify using `[upMat]`.
-/
theorem upMat_diag (t : TriCo N) (a : Fin N) : upMat t a a = ((t.1 a : ℝ) : ℂ) := by
  simp [upMat]

/- English proof (translation)
Simplify using `[upMat, h.ne, h]`.
-/
theorem upMat_lt (t : TriCo N) {a b : Fin N} (h : a < b) : upMat t a b = t.2 ⟨(a, b), h⟩ := by
  simp [upMat, h.ne, h]

/- English proof (translation)
Introduce `a b h`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Break down `lt_or_ge k a with hk | hk` into its components or cases. Rewrite using `[hA a k hk, zero_mul]`.

Rewrite using `[hB k b (lt_of_lt_of_le h hk), mul_zero]`.
-/
theorem isUpT_mul {A B : Matrix (Fin N) (Fin N) ℂ} (hA : IsUpT A) (hB : IsUpT B) : IsUpT (A * B) := by
  intro a b h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge k a with hk | hk
  · rw [hA a k hk, zero_mul]
  · rw [hB k b (lt_of_lt_of_le h hk), mul_zero]

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single a]`. Introduce `k _ hk`. Break down `lt_or_gt_of_ne hk with hk | hk` into its components or cases. Rewrite using `[hA a k hk, zero_mul]`. Rewrite using `[hB k a hk, mul_zero]`.

Simplify using the standard rewrite rules.
-/
theorem isUpT_mul_diag {A B : Matrix (Fin N) (Fin N) ℂ} (hA : IsUpT A) (hB : IsUpT B) (a : Fin N) :
    (A * B) a a = A a a * B a a := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hk | hk
    · rw [hA a k hk, zero_mul]
    · rw [hB k a hk, mul_zero]
  · simp

/- English proof (translation)
Use extensionality with `a b`. Break down `lt_trichotomy a b with h | h | h` into its components or cases. Rewrite using `[upMat_lt _ h]`. Both sides reduce to the same expression. Substitute `h` using the available equality.

Rewrite using `[upMat_diag]`. Simplify using `only [triCoOf]`. Conclude with `Complex.ext (by simp) (by simp [hd])`. Rewrite using `[upMat_isUpT _ a b h, hM a b h]`.
-/
theorem upMat_triCoOf_of {M : Matrix (Fin N) (Fin N) ℂ} (hM : IsUpT M) (hd : ∀ a, (M a a).im = 0) :
    upMat (triCoOf M) = M := by
  ext a b
  rcases lt_trichotomy a b with h | h | h
  · rw [upMat_lt _ h]; rfl
  · subst h; rw [upMat_diag]; simp only [triCoOf]
    exact Complex.ext (by simp) (by simp [hd])
  · rw [upMat_isUpT _ a b h, hM a b h]

/- English proof (translation)
Use extensionality with `j`. Simplify using `[triCoOf, upMat]`. Simplify using `only [triCoOf]`. Rewrite using `[upMat_lt _ j.2]`.
-/
theorem triCoOf_upMat (t : TriCo N) : triCoOf (upMat t) = t := by
  ext j
  · simp [triCoOf, upMat]
  · simp only [triCoOf]; rw [upMat_lt _ j.2]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [upMat, Matrix.add_apply, Prod.fst_add, Prod.snd_add, Pi.add_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem upMat_add (s t : TriCo N) : upMat (s + t) = upMat s + upMat t := by
  ext a b; simp only [upMat, Matrix.add_apply, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  split_ifs <;> simp

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [upMat, Matrix.smul_apply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply]`. Apply the tactic sequence `split_ifs <;> simp [Complex.real_smul]`.
-/
theorem upMat_smul (c : ℝ) (t : TriCo N) : upMat (c • t) = c • upMat t := by
  ext a b; simp only [upMat, Matrix.smul_apply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply]
  split_ifs <;> simp [Complex.real_smul]

/- English proof (translation)
Apply the tactic sequence `ext j <;> simp [triCoOf]`.
-/
theorem triCoOf_add (A B : Matrix (Fin N) (Fin N) ℂ) : triCoOf (A + B) = triCoOf A + triCoOf B := by
  ext j <;> simp [triCoOf]

/- English proof (translation)
Apply the tactic sequence `ext j <;> simp [triCoOf]`.
-/
theorem triCoOf_smul (c : ℝ) (A : Matrix (Fin N) (Fin N) ℂ) : triCoOf (c • A) = c • triCoOf A := by
  ext j <;> simp [triCoOf]

/- English proof (translation)
Introduce `s t h`. Rewrite using `[← triCoOf_upMat s, ← triCoOf_upMat t, h]`.
-/
theorem upMat_injective : Function.Injective (upMat (N := N)) := by
  intro s t h
  rw [← triCoOf_upMat s, ← triCoOf_upMat t, h]

def rmulL (B : Matrix (Fin N) (Fin N) ℂ) : TriCo N →ₗ[ℝ] TriCo N where
  toFun t := triCoOf (upMat t * B)
  map_add' s t := by rw [upMat_add, Matrix.add_mul, triCoOf_add]
  map_smul' c t := by rw [upMat_smul, Matrix.smul_mul, triCoOf_smul]; rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rmulL_apply (B : Matrix (Fin N) (Fin N) ℂ) (t : TriCo N) :
    rmulL B t = triCoOf (upMat t * B) := rfl

/- English proof (translation)
Apply the tactic sequence `ext j <;> simp [triCoOf]`.
-/
theorem triCoOf_sub (A B : Matrix (Fin N) (Fin N) ℂ) : triCoOf (A - B) = triCoOf A - triCoOf B := by
  ext j <;> simp [triCoOf]

/- English proof (translation)
Apply the tactic sequence `ext a b; simp only [upMat, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply]; split_ifs <;> simp`.
-/
theorem upMat_zero : upMat (0 : TriCo N) = 0 := by
  ext a b; simp only [upMat, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply]; split_ifs <;> simp

/- English proof (translation)
Break down `lt_trichotomy a b with hab | hab | hab` into its components or cases. Rewrite using `[upMat_lt _ hab]`. Conclude with `h`. Substitute `hab` using the available equality. Rewrite using `[upMat_diag]`.

Simplify using `[triCoOf, h]`. Conclude with `upMat_isUpT _ a b hab`.
-/
theorem upMat_triCoOf_eq_zero {X : Matrix (Fin N) (Fin N) ℂ} {a b : Fin N} (h : X a b = 0) :
    upMat (triCoOf X) a b = 0 := by
  rcases lt_trichotomy a b with hab | hab | hab
  · rw [upMat_lt _ hab]; exact h
  · subst hab; rw [upMat_diag]; simp [triCoOf, h]
  · exact upMat_isUpT _ a b hab

/- English proof (translation)
Use `set Nl : Module.End ℝ (TriCo N) := 1 - rmulL U with hNl`. Establish `hN : ∀ s, Nl s = triCoOf (upMat s * (1 - U))`. Introduce `s`. Rewrite using `[Matrix.mul_sub, Matrix.mul_one, triCoOf_sub, triCoOf_upMat, hNl]`. Both sides reduce to the same expression.

Establish `hpow : ∀ k s, ∀ a b : Fin N, (b : ℕ) < a + k → upMat ((Nl ^ k) s) a b = 0`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro s a b h; exact upMat_isUpT _ a b (by simpa using h)`. Consider the case `succ k ih`.

Introduce `s a b h`. Rewrite using `[pow_succ', Module.End.mul_apply, hN]`. Apply `upMat_triCoOf_eq_zero` to reduce the goal to its premises. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hc : (c : ℕ) < a + k`. Rewrite using `[ih s a c hc, zero_mul]`. Rewrite using `[hU c b (by rw [Fin.le_def]; omega), mul_zero]`. Establish `hnil : IsNilpotent Nl`. Use `⟨N, LinearMap.ext fun s => ?_⟩` and prove the remaining obligations.

Apply `upMat_injective` to reduce the goal to its premises. Rewrite using `[LinearMap.zero_apply, upMat_zero]`. Use extensionality with `a b`. Conclude with `hpow N s a b (by omega)`. Establish `h1` using `LinearMap.eval_charpoly Nl 1`.

Rewrite `h1` using `[hnil.charpoly_eq_X_pow_finrank]`. Simplify using `only [Polynomial.eval_pow, Polynomial.eval_X, one_pow, map_one] at h1`. Rewrite using `[h1, hNl, sub_sub_cancel]`.
-/
theorem det_rmulL_unip (U : Matrix (Fin N) (Fin N) ℂ) (hU : ∀ c b, b ≤ c → (1 - U) c b = 0) :
    LinearMap.det (rmulL U) = 1 := by
  set Nl : Module.End ℝ (TriCo N) := 1 - rmulL U with hNl
  have hN : ∀ s, Nl s = triCoOf (upMat s * (1 - U)) := by
    intro s
    rw [Matrix.mul_sub, Matrix.mul_one, triCoOf_sub, triCoOf_upMat, hNl]
    rfl
  have hpow : ∀ k s, ∀ a b : Fin N, (b : ℕ) < a + k → upMat ((Nl ^ k) s) a b = 0 := by
    intro k
    induction k with
    | zero => intro s a b h; exact upMat_isUpT _ a b (by simpa using h)
    | succ k ih =>
      intro s a b h
      rw [pow_succ', Module.End.mul_apply, hN]
      apply upMat_triCoOf_eq_zero
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hc : (c : ℕ) < a + k
      · rw [ih s a c hc, zero_mul]
      · rw [hU c b (by rw [Fin.le_def]; omega), mul_zero]
  have hnil : IsNilpotent Nl := by
    refine ⟨N, LinearMap.ext fun s => ?_⟩
    apply upMat_injective
    rw [LinearMap.zero_apply, upMat_zero]
    ext a b
    exact hpow N s a b (by omega)
  have h1 := LinearMap.eval_charpoly Nl 1
  rw [hnil.charpoly_eq_X_pow_finrank] at h1
  simp only [Polynomial.eval_pow, Polynomial.eval_X, one_pow, map_one] at h1
  rw [h1, hNl, sub_sub_cancel]

def scaleL (d : Fin N → ℝ) : TriCo N →ₗ[ℝ] TriCo N :=
  LinearMap.prodMap (LinearMap.pi fun j => (d j • LinearMap.id).comp (LinearMap.proj j))
    (LinearMap.pi fun ab : {ab : Fin N × Fin N // ab.1 < ab.2} =>
      ((d ab.1.2 • LinearMap.id : ℂ →ₗ[ℝ] ℂ)).comp (LinearMap.proj ab))

/- English proof (translation)
Use extensionality with `j`. Simplify using `[scaleL, triCoOf, Matrix.mul_diagonal, mul_comm]`. Simplify using `[scaleL, triCoOf, Matrix.mul_diagonal, Complex.real_smul, mul_comm]`.
-/
theorem scaleL_triCoOf (d : Fin N → ℝ) (X : Matrix (Fin N) (Fin N) ℂ) :
    scaleL d (triCoOf X) = triCoOf (X * Matrix.diagonal fun j => ((d j : ℝ) : ℂ)) := by
  ext j
  · simp [scaleL, triCoOf, Matrix.mul_diagonal, mul_comm]
  · simp [scaleL, triCoOf, Matrix.mul_diagonal, Complex.real_smul, mul_comm]

/- English proof (translation)
Rewrite using `[← Finset.prod_subtype (univ.filter fun ab : Fin N × Fin N => ab.1 < ab.2) (by simp) (fun ab => f ab.2), Finset.prod_filter, Fintype.prod_prod_type, Finset.prod_comm]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_filter]`. Use `show ∏ a ∈ univ.filter (fun a : Fin N => a < j), f j = _`. Rewrite using `[Finset.prod_const]`.

Establish `: (univ.filter fun a : Fin N => a < j) = Iio j` using `by ext; simp`. Rewrite using `[this, Fin.card_Iio]`.
-/
theorem prod_subtype_snd (f : Fin N → ℝ) :
    ∏ ab : {ab : Fin N × Fin N // ab.1 < ab.2}, f ab.1.2 = ∏ j : Fin N, f j ^ (j : ℕ) := by
  rw [← Finset.prod_subtype (univ.filter fun ab : Fin N × Fin N => ab.1 < ab.2) (by simp)
    (fun ab => f ab.2), Finset.prod_filter, Fintype.prod_prod_type, Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← Finset.prod_filter]
  show ∏ a ∈ univ.filter (fun a : Fin N => a < j), f j = _
  rw [Finset.prod_const]
  have : (univ.filter fun a : Fin N => a < j) = Iio j := by ext; simp
  rw [this, Fin.card_Iio]

/- English proof (translation)
Rewrite using `[scaleL, LinearMap.det_prodMap, LinearMap.det_pi, LinearMap.det_pi]`. Simplify using `only [LinearMap.det_smul, LinearMap.det_id, mul_one, Module.finrank_self, pow_one, Complex.finrank_real_complex]`. Rewrite using `[prod_subtype_snd (fun j => d j ^ 2), ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_scaleL (d : Fin N → ℝ) :
    LinearMap.det (scaleL d) = ∏ j : Fin N, d j ^ (2 * (j : ℕ) + 1) := by
  rw [scaleL, LinearMap.det_prodMap, LinearMap.det_pi, LinearMap.det_pi]
  simp only [LinearMap.det_smul, LinearMap.det_id, mul_one, Module.finrank_self, pow_one,
    Complex.finrank_real_complex]
  rw [prod_subtype_snd (fun j => d j ^ 2), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  ring

def unipOf (t0 : TriCo N) : TriCo N := (fun _ => 1, fun ab => t0.2 ab / ((t0.1 ab.1.2 : ℝ) : ℂ))

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[Matrix.mul_diagonal]`. Break down `lt_trichotomy a b with h | h | h` into its components or cases. Rewrite using `[upMat_lt _ h, upMat_lt _ h]`. Establish `: ((t0.1 b : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast h0 b`.

Simplify using `only [unipOf]`. Clear the denominators using the available nonvanishing facts. Substitute `h` using the available equality. Rewrite using `[upMat_diag, upMat_diag]`. Simplify using `[unipOf]`.

Rewrite using `[upMat_isUpT _ a b h, upMat_isUpT _ a b h, zero_mul]`.
-/
theorem upMat_eq_unip_mul (t0 : TriCo N) (h0 : ∀ j, t0.1 j ≠ 0) :
    upMat t0 = upMat (unipOf t0) * Matrix.diagonal fun j => ((t0.1 j : ℝ) : ℂ) := by
  ext a b
  rw [Matrix.mul_diagonal]
  rcases lt_trichotomy a b with h | h | h
  · rw [upMat_lt _ h, upMat_lt _ h]
    have : ((t0.1 b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h0 b
    simp only [unipOf]
    field_simp
  · subst h; rw [upMat_diag, upMat_diag]; simp [unipOf]
  · rw [upMat_isUpT _ a b h, upMat_isUpT _ a b h, zero_mul]

/- English proof (translation)
Establish `hne : ∀ j, t0.1 j ≠ 0` using `fun j => (h0 j).ne'`. Establish `hc : rmulL (upMat t0) = scaleL t0.1 ∘ₗ rmulL (upMat (unipOf t0))`. Use `LinearMap.ext fun t => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, rmulL_apply, rmulL_apply, scaleL_triCoOf, upMat_eq_unip_mul t0 hne, Matrix.mul_assoc]`. Rewrite using `[hc, LinearMap.det_comp, det_scaleL, det_rmulL_unip, mul_one]`.

Introduce `c b hbc`. Break down `lt_or_eq_of_le hbc with h | h` into its components or cases. Rewrite using `[Matrix.sub_apply, Matrix.one_apply_ne (ne_of_gt h), upMat_isUpT _ c b h, sub_zero]`. Substitute `h` using the available equality. Rewrite using `[Matrix.sub_apply, Matrix.one_apply_eq, upMat_diag]`.

Simplify using `[unipOf]`.
-/
theorem det_rmulL_upMat (t0 : TriCo N) (h0 : t0 ∈ triPos N) :
    LinearMap.det (rmulL (upMat t0)) = ∏ j : Fin N, t0.1 j ^ (2 * (j : ℕ) + 1) := by
  have hne : ∀ j, t0.1 j ≠ 0 := fun j => (h0 j).ne'
  have hc : rmulL (upMat t0) = scaleL t0.1 ∘ₗ rmulL (upMat (unipOf t0)) := by
    refine LinearMap.ext fun t => ?_
    rw [LinearMap.comp_apply, rmulL_apply, rmulL_apply, scaleL_triCoOf, upMat_eq_unip_mul t0 hne,
      Matrix.mul_assoc]
  rw [hc, LinearMap.det_comp, det_scaleL, det_rmulL_unip, mul_one]
  intro c b hbc
  rcases lt_or_eq_of_le hbc with h | h
  · rw [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_gt h), upMat_isUpT _ c b h, sub_zero]
  · subst h; rw [Matrix.sub_apply, Matrix.one_apply_eq, upMat_diag]; simp [unipOf]

/- English proof (translation)
Establish `hU` using `isUpT_mul (upMat_isUpT t) (upMat_isUpT t0)`. Establish `hd : ∀ a, (upMat t * upMat t0) a a = ((t.1 a * t0.1 a : ℝ) : ℂ)` using `fun a => by`. Rewrite using `[isUpT_mul_diag (upMat_isUpT t) (upMat_isUpT t0), upMat_diag, upMat_diag]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨upMat_triCoOf_of hU fun a => by rw [hd]; simp, fun j => ?_⟩` and prove the remaining obligations. Simplify using `only [triCoOf]`. Rewrite using `[hd]`. Simplify using the standard rewrite rules.
-/
theorem upMat_triCoOf_mul' (t t0 : TriCo N) :
    upMat (triCoOf (upMat t * upMat t0)) = upMat t * upMat t0 ∧
      ∀ j, (triCoOf (upMat t * upMat t0)).1 j = t.1 j * t0.1 j := by
  have hU := isUpT_mul (upMat_isUpT t) (upMat_isUpT t0)
  have hd : ∀ a, (upMat t * upMat t0) a a = ((t.1 a * t0.1 a : ℝ) : ℂ) := fun a => by
    rw [isUpT_mul_diag (upMat_isUpT t) (upMat_isUpT t0), upMat_diag, upMat_diag]; push_cast; ring
  refine ⟨upMat_triCoOf_of hU fun a => by rw [hd]; simp, fun j => ?_⟩
  simp only [triCoOf]; rw [hd]; simp

/- English proof (translation)
Establish `: (volume : Measure ({ab : Fin N × Fin N // ab.1 < ab.2} → ℂ)).IsAddHaarMeasure` using `MeasureTheory.Measure.pi.isAddHaarMeasure _`. Conclude with `Measure.prod.instIsAddHaarMeasure _ _`.
-/
theorem volume_triCo_isAddHaar : (volume : Measure (TriCo N)).IsAddHaarMeasure := by
  have : (volume : Measure ({ab : Fin N × Fin N // ab.1 < ab.2} → ℂ)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  exact Measure.prod.instIsAddHaarMeasure _ _

/- English proof (translation)
Unfold `triDens`. Use `fun_prop`.
-/
theorem triDens_measurable : Measurable (triDens (N := N)) := by unfold triDens; fun_prop

/- English proof (translation)
Establish `: triPos N = ⋂ j, {t : TriCo N | 0 < t.1 j}` using `by ext; simp [triPos]`. Rewrite using `[this]`. Conclude with `MeasurableSet.iInter fun j => measurableSet_lt measurable_const (by fun_prop)`.
-/
theorem triPos_measurableSet : MeasurableSet (triPos N) := by
  have : triPos N = ⋂ j, {t : TriCo N | 0 < t.1 j} := by ext; simp [triPos]
  rw [this]
  exact MeasurableSet.iInter fun j => measurableSet_lt measurable_const (by fun_prop)

/- English proof (translation)
Establish `h2` using `(upMat_triCoOf_mul' t t0).2`. Unfold `triDens`. Rewrite using `[← ENNReal.ofReal_mul (Finset.prod_nonneg fun j _ => pow_nonneg (h0 j).le _)]`. Use `congr 1`. Rewrite using `[← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[rmulL_apply, h2 j, mul_zpow]`. Establish `hne : t0.1 j ≠ 0` using `(h0 j).ne'`. Establish `: t0.1 j ^ (2 * (j : ℕ) + 1) * t0.1 j ^ (-(2 * ((j : ℕ) : ℤ) + 1)) = 1`. Rewrite using `[← zpow_natCast, ← zpow_add₀ hne]`.

Use `push_cast`. Simplify using the standard rewrite rules. Rewrite using `[mul_left_comm, this, mul_one]`.
-/
theorem triDens_rmulL (t0 t : TriCo N) (h0 : t0 ∈ triPos N) :
    triDens t = ENNReal.ofReal (∏ j : Fin N, t0.1 j ^ (2 * (j : ℕ) + 1)) *
      triDens (rmulL (upMat t0) t) := by
  have h2 := (upMat_triCoOf_mul' t t0).2
  unfold triDens
  rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun j _ => pow_nonneg (h0 j).le _)]
  congr 1
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [rmulL_apply, h2 j, mul_zpow]
  have hne : t0.1 j ≠ 0 := (h0 j).ne'
  have : t0.1 j ^ (2 * (j : ℕ) + 1) * t0.1 j ^ (-(2 * ((j : ℕ) : ℤ) + 1)) = 1 := by
    rw [← zpow_natCast, ← zpow_add₀ hne]; push_cast; simp
  rw [mul_left_comm, this, mul_one]

/- English proof (translation)
Simplify using `only [triPos, Set.mem_ofPred_eq, rmulL_apply, (upMat_triCoOf_mul' t t0).2]`. Conclude with `forall_congr' fun j => mul_pos_iff_of_pos_right (h0 j)`.
-/
theorem rmulL_mem_triPos (t0 t : TriCo N) (h0 : t0 ∈ triPos N) :
    rmulL (upMat t0) t ∈ triPos N ↔ t ∈ triPos N := by
  simp only [triPos, Set.mem_ofPred_eq, rmulL_apply, (upMat_triCoOf_mul' t t0).2]
  exact forall_congr' fun j => mul_pos_iff_of_pos_right (h0 j)

end ReciprocityTheory.ChartRestriction.DS.UpperTriangularMatrices
