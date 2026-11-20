import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.GaussA

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

/- English proof (translation)
Establish `hpt : ∀ Z : Fin N → Fin N → ℂ, ENNReal.ofReal (Real.exp (-hs (Matrix.of Z))) = ENNReal.ofReal (∏ i, (fun (_ : Fin N) (row : Fin N → ℂ) => ∏ j, Real.exp (-‖row j‖ ^ 2)) i (Z i))`. Introduce `Z`. Use `congr 1`. Simplify using `only [hs, Matrix.of_apply, ← Real.exp_sum, ← Finset.sum_neg_distrib]`. Establish `hrow : Integrable (fun row : Fin N → ℂ => ∏ j, Real.exp (-‖row j‖ ^ 2))` using `Integrable.fintype_prod (fun _ => gaussA_cint)`.

Establish `hrowi : ∫ row : Fin N → ℂ, ∏ j, Real.exp (-‖row j‖ ^ 2) = Real.pi ^ N`. Rewrite using `[integral_fintype_prod_volume_eq_prod (fun (_ : Fin N) (z : ℂ) => Real.exp (-‖z‖ ^ 2))]`. Simplify using `only [gaussA_cintegral, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Repeatedly rewrite using `[hpt]`. Rewrite using `[show (volume : Measure (Fin N → Fin N → ℂ)) = Measure.pi (fun _ => volume) from rfl, gaussA_lint_pi_ofReal _ (fun _ => hrow) (fun _ _ => Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)]`.

Simplify using `only [hrowi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Rewrite using `[← ENNReal.ofReal_pow (pow_nonneg Real.pi_pos.le _), ← pow_mul, sq]`.
-/
theorem gaussC_mat :
    ∫⁻ Z : Fin N → Fin N → ℂ, ENNReal.ofReal (Real.exp (-hs (Matrix.of Z))) =
      ENNReal.ofReal (Real.pi ^ (N ^ 2)) := by
  have hpt : ∀ Z : Fin N → Fin N → ℂ, ENNReal.ofReal (Real.exp (-hs (Matrix.of Z))) =
      ENNReal.ofReal (∏ i, (fun (_ : Fin N) (row : Fin N → ℂ) => ∏ j, Real.exp (-‖row j‖ ^ 2)) i (Z i)) := by
    intro Z
    congr 1
    simp only [hs, Matrix.of_apply, ← Real.exp_sum, ← Finset.sum_neg_distrib]
  have hrow : Integrable (fun row : Fin N → ℂ => ∏ j, Real.exp (-‖row j‖ ^ 2)) :=
    Integrable.fintype_prod (fun _ => gaussA_cint)
  have hrowi : ∫ row : Fin N → ℂ, ∏ j, Real.exp (-‖row j‖ ^ 2) = Real.pi ^ N := by
    rw [integral_fintype_prod_volume_eq_prod (fun (_ : Fin N) (z : ℂ) => Real.exp (-‖z‖ ^ 2))]
    simp only [gaussA_cintegral, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp_rw [hpt]
  rw [show (volume : Measure (Fin N → Fin N → ℂ)) = Measure.pi (fun _ => volume) from rfl,
    gaussA_lint_pi_ofReal _ (fun _ => hrow)
      (fun _ _ => Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)]
  simp only [hrowi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (pow_nonneg Real.pi_pos.le _), ← pow_mul, sq]

/- English proof (translation)
Establish `hp : ∀ a b : Fin N, ‖upMat t a b‖ ^ 2 = (if a = b then t.1 a ^ 2 else 0) + (if h : a < b then ‖t.2 ⟨(a, b), h⟩‖ ^ 2 else 0)`. Introduce `a b`. Unfold `upMat`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Simplify using `[Complex.norm_real, sq_abs]`. Distinguish the cases in `h : a < b`. Simplify using `[hab, h]`. Simplify using `[hab, h]`. Unfold `hs`.

Repeatedly rewrite using `[hp, Finset.sum_add_distrib]`. Use `congr 1`. Simplify using `[Finset.sum_ite_eq]`. Rewrite using `[← Finset.sum_product' (f := fun a b => if h : a < b then ‖t.2 ⟨(a, b), h⟩‖ ^ 2 else 0), Finset.univ_product_univ, ← (Equiv.sumCompl (fun p : Fin N × Fin N => p.1 < p.2)).sum_comp, Fintype.sum_sum_type]`. Establish `h1 : ∀ a : {p : Fin N × Fin N // p.1 < p.2}, (fun p : Fin N × Fin N => if h : p.1 < p.2 then ‖t.2 ⟨(p.1, p.2), h⟩‖ ^ 2 else 0) ((Equiv.sumCompl (fun p : Fin N × Fin N => p.1 < p.2)) (Sum.inl a)) = ‖t.2 a‖ ^ 2`.

Introduce `a`. Take `⟨⟨x, y⟩, h⟩` from `a`. Simplify using `[h]`. Establish `h2 : ∀ b : {p : Fin N × Fin N // ¬ p.1 < p.2}, (fun p : Fin N × Fin N => if h : p.1 < p.2 then ‖t.2 ⟨(p.1, p.2), h⟩‖ ^ 2 else 0) ((Equiv.sumCompl (fun p : Fin N × Fin N => p.1 < p.2)) (Sum.inr b)) = 0`. Introduce `b`.

Take `⟨⟨x, y⟩, h⟩` from `b`. Simplify using `[h]`. Simplify using `only [h1, h2, Finset.sum_const_zero, add_zero]`.
-/
theorem gaussC_hs_upMat (t : TriCo N) :
    hs (upMat t) = ∑ j, t.1 j ^ 2 + ∑ ab : {ab : Fin N × Fin N // ab.1 < ab.2}, ‖t.2 ab‖ ^ 2 := by
  have hp : ∀ a b : Fin N, ‖upMat t a b‖ ^ 2 = (if a = b then t.1 a ^ 2 else 0) +
      (if h : a < b then ‖t.2 ⟨(a, b), h⟩‖ ^ 2 else 0) := by
    intro a b
    unfold upMat
    by_cases hab : a = b
    · subst hab; simp [Complex.norm_real, sq_abs]
    · by_cases h : a < b
      · simp [hab, h]
      · simp [hab, h]
  unfold hs
  simp_rw [hp, Finset.sum_add_distrib]
  congr 1
  · simp [Finset.sum_ite_eq]
  · rw [← Finset.sum_product' (f := fun a b => if h : a < b then ‖t.2 ⟨(a, b), h⟩‖ ^ 2 else 0),
      Finset.univ_product_univ,
      ← (Equiv.sumCompl (fun p : Fin N × Fin N => p.1 < p.2)).sum_comp, Fintype.sum_sum_type]
    have h1 : ∀ a : {p : Fin N × Fin N // p.1 < p.2},
        (fun p : Fin N × Fin N => if h : p.1 < p.2 then ‖t.2 ⟨(p.1, p.2), h⟩‖ ^ 2 else 0)
          ((Equiv.sumCompl (fun p : Fin N × Fin N => p.1 < p.2)) (Sum.inl a)) = ‖t.2 a‖ ^ 2 := by
      intro a; obtain ⟨⟨x, y⟩, h⟩ := a; simp [h]
    have h2 : ∀ b : {p : Fin N × Fin N // ¬ p.1 < p.2},
        (fun p : Fin N × Fin N => if h : p.1 < p.2 then ‖t.2 ⟨(p.1, p.2), h⟩‖ ^ 2 else 0)
          ((Equiv.sumCompl (fun p : Fin N × Fin N => p.1 < p.2)) (Sum.inr b)) = 0 := by
      intro b; obtain ⟨⟨x, y⟩, h⟩ := b; simp [h]
    simp only [h1, h2, Finset.sum_const_zero, add_zero]

def gaussRadW (N : ℕ) (j : Fin N) (r : ℝ) : ℝ := Real.exp (-r ^ 2) * |r| ^ (2 * (N - 1 - (j : ℕ)) + 1)

/- English proof (translation)
Rewrite using `[← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul' (Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)]`. Use `congr 1`. Rewrite using `[gaussC_hs_upMat, neg_add, Real.exp_add, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, Real.exp_sum, Real.exp_sum]`. Establish `hw : ∀ j : Fin N, t.1 j ^ (2 * (N - (j : ℕ)) - 1) = |t.1 j| ^ (2 * (N - 1 - (j : ℕ)) + 1)`. Introduce `j`.

Rewrite using `[abs_of_pos (ht j)]`. Use `congr 1`. Use `j.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Unfold `qrWt gaussRadW`.

Repeatedly rewrite using `[hw, Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gaussD_integrand (t : TriCo N) (ht : t ∈ triPos N) :
    ENNReal.ofReal (Real.exp (-hs (upMat t))) * ENNReal.ofReal (qrWt t) =
      ENNReal.ofReal (∏ j, gaussRadW N j (t.1 j)) *
        ENNReal.ofReal (∏ ab : {ab : Fin N × Fin N // ab.1 < ab.2}, Real.exp (-‖t.2 ab‖ ^ 2)) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul' (Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)]
  congr 1
  rw [gaussC_hs_upMat, neg_add, Real.exp_add, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
    Real.exp_sum, Real.exp_sum]
  have hw : ∀ j : Fin N, t.1 j ^ (2 * (N - (j : ℕ)) - 1) = |t.1 j| ^ (2 * (N - 1 - (j : ℕ)) + 1) := by
    intro j
    rw [abs_of_pos (ht j)]
    congr 1
    have := j.2
    omega
  unfold qrWt gaussRadW
  simp_rw [hw, Finset.prod_mul_distrib]
  ring

/- English proof (translation)
Use extensionality with `t`. Simplify using `[triPos]`.
-/
theorem gaussD_triPos_eq : triPos N = (Set.univ.pi fun _ : Fin N => Set.Ioi (0:ℝ)) ×ˢ Set.univ := by
  ext t
  simp [triPos]

/- English proof (translation)
Establish `hms : MeasurableSet (triPos N)`. Rewrite using `[gaussD_triPos_eq]`. Conclude with `(MeasurableSet.univ_pi fun _ => measurableSet_Ioi).prod MeasurableSet.univ`. Rewrite using `[setLIntegral_congr_fun hms (fun t ht => gaussD_integrand t ht), gaussD_triPos_eq, show (volume : Measure (TriCo N)) = (volume : Measure (Fin N → ℝ)).prod (volume : Measure ({ab : Fin N × Fin N // ab.1 < ab.2} → ℂ)) from rfl, ← Measure.prod_restrict, Measure.restrict_univ, show ( …`. Rewrite using `[lintegral_prod_mul (f := fun x : Fin N → ℝ => ENNReal.ofReal (∏ j, gaussRadW N j (x j))) (g := fun y : {ab : Fin N × Fin N // ab.1 < ab.2} → ℂ => ENNReal.ofReal (∏ ab, Real.exp (-‖y ab‖ ^ 2))) (by unfold gaussRadW; fun_prop) (ENNReal.measurable_ofReal.comp (by fun_prop : Continu …`.

Rewrite using `[gaussA_lint_pi_ofReal (fun j => gaussRadW N j) (fun j => gaussA_rad_int _) (fun j r => mul_nonneg (Real.exp_pos _).le (pow_nonneg (abs_nonneg _) _)), show (volume : Measure ({ab : Fin N × Fin N // ab.1 < ab.2} → ℂ)) = Measure.pi (fun _ => volume) from rfl, gaussA_lint_pi_ofReal …`. Simplify using `only [gaussRadW, gaussA_rad, gaussA_cintegral, Finset.prod_const, Finset.card_univ, gaussB_card_lt]`. Rewrite using `[← ENNReal.ofReal_prod_of_nonneg (fun _ _ => by positivity), ← ENNReal.ofReal_pow Real.pi_pos.le, ← ENNReal.ofReal_mul (Finset.prod_nonneg fun _ _ => by positivity), gaussB_prod_fact]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gaussD_tri :
    ∫⁻ t in triPos N, ENNReal.ofReal (Real.exp (-hs (upMat t))) * ENNReal.ofReal (qrWt t) =
      ENNReal.ofReal (Real.pi ^ (N * (N - 1) / 2) * (∏ i ∈ range N, (i.factorial : ℝ)) / 2 ^ N) := by
  have hms : MeasurableSet (triPos N) := by
    rw [gaussD_triPos_eq]
    exact (MeasurableSet.univ_pi fun _ => measurableSet_Ioi).prod MeasurableSet.univ
  rw [setLIntegral_congr_fun hms (fun t ht => gaussD_integrand t ht), gaussD_triPos_eq,
    show (volume : Measure (TriCo N)) = (volume : Measure (Fin N → ℝ)).prod
      (volume : Measure ({ab : Fin N × Fin N // ab.1 < ab.2} → ℂ)) from rfl,
    ← Measure.prod_restrict, Measure.restrict_univ,
    show (volume : Measure (Fin N → ℝ)) = Measure.pi (fun _ => volume) from rfl,
    Measure.restrict_pi_pi]
  rw [lintegral_prod_mul (f := fun x : Fin N → ℝ => ENNReal.ofReal (∏ j, gaussRadW N j (x j)))
    (g := fun y : {ab : Fin N × Fin N // ab.1 < ab.2} → ℂ =>
      ENNReal.ofReal (∏ ab, Real.exp (-‖y ab‖ ^ 2)))
    (by unfold gaussRadW; fun_prop)
    (ENNReal.measurable_ofReal.comp (by fun_prop : Continuous fun y : {ab : Fin N × Fin N // ab.1 < ab.2} → ℂ =>
      ∏ ab, Real.exp (-‖y ab‖ ^ 2)).measurable).aemeasurable]
  rw [gaussA_lint_pi_ofReal (fun j => gaussRadW N j) (fun j => gaussA_rad_int _)
      (fun j r => mul_nonneg (Real.exp_pos _).le (pow_nonneg (abs_nonneg _) _)),
    show (volume : Measure ({ab : Fin N × Fin N // ab.1 < ab.2} → ℂ)) = Measure.pi (fun _ => volume) from rfl,
    gaussA_lint_pi_ofReal (fun (_ : {ab : Fin N × Fin N // ab.1 < ab.2}) (z : ℂ) => Real.exp (-‖z‖ ^ 2))
      (fun _ => gaussA_cint) (fun _ _ => (Real.exp_pos _).le)]
  simp only [gaussRadW, gaussA_rad, gaussA_cintegral, Finset.prod_const, Finset.card_univ, gaussB_card_lt]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => by positivity),
    ← ENNReal.ofReal_pow Real.pi_pos.le, ← ENNReal.ofReal_mul (Finset.prod_nonneg fun _ _ => by positivity),
    gaussB_prod_fact]
  congr 1
  ring

end ReciprocityTheory.ChartRestriction.DS
