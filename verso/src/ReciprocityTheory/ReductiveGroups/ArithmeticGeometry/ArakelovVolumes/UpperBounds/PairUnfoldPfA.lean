import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfB

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

/- English proof (translation)
Establish `hU` using `(X.Γ_stab γ hγ).1`. Use extensionality with `i j`. Establish `e1 : herm X.Gm (Pi.single i 1) (Pi.single j 1) = X.Gm i j`. Simplify using `[herm, Pi.single_apply, apply_ite cc, cc_one, cc_zero]`. Rewrite using `[← e1, ← hU (Pi.single i 1) (Pi.single j 1)]`.

Simplify using `only [herm, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Conclude with `Finset.sum_comm`.
-/
theorem gramE {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    (γ : Matrix (Fin r) (Fin r) E).transpose * X.Gm * (γ : Matrix (Fin r) (Fin r) E).map cc = X.Gm := by
  have hU := (X.Γ_stab γ hγ).1
  ext i j
  have e1 : herm X.Gm (Pi.single i 1) (Pi.single j 1) = X.Gm i j := by
    simp [herm, Pi.single_apply, apply_ite cc, cc_one, cc_zero]
  rw [← e1, ← hU (Pi.single i 1) (Pi.single j 1)]
  simp only [herm, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  exact Finset.sum_comm

instance countGL : Countable (GL (Fin r) E) := by
  have : Countable E := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := E)
  have : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))
  exact Function.Injective.countable Units.val_injective

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mat_lact (γ : GL (Fin r) E) (x : Frame X.Ψ r) (τ : X.Ψ) :
    mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Conclude with `Finset.sum_comm`.
-/
theorem gram_eq' (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G M = M.transpose * G.map τ * M.map (starRingEnd ℂ) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  exact Finset.sum_comm

/- English proof (translation)
Establish `key` using `congrArg (fun M : Matrix (Fin r) (Fin r) E => M.map τ.1) (gramE X hγ)`. Simplify using `only [Matrix.map_mul, Matrix.transpose_map] at key`. Establish `hcc : ((γ : Matrix (Fin r) (Fin r) E).map cc).map τ.1 = ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ)`. Use extensionality with `i j`. Simplify using `[emb_cc]`.

Rewrite `key` using `[hcc]`. Rewrite using `[mat_lact, gram_eq', gram_eq', Matrix.transpose_mul, Matrix.map_mul]`. Rewrite using `[show ∀ A B C D F : Matrix (Fin r) (Fin r) ℂ, A * B * C * (D * F) = A * (B * C * D) * F from fun A B C D F => by simp only [Matrix.mul_assoc], key]`.
-/
theorem gram_lact {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (x : Frame X.Ψ r) (τ : X.Ψ) :
    gram τ.1 X.Gm (mat (lact γ x) τ) = gram τ.1 X.Gm (mat x τ) := by
  have key := congrArg (fun M : Matrix (Fin r) (Fin r) E => M.map τ.1) (gramE X hγ)
  simp only [Matrix.map_mul, Matrix.transpose_map] at key
  have hcc : ((γ : Matrix (Fin r) (Fin r) E).map cc).map τ.1 =
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) := by
    ext i j
    simp [emb_cc]
  rw [hcc] at key
  rw [mat_lact, gram_eq', gram_eq', Matrix.transpose_mul, Matrix.map_mul]
  rw [show ∀ A B C D F : Matrix (Fin r) (Fin r) ℂ, A * B * C * (D * F) = A * (B * C * D) * F from
    fun A B C D F => by simp only [Matrix.mul_assoc], key]

/- English proof (translation)
Unfold `dmin`. Rewrite using `[gram_lact X hγ]`.
-/
theorem dmin_lact {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (x : Frame X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm (lact γ x) τ i = dmin X.Gm x τ i := by
  unfold dmin
  rw [gram_lact X hγ]

/- English proof (translation)
Rewrite using `[mat_lact, Matrix.det_mul, RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem det_lact (γ : GL (Fin r) E) (x : Frame X.Ψ r) (τ : X.Ψ) :
    (mat (lact γ x) τ).det = τ.1 (γ : Matrix (Fin r) (Fin r) E).det * (mat x τ).det := by
  rw [mat_lact, Matrix.det_mul, RingHom.map_det]
  rfl

/- English proof (translation)
Establish `hd : ∀ τ : X.Ψ, τ.1 (γ : Matrix (Fin r) (Fin r) E).det ≠ 0` using `fun τ => (map_ne_zero τ.1).mpr (Matrix.isUnits_det_units γ).ne_zero`. Simplify using `only [GG, Set.mem_setOf_eq]`. Use `forall_congr' fun τ => and_congr ?_ (forall_congr' fun i => by rw [dmin_lact X hγ])` and prove the remaining obligations. Rewrite using `[det_lact]`. Conclude with `⟨fun h => right_ne_zero_of_mul h, fun h => mul_ne_zero (hd τ) h⟩`.
-/
theorem lact_mem_dom_iff {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (x : Frame X.Ψ r) :
    lact γ x ∈ X.dom ↔ x ∈ X.dom := by
  have hd : ∀ τ : X.Ψ, τ.1 (γ : Matrix (Fin r) (Fin r) E).det ≠ 0 := fun τ =>
    (map_ne_zero τ.1).mpr (Matrix.isUnits_det_units γ).ne_zero
  simp only [GG, Set.mem_setOf_eq]
  refine forall_congr' fun τ => and_congr ?_ (forall_congr' fun i => by rw [dmin_lact X hγ])
  rw [det_lact]
  exact ⟨fun h => right_ne_zero_of_mul h, fun h => mul_ne_zero (hd τ) h⟩

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Use `show (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat (lact γ' x) τ = ((↑(γ * γ') : Matrix (Fin r) (Fin r) E)).map τ.1 * mat x τ`. Rewrite using `[mat_lact, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]`.
-/
theorem lact_lact (γ γ' : GL (Fin r) E) (x : Frame X.Ψ r) : lact γ (lact γ' x) = lact (γ * γ') x := by
  funext τ
  show (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat (lact γ' x) τ =
    ((↑(γ * γ') : Matrix (Fin r) (Fin r) E)).map τ.1 * mat x τ
  rw [mat_lact, Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Use `show ((↑(1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)).map τ.1 * mat x τ = mat x τ`. Rewrite using `[Units.val_one, Matrix.map_one _ (map_zero τ.1) (map_one τ.1), Matrix.one_mul]`.
-/
theorem lact_one (x : Frame X.Ψ r) : lact (1 : GL (Fin r) E) x = x := by
  funext τ
  show ((↑(1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)).map τ.1 * mat x τ = mat x τ
  rw [Units.val_one, Matrix.map_one _ (map_zero τ.1) (map_one τ.1), Matrix.one_mul]

/- English proof (translation)
Rewrite using `[lact_lact, inv_mul_cancel, lact_one]`.
-/
theorem lact_inv_lact (γ : GL (Fin r) E) (x : Frame X.Ψ r) : lact γ⁻¹ (lact γ x) = x := by
  rw [lact_lact, inv_mul_cancel, lact_one]

/- English proof (translation)
Rewrite using `[lact_lact, mul_inv_cancel, lact_one]`.
-/
theorem lact_lact_inv (γ : GL (Fin r) E) (x : Frame X.Ψ r) : lact γ (lact γ⁻¹ x) = x := by
  rw [lact_lact, mul_inv_cancel, lact_one]

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Use `show (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ * mat b τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x τ * mat b τ)`. Conclude with `Matrix.mul_assoc _ _ _`.
-/
theorem rmul_lact (γ : GL (Fin r) E) (x b : Frame X.Ψ r) : rmul (lact γ x) b = lact γ (rmul x b) := by
  funext τ
  show (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ * mat b τ =
    (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x τ * mat b τ)
  exact Matrix.mul_assoc _ _ _

/- English proof (translation)
Unfold `cpt`. Conclude with `rmul_lact X γ x0 _`.
-/
theorem cpt_lact (γ : GL (Fin r) E) (x0 : Frame X.Ψ r) (z : V (nd X)) :
    cpt X (lact γ x0) z = lact γ (cpt X x0 z) := by
  unfold cpt
  exact rmul_lact X γ x0 _

/- English proof (translation)
Introduce `τ` and use `by rw [gram_lact X hγ] exact h τ`.
-/
theorem isOrth_lact {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x0 : Frame X.Ψ r} (h : IsOrth X x0) :
    IsOrth X (lact γ x0) := fun τ => by
  rw [gram_lact X hγ]
  exact h τ

/- English proof (translation)
Use extensionality with `z`. Simplify using `only [OmF, Set.mem_setOf_eq, cpt_lact, lact_mem_dom_iff X hγ]`.
-/
theorem OmF_lact {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (x0 : Frame X.Ψ r) : OmF X (lact γ x0) = OmF X x0 := by
  ext z
  simp only [OmF, Set.mem_setOf_eq, cpt_lact, lact_mem_dom_iff X hγ]

/- English proof (translation)
Simplify using `only [densF, cpt_lact, dmin_lact X hγ]`.
-/
theorem densF_lact {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (x0 : Frame X.Ψ r) (z : V (nd X)) :
    densF X (lact γ x0) z = densF X x0 z := by
  simp only [densF, cpt_lact, dmin_lact X hγ]

/- English proof (translation)
Simplify using `only [muF, OmF_lact X hγ, densF_lact X hγ]`.
-/
theorem muF_lact {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (x0 : Frame X.Ψ r) : muF X (lact γ x0) = muF X x0 := by
  simp only [muF, OmF_lact X hγ, densF_lact X hγ]

/- English proof (translation)
Use `continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations. Simplify using `only [lact, mat, Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply]`. Conclude with `continuous_finset_sum _ fun k _ => continuous_const.mul ((continuous_apply b).comp ((continuous_apply k).comp (continuous_apply τ)))`.
-/
theorem lact_cont (γ : GL (Fin r) E) : Continuous (lact (Ψ := X.Ψ) (r := r) γ) := by
  refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
  simp only [lact, mat, Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply]
  exact continuous_finset_sum _ fun k _ =>
    continuous_const.mul ((continuous_apply b).comp ((continuous_apply k).comp (continuous_apply τ)))

/- English proof (translation)
Use `continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations. Simplify using `only [cpt, rmul, mat, Matrix.mul_apply, Matrix.of_apply]`. Use `continuous_finset_sum _ fun k _ => continuous_const.mul ?_` and prove the remaining obligations. Simplify using `only [nmat]`. Use `split_ifs`.

Conclude with `PiLp.continuous_apply 2 _ _`. Conclude with `continuous_const`. Conclude with `continuous_const`.
-/
theorem cpt_cont (x0 : Frame X.Ψ r) : Continuous (cpt X x0) := by
  refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
  simp only [cpt, rmul, mat, Matrix.mul_apply, Matrix.of_apply]
  refine continuous_finset_sum _ fun k _ => continuous_const.mul ?_
  simp only [nmat]
  split_ifs
  · exact PiLp.continuous_apply 2 _ _
  · exact continuous_const
  · exact continuous_const

/- English proof (translation)
Establish `hb' : ∀ τ : X.Ψ, (mat b τ).det ≠ 0 ∧ ∀ a c : Fin r, c < a → b τ a c = 0` using `hb`. Unfold `bchar`. Use `Finset.prod_ne_zero_iff.mpr fun τ _ => Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ ?_` and prove the remaining obligations. Take `⟨hdet, htri⟩` from `hb' τ`. Establish `hbt : (mat b τ).BlockTriangular id` using `fun a c hca => htri a c hca`.

Rewrite `hdet` using `[Matrix.det_of_upperTriangular hbt]`. Conclude with `(Finset.prod_ne_zero_iff.mp hdet) i (Finset.mem_univ _)`.
-/
theorem bchar_ne {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (la : Wt X.Ψ r) : bchar la b ≠ 0 := by
  have hb' : ∀ τ : X.Ψ, (mat b τ).det ≠ 0 ∧ ∀ a c : Fin r, c < a → b τ a c = 0 := hb
  unfold bchar
  refine Finset.prod_ne_zero_iff.mpr fun τ _ => Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ ?_
  obtain ⟨hdet, htri⟩ := hb' τ
  have hbt : (mat b τ).BlockTriangular id := fun a c hca => htri a c hca
  rw [Matrix.det_of_upperTriangular hbt] at hdet
  exact (Finset.prod_ne_zero_iff.mp hdet) i (Finset.mem_univ _)

variable {X} {x0 : Frame X.Ψ r} (D : ExtFPf.LUData X x0) (FF : Set (V (nd X)))

def T : Set (Frame X.Ψ r) := {x | x ∈ X.dom ∧ D.Δ x ≠ 0 ∧ D.zOf x ∈ FF}

/- English proof (translation)
Establish `hdom : IsOpen X.dom`. Establish `hc : ∀ (τ : X.Ψ) (i : Fin (r + 1)), Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i`. Introduce `τ i`. Unfold `dmin lminor`. Use `(Continuous.matrix_submatrix ?_ _ _).matrix_det` and prove the remaining obligations.

Use `continuous_matrix fun a b => ?_` and prove the remaining obligations. Simplify using `only [gram, hermC, col, mat, Matrix.of_apply]`. Use `fun_prop`. Establish `hm : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => (mat x τ).det` using `fun τ => Continuous.matrix_det (continuous_apply τ)`. Establish `he : X.dom = ⋂ τ : X.Ψ, ({x | (mat x τ).det ≠ 0} ∩ ⋂ i : Fin (r + 1), {x | 0 < psgn X.p0 i * (dmin X.Gm x τ i).re})`.

Use extensionality with `x`. Simplify using `[GG]`. Rewrite using `[he]`. Conclude with `isOpen_iInter_of_finite fun τ => (isOpen_ne_fun (hm τ) continuous_const).inter (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_re.comp (hc τ i))))`. Set `U : Set (Frame X.Ψ r)` to `{x | x ∈ X.dom ∧ D.Δ x ≠ 0}`.

Establish `hU : IsOpen U` using `hdom.inter (isOpen_ne_fun D.hΔ.continuous continuous_const)`. Establish `hg : Measurable (U.piecewise D.zOf fun _ => 0)` using `D.hz.continuousOn.measurable_piecewise continuousOn_const hU.measurableSet`. Establish `hT : T D FF = U ∩ (U.piecewise D.zOf fun _ => 0) ⁻¹' FF`. Use extensionality with `x`. Simplify using `only [T, U, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2, h3⟩`. Conclude with `⟨⟨h1, h2⟩, by rw [Set.piecewise_eq_of_mem _ _ _ (show x ∈ U from ⟨h1, h2⟩)]; exact h3⟩`. Introduce and unpack `⟨⟨h1, h2⟩, h3⟩`. Rewrite `h3` using `[Set.piecewise_eq_of_mem _ _ _ (show x ∈ U from ⟨h1, h2⟩)]`.

Conclude with `⟨h1, h2, h3⟩`. Rewrite using `[hT]`. Conclude with `hU.measurableSet.inter (hg hFF)`.
-/
theorem T_meas (hFF : MeasurableSet FF) : MeasurableSet (T D FF) := by
  have hdom : IsOpen X.dom := by
    have hc : ∀ (τ : X.Ψ) (i : Fin (r + 1)), Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
      intro τ i
      unfold dmin lminor
      refine (Continuous.matrix_submatrix ?_ _ _).matrix_det
      refine continuous_matrix fun a b => ?_
      simp only [gram, hermC, col, mat, Matrix.of_apply]
      fun_prop
    have hm : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => (mat x τ).det := fun τ =>
      Continuous.matrix_det (continuous_apply τ)
    have he : X.dom = ⋂ τ : X.Ψ, ({x | (mat x τ).det ≠ 0} ∩
        ⋂ i : Fin (r + 1), {x | 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}) := by
      ext x
      simp [GG]
    rw [he]
    exact isOpen_iInter_of_finite fun τ => (isOpen_ne_fun (hm τ) continuous_const).inter
      (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const
        (continuous_const.mul (Complex.continuous_re.comp (hc τ i))))
  classical
  let U : Set (Frame X.Ψ r) := {x | x ∈ X.dom ∧ D.Δ x ≠ 0}
  have hU : IsOpen U := hdom.inter (isOpen_ne_fun D.hΔ.continuous continuous_const)
  have hg : Measurable (U.piecewise D.zOf fun _ => 0) :=
    D.hz.continuousOn.measurable_piecewise continuousOn_const hU.measurableSet
  have hT : T D FF = U ∩ (U.piecewise D.zOf fun _ => 0) ⁻¹' FF := by
    ext x
    simp only [T, U, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, by rw [Set.piecewise_eq_of_mem _ _ _ (show x ∈ U from ⟨h1, h2⟩)]; exact h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      rw [Set.piecewise_eq_of_mem _ _ _ (show x ∈ U from ⟨h1, h2⟩)] at h3
      exact ⟨h1, h2, h3⟩
  rw [hT]
  exact hU.measurableSet.inter (hg hFF)

/- English proof (translation)
Establish `h1' : ∀ τ : X.Ψ, (mat b τ).det ≠ 0 ∧ ∀ a c : Fin r, c < a → b τ a c = 0` using `hb`. Establish `h2' : ∀ τ : X.Ψ, (mat b' τ).det ≠ 0 ∧ ∀ a c : Fin r, c < a → b' τ a c = 0` using `hb'`. Use `show ∀ τ : X.Ψ, (mat (rmul b b') τ).det ≠ 0 ∧ ∀ a c : Fin r, c < a → rmul b b' τ a c = 0`. Introduce `τ`. Take `⟨d1, t1⟩` from `h1' τ`.

Take `⟨d2, t2⟩` from `h2' τ`. Establish `ht : (mat b τ * mat b' τ).BlockTriangular id` using `Matrix.BlockTriangular.mul (fun a c h => t1 a c h) (fun a c h => t2 a c h)`. Use `⟨?_, fun a c h => ht h⟩` and prove the remaining obligations. Use `show (mat b τ * mat b' τ).det ≠ 0`. Rewrite using `[Matrix.det_mul]`.

Conclude with `mul_ne_zero d1 d2`.
-/
private lemma rmul_mem_Bor {b b' : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (hb' : b' ∈ Bor X.Ψ r) :
    rmul b b' ∈ Bor X.Ψ r := by
  have h1' : ∀ τ : X.Ψ, (mat b τ).det ≠ 0 ∧ ∀ a c : Fin r, c < a → b τ a c = 0 := hb
  have h2' : ∀ τ : X.Ψ, (mat b' τ).det ≠ 0 ∧ ∀ a c : Fin r, c < a → b' τ a c = 0 := hb'
  show ∀ τ : X.Ψ, (mat (rmul b b') τ).det ≠ 0 ∧ ∀ a c : Fin r, c < a → rmul b b' τ a c = 0
  intro τ
  obtain ⟨d1, t1⟩ := h1' τ
  obtain ⟨d2, t2⟩ := h2' τ
  have ht : (mat b τ * mat b' τ).BlockTriangular id :=
    Matrix.BlockTriangular.mul (fun a c h => t1 a c h) (fun a c h => t2 a c h)
  refine ⟨?_, fun a c h => ht h⟩
  show (mat b τ * mat b' τ).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero d1 d2

/- English proof (translation)
Establish `h1' : ∀ τ : X.Ψ, (mat b τ).det ≠ 0 ∧ ∀ a c : Fin r, c < a → b τ a c = 0` using `hb`. Use `show ∀ τ : X.Ψ, (mat (fun τ a c => (mat b τ)⁻¹ a c) τ).det ≠ 0 ∧ ∀ a c : Fin r, c < a → ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) a c = 0`. Introduce `τ`. Take `⟨d1, t1⟩` from `h1' τ`. Use `haveI := (mat b τ).invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr d1)`.

Establish `ht : ((mat b τ)⁻¹).BlockTriangular id` using `Matrix.blockTriangular_inv_of_blockTriangular (fun a c h => t1 a c h)`. Use `⟨?_, fun a c h => ht h⟩` and prove the remaining obligations. Conclude with `((mat b τ).isUnit_nonsing_inv_det (isUnit_iff_ne_zero.mpr d1)).ne_zero`.
-/
private lemma inv_mat_apply_mem_bor {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    (fun τ a c => (mat b τ)⁻¹ a c) ∈ Bor X.Ψ r := by
  have h1' : ∀ τ : X.Ψ, (mat b τ).det ≠ 0 ∧ ∀ a c : Fin r, c < a → b τ a c = 0 := hb
  show ∀ τ : X.Ψ, (mat (fun τ a c => (mat b τ)⁻¹ a c) τ).det ≠ 0 ∧
    ∀ a c : Fin r, c < a → ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) a c = 0
  intro τ
  obtain ⟨d1, t1⟩ := h1' τ
  haveI := (mat b τ).invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr d1)
  have ht : ((mat b τ)⁻¹).BlockTriangular id :=
    Matrix.blockTriangular_inv_of_blockTriangular (fun a c h => t1 a c h)
  refine ⟨?_, fun a c h => ht h⟩
  exact ((mat b τ).isUnit_nonsing_inv_det (isUnit_iff_ne_zero.mpr d1)).ne_zero

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Use `show mat x τ * mat b τ * mat b' τ = mat x τ * (mat b τ * mat b' τ)`. Conclude with `Matrix.mul_assoc _ _ _`.
-/
private lemma rmul_rmul_assoc (x b b' : Frame X.Ψ r) : rmul (rmul x b) b' = rmul x (rmul b b') := by
  funext τ
  show mat x τ * mat b τ * mat b' τ = mat x τ * (mat b τ * mat b' τ)
  exact Matrix.mul_assoc _ _ _

/- English proof (translation)
Establish `h1' : ∀ τ : X.Ψ, (mat b τ).det ≠ 0 ∧ ∀ a c : Fin r, c < a → b τ a c = 0` using `hb`. Use function extensionality and compare the values at `τ`. Use `show mat x τ * mat b τ * (mat b τ)⁻¹ = mat x τ`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (h1' τ).1), Matrix.mul_one]`.
-/
private lemma rmul_rmul_inv_mat {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (x : Frame X.Ψ r) :
    rmul (rmul x b) (fun τ a c => (mat b τ)⁻¹ a c) = x := by
  have h1' : ∀ τ : X.Ψ, (mat b τ).det ≠ 0 ∧ ∀ a c : Fin r, c < a → b τ a c = 0 := hb
  funext τ
  show mat x τ * mat b τ * (mat b τ)⁻¹ = mat x τ
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (h1' τ).1), Matrix.mul_one]

/- English proof (translation)
Simplify using `only [T, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hd, hΔ, hF⟩`. Take `⟨hzO, hbO, hs⟩` from `D.split _ hd hΔ`. Establish `hx' : x = rmul (cpt X x0 (D.zOf (rmul x b))) (rmul (D.bOf (rmul x b)) (fun τ a c => (mat b τ)⁻¹ a c))`.

Rewrite using `[← rmul_rmul_assoc (X := X), ← hs, rmul_rmul_inv_mat (X := X) hb]`. Take `⟨hΔx, hzx, -⟩` from `D.uniq _ hzO _ (rmul_mem_Bor (X := X) hbO (inv_mat_apply_mem_bor (X := X) hb))`. Rewrite `hΔx`, `hzx` using `[← hx']`. Conclude with `⟨hx, hΔx, by rw [hzx]; exact hF⟩`. Introduce and unpack `⟨-, hΔ, hF⟩`.

Take `⟨hzO, hbO, hs⟩` from `D.split _ hx hΔ`. Establish `hxb : rmul x b = rmul (cpt X x0 (D.zOf x)) (rmul (D.bOf x) b)`. Rewrite using `[← rmul_rmul_assoc (X := X), ← hs]`. Take `⟨hΔ', hz', -⟩` from `D.uniq _ hzO _ (rmul_mem_Bor (X := X) hbO hb)`. Rewrite `hΔ'`, `hz'` using `[← hxb]`.

Conclude with `⟨ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom X hx hb, hΔ', by rw [hz']; exact hF⟩`.
-/
theorem T_rmul {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r) :
    rmul x b ∈ T D FF ↔ x ∈ T D FF := by
  simp only [T, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hd, hΔ, hF⟩
    obtain ⟨hzO, hbO, hs⟩ := D.split _ hd hΔ
    have hx' : x = rmul (cpt X x0 (D.zOf (rmul x b)))
        (rmul (D.bOf (rmul x b)) (fun τ a c => (mat b τ)⁻¹ a c)) := by
      rw [← rmul_rmul_assoc (X := X), ← hs, rmul_rmul_inv_mat (X := X) hb]
    obtain ⟨hΔx, hzx, -⟩ := D.uniq _ hzO _ (rmul_mem_Bor (X := X) hbO (inv_mat_apply_mem_bor (X := X) hb))
    rw [← hx'] at hΔx hzx
    exact ⟨hx, hΔx, by rw [hzx]; exact hF⟩
  · rintro ⟨-, hΔ, hF⟩
    obtain ⟨hzO, hbO, hs⟩ := D.split _ hx hΔ
    have hxb : rmul x b = rmul (cpt X x0 (D.zOf x)) (rmul (D.bOf x) b) := by
      rw [← rmul_rmul_assoc (X := X), ← hs]
    obtain ⟨hΔ', hz', -⟩ := D.uniq _ hzO _ (rmul_mem_Bor (X := X) hbO hb)
    rw [← hxb] at hΔ' hz'
    exact ⟨ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom X hx hb, hΔ', by rw [hz']; exact hF⟩

/- English proof (translation)
Establish `h1 : (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) ∈ Bor X.Ψ r` using `by show ∀ τ : X.Ψ, (mat (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) τ).det ≠ 0 ∧ ∀ a c : Fin r, c < a → (1 : Matrix (Fin r) (Fin r) ℂ) a c = 0`. Introduce `τ`. Use `⟨?_, fun a c h => Matrix.one_apply_ne h.ne'⟩` and prove the remaining obligations. Use `show (1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0`. Simplify using the standard rewrite rules.

Establish `hr : rmul (cpt X x0 z) (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) = cpt X x0 z`. Use function extensionality and compare the values at `τ`. Use `show mat (cpt X x0 z) τ * 1 = mat (cpt X x0 z) τ`. Conclude with `Matrix.mul_one _`. Take `⟨hΔ, hzO, -⟩` from `D.uniq z hz _ h1`.

Rewrite `hΔ`, `hzO` using `[hr]`. Simplify using `only [T, Set.mem_setOf_eq, hzO]`. Conclude with `⟨fun h => h.2.2, fun h => ⟨hz, hΔ, h⟩⟩`.
-/
theorem T_cpt {z : V (nd X)} (hz : z ∈ OmF X x0) : cpt X x0 z ∈ T D FF ↔ z ∈ FF := by
  have h1 : (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) ∈ Bor X.Ψ r := by
    show ∀ τ : X.Ψ, (mat (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) τ).det ≠ 0 ∧
      ∀ a c : Fin r, c < a → (1 : Matrix (Fin r) (Fin r) ℂ) a c = 0
    intro τ
    refine ⟨?_, fun a c h => Matrix.one_apply_ne h.ne'⟩
    show (1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0
    simp
  have hr : rmul (cpt X x0 z) (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r) = cpt X x0 z := by
    funext τ
    show mat (cpt X x0 z) τ * 1 = mat (cpt X x0 z) τ
    exact Matrix.mul_one _
  obtain ⟨hΔ, hzO, -⟩ := D.uniq z hz _ h1
  rw [hr] at hΔ hzO
  simp only [T, Set.mem_setOf_eq, hzO]
  exact ⟨fun h => h.2.2, fun h => ⟨hz, hΔ, h⟩⟩

/- English proof (translation)
Rewrite using `[T_rmul D FF hz hb, T_cpt D FF hz]`.
-/
theorem T_rmul_cpt {z : V (nd X)} (hz : z ∈ OmF X x0) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    rmul (cpt X x0 z) b ∈ T D FF ↔ z ∈ FF := by
  rw [T_rmul D FF hz hb, T_cpt D FF hz]

/- English proof (translation)
Take `⟨hd, hΔ, hF⟩` from `hx`. Take `⟨-, hbO, hs⟩` from `D.split x hd hΔ`. Conclude with `⟨_, hF, _, hbO, hs⟩`.
-/
theorem T_split {x : Frame X.Ψ r} (hx : x ∈ T D FF) :
    ∃ z ∈ FF, ∃ b ∈ Bor X.Ψ r, x = rmul (cpt X x0 z) b := by
  obtain ⟨hd, hΔ, hF⟩ := hx
  obtain ⟨-, hbO, hs⟩ := D.split x hd hΔ
  exact ⟨_, hF, _, hbO, hs⟩

/- English proof (translation)
Take `⟨-, hsub, hinj, hcov⟩` from `hFF`. Use `filter_upwards [ExtFPf.ae_OmF (X := X) (x0 := x0), hcov] with z hz hc`. Take `⟨z', hz', γ, hγ, b, hb, hcz⟩` from `hc`. Use `⟨hz, γ, hγ, fun γ' hγ' => ?_⟩` and prove the remaining obligations. Establish `hz'O : z' ∈ OmF X x0` using `hsub hz'`.

Establish `key : lact γ'⁻¹ (cpt X x0 z) = lact (γ'⁻¹ * γ) (rmul (cpt X x0 z') b)`. Rewrite using `[hcz, lact_lact]`. Rewrite using `[key]`. Prove the components needed by the constructor for the conclusion. Introduce `hT`.

Take `⟨z'', hz'', b'', hb'', hx⟩` from `T_split D FF hT`. Establish `hδΓ : γ'⁻¹ * γ ∈ X.Γ` using `X.Γ.mul_mem (X.Γ.inv_mem hγ') hγ`. Establish `h3 : cpt X x0 z'' = lact (γ'⁻¹ * γ) (rmul (cpt X x0 z') (rmul b (fun τ a c => (mat b'' τ)⁻¹ a c)))`. Rewrite using `[← rmul_rmul_inv_mat (X := X) hb'' (cpt X x0 z''), ← hx, rmul_lact, rmul_rmul_assoc (X := X)]`. Establish `hB` using `rmul_mem_Bor (X := X) hb (inv_mat_apply_mem_bor (X := X) hb'')`.

Establish `hzz` using `hinj z' hz' z'' hz'' _ hδΓ _ hB h3`. Substitute `hzz` using the available equality. Establish `h4 : lact (γ'⁻¹ * γ)⁻¹ (cpt X x0 z') = rmul (cpt X x0 z') (rmul b (fun τ a c => (mat b'' τ)⁻¹ a c))` using `by conv_lhs => rw [h3]`. Rewrite using `[lact_inv_lact]`. Establish `h5` using `X.Γ_free _ (X.Γ.inv_mem hδΓ) _ hz'O _ hB h4`.

Conclude with `inv_mul_eq_one.mp (inv_eq_one.mp h5)`. Introduce and unpack `rfl`. Rewrite using `[inv_mul_cancel, lact_one]`. Conclude with `(T_rmul_cpt D FF hz'O hb).2 hz'`.
-/
theorem ae_unique (hFF : IsFundSet X x0 FF) :
    ∀ᵐ z ∂muF X x0, z ∈ OmF X x0 ∧ ∃ γ0 ∈ X.Γ, ∀ γ ∈ X.Γ, (lact γ⁻¹ (cpt X x0 z) ∈ T D FF ↔ γ = γ0) := by
  obtain ⟨-, hsub, hinj, hcov⟩ := hFF
  filter_upwards [ExtFPf.ae_OmF (X := X) (x0 := x0), hcov] with z hz hc
  obtain ⟨z', hz', γ, hγ, b, hb, hcz⟩ := hc
  refine ⟨hz, γ, hγ, fun γ' hγ' => ?_⟩
  have hz'O : z' ∈ OmF X x0 := hsub hz'
  have key : lact γ'⁻¹ (cpt X x0 z) = lact (γ'⁻¹ * γ) (rmul (cpt X x0 z') b) := by
    rw [hcz, lact_lact]
  rw [key]
  constructor
  · intro hT
    obtain ⟨z'', hz'', b'', hb'', hx⟩ := T_split D FF hT
    have hδΓ : γ'⁻¹ * γ ∈ X.Γ := X.Γ.mul_mem (X.Γ.inv_mem hγ') hγ

    have h3 : cpt X x0 z'' = lact (γ'⁻¹ * γ) (rmul (cpt X x0 z')
        (rmul b (fun τ a c => (mat b'' τ)⁻¹ a c))) := by
      rw [← rmul_rmul_inv_mat (X := X) hb'' (cpt X x0 z''), ← hx, rmul_lact, rmul_rmul_assoc (X := X)]
    have hB := rmul_mem_Bor (X := X) hb (inv_mat_apply_mem_bor (X := X) hb'')
    have hzz := hinj z' hz' z'' hz'' _ hδΓ _ hB h3
    subst hzz

    have h4 : lact (γ'⁻¹ * γ)⁻¹ (cpt X x0 z') = rmul (cpt X x0 z')
        (rmul b (fun τ a c => (mat b'' τ)⁻¹ a c)) := by
      conv_lhs => rw [h3]
      rw [lact_inv_lact]
    have h5 := X.Γ_free _ (X.Γ.inv_mem hδΓ) _ hz'O _ hB h4
    exact inv_mul_eq_one.mp (inv_eq_one.mp h5)
  · rintro rfl
    rw [inv_mul_cancel, lact_one]
    exact (T_rmul_cpt D FF hz'O hb).2 hz'

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
