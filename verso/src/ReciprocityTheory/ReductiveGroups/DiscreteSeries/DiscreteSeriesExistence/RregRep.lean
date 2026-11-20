import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SquareIntegrableInnerProduct

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

/- English proof (translation)
The claim follows from `Subtype.ext (Units.ext h)`.
-/
theorem rregRep_umat_inj (ε : Fin n → Bool) {x y : Formalism.REAL.UJ ε}
    (h : Formalism.MainNotions.S.umat x = Formalism.MainNotions.S.umat y) : x = y := Subtype.ext (Units.ext h)

/- English proof (translation)
Establish `h : ∃ y' : Formalism.REAL.UJ ε, Formalism.MainNotions.S.umat y' = Formalism.MainNotions.S.umat y` using `⟨y, rfl⟩`. Rewrite using `[rreg, dif_pos h]`. Conclude with `congrArg (rregG ε) (rregRep_umat_inj ε h.choose_spec)`.
-/
theorem rregRep_rreg_umat (ε : Fin n → Bool) (y : Formalism.REAL.UJ ε) :
    rreg ε (Formalism.MainNotions.S.umat y) = rregG ε y := by
  have h : ∃ y' : Formalism.REAL.UJ ε, Formalism.MainNotions.S.umat y' = Formalism.MainNotions.S.umat y := ⟨y, rfl⟩
  rw [rreg, dif_pos h]
  exact congrArg (rregG ε) (rregRep_umat_inj ε h.choose_spec)

/- English proof (translation)
Rewrite using `[rregG, dif_pos (measurePreserving_mul_right ε y)]`. Both sides reduce to the same expression.
-/
theorem rregRep_rregG_apply (ε : Fin n → Bool) (y : Formalism.REAL.UJ ε) (f : L2 ε) :
    rregG ε y f = Lp.compMeasurePreserving (fun x : Formalism.REAL.UJ ε => x * y)
      (measurePreserving_mul_right ε y) f := by
  rw [rregG, dif_pos (measurePreserving_mul_right ε y)]
  rfl

/- English proof (translation)
Unfold `Formalism.REAL.Jm`. Rewrite using `[Matrix.diagonal_mul_diagonal]`. Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Apply the tactic sequence `by_cases h : ε i <;> simp [h]`. Simplify using `[Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]`.
-/
private theorem Jm_mul_selfDiscreteSeriesExistence (ε : Fin n → Bool) :
    Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases h : ε i <;> simp [h]
  · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

/- English proof (translation)
Establish `hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε` using `hg`. Rewrite `hg'` using `[Matrix.mul_assoc]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[hg', Jm_mul_selfDiscreteSeriesExistence]`.
-/
private theorem Jm_conjTranspose_Jm_mul_eq_one_of_mem_UJset (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) : (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) * g = 1 := by
  have hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  rw [Matrix.mul_assoc] at hg'
  simp only [Matrix.mul_assoc]
  rw [hg', Jm_mul_selfDiscreteSeriesExistence]

/- English proof (translation)
Establish `hl` using `Jm_conjTranspose_Jm_mul_eq_one_of_mem_UJset ε hg`. Use `first`. Consider the case `exact mul_eq_one_comm.mp hl`. Consider the case `(rw [← Matrix.inv_eq_left_inv hl]`. Conclude with `Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse hl))`.
-/
private theorem mul_Jm_conjTranspose_Jm_eq_one_of_mem_UJset (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) : g * (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) = 1 := by
  have hl := Jm_conjTranspose_Jm_mul_eq_one_of_mem_UJset ε hg
  first
  | exact mul_eq_one_comm.mp hl
  | (rw [← Matrix.inv_eq_left_inv hl]
     exact Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse hl))

/- English proof (translation)
Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Conclude with `y.2`. Introduce `hg`.

Conclude with `⟨⟨⟨g, Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε, mul_Jm_conjTranspose_Jm_eq_one_of_mem_UJset ε hg, Jm_conjTranspose_Jm_mul_eq_one_of_mem_UJset ε hg⟩, hg⟩, rfl⟩`.
-/
theorem rregRep_range (ε : Fin n → Bool) :
    Set.range (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g) = UJset ε := by
  ext g
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hg
    exact ⟨⟨⟨g, Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε, mul_Jm_conjTranspose_Jm_eq_one_of_mem_UJset ε hg,
      Jm_conjTranspose_Jm_mul_eq_one_of_mem_UJset ε hg⟩, hg⟩, rfl⟩

/- English proof (translation)
Establish `h2 : g ∈ Set.range (fun y : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat y)`. Rewrite using `[rregRep_range ε]`. Conclude with `hg`. Take `⟨y, hy⟩` from `h2`. Conclude with `⟨y, hy⟩`.
-/
theorem rregRep_mem (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    ∃ y : Formalism.REAL.UJ ε, Formalism.MainNotions.S.umat y = g := by
  have h2 : g ∈ Set.range (fun y : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat y) := by
    rw [rregRep_range ε]
    exact hg
  obtain ⟨y, hy⟩ := h2
  exact ⟨y, hy⟩

/- English proof (translation)
Establish `h1 : (1 : Matrix (Fin n) (Fin n) ℂ) = Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε)` using `rfl`. Rewrite using `[h1, rregRep_rreg_umat]`. Use `ext1 f`. Rewrite using `[rregRep_rregG_apply, ContinuousLinearMap.one_apply]`. Apply `Lp.ext` to reduce the goal to its premises.

Use `filter_upwards [Lp.coeFn_compMeasurePreserving f (measurePreserving_mul_right ε 1)] with x hx`. Rewrite using `[hx]`. Simplify using the standard rewrite rules.
-/
theorem rregRep_one (ε : Fin n → Bool) : rreg ε 1 = 1 := by
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) = Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε) := rfl
  rw [h1, rregRep_rreg_umat]
  ext1 f
  rw [rregRep_rregG_apply, ContinuousLinearMap.one_apply]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving f (measurePreserving_mul_right ε 1)] with x hx
  rw [hx]
  simp

/- English proof (translation)
Use `ext1 f`. Rewrite using `[ContinuousLinearMap.comp_apply, rregRep_rregG_apply, rregRep_rregG_apply, rregRep_rregG_apply]`. Apply `Lp.ext` to reduce the goal to its premises. Use `filter_upwards [Lp.coeFn_compMeasurePreserving f (measurePreserving_mul_right ε (a * b)), Lp.coeFn_compMeasurePreserving (Lp.compMeasurePreserving (fun x : Formalism.REAL.UJ ε => x * b) (measurePreserving_mul_right ε b) f) (measurePreserving_mul_right ε a), (measurePreserving_mul …`. Simplify using `only [Function.comp_apply] at h1 h2 h3 ⊢`.

Rewrite using `[h1, h2, h3, mul_assoc]`.
-/
theorem rregRep_mul (ε : Fin n → Bool) (a b : Formalism.REAL.UJ ε) :
    rregG ε (a * b) = (rregG ε a).comp (rregG ε b) := by
  ext1 f
  rw [ContinuousLinearMap.comp_apply, rregRep_rregG_apply, rregRep_rregG_apply,
    rregRep_rregG_apply]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving f (measurePreserving_mul_right ε (a * b)),
    Lp.coeFn_compMeasurePreserving
      (Lp.compMeasurePreserving (fun x : Formalism.REAL.UJ ε => x * b)
        (measurePreserving_mul_right ε b) f) (measurePreserving_mul_right ε a),
    (measurePreserving_mul_right ε a).quasiMeasurePreserving.ae_eq
      (Lp.coeFn_compMeasurePreserving f (measurePreserving_mul_right ε b))] with x h1 h2 h3
  simp only [Function.comp_apply] at h1 h2 h3 ⊢
  rw [h1, h2, h3, mul_assoc]

/- English proof (translation)
Use `haveI : SMulInvariantMeasure (Formalism.REAL.UJ ε)ᵐᵒᵖ (Formalism.REAL.UJ ε) (Formalism.REAL.muG ε) := by`. Use `⟨fun c s hs => ?_⟩` and prove the remaining obligations. Use `first`. Consider the case `exact (measurePreserving_mul_right ε c.unop).measure_preimage hs.nullMeasurableSet`. Consider the case `exact (measurePreserving_mul_right ε c.unop).measure_preimage hs`.

Apply the tactic sequence `haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by first | simp | exact ENNReal.ofNat_ne_top⟩`. Establish `he : (fun y : Formalism.REAL.UJ ε => rregG ε y v) = fun y => (DomMulAct.mk (MulOpposite.op y)) • v`. Use function extensionality and compare the values at `y`. Rewrite using `[rregRep_rregG_apply]`. Both sides reduce to the same expression.

Rewrite using `[he]`. Establish `hm : Continuous (fun y : Formalism.REAL.UJ ε => DomMulAct.mk (MulOpposite.op y))` using `by first`. Consider the case `exact DomMulAct.continuous_mk.comp MulOpposite.continuous_op`. Consider the case `exact DomMulAct.mkHomeomorph.continuous.comp MulOpposite.continuous_op`. Consider the case `fun_prop`.

Use `haveI : OpensMeasurableSpace (Formalism.REAL.UJ ε)ᵐᵒᵖ := ⟨MeasurableSpace.generateFrom_le fun s hs => (IsOpen.preimage MulOpposite.continuous_op hs).measurableSet⟩`. Conclude with `hm.smul continuous_const`.
-/
theorem rregRep_cont (ε : Fin n → Bool) (v : L2 ε) :
    Continuous (fun y : Formalism.REAL.UJ ε => rregG ε y v) := by
  haveI : SMulInvariantMeasure (Formalism.REAL.UJ ε)ᵐᵒᵖ (Formalism.REAL.UJ ε) (Formalism.REAL.muG ε) := by
    refine ⟨fun c s hs => ?_⟩
    first
    | exact (measurePreserving_mul_right ε c.unop).measure_preimage hs.nullMeasurableSet
    | exact (measurePreserving_mul_right ε c.unop).measure_preimage hs
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by first | simp | exact ENNReal.ofNat_ne_top⟩
  have he : (fun y : Formalism.REAL.UJ ε => rregG ε y v) =
      fun y => (DomMulAct.mk (MulOpposite.op y)) • v := by
    funext y
    rw [rregRep_rregG_apply]
    rfl
  rw [he]
  have hm : Continuous (fun y : Formalism.REAL.UJ ε => DomMulAct.mk (MulOpposite.op y)) := by
    first
    | exact DomMulAct.continuous_mk.comp MulOpposite.continuous_op
    | exact DomMulAct.mkHomeomorph.continuous.comp MulOpposite.continuous_op
    | fun_prop
  haveI : OpensMeasurableSpace (Formalism.REAL.UJ ε)ᵐᵒᵖ :=
    ⟨MeasurableSpace.generateFrom_le fun s hs =>
      (IsOpen.preimage MulOpposite.continuous_op hs).measurableSet⟩
  exact hm.smul continuous_const

/- English proof (translation)
Unfold `IsURepOn`. Use `⟨⟨rregRep_one ε, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `a ha b hb`. Take `⟨ya, rfl⟩` from `rregRep_mem ε ha`. Take `⟨yb, rfl⟩` from `rregRep_mem ε hb`.

Establish `hab : Formalism.MainNotions.S.umat ya * Formalism.MainNotions.S.umat yb = Formalism.MainNotions.S.umat (ya * yb)` using `rfl`. Rewrite using `[hab, rregRep_rreg_umat, rregRep_rreg_umat, rregRep_rreg_umat, rregRep_mul]`. Introduce `g hg v`. Take `⟨y, rfl⟩` from `rregRep_mem ε hg`. Rewrite using `[rregRep_rreg_umat, rregRep_rregG_apply]`.

Conclude with `Lp.norm_compMeasurePreserving v _`. Introduce `v`. Take `⟨φ, hφc, hφ⟩ : ∃ φ : UJset ε → Formalism.REAL.UJ ε, Continuous φ ∧ ∀ g : UJset ε, Formalism.MainNotions.S.umat (φ g) = g` from `⟨fun g => ⟨⟨(g : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.Jm ε * (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε, mul_Jm_conjTranspose_Jm_eq_one_of_mem_UJset ε g.2, Jm_conjTranspose_Jm_mul_eq_one_of_mem_UJset ε g.2⟩, g.2⟩, by`. Apply `Continuous.subtype_mk` to reduce the goal to its premises. Rewrite using `[Units.continuous_iff]`.

Prove the components needed by the constructor for the conclusion. Conclude with `continuous_subtype_val`. Conclude with `(continuous_const.mul continuous_subtype_val.matrix_conjTranspose).mul continuous_const,`. Use `fun g => rfl⟩`. Establish `he : ∀ g : UJset ε, rreg ε (g : Matrix (Fin n) (Fin n) ℂ) v = rregG ε (φ g) v`.

Introduce `g`. Rewrite using `[← hφ g, rregRep_rreg_umat]`. Rewrite using `[continuousOn_iff_continuous_restrict]`. Use `(rregRep_cont ε v).comp hφc using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`.

Conclude with `he g`.
-/
theorem rreg_isURepOn (ε : Fin n → Bool) : IsURepOn (UJset ε) (rreg ε) := by
  unfold IsURepOn
  refine ⟨⟨rregRep_one ε, ?_⟩, ?_, ?_⟩
  · intro a ha b hb
    obtain ⟨ya, rfl⟩ := rregRep_mem ε ha
    obtain ⟨yb, rfl⟩ := rregRep_mem ε hb
    have hab : Formalism.MainNotions.S.umat ya * Formalism.MainNotions.S.umat yb = Formalism.MainNotions.S.umat (ya * yb) := rfl
    rw [hab, rregRep_rreg_umat, rregRep_rreg_umat, rregRep_rreg_umat, rregRep_mul]
  · intro g hg v
    obtain ⟨y, rfl⟩ := rregRep_mem ε hg
    rw [rregRep_rreg_umat, rregRep_rregG_apply]
    exact Lp.norm_compMeasurePreserving v _
  · intro v
    obtain ⟨φ, hφc, hφ⟩ : ∃ φ : UJset ε → Formalism.REAL.UJ ε, Continuous φ ∧
        ∀ g : UJset ε, Formalism.MainNotions.S.umat (φ g) = g :=
      ⟨fun g => ⟨⟨(g : Matrix (Fin n) (Fin n) ℂ),
          Formalism.REAL.Jm ε * (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε,
          mul_Jm_conjTranspose_Jm_eq_one_of_mem_UJset ε g.2, Jm_conjTranspose_Jm_mul_eq_one_of_mem_UJset ε g.2⟩, g.2⟩,
        by
          apply Continuous.subtype_mk
          rw [Units.continuous_iff]
          constructor
          · exact continuous_subtype_val
          · exact (continuous_const.mul continuous_subtype_val.matrix_conjTranspose).mul
              continuous_const,
        fun g => rfl⟩
    have he : ∀ g : UJset ε, rreg ε (g : Matrix (Fin n) (Fin n) ℂ) v = rregG ε (φ g) v := by
      intro g
      rw [← hφ g, rregRep_rreg_umat]
    rw [continuousOn_iff_continuous_restrict]
    convert (rregRep_cont ε v).comp hφc using 1
    funext g
    exact he g

end ReciprocityTheory.ChartRestriction.DS
