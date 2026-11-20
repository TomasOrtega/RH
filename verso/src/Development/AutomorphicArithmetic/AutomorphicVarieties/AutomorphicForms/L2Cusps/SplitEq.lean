import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.InfEmbGrpEq

open NumberField GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global.IdeleGroup

/- English proof (translation)
Establish `hw : ¬ w.IsReal` using `InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)`. Rewrite using `[← coe_infiniteProj, infiniteProj_posIdele]`. Express the relevant statement in the definitionally equal form `GroundTheory.Global.posRealElem w _ = _`. Unfold `GroundTheory.Global.posRealElem`. Rewrite using `[dif_neg hw]`.

Simplify using `[InfinitePlace.mult, hw, Real.sqrt_sq hs.le]`.
-/
private theorem posIdele_inf {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (s : ℝ) (hs : 0 < s)
    (w : InfinitePlace E) :
    ((posIdele s hs : GroundTheory.Global.IdeleGroup E) : AdeleRing (𝓞 E) E).1 w =
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm (s : ℂ) := by
  have hw : ¬ w.IsReal := InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)
  rw [← coe_infiniteProj, infiniteProj_posIdele]
  change GroundTheory.Global.posRealElem w _ = _
  unfold GroundTheory.Global.posRealElem
  rw [dif_neg hw]
  simp [InfinitePlace.mult, hw, Real.sqrt_sq hs.le]

/- English proof (translation)
Introduce `E _ _ _ a t`. Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Establish `ha : (a : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 i.pos.ne'`. Establish `hd : (Module.finrank ℚ E : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 Module.finrank_pos.ne'`. Establish `e : rpowHom ((a * Module.finrank ℚ E : ℝ))⁻¹ ⟨Real.exp (a * Module.finrank ℚ E * t), Real.exp_pos _⟩ = ⟨Real.exp t, Real.exp_pos t⟩`.

Use `Subtype.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Real.exp (a * Module.finrank ℚ E * t) ^ ((a * Module.finrank ℚ E : ℝ))⁻¹ = Real.exp t`. Rewrite using `[← Real.exp_mul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[centralSection, MonoidHom.comp_apply, MonoidHom.comp_apply, e, posIdeleHom_apply, scalarUnits_apply, coe_diagUnits, splitCentre]`. Use `set y : GL (Fin a) (Cinf E) := Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => (t : ℂ)) with hy`. Establish `h2 : ((infGL E a y).val i j).2 = (1 : Matrix (Fin a) (Fin a) (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E)) i j` using `congrArg (fun g : GL (Fin a) (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) => g.val i j) (pFin_infGL y)`. Apply the tactic sequence `have h1 : ∀ w, ((infGL E a y).val i j).1 w = (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm (y.val i j w) := fun w => congrFun (UpperTheory.V.Cm.infGL_entry y i j) w`. Establish `hyv : y.val = Matrix.diagonal fun _ => (fun _ : InfinitePlace E => Complex.exp (t : ℂ))` using `rfl`.

Use `Prod.ext (funext fun w => ?_) ?_` and prove the remaining obligations. Rewrite using `[h1, hyv]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Rewrite using `[Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, posIdele_inf, Complex.ofReal_exp]`.

Rewrite using `[Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h]`. Conclude with `map_zero _`. Rewrite using `[h2]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Rewrite using `[Matrix.diagonal_apply_eq, Matrix.one_apply_eq]`. Conclude with `IsDedekindDomain.FiniteAdeleRing.ext E fun v => (posIdele_finite _ _ v).symm`. Rewrite using `[Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.KernelIndexFullLattice.splitEq_holds :
    UpperTheory.V.KernelIndexFullLattice.SplitEq := by
  intro E _ _ _ a t
  refine Units.ext (Matrix.ext fun i j => ?_)
  have ha : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.2 i.pos.ne'
  have hd : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have e : rpowHom ((a * Module.finrank ℚ E : ℝ))⁻¹ ⟨Real.exp (a * Module.finrank ℚ E * t), Real.exp_pos _⟩ =
      ⟨Real.exp t, Real.exp_pos t⟩ := by
    refine Subtype.ext ?_
    change Real.exp (a * Module.finrank ℚ E * t) ^ ((a * Module.finrank ℚ E : ℝ))⁻¹ = Real.exp t
    rw [← Real.exp_mul]
    congr 1
    field_simp
  rw [centralSection, MonoidHom.comp_apply, MonoidHom.comp_apply, e, posIdeleHom_apply, scalarUnits_apply,
    coe_diagUnits, splitCentre]
  set y : GL (Fin a) (Cinf E) :=
    Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => (t : ℂ)) with hy
  have h2 : ((infGL E a y).val i j).2 =
      (1 : Matrix (Fin a) (Fin a) (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E)) i j :=
    congrArg (fun g : GL (Fin a) (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) => g.val i j) (pFin_infGL y)
  have h1 : ∀ w, ((infGL E a y).val i j).1 w =
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm (y.val i j w) :=
    fun w => congrFun (UpperTheory.V.Cm.infGL_entry y i j) w
  have hyv : y.val = Matrix.diagonal fun _ => (fun _ : InfinitePlace E => Complex.exp (t : ℂ)) := rfl
  refine Prod.ext (funext fun w => ?_) ?_
  · rw [h1, hyv]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, posIdele_inf, Complex.ofReal_exp]
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h]
      exact map_zero _
  · rw [h2]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      exact IsDedekindDomain.FiniteAdeleRing.ext E fun v => (posIdele_finite _ _ v).symm
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
      rfl
