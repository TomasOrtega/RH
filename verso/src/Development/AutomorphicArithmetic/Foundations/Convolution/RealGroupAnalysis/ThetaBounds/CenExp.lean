import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.NormInf

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private noncomputable def euF {F : Type} [Field F] (z : TR.Rinf F) (t : ℝ) : (TR.Rinf F)ˣ :=
  ⟨fun w => Real.exp (t * z w), fun w => Real.exp (-(t * z w)),
    funext fun w => by simp [← Real.exp_add], funext fun w => by simp [← Real.exp_add]⟩

private noncomputable def euE {E : Type} [Field E] (s : Cinf E) (t : ℝ) : (Cinf E)ˣ :=
  ⟨fun w => Complex.exp (t * s w), fun w => Complex.exp (-(t * s w)),
    funext fun w => by simp [← Complex.exp_add], funext fun w => by simp [← Complex.exp_add]⟩

/- English proof (translation)
Establish `h1 : TR.pInf F (TR.infId F u).val = u.val`. Express the relevant statement in the definitionally equal form `TR.pInf F (1 - TR.sInf F 1 + TR.sInf F _) = _`. Establish `h : ∀ x, TR.pInf F (TR.sInf F x) = x` using `fun x => (TR.infEq F).symm_apply_apply x`. Simplify using `[h]`. Establish `h2 : pFin F (TR.infId F u).val = 1`.

Express the relevant statement in the definitionally equal form `(1 : Af F) - 0 + 0 = 1`. Simplify using the standard rewrite rules. Use `TR.ga_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[TR.pInf_infGL]`. Use extensionality with `i j`.

Apply the tactic sequence `by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h1]`. Rewrite using `[TR.pFin_infGL]`. Use extensionality with `i j`. Apply the tactic sequence `by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h2]`.
-/
private theorem inf_scalarF {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (u : (TR.Rinf F)ˣ) :
    TR.infGL F 2 (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (TR.infId F u) := by
  have h1 : TR.pInf F (TR.infId F u).val = u.val := by
    change TR.pInf F (1 - TR.sInf F 1 + TR.sInf F _) = _
    have h : ∀ x, TR.pInf F (TR.sInf F x) = x := fun x => (TR.infEq F).symm_apply_apply x
    simp [h]
  have h2 : pFin F (TR.infId F u).val = 1 := by
    change (1 : Af F) - 0 + 0 = 1
    simp
  refine TR.ga_ext ?_ ?_
  · rw [TR.pInf_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h1]
  · rw [TR.pFin_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h2]

/- English proof (translation)
Establish `hd : infId E u = Matrix.GeneralLinearGroup.det (infGL E 1 (Matrix.GeneralLinearGroup.scalar (Fin 1) u))`. Rewrite using `[det_infGL]`. Use `congr 1`. Conclude with `Units.ext (by simp)`. Establish `h1 : pInf E (infId E u : Ideles E) = u`.

Rewrite using `[hd, ← GlobalTheory.CuspRep.det_map, pInf_infGL]`. Simplify using the standard rewrite rules. Establish `h2 : pFin E (infId E u : Ideles E) = 1`. Rewrite using `[hd, ← GlobalTheory.CuspRep.det_map, pFin_infGL]`. Simplify using the standard rewrite rules.

Use `ga_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[pInf_infGL]`. Use extensionality with `i j`. Apply the tactic sequence `by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h1]`. Rewrite using `[pFin_infGL]`.

Use extensionality with `i j`. Apply the tactic sequence `by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h2]`.
-/
private theorem inf_scalarE {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (u : (Cinf E)ˣ) :
    infGL E 2 (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (infId E u) := by
  have hd : infId E u =
      Matrix.GeneralLinearGroup.det (infGL E 1 (Matrix.GeneralLinearGroup.scalar (Fin 1) u)) := by
    rw [det_infGL]
    congr 1
    exact Units.ext (by simp)
  have h1 : pInf E (infId E u : Ideles E) = u := by
    rw [hd, ← GlobalTheory.CuspRep.det_map, pInf_infGL]
    simp
  have h2 : pFin E (infId E u : Ideles E) = 1 := by
    rw [hd, ← GlobalTheory.CuspRep.det_map, pFin_infGL]
    simp
  refine ga_ext ?_ ?_
  · rw [pInf_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h1]
  · rw [pFin_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h2]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Establish `e : t • Matrix.of (zE s) = Matrix.diagonal (fun _ : Fin 2 => t • s)`. Use extensionality with `i j w`. Apply the tactic sequence `by_cases h : i = j <;> simp [zE, Matrix.diagonal_apply, h]`. Express the relevant statement in the definitionally equal form `NormedSpace.exp (t • Matrix.of (zE s)) = _`.

Rewrite using `[e, Matrix.exp_diagonal]`. Use extensionality with `i j w`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[euE, Pi.exp_def, Complex.exp_eq_exp_ℂ]`.

Simplify using `[Matrix.diagonal_apply, h]`.
-/
private theorem ex_zE {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (s : Cinf E) (t : ℝ) :
    ex (zE s) t = Matrix.GeneralLinearGroup.scalar (Fin 2) (euE s t) := by
  apply Units.ext
  have e : t • Matrix.of (zE s) = Matrix.diagonal (fun _ : Fin 2 => t • s) := by
    ext i j w
    by_cases h : i = j <;> simp [zE, Matrix.diagonal_apply, h]
  change NormedSpace.exp (t • Matrix.of (zE s)) = _
  rw [e, Matrix.exp_diagonal]
  ext i j w
  by_cases h : i = j
  · subst h
    simp [euE, Pi.exp_def, Complex.exp_eq_exp_ℂ]
  · simp [Matrix.diagonal_apply, h]

/- English proof (translation)
Establish `h : ∀ w : InfinitePlace E, (if w.comap (algebraMap F E) = v then ‖(euE s t).val w‖ ^ 2 else 1) = Real.exp (t * if w.comap (algebraMap F E) = v then 2 * (s w).re else 0)`. Introduce `w`. Use `split_ifs`. Express the relevant statement in the definitionally equal form `‖Complex.exp (t * s w)‖ ^ 2 = _`. Rewrite using `[Complex.norm_exp, ← Real.exp_nat_mul]`.

Simplify using the standard rewrite rules. Put the polynomial expressions in normal form. Simplify using the standard rewrite rules. Simplify using `only [h]`. Rewrite using `[← Real.exp_sum, ← Finset.mul_sum]`.

Both sides reduce to the same expression.
-/
private theorem norm_euE {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [IsTotallyComplex E] (s : Cinf E) (t : ℝ) (v : InfinitePlace F) :
    (∏ w : InfinitePlace E, if w.comap (algebraMap F E) = v then ‖(euE s t).val w‖ ^ 2 else 1) =
      (euF (trI F s) t).val v := by
  have h : ∀ w : InfinitePlace E, (if w.comap (algebraMap F E) = v then ‖(euE s t).val w‖ ^ 2 else 1) =
      Real.exp (t * if w.comap (algebraMap F E) = v then 2 * (s w).re else 0) := by
    intro w
    split_ifs
    · change ‖Complex.exp (t * s w)‖ ^ 2 = _
      rw [Complex.norm_exp, ← Real.exp_nat_mul]
      simp
      ring_nf
    · simp
  simp only [h]
  rw [← Real.exp_sum, ← Finset.mul_sum]
  rfl

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ D s`. Use `⟨fun t => infId E (euE s t), fun t => Matrix.GeneralLinearGroup.scalar (Fin 2) (euF (trI F s) t), ⟨fun a b => ?_, ?_⟩, fun t => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Establish `h : euF (trI F s) (a + b) = euF (trI F s) a * euF (trI F s) b`. Use `Units.ext (funext fun w => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Real.exp ((a + b) * _) = Real.exp (a * _) * Real.exp (b * _)`.

Rewrite using `[add_mul, Real.exp_add]`. Express the relevant statement in the definitionally equal form `Matrix.GeneralLinearGroup.scalar (Fin 2) (euF (trI F s) (a + b)) = _`. Rewrite using `[h, map_mul]`. Use `hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_` and prove the remaining obligations. Distinguish the cases in `e : i = j`.

Substitute `e` using the available equality. Establish `h : HasDerivAt (fun t : ℝ => Real.exp (t * trI F s v)) (trI F s v) 0`. Simplify using `using ((hasDerivAt_id (0 : ℝ)).mul_const (trI F s v)).exp`. Simplify `h` using `[zF, euF, Matrix.diagonal_apply]`. Simplify `hasDerivAt_const (0 : ℝ) (0 : ℝ)` using `[zF, Matrix.diagonal_apply, e]`.

Rewrite using `[ex_zE, inf_scalarE]`. Take `⟨u, hu, hn⟩` from `normInf F E D (euE s t)`. Establish `e : u = euF (trI F s) t` using `Units.ext (funext fun v => by rw [hu, norm_euE])`. Rewrite using `[hn, e, inf_scalarF]`.
-/
theorem UpperTheory.ConvolutionTheory.R2.Ff.cenExp :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (_D : Dat F E), CenExp F E := by
  intro F E _ _ _ _ _ _ _ D s
  refine ⟨fun t => infId E (euE s t), fun t => Matrix.GeneralLinearGroup.scalar (Fin 2) (euF (trI F s) t),
    ⟨fun a b => ?_, ?_⟩, fun t => ⟨?_, ?_⟩⟩
  · have h : euF (trI F s) (a + b) = euF (trI F s) a * euF (trI F s) b := by
      refine Units.ext (funext fun w => ?_)
      change Real.exp ((a + b) * _) = Real.exp (a * _) * Real.exp (b * _)
      rw [add_mul, Real.exp_add]
    change Matrix.GeneralLinearGroup.scalar (Fin 2) (euF (trI F s) (a + b)) = _
    rw [h, map_mul]
  · refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
    by_cases e : i = j
    · subst e
      have h : HasDerivAt (fun t : ℝ => Real.exp (t * trI F s v)) (trI F s v) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (trI F s v)).exp
      simpa [zF, euF, Matrix.diagonal_apply] using h
    · simpa [zF, Matrix.diagonal_apply, e] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · rw [ex_zE, inf_scalarE]
  · obtain ⟨u, hu, hn⟩ := normInf F E D (euE s t)
    have e : u = euF (trI F s) t := Units.ext (funext fun v => by rw [hu, norm_euE])
    rw [hn, e, inf_scalarF]
