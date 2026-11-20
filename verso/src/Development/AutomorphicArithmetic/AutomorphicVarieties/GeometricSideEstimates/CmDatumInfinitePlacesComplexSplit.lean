import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.SplitEq
open UpperTheory.V.Lit.Geo

section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Simplify using `[InfinitePlace.mult, InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)]`.
-/
private theorem mult_two (w : InfinitePlace E) : w.mult = 2 := by
  simp [InfinitePlace.mult, InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)]

/- English proof (translation)
Rewrite using `[← InfinitePlace.sum_mult_eq]`. Simplify using `[mult_two, mul_comm]`.
-/
private theorem rank_eq : (Module.finrank ℚ E : ℝ) = 2 * Fintype.card (InfinitePlace E) := by
  rw [← InfinitePlace.sum_mult_eq]
  simp [mult_two, mul_comm]

/- English proof (translation)
Establish `e1 : pInf E (infGL E a h).val.det = h.val.det`. Rewrite using `[RingHom.map_det]`. Conclude with `congrArg (fun y : GL (Fin a) (Cinf E) => y.val.det) (pInf_infGL h)`. Establish `e2 : pFin E (infGL E a h).val.det = 1`. Rewrite using `[RingHom.map_det]`.

Conclude with `(congrArg (fun y : GL (Fin a) (Af E) => y.val.det) (pFin_infGL h)).trans Matrix.det_one`. Establish `h1 : ∀ v : InfinitePlace E, ‖((infGL E a h).val.det : Ad E).1 v‖ = ‖h.val.det v‖` using `fun v => by`. Rewrite using `[← (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _)]`. Conclude with `congrArg norm (congrFun e1 v)`. Establish `h2 : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), ‖((infGL E a h).val.det : Ad E).2 v‖ = 1` using `fun v => by`.

Express the relevant statement in the definitionally equal form `‖pFin E (infGL E a h).val.det v‖ = 1`. Rewrite using `[e2]`. Conclude with `norm_one`. Express the relevant statement in the definitionally equal form `(IdeleGroup.ideleModule E (AdelicGLn.det E a (infGL E a h)) : ℝ) = _`. Rewrite using `[IdeleGroup.ideleModule_eq]`.

Express the relevant statement in the definitionally equal form `(∏ v : InfinitePlace E, ‖((infGL E a h).val.det : Ad E).1 v‖ ^ v.mult) * ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), ‖((infGL E a h).val.det : Ad E).2 v‖ = _`. Simplify using `only [h1, h2, finprod_one, mul_one, mult_two]`.
-/
private theorem mod_inf (h : GL (Fin a) (Cinf E)) :
    (Reduction.detModule E a (infGL E a h) : ℝ) = ∏ w : InfinitePlace E, ‖h.val.det w‖ ^ 2 := by
  have e1 : pInf E (infGL E a h).val.det = h.val.det := by
    rw [RingHom.map_det]
    exact congrArg (fun y : GL (Fin a) (Cinf E) => y.val.det) (pInf_infGL h)
  have e2 : pFin E (infGL E a h).val.det = 1 := by
    rw [RingHom.map_det]
    exact (congrArg (fun y : GL (Fin a) (Af E) => y.val.det) (pFin_infGL h)).trans Matrix.det_one
  have h1 : ∀ v : InfinitePlace E, ‖((infGL E a h).val.det : Ad E).1 v‖ = ‖h.val.det v‖ := fun v => by
    rw [← (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _)]
    exact congrArg norm (congrFun e1 v)
  have h2 : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), ‖((infGL E a h).val.det : Ad E).2 v‖ = 1 := fun v => by
    change ‖pFin E (infGL E a h).val.det v‖ = 1
    rw [e2]
    exact norm_one
  change (IdeleGroup.ideleModule E (AdelicGLn.det E a (infGL E a h)) : ℝ) = _
  rw [IdeleGroup.ideleModule_eq]
  change (∏ v : InfinitePlace E, ‖((infGL E a h).val.det : Ad E).1 v‖ ^ v.mult) *
    ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), ‖((infGL E a h).val.det : Ad E).2 v‖ = _
  simp only [h1, h2, finprod_one, mul_one, mult_two]

/- English proof (translation)
Rewrite using `[UpperTheory.V.KernelIndexFullLattice.splitEq_holds E a, ← map_inv (Reduction.centralSection E a)]`. Use `congrArg _ (Subtype.ext ?_)` and prove the remaining obligations. Establish `hne : ∀ w : InfinitePlace E, ‖h.val.det w‖ ≠ 0` using `fun w => norm_ne_zero_iff.2 (((Matrix.isUnit_iff_isUnit_det _).1 h.isUnit).map (Pi.evalRingHom _ w)).ne_zero`. Establish `h1 : (a : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`. Establish `h2 : (Fintype.card (InfinitePlace E) : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`.

Establish `hp` using `(Reduction.detModule E a (infGL E a h)).2`. Express the relevant statement in the definitionally equal form `(Reduction.detModule E a (infGL E a h) : ℝ)⁻¹ = Real.exp _`. Rewrite using `[← Real.exp_log hp, ← Real.exp_neg, mod_inf, Real.log_prod fun w _ => pow_ne_zero _ (hne w), sc, Real.log_exp, rank_eq]`. Use `congr 1`. Simplify using `only [Real.log_pow, ← Finset.mul_sum]`.

Clear the denominators using the available nonvanishing facts. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem sect_inv (ha : 1 ≤ a) (h : GL (Fin a) (Cinf E)) :
    (Reduction.centralSection E a (Reduction.detModule E a (infGL E a h)))⁻¹ =
      splitCentre E a (Real.log (sc h.val)) := by
  rw [UpperTheory.V.KernelIndexFullLattice.splitEq_holds E a, ← map_inv (Reduction.centralSection E a)]
  refine congrArg _ (Subtype.ext ?_)
  have hne : ∀ w : InfinitePlace E, ‖h.val.det w‖ ≠ 0 := fun w =>
    norm_ne_zero_iff.2 (((Matrix.isUnit_iff_isUnit_det _).1 h.isUnit).map (Pi.evalRingHom _ w)).ne_zero
  have h1 : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h2 : (Fintype.card (InfinitePlace E) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hp := (Reduction.detModule E a (infGL E a h)).2
  change (Reduction.detModule E a (infGL E a h) : ℝ)⁻¹ = Real.exp _
  rw [← Real.exp_log hp, ← Real.exp_neg, mod_inf, Real.log_prod fun w _ => pow_ne_zero _ (hne w), sc,
    Real.log_exp, rank_eq]
  congr 1
  simp only [Real.log_pow, ← Finset.mul_sum]
  field_simp
  push_cast
  ring

/- English proof (translation)
Rewrite using `[splitCentre, pInf_infGL]`. Express the relevant statement in the definitionally equal form `x ᵥ* Matrix.diagonal (fun _ => (fun _ : InfinitePlace E => Complex.exp (t : ℂ))) = _`. Use extensionality with `i w`. Rewrite using `[Matrix.vecMul_diagonal]`. Simplify using `[mul_comm]`.
-/
private theorem pInf_split (t : ℝ) (x : Fin a → Cinf E) :
    x ᵥ* (GeneralLinearGroup.map (pInf E) (splitCentre E a t)).val = Real.exp t • x := by
  rw [splitCentre, pInf_infGL]
  change x ᵥ* Matrix.diagonal (fun _ => (fun _ : InfinitePlace E => Complex.exp (t : ℂ))) = _
  ext i w
  rw [Matrix.vecMul_diagonal]
  simp [mul_comm]

end

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum in
/- English proof (translation)
Introduce `E _ _ _ a ha g h v`. Establish `e : rt (g * infGL E a h) = rt g * infGL E a h * splitCentre E a (Real.log (sc h.val))`. Rewrite using `[← sect_inv ha h, UpperTheory.V.Lit.Geo.rt, UpperTheory.V.Lit.Geo.rt, coe_retractOne, coe_retractOne, map_mul, map_mul, _root_.mul_inv_rev, mul_assoc g _⁻¹, ← map_inv (Reduction.centralSection E a) (Reduction.detModule E a g), Reduction.centralSection_mul_comm, ← Reduction.centra …`. Simplify using `only [mul_assoc]`. Rewrite using `[e]`.

Express the relevant statement in the definitionally equal form `vInf v ᵥ* _ = sc h.val • ((vInf v ᵥ* _) ᵥ* _)`. Rewrite using `[map_mul, map_mul, Units.val_mul, Units.val_mul, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, pInf_split, pInf_infGL, Real.exp_log (show 0 < sc h.val from Real.exp_pos _)]`.
-/
theorem UpperTheory.cmDatum_infinitePlaces_complex_split :
    RtInf := by
  intro E _ _ _ a ha g h v
  have e : rt (g * infGL E a h) = rt g * infGL E a h * splitCentre E a (Real.log (sc h.val)) := by
    rw [← sect_inv ha h, UpperTheory.V.Lit.Geo.rt, UpperTheory.V.Lit.Geo.rt, coe_retractOne, coe_retractOne, map_mul, map_mul, _root_.mul_inv_rev,
      mul_assoc g _⁻¹, ← map_inv (Reduction.centralSection E a) (Reduction.detModule E a g),
      Reduction.centralSection_mul_comm, ← Reduction.centralSection_mul_comm _ _⁻¹]
    simp only [mul_assoc]
  rw [e]
  change vInf v ᵥ* _ = sc h.val • ((vInf v ᵥ* _) ᵥ* _)
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, pInf_split,
    pInf_infGL, Real.exp_log (show 0 < sc h.val from Real.exp_pos _)]
