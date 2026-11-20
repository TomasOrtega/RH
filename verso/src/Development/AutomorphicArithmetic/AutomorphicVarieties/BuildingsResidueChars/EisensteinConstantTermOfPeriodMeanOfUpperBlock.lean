import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.PerDeriv
open UpperTheory.V.Sd.Eis

open UpperTheory.V.Sd in
/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ]`.
-/
private theorem cb_aff_mul {R : Type} [CommRing R] (y y' : Rˣ) (x x' : R) :
    aff y x * aff y' x' = aff (y * y') (y * x' + x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ]

open NumberField GlobalTheory.CuspRep UpperTheory.V.Sd in
/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [aff, ratGL]`.
-/
private theorem cb_rat_aff (F : Type) [Field F] [NumberField F] (a : Fˣ) (y : F) :
    ratGL F 2 (aff a y) =
      aff (Units.map (algebraMap F (Ad F)).toMonoidHom a) (algebraMap F (Ad F) y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, ratGL]

open NumberField GlobalTheory.CuspRep in

private noncomputable def cb_scale (F : Type) [Field F] [NumberField F] (u : (Ad F)ˣ) : NA F ≃ₜ+ NA F where
  toFun x p := (u : Ad F) * x p
  invFun x p := ((u⁻¹ : (Ad F)ˣ) : Ad F) * x p
  left_inv x := funext fun p => Units.inv_mul_cancel_left u (x p)
  right_inv x := funext fun p => Units.mul_inv_cancel_left u (x p)
  map_add' x y := funext fun p => mul_add _ _ _
  continuous_toFun := continuous_pi fun p => continuous_const.mul (continuous_apply p)
  continuous_invFun := continuous_pi fun p => continuous_const.mul (continuous_apply p)

open NumberField GlobalTheory.CuspRep in
/- English proof (translation)
Take `⟨y, rfl⟩` from `hx`. Conclude with `⟨fun p => a * y p, funext fun p => map_mul (algebraMap F (Ad F)) _ _⟩`.
-/
private theorem cb_mem (F : Type) [Field F] [NumberField F] (a : F) (x : NA F) (hx : x ∈ ratN F 2 1) :
    (fun p => algebraMap F (Ad F) a * x p) ∈ ratN F 2 1 := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨fun p => a * y p, funext fun p => map_mul (algebraMap F (Ad F)) _ _⟩

open NumberField MeasureTheory GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd in
/- English proof (translation)
Introduce `hM hB F _ _ _ _ μ _ D hF φ hc hl`. Take `⟨i1, i2, i3, i4, hco, hu, hx⟩` from `hB F`. Establish `hper : ∀ (h : GA F 2), ∀ γ ∈ ratN F 2 1, ∀ x : NA F, φ (unip (γ + x) * h) = φ (unip x * h)`. Introduce and unpack `h _ ⟨y, rfl⟩ x`. Rewrite using `[hx, hx x]`.

Use `Eq.trans ?_ (hl (aff 1 (y ⟨(0, 1), by decide⟩)) _)` and prove the remaining obligations. Rewrite using `[← mul_assoc, cb_rat_aff, cb_aff_mul, map_one, one_mul, Units.val_one, one_mul, add_comm (x _)]`. Both sides reduce to the same expression. Establish `key` using `fun g : GA F 2 => (hM (NA F) (ratN F 2 1) hco μ D hF).2 (fun x => φ (unip x * g)) (hper g)`. Use `⟨fun g => (key g).1 (hc.comp (hu.mul continuous_const)), fun y g => ?_, fun a g => ?_⟩` and prove the remaining obligations.

Unfold `cterm`. Use `Eq.trans ?_ ((key g).2.1 fun _ => y)` and prove the remaining obligations. Use `congrArg (integral (μ.restrict D)) (funext fun x => ?_)` and prove the remaining obligations. Rewrite using `[hx, hx, ← mul_assoc, cb_aff_mul, one_mul, Units.val_one, one_mul, add_comm y]`. Both sides reduce to the same expression.

Set `u : (Ad F)ˣ` to `Units.map (algebraMap F (Ad F)).toMonoidHom a`. Unfold `cterm`. Use `Eq.trans ?_ ((key g).2.2 (cb_scale F u⁻¹) fun x => ⟨fun h => ?_, fun h => cb_mem F ((a⁻¹ : Fˣ) : F) x h⟩)` and prove the remaining obligations. Use `congrArg (integral (μ.restrict D)) (funext fun x => ?_)` and prove the remaining obligations. Use `Eq.trans ?_ (hl (aff a 0) _)` and prove the remaining obligations.

Rewrite using `[hx, hx, cb_rat_aff, map_zero, ← mul_assoc, ← mul_assoc, cb_aff_mul, cb_aff_mul, one_mul, mul_one, mul_zero, zero_add, add_zero]`. Express the relevant statement in the definitionally equal form `φ (aff u _ * g) = φ (aff u ((u : Ad F) * (((u⁻¹ : (Ad F)ˣ) : Ad F) * x _)) * g)`. Rewrite using `[Units.mul_inv_cancel_left]`. Establish `h2` using `cb_mem F (a : F) _ h`. Establish `e : (fun p => algebraMap F (Ad F) (a : F) * cb_scale F u⁻¹ x p) = x`.

Use function extensionality and compare the values at `fun p => Units.mul_inv_cancel_left u (x p)`. Rewrite `h2` using `[e]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.eisenstein_constantTerm_of_periodMean_of_upperBlock :
    UpperTheory.V.Sd.Eis.PerMean → UpperTheory.V.Sd.Eis.BlockTop → UpperTheory.V.Sd.Eis.CtBasic := by
  intro hM hB F _ _ _ _ μ _ D hF φ hc hl
  obtain ⟨i1, i2, i3, i4, hco, hu, hx⟩ := hB F
  have hper : ∀ (h : GA F 2), ∀ γ ∈ ratN F 2 1, ∀ x : NA F, φ (unip (γ + x) * h) = φ (unip x * h) := by
    rintro h _ ⟨y, rfl⟩ x
    rw [hx, hx x]
    refine Eq.trans ?_ (hl (aff 1 (y ⟨(0, 1), by decide⟩)) _)
    rw [← mul_assoc, cb_rat_aff, cb_aff_mul, map_one, one_mul, Units.val_one, one_mul, add_comm (x _)]
    rfl
  have key := fun g : GA F 2 =>
    (hM (NA F) (ratN F 2 1) hco μ D hF).2 (fun x => φ (unip x * g)) (hper g)
  refine ⟨fun g => (key g).1 (hc.comp (hu.mul continuous_const)), fun y g => ?_, fun a g => ?_⟩
  · unfold cterm
    refine Eq.trans ?_ ((key g).2.1 fun _ => y)
    refine congrArg (integral (μ.restrict D)) (funext fun x => ?_)
    rw [hx, hx, ← mul_assoc, cb_aff_mul, one_mul, Units.val_one, one_mul, add_comm y]
    rfl
  · let u : (Ad F)ˣ := Units.map (algebraMap F (Ad F)).toMonoidHom a
    unfold cterm
    refine Eq.trans ?_ ((key g).2.2 (cb_scale F u⁻¹) fun x => ⟨fun h => ?_, fun h => cb_mem F ((a⁻¹ : Fˣ) : F) x h⟩)
    · refine congrArg (integral (μ.restrict D)) (funext fun x => ?_)
      refine Eq.trans ?_ (hl (aff a 0) _)
      rw [hx, hx, cb_rat_aff, map_zero, ← mul_assoc, ← mul_assoc, cb_aff_mul, cb_aff_mul, one_mul, mul_one,
        mul_zero, zero_add, add_zero]
      change φ (aff u _ * g) = φ (aff u ((u : Ad F) * (((u⁻¹ : (Ad F)ˣ) : Ad F) * x _)) * g)
      rw [Units.mul_inv_cancel_left]
    · have h2 := cb_mem F (a : F) _ h
      have e : (fun p => algebraMap F (Ad F) (a : F) * cb_scale F u⁻¹ x p) = x :=
        funext fun p => Units.mul_inv_cancel_left u (x p)
      rwa [e] at h2
