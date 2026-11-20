import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.TracePow

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix UpperTheory.ConvolutionTheory.Loc

namespace UpperTheory.Gal.LocD

section

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

private def dg (E : Type) [Field E] (n : ℕ) : borel E (Fin n) →* (Fin n → Eˣ) :=
  (leviTorus E (Fin n)).symm.toMonoidHom.comp (leviProj E (points (Fin n)))

/- English proof (translation)
Use `show (GeneralLinearGroup.det (leviProj E (points (Fin n)) b i) : E) = _`. Rewrite using `[GeneralLinearGroup.val_det_apply, Matrix.det_unique]`. Conclude with `leviProj_apply E (points (Fin n)) b i _ _`.
-/
private theorem dg_val (b : borel E (Fin n)) (i : Fin n) :
    ((dg E n b i : Eˣ) : E) = ((b : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i i := by
  show (GeneralLinearGroup.det (leviProj E (points (Fin n)) b i) : E) = _
  rw [GeneralLinearGroup.val_det_apply, Matrix.det_unique]
  exact leviProj_apply E (points (Fin n)) b i _ _

/- English proof (translation)
Establish `hv : valuation E ((Units.map (σ : E →* E) x * x⁻¹ : Eˣ) : E) = 1`. Establish `hx : valuation E (x : E) ≠ 0` using `by simp`. Simplify using `only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, Units.val_inv_eq_inv_val, map_mul, map_inv₀]`. Rewrite using `[hσ]`. Conclude with `mul_inv_cancel₀ hx`.

Establish `h1` using `isUnram_absPow E s _ hv`. Establish `h2 : Units.map (σ : E →* E) x = (Units.map (σ : E →* E) x * x⁻¹) * x` using `by group`. Rewrite using `[h2, map_mul, h1, one_mul]`.
-/
private theorem absPow_map (σ : E ≃+* E) (hσ : Isom σ) (s : ℂ) (x : Eˣ) :
    absPow E s (Units.map (σ : E →* E) x) = absPow E s x := by
  have hv : valuation E ((Units.map (σ : E →* E) x * x⁻¹ : Eˣ) : E) = 1 := by
    have hx : valuation E (x : E) ≠ 0 := by simp
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
    rw [hσ]
    exact mul_inv_cancel₀ hx
  have h1 := isUnram_absPow E s _ hv
  have h2 : Units.map (σ : E →* E) x = (Units.map (σ : E →* E) x * x⁻¹) * x := by group
  rw [h2, map_mul, h1, one_mul]

private def dl (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) :
    borel E (Fin n) →* ℂˣ :=
  (deltaHalf E (fun _ : Fin n => Unit)).comp (leviProj E (points (Fin n)))

/- English proof (translation)
The claim follows from `deltaHalf_apply E _`.
-/
private theorem dl_eq (b : borel E (Fin n)) :
    dl E n b = ∏ i, absPow E ((modExp (fun _ : Fin n => Unit) i : ℂ) / 2) (dg E n b i) :=
  deltaHalf_apply E _

end

/- English proof (translation)
Introduce `E _ _ _ _ n σ hσ V _ _ π μ hμ l hl`. Use `⟨dl E n * μ.comp (dg E n), ?_, ?_⟩` and prove the remaining obligations. Introduce `b b' hbb'`. Establish `hd : dg E n b' = fun i => Units.map (σ : E →* E) (dg E n b i)`. Use function extensionality and compare the values at `i`.

Use `ext`. Rewrite using `[dg_val, hbb', Units.coe_map, dg_val]`. Simplify using `only [sg, Matrix.GeneralLinearGroup.map_apply]`. Both sides reduce to the same expression. Simplify using `only [MonoidHom.mul_apply, MonoidHom.comp_apply, dl_eq, hd, hμ, absPow_map σ hσ]`.

Introduce `b v`. Take `⟨u, hu, hbu⟩` from `exists_levi_mul_unip E (points (Fin n)) b`. Establish `hq : (Submodule.Quotient.mk (π u v) : Jacquet π (unipB E (Fin n))) = Submodule.Quotient.mk v`. Rewrite using `[Submodule.Quotient.eq]`. Apply `Submodule.subset_span` to reduce the goal to its premises.

Conclude with `⟨⟨u, hu⟩, v, by simp⟩`. Establish `hL : leviTorus E (Fin n) (dg E n b) = leviProj E (points (Fin n)) b` using `MulEquiv.apply_symm_apply _ _`. Establish `ht : jacB π (dg E n b) (Submodule.Quotient.mk (π u v)) = jac (points (Fin n)) π (leviProj E (points (Fin n)) b) (Submodule.Quotient.mk (π u v))` using `by show jac (points (Fin n)) π (leviTorus E (Fin n) (dg E n b)) _ = _`. Conclude with `congrArg (fun g => jac (points (Fin n)) π g (Submodule.Quotient.mk (π u v))) hL`. Establish `h2 : l (jacB π (dg E n b) (Submodule.Quotient.mk (π u v))) = (((deltaHalf E (fun _ : Fin n => Unit) (leviProj E (points (Fin n)) b))⁻¹ : ℂˣ) : ℂ) * l (Submodule.Quotient.mk ((π (leviEmb E (points (Fin n)) (leviProj E (points (Fin n)) b))) (π u v)))`.

Rewrite using `[ht, jac_mk]`. Conclude with `map_smul l _ _`. Establish `hX : l (Submodule.Quotient.mk ((π (leviEmb E (points (Fin n)) (leviProj E (points (Fin n)) b))) (π u v)) : Jacquet π (unipB E (Fin n))) = ((deltaHalf E (fun _ : Fin n => Unit) (leviProj E (points (Fin n)) b) : ℂˣ) : ℂ) * ((μ (dg E n b) : ℂ) * l (Submodule.Quotient.mk v))`. Rewrite using `[← hq, ← hl, h2, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]`. Rewrite using `[hbu, map_mul, Module.End.mul_apply, hX, MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul, mul_assoc]`.

Both sides reduce to the same expression.
-/
theorem toBorel : ToBorel := by
  intro E _ _ _ _ n σ hσ V _ _ π μ hμ l hl
  refine ⟨dl E n * μ.comp (dg E n), ?_, ?_⟩
  · intro b b' hbb'
    have hd : dg E n b' = fun i => Units.map (σ : E →* E) (dg E n b i) := by
      funext i
      ext
      rw [dg_val, hbb', Units.coe_map, dg_val]
      simp only [sg, Matrix.GeneralLinearGroup.map_apply]
      rfl
    simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, dl_eq, hd, hμ, absPow_map σ hσ]
  · intro b v
    obtain ⟨u, hu, hbu⟩ := exists_levi_mul_unip E (points (Fin n)) b
    have hq : (Submodule.Quotient.mk (π u v) : Jacquet π (unipB E (Fin n))) = Submodule.Quotient.mk v := by
      rw [Submodule.Quotient.eq]
      apply Submodule.subset_span
      exact ⟨⟨u, hu⟩, v, by simp⟩
    have hL : leviTorus E (Fin n) (dg E n b) = leviProj E (points (Fin n)) b :=
      MulEquiv.apply_symm_apply _ _
    have ht : jacB π (dg E n b) (Submodule.Quotient.mk (π u v))
        = jac (points (Fin n)) π (leviProj E (points (Fin n)) b) (Submodule.Quotient.mk (π u v)) := by
      show jac (points (Fin n)) π (leviTorus E (Fin n) (dg E n b)) _ = _
      exact congrArg (fun g => jac (points (Fin n)) π g (Submodule.Quotient.mk (π u v))) hL
    have h2 : l (jacB π (dg E n b) (Submodule.Quotient.mk (π u v)))
        = (((deltaHalf E (fun _ : Fin n => Unit) (leviProj E (points (Fin n)) b))⁻¹ : ℂˣ) : ℂ)
          * l (Submodule.Quotient.mk ((π (leviEmb E (points (Fin n)) (leviProj E (points (Fin n)) b))) (π u v))) := by
      rw [ht, jac_mk]
      exact map_smul l _ _
    have hX : l (Submodule.Quotient.mk ((π (leviEmb E (points (Fin n)) (leviProj E (points (Fin n)) b))) (π u v)) : Jacquet π (unipB E (Fin n)))
        = ((deltaHalf E (fun _ : Fin n => Unit) (leviProj E (points (Fin n)) b) : ℂˣ) : ℂ)
          * ((μ (dg E n b) : ℂ) * l (Submodule.Quotient.mk v)) := by
      rw [← hq, ← hl, h2, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    rw [hbu, map_mul, Module.End.mul_apply, hX, MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul, mul_assoc]
    rfl

end UpperTheory.Gal.LocD

end
