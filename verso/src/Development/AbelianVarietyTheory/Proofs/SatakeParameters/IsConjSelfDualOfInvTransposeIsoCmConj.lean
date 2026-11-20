import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub

noncomputable section

open NumberField Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.CsdFromConj

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {a : ℕ}

/- English proof (translation)
Consider the cases of `o with`. Consider the case `fin k => exact congrArg Op.fin (Units.ext (Matrix.transpose_transpose k.val))`. Consider the case `cpt k`. Use `congrArg Op.cpt (Subtype.ext ?_)` and prove the remaining obligations. Use extensionality with `i j : 1`.

Simplify using `[barK, Matrix.star_apply]`. Consider the case `lie X`. Use `congrArg Op.lie ?_` and prove the remaining obligations. Use function extensionality and compare the values at `i j`. Simplify using `[toL]`.
-/
theorem invTOp_invTOp (o : Op L a) : invTOp (invTOp o) = o := by
  cases o with
  | fin k => exact congrArg Op.fin (Units.ext (Matrix.transpose_transpose k.val))
  | cpt k =>
    refine congrArg Op.cpt (Subtype.ext ?_)
    ext i j : 1
    simp [barK, Matrix.star_apply]
  | lie X =>
    refine congrArg Op.lie ?_
    funext i j
    simp [toL]

/- English proof (translation)
The claim follows from `Units.ext (by rw [show (invT a R (GeneralLinearGroup.map c g)).val = ((GeneralLinearGroup.map c g)⁻¹).valᵀ from rfl, ← map_inv]; rfl)`.
-/
theorem invT_map {R : Type} [CommRing R] (c : R →+* R) (g : GL (Fin a) R) :
    invT a R (GeneralLinearGroup.map c g) = GeneralLinearGroup.map c (invT a R g) :=
  Units.ext (by rw [show (invT a R (GeneralLinearGroup.map c g)).val = ((GeneralLinearGroup.map c g)⁻¹).valᵀ from rfl,
    ← map_inv]; rfl)

omit [NumberField L] [IsCMField L] in

/- English proof (translation)
Use `Subtype.ext ?_` and prove the remaining obligations. Use extensionality with `i j : 1`. Simplify using `[barK, Matrix.star_apply]`.
-/
theorem barK_barK (k : Kinf L a) : barK (barK k) = k := by
  refine Subtype.ext ?_
  ext i j : 1
  simp [barK, Matrix.star_apply]

def phiG (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) : GA L a :=
  finGL L a (PhiU a (Af L)) * infGL L a (Unitary.toUnits (PhiK L a))

/- English proof (translation)
The claim follows from `Units.ext rfl`.
-/
theorem toUnits_PhiK : Unitary.toUnits (PhiK L a) = PhiU a (Cinf L) := Units.ext rfl

/- English proof (translation)
Consider the cases of `o with`. Consider the case `fin k`. Express the relevant statement in the definitionally equal form `rt L a (finGL L a _) * rt L a (phiG L a) = rt L a (phiG L a) * rt L a (finGL L a _)`. Rewrite using `[← map_mul, ← map_mul]`. Use `congr 1`.

Use `ga_ext ?_ ?_` and prove the remaining obligations. Simplify using `[phiG, map_mul]`. Simplify using `only [phiG, map_mul, pFin_finGL, pFin_infGL, mul_one]`. Rewrite using `[thetaGL, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, invT_map]`. Simplify using `[mul_assoc]`.

Consider the case `cpt k`. Express the relevant statement in the definitionally equal form `rt L a (infGL L a (Unitary.toUnits _)) * rt L a (phiG L a) = rt L a (phiG L a) * rt L a (infGL L a (Unitary.toUnits _))`. Rewrite using `[← map_mul, ← map_mul]`. Use `congr 1`. Rewrite using `[barK_barK]`.

Use `ga_ext ?_ ?_` and prove the remaining obligations. Simplify using `[phiG, map_mul, map_inv]`. Simplify using `[phiG, map_mul]`. Consider the case `lie X`. Establish `hY : (fun i j => star (toL (-(Matrix.of X)ᵀ) i j) : Lie L a) = toL (-(Matrix.of X)ᴴ)`.

Use function extensionality and compare the values at `i j`. Simplify using `[toL, Matrix.conjTranspose_apply]`. Establish `hR` using `GlobalTheory.CapAdInv.rt_lie (PhiU a (Cinf L)) (-(Matrix.of X)ᴴ)`. Establish `e : (PhiU a (Cinf L)).val * -(Matrix.of X)ᴴ * ((PhiU a (Cinf L))⁻¹).val = -(GlobalTheory.Tw.Phi a (Cinf L) * (Matrix.of X)ᴴ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ)`. Rewrite using `[Matrix.mul_neg, Matrix.neg_mul]`.

Both sides reduce to the same expression. Rewrite `hR` using `[e]`. Express the relevant statement in the definitionally equal form `lie L a _ * rt L a (phiG L a) = rt L a (phiG L a) * lie L a (fun i j => star (toL (-(Matrix.of X)ᵀ) i j))`. Rewrite using `[hY, phiG, map_mul, toUnits_PhiK, mul_assoc (rt L a (finGL L a _)), hR, ← mul_assoc (rt L a (finGL L a _)), ← lie_rt_fin, mul_assoc (lie L a _)]`.
-/
theorem act_thetaOp (o : Op L a) :
    act (thetaOp o) * rt L a (phiG L a) = rt L a (phiG L a) * act (conjOp (invTOp o)) := by
  cases o with
  | fin k =>
    change rt L a (finGL L a _) * rt L a (phiG L a) = rt L a (phiG L a) * rt L a (finGL L a _)
    rw [← map_mul, ← map_mul]
    congr 1
    refine ga_ext ?_ ?_
    · simp [phiG, map_mul]
    · simp only [phiG, map_mul, pFin_finGL, pFin_infGL, mul_one]
      rw [thetaGL, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, invT_map]
      simp [mul_assoc]
  | cpt k =>
    change rt L a (infGL L a (Unitary.toUnits _)) * rt L a (phiG L a) =
      rt L a (phiG L a) * rt L a (infGL L a (Unitary.toUnits _))
    rw [← map_mul, ← map_mul]
    congr 1
    rw [barK_barK]
    refine ga_ext ?_ ?_
    · simp [phiG, map_mul, map_inv]
    · simp [phiG, map_mul]
  | lie X =>
    have hY : (fun i j => star (toL (-(Matrix.of X)ᵀ) i j) : Lie L a) = toL (-(Matrix.of X)ᴴ) := by
      funext i j
      simp [toL, Matrix.conjTranspose_apply]
    have hR := GlobalTheory.CapAdInv.rt_lie (PhiU a (Cinf L)) (-(Matrix.of X)ᴴ)
    have e : (PhiU a (Cinf L)).val * -(Matrix.of X)ᴴ * ((PhiU a (Cinf L))⁻¹).val =
        -(GlobalTheory.Tw.Phi a (Cinf L) * (Matrix.of X)ᴴ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ) := by
      rw [Matrix.mul_neg, Matrix.neg_mul]; rfl
    rw [e] at hR
    change lie L a _ * rt L a (phiG L a) = rt L a (phiG L a) * lie L a (fun i j => star (toL (-(Matrix.of X)ᵀ) i j))
    rw [hY, phiG, map_mul, toUnits_PhiK, mul_assoc (rt L a (finGL L a _)), hR, ← mul_assoc (rt L a (finGL L a _)),
      ← lie_rt_fin, mul_assoc (lie L a _)]

/- English proof (translation)
The claim follows from `map_mul _ _ _`.
-/
theorem rt_phiG : rt L a (phiG L a) = act (.fin (PhiU a (Af L))) * act (.cpt (PhiK L a)) := map_mul _ _ _

/- English proof (translation)
Express the relevant statement in the definitionally equal form `finRep L a k * finRep L a k⁻¹ = 1`. Rewrite using `[← map_mul, mul_inv_cancel, map_one]`.
-/
theorem act_fin_inv (k : GL (Fin a) (Af L)) : act (.fin k) * act (.fin k⁻¹) = 1 := by
  change finRep L a k * finRep L a k⁻¹ = 1
  rw [← map_mul, mul_inv_cancel, map_one]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `finRep L a k⁻¹ * finRep L a k = 1`. Rewrite using `[← map_mul, inv_mul_cancel, map_one]`.
-/
theorem act_fin_inv' (k : GL (Fin a) (Af L)) : act (.fin k⁻¹) * act (.fin k) = 1 := by
  change finRep L a k⁻¹ * finRep L a k = 1
  rw [← map_mul, inv_mul_cancel, map_one]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `cptRep L a k * cptRep L a k⁻¹ = 1`. Rewrite using `[← map_mul, mul_inv_cancel, map_one]`.
-/
theorem act_cpt_inv (k : Kinf L a) : act (.cpt k) * act (.cpt k⁻¹) = 1 := by
  change cptRep L a k * cptRep L a k⁻¹ = 1
  rw [← map_mul, mul_inv_cancel, map_one]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `cptRep L a k⁻¹ * cptRep L a k = 1`. Rewrite using `[← map_mul, inv_mul_cancel, map_one]`.
-/
theorem act_cpt_inv' (k : Kinf L a) : act (.cpt k⁻¹) * act (.cpt k) = 1 := by
  change cptRep L a k⁻¹ * cptRep L a k = 1
  rw [← map_mul, inv_mul_cancel, map_one]

def phiEquiv (π : CuspSub L a) : π.V ≃ₗ[ℂ] π.V :=
  LinearEquiv.ofLinear (π.op (.fin (PhiU a (Af L))) * π.op (.cpt (PhiK L a)))
    (π.op (.cpt (PhiK L a)⁻¹) * π.op (.fin (PhiU a (Af L))⁻¹))
    (LinearMap.ext fun φ => Subtype.ext <| by
      change act (.fin (PhiU a (Af L))) (act (.cpt (PhiK L a)) (act (.cpt (PhiK L a)⁻¹)
        (act (.fin (PhiU a (Af L))⁻¹) φ.1))) = φ.1
      rw [← Module.End.mul_apply (act (.cpt (PhiK L a))), act_cpt_inv, Module.End.one_apply,
        ← Module.End.mul_apply, act_fin_inv, Module.End.one_apply])
    (LinearMap.ext fun φ => Subtype.ext <| by
      change act (.cpt (PhiK L a)⁻¹) (act (.fin (PhiU a (Af L))⁻¹) (act (.fin (PhiU a (Af L)))
        (act (.cpt (PhiK L a)) φ.1))) = φ.1
      rw [← Module.End.mul_apply (act (.fin (PhiU a (Af L))⁻¹)), act_fin_inv', Module.End.one_apply,
        ← Module.End.mul_apply, act_cpt_inv', Module.End.one_apply])

/- English proof (translation)
The claim follows from `Subtype.ext <| by change act (thetaOp o) (act (.fin (PhiU a (Af L))) (act (.cpt (PhiK L a)) φ.1)) = act (.fin (PhiU a (Af L))) (act (.cpt (PhiK L a)) (act (conjOp (invTOp o)) φ.1)) have h := LinearMap.congr_fun (act_thetaOp (L := L) (a := a) o) φ.1 rw [rt_phiG] at h exact h`.
-/
theorem op_thetaOp_phiEquiv (π : CuspSub L a) (o : Op L a) (φ : π.V) :
    π.op (thetaOp o) (phiEquiv π φ) = phiEquiv π (π.op (conjOp (invTOp o)) φ) := Subtype.ext <| by
  change act (thetaOp o) (act (.fin (PhiU a (Af L))) (act (.cpt (PhiK L a)) φ.1)) =
    act (.fin (PhiU a (Af L))) (act (.cpt (PhiK L a)) (act (conjOp (invTOp o)) φ.1))
  have h := LinearMap.congr_fun (act_thetaOp (L := L) (a := a) o) φ.1
  rw [rt_phiG] at h
  exact h

/- English proof (translation)
Use `⟨(phiEquiv π).symm.trans S.symm, fun o φ => ?_⟩` and prove the remaining obligations. Take `⟨χ, rfl⟩` from `(phiEquiv π).surjective φ`. Take `⟨ψ, rfl⟩` from `S.surjective χ`. Establish `h` using `hS (invTOp o) ψ`. Rewrite `h` using `[invTOp_invTOp]`.

Simplify using `only [LinearEquiv.trans_apply, op_thetaOp_phiEquiv, LinearEquiv.symm_apply_apply, ← h]`.
-/
theorem isCsd_of_invT_conj (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) (π : CuspSub L a)
    (S : π.V ≃ₗ[ℂ] π.V) (hS : ∀ o φ, S (π.op (invTOp o) φ) = π.op (conjOp o) (S φ)) : π.IsCsd := by
  refine ⟨(phiEquiv π).symm.trans S.symm, fun o φ => ?_⟩
  obtain ⟨χ, rfl⟩ := (phiEquiv π).surjective φ
  obtain ⟨ψ, rfl⟩ := S.surjective χ
  have h := hS (invTOp o) ψ
  rw [invTOp_invTOp] at h
  simp only [LinearEquiv.trans_apply, op_thetaOp_phiEquiv, LinearEquiv.symm_apply_apply, ← h]

end GlobalTheory.CsdFromConj
