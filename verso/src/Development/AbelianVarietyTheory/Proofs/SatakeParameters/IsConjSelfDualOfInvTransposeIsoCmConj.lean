import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub

noncomputable section

open NumberField Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.CsdFromConj

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {a : ℕ}

/- English proof (translation)
Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Treat this case separately. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
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
A detailed English derivation is pending.
-/
theorem invT_map {R : Type} [CommRing R] (c : R →+* R) (g : GL (Fin a) R) :
    invT a R (GeneralLinearGroup.map c g) = GeneralLinearGroup.map c (invT a R g) :=
  Units.ext (by rw [show (invT a R (GeneralLinearGroup.map c g)).val = ((GeneralLinearGroup.map c g)⁻¹).valᵀ from rfl,
    ← map_inv]; rfl)

omit [NumberField L] [IsCMField L] in

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem barK_barK (k : Kinf L a) : barK (barK k) = k := by
  refine Subtype.ext ?_
  ext i j : 1
  simp [barK, Matrix.star_apply]

def phiG (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) : GA L a :=
  finGL L a (PhiU a (Af L)) * infGL L a (Unitary.toUnits (PhiK L a))

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem toUnits_PhiK : Unitary.toUnits (PhiK L a) = PhiU a (Cinf L) := Units.ext rfl

/- English proof (translation)
Split into cases according to the possible forms of the given data. Treat this case separately. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Treat this case separately. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Treat this case separately. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Rewrite the indicated hypotheses using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
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
A detailed English derivation is pending.
-/
theorem rt_phiG : rt L a (phiG L a) = act (.fin (PhiU a (Af L))) * act (.cpt (PhiK L a)) := map_mul _ _ _

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem act_fin_inv (k : GL (Fin a) (Af L)) : act (.fin k) * act (.fin k⁻¹) = 1 := by
  change finRep L a k * finRep L a k⁻¹ = 1
  rw [← map_mul, mul_inv_cancel, map_one]

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem act_fin_inv' (k : GL (Fin a) (Af L)) : act (.fin k⁻¹) * act (.fin k) = 1 := by
  change finRep L a k⁻¹ * finRep L a k = 1
  rw [← map_mul, inv_mul_cancel, map_one]

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem act_cpt_inv (k : Kinf L a) : act (.cpt k) * act (.cpt k⁻¹) = 1 := by
  change cptRep L a k * cptRep L a k⁻¹ = 1
  rw [← map_mul, mul_inv_cancel, map_one]

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
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
A detailed English derivation is pending.
-/
theorem op_thetaOp_phiEquiv (π : CuspSub L a) (o : Op L a) (φ : π.V) :
    π.op (thetaOp o) (phiEquiv π φ) = phiEquiv π (π.op (conjOp (invTOp o)) φ) := Subtype.ext <| by
  change act (thetaOp o) (act (.fin (PhiU a (Af L))) (act (.cpt (PhiK L a)) φ.1)) =
    act (.fin (PhiU a (Af L))) (act (.cpt (PhiK L a)) (act (conjOp (invTOp o)) φ.1))
  have h := LinearMap.congr_fun (act_thetaOp (L := L) (a := a) o) φ.1
  rw [rt_phiG] at h
  exact h

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Simplify using the standard rewrite rules.
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
