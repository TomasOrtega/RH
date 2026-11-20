import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL

noncomputable section

open NumberField Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.ConjDualPair

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {a : ℕ}

variable (L a) in

def phiA : GA L a := finGL L a (PhiU a (Af L)) * infGL L a (PhiU a (Cinf L))

/- English proof (translation)
The claim follows from `Units.ext rfl`.
-/
theorem toUnits_PhiK : Unitary.toUnits (PhiK L a) = PhiU a (Cinf L) := Units.ext rfl

/- English proof (translation)
Use extensionality with `i j`. Both sides reduce to the same expression.
-/
theorem invT_map_invT (c : Af L →+* Af L) (k : GL (Fin a) (Af L)) :
    invT a (Af L) (GeneralLinearGroup.map c (invT a (Af L) k)) = GeneralLinearGroup.map c k := by
  ext i j
  rfl

/- English proof (translation)
Consider the cases of `o with`. Consider the case `fin k`. Express the relevant statement in the definitionally equal form `rt L a (phiA L a) * rt L a (finGL L a _) = rt L a (finGL L a (thetaGL a _ (invT a (Af L) k))) * rt L a (phiA L a)`. Rewrite using `[← map_mul, ← map_mul]`. Use `congr 1`.

Establish `h : thetaGL a (conjFin (IsCMField.complexConj L).toRingEquiv) (invT a (Af L) k) = PhiU a (Af L) * GeneralLinearGroup.map (conjFin (IsCMField.complexConj L).toRingEquiv) k * (PhiU a (Af L))⁻¹`. Express the relevant statement in the definitionally equal form `PhiU a (Af L) * invT a (Af L) (GeneralLinearGroup.map _ (invT a (Af L) k)) * (PhiU a (Af L))⁻¹ = _`. Rewrite using `[invT_map_invT]`. Rewrite using `[h, phiA, map_mul, map_mul, map_inv, mul_assoc, infGL_comm]`. Use `group`.

Consider the case `cpt k`. Express the relevant statement in the definitionally equal form `rt L a (phiA L a) * rt L a (infGL L a (Unitary.toUnits _)) = rt L a (infGL L a (Unitary.toUnits (PhiK L a * barK k * (PhiK L a)⁻¹))) * rt L a (phiA L a)`. Rewrite using `[← map_mul, ← map_mul]`. Use `congr 1`. Rewrite using `[phiA, map_mul, map_mul, map_inv, toUnits_PhiK, map_mul, map_mul, map_inv]`.

Establish `e` using `infGL_comm (E := L) (a := a) (PhiU a (Cinf L) * Unitary.toUnits (barK k) * (PhiU a (Cinf L))⁻¹) (PhiU a (Af L))`. Rewrite `e` using `[map_mul, map_mul, map_inv]`. Rewrite using `[toUnits_PhiK, ← mul_assoc (_ * _ * _) (finGL L a _), e]`. Use `group`. Consider the case `lie X`.

Express the relevant statement in the definitionally equal form `rt L a (phiA L a) * lie L a (fun i j => star (X i j)) = lie L a (toL (-(GlobalTheory.Tw.Phi a (Cinf L) * (Matrix.of (toL (-(Matrix.of X)ᵀ)))ᴴ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ))) * rt L a (phiA L a)`. Rewrite using `[phiA, map_mul, mul_assoc, show (fun i j => star (X i j) : Lie L a) = toL (Matrix.of fun i j => star (X i j)) from rfl, GlobalTheory.CapAdInv.rt_lie, ← mul_assoc, ← lie_rt_fin, mul_assoc]`. Use `congrArg (fun Y => lie L a (toL Y) * _) ?_` and prove the remaining obligations. Establish `h : (Matrix.of (toL (-(Matrix.of X)ᵀ)))ᴴ = -(Matrix.of fun i j => star (X i j))`. Use extensionality with `i j`.

Simplify using `[Matrix.conjTranspose_apply]`. Express the relevant statement in the definitionally equal form `GlobalTheory.Tw.Phi a (Cinf L) * _ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ = _`. Rewrite using `[h, mul_neg, neg_mul, neg_neg]`.
-/
theorem rt_phiA_act (o : Op L a) :
    rt L a (phiA L a) * act (conjOp o) = act (thetaOp (invTOp o)) * rt L a (phiA L a) := by
  cases o with
  | fin k =>
    change rt L a (phiA L a) * rt L a (finGL L a _) = rt L a (finGL L a (thetaGL a _ (invT a (Af L) k))) * rt L a (phiA L a)
    rw [← map_mul, ← map_mul]
    congr 1
    have h : thetaGL a (conjFin (IsCMField.complexConj L).toRingEquiv) (invT a (Af L) k) =
        PhiU a (Af L) * GeneralLinearGroup.map (conjFin (IsCMField.complexConj L).toRingEquiv) k * (PhiU a (Af L))⁻¹ := by
      change PhiU a (Af L) * invT a (Af L) (GeneralLinearGroup.map _ (invT a (Af L) k)) * (PhiU a (Af L))⁻¹ = _
      rw [invT_map_invT]
    rw [h, phiA, map_mul, map_mul, map_inv, mul_assoc, infGL_comm]
    group
  | cpt k =>
    change rt L a (phiA L a) * rt L a (infGL L a (Unitary.toUnits _)) =
      rt L a (infGL L a (Unitary.toUnits (PhiK L a * barK k * (PhiK L a)⁻¹))) * rt L a (phiA L a)
    rw [← map_mul, ← map_mul]
    congr 1
    rw [phiA, map_mul, map_mul, map_inv, toUnits_PhiK, map_mul, map_mul, map_inv]
    have e := infGL_comm (E := L) (a := a) (PhiU a (Cinf L) * Unitary.toUnits (barK k) * (PhiU a (Cinf L))⁻¹)
      (PhiU a (Af L))
    rw [map_mul, map_mul, map_inv] at e
    rw [toUnits_PhiK, ← mul_assoc (_ * _ * _) (finGL L a _), e]
    group
  | lie X =>
    change rt L a (phiA L a) * lie L a (fun i j => star (X i j)) =
      lie L a (toL (-(GlobalTheory.Tw.Phi a (Cinf L) * (Matrix.of (toL (-(Matrix.of X)ᵀ)))ᴴ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ))) *
        rt L a (phiA L a)
    rw [phiA, map_mul, mul_assoc,
      show (fun i j => star (X i j) : Lie L a) = toL (Matrix.of fun i j => star (X i j)) from rfl,
      GlobalTheory.CapAdInv.rt_lie, ← mul_assoc, ← lie_rt_fin, mul_assoc]
    refine congrArg (fun Y => lie L a (toL Y) * _) ?_
    have h : (Matrix.of (toL (-(Matrix.of X)ᵀ)))ᴴ = -(Matrix.of fun i j => star (X i j)) := by
      ext i j
      simp [Matrix.conjTranspose_apply]
    change GlobalTheory.Tw.Phi a (Cinf L) * _ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ = _
    rw [h, mul_neg, neg_mul, neg_neg]

/- English proof (translation)
Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`.
-/
theorem rt_inv_phiA (f : Sm L a) : rt L a (phiA L a)⁻¹ (rt L a (phiA L a) f) = f := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/- English proof (translation)
Introduce `L _ _ _ a π ψ ⟨B, hl, hr, hf, hc, hX⟩ ⟨T, hT⟩`. Set `u : π.V →ₗ[ℂ] π.V` to `π.op (.fin (PhiU a (Af L))) * π.op (.cpt (PhiK L a))`. Establish `hu : ∀ χ : π.V, (u χ).1 = rt L a (phiA L a) χ.1` using `fun χ => by`. Express the relevant statement in the definitionally equal form `rt L a (finGL L a _) (rt L a (infGL L a (Unitary.toUnits (PhiK L a))) χ.1) = _`. Rewrite using `[toUnits_PhiK, phiA, map_mul]`.

Both sides reduce to the same expression. Establish `hkey : ∀ o χ, u (π.op (conjOp o) χ) = π.op (thetaOp (invTOp o)) (u χ)` using `fun o χ => Subtype.ext (by rw [hu, CuspSub.op_val, CuspSub.op_val, hu]; exact LinearMap.congr_fun (rt_phiA_act o) χ.1)`. Establish `hinj : ∀ χ, u χ = 0 → χ = 0` using `fun χ h => Subtype.ext (by`. Establish `e` using `congrArg (fun ξ : π.V => rt L a (phiA L a)⁻¹ ξ.1) h`. Simplify using `only [hu, rt_inv_phiA, ZeroMemClass.coe_zero, map_zero] at e`.

Conclude with `e)`. Establish `hsurj : ∀ χ : π.V, ∃ ξ, u ξ = χ` using `fun χ => ⟨π.op (.cpt (PhiK L a)⁻¹) (π.op (.fin (PhiU a (Af L))⁻¹) χ), Subtype.ext (by`. Rewrite using `[hu]`. Express the relevant statement in the definitionally equal form `rt L a (phiA L a) (rt L a (infGL L a (Unitary.toUnits (PhiK L a)⁻¹)) (rt L a (finGL L a _) χ.1)) = _`. Rewrite using `[← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, map_inv, toUnits_PhiK, phiA, map_inv, map_inv]`.

Use the proof step `simp)⟩`. Use `⟨B.compl₂ (T.toLinearMap ∘ₗ u), fun φ h => hl φ fun ψ' => ?_, fun χ h => hinj χ ?_, fun k φ χ => ?_, fun k φ χ => ?_, fun X φ χ => ?_⟩` and prove the remaining obligations. Take `⟨χ, rfl⟩` from `T.surjective ψ'`. Take `⟨ξ, rfl⟩` from `hsurj χ`. Conclude with `h ξ`.

Conclude with `(LinearEquiv.map_eq_zero_iff T).1 (hr _ h)`. Simplify using `only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]`. Rewrite using `[hkey, hT]`. Conclude with `hf k φ _`. Simplify using `only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]`.

Rewrite using `[hkey, hT]`. Conclude with `hc k φ _`. Simplify using `only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]`. Rewrite using `[hkey, hT]`. Conclude with `hX X φ _`.
-/
theorem dualIsConjBy_of_paired_invT : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) (π : CuspSub L a)
    (ψ : HChar L), Paired (π.twist ψ⁻¹) (π.twist ψ⁻¹) invTOp → GlobalTheory.GalOfCusp.IsConjDualBy π ψ → DualIsConjBy π ψ := by
  intro L _ _ _ a π ψ ⟨B, hl, hr, hf, hc, hX⟩ ⟨T, hT⟩
  let u : π.V →ₗ[ℂ] π.V := π.op (.fin (PhiU a (Af L))) * π.op (.cpt (PhiK L a))
  have hu : ∀ χ : π.V, (u χ).1 = rt L a (phiA L a) χ.1 := fun χ => by
    change rt L a (finGL L a _) (rt L a (infGL L a (Unitary.toUnits (PhiK L a))) χ.1) = _
    rw [toUnits_PhiK, phiA, map_mul]
    rfl
  have hkey : ∀ o χ, u (π.op (conjOp o) χ) = π.op (thetaOp (invTOp o)) (u χ) := fun o χ =>
    Subtype.ext (by rw [hu, CuspSub.op_val, CuspSub.op_val, hu]; exact LinearMap.congr_fun (rt_phiA_act o) χ.1)
  have hinj : ∀ χ, u χ = 0 → χ = 0 := fun χ h => Subtype.ext (by
    have e := congrArg (fun ξ : π.V => rt L a (phiA L a)⁻¹ ξ.1) h
    simp only [hu, rt_inv_phiA, ZeroMemClass.coe_zero, map_zero] at e
    exact e)
  have hsurj : ∀ χ : π.V, ∃ ξ, u ξ = χ := fun χ =>
    ⟨π.op (.cpt (PhiK L a)⁻¹) (π.op (.fin (PhiU a (Af L))⁻¹) χ), Subtype.ext (by
      rw [hu]
      change rt L a (phiA L a) (rt L a (infGL L a (Unitary.toUnits (PhiK L a)⁻¹)) (rt L a (finGL L a _) χ.1)) = _
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, map_inv, toUnits_PhiK, phiA, map_inv,
        map_inv]
      simp)⟩
  refine ⟨B.compl₂ (T.toLinearMap ∘ₗ u), fun φ h => hl φ fun ψ' => ?_, fun χ h => hinj χ ?_,
    fun k φ χ => ?_, fun k φ χ => ?_, fun X φ χ => ?_⟩
  · obtain ⟨χ, rfl⟩ := T.surjective ψ'
    obtain ⟨ξ, rfl⟩ := hsurj χ
    exact h ξ
  · exact (LinearEquiv.map_eq_zero_iff T).1 (hr _ h)
  · simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hkey, hT]
    exact hf k φ _
  · simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hkey, hT]
    exact hc k φ _
  · simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hkey, hT]
    exact hX X φ _

end GlobalTheory.ConjDualPair
