import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GaloisRepOfPolarizedPair

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.Published.PolarizedPairModel

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

def evalOne (V : Submodule ℂ (Sm L 1)) : V →ₗ[ℂ] ℂ where
  toFun φ := φ.1.1 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

abbrev line (ξ : HChar L) : CuspSub L 1 := (CuspSub.triv L (le_refl 1)).twist ξ

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `φ h`. Take `⟨⟨φ, hφ⟩, rfl⟩` from `((CuspSub.triv L (le_refl 1)).toTwist ξ).surjective φ`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hφ`. Establish `h2 : (mulChi 1 ξ (c • oneFn L 1)).1 1 = 0` using `h`.

Rewrite `h2` using `[mulChi_apply, map_one]`. Express the relevant statement in the definitionally equal form `c * 1 * _ = 0 at h2`. Establish `: c = 0` using `by simpa using h2`. Substitute `this` using the available equality. Rewrite using `[← map_zero ((CuspSub.triv L (le_refl 1)).toTwist ξ)]`.

Conclude with `congrArg _ (Subtype.ext (zero_smul _ _))`. Use `⟨(CuspSub.triv L (le_refl 1)).toTwist ξ ⟨oneFn L 1, Submodule.mem_span_singleton_self _⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(mulChi 1 ξ (oneFn L 1)).1 1 = 1`. Rewrite using `[mulChi_apply, map_one]`. Express the relevant statement in the definitionally equal form `(1 : ℂ) * _ = 1`.

Simplify using the standard rewrite rules.
-/
theorem evalOne_line (ξ : HChar L) :
    (∀ φ : (line ξ).V, evalOne _ φ = 0 → φ = 0) ∧ ∃ φ : (line ξ).V, evalOne _ φ = 1 := by
  constructor
  · intro φ h
    obtain ⟨⟨φ, hφ⟩, rfl⟩ := ((CuspSub.triv L (le_refl 1)).toTwist ξ).surjective φ
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
    have h2 : (mulChi 1 ξ (c • oneFn L 1)).1 1 = 0 := h
    rw [mulChi_apply, map_one] at h2
    change c * 1 * _ = 0 at h2
    have : c = 0 := by simpa using h2
    subst this
    rw [← map_zero ((CuspSub.triv L (le_refl 1)).toTwist ξ)]
    exact congrArg _ (Subtype.ext (zero_smul _ _))
  · refine ⟨(CuspSub.triv L (le_refl 1)).toTwist ξ ⟨oneFn L 1, Submodule.mem_span_singleton_self _⟩, ?_⟩
    change (mulChi 1 ξ (oneFn L 1)).1 1 = 1
    rw [mulChi_apply, map_one]
    change (1 : ℂ) * _ = 1
    simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨B, h1, -, hf, hk, hl⟩ o`. Take `⟨φ, hφ⟩` from `(evalOne_line μ).2`. Choose the witnesses or unpack the hypotheses as in `⟨ψ, hψ⟩ : ∃ ψ, B φ ψ ≠ 0 := by`. Assume the negation of the conclusion as `hc`.

Use `push Not at hc`. Rewrite `hφ` using `[h1 φ hc, map_zero]`. Conclude with `zero_ne_one hφ`. Consider the cases of `o with`. Consider the case `fin k`.

Establish `h` using `hf k φ ψ`. Rewrite `h` using `[CuspSub.op_triv_twist, CuspSub.op_triv_twist]`. Simplify using `only [conjOp, opTriv, opAdd, mul_one, add_zero, map_smul, LinearMap.smul_apply, smul_eq_mul] at h`. Use `⟨Units.ext (mul_right_cancel₀ hψ ?_), by simp [conjOp, opAdd]⟩` and prove the remaining obligations. Simplify using `only [conjOp, Units.val_mul, Units.val_one, one_mul]`.

Take the linear combination `h`. Consider the case `cpt k`. Establish `h` using `hk k φ ψ`. Rewrite `h` using `[CuspSub.op_triv_twist, CuspSub.op_triv_twist]`. Simplify using `only [conjOp, opTriv, opAdd, mul_one, add_zero, map_smul, LinearMap.smul_apply, smul_eq_mul] at h`.

Use `⟨Units.ext (mul_right_cancel₀ hψ ?_), by simp [conjOp, opAdd]⟩` and prove the remaining obligations. Simplify using `only [conjOp, Units.val_mul, Units.val_one, one_mul]`. Take the linear combination `h`. Consider the case `lie X`. Establish `h` using `hl X φ ψ`.

Rewrite `h` using `[CuspSub.op_triv_twist, CuspSub.op_triv_twist]`. Simplify using `only [conjOp, opTriv, mul_zero, zero_add, map_smul, LinearMap.smul_apply, smul_eq_mul] at h`. Use `⟨by simp [conjOp, opMul], mul_right_cancel₀ hψ ?_⟩` and prove the remaining obligations. Simplify using `only [conjOp]`. Take the linear combination `h`.

Introduce `H`. Take `⟨φ₁, h₁⟩` from `(evalOne_line μ).2`. Take `⟨φ₂, h₂⟩` from `(evalOne_line ξ).2`. Use `⟨(LinearMap.mul ℂ ℂ).compl₁₂ (evalOne _) (evalOne _), fun φ h => (evalOne_line μ).1 φ ?_, fun φ h => (evalOne_line ξ).1 φ ?_, fun k φ ψ => ?_, fun k φ ψ => ?_, fun X φ ψ => ?_⟩` and prove the remaining obligations. Simplify `h φ₂` using `[h₂]`.

Simplify `h φ₁` using `[h₁]`. Establish `h` using `congrArg Units.val (H (.fin k)).1`. Rewrite using `[CuspSub.op_triv_twist, CuspSub.op_triv_twist]`. Simplify using `only [conjOp, Units.val_mul, Units.val_one] at h`. Simplify using `only [conjOp, opTriv, opAdd, mul_one, add_zero, map_smul, LinearMap.smul_apply, smul_eq_mul]`.

Rewrite using `[← mul_assoc, mul_comm (Units.val _), h, one_mul]`. Establish `h` using `congrArg Units.val (H (.cpt k)).1`. Rewrite using `[CuspSub.op_triv_twist, CuspSub.op_triv_twist]`. Simplify using `only [conjOp, Units.val_mul, Units.val_one] at h`. Simplify using `only [conjOp, opTriv, opAdd, mul_one, add_zero, map_smul, LinearMap.smul_apply, smul_eq_mul]`.

Rewrite using `[← mul_assoc, mul_comm (Units.val _), h, one_mul]`. Establish `h` using `(H (.lie X)).2`. Rewrite using `[CuspSub.op_triv_twist, CuspSub.op_triv_twist]`. Simplify using `only [conjOp] at h`. Simplify using `only [conjOp, opTriv, mul_zero, zero_add, map_smul, LinearMap.smul_apply, smul_eq_mul]`.

Rewrite using `[← add_mul, h, zero_mul]`.
-/
theorem paired_line (μ ξ : HChar L) : Paired (line μ) (line ξ) conjOp ↔
    ∀ o : Op L 1, opMul μ o * opMul ξ (conjOp o) = 1 ∧ opAdd μ o + opAdd ξ (conjOp o) = 0 := by
  constructor
  · rintro ⟨B, h1, -, hf, hk, hl⟩ o
    obtain ⟨φ, hφ⟩ := (evalOne_line μ).2
    obtain ⟨ψ, hψ⟩ : ∃ ψ, B φ ψ ≠ 0 := by
      by_contra hc
      push Not at hc
      rw [h1 φ hc, map_zero] at hφ
      exact zero_ne_one hφ
    cases o with
    | fin k =>
      have h := hf k φ ψ
      rw [CuspSub.op_triv_twist, CuspSub.op_triv_twist] at h
      simp only [conjOp, opTriv, opAdd, mul_one, add_zero, map_smul, LinearMap.smul_apply, smul_eq_mul] at h
      refine ⟨Units.ext (mul_right_cancel₀ hψ ?_), by simp [conjOp, opAdd]⟩
      simp only [conjOp, Units.val_mul, Units.val_one, one_mul]
      linear_combination h
    | cpt k =>
      have h := hk k φ ψ
      rw [CuspSub.op_triv_twist, CuspSub.op_triv_twist] at h
      simp only [conjOp, opTriv, opAdd, mul_one, add_zero, map_smul, LinearMap.smul_apply, smul_eq_mul] at h
      refine ⟨Units.ext (mul_right_cancel₀ hψ ?_), by simp [conjOp, opAdd]⟩
      simp only [conjOp, Units.val_mul, Units.val_one, one_mul]
      linear_combination h
    | lie X =>
      have h := hl X φ ψ
      rw [CuspSub.op_triv_twist, CuspSub.op_triv_twist] at h
      simp only [conjOp, opTriv, mul_zero, zero_add, map_smul, LinearMap.smul_apply, smul_eq_mul] at h
      refine ⟨by simp [conjOp, opMul], mul_right_cancel₀ hψ ?_⟩
      simp only [conjOp]
      linear_combination h
  · intro H
    obtain ⟨φ₁, h₁⟩ := (evalOne_line μ).2
    obtain ⟨φ₂, h₂⟩ := (evalOne_line ξ).2
    refine ⟨(LinearMap.mul ℂ ℂ).compl₁₂ (evalOne _) (evalOne _), fun φ h => (evalOne_line μ).1 φ ?_,
      fun φ h => (evalOne_line ξ).1 φ ?_, fun k φ ψ => ?_, fun k φ ψ => ?_, fun X φ ψ => ?_⟩
    · simpa [h₂] using h φ₂
    · simpa [h₁] using h φ₁
    · have h := congrArg Units.val (H (.fin k)).1
      rw [CuspSub.op_triv_twist, CuspSub.op_triv_twist]
      simp only [conjOp, Units.val_mul, Units.val_one] at h
      simp only [conjOp, opTriv, opAdd, mul_one, add_zero, map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [← mul_assoc, mul_comm (Units.val _), h, one_mul]
    · have h := congrArg Units.val (H (.cpt k)).1
      rw [CuspSub.op_triv_twist, CuspSub.op_triv_twist]
      simp only [conjOp, Units.val_mul, Units.val_one] at h
      simp only [conjOp, opTriv, opAdd, mul_one, add_zero, map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [← mul_assoc, mul_comm (Units.val _), h, one_mul]
    · have h := (H (.lie X)).2
      rw [CuspSub.op_triv_twist, CuspSub.op_triv_twist]
      simp only [conjOp] at h
      simp only [conjOp, opTriv, mul_zero, zero_add, map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [← add_mul, h, zero_mul]

/- English proof (translation)
Rewrite using `[DualIsConjBy, ← CuspSub.twist_mul]`. Conclude with `paired_line _ _`.
-/
theorem dualIsConjBy_line (ξ ψ : HChar L) : DualIsConjBy (line ξ) ψ ↔
    ∀ o : Op L 1, opMul (ξ * ψ⁻¹) o * opMul ξ (conjOp o) = 1 ∧ opAdd (ξ * ψ⁻¹) o + opAdd ξ (conjOp o) = 0 := by
  rw [DualIsConjBy, ← CuspSub.twist_mul]
  exact paired_line _ _

/- English proof (translation)
Consider the cases of `o with`. Consider the case `fin k`. Use `⟨?_, by simp [thetaOp, conjOp, opAdd]⟩` and prove the remaining obligations. Establish `e : GeneralLinearGroup.det (GeneralLinearGroup.map (conjFin (IsCMField.complexConj L).toRingEquiv) k) = Units.map (conjFin (IsCMField.complexConj L).toRingEquiv).toMonoidHom (GeneralLinearGroup.det k)` using `Units.ext (RingHom.map_det _ _).symm`. Simplify using `only [thetaOp, conjOp, opMul, chiDet, MonoidHom.comp_apply, det_finGL, det_thetaGL, e]`.

Rewrite using `[← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]`. Consider the case `cpt k`. Use `⟨?_, by simp [thetaOp, conjOp, opAdd]⟩` and prove the remaining obligations. Simplify using `only [thetaOp, conjOp, opMul, map_mul, map_inv, mul_inv_cancel_comm]`. Simplify using `only [chiDet, MonoidHom.comp_apply, det_infGL]`.

Rewrite using `[← map_mul, ← map_mul]`. Establish `e : GeneralLinearGroup.det (Unitary.toUnits k : GL (Fin a) (Cinf L)) * GeneralLinearGroup.det (Unitary.toUnits (barK k) : GL (Fin a) (Cinf L)) = 1`. Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `k.1.det * ((star k.1)ᵀ).det = 1`. Rewrite using `[Matrix.det_transpose, ← Matrix.det_mul, Matrix.mem_unitaryGroup_iff.1 k.2, Matrix.det_one]`.

Rewrite using `[e, map_one, map_one]`. Consider the case `lie X`. Use `⟨by simp [thetaOp, conjOp, opMul], ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `dchi ξ (-(GlobalTheory.Tw.Phi a (Cinf L) * (Matrix.of X)ᴴ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ)).trace + dchi ξ (Matrix.of fun i j => star (X i j)).trace = 0`. Rewrite using `[CG.trace_theta, ← map_add]`.

Simplify using `[Matrix.trace, star_sum]`.
-/
theorem op_theta_conj {a : ℕ} (ξ : HChar L) (o : Op L a) :
    opMul ξ (thetaOp o) * opMul ξ (conjOp o) = 1 ∧ opAdd ξ (thetaOp o) + opAdd ξ (conjOp o) = 0 := by
  cases o with
  | fin k =>
    refine ⟨?_, by simp [thetaOp, conjOp, opAdd]⟩
    have e : GeneralLinearGroup.det (GeneralLinearGroup.map (conjFin (IsCMField.complexConj L).toRingEquiv) k) =
        Units.map (conjFin (IsCMField.complexConj L).toRingEquiv).toMonoidHom (GeneralLinearGroup.det k) :=
      Units.ext (RingHom.map_det _ _).symm
    simp only [thetaOp, conjOp, opMul, chiDet, MonoidHom.comp_apply, det_finGL, det_thetaGL, e]
    rw [← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
  | cpt k =>
    refine ⟨?_, by simp [thetaOp, conjOp, opAdd]⟩
    simp only [thetaOp, conjOp, opMul, map_mul, map_inv, mul_inv_cancel_comm]
    simp only [chiDet, MonoidHom.comp_apply, det_infGL]
    rw [← map_mul, ← map_mul]
    have e : GeneralLinearGroup.det (Unitary.toUnits k : GL (Fin a) (Cinf L)) *
        GeneralLinearGroup.det (Unitary.toUnits (barK k) : GL (Fin a) (Cinf L)) = 1 := by
      apply Units.ext
      change k.1.det * ((star k.1)ᵀ).det = 1
      rw [Matrix.det_transpose, ← Matrix.det_mul, Matrix.mem_unitaryGroup_iff.1 k.2, Matrix.det_one]
    rw [e, map_one, map_one]
  | lie X =>
    refine ⟨by simp [thetaOp, conjOp, opMul], ?_⟩
    change dchi ξ (-(GlobalTheory.Tw.Phi a (Cinf L) * (Matrix.of X)ᴴ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ)).trace +
      dchi ξ (Matrix.of fun i j => star (X i j)).trace = 0
    rw [CG.trace_theta, ← map_add]
    simp [Matrix.trace, star_sum]

/- English proof (translation)
Rewrite using `[dualIsConjBy_line, GlobalTheory.GalOfCusp.IsConjDualBy, ← CuspSub.twist_mul]`. Prove the components needed by the constructor for the conclusion. Introduce `H`. Use `⟨((CuspSub.triv L (le_refl 1)).toTwist ξ).symm.trans ((CuspSub.triv L (le_refl 1)).toTwist _), fun o φ => ?_⟩` and prove the remaining obligations. Establish `h1 : opMul ξ (thetaOp o) = opMul (ξ * ψ⁻¹) o` using `mul_right_cancel ((op_theta_conj ξ o).1.trans (H o).1.symm)`.

Establish `h2 : opAdd ξ (thetaOp o) = opAdd (ξ * ψ⁻¹) o` using `add_right_cancel ((op_theta_conj ξ o).2.trans (H o).2.symm)`. Rewrite using `[CuspSub.op_triv_twist, CuspSub.op_triv_twist, map_smul, h1, h2]`. Apply the tactic sequence `cases o <;> rfl`. Introduce and unpack `⟨T, hT⟩ o`. Establish `h` using `CG.scalar_eq T (hT o)`.

Establish `h'` using `op_theta_conj ξ o`. Consider the cases of `o with`. Consider the case `fin k`. Establish `: opMul ξ (thetaOp (.fin k)) = opMul (ξ * ψ⁻¹) (.fin k)` using `Units.ext (by simpa [opTriv, opAdd, thetaOp] using h)`. Conclude with `⟨this ▸ h'.1, by simp [conjOp, opAdd]⟩`.

Consider the case `cpt k`. Establish `: opMul ξ (thetaOp (.cpt k)) = opMul (ξ * ψ⁻¹) (.cpt k)` using `Units.ext (by simpa [opTriv, opAdd, thetaOp] using h)`. Conclude with `⟨this ▸ h'.1, by simp [conjOp, opAdd]⟩`. Consider the case `lie X`. Establish `: opAdd ξ (thetaOp (.lie X)) = opAdd (ξ * ψ⁻¹) (.lie X)` using `by simpa [opTriv, thetaOp] using h`.

Conclude with `⟨by simp [conjOp, opMul], this ▸ h'.2⟩`.
-/
theorem dualIsConjBy_line_iff (ξ ψ : HChar L) :
    DualIsConjBy (line ξ) ψ ↔ GlobalTheory.GalOfCusp.IsConjDualBy (line ξ) ψ := by
  rw [dualIsConjBy_line, GlobalTheory.GalOfCusp.IsConjDualBy, ← CuspSub.twist_mul]
  constructor
  · intro H
    refine ⟨((CuspSub.triv L (le_refl 1)).toTwist ξ).symm.trans ((CuspSub.triv L (le_refl 1)).toTwist _), fun o φ => ?_⟩
    have h1 : opMul ξ (thetaOp o) = opMul (ξ * ψ⁻¹) o :=
      mul_right_cancel ((op_theta_conj ξ o).1.trans (H o).1.symm)
    have h2 : opAdd ξ (thetaOp o) = opAdd (ξ * ψ⁻¹) o :=
      add_right_cancel ((op_theta_conj ξ o).2.trans (H o).2.symm)
    rw [CuspSub.op_triv_twist, CuspSub.op_triv_twist, map_smul, h1, h2]
    cases o <;> rfl
  · rintro ⟨T, hT⟩ o
    have h := CG.scalar_eq T (hT o)
    have h' := op_theta_conj ξ o
    cases o with
    | fin k =>
      have : opMul ξ (thetaOp (.fin k)) = opMul (ξ * ψ⁻¹) (.fin k) :=
        Units.ext (by simpa [opTriv, opAdd, thetaOp] using h)
      exact ⟨this ▸ h'.1, by simp [conjOp, opAdd]⟩
    | cpt k =>
      have : opMul ξ (thetaOp (.cpt k)) = opMul (ξ * ψ⁻¹) (.cpt k) :=
        Units.ext (by simpa [opTriv, opAdd, thetaOp] using h)
      exact ⟨this ▸ h'.1, by simp [conjOp, opAdd]⟩
    | lie X =>
      have : opAdd ξ (thetaOp (.lie X)) = opAdd (ξ * ψ⁻¹) (.lie X) := by simpa [opTriv, thetaOp] using h
      exact ⟨by simp [conjOp, opMul], this ▸ h'.2⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => ⟨h.sign, (dualIsConjBy_line_iff _ _).1 h.dual⟩, fun h => ⟨h.sign, (dualIsConjBy_line_iff _ _).2 h.dual⟩⟩`.
-/
theorem polarizedPair_line_iff (ξ : HChar L) (χ : HChar (maximalRealSubfield L)) :
    PolarizedPair (line ξ) χ ↔ GlobalTheory.GalOfCusp.IsPolarized (line ξ) χ :=
  ⟨fun h => ⟨h.sign, (dualIsConjBy_line_iff _ _).1 h.dual⟩, fun h => ⟨h.sign, (dualIsConjBy_line_iff _ _).2 h.dual⟩⟩

/- English proof (translation)
Rewrite using `[polarizedPair_line_iff, line, CuspSub.twist_one]`. Conclude with `GlobalTheory.GalOfCusp.isPolarized_triv.symm`.
-/
theorem hyp_triv : (CG.mk (line (1 : HChar L))).IsRegAlg ∧
    PolarizedPair (line (1 : HChar L)) (GlobalTheory.GalOfCusp.quadChar L ^ 1) := by
  rw [polarizedPair_line_iff, line, CuspSub.twist_one]
  exact GlobalTheory.GalOfCusp.isPolarized_triv.symm

/- English proof (translation)
Introduce `h` and use `by obtain ⟨v⟩ : Nonempty (InfinitePlace (maximalRealSubfield L)) := inferInstance have h1 : (1 : ℂˣ) = (-1) ^ 1 := h.sign v have := congrArg Units.val h1 norm_num at this`.
-/
theorem not_pol_one (π : CuspSub L 1) : ¬ PolarizedPair π 1 := fun h => by
  obtain ⟨v⟩ : Nonempty (InfinitePlace (maximalRealSubfield L)) := inferInstance
  have h1 : (1 : ℂˣ) = (-1) ^ 1 := h.sign v
  have := congrArg Units.val h1
  norm_num at this

end GlobalTheory.Published.PolarizedPairModel

end
