import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolarizedPairLineIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinGLMemOfPow

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.ContraPair.Model

namespace GlobalTheory.Published.InvTransposeModel

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Take `⟨χ, rfl⟩` from `RankOne.exists_eq_twist π`. Conclude with `paired_invTOp le_rfl χ`.
-/
theorem rank_one (π : CuspSub E 1) : Paired π π invTOp := by
  obtain ⟨χ, rfl⟩ := RankOne.exists_eq_twist π
  exact paired_invTOp le_rfl χ

/- English proof (translation)
Use `CuspSub.ext (((CuspSub.triv E (Nat.zero_le 1)).irred π.V (fun φ _ => ?_) π.stable).resolve_left π.ne_bot)` and prove the remaining obligations. Use `Submodule.mem_span_singleton.2 ⟨φ.1 1, Subtype.ext (funext fun g => ?_)⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `φ.1 1 * 1 = φ.1 g`. Rewrite using `[mul_one, show g = 1 from Units.ext (Subsingleton.elim _ _)]`.
-/
theorem eq_triv (π : CuspSub E 0) : π = CuspSub.triv E (Nat.zero_le 1) := by
  refine CuspSub.ext (((CuspSub.triv E (Nat.zero_le 1)).irred π.V (fun φ _ => ?_) π.stable).resolve_left π.ne_bot)
  refine Submodule.mem_span_singleton.2 ⟨φ.1 1, Subtype.ext (funext fun g => ?_)⟩
  change φ.1 1 * 1 = φ.1 g
  rw [mul_one, show g = 1 from Units.ext (Subsingleton.elim _ _)]

/- English proof (translation)
Establish `h` using `paired_invTOp (E := E) (Nat.zero_le 1) 1`. Rewrite `h` using `[line, CuspSub.twist_one]`. Rewrite using `[eq_triv π]`. Conclude with `h`.
-/
theorem rank_zero (π : CuspSub E 0) : Paired π π invTOp := by
  have h := paired_invTOp (E := E) (Nat.zero_le 1) 1
  rw [line, CuspSub.twist_one] at h
  rw [eq_triv π]
  exact h

/- English proof (translation)
Take `⟨B, h1, h2, h3, h4, h5⟩` from `h`. Set `T` to `π.toTwist χ`. Use `⟨B.compl₁₂ T.symm.toLinearMap T.symm.toLinearMap, fun φ h => ?_, fun ψ h => ?_, fun k φ ψ => ?_, fun k φ ψ => ?_, fun X φ ψ => ?_⟩` and prove the remaining obligations. Conclude with `T.symm.map_eq_zero_iff.1 (h1 _ fun ψ => by simpa using h (T ψ))`. Conclude with `T.symm.map_eq_zero_iff.1 (h2 _ fun φ => by simpa using h (T φ))`.

Use `all_goals`. Take `⟨φ, rfl⟩` from `T.surjective φ`. Take `⟨ψ, rfl⟩` from `T.surjective ψ`. Simplify using `only [T, CuspSub.op_toTwist, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]`. Establish `e` using `h3 k φ ψ`.

Simplify using `only [invTOp] at e ⊢`. Simplify using `only [opAdd, zero_smul, add_zero, map_smul, LinearMap.smul_apply, e, smul_smul, opMul, chiDet, MonoidHom.comp_apply, det_finGL, det_invT, map_inv]`. Simplify using the standard rewrite rules. Establish `e` using `h4 k φ ψ`. Simplify using `only [invTOp] at e ⊢`.

Simplify using `only [opAdd, zero_smul, add_zero, map_smul, LinearMap.smul_apply, e, smul_smul, opMul, chiDet, MonoidHom.comp_apply, det_infGL, toUnits_barK, det_invT, map_inv]`. Simplify using the standard rewrite rules. Establish `e` using `h5 X φ ψ`. Establish `e2 : opAdd χ (invTOp (.lie X)) = -opAdd χ (.lie X)`. Express the relevant statement in the definitionally equal form `dchi χ (-(Matrix.of X)ᵀ).trace = -dchi χ _`.

Rewrite using `[Matrix.trace_neg, Matrix.trace_transpose, map_neg]`. Establish `e3 : opMul χ (invTOp (.lie X)) = 1` using `rfl`. Establish `e4 : opMul χ (.lie X) = 1` using `rfl`. Rewrite using `[e2, e3, e4]`. Simplify using `only [Units.val_one, one_smul, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]`.

Take the linear combination `e`.
-/
theorem twist {π : CuspSub E a} (h : Paired π π invTOp) (χ : HChar E) : Paired (π.twist χ) (π.twist χ) invTOp := by
  obtain ⟨B, h1, h2, h3, h4, h5⟩ := h
  let T := π.toTwist χ
  refine ⟨B.compl₁₂ T.symm.toLinearMap T.symm.toLinearMap, fun φ h => ?_, fun ψ h => ?_, fun k φ ψ => ?_,
    fun k φ ψ => ?_, fun X φ ψ => ?_⟩
  · exact T.symm.map_eq_zero_iff.1 (h1 _ fun ψ => by simpa using h (T ψ))
  · exact T.symm.map_eq_zero_iff.1 (h2 _ fun φ => by simpa using h (T φ))
  all_goals
    obtain ⟨φ, rfl⟩ := T.surjective φ
    obtain ⟨ψ, rfl⟩ := T.surjective ψ
    simp only [T, CuspSub.op_toTwist, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  · have e := h3 k φ ψ
    simp only [invTOp] at e ⊢
    simp only [opAdd, zero_smul, add_zero, map_smul, LinearMap.smul_apply, e, smul_smul, opMul, chiDet,
      MonoidHom.comp_apply, det_finGL, det_invT, map_inv]
    simp
  · have e := h4 k φ ψ
    simp only [invTOp] at e ⊢
    simp only [opAdd, zero_smul, add_zero, map_smul, LinearMap.smul_apply, e, smul_smul, opMul, chiDet,
      MonoidHom.comp_apply, det_infGL, toUnits_barK, det_invT, map_inv]
    simp
  · have e := h5 X φ ψ
    have e2 : opAdd χ (invTOp (.lie X)) = -opAdd χ (.lie X) := by
      change dchi χ (-(Matrix.of X)ᵀ).trace = -dchi χ _
      rw [Matrix.trace_neg, Matrix.trace_transpose, map_neg]
    have e3 : opMul χ (invTOp (.lie X)) = 1 := rfl
    have e4 : opMul χ (.lie X) = 1 := rfl
    rw [e2, e3, e4]
    simp only [Units.val_one, one_smul, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    linear_combination e

/- English proof (translation)
Introduce `h` and use `by obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance have h3 := ((paired_line_iff _ _ _ _).1 h).2.2 have h4 : ∀ z, dchi (CuspRep.Model.absC E s) z = 0 := fun z => by have := h3 fun _ _ => z simp only [id, sc, opTriv, opAdd, mul_zero, zero_add, Matrix.trace, Fin.sum_univ_one, Matri …`.
-/
theorem not_paired_id {s : ℂ} (hs : s ≠ 0) :
    ¬ Paired (line le_rfl (CuspRep.Model.absC E s)) (line le_rfl (CuspRep.Model.absC E s)) id := fun h => by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h3 := ((paired_line_iff _ _ _ _).1 h).2.2
  have h4 : ∀ z, dchi (CuspRep.Model.absC E s) z = 0 := fun z => by
    have := h3 fun _ _ => z
    simp only [id, sc, opTriv, opAdd, mul_zero, zero_add, Matrix.trace, Fin.sum_univ_one, Matrix.diag,
      Matrix.of_apply] at this
    linear_combination this / 2
  have := CuspRep.Model.expo_absC s τ
  rw [expo, h4, h4] at this
  exact hs (by simpa using this.symm)

omit [IsTotallyComplex E] in

/- English proof (translation)
Simplify using `only [Matrix.transpose_sub, Matrix.transpose_mul, neg_mul_neg, neg_sub]`.
-/
theorem bracket (X Y : Matrix (Fin a) (Fin a) (Cinf E)) :
    -(X * Y - Y * X)ᵀ = (-Xᵀ) * (-Yᵀ) - (-Yᵀ) * (-Xᵀ) := by
  simp only [Matrix.transpose_sub, Matrix.transpose_mul, neg_mul_neg, neg_sub]

end GlobalTheory.Published.InvTransposeModel

end
