import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellFunctorTransposedTwoBlockStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellFunctorScalarFirst

open GlobalTheory.PRep GlobalTheory.SmGL Matrix

namespace GlobalTheory

/- English proof (translation)
Introduce `k _ _ _ _ hG χ₁ χ₂ h₁ h₂ u v e ϖ`. Establish `hρ : IsSmooth ((extTensor (detRep (Fin u) χ₁) (detRep (Fin (v + 1)) χ₂)).comp (leviTwo k (Fin u) (Fin (v + 1))).symm.toMonoidHom)`. Use `isSmooth_comp (isSmooth_extTensor ((isSmooth_ofChar_iff _).2 h₁.detChar) ((isSmooth_ofChar_iff _).2 h₂.detChar)) _ ?_` and prove the remaining obligations. Use `show Continuous fun g : Levi k (Two (Fin u) (Fin (v + 1))) => (g false, g true)`. Conclude with `(continuous_apply false).prodMk (continuous_apply true)`.

Establish `H` using `hG k Bool Bool (Fin (u + (v + 1))) (Two (Fin u) (Fin (v + 1))) (Two (Fin 1) (Fin (u + v))) (two (stdSum (rfl : u + (v + 1) = u + (v + 1)))) (two e)`. Take `⟨N, b, hb⟩` from `H`. Establish `H2` using `hb (TensorProduct ℂ ℂ ℂ) ((extTensor (detRep (Fin u) χ₁) (detRep (Fin (v + 1)) χ₂)).comp (leviTwo k (Fin u) (Fin (v + 1))).symm.toMonoidHom) hρ`. Take `⟨S, hmono, hbot, htop, hcell⟩` from `H2`. Set `T : Fin (N + 1) → Subrepresentation (jac₂ e (prod₂ (detRep (Fin u) χ₁) (detRep (Fin (v + 1)) χ₂)))` to `fun t => ⟨(S t).toSubmodule, fun g _ hv => (S t).apply_mem_toSubmodule _ hv⟩`.

Establish `hrow : ∀ B : SizeMatrix (Two (Fin u) (Fin (v + 1))) (Two (Fin 1) (Fin (u + v))), B.1 false false + B.1 false true = u ∧ B.1 true false + B.1 true true = v + 1 ∧ B.1 false false + B.1 true false = 1 ∧ B.1 false true + B.1 true true = u + v`. Introduce `B`. Establish `r0` using `B.2.1 false`. Establish `r1` using `B.2.1 true`. Establish `c0` using `B.2.2 false`.

Establish `c1` using `B.2.2 true`. Simplify using `only [Fintype.sum_bool] at r0 r1 c0 c1`. Simplify using `at r0 r1 c0 c1`. Use linear arithmetic over natural numbers and integers. Set `B0 : SizeMatrix (Two (Fin u) (Fin (v + 1))) (Two (Fin 1) (Fin (u + v)))` to `⟨fun i j => Bool.rec (Bool.rec 0 u j) (Bool.rec 1 v j) i, by`.

Use `⟨fun i => ?_, fun j => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `cases i <;> simp`. Apply the tactic sequence `cases j <;> simp <;> omega⟩`. Establish `hB0 : ∀ B : SizeMatrix (Two (Fin u) (Fin (v + 1))) (Two (Fin 1) (Fin (u + v))), B.1 true false = 1 → B = B0`. Introduce `B hB`.

Take `⟨r0, r1, c0, c1⟩` from `hrow B`. Use `Subtype.ext (funext fun i => funext fun j => ?_)` and prove the remaining obligations. Apply the tactic sequence `cases i <;> cases j <;> simp [B0] <;> omega`. Establish `ht₀ : b (b.symm B0) = B0` using `b.apply_symm_apply B0`. Use `⟨N, T, fun x y h => hmono h, ?_, ?_, b.symm B0, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `Subrepresentation.toSubmodule_injective (congrArg Subrepresentation.toSubmodule hbot :)`. Conclude with `Subrepresentation.toSubmodule_injective (congrArg Subrepresentation.toSubmodule htop :)`. Establish `hB' : (b (b.symm B0)).1 true false = 1` using `by rw [ht₀]`. Establish `hA` using `GlobalTheory.T.cell_functor_transposed_two_block χ₁ χ₂ h₁ h₂ u v (b (b.symm B0)) hB'`. Use `Exists.elim hA fun f hf => Exists.elim hf fun g hψ => ?_` and prove the remaining obligations.

Use `hψ.elim fun ψ => (hcell (b.symm B0) f g).elim fun φ => ?_` and prove the remaining obligations. Use `⟨Representation.Equiv.trans ?_ ψ⟩` and prove the remaining obligations. Conclude with `Representation.Equiv.mk φ.toLinearEquiv fun x => φ.isIntertwining' (leviTwo k (Fin 1) (Fin (u + v)) x)`. Introduce `t ht w hw`. Establish `hB : (b t).1 false false = 1`.

Establish `hne : (b t).1 true false ≠ 1` using `fun h => ht ((b.eq_symm_apply).2 (hB0 _ h))`. Take `⟨r0, r1, c0, c1⟩` from `hrow (b t)`. Use linear arithmetic over natural numbers and integers. Use `(b t).nonempty_rows.elim fun f => (b t).nonempty_cols.elim fun g => (hcell t f g).elim fun φ => ?_` and prove the remaining obligations. Establish `key` using `GlobalTheory.SmGL.cellFunctor_scalar_first χ₁ χ₂ u v (b t) hB f g ϖ (φ (Submodule.Quotient.mk ⟨w, hw⟩))`.

Establish `h1 : subQuot (S t.succ) (S t.castSucc) (leviTwo k (Fin 1) (Fin (u + v)) (GeneralLinearGroup.scalar (Fin 1) ϖ, 1)) (Submodule.Quotient.mk ⟨w, hw⟩) = Submodule.Quotient.mk ((((χ₁ * absPow k ((1 - (u : ℂ)) / 2)) ϖ : ℂˣ) : ℂ) • ⟨w, hw⟩)`. Apply `EquivLike.injective φ` to reduce the goal to its premises. Conclude with `(LinearMap.congr_fun (φ.isIntertwining' _) _).trans (key.trans (map_smul φ _ _).symm)`. Conclude with `(Submodule.Quotient.eq ((S t.castSucc).toSubmodule.comap (S t.succ).toSubmodule.subtype)).1 h1`.
-/
theorem jac₂_prod₂_detRep_filtration : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.GeometricLemmaFiltration → ∀ (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → ∀ (u v : ℕ) (e : Fin 1 ⊕ Fin (u + v) ≃ Fin (u + (v + 1))) (ϖ : kˣ), ∃ (N : ℕ) (S : Fin (N + 1) → Subrepresentation (jac₂ e (prod₂ (detRep (Fin u) χ₁) (detRep (Fin (v + 1)) χ₂)))), Monotone S ∧ S 0 = ⊥ ∧ S (Fin.last N) = ⊤ ∧ ∃ t₀ : Fin N, Nonempty ((subQuot (S t₀.succ) (S t₀.castSucc)).Equiv (extTensor (detRep (Fin 1) (χ₂ * absPow k (-(v : ℂ) / 2))) (prod₂ (detRep (Fin u) χ₁) (detRep (Fin v) (χ₂ * absPow k (1 / 2)))))) ∧ ∀ t, t ≠ t₀ → ∀ w ∈ (S t.succ).toSubmodule, jac₂ e (prod₂ (detRep (Fin u) χ₁) (detRep (Fin (v + 1)) χ₂)) (GeneralLinearGroup.scalar (Fin 1) ϖ, 1) w - (((χ₁ * absPow k ((1 - (u : ℂ)) / 2)) ϖ : ℂˣ) : ℂ) • w ∈ (S t.castSucc).toSubmodule := by
  intro k _ _ _ _ hG χ₁ χ₂ h₁ h₂ u v e ϖ
  have hρ : IsSmooth ((extTensor (detRep (Fin u) χ₁) (detRep (Fin (v + 1)) χ₂)).comp
      (leviTwo k (Fin u) (Fin (v + 1))).symm.toMonoidHom) := by
    refine isSmooth_comp (isSmooth_extTensor ((isSmooth_ofChar_iff _).2 h₁.detChar)
      ((isSmooth_ofChar_iff _).2 h₂.detChar)) _ ?_
    show Continuous fun g : Levi k (Two (Fin u) (Fin (v + 1))) => (g false, g true)
    exact (continuous_apply false).prodMk (continuous_apply true)
  have H := hG k Bool Bool (Fin (u + (v + 1))) (Two (Fin u) (Fin (v + 1)))
    (Two (Fin 1) (Fin (u + v))) (two (stdSum (rfl : u + (v + 1) = u + (v + 1)))) (two e)
  obtain ⟨N, b, hb⟩ := H
  have H2 := hb (TensorProduct ℂ ℂ ℂ) ((extTensor (detRep (Fin u) χ₁) (detRep (Fin (v + 1)) χ₂)).comp
    (leviTwo k (Fin u) (Fin (v + 1))).symm.toMonoidHom) hρ
  obtain ⟨S, hmono, hbot, htop, hcell⟩ := H2
  let T : Fin (N + 1) → Subrepresentation (jac₂ e (prod₂ (detRep (Fin u) χ₁) (detRep (Fin (v + 1)) χ₂))) :=
    fun t => ⟨(S t).toSubmodule, fun g _ hv => (S t).apply_mem_toSubmodule _ hv⟩
  have hrow : ∀ B : SizeMatrix (Two (Fin u) (Fin (v + 1))) (Two (Fin 1) (Fin (u + v))),
      B.1 false false + B.1 false true = u ∧ B.1 true false + B.1 true true = v + 1 ∧
      B.1 false false + B.1 true false = 1 ∧ B.1 false true + B.1 true true = u + v := by
    intro B
    have r0 := B.2.1 false
    have r1 := B.2.1 true
    have c0 := B.2.2 false
    have c1 := B.2.2 true
    simp only [Fintype.sum_bool] at r0 r1 c0 c1
    simp at r0 r1 c0 c1
    omega
  let B0 : SizeMatrix (Two (Fin u) (Fin (v + 1))) (Two (Fin 1) (Fin (u + v))) :=
    ⟨fun i j => Bool.rec (Bool.rec 0 u j) (Bool.rec 1 v j) i, by
      refine ⟨fun i => ?_, fun j => ?_⟩
      · cases i <;> simp
      · cases j <;> simp <;> omega⟩
  have hB0 : ∀ B : SizeMatrix (Two (Fin u) (Fin (v + 1))) (Two (Fin 1) (Fin (u + v))),
      B.1 true false = 1 → B = B0 := by
    intro B hB
    obtain ⟨r0, r1, c0, c1⟩ := hrow B
    refine Subtype.ext (funext fun i => funext fun j => ?_)
    cases i <;> cases j <;> simp [B0] <;> omega
  have ht₀ : b (b.symm B0) = B0 := b.apply_symm_apply B0
  refine ⟨N, T, fun x y h => hmono h, ?_, ?_, b.symm B0, ?_, ?_⟩
  · exact Subrepresentation.toSubmodule_injective (congrArg Subrepresentation.toSubmodule hbot :)
  · exact Subrepresentation.toSubmodule_injective (congrArg Subrepresentation.toSubmodule htop :)
  · have hB' : (b (b.symm B0)).1 true false = 1 := by rw [ht₀]
    have hA := GlobalTheory.T.cell_functor_transposed_two_block χ₁ χ₂ h₁ h₂ u v (b (b.symm B0)) hB'
    refine Exists.elim hA fun f hf => Exists.elim hf fun g hψ => ?_
    refine hψ.elim fun ψ => (hcell (b.symm B0) f g).elim fun φ => ?_
    refine ⟨Representation.Equiv.trans ?_ ψ⟩
    exact Representation.Equiv.mk φ.toLinearEquiv fun x =>
      φ.isIntertwining' (leviTwo k (Fin 1) (Fin (u + v)) x)
  · intro t ht w hw
    have hB : (b t).1 false false = 1 := by
      have hne : (b t).1 true false ≠ 1 := fun h => ht ((b.eq_symm_apply).2 (hB0 _ h))
      obtain ⟨r0, r1, c0, c1⟩ := hrow (b t)
      omega
    refine (b t).nonempty_rows.elim fun f => (b t).nonempty_cols.elim fun g =>
      (hcell t f g).elim fun φ => ?_
    have key := GlobalTheory.SmGL.cellFunctor_scalar_first χ₁ χ₂ u v (b t) hB f g ϖ (φ (Submodule.Quotient.mk ⟨w, hw⟩))
    have h1 : subQuot (S t.succ) (S t.castSucc)
        (leviTwo k (Fin 1) (Fin (u + v)) (GeneralLinearGroup.scalar (Fin 1) ϖ, 1))
          (Submodule.Quotient.mk ⟨w, hw⟩) =
        Submodule.Quotient.mk ((((χ₁ * absPow k ((1 - (u : ℂ)) / 2)) ϖ : ℂˣ) : ℂ) • ⟨w, hw⟩) := by
      apply EquivLike.injective φ
      exact (LinearMap.congr_fun (φ.isIntertwining' _) _).trans (key.trans (map_smul φ _ _).symm)
    exact (Submodule.Quotient.eq ((S t.castSucc).toSubmodule.comap (S t.succ).toSubmodule.subtype)).1 h1

end GlobalTheory
