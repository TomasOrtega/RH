import Mathlib

open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Establish an intermediate fact. By extensionality, compare the relevant components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
-/
theorem det_mul_map_det_eq_one_of_sesq {E : Type*} [Field E] {V : Type*} [AddCommGroup V]
    [Module E V] [FiniteDimensional E V] (σ : E →+* E) (H : V →ₗ[E] V →ₛₗ[σ] E)
    (hH : ∀ x, (∀ y, H x y = 0) → x = 0) (g : V →ₗ[E] V)
    (hg : ∀ x y, H (g x) (g y) = H x y) :
    LinearMap.det g * σ (LinearMap.det g) = 1 := by
  classical
  let b := Module.finBasis E V
  let S : Matrix _ _ E := Matrix.of fun i j => H (b i) (b j)
  let G := LinearMap.toMatrix b b g
  have hgb : ∀ j, g (b j) = ∑ i, G i j • b i := by
    intro j
    simp only [G, LinearMap.toMatrix_apply]
    exact (b.sum_repr (g (b j))).symm
  have hS : G.transpose * S * σ.mapMatrix G = S := by
    ext i j
    have h1 : S i j = H (g (b i)) (g (b j)) := (hg _ _).symm
    rw [h1, hgb, hgb]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, RingHom.mapMatrix_apply,
      Matrix.map_apply, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
      LinearMap.map_smulₛₗ, smul_eq_mul, S, Matrix.of_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm]
  have hdet : S.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hvS⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
    apply hv
    have hx : ∑ i, v i • b i = 0 := by
      apply hH
      have : H (∑ i, v i • b i) = 0 := by
        apply b.ext
        intro j
        have := congrFun hvS j
        simpa [Matrix.vecMul, dotProduct, S, map_sum, LinearMap.sum_apply] using this
      intro y
      rw [this]; rfl
    funext i
    exact Fintype.linearIndependent_iff.mp b.linearIndependent v hx i
  have hd := congrArg Matrix.det hS
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det] at hd
  have hG : G.det = LinearMap.det g := LinearMap.det_toMatrix b g
  rw [hG] at hd
  apply mul_left_cancel₀ hdet
  linear_combination hd

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

By extensionality, compare the relevant components. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Introduce a local definition for the expression. Establish an intermediate fact.

Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem det_mul_complexConj_det_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (V : Type) [AddCommGroup V] [Module E V] [Module ℚ V] [IsScalarTower ℚ E V] [FiniteDimensional E V] (B : LinearMap.BilinForm ℚ V), (∀ x, (∀ y, B x y = 0) → x = 0) → (∀ (a : E) x y, B (a • x) y = B x (IsCMField.complexConj E a • y)) → ∀ g : V →ₗ[E] V, (∀ x y, B (g x) (g y) = B x y) → LinearMap.det g * IsCMField.complexConj E (LinearMap.det g) = 1 := by
  intro E _ _ _ V _ _ _ _ _ B hB hc g hg
  have hnd := traceForm_nondegenerate ℚ E
  have hext : ∀ u v : E, (∀ a, Algebra.trace ℚ E (u * a) = Algebra.trace ℚ E (v * a)) → u = v := by
    intro u v huv
    apply ((Algebra.traceForm ℚ E).toDual hnd).injective
    ext a
    simpa [LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply] using huv a
  have hex : ∀ x y : V, ∃ u : E, ∀ a, Algebra.trace ℚ E (u * a) = B (a • x) y := by
    intro x y
    obtain ⟨u, hu⟩ := ((Algebra.traceForm ℚ E).toDual hnd).surjective
      ((LinearMap.flip B y) ∘ₗ (LinearMap.toSpanSingleton E V x).restrictScalars ℚ)
    refine ⟨u, fun a => ?_⟩
    have := LinearMap.congr_fun hu a
    simpa [LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply] using this
  choose h hh using hex
  let σ : E →+* E := (IsCMField.complexConj E : E →+* E)
  have hσ : ∀ a, σ a = IsCMField.complexConj E a := fun _ => rfl
  let H : V →ₗ[E] V →ₛₗ[σ] E := LinearMap.mk₂'ₛₗ (RingHom.id E) σ h
    (fun x x' y => hext _ _ fun a => by
      rw [add_mul, map_add, hh, hh, hh, smul_add, map_add, LinearMap.add_apply])
    (fun c x y => hext _ _ fun a => by
      rw [RingHom.id_apply, smul_eq_mul, mul_comm c, mul_assoc, hh, hh, smul_smul, mul_comm])
    (fun x y y' => hext _ _ fun a => by
      rw [add_mul, map_add, hh, hh, hh, map_add])
    (fun c x y => hext _ _ fun a => by
      rw [smul_eq_mul, mul_comm (σ c), mul_assoc, hh, hh, mul_smul, hc (σ c), hσ,
        IsCMField.complexConj_apply_apply])
  have hH : ∀ x y, H x y = h x y := fun _ _ => rfl
  refine det_mul_map_det_eq_one_of_sesq σ H (fun x hx => hB x fun y => ?_) g (fun x y => ?_)
  · have := hh x y 1
    rw [← hH, hx, zero_mul, map_zero, one_smul] at this
    exact this.symm
  · rw [hH, hH]
    refine hext _ _ fun a => ?_
    rw [hh, hh, ← map_smul, hg]

end GlobalTheory.CompanionTheory.Ar.Flat
