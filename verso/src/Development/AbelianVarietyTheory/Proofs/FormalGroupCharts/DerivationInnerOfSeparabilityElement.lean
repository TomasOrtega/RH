import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.WickOperatorVanishing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GEWick

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Treat this case separately. Treat this case separately. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Treat this case separately. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Rewrite the conclusion using the stated equalities.
-/
theorem derivation_inner_of_separability_element (O : Type) [CommRing O] (N : ℕ)
    (e : TensorProduct ℤ O O) (hN : 0 < N) (he : Algebra.TensorProduct.lmul' ℤ e = (N : O))
    (hc : ∀ c : O, (TensorProduct.tmul ℤ c (1 : O) - TensorProduct.tmul ℤ (1 : O) c) * e = 0)
    (V : Type) [AddCommGroup V] [Module ℚ V] (l r : O →+* Module.End ℚ V)
    (hlr : ∀ a b, Commute (l a) (r b)) (δ : O →+ V)
    (hδ : ∀ a b, δ (a * b) = l b (δ a) + r a (δ b)) :
    ∃ v : V, ∀ a, δ a = l a v - r a v := by
  let Φ : TensorProduct ℤ O O →ₗ[ℤ] V := TensorProduct.lift
    (LinearMap.mk₂ ℤ (fun a b => l a (δ b))
      (fun a a' b => by simp) (fun n a b => by simp)
      (fun a b b' => by simp) (fun n a b => by rw [map_zsmul, map_zsmul]))
  have hΦ : ∀ a b, Φ (TensorProduct.tmul ℤ a b) = l a (δ b) := fun a b => TensorProduct.lift.tmul a b
  have h1 : ∀ (c : O) (t : TensorProduct ℤ O O),
      Φ (TensorProduct.tmul ℤ c (1 : O) * t) = l c (Φ t) := by
    intro c t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul, hΦ]
    | add x y hx hy => simp [mul_add, hx, hy]
  have h2 : ∀ (c : O) (t : TensorProduct ℤ O O),
      Φ (TensorProduct.tmul ℤ (1 : O) c * t)
        = l (Algebra.TensorProduct.lmul' ℤ t) (δ c) + r c (Φ t) := by
    intro c t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have h := LinearMap.congr_fun (hlr a c).eq (δ b)
      simp only [Module.End.mul_apply] at h
      simp [Algebra.TensorProduct.tmul_mul_tmul, hΦ, hδ, h]
    | add x y hx hy =>
      simp only [mul_add, map_add, hx, hy, LinearMap.add_apply]
      abel
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨(N : ℚ)⁻¹ • Φ e, fun c => ?_⟩
  have h := congrArg Φ (hc c)
  rw [sub_mul, map_sub, h1, h2, he, map_zero, map_natCast, Module.End.natCast_apply] at h
  have h' : l c (Φ e) - r c (Φ e) = (N : ℚ) • δ c := by
    rw [Nat.cast_smul_eq_nsmul]
    rw [sub_eq_zero] at h
    rw [h]; abel
  rw [map_smul, map_smul, ← smul_sub, h', smul_smul, inv_mul_cancel₀ hN', one_smul]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem derivation_inner_of_reduced_order :
    (∀ (O : Type) [CommRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O], ∃ (N : ℕ) (e : TensorProduct ℤ O O), 0 < N ∧ Algebra.TensorProduct.lmul' ℤ e = (N : O) ∧ ∀ c : O, (TensorProduct.tmul ℤ c (1 : O) - TensorProduct.tmul ℤ (1 : O) c) * e = 0) → ∀ (O : Type) [CommRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] (V : Type) [AddCommGroup V] [Module ℚ V] (l r : O →+* Module.End ℚ V), (∀ a b, Commute (l a) (r b)) → ∀ δ : O →+ V, (∀ a b, δ (a * b) = l b (δ a) + r a (δ b)) → ∃ v : V, ∀ a, δ a = l a v - r a v := by
  intro H O _ _ _ _ V _ _ l r hlr δ hδ
  obtain ⟨N, e, hN, he, hc⟩ := H O
  exact derivation_inner_of_separability_element O N e hN he hc V l r hlr δ hδ

end GlobalTheory
