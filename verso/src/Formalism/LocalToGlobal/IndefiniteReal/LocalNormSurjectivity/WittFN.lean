import Formalism.LocalToGlobal.IndefiniteReal.LocalNormSurjectivity.FinNormSurj

noncomputable section

namespace Formalism.IndefR.LocBrg

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Take a linear combination of the given relations to obtain the conclusion.

Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem finNormSurj : FinNormSurj := by
  intro k _ _ τ hτ hnt c hc hc0
  classical
  have hτu : ∀ x : kˣ, Units.map τ.toMonoidHom (Units.map τ.toMonoidHom x) = x := by
    intro x; ext; simp [hτ]
  let T : kˣ →* kˣ := Units.map τ.toMonoidHom
  let N : kˣ →* kˣ :=
    { toFun := fun x => T x * x
      map_one' := by simp
      map_mul' := by intro x y; simp only [map_mul]; exact mul_mul_mul_comm _ _ _ _ }
  let ψ : kˣ →* kˣ :=
    { toFun := fun x => x * (T x)⁻¹
      map_one' := by simp
      map_mul' := by intro x y; simp only [map_mul, mul_inv]; exact mul_mul_mul_comm _ _ _ _ }
  have hTT : ∀ x, T (T x) = x := hτu
  have hT : ∀ x : kˣ, ((T x : kˣ) : k) = τ (x : k) := fun x => rfl
  have hψv : ∀ y : kˣ, ((ψ y : kˣ) : k) = (y : k) * (τ (y : k))⁻¹ := fun y => by
    show ((y * (T y)⁻¹ : kˣ) : k) = _
    rw [Units.val_mul, Units.val_inv_eq_inv_val, hT]
  have hkerψ : ∀ x, x ∈ ψ.ker ↔ T x = x := by
    intro x
    rw [MonoidHom.mem_ker]
    show x * (T x)⁻¹ = 1 ↔ T x = x
    rw [mul_inv_eq_one, eq_comm]
  have hrangeψ : ψ.range = N.ker := by
    ext x
    rw [MonoidHom.mem_range, MonoidHom.mem_ker]
    constructor
    · rintro ⟨y, rfl⟩
      show T (y * (T y)⁻¹) * (y * (T y)⁻¹) = 1
      rw [map_mul, map_inv, hTT]
      group
    · intro hx
      have hx' : T x * x = 1 := hx
      have hTx : (τ (x : k)) * (x : k) = 1 := by
        have := congrArg (fun u : kˣ => (u : k)) hx'
        simp only [Units.val_mul, Units.val_one, hT] at this
        exact this
      by_cases hm : (x : k) = -1
      · obtain ⟨θ, hθ⟩ := hnt
        have hy0 : θ - τ θ ≠ 0 := fun h => hθ (sub_eq_zero.1 h).symm
        refine ⟨Units.mk0 _ hy0, ?_⟩
        ext
        rw [hψv, Units.val_mk0]
        rw [map_sub, hτ, hm]
        have : τ θ - θ = -(θ - τ θ) := by ring
        rw [this, inv_neg, mul_neg, mul_inv_cancel₀ hy0]
      · have hy0 : (1 : k) + x ≠ 0 := by
          intro h; apply hm; linear_combination h
        refine ⟨Units.mk0 _ hy0, ?_⟩
        ext
        rw [hψv, Units.val_mk0]
        have hx0 : (x : k) ≠ 0 := x.ne_zero
        have hτx : τ (x : k) = (x : k)⁻¹ := eq_inv_of_mul_eq_one_left hTx
        rw [map_add, map_one, hτx]
        have h1 : (1 : k) + (x : k)⁻¹ = (1 + (x : k)) * (x : k)⁻¹ := by field_simp; ring
        rw [h1, mul_inv, inv_inv, ← mul_assoc, mul_inv_cancel₀ hy0, one_mul]
  have hle : N.range ≤ ψ.ker := by
    rintro _ ⟨x, rfl⟩
    rw [hkerψ]
    show T (T x * x) = T x * x
    rw [map_mul, hTT, mul_comm]
  have hcardN := Subgroup.card_mul_index N.ker
  rw [Subgroup.index_ker] at hcardN
  have hcardψ := Subgroup.card_mul_index ψ.ker
  rw [Subgroup.index_ker, hrangeψ] at hcardψ
  have hpos : 0 < Nat.card N.ker := Nat.card_pos
  have heq : Nat.card N.range = Nat.card ψ.ker := by
    have h := hcardN.trans hcardψ.symm
    rw [mul_comm (Nat.card ψ.ker)] at h
    exact (Nat.eq_of_mul_eq_mul_left hpos h)
  have hEq : N.range = ψ.ker := Subgroup.eq_of_le_of_card_ge hle heq.ge
  have hcu : Units.mk0 c hc0 ∈ ψ.ker := by
    rw [hkerψ]; ext; rw [hT, Units.val_mk0]; exact hc
  rw [← hEq] at hcu
  obtain ⟨x, hx⟩ := hcu
  refine ⟨(x : k), ?_⟩
  have := congrArg (fun u : kˣ => (u : k)) hx
  simp only [Units.val_mk0] at this
  rw [show ((N x : kˣ) : k) = τ (x : k) * (x : k) from rfl] at this
  exact this

end Formalism.IndefR.LocBrg
