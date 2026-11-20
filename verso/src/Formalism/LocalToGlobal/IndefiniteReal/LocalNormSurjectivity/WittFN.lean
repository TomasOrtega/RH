import Formalism.LocalToGlobal.IndefiniteReal.LocalNormSurjectivity.FinNormSurj

noncomputable section

namespace Formalism.IndefR.LocBrg

/- English proof (translation)
Introduce `k _ _ τ hτ hnt c hc hc0`. Establish `hτu : ∀ x : kˣ, Units.map τ.toMonoidHom (Units.map τ.toMonoidHom x) = x`. Introduce `x`. Use `ext`. Simplify using `[hτ]`.

Set `T : kˣ →* kˣ` to `Units.map τ.toMonoidHom`. Set `N : kˣ →* kˣ` to `{ toFun := fun x => T x * x map_one' := by simp map_mul' := by intro x y; simp only [map_mul]; exact mul_mul_mul_comm _ _ _ _ }`. Set `ψ : kˣ →* kˣ` to `{ toFun := fun x => x * (T x)⁻¹ map_one' := by simp map_mul' := by intro x y; simp only [map_mul, mul_inv]; exact mul_mul_mul_comm _ _ _ _ }`. Establish `hTT : ∀ x, T (T x) = x` using `hτu`. Establish `hT : ∀ x : kˣ, ((T x : kˣ) : k) = τ (x : k)` using `fun x => rfl`.

Establish `hψv : ∀ y : kˣ, ((ψ y : kˣ) : k) = (y : k) * (τ (y : k))⁻¹` using `fun y => by show ((y * (T y)⁻¹ : kˣ) : k) = _`. Rewrite using `[Units.val_mul, Units.val_inv_eq_inv_val, hT]`. Establish `hkerψ : ∀ x, x ∈ ψ.ker ↔ T x = x`. Introduce `x`. Rewrite using `[MonoidHom.mem_ker]`.

Use `show x * (T x)⁻¹ = 1 ↔ T x = x`. Rewrite using `[mul_inv_eq_one, eq_comm]`. Establish `hrangeψ : ψ.range = N.ker`. Use extensionality with `x`. Rewrite using `[MonoidHom.mem_range, MonoidHom.mem_ker]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩ show T (y * (T y)⁻¹) * (y * (T y)⁻¹) = 1`. Rewrite using `[map_mul, map_inv, hTT]`. Use `group`. Introduce `hx`.

Establish `hx' : T x * x = 1` using `hx`. Establish `hTx : (τ (x : k)) * (x : k) = 1`. Use `congrArg (fun u : kˣ => (u : k)) hx'` as an intermediate fact. Simplify using `only [Units.val_mul, Units.val_one, hT] at this`. Conclude with `this`.

Distinguish the cases in `hm : (x : k) = -1`. Take `⟨θ, hθ⟩` from `hnt`. Establish `hy0 : θ - τ θ ≠ 0` using `fun h => hθ (sub_eq_zero.1 h).symm`. Use `⟨Units.mk0 _ hy0, ?_⟩` and prove the remaining obligations. Use `ext`.

Rewrite using `[hψv, Units.val_mk0]`. Rewrite using `[map_sub, hτ, hm]`. Establish `: τ θ - θ = -(θ - τ θ)` using `by ring`. Rewrite using `[this, inv_neg, mul_neg, mul_inv_cancel₀ hy0]`. Establish `hy0 : (1 : k) + x ≠ 0`.

Introduce `h`. Apply `hm` to reduce the goal to its premises. Take the linear combination `h`. Use `⟨Units.mk0 _ hy0, ?_⟩` and prove the remaining obligations. Use `ext`.

Rewrite using `[hψv, Units.val_mk0]`. Establish `hx0 : (x : k) ≠ 0` using `x.ne_zero`. Establish `hτx : τ (x : k) = (x : k)⁻¹` using `eq_inv_of_mul_eq_one_left hTx`. Rewrite using `[map_add, map_one, hτx]`. Establish `h1 : (1 : k) + (x : k)⁻¹ = (1 + (x : k)) * (x : k)⁻¹` using `by field_simp; ring`.

Rewrite using `[h1, mul_inv, inv_inv, ← mul_assoc, mul_inv_cancel₀ hy0, one_mul]`. Establish `hle : N.range ≤ ψ.ker`. Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[hkerψ]`. Use `show T (T x * x) = T x * x`.

Rewrite using `[map_mul, hTT, mul_comm]`. Establish `hcardN` using `Subgroup.card_mul_index N.ker`. Rewrite `hcardN` using `[Subgroup.index_ker]`. Establish `hcardψ` using `Subgroup.card_mul_index ψ.ker`. Rewrite `hcardψ` using `[Subgroup.index_ker, hrangeψ]`.

Establish `hpos : 0 < Nat.card N.ker` using `Nat.card_pos`. Establish `heq : Nat.card N.range = Nat.card ψ.ker`. Establish `h` using `hcardN.trans hcardψ.symm`. Rewrite `h` using `[mul_comm (Nat.card ψ.ker)]`. Conclude with `(Nat.eq_of_mul_eq_mul_left hpos h)`.

Establish `hEq : N.range = ψ.ker` using `Subgroup.eq_of_le_of_card_ge hle heq.ge`. Establish `hcu : Units.mk0 c hc0 ∈ ψ.ker`. Rewrite using `[hkerψ]`. Use `ext`. Rewrite using `[hT, Units.val_mk0]`.

Conclude with `hc`. Rewrite `hcu` using `[← hEq]`. Take `⟨x, hx⟩` from `hcu`. Use `⟨(x : k), ?_⟩` and prove the remaining obligations. Use `congrArg (fun u : kˣ => (u : k)) hx` as an intermediate fact.

Simplify using `only [Units.val_mk0] at this`. Rewrite `this` using `[show ((N x : kˣ) : k) = τ (x : k) * (x : k) from rfl]`. Conclude with `this`.
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
