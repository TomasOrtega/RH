import Mathlib

namespace GlobalTheory

/- English proof (translation)
Use `set E : Module.End L V := ∑ x : G, ρ x * e * ρ x⁻¹ with hE`. Establish `hcomm : ∀ g : G, ρ g * E = E * ρ g`. Introduce `g`. Rewrite using `[hE, Finset.mul_sum, Finset.sum_mul]`. Use `Fintype.sum_equiv (Equiv.mulLeft g) _ _ ?_` and prove the remaining obligations.

Introduce `x`. Establish `h1 : ρ (g * x)⁻¹ * ρ g = ρ x⁻¹`. Rewrite using `[← map_mul]`. Use `congr 1`. Use `group`.

Simplify using `only [Equiv.coe_mulLeft]`. Rewrite using `[mul_assoc (ρ (g * x) * e), h1, map_mul]`. Simplify using `only [mul_assoc]`. Establish `hEe : E * e = (Nat.card T : L) • e`. Rewrite using `[hE, Finset.sum_mul]`.

Establish `h2 : ∀ x : G, ρ x * e * ρ x⁻¹ * e = if x ∈ T then e else 0`. Introduce `x`. Use `split_ifs with hx`. Establish `h3 : ρ x * ρ x⁻¹ = 1` using `by rw [← map_mul, mul_inv_cancel, map_one]`. Rewrite using `[hT x hx, mul_assoc e, h3, mul_one, hee]`.

Establish `h4` using `hoff x⁻¹ (fun h => hx (by simpa using T.inv_mem h))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_congr rfl (fun x _ => h2 x), ← Finset.sum_filter, Finset.sum_const, Nat.cast_smul_eq_nsmul, Nat.card_eq_fintype_card, Fintype.card_subtype]`. Use `set D : Module.End L V := E - (Nat.card T : L) • (1 : Module.End L V) with hD`. Establish `hDc : ∀ g : G, ρ g * D = D * ρ g`.

Introduce `g`. Rewrite using `[hD, mul_sub, sub_mul, hcomm, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]`. Establish `hDe : D * e = 0`. Rewrite using `[hD, sub_mul, hEe, smul_mul_assoc, one_mul, sub_self]`. Set `K : Subrepresentation ρ` to `{ toSubmodule := LinearMap.ker D apply_mem_toSubmodule := by`.

Introduce `g v hv`. Rewrite `hv`, the goal using `[LinearMap.mem_ker]`. Use `congrArg (fun f : Module.End L V => f v) (hDc g)` as an intermediate fact. Simplify using `only [Module.End.mul_apply] at this`. Rewrite using `[← this, hv, map_zero] }`.

Use `hirr` as an intermediate fact. Break down `IsSimpleOrder.eq_bot_or_eq_top K with h | h` into its components or cases. It suffices to derive a contradiction. Apply `he0` to reduce the goal to its premises. Use extensionality with `v`.

Establish `hv : e v ∈ K.toSubmodule`. Express the relevant statement in the definitionally equal form `e v ∈ LinearMap.ker D`. Rewrite using `[LinearMap.mem_ker, ← Module.End.mul_apply, hDe]`. Both sides reduce to the same expression. Rewrite `hv` using `[h]`.

Conclude with `hv`. Establish `hk : LinearMap.ker D = ⊤`. Express the relevant statement in the definitionally equal form `K.toSubmodule = ⊤`. Rewrite using `[h]`. Both sides reduce to the same expression.

Conclude with `sub_eq_zero.mp (LinearMap.ker_eq_top.mp hk)`.
-/
theorem sum_conj_idempotent_eq_card_smul (L : Type) [Field L] (G : Type) [Group G] [Fintype G]
    (V : Type) [AddCommGroup V] [Module L V] (ρ : Representation L G V) (T : Subgroup G)
    (e : Module.End L V) (hirr : ρ.IsIrreducible) (he0 : e ≠ 0) (hee : e * e = e)
    (hT : ∀ t ∈ T, ρ t * e = e * ρ t) (hoff : ∀ g ∉ T, e * ρ g * e = 0) :
    ∑ x : G, ρ x * e * ρ x⁻¹ = (Nat.card T : L) • (1 : Module.End L V) := by
  classical
  set E : Module.End L V := ∑ x : G, ρ x * e * ρ x⁻¹ with hE
  have hcomm : ∀ g : G, ρ g * E = E * ρ g := by
    intro g
    rw [hE, Finset.mul_sum, Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ ?_
    intro x
    have h1 : ρ (g * x)⁻¹ * ρ g = ρ x⁻¹ := by
      rw [← map_mul]; congr 1; group
    simp only [Equiv.coe_mulLeft]
    rw [mul_assoc (ρ (g * x) * e), h1, map_mul]
    simp only [mul_assoc]
  have hEe : E * e = (Nat.card T : L) • e := by
    rw [hE, Finset.sum_mul]
    have h2 : ∀ x : G, ρ x * e * ρ x⁻¹ * e = if x ∈ T then e else 0 := by
      intro x
      split_ifs with hx
      · have h3 : ρ x * ρ x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
        rw [hT x hx, mul_assoc e, h3, mul_one, hee]
      · have h4 := hoff x⁻¹ (fun h => hx (by simpa using T.inv_mem h))
        calc ρ x * e * ρ x⁻¹ * e = ρ x * (e * ρ x⁻¹ * e) := by simp only [mul_assoc]
          _ = 0 := by rw [h4, mul_zero]
    rw [Finset.sum_congr rfl (fun x _ => h2 x), ← Finset.sum_filter, Finset.sum_const,
      Nat.cast_smul_eq_nsmul, Nat.card_eq_fintype_card, Fintype.card_subtype]
  set D : Module.End L V := E - (Nat.card T : L) • (1 : Module.End L V) with hD
  have hDc : ∀ g : G, ρ g * D = D * ρ g := by
    intro g
    rw [hD, mul_sub, sub_mul, hcomm, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  have hDe : D * e = 0 := by
    rw [hD, sub_mul, hEe, smul_mul_assoc, one_mul, sub_self]
  let K : Subrepresentation ρ :=
    { toSubmodule := LinearMap.ker D
      apply_mem_toSubmodule := by
        intro g v hv
        rw [LinearMap.mem_ker] at hv ⊢
        have := congrArg (fun f : Module.End L V => f v) (hDc g)
        simp only [Module.End.mul_apply] at this
        rw [← this, hv, map_zero] }
  have := hirr
  rcases IsSimpleOrder.eq_bot_or_eq_top K with h | h
  · exfalso
    apply he0
    ext v
    have hv : e v ∈ K.toSubmodule := by
      change e v ∈ LinearMap.ker D
      rw [LinearMap.mem_ker, ← Module.End.mul_apply, hDe]; rfl
    rw [h] at hv
    exact hv
  · have hk : LinearMap.ker D = ⊤ := by
      change K.toSubmodule = ⊤
      rw [h]; rfl
    exact sub_eq_zero.mp (LinearMap.ker_eq_top.mp hk)

end GlobalTheory
