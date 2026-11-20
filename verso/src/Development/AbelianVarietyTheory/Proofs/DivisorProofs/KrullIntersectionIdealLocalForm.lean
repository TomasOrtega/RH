import Mathlib

namespace GlobalTheory

/- English proof (translation)
Use `set N : Submodule B (B ⧸ a') := Submodule.map (Submodule.mkQ a') a with hN`. Take `⟨k, hk⟩` from `Ideal.exists_pow_inf_eq_pow_smul I N`. Establish `hle : N ≤ I ^ (k + 1) • (⊤ : Submodule B (B ⧸ a'))`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.1 (h k hx)`.

Establish `h1 : Submodule.mkQ a' (y + z) = z • Submodule.mkQ a' 1`. Establish `hy0 : Submodule.mkQ a' y = 0`. Rewrite using `[Submodule.mkQ_apply]`. Conclude with `(Submodule.Quotient.mk_eq_zero a').2 hy`. Rewrite using `[map_add, hy0, zero_add, ← map_smul, smul_eq_mul, mul_one]`.

Rewrite using `[h1]`. Conclude with `Submodule.smul_mem_smul hz Submodule.mem_top`. Establish `hNI : N ≤ I • N`. Establish `e1 : N = I ^ (k + 1) • (⊤ : Submodule B (B ⧸ a')) ⊓ N` using `(inf_eq_right.2 hle).symm`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Nat.add_sub_cancel_left, pow_one]`. Conclude with `Submodule.smul_mono le_rfl inf_le_right`. Establish `hfg : N.FG` using `IsNoetherian.noetherian N`. Take `⟨r, hr, hrN⟩` from `Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul I N hfg hNI`. Use `⟨r, hr, fun x hx => ?_⟩` and prove the remaining obligations.

Establish `hx'` using `hrN (Submodule.mkQ a' x) ⟨x, hx, rfl⟩`. Rewrite `hx'` using `[← map_smul, smul_eq_mul]`. Establish `: Submodule.mkQ a' ((1 - r) * x) = 0`. Rewrite using `[sub_mul, one_mul, map_sub, hx', sub_self]`. Rewrite `this` using `[Submodule.mkQ_apply]`.

Conclude with `(Submodule.Quotient.mk_eq_zero a').1 this`.
-/
theorem krull_inter_ideal_local (B : Type) [CommRing B] [IsNoetherianRing B] (I a a' : Ideal B)
    (h : ∀ e : ℕ, a ≤ a' ⊔ I ^ (e + 1)) : ∃ r ∈ I, ∀ x ∈ a, (1 - r) * x ∈ a' := by
  set N : Submodule B (B ⧸ a') := Submodule.map (Submodule.mkQ a') a with hN
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I N
  have hle : N ≤ I ^ (k + 1) • (⊤ : Submodule B (B ⧸ a')) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (h k hx)
    have h1 : Submodule.mkQ a' (y + z) = z • Submodule.mkQ a' 1 := by
      have hy0 : Submodule.mkQ a' y = 0 := by
        rw [Submodule.mkQ_apply]; exact (Submodule.Quotient.mk_eq_zero a').2 hy
      rw [map_add, hy0, zero_add, ← map_smul, smul_eq_mul, mul_one]
    rw [h1]
    exact Submodule.smul_mem_smul hz Submodule.mem_top
  have hNI : N ≤ I • N := by
    have e1 : N = I ^ (k + 1) • (⊤ : Submodule B (B ⧸ a')) ⊓ N := (inf_eq_right.2 hle).symm
    calc N = I ^ (k + 1) • (⊤ : Submodule B (B ⧸ a')) ⊓ N := e1
      _ = I ^ (k + 1 - k) • (I ^ k • ⊤ ⊓ N) := hk (k + 1) (Nat.le_succ k)
      _ ≤ I • N := by
        rw [Nat.add_sub_cancel_left, pow_one]
        exact Submodule.smul_mono le_rfl inf_le_right
  have hfg : N.FG := IsNoetherian.noetherian N
  obtain ⟨r, hr, hrN⟩ := Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul I N hfg hNI
  refine ⟨r, hr, fun x hx => ?_⟩
  have hx' := hrN (Submodule.mkQ a' x) ⟨x, hx, rfl⟩
  rw [← map_smul, smul_eq_mul] at hx'
  have : Submodule.mkQ a' ((1 - r) * x) = 0 := by
    rw [sub_mul, one_mul, map_sub, hx', sub_self]
  rw [Submodule.mkQ_apply] at this
  exact (Submodule.Quotient.mk_eq_zero a').1 this

end GlobalTheory
