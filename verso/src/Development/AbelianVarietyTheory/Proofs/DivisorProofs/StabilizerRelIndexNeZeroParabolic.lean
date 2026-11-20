import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `P M N _ _ _ s π u _ _ _ KP KM L _ _ _ TM hU q X`. Take `⟨U, hUK, hUi, hUk⟩` from `hU X`. Use `set S := TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM`. Use `set C := KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)`. Establish `hUC : U ≤ C`.

Introduce `k hk`. Simplify using `only [C, Subgroup.mem_comap, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]`. Conclude with `hUk k hk`. Establish `hSK : S ≤ KM` using `inf_le_right`. Establish `hUS : U.relIndex S ≠ 0` using `fun h => hUi (Subgroup.relIndex_eq_zero_of_le_right hSK h)`.

Establish `hCS : C.relIndex S ≠ 0` using `fun h => hUS (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.relIndex_dvd_of_le_left S hUC))`. Rewrite using `[Subgroup.inf_relIndex_left]`. Conclude with `hCS`.
-/
theorem stab_relIndex_ne_zero : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ TM : Subgroup M, (∀ X : N, ∃ U : Subgroup M, U ≤ KM ∧ U.relIndex KM ≠ 0 ∧ ∀ k ∈ U, (u X)⁻¹ * s k * u X ∈ KP) → ∀ (q : M) (X : N), (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM ⊓ KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)).relIndex (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM) ≠ 0 := by
  intro P M N _ _ _ s π u _ _ _ KP KM L _ _ _ TM hU q X
  obtain ⟨U, hUK, hUi, hUk⟩ := hU X
  set S := TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM
  set C := KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)
  have hUC : U ≤ C := by
    intro k hk
    simp only [C, Subgroup.mem_comap, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact hUk k hk
  have hSK : S ≤ KM := inf_le_right
  have hUS : U.relIndex S ≠ 0 := fun h =>
    hUi (Subgroup.relIndex_eq_zero_of_le_right hSK h)
  have hCS : C.relIndex S ≠ 0 := fun h =>
    hUS (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.relIndex_dvd_of_le_left S hUC))
  rw [Subgroup.inf_relIndex_left]
  exact hCS

end GlobalTheory
