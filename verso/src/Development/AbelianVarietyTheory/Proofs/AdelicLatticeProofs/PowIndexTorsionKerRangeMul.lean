import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

/- English proof (translation)
Unfold `pTor`. Conclude with `Nat.card_congr (Equiv.subtypeEquivRight fun x => by`. Simplify using `only [Subgroup.mem_inf, MonoidHom.mem_ker, powMonoidHom_apply])`.
-/
theorem pTor_eq_card_inf_ker (p : ℕ) {G : Type} [CommGroup G] (U : Subgroup G) :
    pTor p U = Nat.card (U ⊓ (powMonoidHom p : G →* G).ker : Subgroup G) := by
  unfold pTor
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by
    simp only [Subgroup.mem_inf, MonoidHom.mem_ker, powMonoidHom_apply])

/- English proof (translation)
Introduce `p A A' _ _ g hIK hTK hIR hTR`. Establish `hcomm : (powMonoidHom p : A' →* A').comp g = g.comp (powMonoidHom p : A →* A)`. Use extensionality with `a`. Simplify using `[map_pow]`. Establish `hRp : pows p g.range = (powMonoidHom p : A →* A).range.map g`.

Simplify using `only [pows, MonoidHom.range_eq_map, Subgroup.map_map, hcomm]`. Establish `hKpow : g.ker.map (powMonoidHom p : A →* A) ≤ g.ker`. Introduce and unpack `_ ⟨k, hk, rfl⟩`. Conclude with `g.ker.pow_mem hk p`. Establish `eA : pIdx p (⊤ : Subgroup A) = (powMonoidHom p : A →* A).range.relIndex g.ker * pIdx p g.range`.

Establish `h1 : pIdx p (⊤ : Subgroup A) = (powMonoidHom p : A →* A).range.index`. Rewrite using `[pIdx, Subgroup.relIndex_top_right, pows, ← MonoidHom.range_eq_map]`. Rewrite using `[h1, ← Subgroup.relIndex_mul_index (le_sup_left : (powMonoidHom p : A →* A).range ≤ (powMonoidHom p : A →* A).range ⊔ g.ker), Subgroup.relIndex_sup_left, ← Subgroup.comap_map_eq, Subgroup.index_comap, pIdx, hRp]`. Establish `eK : pIdx p g.ker = (g.ker.map (powMonoidHom p : A →* A)).relIndex ((powMonoidHom p : A →* A).range ⊓ g.ker) * (powMonoidHom p : A →* A).range.relIndex g.ker`. Establish `h0 : pIdx p g.ker = (g.ker.map (powMonoidHom p : A →* A)).relIndex g.ker` using `rfl`.

Rewrite using `[h0, ← Subgroup.relIndex_mul_relIndex _ ((powMonoidHom p : A →* A).range ⊓ g.ker) _ (le_inf (Subgroup.map_le_range _ _) hKpow) inf_le_right, Subgroup.inf_relIndex_right]`. Establish `hB : g.ker.comap (powMonoidHom p : A →* A) = (powMonoidHom p : A' →* A').ker.comap g`. Use extensionality with `a`. Simplify using `[MonoidHom.mem_ker, map_pow]`. Establish `hKB : g.ker ≤ g.ker.comap (powMonoidHom p : A →* A)` using `fun x hx => g.ker.pow_mem hx p`.

Establish `hQB : (powMonoidHom p : A →* A).ker ≤ g.ker.comap (powMonoidHom p : A →* A)`. Introduce `x hx`. Rewrite `hx` using `[MonoidHom.mem_ker]`. Simplify using `[Subgroup.mem_comap, hx]`. Establish `eR : pTor p g.range = g.ker.relIndex (powMonoidHom p : A →* A).ker * (g.ker.map (powMonoidHom p : A →* A)).relIndex ((powMonoidHom p : A →* A).range ⊓ g.ker)`.

Establish `h1 : pTor p g.range = g.ker.relIndex (g.ker.comap (powMonoidHom p : A →* A))`. Rewrite using `[pTor_eq_card_inf_ker, Subgroup.relIndex_ker, hB, Subgroup.map_comap_eq]`. Establish `h2 : (g.ker ⊔ (powMonoidHom p : A →* A).ker).relIndex (g.ker.comap (powMonoidHom p : A →* A)) = (g.ker.map (powMonoidHom p : A →* A)).relIndex ((powMonoidHom p : A →* A).range ⊓ g.ker)`. Rewrite using `[← Subgroup.comap_map_eq, Subgroup.relIndex_comap, Subgroup.map_comap_eq]`. Rewrite using `[h1, ← Subgroup.relIndex_mul_relIndex g.ker (g.ker ⊔ (powMonoidHom p : A →* A).ker) _ le_sup_left (sup_le hKB hQB), h2, Subgroup.relIndex_sup_left]`.

Establish `eT : pTor p (⊤ : Subgroup A) = pTor p g.ker * g.ker.relIndex (powMonoidHom p : A →* A).ker`. Establish `h` using `Subgroup.relIndex_mul_relIndex ⊥ (g.ker ⊓ (powMonoidHom p : A →* A).ker) (powMonoidHom p : A →* A).ker bot_le inf_le_right`. Rewrite `h` using `[Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, Subgroup.inf_relIndex_right]`. Rewrite using `[pTor_eq_card_inf_ker, pTor_eq_card_inf_ker, top_inf_eq, ← h]`. Rewrite `hIK`, the goal using `[eK]`.

Rewrite `hTR`, the goal using `[eR]`. Rewrite using `[eA, eT]`. Use `⟨mul_ne_zero (right_ne_zero_of_mul hIK) hIR, mul_ne_zero hTK (left_ne_zero_of_mul hTR), ?_⟩` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pIdx_pTor_ker_range :
    ∀ (p : ℕ) (A A' : Type) [CommGroup A] [CommGroup A'] (g : A →* A'), pIdx p g.ker ≠ 0 → pTor p g.ker ≠ 0 → pIdx p g.range ≠ 0 → pTor p g.range ≠ 0 → pIdx p (⊤ : Subgroup A) ≠ 0 ∧ pTor p (⊤ : Subgroup A) ≠ 0 ∧ pIdx p (⊤ : Subgroup A) * pTor p g.ker * pTor p g.range = pIdx p g.ker * pIdx p g.range * pTor p (⊤ : Subgroup A) := by
  intro p A A' _ _ g hIK hTK hIR hTR
  have hcomm : (powMonoidHom p : A' →* A').comp g = g.comp (powMonoidHom p : A →* A) := by
    ext a; simp [map_pow]
  have hRp : pows p g.range = (powMonoidHom p : A →* A).range.map g := by
    simp only [pows, MonoidHom.range_eq_map, Subgroup.map_map, hcomm]
  have hKpow : g.ker.map (powMonoidHom p : A →* A) ≤ g.ker := by
    rintro _ ⟨k, hk, rfl⟩
    exact g.ker.pow_mem hk p

  have eA : pIdx p (⊤ : Subgroup A) =
      (powMonoidHom p : A →* A).range.relIndex g.ker * pIdx p g.range := by
    have h1 : pIdx p (⊤ : Subgroup A) = (powMonoidHom p : A →* A).range.index := by
      rw [pIdx, Subgroup.relIndex_top_right, pows, ← MonoidHom.range_eq_map]
    rw [h1, ← Subgroup.relIndex_mul_index
      (le_sup_left : (powMonoidHom p : A →* A).range ≤ (powMonoidHom p : A →* A).range ⊔ g.ker),
      Subgroup.relIndex_sup_left, ← Subgroup.comap_map_eq, Subgroup.index_comap, pIdx, hRp]

  have eK : pIdx p g.ker = (g.ker.map (powMonoidHom p : A →* A)).relIndex
      ((powMonoidHom p : A →* A).range ⊓ g.ker) * (powMonoidHom p : A →* A).range.relIndex g.ker := by
    have h0 : pIdx p g.ker = (g.ker.map (powMonoidHom p : A →* A)).relIndex g.ker := rfl
    rw [h0, ← Subgroup.relIndex_mul_relIndex _ ((powMonoidHom p : A →* A).range ⊓ g.ker) _
      (le_inf (Subgroup.map_le_range _ _) hKpow) inf_le_right, Subgroup.inf_relIndex_right]

  have hB : g.ker.comap (powMonoidHom p : A →* A) = (powMonoidHom p : A' →* A').ker.comap g := by
    ext a; simp [MonoidHom.mem_ker, map_pow]
  have hKB : g.ker ≤ g.ker.comap (powMonoidHom p : A →* A) := fun x hx => g.ker.pow_mem hx p
  have hQB : (powMonoidHom p : A →* A).ker ≤ g.ker.comap (powMonoidHom p : A →* A) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    simp [Subgroup.mem_comap, hx]

  have eR : pTor p g.range = g.ker.relIndex (powMonoidHom p : A →* A).ker *
      (g.ker.map (powMonoidHom p : A →* A)).relIndex ((powMonoidHom p : A →* A).range ⊓ g.ker) := by
    have h1 : pTor p g.range = g.ker.relIndex (g.ker.comap (powMonoidHom p : A →* A)) := by
      rw [pTor_eq_card_inf_ker, Subgroup.relIndex_ker, hB, Subgroup.map_comap_eq]
    have h2 : (g.ker ⊔ (powMonoidHom p : A →* A).ker).relIndex
        (g.ker.comap (powMonoidHom p : A →* A)) =
        (g.ker.map (powMonoidHom p : A →* A)).relIndex ((powMonoidHom p : A →* A).range ⊓ g.ker) := by
      rw [← Subgroup.comap_map_eq, Subgroup.relIndex_comap, Subgroup.map_comap_eq]
    rw [h1, ← Subgroup.relIndex_mul_relIndex g.ker (g.ker ⊔ (powMonoidHom p : A →* A).ker) _
      le_sup_left (sup_le hKB hQB), h2,
      Subgroup.relIndex_sup_left]

  have eT : pTor p (⊤ : Subgroup A) = pTor p g.ker * g.ker.relIndex (powMonoidHom p : A →* A).ker := by
    have h := Subgroup.relIndex_mul_relIndex ⊥ (g.ker ⊓ (powMonoidHom p : A →* A).ker)
      (powMonoidHom p : A →* A).ker bot_le inf_le_right
    rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, Subgroup.inf_relIndex_right] at h
    rw [pTor_eq_card_inf_ker, pTor_eq_card_inf_ker, top_inf_eq, ← h]
  rw [eK] at hIK ⊢
  rw [eR] at hTR ⊢
  rw [eA, eT]
  refine ⟨mul_ne_zero (right_ne_zero_of_mul hIK) hIR, mul_ne_zero hTK (left_ne_zero_of_mul hTR), ?_⟩
  ring

end GlobalTheory.CNorm
