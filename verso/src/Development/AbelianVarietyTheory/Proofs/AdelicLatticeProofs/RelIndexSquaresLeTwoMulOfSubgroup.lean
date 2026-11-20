import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

/- English proof (translation)
Distinguish the cases in `hK : K ≤ H`. Rewrite using `[Subgroup.relIndex_eq_one.mpr hK]`. Evaluate the numerical expressions. Take `⟨a, haK, haH⟩` from `SetLike.not_le_iff_exists.mp hK`. Establish `ha` using `(h a haK).resolve_left haH`.

Apply `le_of_eq` to reduce the goal to its premises. Unfold `Subgroup.relIndex`. Rewrite using `[Subgroup.index_eq_two_iff]`. Use `⟨⟨a⁻¹, K.inv_mem haK⟩, fun b => ?_⟩` and prove the remaining obligations. Simplify using `only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]`.

Distinguish the cases in `hb : (b : G) ∈ H`. Use `right`. Use `⟨hb, fun hba => haH ?_⟩` and prove the remaining obligations. Use `H.mul_mem hb (H.inv_mem hba)` as an intermediate fact. Simplify using `using this`.

Use `left`. Use `⟨?_, hb⟩` and prove the remaining obligations. Use `H.mul_mem ((h b b.2).resolve_left hb) (H.inv_mem ha)` as an intermediate fact. Establish `e : (b : G) * ε⁻¹ * (a * ε⁻¹)⁻¹ = b * a⁻¹`. Rewrite using `[mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]`.

Rewrite `this` using `[e]`. Then use the resulting hypothesis.
-/
theorem relIndex_le_two_of_coset {G : Type} [CommGroup G] (H K : Subgroup G) (ε : G)
    (h : ∀ x ∈ K, x ∈ H ∨ x * ε⁻¹ ∈ H) : H.relIndex K ≤ 2 := by
  by_cases hK : K ≤ H
  · rw [Subgroup.relIndex_eq_one.mpr hK]; norm_num
  · obtain ⟨a, haK, haH⟩ := SetLike.not_le_iff_exists.mp hK
    have ha := (h a haK).resolve_left haH
    apply le_of_eq
    unfold Subgroup.relIndex
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨a⁻¹, K.inv_mem haK⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    by_cases hb : (b : G) ∈ H
    · right
      refine ⟨hb, fun hba => haH ?_⟩
      have := H.mul_mem hb (H.inv_mem hba)
      simpa using this
    · left
      refine ⟨?_, hb⟩
      have := H.mul_mem ((h b b.2).resolve_left hb) (H.inv_mem ha)
      have e : (b : G) * ε⁻¹ * (a * ε⁻¹)⁻¹ = b * a⁻¹ := by
        rw [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]
      rwa [e] at this

/- English proof (translation)
Introduce `G _ U H ε hHU hfin hε hsq`. Establish `hle : ∀ V : Subgroup G, sqs V ≤ V`. Introduce and unpack `V x ⟨y, hy, rfl⟩`. Conclude with `V.pow_mem hy 2`. Establish `hmono : sqs H ≤ sqs U` using `Subgroup.map_mono hHU`.

Establish `h1` using `Subgroup.relIndex_mul_relIndex (sqs H) H U (hle H) hHU`. Establish `h2` using `Subgroup.relIndex_mul_relIndex (sqs H) (sqs U) U hmono (hle U)`. Use `set H' : Subgroup G := (sqs H).comap (powMonoidHom 2) with hH'`. Establish `h3 : H'.relIndex U = (sqs H).relIndex (sqs U)`. Rewrite using `[hH', Subgroup.relIndex_comap]`.

Both sides reduce to the same expression. Establish `hHH' : H ≤ H' ⊓ U` using `le_inf (Subgroup.le_comap_map _ _) hHU`. Establish `h4` using `Subgroup.relIndex_mul_relIndex H (H' ⊓ U) U hHH' inf_le_right`. Rewrite `h4` using `[Subgroup.inf_relIndex_right, h3]`. Establish `h5 : H.relIndex (H' ⊓ U) ≤ 2`.

Apply `relIndex_le_two_of_coset H _ ε` to reduce the goal to its premises. Introduce and unpack `x ⟨⟨y, hy, hxy⟩, -⟩`. Simplify using `only [powMonoidHom_apply] at hxy`. Establish `: (x * y⁻¹) ^ 2 = 1` using `by rw [mul_pow, ← hxy, inv_pow, mul_inv_cancel]`. Break down `hε _ this with h | h` into its components or cases.

Use `left`. Rewrite `h` using `[mul_inv_eq_one]`. Rewrite using `[h]`. Conclude with `hy`. Use `right`.

Establish `e : x * ε⁻¹ = y`. Rewrite using `[← h, mul_inv_rev, inv_inv, mul_comm y, mul_inv_cancel_left]`. Rewrite using `[e]`. Conclude with `hy`. Establish `hne : (sqs H).relIndex (sqs U) * (sqs U).relIndex U ≠ 0`.

Rewrite using `[h2, ← h1]`. Conclude with `mul_ne_zero hsq hfin`. Take `⟨hb, ha⟩` from `mul_ne_zero_iff.mp hne`. Use `⟨ha, ?_⟩` and prove the remaining obligations. Apply `Nat.le_of_mul_le_mul_left _ (Nat.pos_of_ne_zero hb)` to reduce the goal to its premises.

Rewrite using `[h2, ← h1, ← h4]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem relIndex_sqs_le_two_mul :
    ∀ (G : Type) [CommGroup G] (U H : Subgroup G) (ε : G), H ≤ U → H.relIndex U ≠ 0 →
      (∀ a : G, a ^ 2 = 1 → a = 1 ∨ a = ε) → (sqs H).relIndex H ≠ 0 →
      (sqs U).relIndex U ≠ 0 ∧ (sqs U).relIndex U ≤ 2 * (sqs H).relIndex H := by
  intro G _ U H ε hHU hfin hε hsq
  have hle : ∀ V : Subgroup G, sqs V ≤ V := by
    rintro V x ⟨y, hy, rfl⟩
    exact V.pow_mem hy 2
  have hmono : sqs H ≤ sqs U := Subgroup.map_mono hHU
  have h1 := Subgroup.relIndex_mul_relIndex (sqs H) H U (hle H) hHU
  have h2 := Subgroup.relIndex_mul_relIndex (sqs H) (sqs U) U hmono (hle U)
  set H' : Subgroup G := (sqs H).comap (powMonoidHom 2) with hH'
  have h3 : H'.relIndex U = (sqs H).relIndex (sqs U) := by
    rw [hH', Subgroup.relIndex_comap]; rfl
  have hHH' : H ≤ H' ⊓ U := le_inf (Subgroup.le_comap_map _ _) hHU
  have h4 := Subgroup.relIndex_mul_relIndex H (H' ⊓ U) U hHH' inf_le_right
  rw [Subgroup.inf_relIndex_right, h3] at h4
  have h5 : H.relIndex (H' ⊓ U) ≤ 2 := by
    apply relIndex_le_two_of_coset H _ ε
    rintro x ⟨⟨y, hy, hxy⟩, -⟩
    simp only [powMonoidHom_apply] at hxy
    have : (x * y⁻¹) ^ 2 = 1 := by rw [mul_pow, ← hxy, inv_pow, mul_inv_cancel]
    rcases hε _ this with h | h
    · left
      rw [mul_inv_eq_one] at h
      rw [h]; exact hy
    · right
      have e : x * ε⁻¹ = y := by
        rw [← h, mul_inv_rev, inv_inv, mul_comm y, mul_inv_cancel_left]
      rw [e]; exact hy
  have hne : (sqs H).relIndex (sqs U) * (sqs U).relIndex U ≠ 0 := by
    rw [h2, ← h1]; exact mul_ne_zero hsq hfin
  obtain ⟨hb, ha⟩ := mul_ne_zero_iff.mp hne
  refine ⟨ha, ?_⟩
  apply Nat.le_of_mul_le_mul_left _ (Nat.pos_of_ne_zero hb)
  rw [h2, ← h1, ← h4]
  calc (sqs H).relIndex H * (H.relIndex (H' ⊓ U) * (sqs H).relIndex (sqs U))
      ≤ (sqs H).relIndex H * (2 * (sqs H).relIndex (sqs U)) := by gcongr
    _ = _ := by ring

end GlobalTheory.QNorm
