import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open TensorProduct

namespace GlobalTheory.BSP

open TensorProduct in
/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `tmul t x`. Take `⟨r, rfl⟩` from `Ideal.Quotient.mk_surjective t`. Use `⟨r • x, ?_⟩` and prove the remaining obligations.

Rewrite using `[← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]`. Both sides reduce to the same expression. Consider the case `add z z' hz hz'`. Take `⟨x, rfl⟩` from `hz`. Take `⟨x', rfl⟩` from `hz'`.

Conclude with `⟨x + x', by rw [TensorProduct.tmul_add]⟩`.
-/
private theorem exists_eq_one_tmul_quotient {A : Type} [CommRing A] (I : Ideal A) {M : Type}
    [AddCommGroup M] [Module A M] (z : (A ⧸ I) ⊗[A] M) : ∃ x : M, z = (1 : A ⧸ I) ⊗ₜ[A] x := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul t x =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective t
    refine ⟨r • x, ?_⟩
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    rfl
  | add z z' hz hz' =>
    obtain ⟨x, rfl⟩ := hz
    obtain ⟨x', rfl⟩ := hz'
    exact ⟨x + x', by rw [TensorProduct.tmul_add]⟩

open TensorProduct in
/- English proof (translation)
Establish `h` using `quotTensorEquivQuotSMul_mk_tmul (M := M) I 1 y`. Rewrite `h` using `[map_one, one_smul]`. Rewrite using `[← (quotTensorEquivQuotSMul M I).map_eq_zero_iff, h, Submodule.Quotient.mk_eq_zero]`.
-/
private theorem one_tmul_quotient_eq_zero_iff_mem_smul {A : Type} [CommRing A] (I : Ideal A) {M : Type}
    [AddCommGroup M] [Module A M] (y : M) :
    (1 : A ⧸ I) ⊗ₜ[A] y = 0 ↔ y ∈ I • (⊤ : Submodule A M) := by
  have h := quotTensorEquivQuotSMul_mk_tmul (M := M) I 1 y
  rw [map_one, one_smul] at h
  rw [← (quotTensorEquivQuotSMul M I).map_eq_zero_iff, h, Submodule.Quotient.mk_eq_zero]

open TensorProduct in

/- English proof (translation)
Introduce `A _ 𝔞 h𝔞 P _ _ _ P' _ _ _ _ w hw`. Establish `surj : Function.Surjective w`. Rewrite using `[← LinearMap.range_eq_top, eq_top_iff]`. Use `Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top h𝔞 ?_` and prove the remaining obligations. Introduce `y _`.

Take `⟨z, hz⟩` from `hw.2 ((1 : A ⧸ 𝔞) ⊗ₜ[A] y)`. Take `⟨x, rfl⟩` from `exists_eq_one_tmul_quotient 𝔞 z`. Rewrite `hz` using `[LinearMap.baseChange_tmul]`. Establish `hmem : w x - y ∈ 𝔞 • (⊤ : Submodule A P')`. Rewrite using `[← one_tmul_quotient_eq_zero_iff_mem_smul, TensorProduct.tmul_sub, hz, sub_self]`.

Establish `: y = w x - (w x - y)` using `by abel`. Rewrite using `[this]`. Conclude with `Submodule.sub_mem _ (Submodule.mem_sup_left ⟨x, rfl⟩) (Submodule.mem_sup_right hmem)`. Use `⟨?_, surj⟩` and prove the remaining obligations. Take `⟨s, hs⟩` from `Module.projective_lifting_property w LinearMap.id surj`.

Use `set π : P →ₗ[A] P := LinearMap.id - s ∘ₗ w with hπ`. Establish `hwπ : ∀ p, w (π p) = 0` using `fun p => by`. Use `LinearMap.congr_fun hs (w p)` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, LinearMap.id_apply] at this`. Simplify using `[hπ, this]`.

Establish `hπw : ∀ p, w p = 0 → π p = p` using `fun p hp => by simp [hπ, hp]`. Establish `hbot : LinearMap.range π = ⊥`. Use `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot 𝔞 _ ?_ ?_ h𝔞` and prove the remaining obligations. Rewrite using `[LinearMap.range_eq_map]`. Conclude with `Module.Finite.fg_top.map _`.

Introduce and unpack `_ ⟨p, rfl⟩`. Establish `h0 : (1 : A ⧸ 𝔞) ⊗ₜ[A] π p = 0`. Apply `hw.1` to reduce the goal to its premises. Rewrite using `[LinearMap.baseChange_tmul, hwπ, TensorProduct.tmul_zero, map_zero]`. Rewrite `h0` using `[one_tmul_quotient_eq_zero_iff_mem_smul]`.

Rewrite using `[LinearMap.range_eq_map, ← Submodule.map_smul'', ← hπw _ (hwπ p)]`. Conclude with `Submodule.mem_map_of_mem h0`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `p hp`. Establish `: π p ∈ LinearMap.range π` using `⟨p, rfl⟩`.

Rewrite `this` using `[hbot, Submodule.mem_bot, hπw p hp]`. Conclude with `this`.
-/
theorem _root_.GlobalTheory.BSP.bijective_of_bijective_baseChange_quotient :
    ∀ (A : Type) [CommRing A] (𝔞 : Ideal A), 𝔞 ≤ Ideal.jacobson ⊥ → ∀ (P : Type) [AddCommGroup P] [Module A P] [Module.Finite A P] (P' : Type) [AddCommGroup P'] [Module A P'] [Module.Finite A P'] [Module.Projective A P'] (w : P →ₗ[A] P'), Function.Bijective (w.baseChange (A ⧸ 𝔞)) → Function.Bijective w := by
  intro A _ 𝔞 h𝔞 P _ _ _ P' _ _ _ _ w hw
  have surj : Function.Surjective w := by
    rw [← LinearMap.range_eq_top, eq_top_iff]
    refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top h𝔞 ?_
    intro y _
    obtain ⟨z, hz⟩ := hw.2 ((1 : A ⧸ 𝔞) ⊗ₜ[A] y)
    obtain ⟨x, rfl⟩ := exists_eq_one_tmul_quotient 𝔞 z
    rw [LinearMap.baseChange_tmul] at hz
    have hmem : w x - y ∈ 𝔞 • (⊤ : Submodule A P') := by
      rw [← one_tmul_quotient_eq_zero_iff_mem_smul, TensorProduct.tmul_sub, hz, sub_self]
    have : y = w x - (w x - y) := by abel
    rw [this]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left ⟨x, rfl⟩) (Submodule.mem_sup_right hmem)
  refine ⟨?_, surj⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property w LinearMap.id surj
  set π : P →ₗ[A] P := LinearMap.id - s ∘ₗ w with hπ
  have hwπ : ∀ p, w (π p) = 0 := fun p => by
    have := LinearMap.congr_fun hs (w p)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp [hπ, this]
  have hπw : ∀ p, w p = 0 → π p = p := fun p hp => by simp [hπ, hp]
  have hbot : LinearMap.range π = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot 𝔞 _ ?_ ?_ h𝔞
    · rw [LinearMap.range_eq_map]
      exact Module.Finite.fg_top.map _
    · rintro _ ⟨p, rfl⟩
      have h0 : (1 : A ⧸ 𝔞) ⊗ₜ[A] π p = 0 := by
        apply hw.1
        rw [LinearMap.baseChange_tmul, hwπ, TensorProduct.tmul_zero, map_zero]
      rw [one_tmul_quotient_eq_zero_iff_mem_smul] at h0
      rw [LinearMap.range_eq_map, ← Submodule.map_smul'', ← hπw _ (hwπ p)]
      exact Submodule.mem_map_of_mem h0
  rw [injective_iff_map_eq_zero]
  intro p hp
  have : π p ∈ LinearMap.range π := ⟨p, rfl⟩
  rw [hbot, Submodule.mem_bot, hπw p hp] at this
  exact this

end GlobalTheory.BSP
