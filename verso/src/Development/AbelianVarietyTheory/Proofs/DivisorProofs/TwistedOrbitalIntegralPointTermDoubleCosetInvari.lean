import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwOrbEqFinsumTwTerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubgroupAverageLinearTranslateConst
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerAbs

variable {G : Type} [Group G]

/- English proof (translation)
Establish `htd : t * δ = δ * θ t` using `ht`. Rewrite using `[map_mul, _root_.mul_inv_rev]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem twCent_mul_inv_conj (θ : G →* G) (δ : G) {t : G} (ht : t ∈ twCent θ δ) (z : G) :
    (t * z)⁻¹ * δ * θ (t * z) = z⁻¹ * δ * θ z := by
  have htd : t * δ = δ * θ t := ht
  rw [map_mul, _root_.mul_inv_rev]
  calc z⁻¹ * t⁻¹ * δ * (θ t * θ z) = z⁻¹ * (t⁻¹ * (δ * θ t)) * θ z := by simp only [mul_assoc]
    _ = z⁻¹ * δ * θ z := by rw [← htd, inv_mul_cancel_left]

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hxT, z, hz, rfl⟩`. Use `⟨hxT, k * z * k⁻¹, K.mul_mem (K.mul_mem hk hz) (K.inv_mem hk), ?_⟩` and prove the remaining obligations.

Establish `hx : t * y * k * z * (t * y * k)⁻¹ = t * (y * (k * z * k⁻¹) * y⁻¹) * t⁻¹` using `by group`. Rewrite `hxT`, the goal using `[hx]`. Establish `hlT : y * (k * z * k⁻¹) * y⁻¹ ∈ twCent θ δ`. Establish `h` using `(twCent θ δ).mul_mem ((twCent θ δ).mul_mem ((twCent θ δ).inv_mem ht) hxT) ht`. Simplify `h` using `only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]`.

Rewrite using `[hcomm t ht _ hlT, mul_inv_cancel_right]`. Introduce and unpack `⟨hxT, z, hz, rfl⟩`. Use `⟨hxT, k⁻¹ * z * k, K.mul_mem (K.mul_mem (K.inv_mem hk) hz) hk, ?_⟩` and prove the remaining obligations. Establish `hx : t * y * k * (k⁻¹ * z * k) * (t * y * k)⁻¹ = t * (y * z * y⁻¹) * t⁻¹` using `by group`. Rewrite using `[hx, hcomm t ht _ hxT, mul_inv_cancel_right]`.
-/
theorem twCent_inf_map_conj (θ : G →* G) (K : Subgroup G) (δ : G)
    (hcomm : ∀ a ∈ twCent θ δ, ∀ b ∈ twCent θ δ, a * b = b * a) {t : G} (ht : t ∈ twCent θ δ) (y : G) {k : G}
    (hk : k ∈ K) :
    twCent θ δ ⊓ K.map (MulAut.conj (t * y * k)).toMonoidHom = twCent θ δ ⊓ K.map (MulAut.conj y).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hxT, z, hz, rfl⟩
    refine ⟨hxT, k * z * k⁻¹, K.mul_mem (K.mul_mem hk hz) (K.inv_mem hk), ?_⟩
    have hx : t * y * k * z * (t * y * k)⁻¹ = t * (y * (k * z * k⁻¹) * y⁻¹) * t⁻¹ := by group
    rw [hx] at hxT ⊢
    have hlT : y * (k * z * k⁻¹) * y⁻¹ ∈ twCent θ δ := by
      have h := (twCent θ δ).mul_mem ((twCent θ δ).mul_mem ((twCent θ δ).inv_mem ht) hxT) ht
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h
    rw [hcomm t ht _ hlT, mul_inv_cancel_right]
  · rintro ⟨hxT, z, hz, rfl⟩
    refine ⟨hxT, k⁻¹ * z * k, K.mul_mem (K.mul_mem (K.inv_mem hk) hz) hk, ?_⟩
    have hx : t * y * k * (k⁻¹ * z * k) * (t * y * k)⁻¹ = t * (y * z * y⁻¹) * t⁻¹ := by group
    rw [hx, hcomm t ht _ hxT, mul_inv_cancel_right]

/- English proof (translation)
Introduce `t ht y k hk`. Unfold `twTerm`. Rewrite using `[twCent_inf_map_conj θ K δ hcomm ht y hk]`. Use `congr 1`. Establish `key` using `(GlobalTheory.AvgLin.avg_linear_translate_const K (fun k' : K => f ((y * k')⁻¹ * δ * θ (y * k'))) (fun k' : K => f ((y * k')⁻¹ * δ * θ (y * k'))) 0 ⟨k, hk⟩ (hidx y) (hidx y)).2.2.1`.

Rewrite using `[← key]`. Use `congr 1`. Use function extensionality and compare the values at `k'`. Use `congr 1`. Rewrite using `[Subgroup.coe_mul, Subgroup.coe_mk, mul_assoc t y, mul_assoc t (y * k), ← mul_assoc y k]`.

Conclude with `twCent_mul_inv_conj θ δ ht _`.
-/
theorem twTerm_mul_mul [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ)
    (hcomm : ∀ a ∈ twCent θ δ, ∀ b ∈ twCent θ δ, a * b = b * a)
    (hidx : ∀ y : G, (rStab fun k : K => f ((y * k)⁻¹ * δ * θ (y * k))).index ≠ 0) :
    ∀ t ∈ twCent θ δ, ∀ y, ∀ k ∈ K, twTerm θ K δ f (t * y * k) = twTerm θ K δ f y := by
  intro t ht y k hk
  unfold twTerm
  rw [twCent_inf_map_conj θ K δ hcomm ht y hk]
  congr 1
  have key := (GlobalTheory.AvgLin.avg_linear_translate_const K (fun k' : K => f ((y * k')⁻¹ * δ * θ (y * k'))) (fun k' : K => f ((y * k')⁻¹ * δ * θ (y * k')))
    0 ⟨k, hk⟩ (hidx y) (hidx y)).2.2.1
  rw [← key]
  congr 1
  funext k'
  congr 1
  rw [Subgroup.coe_mul, Subgroup.coe_mk, mul_assoc t y, mul_assoc t (y * k), ← mul_assoc y k]
  exact twCent_mul_inv_conj θ δ ht _

/- English proof (translation)
Introduce `θ K δ f hcomm hidx` and use `twTerm_mul_mul θ K δ f hcomm hidx`.
-/
theorem twTerm_inv : ∀ {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ),
    (∀ a ∈ twCent θ δ, ∀ b ∈ twCent θ δ, a * b = b * a) →
    (∀ y : G, (rStab fun k : K => f ((y * k)⁻¹ * δ * θ (y * k))).index ≠ 0) →
    ∀ t ∈ twCent θ δ, ∀ y, ∀ k ∈ K, GlobalTheory.EulerAbs.twTerm θ K δ f (t * y * k) = GlobalTheory.EulerAbs.twTerm θ K δ f y :=
  fun θ K δ f hcomm hidx => twTerm_mul_mul θ K δ f hcomm hidx

end GlobalTheory.EulerAbs
