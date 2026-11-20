import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartDehomogPrime
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartLocDomain
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartHomogenise
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

/- English proof (translation)
Introduce `F _ n W t hW ht`. Use `hW.isPrime` as an intermediate fact. Use `set a : MvPolynomial (Fin n) F ⧸ W := Ideal.Quotient.mk W (linForm t) with ha_def`. Establish `ha : a ≠ 0` using `fun h => ht (Ideal.Quotient.eq_zero_iff_mem.mp h)`. Set `A` to `Localization.Away a`.

Establish `: IsDomain A` using `IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors ha)`. Set `v : A` to `IsLocalization.Away.invSelf a`. Set `φ : MvPolynomial (Fin n) F →ₐ[F] A` to `(IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F ⧸ W) A).comp (Ideal.Quotient.mkₐ F W)`. Establish `hφ : ∀ g, aeval (fun m => φ (X m)) g = φ g` using `fun g => by`. Rewrite using `[← comp_aeval_apply]`.

Simplify using the standard rewrite rules. Set `ψ : MvPolynomial (Fin n) F →ₐ[F] A` to `aeval fun m => v * φ (X m)`. Establish `hhom : ∀ {g : MvPolynomial (Fin n) F} {k : ℕ}, g.IsHomogeneous k → ψ g = v ^ k * φ g` using `fun hg => by rw [← hφ]; exact ChartLocDomain.aeval_mul_of_isHomogeneous hg _ _`. Establish `hℓ : (linForm t).IsHomogeneous 1` using `ChartLocDomain.linForm_isHomogeneous t`. Establish `hspan : Ideal.span {linForm t - 1} ≤ RingHom.ker ψ`.

Rewrite using `[Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, hhom hℓ, pow_one]`. Establish `: φ (linForm t) = algebraMap _ A a` using `rfl`. Rewrite using `[this, mul_comm, IsLocalization.Away.mul_invSelf, sub_self]`. Establish `hle : W ⊔ Ideal.span {linForm t - 1} ≤ RingHom.ker ψ`. Use `sup_le (fun g hg => ?_) hspan` and prove the remaining obligations.

Rewrite using `[RingHom.mem_ker, ← sum_homogeneousComponent g, map_sum]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hhom (homogeneousComponent_isHomogeneous k g)]`. Establish `: φ (homogeneousComponent k g) = 0`. Simplify using `[φ, Ideal.Quotient.eq_zero_iff_mem.mpr (hW.isHomog g hg k)]`.

Rewrite using `[this, mul_zero]`. Establish `hinj : Function.Injective (algebraMap (MvPolynomial (Fin n) F ⧸ W) A)` using `IsLocalization.injective A (powers_le_nonZeroDivisors_of_noZeroDivisors ha)`. Establish `hker : RingHom.ker ψ ≤ W ⊔ Ideal.span {linForm t - 1}`. Introduce `g hg`. Take `⟨G, D, hG, hGg⟩` from `ChartHomogenise.exists_homogeneous_sub_mem_span (linForm t) g hℓ`.

Establish `hψG : ψ G = 0`. Establish `h1 : ψ (G - g) = 0` using `hspan hGg`. Rewrite `h1` using `[map_sub, RingHom.mem_ker.mp hg, sub_zero]`. Conclude with `h1`. Rewrite `hψG` using `[hhom hG]`.

Establish `h1 : algebraMap _ A (Ideal.Quotient.mk W G) = 0`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[IsLocalization.Away.mul_invSelf, one_pow, one_mul]`. Both sides reduce to the same expression. Use `_ = algebraMap _ A a ^ D * (v ^ D * φ G) := by ring`.

Use `_ = 0 := by rw [hψG, mul_zero]`. Establish `hGW : G ∈ W` using `Ideal.Quotient.eq_zero_iff_mem.mp (hinj (h1.trans (map_zero _).symm))`. Establish `e : g = G - (G - g)` using `by ring`. Rewrite using `[e]`. Conclude with `Ideal.sub_mem _ (Ideal.mem_sup_left hGW) (Ideal.mem_sup_right hGg)`.

Rewrite using `[← le_antisymm hker hle]`. Conclude with `RingHom.ker_isPrime ψ`.
-/
theorem ChartDehomogPrime.proof : ChartDehomogPrime.Statement := by
  intro F _ n W t hW ht
  have := hW.isPrime
  set a : MvPolynomial (Fin n) F ⧸ W := Ideal.Quotient.mk W (linForm t) with ha_def
  have ha : a ≠ 0 := fun h => ht (Ideal.Quotient.eq_zero_iff_mem.mp h)
  let A := Localization.Away a
  have : IsDomain A := IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
  let v : A := IsLocalization.Away.invSelf a
  let φ : MvPolynomial (Fin n) F →ₐ[F] A :=
    (IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F ⧸ W) A).comp (Ideal.Quotient.mkₐ F W)
  have hφ : ∀ g, aeval (fun m => φ (X m)) g = φ g := fun g => by
    rw [← comp_aeval_apply]; simp
  let ψ : MvPolynomial (Fin n) F →ₐ[F] A := aeval fun m => v * φ (X m)
  have hhom : ∀ {g : MvPolynomial (Fin n) F} {k : ℕ}, g.IsHomogeneous k → ψ g = v ^ k * φ g :=
    fun hg => by rw [← hφ]; exact ChartLocDomain.aeval_mul_of_isHomogeneous hg _ _
  have hℓ : (linForm t).IsHomogeneous 1 := ChartLocDomain.linForm_isHomogeneous t
  have hspan : Ideal.span {linForm t - 1} ≤ RingHom.ker ψ := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one,
      hhom hℓ, pow_one]
    have : φ (linForm t) = algebraMap _ A a := rfl
    rw [this, mul_comm, IsLocalization.Away.mul_invSelf, sub_self]
  have hle : W ⊔ Ideal.span {linForm t - 1} ≤ RingHom.ker ψ := by
    refine sup_le (fun g hg => ?_) hspan
    rw [RingHom.mem_ker, ← sum_homogeneousComponent g, map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [hhom (homogeneousComponent_isHomogeneous k g)]
    have : φ (homogeneousComponent k g) = 0 := by
      simp [φ, Ideal.Quotient.eq_zero_iff_mem.mpr (hW.isHomog g hg k)]
    rw [this, mul_zero]
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin n) F ⧸ W) A) :=
    IsLocalization.injective A (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
  have hker : RingHom.ker ψ ≤ W ⊔ Ideal.span {linForm t - 1} := by
    intro g hg
    obtain ⟨G, D, hG, hGg⟩ := ChartHomogenise.exists_homogeneous_sub_mem_span (linForm t) g hℓ
    have hψG : ψ G = 0 := by
      have h1 : ψ (G - g) = 0 := hspan hGg
      rw [map_sub, RingHom.mem_ker.mp hg, sub_zero] at h1
      exact h1
    rw [hhom hG] at hψG
    have h1 : algebraMap _ A (Ideal.Quotient.mk W G) = 0 :=
      calc algebraMap _ A (Ideal.Quotient.mk W G)
          = (algebraMap _ A a * v) ^ D * φ G := by
            rw [IsLocalization.Away.mul_invSelf, one_pow, one_mul]; rfl
        _ = algebraMap _ A a ^ D * (v ^ D * φ G) := by ring
        _ = 0 := by rw [hψG, mul_zero]
    have hGW : G ∈ W := Ideal.Quotient.eq_zero_iff_mem.mp (hinj (h1.trans (map_zero _).symm))
    have e : g = G - (G - g) := by ring
    rw [e]
    exact Ideal.sub_mem _ (Ideal.mem_sup_left hGW) (Ideal.mem_sup_right hGg)
  rw [← le_antisymm hker hle]
  exact RingHom.ker_isPrime ψ

end

end GroundTheory.Heights₂.Heights
