import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartZeroTrdeg
import GroundTheory.HeightsAndTheta.Heights.ChowForms.ImportsAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChartZeroTrdeg

variable {F : Type} [Field F] {n : ℕ}

def homogAt (p : MvPolynomial (Fin n) F) (j : Fin n) (N : ℕ) : MvPolynomial (Fin n) F :=
  ∑ α ∈ p.support, monomial α (coeff α p) * X j ^ (N - α.sum fun _ e => e)

/- English proof (translation)
Use `conv_rhs => rw [p.as_sum]`. Rewrite using `[homogAt, map_sum, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun α hα => ?_` and prove the remaining obligations. Establish `hk` using `(le_totalDegree hα).trans hN`. Simplify using `only [map_mul, aeval_monomial, map_pow, aeval_X, mul_pow, Finsupp.prod_mul]`.

Establish `hc : (α.prod fun a => HPow.hPow (z j)⁻¹) = (z j)⁻¹ ^ (α.sum fun _ e => e)`. Simplify using `only [Finsupp.prod, Finsupp.sum]`. Conclude with `Finset.prod_pow_eq_pow_sum _ _ _`. Rewrite using `[hc]`. Establish `: z j ^ N = z j ^ (N - α.sum fun _ e => e) * z j ^ (α.sum fun _ e => e)`.

Rewrite using `[← pow_add, Nat.sub_add_cancel hk]`. Rewrite using `[this, inv_pow]`. Clear the denominators using the available nonvanishing facts.
-/
theorem aeval_homogAt {L : Type} [Field L] [Algebra F L] (p : MvPolynomial (Fin n) F) (j : Fin n)
    (N : ℕ) (hN : p.totalDegree ≤ N) (z : Fin n → L) (hz : z j ≠ 0) :
    aeval z (homogAt p j N) = z j ^ N * aeval (fun m => z m * (z j)⁻¹) p := by
  conv_rhs => rw [p.as_sum]
  rw [homogAt, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hk := (le_totalDegree hα).trans hN
  simp only [map_mul, aeval_monomial, map_pow, aeval_X, mul_pow, Finsupp.prod_mul]
  have hc : (α.prod fun a => HPow.hPow (z j)⁻¹) = (z j)⁻¹ ^ (α.sum fun _ e => e) := by
    simp only [Finsupp.prod, Finsupp.sum]
    exact Finset.prod_pow_eq_pow_sum _ _ _
  rw [hc]
  have : z j ^ N = z j ^ (N - α.sum fun _ e => e) * z j ^ (α.sum fun _ e => e) := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  rw [this, inv_pow]
  field_simp

/- English proof (translation)
Establish `h : aeval (genPt P) = (IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F ⧸ P) (FractionRing (MvPolynomial (Fin n) F ⧸ P))).comp (Ideal.Quotient.mkₐ F P)` using `MvPolynomial.algHom_ext fun i => by simp [genPt]`. Rewrite using `[h]`. Express the relevant statement in the definitionally equal form `algebraMap _ (FractionRing (MvPolynomial (Fin n) F ⧸ P)) (Ideal.Quotient.mk P f) = 0 ↔ _`. Rewrite using `[IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]`.
-/
theorem aeval_genPt_eq_zero_iff' (P : Ideal (MvPolynomial (Fin n) F)) (f : MvPolynomial (Fin n) F) :
    aeval (genPt P) f = 0 ↔ f ∈ P := by
  have h : aeval (genPt P) = (IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F ⧸ P)
      (FractionRing (MvPolynomial (Fin n) F ⧸ P))).comp (Ideal.Quotient.mkₐ F P) :=
    MvPolynomial.algHom_ext fun i => by simp [genPt]
  rw [h]
  change algebraMap _ (FractionRing (MvPolynomial (Fin n) F ⧸ P)) (Ideal.Quotient.mk P f) = 0 ↔ _
  rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

end ChartZeroTrdeg

open ChartZeroTrdeg in

/- English proof (translation)
Introduce `F _ n d Q hQ hdim Ω _ _ y j hy hyj`. Use `hQ.isPrime` as an intermediate fact. Establish `hXj : X j ∉ Q` using `fun h => hyj (by simpa using hy _ h)`. Use `set ξ := genPt Q`. Establish `hξ : ξ j ≠ 0` using `fun h => hXj ((aeval_genPt_eq_zero_iff' Q (X j)).1 (by simpa using h))`.

Use `set gξ := aeval (R := F) (fun m => ξ m * (ξ j)⁻¹)`. Use `set gy := aeval (R := F) (fun m => y m * (y j)⁻¹)`. Establish `hker : ∀ p, gξ p = 0 → gy p = 0`. Introduce `p hp`. Establish `hH : homogAt p j p.totalDegree ∈ Q`.

Rewrite using `[← aeval_genPt_eq_zero_iff', aeval_homogAt p j _ le_rfl ξ hξ]`. Simplify using `[gξ] at hp`. Simplify using `[hp]`. Use `hy _ hH` as an intermediate fact. Rewrite `this` using `[aeval_homogAt p j _ le_rfl y hyj]`.

Simplify `this` using `[gy, hyj]`. Establish `hAξ` using `hA F n d Q j hQ hdim hXj`. Rewrite `hAξ`, the goal using `[Algebra.adjoin_range_eq_range_aeval]`. Set `e` to `Ideal.quotientKerAlgEquivOfSurjective gξ.rangeRestrict_surjective`. Set `φ` to `Ideal.Quotient.liftₐ (RingHom.ker gξ.rangeRestrict) gy.rangeRestrict fun p hp => by`.

Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `hker p (congrArg Subtype.val hp)`. Establish `hφ : Function.Surjective φ`. Introduce `b`. Take `⟨p, hp⟩` from `gy.rangeRestrict_surjective b`.

Conclude with `⟨Ideal.Quotient.mk _ p, hp⟩`. Use `trdeg_le_of_surjective (φ.comp e.symm.toAlgHom) (hφ.comp e.symm.surjective)` as an intermediate fact. Conclude with `this.trans hAξ.le`.
-/
theorem ChartZeroTrdeg.proof (hA : AffineChartTrdeg.Statement) : ChartZeroTrdeg.Statement := by
  intro F _ n d Q hQ hdim Ω _ _ y j hy hyj
  have := hQ.isPrime
  have hXj : X j ∉ Q := fun h => hyj (by simpa using hy _ h)
  set ξ := genPt Q
  have hξ : ξ j ≠ 0 := fun h => hXj ((aeval_genPt_eq_zero_iff' Q (X j)).1 (by simpa using h))
  set gξ := aeval (R := F) (fun m => ξ m * (ξ j)⁻¹)
  set gy := aeval (R := F) (fun m => y m * (y j)⁻¹)
  have hker : ∀ p, gξ p = 0 → gy p = 0 := by
    intro p hp
    have hH : homogAt p j p.totalDegree ∈ Q := by
      rw [← aeval_genPt_eq_zero_iff', aeval_homogAt p j _ le_rfl ξ hξ]
      simp [gξ] at hp
      simp [hp]
    have := hy _ hH
    rw [aeval_homogAt p j _ le_rfl y hyj] at this
    simpa [gy, hyj] using this
  have hAξ := hA F n d Q j hQ hdim hXj
  rw [Algebra.adjoin_range_eq_range_aeval] at hAξ ⊢
  let e := Ideal.quotientKerAlgEquivOfSurjective gξ.rangeRestrict_surjective
  let φ := Ideal.Quotient.liftₐ (RingHom.ker gξ.rangeRestrict) gy.rangeRestrict fun p hp => by
    apply Subtype.ext
    exact hker p (congrArg Subtype.val hp)
  have hφ : Function.Surjective φ := by
    intro b
    obtain ⟨p, hp⟩ := gy.rangeRestrict_surjective b
    exact ⟨Ideal.Quotient.mk _ p, hp⟩
  have := trdeg_le_of_surjective (φ.comp e.symm.toAlgHom) (hφ.comp e.symm.surjective)
  exact this.trans hAξ.le

end

end GroundTheory.Heights₂.Heights
