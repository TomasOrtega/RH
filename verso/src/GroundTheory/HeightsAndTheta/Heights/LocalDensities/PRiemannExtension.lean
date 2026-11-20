import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.LeviFormGbPotOne
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.StatementsKrullHeightOne
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.StatementsZariskiDense
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB

/- English proof (translation)
Establish `: IsJacobsonRing A` using `isJacobsonRing_of_finiteType (A := ℂ)`. Establish `hJ : P.jacobson = P` using `IsJacobsonRing.out ‹_› (Ideal.IsPrime.isRadical ‹_›)`. Rewrite `hc` using `[← hJ, Ideal.jacobson, Submodule.mem_sInf]`. Use `push Not at hc`. Take `⟨m, ⟨hPm, hm⟩, hcm⟩` from `hc`.

Use `letI : Field (A ⧸ m) := Ideal.Quotient.field m`. Establish `: Module.Finite ℂ (A ⧸ m)` using `finite_of_finite_type_of_isJacobsonRing ℂ (A ⧸ m)`. Set `e : ℂ ≃ₐ[ℂ] A ⧸ m` to `AlgEquiv.ofBijective (Algebra.ofId ℂ (A ⧸ m)) IsAlgClosed.algebraMap_bijective_of_isIntegral`. Use `⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ m), fun a ha => ?_, ?_⟩` and prove the remaining obligations. Simplify using `[Ideal.Quotient.eq_zero_iff_mem.2 (hPm ha)]`.

Simplify `hcm` using `[Ideal.Quotient.eq_zero_iff_mem]`.
-/
theorem RiemannExt.exists_point {A : Type} [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]
    (P : Ideal A) [P.IsPrime] (c : A) (hc : c ∉ P) :
    ∃ x : A →ₐ[ℂ] ℂ, (∀ a ∈ P, x a = 0) ∧ x c ≠ 0 := by
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := ℂ)
  have hJ : P.jacobson = P := IsJacobsonRing.out ‹_› (Ideal.IsPrime.isRadical ‹_›)
  rw [← hJ, Ideal.jacobson, Submodule.mem_sInf] at hc
  push Not at hc
  obtain ⟨m, ⟨hPm, hm⟩, hcm⟩ := hc
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  have : Module.Finite ℂ (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (A ⧸ m)
  let e : ℂ ≃ₐ[ℂ] A ⧸ m :=
    AlgEquiv.ofBijective (Algebra.ofId ℂ (A ⧸ m)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ m), fun a ha => ?_, ?_⟩
  · simp [Ideal.Quotient.eq_zero_iff_mem.2 (hPm ha)]
  · simpa [Ideal.Quotient.eq_zero_iff_mem] using hcm

/- English proof (translation)
Introduce `A _ _ p q ⟨hft, hdom, hic, hq, hbdd⟩`. Assume the negation of the conclusion as `hne`. Establish `hdvd : ¬ q ∣ p` using `fun ⟨r, hr⟩ => hne ⟨r, hr⟩`. Use `hdom` as an intermediate fact. Use `hft` as an intermediate fact.

Establish `: IsNoetherianRing A` using `Algebra.FiniteType.isNoetherianRing ℂ A`. Establish `hp : p ≠ 0` using `by rintro rfl; exact hdvd (dvd_zero q)`. Take `⟨P, hP, -, c, hc, t, ht, hct⟩` from `hK A p q ⟨hq, hdvd⟩`. Take `⟨x, hxP, hxc⟩` from `RiemannExt.exists_point P c hc`. Take `⟨s, ε, hε, M, hM⟩` from `hbdd x`.

Establish `hδ : 0 < ‖x c‖` using `norm_pos_iff.2 hxc`. Establish `hxt : x t = 0` using `hxP t ht`. Establish `hM1 : 0 < |M| + 1` using `by positivity`. Take `⟨y, hy, hyg⟩` from `hZ A (p * q) ⟨hft, hdom, mul_ne_zero hp hq⟩ x (insert c (insert t s)) (min ε (min (‖x c‖ / 2) (‖x c‖ / (2 * (|M| + 1))))) (by positivity)`. Establish `hyp : y p ≠ 0` using `fun h => hyg (by rw [map_mul, h, zero_mul])`.

Establish `hyq : y q ≠ 0` using `fun h => hyg (by rw [map_mul, h, mul_zero])`. Establish `h1` using `hM y (fun a ha => (hy a (by simp [ha])).trans_le (min_le_left _ _)) hyq`. Establish `hyc : ‖y c - x c‖ < ‖x c‖ / 2` using `(hy c (by simp)).trans_le ((min_le_right _ _).trans (min_le_left _ _))`. Establish `hyt : ‖y t‖ < ‖x c‖ / (2 * (|M| + 1))`. Use `(hy t (by simp)).trans_le ((min_le_right _ _).trans (min_le_right _ _))` as an intermediate fact.

Rewrite `this` using `[hxt, sub_zero]`. Then use the resulting hypothesis. Establish `hrel : ‖y c‖ * ‖y q‖ = ‖y t‖ * ‖y p‖`. Rewrite using `[← norm_mul, ← norm_mul, ← map_mul, ← map_mul, hct]`. Establish `hc' : ‖x c‖ / 2 < ‖y c‖`. Use `norm_sub_norm_le (x c) (y c)` as an intermediate fact.

Rewrite `this` using `[norm_sub_rev]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `key : ‖y c‖ ≤ |M| * ‖y t‖`. Establish `hle : ‖y c‖ * ‖y q‖ ≤ (|M| * ‖y t‖) * ‖y q‖`. Rewrite using `[hrel]`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `le_of_mul_le_mul_right hle (norm_pos_iff.2 hyq)`. Establish `hsmall : |M| * ‖y t‖ < ‖x c‖ / 2`. Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem RiemannExt.proof (hK : KrullHeightOne.Statement) (hZ : ZariskiDense.Statement) :
    RiemannExt.Statement := by
  classical
  intro A _ _ p q ⟨hft, hdom, hic, hq, hbdd⟩
  by_contra hne
  have hdvd : ¬ q ∣ p := fun ⟨r, hr⟩ => hne ⟨r, hr⟩
  have := hdom
  have := hft
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
  have hp : p ≠ 0 := by rintro rfl; exact hdvd (dvd_zero q)
  obtain ⟨P, hP, -, c, hc, t, ht, hct⟩ := hK A p q ⟨hq, hdvd⟩
  obtain ⟨x, hxP, hxc⟩ := RiemannExt.exists_point P c hc
  obtain ⟨s, ε, hε, M, hM⟩ := hbdd x
  have hδ : 0 < ‖x c‖ := norm_pos_iff.2 hxc
  have hxt : x t = 0 := hxP t ht
  have hM1 : 0 < |M| + 1 := by positivity
  obtain ⟨y, hy, hyg⟩ := hZ A (p * q) ⟨hft, hdom, mul_ne_zero hp hq⟩ x (insert c (insert t s))
    (min ε (min (‖x c‖ / 2) (‖x c‖ / (2 * (|M| + 1))))) (by positivity)
  have hyp : y p ≠ 0 := fun h => hyg (by rw [map_mul, h, zero_mul])
  have hyq : y q ≠ 0 := fun h => hyg (by rw [map_mul, h, mul_zero])
  have h1 := hM y (fun a ha => (hy a (by simp [ha])).trans_le (min_le_left _ _)) hyq
  have hyc : ‖y c - x c‖ < ‖x c‖ / 2 :=
    (hy c (by simp)).trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hyt : ‖y t‖ < ‖x c‖ / (2 * (|M| + 1)) := by
    have := (hy t (by simp)).trans_le ((min_le_right _ _).trans (min_le_right _ _))
    rwa [hxt, sub_zero] at this
  have hrel : ‖y c‖ * ‖y q‖ = ‖y t‖ * ‖y p‖ := by
    rw [← norm_mul, ← norm_mul, ← map_mul, ← map_mul, hct]
  have hc' : ‖x c‖ / 2 < ‖y c‖ := by
    have := norm_sub_norm_le (x c) (y c)
    rw [norm_sub_rev] at this
    linarith
  have key : ‖y c‖ ≤ |M| * ‖y t‖ := by
    have hle : ‖y c‖ * ‖y q‖ ≤ (|M| * ‖y t‖) * ‖y q‖ := by
      rw [hrel]
      calc ‖y t‖ * ‖y p‖ ≤ ‖y t‖ * (M * ‖y q‖) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ ≤ ‖y t‖ * (|M| * ‖y q‖) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (le_abs_self M) (norm_nonneg _)) (norm_nonneg _)
        _ = (|M| * ‖y t‖) * ‖y q‖ := by ring
    exact le_of_mul_le_mul_right hle (norm_pos_iff.2 hyq)
  have hsmall : |M| * ‖y t‖ < ‖x c‖ / 2 := by
    calc |M| * ‖y t‖ ≤ (|M| + 1) * ‖y t‖ := by nlinarith [norm_nonneg (y t)]
      _ < (|M| + 1) * (‖x c‖ / (2 * (|M| + 1))) := mul_lt_mul_of_pos_left hyt hM1
      _ = ‖x c‖ / 2 := by field_simp
  linarith

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
