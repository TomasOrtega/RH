import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConeVarInj
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConeVarNumerator
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

/- English proof (translation)
Introduce `F _ K _ _ ι _ P hP W hW hPW v hv`. Use `hP.isPrime` as an intermediate fact. Use `hW.isPrime` as an intermediate fact. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `p hp`.

Take `⟨B, g, h, -, hgW, hh, hc, hφ⟩` from `hNum F K ι P hP W hW hPW v hv p`. Establish `hu : ∀ d : K →₀ ℕ, IsMultiHomog (∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ d k) ⇑d` using `fun d => by`. Unfold `IsMultiHomog`. Use `IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, v k⟩ : MRing ι F) ^ d k) (fun k => d k • blockWeight ι ⟨k, v k⟩) (fun k _ => (isWeightedHomogeneous_X F (blockWeight ι) ⟨k, v k⟩).pow (d k)) using 1` and compare the differences between its conclusion and the goal. Use extensionality with `k`.

Simplify using `[blockWeight, Finset.sum_apply, Pi.single_apply]`. Establish `huW : ∀ d : K →₀ ℕ, ∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ d k ∉ W` using `fun d => by`. Rewrite using `[Ideal.IsPrime.prod_mem_iff]`. Introduce and unpack `⟨k, -, hk⟩`. Conclude with `hv k (hW.isPrime.mem_of_pow_mem _ hk)`.

Establish `hN : ∑ d ∈ p.support, h d * ∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ d k ∈ P`. Establish `hg0 : algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P g) ≠ 0`. Rewrite using `[Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `fun hg => hgW (hPW hg)`. Rewrite `hφ` using `[hp, ZeroMemClass.coe_zero, eq_comm, div_eq_zero_iff, or_iff_left hg0, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `hφ`. Use `MvPolynomial.ext _ _ fun d => ?_` and prove the remaining obligations. Rewrite using `[coeff_zero]`. Assume the negation of the conclusion as `hd`. Establish `hcomp` using `hP.multiHomog _ hN (B + ⇑d)`.

Rewrite `hcomp` using `[map_sum, Finset.sum_eq_single d]`. Rewrite `hcomp` using `[((hh d).mul (hu d)).weightedHomogeneousComponent_same]`. Establish `hhd : h d ∈ P` using `(hP.isPrime.mem_or_mem hcomp).resolve_right fun hm => huW d (hPW hm)`. Apply `hd` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[hc d, Ideal.Quotient.eq_zero_iff_mem.mpr hhd, map_zero, zero_div]`. Both sides reduce to the same expression. Introduce `d' _ hne`. Use `((hh d').mul (hu d')).weightedHomogeneousComponent_ne _ fun heq => hne ?_` and prove the remaining obligations. Use extensionality with `k`.

Use `congrFun heq k` as an intermediate fact. Simplify using `only [Pi.add_apply] at this`. Use linear arithmetic over natural numbers and integers. Conclude with `fun hn => absurd (mem_support_iff.mpr hd) hn`.
-/
theorem ConeVarInj.proof (hNum : ConeVarNumerator.Statement.{u}) : ConeVarInj.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW v hv
  have := hP.isPrime
  have := hW.isPrime
  rw [injective_iff_map_eq_zero]
  intro p hp
  obtain ⟨B, g, h, -, hgW, hh, hc, hφ⟩ := hNum F K ι P hP W hW hPW v hv p

  have hu : ∀ d : K →₀ ℕ, IsMultiHomog (∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ d k) ⇑d := fun d => by
    unfold IsMultiHomog
    convert IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, v k⟩ : MRing ι F) ^ d k)
      (fun k => d k • blockWeight ι ⟨k, v k⟩)
      (fun k _ => (isWeightedHomogeneous_X F (blockWeight ι) ⟨k, v k⟩).pow (d k)) using 1
    ext k
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  have huW : ∀ d : K →₀ ℕ, ∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ d k ∉ W := fun d => by
    rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨k, -, hk⟩
    exact hv k (hW.isPrime.mem_of_pow_mem _ hk)
  have hN : ∑ d ∈ p.support, h d * ∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ d k ∈ P := by
    have hg0 : algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P g) ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact fun hg => hgW (hPW hg)
    rw [hp, ZeroMemClass.coe_zero, eq_comm, div_eq_zero_iff, or_iff_left hg0,
      IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at hφ
    exact hφ
  refine MvPolynomial.ext _ _ fun d => ?_
  rw [coeff_zero]
  by_contra hd
  have hcomp := hP.multiHomog _ hN (B + ⇑d)
  rw [map_sum, Finset.sum_eq_single d] at hcomp
  · rw [((hh d).mul (hu d)).weightedHomogeneousComponent_same] at hcomp
    have hhd : h d ∈ P := (hP.isPrime.mem_or_mem hcomp).resolve_right fun hm => huW d (hPW hm)
    apply hd
    apply Subtype.ext
    rw [hc d, Ideal.Quotient.eq_zero_iff_mem.mpr hhd, map_zero, zero_div]
    rfl
  · intro d' _ hne
    refine ((hh d').mul (hu d')).weightedHomogeneousComponent_ne _ fun heq => hne ?_
    ext k
    have := congrFun heq k
    simp only [Pi.add_apply] at this
    omega
  · exact fun hn => absurd (mem_support_iff.mpr hd) hn

end

end GroundTheory.Heights₂.Heights.FieldNumbers
