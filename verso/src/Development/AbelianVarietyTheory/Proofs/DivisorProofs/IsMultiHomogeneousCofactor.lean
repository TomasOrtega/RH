import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.CofactorHom

/- English proof (translation)
Use `letI := weightedGradedAlgebra F w`. Establish `h` using `DirectSum.coe_decompose_mul_of_left_mem (weightedHomogeneousSubmodule F w) (a := P) (b := Q) n ((mem_weightedHomogeneousSubmodule F w k P).2 hP)`. Establish `e : ∀ (m : ℕ) (R : MvPolynomial σ F), ((DirectSum.decompose (weightedHomogeneousSubmodule F w) R m : weightedHomogeneousSubmodule F w m) : MvPolynomial σ F) = weightedHomogeneousComponent w m R` using `fun m R => weightedDecomposition.decompose'_apply F w R m`. Rewrite `h` using `[e, e]`. Conclude with `h`.
-/
theorem wcomp_mul_of_left {σ F : Type} [Field F] (w : σ → ℕ) (n : ℕ) {P : MvPolynomial σ F} {k : ℕ}
    (hP : IsWeightedHomogeneous w P k) (Q : MvPolynomial σ F) :
    weightedHomogeneousComponent w n (P * Q) =
      if k ≤ n then P * weightedHomogeneousComponent w (n - k) Q else 0 := by
  classical
  letI := weightedGradedAlgebra F w
  have h := DirectSum.coe_decompose_mul_of_left_mem (weightedHomogeneousSubmodule F w) (a := P) (b := Q) n
    ((mem_weightedHomogeneousSubmodule F w k P).2 hP)
  have e : ∀ (m : ℕ) (R : MvPolynomial σ F),
      ((DirectSum.decompose (weightedHomogeneousSubmodule F w) R m : weightedHomogeneousSubmodule F w m) :
        MvPolynomial σ F) = weightedHomogeneousComponent w m R :=
    fun m R => weightedDecomposition.decompose'_apply F w R m
  rw [e, e] at h
  exact h

/- English proof (translation)
Establish `hP0 : P ≠ 0` using `left_ne_zero_of_mul hPQ`. Use `set j := Finsupp.weight w s`. Establish `hc : weightedHomogeneousComponent w j Q ≠ 0`. Introduce `h0`. Use `congrArg (coeff s) h0` as an intermediate fact.

Rewrite `this` using `[coeff_weightedHomogeneousComponent, if_pos rfl, coeff_zero]`. Conclude with `(mem_support_iff.mp hs) this`. Establish `hne : weightedHomogeneousComponent w (k + j) (P * Q) ≠ 0`. Rewrite using `[wcomp_mul_of_left w (k + j) hP Q, if_pos (Nat.le_add_right k j), Nat.add_sub_cancel_left]`. Conclude with `mul_ne_zero hP0 hc`.

Assume the negation of the conclusion as `hkm`. Conclude with `hne (hm.weightedHomogeneousComponent_ne (k + j) hkm)`.
-/
theorem weight_add_of_mul {σ F : Type} [Field F] (w : σ → ℕ) {P Q : MvPolynomial σ F} {k m : ℕ}
    (hPQ : P * Q ≠ 0) (hP : IsWeightedHomogeneous w P k) (hm : IsWeightedHomogeneous w (P * Q) m)
    (s : σ →₀ ℕ) (hs : s ∈ Q.support) : k + Finsupp.weight w s = m := by
  classical
  have hP0 : P ≠ 0 := left_ne_zero_of_mul hPQ
  set j := Finsupp.weight w s
  have hc : weightedHomogeneousComponent w j Q ≠ 0 := by
    intro h0
    have := congrArg (coeff s) h0
    rw [coeff_weightedHomogeneousComponent, if_pos rfl, coeff_zero] at this
    exact (mem_support_iff.mp hs) this
  have hne : weightedHomogeneousComponent w (k + j) (P * Q) ≠ 0 := by
    rw [wcomp_mul_of_left w (k + j) hP Q, if_pos (Nat.le_add_right k j), Nat.add_sub_cancel_left]
    exact mul_ne_zero hP0 hc
  by_contra hkm
  exact hne (hm.weightedHomogeneousComponent_ne (k + j) hkm)

end GlobalTheory.CofactorHom

open GlobalTheory.CofactorHom in

/- English proof (translation)
Introduce `F _ B N a a₁ G G' h0 ha ha₁`. Rewrite `ha`, `ha₁` using `[isMultiHomogeneous_iff_forall_weighted_lh0BlockWt]`. Establish `key : ∀ b, ∀ s ∈ G'.support, a₁ b + ∑ j : Fin N, s (b, j) = a b` using `fun b s hs => by`. Rewrite using `[← weight_lh0BlockWt_apply]`. Conclude with `weight_add_of_mul _ h0 (ha₁ b) (ha b) s hs`.

Choose the witnesses or unpack the hypotheses as in `⟨s₀, hs₀⟩ : ∃ s, s ∈ G'.support := by`. Assume the negation of the conclusion as `hno`. Use `push_neg at hno`. Apply `h0` to reduce the goal to its premises. Rewrite using `[show G' = 0 from by`.

Use extensionality with `s`. Assume the negation of the conclusion as `hc`. Conclude with `hno s (mem_support_iff.mpr hc), mul_zero]`. Use `⟨fun b => a b - a₁ b, fun s hs b => ?_, fun i => ?_⟩` and prove the remaining obligations. Use `key b s hs show _ = a b - a₁ b` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Use `key i s₀ hs₀ show a₁ i + (a i - a₁ i) = a i` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem GlobalTheory.HSShort.isMultiHomogeneous_cofactor :
    ∀ (F : Type) [Field F] (B N : ℕ) (a a₁ : Fin B → ℕ) (G G' : MvPolynomial (Fin B × Fin N) F),
      G * G' ≠ 0 → IsMultiHomogeneous a (G * G') → IsMultiHomogeneous a₁ G →
        ∃ a' : Fin B → ℕ, IsMultiHomogeneous a' G' ∧ ∀ i, a₁ i + a' i = a i := by
  intro F _ B N a a₁ G G' h0 ha ha₁
  rw [isMultiHomogeneous_iff_forall_weighted_lh0BlockWt] at ha ha₁
  have key : ∀ b, ∀ s ∈ G'.support, a₁ b + ∑ j : Fin N, s (b, j) = a b := fun b s hs => by
    rw [← weight_lh0BlockWt_apply]
    exact weight_add_of_mul _ h0 (ha₁ b) (ha b) s hs
  obtain ⟨s₀, hs₀⟩ : ∃ s, s ∈ G'.support := by
    by_contra hno
    push_neg at hno
    apply h0
    rw [show G' = 0 from by
      ext s; by_contra hc; exact hno s (mem_support_iff.mpr hc), mul_zero]
  refine ⟨fun b => a b - a₁ b, fun s hs b => ?_, fun i => ?_⟩
  · have := key b s hs
    show _ = a b - a₁ b
    omega
  · have := key i s₀ hs₀
    show a₁ i + (a i - a₁ i) = a i
    omega
