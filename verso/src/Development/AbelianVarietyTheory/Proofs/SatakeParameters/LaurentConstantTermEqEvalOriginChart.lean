import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAffineOpenRingPolynomialEquivStatement
open GlobalTheory GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD.ResEv

open MvPolynomial

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `p hp`. Rewrite using `[← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]`. Introduce `m hm`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Establish `hm0 : m = 0` using `by ext i; simpa using h i (Set.mem_univ i)`. Substitute `hm0` using the available equality. Rewrite `hp` using `[RingHom.mem_ker]`. Establish `: aeval (R` using `k) (fun _ : Fin d ↦ (0 : k)) p = coeff 0 p := by`.

Rewrite using `[show (fun _ : Fin d ↦ (0 : k)) = 0 from rfl, MvPolynomial.aeval_zero]`. Simplify using `[MvPolynomial.constantCoeff_eq]`. Conclude with `(mem_support_iff.mp hm) (this ▸ hp)`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`.

Simplify using the standard rewrite rules.
-/
theorem ker_aeval_zero (k : Type) [Field k] (d : ℕ) :
    RingHom.ker (aeval (R := k) (fun _ : Fin d ↦ (0 : k))) = Ideal.span (Set.range X) := by
  apply le_antisymm
  · intro p hp
    rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra h
    push_neg at h
    have hm0 : m = 0 := by ext i; simpa using h i (Set.mem_univ i)
    subst hm0
    rw [RingHom.mem_ker] at hp
    have : aeval (R := k) (fun _ : Fin d ↦ (0 : k)) p = coeff 0 p := by
      rw [show (fun _ : Fin d ↦ (0 : k)) = 0 from rfl, MvPolynomial.aeval_zero]
      simp [MvPolynomial.constantCoeff_eq]
    exact (mem_support_iff.mp hm) (this ▸ hp)
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    simp

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on' with`. Consider the case `monomial n c`. Rewrite using `[aeval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_eq_mul]`. Distinguish the cases in `hn : n = 0`. Substitute `hn` using the available equality.

Simplify using `[hρ.1]`. Choose the witnesses or unpack the hypotheses as in `⟨j0, hj0⟩ : ∃ j, n j ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hn (Finsupp.ext h)`.

Establish `h0 : ∏ j : Fin d, (0 : k) ^ n j = 0` using `Finset.prod_eq_zero (Finset.mem_univ j0) (zero_pow hj0)`. Rewrite using `[h0, smul_zero]`. Set `m : Fin (d + 1) → ℤ` to `Fin.cons (-(∑ j, (n j : ℤ))) (fun j ↦ (n j : ℤ))`. Establish `hsum : ∑ i, m i = 0`. Rewrite using `[Fin.sum_univ_succ]`.

Simplify using `[m]`. Establish `hm : m ≠ 0`. Introduce `h`. Use `congrFun h j0.succ` as an intermediate fact. Simplify using `[m] at this`.

Conclude with `hj0 this`. Establish `hprod : ∏ j : Fin d, (x j.succ / x 0) ^ n j = ∏ i, x i ^ m i`. Rewrite using `[Fin.prod_univ_succ]`. Simplify using `only [m, Fin.cons_zero, Fin.cons_succ, zpow_natCast, zpow_neg]`. Rewrite using `[Finset.prod_congr rfl (fun j _ ↦ div_pow (x j.succ) (x 0) (n j)), Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, ← Nat.cast_sum, zpow_natCast, div_eq_inv_mul]`.

Rewrite using `[hprod, hρ.2 m hsum hm, mul_zero]`. Consider the case `add p q hp hq => rw [map_add, map_add, hp, hq, map_add]`.
-/
theorem res_aeval (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F)
    (hx : IsPd k x) (ρ : F →ₗ[k] k) (hρ : IsRes k x ρ) (p : MvPolynomial (Fin d) k) :
    ρ (aeval (fun j : Fin d ↦ x j.succ / x 0) p) = aeval (R := k) (fun _ : Fin d ↦ (0 : k)) p := by
  induction p using MvPolynomial.induction_on' with
  | monomial n c =>
    rw [aeval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _),
      Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      map_smul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_eq_mul]
    by_cases hn : n = 0
    · subst hn
      simp [hρ.1]
    · obtain ⟨j0, hj0⟩ : ∃ j, n j ≠ 0 := by
        by_contra h; push_neg at h; exact hn (Finsupp.ext h)
      have h0 : ∏ j : Fin d, (0 : k) ^ n j = 0 := Finset.prod_eq_zero (Finset.mem_univ j0) (zero_pow hj0)
      rw [h0, smul_zero]
      let m : Fin (d + 1) → ℤ := Fin.cons (-(∑ j, (n j : ℤ))) (fun j ↦ (n j : ℤ))
      have hsum : ∑ i, m i = 0 := by
        rw [Fin.sum_univ_succ]; simp [m]
      have hm : m ≠ 0 := by
        intro h
        have := congrFun h j0.succ
        simp [m] at this
        exact hj0 this
      have hprod : ∏ j : Fin d, (x j.succ / x 0) ^ n j = ∏ i, x i ^ m i := by
        rw [Fin.prod_univ_succ]
        simp only [m, Fin.cons_zero, Fin.cons_succ, zpow_natCast, zpow_neg]
        rw [Finset.prod_congr rfl (fun j _ ↦ div_pow (x j.succ) (x 0) (n j)), Finset.prod_div_distrib,
          Finset.prod_pow_eq_pow_sum, ← Nat.cast_sum, zpow_natCast, div_eq_inv_mul]
      rw [hprod, hρ.2 m hsum hm, mul_zero]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]

end GlobalTheory.PD.ResEv

open MvPolynomial in
/- English proof (translation)
Introduce `k _ F _ _ d x hx ρ hρ`. Take `⟨e, he⟩` from `GlobalTheory.T.standardAffineOpen_ring_polynomialEquiv k F d x hx 0`. Establish `hv : ∀ p : MvPolynomial (Fin d) k, ((e p : rA k x {0}) : F) = aeval (fun j : Fin d ↦ x j.succ / x 0) p`. Introduce `p`. Establish `h1 : ((rA k x {0}).val.comp e.toAlgHom) = aeval (fun j : Fin d ↦ x j.succ / x 0)`.

Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `j`. Simplify using `[he]`. Conclude with `congrArg (fun f => f p) (congrArg DFunLike.coe h1)`. Use `⟨(aeval (R := k) (fun _ : Fin d ↦ (0 : k))).comp e.symm.toAlgHom, fun a => ?_, ?_⟩` and prove the remaining obligations.

Use `GlobalTheory.PD.ResEv.res_aeval k F d x hx ρ hρ (e.symm a)` as an intermediate fact. Rewrite `this` using `[← hv, AlgEquiv.apply_symm_apply]`. Simplify using `using this`. Establish `ht : (Set.range fun j : Fin d => (⟨x j.succ / x 0, Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, j.succ, rfl⟩⟩ : rA k x {0})) = (e.toRingEquiv : MvPolynomial (Fin d) k →+* rA k x {0}) '' Set.range X`. Rewrite using `[← Set.range_comp]`.

Use `congr 1`. Use function extensionality and compare the values at `j`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[he]`. Rewrite using `[ht, ← Ideal.map_span, ← GlobalTheory.PD.ResEv.ker_aeval_zero]`.

Use extensionality with `a`. Rewrite using `[Ideal.map_comap_of_equiv, Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker]`. Both sides reduce to the same expression.
-/
theorem GlobalTheory.PD.ResEv.chart0 : ∀ (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), IsPd k x → ∀ ρ : F →ₗ[k] k, IsRes k x ρ → ∃ ev : rA k x {0} →ₐ[k] k, (∀ a : rA k x {0}, ρ a = ev a) ∧ RingHom.ker ev = Ideal.span (Set.range fun j : Fin d => (⟨x j.succ / x 0, Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, j.succ, rfl⟩⟩ : rA k x {0})) := by
  intro k _ F _ _ d x hx ρ hρ
  obtain ⟨e, he⟩ := GlobalTheory.T.standardAffineOpen_ring_polynomialEquiv k F d x hx 0
  have hv : ∀ p : MvPolynomial (Fin d) k, ((e p : rA k x {0}) : F) = aeval (fun j : Fin d ↦ x j.succ / x 0) p := by
    intro p
    have h1 : ((rA k x {0}).val.comp e.toAlgHom) = aeval (fun j : Fin d ↦ x j.succ / x 0) := by
      apply MvPolynomial.algHom_ext
      intro j
      simp [he]
    exact congrArg (fun f => f p) (congrArg DFunLike.coe h1)
  refine ⟨(aeval (R := k) (fun _ : Fin d ↦ (0 : k))).comp e.symm.toAlgHom, fun a => ?_, ?_⟩
  · have := GlobalTheory.PD.ResEv.res_aeval k F d x hx ρ hρ (e.symm a)
    rw [← hv, AlgEquiv.apply_symm_apply] at this
    simpa using this
  · have ht : (Set.range fun j : Fin d => (⟨x j.succ / x 0, Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, j.succ, rfl⟩⟩ : rA k x {0})) = (e.toRingEquiv : MvPolynomial (Fin d) k →+* rA k x {0}) '' Set.range X := by
      rw [← Set.range_comp]
      congr 1
      funext j
      apply Subtype.ext
      simp [he]
    rw [ht, ← Ideal.map_span, ← GlobalTheory.PD.ResEv.ker_aeval_zero]
    ext a
    rw [Ideal.map_comap_of_equiv, Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker]
    rfl
