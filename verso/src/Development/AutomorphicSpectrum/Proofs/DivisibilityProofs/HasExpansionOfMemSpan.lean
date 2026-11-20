import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBundles

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

noncomputable section

def negReal (N : ℕ) : MvPolynomial (Fin N) ℤ →ₐ[ℤ] MvPolynomial (Fin N) ℝ :=
  aeval fun i => (-X i : MvPolynomial (Fin N) ℝ)

/- English proof (translation)
Simplify using `only [negReal, hsymm, map_sum, map_multiset_prod, Multiset.map_map, Function.comp_def, aeval_X]`.
-/
theorem negReal_hsymm (N a : ℕ) :
    negReal N (hsymm (Fin N) ℤ a) =
      aeval (fun i => (-X i : MvPolynomial (Fin N) ℝ)) (hsymm (Fin N) ℝ a) := by
  simp only [negReal, hsymm, map_sum, map_multiset_prod, Multiset.map_map, Function.comp_def, aeval_X]

/- English proof (translation)
Establish `h` using `hP.aeval (S := ℝ) (n := 1) (fun i => (-X i : MvPolynomial (Fin N) ℝ)) (fun i => (isHomogeneous_X ℝ i).neg)`. Simplify `h` using `[negReal]`.
-/
theorem negReal_isHomogeneous {N n : ℕ} {P : MvPolynomial (Fin N) ℤ} (hP : P.IsHomogeneous n) :
    (negReal N P).IsHomogeneous n := by
  have h := hP.aeval (S := ℝ) (n := 1) (fun i => (-X i : MvPolynomial (Fin N) ℝ))
    (fun i => (isHomogeneous_X ℝ i).neg)
  simpa [negReal] using h

/- English proof (translation)
Simplify using `only [negReal, psum, map_sum, map_pow, aeval_X, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[neg_pow]`.
-/
theorem negReal_psum (N k : ℕ) :
    negReal N (psum (Fin N) ℤ k) = (-1) ^ k * ∑ i, (X i ^ k : MvPolynomial (Fin N) ℝ) := by
  simp only [negReal, psum, map_sum, map_pow, aeval_X, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [neg_pow]

def HasExpansion (N k : ℕ) (G : MvPolynomial (Fin N) ℤ) : Prop :=
  ∃ R : ℕ → MvPolynomial (Fin N) ℝ, (∀ a, (R a).IsHomogeneous (k - a)) ∧
    negReal N G = ∑ a ∈ Finset.Icc 1 k,
      aeval (fun i => (-X i : MvPolynomial (Fin N) ℝ)) (hsymm (Fin N) ℝ a) * R a

/- English proof (translation)
Establish `hne : μ.parts ≠ 0`. Introduce `h`. Use `μ.parts_sum` as an intermediate fact. Rewrite `this` using `[h]`. Simplify using `at this`.

Use linear arithmetic over natural numbers and integers. Take `⟨a, ha⟩` from `Multiset.exists_mem_of_ne_zero hne`. Take `⟨t, ht⟩` from `Multiset.exists_cons_of_mem ha`. Establish `hsum : a + t.sum = k`. Use `μ.parts_sum` as an intermediate fact.

Rewrite `this` using `[ht, Multiset.sum_cons]`. Then use the resulting hypothesis. Establish `hpos : 0 < a` using `μ.parts_pos ha`. Establish `hmem : a ∈ Finset.Icc 1 k` using `Finset.mem_Icc.mpr ⟨hpos, by omega⟩`. Use `⟨Pi.single a (negReal N (t.map (hsymm (Fin N) ℤ)).prod), fun b => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hb : b = a`.

Substitute `hb` using the available equality. Rewrite using `[Pi.single_eq_same]`. Establish `h` using `negReal_isHomogeneous (SymmetricSpanHsymm.isHomogeneous_prod_map_hsymm (σ := Fin N) t)`. Rewrite `h` using `[show t.sum = k - b by omega]`. Then use the resulting hypothesis. Rewrite using `[Pi.single_eq_of_ne hb]`.

Conclude with `isHomogeneous_zero _ _ _`. Rewrite using `[Finset.sum_eq_single_of_mem a hmem (fun b _ hb => by rw [Pi.single_eq_of_ne hb, mul_zero])]`. Rewrite using `[Pi.single_eq_same, hsymmPart, ht, Multiset.map_cons, Multiset.prod_cons, map_mul, negReal_hsymm]`.
-/
theorem hasExpansion_hsymmPart {N k : ℕ} (hk : 1 ≤ k) (μ : k.Partition) :
    HasExpansion N k (hsymmPart (Fin N) ℤ μ) := by
  classical
  have hne : μ.parts ≠ 0 := by
    intro h
    have := μ.parts_sum
    rw [h] at this
    simp at this
    omega
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne
  obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem ha
  have hsum : a + t.sum = k := by
    have := μ.parts_sum
    rwa [ht, Multiset.sum_cons] at this
  have hpos : 0 < a := μ.parts_pos ha
  have hmem : a ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨hpos, by omega⟩
  refine ⟨Pi.single a (negReal N (t.map (hsymm (Fin N) ℤ)).prod), fun b => ?_, ?_⟩
  · by_cases hb : b = a
    · subst hb
      rw [Pi.single_eq_same]
      have h := negReal_isHomogeneous (SymmetricSpanHsymm.isHomogeneous_prod_map_hsymm (σ := Fin N) t)
      rwa [show t.sum = k - b by omega] at h
    · rw [Pi.single_eq_of_ne hb]
      exact isHomogeneous_zero _ _ _
  · rw [Finset.sum_eq_single_of_mem a hmem
      (fun b _ hb => by rw [Pi.single_eq_of_ne hb, mul_zero])]
    rw [Pi.single_eq_same, hsymmPart, ht, Multiset.map_cons, Multiset.prod_cons, map_mul,
      negReal_hsymm]

/- English proof (translation)
Proceed by induction on `hG using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨μ, rfl⟩` from `hx`. Conclude with `hasExpansion_hsymmPart hk μ`. Consider the case `zero => exact ⟨0, fun a => isHomogeneous_zero _ _ _, by simp⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨R, hR, e⟩` from `hx`. Take `⟨S, hS, f⟩` from `hy`. Use `⟨R + S, fun a => (hR a).add (hS a), ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, e, f, Pi.add_apply, mul_add, Finset.sum_add_distrib]`.

Consider the case `smul c x _ hx`. Take `⟨R, hR, e⟩` from `hx`. Use `⟨fun a => C (c : ℝ) * R a, fun a => ?_, ?_⟩` and prove the remaining obligations. Simplify using `using (isHomogeneous_C (Fin N) (c : ℝ)).mul (hR a)`. Rewrite using `[map_zsmul, e, Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[zsmul_eq_mul, show ((c : MvPolynomial (Fin N) ℝ)) = C (c : ℝ) by simp]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasExpansion_of_mem_span {N k : ℕ} (hk : 1 ≤ k) {G : MvPolynomial (Fin N) ℤ}
    (hG : G ∈ Submodule.span ℤ (Set.range fun μ : k.Partition => hsymmPart (Fin N) ℤ μ)) :
    HasExpansion N k G := by
  induction hG using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨μ, rfl⟩ := hx
    exact hasExpansion_hsymmPart hk μ
  | zero => exact ⟨0, fun a => isHomogeneous_zero _ _ _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨R, hR, e⟩ := hx
    obtain ⟨S, hS, f⟩ := hy
    refine ⟨R + S, fun a => (hR a).add (hS a), ?_⟩
    simp only [map_add, e, f, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  | smul c x _ hx =>
    obtain ⟨R, hR, e⟩ := hx
    refine ⟨fun a => C (c : ℝ) * R a, fun a => ?_, ?_⟩
    · simpa using (isHomogeneous_C (Fin N) (c : ℝ)).mul (hR a)
    · rw [map_zsmul, e, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [zsmul_eq_mul, show ((c : MvPolynomial (Fin N) ℝ)) = C (c : ℝ) by simp]
      ring

/- English proof (translation)
Introduce `N k hk`. Take `⟨R, hR, e⟩` from `hasExpansion_of_mem_span hk (SymmetricSpanHsymm.full N k (psum (Fin N) ℤ k) (isHomogeneous_psum N k) (psum_isSymmetric _ _ _))`. Use `⟨fun a => C ((-1) ^ k) * R a, fun a => ?_, ?_⟩` and prove the remaining obligations. Simplify using `using (isHomogeneous_C (Fin N) (((-1 : ℝ)) ^ k)).mul (hR a)`. Establish `h1 : ((-1 : MvPolynomial (Fin N) ℝ) ^ k) * (-1) ^ k = 1`.

Rewrite using `[← mul_pow]`. Simplify using the standard rewrite rules. Rewrite `e` using `[negReal_psum]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, h1, one_mul]`.

Use `_ = _ := by`. Rewrite using `[e, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `only [map_pow, map_neg, map_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem psum_eq_sum_hsymm_neg :
    ∀ (N k : ℕ), 1 ≤ k → ∃ R : ℕ → MvPolynomial (Fin N) ℝ, (∀ a, (R a).IsHomogeneous (k - a)) ∧
      (∑ i, X i ^ k : MvPolynomial (Fin N) ℝ) = ∑ a ∈ Finset.Icc 1 k,
        aeval (fun i => (-X i : MvPolynomial (Fin N) ℝ)) (hsymm (Fin N) ℝ a) * R a := by
  intro N k hk
  obtain ⟨R, hR, e⟩ := hasExpansion_of_mem_span hk
    (SymmetricSpanHsymm.full N k (psum (Fin N) ℤ k) (isHomogeneous_psum N k) (psum_isSymmetric _ _ _))
  refine ⟨fun a => C ((-1) ^ k) * R a, fun a => ?_, ?_⟩
  · simpa using (isHomogeneous_C (Fin N) (((-1 : ℝ)) ^ k)).mul (hR a)
  · have h1 : ((-1 : MvPolynomial (Fin N) ℝ) ^ k) * (-1) ^ k = 1 := by
      rw [← mul_pow]; simp
    rw [negReal_psum] at e
    calc (∑ i, X i ^ k : MvPolynomial (Fin N) ℝ)
        = (-1) ^ k * ((-1) ^ k * ∑ i, (X i ^ k : MvPolynomial (Fin N) ℝ)) := by
          rw [← mul_assoc, h1, one_mul]
      _ = _ := by
          rw [e, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          simp only [map_pow, map_neg, map_one]
          ring

end

end GlobalTheory.CompanionTheory.Ar.Num
