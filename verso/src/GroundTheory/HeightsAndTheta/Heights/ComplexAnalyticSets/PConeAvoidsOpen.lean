import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StConeAvoidsOpen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n d : ℕ}

/- English proof (translation)
Use `Ideal.IsHomogeneous.sup (Ideal.homogeneous_span _ _ ?_) (Ideal.homogeneous_span _ _ ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨f, -, rfl⟩`. Conclude with `⟨f.totalDegree, homogeneousComponent_mem _ _⟩`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `⟨1, (mem_homogeneousSubmodule _ _).2 (IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X _ _)⟩`.
-/
theorem isHomogeneous_leadIdeal_sup_linIdeal (J : Ideal (MvPolynomial (Fin n) ℂ))
    (A : Matrix (Fin d) (Fin n) ℂ) :
    (leadIdeal J ⊔ linIdeal A).IsHomogeneous (homogeneousSubmodule (Fin n) ℂ) := by
  refine Ideal.IsHomogeneous.sup (Ideal.homogeneous_span _ _ ?_) (Ideal.homogeneous_span _ _ ?_)
  · rintro _ ⟨f, -, rfl⟩
    exact ⟨f.totalDegree, homogeneousComponent_mem _ _⟩
  · rintro _ ⟨i, rfl⟩
    exact ⟨1, (mem_homogeneousSubmodule _ _).2
      (IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X _ _)⟩

/- English proof (translation)
Establish `hprod : ∏ i ∈ m.support, (X i : MvPolynomial (Fin n) ℂ) ^ m i = ∏ i, X i ^ m i` using `Finset.prod_subset (Finset.subset_univ _) fun i _ hi => by simp [Finsupp.notMem_support_iff.1 hi]`. Rewrite using `[← prod_X_pow_eq_monomial, hprod, ← hm, Finsupp.degree_eq_sum, ← Finset.prod_pow_eq_pow_sum]`. Conclude with `Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (show (X i : MvPolynomial (Fin n) ℂ) ∈ originIdeal n from Ideal.subset_span ⟨i, rfl⟩) _`.
-/
theorem monomial_mem_originIdeal_pow {N : ℕ} {m : Fin n →₀ ℕ} (hm : m.degree = N) :
    monomial m (1 : ℂ) ∈ originIdeal n ^ N := by
  have hprod : ∏ i ∈ m.support, (X i : MvPolynomial (Fin n) ℂ) ^ m i = ∏ i, X i ^ m i :=
    Finset.prod_subset (Finset.subset_univ _) fun i _ hi => by simp [Finsupp.notMem_support_iff.1 hi]
  rw [← prod_X_pow_eq_monomial, hprod, ← hm, Finsupp.degree_eq_sum, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow
    (show (X i : MvPolynomial (Fin n) ℂ) ∈ originIdeal n from Ideal.subset_span ⟨i, rfl⟩) _

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => simp only [pow_zero, Ideal.one_eq_top, top_le_iff, Ideal.eq_top_iff_one]`. Conclude with `Ideal.subset_span ⟨0, by simp, by simp⟩`. Consider the case `succ N ih`. Rewrite using `[pow_succ]`.

Use `(Ideal.mul_mono_left ih).trans ?_` and prove the remaining obligations. Rewrite using `[originIdeal, Ideal.span_mul_span', Ideal.span_le]`. Introduce and unpack `_ ⟨_, ⟨m, hm, rfl⟩, _, ⟨i, rfl⟩, rfl⟩`. Conclude with `Ideal.subset_span ⟨m + Finsupp.single i 1, by simp [hm], by simp [X, monomial_mul]⟩`.
-/
theorem originIdeal_pow_le_span (N : ℕ) :
    originIdeal n ^ N ≤
      Ideal.span {p | ∃ m : Fin n →₀ ℕ, m.degree = N ∧ monomial m (1 : ℂ) = p} := by
  induction N with
  | zero => simp only [pow_zero, Ideal.one_eq_top, top_le_iff, Ideal.eq_top_iff_one]
            exact Ideal.subset_span ⟨0, by simp, by simp⟩
  | succ N ih =>
    rw [pow_succ]
    refine (Ideal.mul_mono_left ih).trans ?_
    rw [originIdeal, Ideal.span_mul_span', Ideal.span_le]
    rintro _ ⟨_, ⟨m, hm, rfl⟩, _, ⟨i, rfl⟩, rfl⟩
    exact Ideal.subset_span ⟨m + Finsupp.single i 1, by simp [hm], by simp [X, monomial_mul]⟩

/- English proof (translation)
Use `(originIdeal_pow_le_span N).trans (Ideal.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨m, hm, rfl⟩`. Conclude with `h m hm`.
-/
theorem originIdeal_pow_le {N : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)}
    (h : ∀ m : Fin n →₀ ℕ, m.degree = N → monomial m (1 : ℂ) ∈ I) : originIdeal n ^ N ≤ I := by
  refine (originIdeal_pow_le_span N).trans (Ideal.span_le.2 ?_)
  rintro _ ⟨m, hm, rfl⟩
  exact h m hm

/- English proof (translation)
Use `⟨{p | ∀ A : Matrix (Fin d) (Fin n) ℂ, eval (fun ij : Fin d × Fin n => A ij.1 ij.2) p ≠ 0 → A ∈ U}, ?_⟩` and prove the remaining obligations. Use extensionality with `A`. Prove the components needed by the constructor for the conclusion. Introduce `hA`. Take `⟨p, hp, hpU⟩` from `H A hA`.

Conclude with `⟨p, hpU, hp⟩`. Introduce and unpack `⟨p, hpU, hp⟩`. Conclude with `hpU A hp`.
-/
theorem isZariskiOpen_of_local {U : Set (Matrix (Fin d) (Fin n) ℂ)}
    (H : ∀ A₀ ∈ U, ∃ p : MvPolynomial (Fin d × Fin n) ℂ,
      eval (fun ij : Fin d × Fin n => A₀ ij.1 ij.2) p ≠ 0 ∧
        ∀ A : Matrix (Fin d) (Fin n) ℂ, eval (fun ij : Fin d × Fin n => A ij.1 ij.2) p ≠ 0 → A ∈ U) :
    IsZariskiOpen U := by
  refine ⟨{p | ∀ A : Matrix (Fin d) (Fin n) ℂ,
    eval (fun ij : Fin d × Fin n => A ij.1 ij.2) p ≠ 0 → A ∈ U}, ?_⟩
  ext A
  constructor
  · intro hA
    obtain ⟨p, hp, hpU⟩ := H A hA
    exact ⟨p, hpU, hp⟩
  · rintro ⟨p, hpU, hp⟩
    exact hpU A hp

/- English proof (translation)
Introduce `n d N J`. Use `isZariskiOpen_of_local fun A₀ hA₀ => ?_` and prove the remaining obligations. Use `set V := Finset.finsuppAntidiag (Finset.univ : Finset (Fin n)) N`. Establish `hV : ∀ m : Fin n →₀ ℕ, m ∈ V ↔ m.degree = N` using `fun m => by`. Simplify using `[V, Finsupp.degree_eq_sum]`.

Establish `hrep : ∀ m : V, ∃ a ∈ leadIdeal J, ∃ h : Fin d → MvPolynomial (Fin n) ℂ, a + ∑ j, h j * linPoly A₀ j = monomial (m : Fin n →₀ ℕ) 1`. Introduce `m`. Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.1 (hA₀ (monomial_mem_originIdeal_pow ((hV m).1 m.2)))`. Take `⟨h, rfl⟩` from `Ideal.mem_span_range_iff_exists_fun.1 hb`. Conclude with `⟨a, ha, h, hab⟩`.

Use `choose a ha h hah using hrep`. Set `T : Matrix (Fin d) (Fin n) ℂ → V → MvPolynomial (Fin n) ℂ` to `fun A m => a m + ∑ j, h m j * linPoly A j`. Set `P : Matrix V V (MvPolynomial (Fin d × Fin n) ℂ)` to `fun m' m => C (coeff (m' : Fin n →₀ ℕ) (a m)) + ∑ j, ∑ k, C (coeff (m' : Fin n →₀ ℕ) (h m j * X k)) * X (j, k)`. Establish `hP : ∀ (A : Matrix (Fin d) (Fin n) ℂ) (m' m : V), (eval fun ij : Fin d × Fin n => A ij.1 ij.2).mapMatrix P m' m = coeff (m' : Fin n →₀ ℕ) (T A m)`. Introduce `A m' m`.

Use `show eval _ (P m' m) = _`. Simplify using `only [P, T, linPoly, map_add, map_sum, map_mul, eval_C, eval_X, coeff_add, coeff_sum, Finset.mul_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_left_comm, coeff_C_mul, mul_comm]`.

Use `⟨P.det, ?_, fun A hA => ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.map_det]`. Establish `h1 : (eval fun ij : Fin d × Fin n => A₀ ij.1 ij.2).mapMatrix P = 1`. Use extensionality with `m' m`. Rewrite using `[hP, Matrix.one_apply]`.

Simplify using `only [T, hah, coeff_monomial, Subtype.ext_iff, eq_comm]`. Rewrite using `[h1, Matrix.det_one]`. Conclude with `one_ne_zero`. Rewrite using `[RingHom.map_det] at hA set M := (eval fun ij : Fin d × Fin n => A ij.1 ij.2).mapMatrix P`. Establish `hMT : ∀ m' m : V, M m' m = coeff (m' : Fin n →₀ ℕ) (T A m)` using `hP A`.

Establish `hinv : M * M⁻¹ = 1` using `Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.2 hA)`. Establish `hI : ∀ m, T A m ∈ leadIdeal J ⊔ linIdeal A` using `fun m => Submodule.add_mem_sup (ha m) (Ideal.mem_span_range_iff_exists_fun.2 ⟨h m, rfl⟩)`. Establish `hhom` using `isHomogeneous_leadIdeal_sup_linIdeal J A`. Use `originIdeal_pow_le fun m hm => ?_` and prove the remaining obligations. Establish `key : monomial m (1 : ℂ) = ∑ m'' : V, C (M⁻¹ m'' ⟨m, (hV m).2 hm⟩) * homogeneousComponent N (T A m'')`.

Use extensionality with `s`. Simplify using `only [coeff_sum, coeff_C_mul, coeff_homogeneousComponent, coeff_monomial]`. Distinguish the cases in `hs : s.degree = N`. Establish `e` using `congr_fun (congr_fun hinv ⟨s, (hV s).2 hs⟩) ⟨m, (hV m).2 hm⟩`. Simplify using `only [Matrix.mul_apply, hMT, Matrix.one_apply, Subtype.ext_iff] at e`.

Simplify using `only [hs, if_true]`. Repeatedly rewrite using `[mul_comm (M⁻¹ _ _)]`. Rewrite using `[e]`. Distinguish the cases in `hsm : s = m`. Simplify using `[hsm]`.

Simplify using `[hsm, Ne.symm hsm]`. Simplify using `only [hs, if_false, mul_zero, Finset.sum_const_zero]`. Rewrite using `[if_neg]`. Introduce and unpack `rfl`. Conclude with `hs hm`.

Rewrite using `[key]`. Conclude with `Ideal.sum_mem _ fun m'' _ => Ideal.mul_mem_left _ _ (homogeneousComponent_mem_of_mem hhom (hI m'') N)`.
-/
theorem ConeAvoidsOpen.proof : ConeAvoidsOpen.Statement := by
  intro n d N J
  classical
  refine isZariskiOpen_of_local fun A₀ hA₀ => ?_
  set V := Finset.finsuppAntidiag (Finset.univ : Finset (Fin n)) N
  have hV : ∀ m : Fin n →₀ ℕ, m ∈ V ↔ m.degree = N := fun m => by
    simp [V, Finsupp.degree_eq_sum]
  have hrep : ∀ m : V, ∃ a ∈ leadIdeal J, ∃ h : Fin d → MvPolynomial (Fin n) ℂ,
      a + ∑ j, h j * linPoly A₀ j = monomial (m : Fin n →₀ ℕ) 1 := by
    intro m
    obtain ⟨a, ha, b, hb, hab⟩ :=
      Submodule.mem_sup.1 (hA₀ (monomial_mem_originIdeal_pow ((hV m).1 m.2)))
    obtain ⟨h, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hb
    exact ⟨a, ha, h, hab⟩
  choose a ha h hah using hrep
  let T : Matrix (Fin d) (Fin n) ℂ → V → MvPolynomial (Fin n) ℂ :=
    fun A m => a m + ∑ j, h m j * linPoly A j
  let P : Matrix V V (MvPolynomial (Fin d × Fin n) ℂ) := fun m' m =>
    C (coeff (m' : Fin n →₀ ℕ) (a m)) +
      ∑ j, ∑ k, C (coeff (m' : Fin n →₀ ℕ) (h m j * X k)) * X (j, k)
  have hP : ∀ (A : Matrix (Fin d) (Fin n) ℂ) (m' m : V),
      (eval fun ij : Fin d × Fin n => A ij.1 ij.2).mapMatrix P m' m =
        coeff (m' : Fin n →₀ ℕ) (T A m) := by
    intro A m' m
    show eval _ (P m' m) = _
    simp only [P, T, linPoly, map_add, map_sum, map_mul, eval_C, eval_X, coeff_add, coeff_sum,
      Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_left_comm, coeff_C_mul, mul_comm]
  refine ⟨P.det, ?_, fun A hA => ?_⟩
  · rw [RingHom.map_det]
    have h1 : (eval fun ij : Fin d × Fin n => A₀ ij.1 ij.2).mapMatrix P = 1 := by
      ext m' m
      rw [hP, Matrix.one_apply]
      simp only [T, hah, coeff_monomial, Subtype.ext_iff, eq_comm]
    rw [h1, Matrix.det_one]
    exact one_ne_zero
  · rw [RingHom.map_det] at hA
    set M := (eval fun ij : Fin d × Fin n => A ij.1 ij.2).mapMatrix P
    have hMT : ∀ m' m : V, M m' m = coeff (m' : Fin n →₀ ℕ) (T A m) := hP A
    have hinv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.2 hA)
    have hI : ∀ m, T A m ∈ leadIdeal J ⊔ linIdeal A := fun m =>
      Submodule.add_mem_sup (ha m) (Ideal.mem_span_range_iff_exists_fun.2 ⟨h m, rfl⟩)
    have hhom := isHomogeneous_leadIdeal_sup_linIdeal J A
    refine originIdeal_pow_le fun m hm => ?_
    have key : monomial m (1 : ℂ) =
        ∑ m'' : V, C (M⁻¹ m'' ⟨m, (hV m).2 hm⟩) * homogeneousComponent N (T A m'') := by
      ext s
      simp only [coeff_sum, coeff_C_mul, coeff_homogeneousComponent, coeff_monomial]
      by_cases hs : s.degree = N
      · have e := congr_fun (congr_fun hinv ⟨s, (hV s).2 hs⟩) ⟨m, (hV m).2 hm⟩
        simp only [Matrix.mul_apply, hMT, Matrix.one_apply, Subtype.ext_iff] at e
        simp only [hs, if_true]
        simp_rw [mul_comm (M⁻¹ _ _)]
        rw [e]
        by_cases hsm : s = m
        · simp [hsm]
        · simp [hsm, Ne.symm hsm]
      · simp only [hs, if_false, mul_zero, Finset.sum_const_zero]
        rw [if_neg]
        rintro rfl
        exact hs hm
    rw [key]
    exact Ideal.sum_mem _ fun m'' _ =>
      Ideal.mul_mem_left _ _ (homogeneousComponent_mem_of_mem hhom (hI m'') N)

end

end GroundTheory.Heights₂.Heights.ComplexSets
