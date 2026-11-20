import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementKT
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.ComatrixEigen

open Formalism.REAL

/- English proof (translation)
Use `⟨∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : Polynomial A) * (List.ofFn fun k : Fin t => ((if a (σ k) = b k then Polynomial.X - Polynomial.C (algebraMap ℂ A (k : ℂ)) else 0) + Polynomial.C (E (a (σ k)) (b k)) : Polynomial A)).prod, fun u => ?_⟩` and prove the remaining obligations. Set `φ : Polynomial A →+* A` to `Polynomial.eval₂RingHom' (RingHom.id A) (algebraMap ℂ A u) (fun x => (Algebra.commutes u x).symm)`. Establish `hφ : ∀ p : Polynomial A, φ p = ∑ d ∈ p.support, u ^ d • p.coeff d`. Introduce `p`. Express the relevant statement in the definitionally equal form `Polynomial.eval₂ (RingHom.id A) (algebraMap ℂ A u) p = _`.

Rewrite using `[Polynomial.eval₂_eq_sum, Polynomial.sum_def]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[RingHom.id_apply, ← map_pow, Algebra.smul_def, Algebra.commutes]`. Establish `hX : φ Polynomial.X = algebraMap ℂ A u` using `Polynomial.eval₂_X _ _`. Establish `hC : ∀ x, φ (Polynomial.C x) = x` using `fun x => Polynomial.eval₂_C _ _`.

Rewrite using `[← hφ, map_sum, qminor]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_intCast, map_list_prod, List.map_ofFn]`. Use `congr 3`. Use function extensionality and compare the values at `k`.

Simplify using `only [Function.comp_apply, Tm, map_add, hC]`. Use `split_ifs`. Rewrite using `[map_sub, map_sub, hX, hC]`. Rewrite using `[map_zero]`.
-/
theorem qminor_exists_poly {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin t → Fin n) :
    ∃ p : Polynomial A, ∀ u : ℂ, qminor E a b u = ∑ d ∈ p.support, u ^ d • p.coeff d := by
  refine ⟨∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : Polynomial A) *
    (List.ofFn fun k : Fin t => ((if a (σ k) = b k then
      Polynomial.X - Polynomial.C (algebraMap ℂ A (k : ℂ)) else 0) + Polynomial.C (E (a (σ k)) (b k)) :
        Polynomial A)).prod, fun u => ?_⟩
  let φ : Polynomial A →+* A := Polynomial.eval₂RingHom' (RingHom.id A) (algebraMap ℂ A u)
    (fun x => (Algebra.commutes u x).symm)
  have hφ : ∀ p : Polynomial A, φ p = ∑ d ∈ p.support, u ^ d • p.coeff d := by
    intro p
    change Polynomial.eval₂ (RingHom.id A) (algebraMap ℂ A u) p = _
    rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [RingHom.id_apply, ← map_pow, Algebra.smul_def, Algebra.commutes]
  have hX : φ Polynomial.X = algebraMap ℂ A u := Polynomial.eval₂_X _ _
  have hC : ∀ x, φ (Polynomial.C x) = x := fun x => Polynomial.eval₂_C _ _
  rw [← hφ, map_sum, qminor]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  congr 3
  funext k
  simp only [Function.comp_apply, Tm, map_add, hC]
  split_ifs
  · rw [map_sub, map_sub, hX, hC]
  · rw [map_zero]

/- English proof (translation)
Take `⟨p, hp⟩` from `qminor_exists_poly E a b`. Simplify using `only [hp, LinearMap.sum_apply, LinearMap.smul_apply]`. Use `fun_prop`.
-/
theorem continuous_qminor_apply {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n t : ℕ}
    (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin t → Fin n) (v : M) :
    Continuous fun u : ℂ => qminor E a b u v := by
  obtain ⟨p, hp⟩ := qminor_exists_poly E a b
  simp only [hp, LinearMap.sum_apply, LinearMap.smul_apply]
  fun_prop

/- English proof (translation)
Establish `key : ∀ Y : ℂ, (Y + (mu t : ℂ)) • ∑ j : Fin (m + 1), ((-1 : ℂ) ^ (i.val + j.val)) • qminor E (Fin.succAbove j) (Fin.succAbove i) (Y + (m : ℂ) / 2) (x j) = (Y + (mu t : ℂ)) • (∏ r ∈ univ.erase t, (Y + (mu r : ℂ))) • x i`. Introduce `Y`. Establish `hT : ∀ j, ∑ l, Tm E (Y + (m : ℂ) / 2 - (m : ℂ)) j l (x l) = (Y + (mu t : ℂ)) • x j`. Introduce `j`. Establish `h1` using `congrFun hx j`.

Simplify using `only [splitCas, Pi.smul_apply] at h1`. Establish `h2 : ∀ l, Tm E (Y + (m : ℂ) / 2 - (m : ℂ)) j l (x l) = (if j = l then (Y + (m : ℂ) / 2 - (m : ℂ)) • x l else 0) + E j l (x l)`. Introduce `l`. Rewrite using `[Tm, LinearMap.add_apply]`. Use `split_ifs`.

Rewrite using `[Module.algebraMap_end_apply]`. Rewrite using `[LinearMap.zero_apply]`. Simplify using `only [h2, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Rewrite `h1` using `[neg_eq_iff_eq_neg]`. Rewrite using `[h1, ← neg_smul, ← add_smul]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hu : Y + (m : ℂ) / 2 = Y + (((m + 1 : ℕ) : ℂ) - 1) / 2` using `by push_cast; ring`. Establish `h3 : ∑ l, (if i = l then qdet E (Y + (m : ℂ) / 2) else 0) (x l) = (Y + (mu t : ℂ)) • (∏ r ∈ univ.erase t, (Y + (mu r : ℂ))) • x i`.

Rewrite using `[Finset.sum_eq_single i]`. Rewrite using `[if_pos rfl, hu, hq, smul_smul, Finset.mul_prod_erase _ (fun r => Y + (mu r : ℂ)) (Finset.mem_univ t)]`. Introduce `l _ hl`. Rewrite using `[if_neg (Ne.symm hl), LinearMap.zero_apply]`. Simplify using the standard rewrite rules.

Rewrite using `[← h3]`. Simplify using `only [← qComatrix (Module.End ℂ M) m E hE (Y + (m : ℂ) / 2) i, LinearMap.sum_apply]`. Rewrite using `[Finset.sum_comm, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [Module.End.mul_apply]`.

Rewrite using `[← map_sum, ← map_sum, hT, map_smul, map_smul, Module.End.intCast_apply, ← Int.cast_smul_eq_zsmul ℂ]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hc1 : Continuous fun Y : ℂ => ∑ j : Fin (m + 1), ((-1 : ℂ) ^ (i.val + j.val)) • qminor E (Fin.succAbove j) (Fin.succAbove i) (Y + (m : ℂ) / 2) (x j)`. Use `continuous_finset_sum _ fun j _ => Continuous.const_smul ?_ _` and prove the remaining obligations.

Conclude with `(continuous_qminor_apply E _ _ (x j)).comp (continuous_add_const _)`. Establish `hc2 : Continuous fun Y : ℂ => (∏ r ∈ univ.erase t, (Y + (mu r : ℂ))) • x i` using `by fun_prop`. Establish `hd : Dense ({-(mu t : ℂ)}ᶜ : Set ℂ)` using `dense_compl_singleton _`. Use `congrFun (Continuous.ext_on hd hc1 hc2 fun Z hZ => ?_) Y` and prove the remaining obligations. Establish `hne : Z + (mu t : ℂ) ≠ 0` using `fun h => hZ (eq_neg_of_add_eq_zero_left h)`.

Conclude with `smul_right_injective M hne (key Z)`.
-/
theorem cof_eigen {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {m : ℕ}
    (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ M) (mu : Fin (m + 1) → ℝ) (x : Fin (m + 1) → M)
    (hE : GlRel E)
    (hq : ∀ (Y : ℂ) (w : M), qdet E (Y + (((m + 1 : ℕ) : ℂ) - 1) / 2) w = (∏ s, (Y + (mu s : ℂ))) • w)
    (t : Fin (m + 1))
    (hx : splitCas E x = ((-mu t + (1 - ((m + 1 : ℕ) : ℝ)) / 2 : ℝ) : ℂ) • x) (i : Fin (m + 1)) (Y : ℂ) :
    ∑ j : Fin (m + 1), ((-1 : ℂ) ^ (i.val + j.val)) •
      qminor E (Fin.succAbove j) (Fin.succAbove i) (Y + (m : ℂ) / 2) (x j) =
      (∏ r ∈ univ.erase t, (Y + (mu r : ℂ))) • x i := by
  have key : ∀ Y : ℂ, (Y + (mu t : ℂ)) • ∑ j : Fin (m + 1), ((-1 : ℂ) ^ (i.val + j.val)) •
      qminor E (Fin.succAbove j) (Fin.succAbove i) (Y + (m : ℂ) / 2) (x j) =
      (Y + (mu t : ℂ)) • (∏ r ∈ univ.erase t, (Y + (mu r : ℂ))) • x i := by
    intro Y
    have hT : ∀ j, ∑ l, Tm E (Y + (m : ℂ) / 2 - (m : ℂ)) j l (x l) = (Y + (mu t : ℂ)) • x j := by
      intro j
      have h1 := congrFun hx j
      simp only [splitCas, Pi.smul_apply] at h1
      have h2 : ∀ l, Tm E (Y + (m : ℂ) / 2 - (m : ℂ)) j l (x l) =
          (if j = l then (Y + (m : ℂ) / 2 - (m : ℂ)) • x l else 0) + E j l (x l) := by
        intro l
        rw [Tm, LinearMap.add_apply]
        split_ifs
        · rw [Module.algebraMap_end_apply]
        · rw [LinearMap.zero_apply]
      simp only [h2, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [neg_eq_iff_eq_neg] at h1
      rw [h1, ← neg_smul, ← add_smul]
      congr 1
      push_cast
      ring
    have hu : Y + (m : ℂ) / 2 = Y + (((m + 1 : ℕ) : ℂ) - 1) / 2 := by push_cast; ring
    have h3 : ∑ l, (if i = l then qdet E (Y + (m : ℂ) / 2) else 0) (x l) =
        (Y + (mu t : ℂ)) • (∏ r ∈ univ.erase t, (Y + (mu r : ℂ))) • x i := by
      rw [Finset.sum_eq_single i]
      · rw [if_pos rfl, hu, hq, smul_smul, Finset.mul_prod_erase _ (fun r => Y + (mu r : ℂ)) (Finset.mem_univ t)]
      · intro l _ hl
        rw [if_neg (Ne.symm hl), LinearMap.zero_apply]
      · simp
    rw [← h3]
    simp only [← qComatrix (Module.End ℂ M) m E hE (Y + (m : ℂ) / 2) i, LinearMap.sum_apply]
    rw [Finset.sum_comm, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Module.End.mul_apply]
    rw [← map_sum, ← map_sum, hT, map_smul, map_smul, Module.End.intCast_apply,
      ← Int.cast_smul_eq_zsmul ℂ]
    push_cast
    rfl
  have hc1 : Continuous fun Y : ℂ => ∑ j : Fin (m + 1), ((-1 : ℂ) ^ (i.val + j.val)) •
      qminor E (Fin.succAbove j) (Fin.succAbove i) (Y + (m : ℂ) / 2) (x j) := by
    refine continuous_finset_sum _ fun j _ => Continuous.const_smul ?_ _
    exact (continuous_qminor_apply E _ _ (x j)).comp (continuous_add_const _)
  have hc2 : Continuous fun Y : ℂ => (∏ r ∈ univ.erase t, (Y + (mu r : ℂ))) • x i := by fun_prop
  have hd : Dense ({-(mu t : ℂ)}ᶜ : Set ℂ) := dense_compl_singleton _
  refine congrFun (Continuous.ext_on hd hc1 hc2 fun Z hZ => ?_) Y
  have hne : Z + (mu t : ℂ) ≠ 0 := fun h => hZ (eq_neg_of_add_eq_zero_left h)
  exact smul_right_injective M hne (key Z)

end GlobalTheory.ComatrixEigen

namespace GlobalTheory

/- English proof (translation)
Introduce `M _ _ m E mu y hE hq hy s i`. Simplify using `only [map_sum, Finset.smul_sum]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [fun t => ComatrixEigen.cof_eigen E mu (y t) hE hq t (hy t) i (-(mu s : ℂ))]`. Rewrite using `[Finset.sum_eq_single s]`.

Simplify using `only [neg_add_eq_sub]`. Introduce `t _ ht`. Rewrite using `[Finset.prod_eq_zero (i := s) (Finset.mem_erase.2 ⟨Ne.symm ht, Finset.mem_univ _⟩) (neg_add_cancel _), zero_smul]`. Simplify using the standard rewrite rules.
-/
theorem comatrix_picks_eigencomponent : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ M) (mu : Fin (m + 1) → ℝ) (y : Fin (m + 1) → Fin (m + 1) → M), Formalism.REAL.GlRel E → (∀ (Y : ℂ) (w : M), Formalism.REAL.qdet E (Y + (((m + 1 : ℕ) : ℂ) - 1) / 2) w = (∏ s, (Y + (mu s : ℂ))) • w) → (∀ t, splitCas E (y t) = ((-mu t + (1 - ((m + 1 : ℕ) : ℝ)) / 2 : ℝ) : ℂ) • y t) → ∀ s i, ∑ j : Fin (m + 1), ((-1 : ℂ) ^ (i.val + j.val)) • Formalism.REAL.qminor E (Fin.succAbove j) (Fin.succAbove i) (-(mu s : ℂ) + (m : ℂ) / 2) (∑ t, y t j) = (∏ t ∈ univ.erase s, ((mu t : ℂ) - mu s)) • y s i := by
  intro M _ _ m E mu y hE hq hy s i
  simp only [map_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  simp only [fun t => ComatrixEigen.cof_eigen E mu (y t) hE hq t (hy t) i (-(mu s : ℂ))]
  rw [Finset.sum_eq_single s]
  · simp only [neg_add_eq_sub]
  · intro t _ ht
    rw [Finset.prod_eq_zero (i := s) (Finset.mem_erase.2 ⟨Ne.symm ht, Finset.mem_univ _⟩) (neg_add_cancel _),
      zero_smul]
  · simp

end GlobalTheory
