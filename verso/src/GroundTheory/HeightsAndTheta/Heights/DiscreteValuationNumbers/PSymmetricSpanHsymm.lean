import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import GroundTheory.HeightsAndTheta.Theta.Capelli.CompleteHomogeneous
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial Finset

namespace SymmetricSpanHsymm

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/- English proof (translation)
Apply `map_injective (Int.castRingHom ℂ) Int.cast_injective` to reduce the goal to its premises. Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `x`. Simplify using `only [map_sum, map_mul, map_pow, map_neg, map_one, map_esymm, map_hsymm, map_zero]`. Rewrite using `[GroundTheory.Heights₂.Theta.SymmFun.sum_esymm_mul_hsymm x k, if_neg hk]`.
-/
theorem sum_esymm_mul_hsymm_int {k : ℕ} (hk : k ≠ 0) :
    ∑ s ∈ range (k + 1), (-1) ^ s * esymm σ ℤ s * hsymm σ ℤ (k - s) = 0 := by
  apply map_injective (Int.castRingHom ℂ) Int.cast_injective
  apply MvPolynomial.funext
  intro x
  simp only [map_sum, map_mul, map_pow, map_neg, map_one, map_esymm, map_hsymm, map_zero]
  rw [GroundTheory.Heights₂.Theta.SymmFun.sum_esymm_mul_hsymm x k, if_neg hk]

/- English proof (translation)
Proceed by induction on `k using Nat.strong_induction_on with`. Consider the case `_ k ih`. Use `set A := Algebra.adjoin ℤ (Set.range (hsymm σ ℤ))`. Break down `Nat.eq_zero_or_pos k with rfl | hk` into its components or cases. Rewrite using `[esymm_zero]`.

Conclude with `one_mem A`. Establish `h` using `sum_esymm_mul_hsymm_int (σ := σ) hk.ne'`. Rewrite `h` using `[sum_range_succ, Nat.sub_self, hsymm_zero, mul_one]`. Establish `h2 : ((-1 : MvPolynomial σ ℤ) ^ k) * (-1) ^ k = 1`. Rewrite using `[← mul_pow]`.

Evaluate the numerical expressions. Establish `he : esymm σ ℤ k = -((-1) ^ k * ∑ s ∈ range k, (-1) ^ s * esymm σ ℤ s * hsymm σ ℤ (k - s))`. Take the linear combination `(-1 : MvPolynomial σ ℤ) ^ k * h - esymm σ ℤ k * h2`. Establish `hm1 : ∀ j : ℕ, (-1 : MvPolynomial σ ℤ) ^ j ∈ A` using `fun j => pow_mem (neg_mem (one_mem A)) j`. Rewrite using `[he]`.

Use `neg_mem (mul_mem (hm1 k) (sum_mem fun s hs => mul_mem (mul_mem (hm1 s) (ih s (mem_range.mp hs))) (Algebra.subset_adjoin ⟨k - s, rfl⟩)))` and prove the remaining obligations.
-/
theorem esymm_mem_adjoin (k : ℕ) :
    esymm σ ℤ k ∈ Algebra.adjoin ℤ (Set.range (hsymm σ ℤ)) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  set A := Algebra.adjoin ℤ (Set.range (hsymm σ ℤ))
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [esymm_zero]; exact one_mem A
  have h := sum_esymm_mul_hsymm_int (σ := σ) hk.ne'
  rw [sum_range_succ, Nat.sub_self, hsymm_zero, mul_one] at h
  have h2 : ((-1 : MvPolynomial σ ℤ) ^ k) * (-1) ^ k = 1 := by
    rw [← mul_pow]; norm_num
  have he : esymm σ ℤ k =
      -((-1) ^ k * ∑ s ∈ range k, (-1) ^ s * esymm σ ℤ s * hsymm σ ℤ (k - s)) := by
    linear_combination (-1 : MvPolynomial σ ℤ) ^ k * h - esymm σ ℤ k * h2
  have hm1 : ∀ j : ℕ, (-1 : MvPolynomial σ ℤ) ^ j ∈ A := fun j => pow_mem (neg_mem (one_mem A)) j
  rw [he]
  refine neg_mem (mul_mem (hm1 k) (sum_mem fun s hs => mul_mem (mul_mem (hm1 s)
    (ih s (mem_range.mp hs))) (Algebra.subset_adjoin ⟨k - s, rfl⟩)))

omit [Fintype σ] [DecidableEq σ] in

/- English proof (translation)
Proceed by induction on `t using Multiset.induction_on with`. Consider the case `empty => simpa using isHomogeneous_one σ ℤ`. Consider the case `cons a t ih`. Rewrite using `[Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, add_comm]`. Conclude with `(isHomogeneous_X ℤ a).mul ih`.
-/
theorem isHomogeneous_prod_map_X (t : Multiset σ) :
    ((t.map (X : σ → MvPolynomial σ ℤ)).prod).IsHomogeneous (Multiset.card t) := by
  induction t using Multiset.induction_on with
  | empty => simpa using isHomogeneous_one σ ℤ
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, add_comm]
    exact (isHomogeneous_X ℤ a).mul ih

/- English proof (translation)
Unfold `hsymm`. Use `IsHomogeneous.sum _ _ _ fun s _ => ?_` and prove the remaining obligations. Use `isHomogeneous_prod_map_X (σ := σ) s.1` as an intermediate fact. Rewrite `this` using `[s.2]`. Then use the resulting hypothesis.
-/
theorem isHomogeneous_hsymm_int (a : ℕ) : (hsymm σ ℤ a).IsHomogeneous a := by
  unfold hsymm
  refine IsHomogeneous.sum _ _ _ fun s _ => ?_
  have := isHomogeneous_prod_map_X (σ := σ) s.1
  rwa [s.2] at this

/- English proof (translation)
Proceed by induction on `t using Multiset.induction_on with`. Consider the case `empty => simpa using isHomogeneous_one σ ℤ`. Consider the case `cons a t ih`. Rewrite using `[Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]`. Conclude with `(isHomogeneous_hsymm_int a).mul ih`.
-/
theorem isHomogeneous_prod_map_hsymm (t : Multiset ℕ) :
    ((t.map (hsymm σ ℤ)).prod).IsHomogeneous t.sum := by
  induction t using Multiset.induction_on with
  | empty => simpa using isHomogeneous_one σ ℤ
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    exact (isHomogeneous_hsymm_int a).mul ih

/- English proof (translation)
Use `isHomogeneous_prod_map_hsymm (σ := σ) μ.parts` as an intermediate fact. Rewrite `this` using `[μ.parts_sum]`. Then use the resulting hypothesis.
-/
theorem isHomogeneous_hsymmPart {n : ℕ} (μ : n.Partition) : (hsymmPart σ ℤ μ).IsHomogeneous n := by
  have := isHomogeneous_prod_map_hsymm (σ := σ) μ.parts
  rwa [μ.parts_sum] at this

/- English proof (translation)
Proceed by induction on `hx using Submonoid.closure_induction with`. Consider the case `mem y hy`. Take `⟨a, rfl⟩` from `hy`. Conclude with `⟨a, .indiscrete a, (hsymmPart_indiscrete σ ℤ a).symm⟩`. Consider the case `one => exact ⟨0, .indiscrete 0, (hsymmPart_zero σ ℤ).symm⟩`.

Consider the case `mul y z _ _ hy hz`. Take `⟨n, μ, rfl⟩` from `hy`. Take `⟨n', ν, rfl⟩` from `hz`. Use `⟨n + n', ⟨μ.parts + ν.parts, fun {i} hi => ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Break down `Multiset.mem_add.mp hi with h | h exacts [μ.parts_pos h, ν.parts_pos h]` into its components or cases.

Rewrite using `[Multiset.sum_add, μ.parts_sum, ν.parts_sum]`. Simplify using `only [hsymmPart, Multiset.map_add, Multiset.prod_add]`.
-/
theorem exists_hsymmPart_of_mem_closure {x : MvPolynomial σ ℤ}
    (hx : x ∈ Submonoid.closure (Set.range (hsymm σ ℤ))) :
    ∃ (n : ℕ) (μ : n.Partition), x = hsymmPart σ ℤ μ := by
  induction hx using Submonoid.closure_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    exact ⟨a, .indiscrete a, (hsymmPart_indiscrete σ ℤ a).symm⟩
  | one => exact ⟨0, .indiscrete 0, (hsymmPart_zero σ ℤ).symm⟩
  | mul y z _ _ hy hz =>
    obtain ⟨n, μ, rfl⟩ := hy
    obtain ⟨n', ν, rfl⟩ := hz
    refine ⟨n + n', ⟨μ.parts + ν.parts, fun {i} hi => ?_, ?_⟩, ?_⟩
    · rcases Multiset.mem_add.mp hi with h | h
      exacts [μ.parts_pos h, ν.parts_pos h]
    · rw [Multiset.sum_add, μ.parts_sum, ν.parts_sum]
    · simp only [hsymmPart, Multiset.map_add, Multiset.prod_add]

/- English proof (translation)
Introduce `N m G hG hsym`. Use `set S := Submodule.span ℤ (Set.range fun μ : m.Partition => hsymmPart (Fin N) ℤ μ)`. Establish `hA : G ∈ Algebra.adjoin ℤ (Set.range (hsymm (Fin N) ℤ))`. Take `⟨p, hp⟩` from `esymmAlgHom_fin_surjective ℤ (le_refl N) ⟨G, hsym⟩`. Establish `hG' : G = aeval (fun i : Fin N => esymm (Fin N) ℤ (i + 1)) p`.

Rewrite using `[← esymmAlgHom_apply, hp]`. Rewrite using `[hG']`. Use `clear hp hG'`. Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C r => rw [aeval_C]`.

Conclude with `Subalgebra.algebraMap_mem _ r`. Consider the case `add p q hp hq => rw [map_add]`. Conclude with `add_mem hp hq`. Consider the case `mul_X p i hp => rw [map_mul, aeval_X]`. Conclude with `mul_mem hp (esymm_mem_adjoin _)`.

Establish `hspan : G ∈ Submodule.span ℤ (Submonoid.closure (Set.range (hsymm (Fin N) ℤ)) : Set (MvPolynomial (Fin N) ℤ))`. Rewrite using `[← Algebra.adjoin_eq_span, Subalgebra.mem_toSubmodule]`. Conclude with `hA`. Establish `hle : Submodule.span ℤ (Submonoid.closure (Set.range (hsymm (Fin N) ℤ)) : Set (MvPolynomial (Fin N) ℤ)) ≤ S.comap (homogeneousComponent m)`. Rewrite using `[Submodule.span_le]`.

Introduce `x hx`. Take `⟨n, μ, rfl⟩` from `exists_hsymmPart_of_mem_closure hx`. Use `show homogeneousComponent m (hsymmPart (Fin N) ℤ μ) ∈ S`. Rewrite using `[homogeneousComponent_of_mem (isHomogeneous_hsymmPart μ)]`. Use `split_ifs with h`.

Substitute `h` using the available equality. Conclude with `Submodule.subset_span ⟨μ, rfl⟩`. Conclude with `zero_mem S`. Use `hle hspan` as an intermediate fact. Rewrite `this` using `[Submodule.mem_comap, homogeneousComponent_eq_self hG]`. Then use the resulting hypothesis.
-/
theorem proof : SymmetricSpanHsymm.Statement := by
  intro N m G hG hsym
  set S := Submodule.span ℤ (Set.range fun μ : m.Partition => hsymmPart (Fin N) ℤ μ)
  have hA : G ∈ Algebra.adjoin ℤ (Set.range (hsymm (Fin N) ℤ)) := by
    obtain ⟨p, hp⟩ := esymmAlgHom_fin_surjective ℤ (le_refl N) ⟨G, hsym⟩
    have hG' : G = aeval (fun i : Fin N => esymm (Fin N) ℤ (i + 1)) p := by
      rw [← esymmAlgHom_apply, hp]
    rw [hG']
    clear hp hG'
    induction p using MvPolynomial.induction_on with
    | C r => rw [aeval_C]; exact Subalgebra.algebraMap_mem _ r
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp => rw [map_mul, aeval_X]; exact mul_mem hp (esymm_mem_adjoin _)
  have hspan : G ∈ Submodule.span ℤ
      (Submonoid.closure (Set.range (hsymm (Fin N) ℤ)) : Set (MvPolynomial (Fin N) ℤ)) := by
    rw [← Algebra.adjoin_eq_span, Subalgebra.mem_toSubmodule]
    exact hA
  have hle : Submodule.span ℤ
      (Submonoid.closure (Set.range (hsymm (Fin N) ℤ)) : Set (MvPolynomial (Fin N) ℤ)) ≤
      S.comap (homogeneousComponent m) := by
    rw [Submodule.span_le]
    intro x hx
    obtain ⟨n, μ, rfl⟩ := exists_hsymmPart_of_mem_closure hx
    show homogeneousComponent m (hsymmPart (Fin N) ℤ μ) ∈ S
    rw [homogeneousComponent_of_mem (isHomogeneous_hsymmPart μ)]
    split_ifs with h
    · subst h; exact Submodule.subset_span ⟨μ, rfl⟩
    · exact zero_mem S
  have := hle hspan
  rwa [Submodule.mem_comap, homogeneousComponent_eq_self hG] at this

end SymmetricSpanHsymm

end GroundTheory.Heights₂.Heights.NumbersDVR
