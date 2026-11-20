import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QdetTopThreeOrders

open NumberField GlobalTheory.CuspRep Polynomial Finset

namespace GlobalTheory.CompanionTheory.CapelliTrace

/- English proof (translation)
Assume the negation of the conclusion as `hx`. Establish `hx' : x ∉ Subalgebra.toSubmodule S` using `hx`. Take `⟨f, hf1, hf2⟩` from `Submodule.exists_le_ker_of_notMem hx'`. Conclude with `hf1 (h f fun z hz => LinearMap.mem_ker.1 (hf2 hz))`.
-/
theorem mem_of_dual {A : Type} [Ring A] [Algebra ℂ A] (S : Subalgebra ℂ A) (x : A)
    (h : ∀ f : A →ₗ[ℂ] ℂ, (∀ z ∈ S, f z = 0) → f x = 0) : x ∈ S := by
  by_contra hx
  have hx' : x ∉ Subalgebra.toSubmodule S := hx
  obtain ⟨f, hf1, hf2⟩ := Submodule.exists_le_ker_of_notMem hx'
  exact hf1 (h f fun z hz => LinearMap.mem_ker.1 (hf2 hz))

/- English proof (translation)
Use `⟨?_, monic_prod_of_monic _ _ fun l _ => monic_X_sub_C _⟩` and prove the remaining obligations. Rewrite using `[natDegree_prod_of_monic _ _ fun l _ => monic_X_sub_C _, Finset.sum_congr rfl fun l _ => natDegree_X_sub_C _]`. Simplify using the standard rewrite rules.
-/
theorem prod_X_sub {n : ℕ} (s : Finset (Fin n)) :
    (∏ l ∈ s, (X - C ((l : ℕ) : ℂ))).natDegree = s.card ∧ (∏ l ∈ s, (X - C ((l : ℕ) : ℂ))).Monic := by
  refine ⟨?_, monic_prod_of_monic _ _ fun l _ => monic_X_sub_C _⟩
  rw [natDegree_prod_of_monic _ _ fun l _ => monic_X_sub_C _, Finset.sum_congr rfl fun l _ => natDegree_X_sub_C _]
  simp

/- English proof (translation)
Take `⟨Rm, hR⟩` from `GlobalTheory.qdet_top_three_orders A n M`. Use `mem_of_dual S _ fun f hf => ?_` and prove the remaining obligations. Establish `f1 : f 1 = 0` using `hf 1 S.one_mem`. Use `set Q : ℂ[X] := ∑ i, C (f (M i i)) * ∏ l ∈ univ.erase i, (X - C ((l : ℕ) : ℂ)) + ∑ i, ∑ j ∈ univ.filter (fun j => i < j), C (f (M i i * M j j - M j i * M i j)) * ∏ l ∈ (univ.erase i).erase j, (X - C ((l : ℕ) : ℂ)) + ∑ d ∈ range (n - 2), C (f (Rm d)) * X ^ d with hQ`. Establish `hQ0 : Q = 0` using `Polynomial.funext fun u => by`.

Establish `h1` using `hf _ (h u)`. Rewrite `h1` using `[hR u]`. Simplify using `only [map_add, map_sum, map_smul, smul_eq_mul, f1, mul_zero, zero_add] at h1`. Simplify using `only [hQ, eval_add, eval_finsetSum, eval_mul, eval_C, eval_prod, eval_sub, eval_X, eval_pow, eval_zero]`. Rewrite using `[← h1]`.

Use `congr 1`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _`. Conclude with `Finset.sum_congr rfl fun d _ => mul_comm _ _`.

Establish `hc` using `congrArg (fun p : ℂ[X] => p.coeff (n - 1)) hQ0`. Simplify using `only [hQ, coeff_add, finsetSum_coeff, coeff_C_mul, coeff_zero] at hc`. Establish `t1 : ∀ i : Fin n, (∏ l ∈ univ.erase i, (X - C ((l : ℕ) : ℂ))).coeff (n - 1) = 1` using `fun i => by`. Take `⟨hd, hm⟩` from `prod_X_sub (univ.erase i)`. Rewrite `hd` using `[card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]`.

Rewrite using `[← hd]`. Conclude with `hm.coeff_natDegree`. Establish `t2 : ∀ i : Fin n, ∀ j ∈ univ.filter (fun j => i < j), (∏ l ∈ (univ.erase i).erase j, (X - C ((l : ℕ) : ℂ))).coeff (n - 1) = 0` using `fun i j hj => by`. Establish `hij : i < j` using `(mem_filter.1 hj).2`. Establish `hj' : (j : ℕ) < n` using `j.2`.

Establish `hi' : (i : ℕ) < j` using `hij`. Take `⟨hd, -⟩` from `prod_X_sub ((univ.erase i).erase j)`. Rewrite `hd` using `[card_erase_of_mem (mem_erase.2 ⟨hij.ne', mem_univ _⟩), card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]`. Conclude with `coeff_eq_zero_of_natDegree_lt (by omega)`. Establish `t3 : ∀ d ∈ range (n - 2), ((X : ℂ[X]) ^ d).coeff (n - 1) = 0` using `fun d hd => by`.

Rewrite using `[coeff_X_pow, if_neg]`. Use `mem_range.1 hd` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `e3 : ∑ d ∈ range (n - 2), f (Rm d) * ((X : ℂ[X]) ^ d).coeff (n - 1) = 0` using `Finset.sum_eq_zero fun d hd => by rw [t3 d hd, mul_zero]`. Establish `e2 : ∑ i : Fin n, ∑ j ∈ univ.filter (fun j => i < j), f (M i i * M j j - M j i * M i j) * (∏ l ∈ (univ.erase i).erase j, (X - C ((l : ℕ) : ℂ))).coeff (n - 1) = 0` using `Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j hj => by rw [t2 i j hj, mul_zero]`.

Establish `e1 : ∑ i : Fin n, f (M i i) * (∏ l ∈ univ.erase i, (X - C ((l : ℕ) : ℂ))).coeff (n - 1) = ∑ i, f (M i i)` using `Finset.sum_congr rfl fun i _ => by rw [t1 i, mul_one]`. Rewrite `hc` using `[e1, e2, e3, add_zero, add_zero]`. Rewrite using `[map_sum]`. Conclude with `hc`.
-/
theorem trace_mem {A : Type} [Ring A] [Algebra ℂ A] (S : Subalgebra ℂ A) (n : ℕ) (M : Fin n → Fin n → A)
    (h : ∀ u : ℂ, Formalism.REAL.qdet M u ∈ S) : ∑ i, M i i ∈ S := by
  obtain ⟨Rm, hR⟩ := GlobalTheory.qdet_top_three_orders A n M
  refine mem_of_dual S _ fun f hf => ?_
  have f1 : f 1 = 0 := hf 1 S.one_mem
  set Q : ℂ[X] := ∑ i, C (f (M i i)) * ∏ l ∈ univ.erase i, (X - C ((l : ℕ) : ℂ)) +
    ∑ i, ∑ j ∈ univ.filter (fun j => i < j), C (f (M i i * M j j - M j i * M i j)) *
      ∏ l ∈ (univ.erase i).erase j, (X - C ((l : ℕ) : ℂ)) +
    ∑ d ∈ range (n - 2), C (f (Rm d)) * X ^ d with hQ
  have hQ0 : Q = 0 := Polynomial.funext fun u => by
    have h1 := hf _ (h u)
    rw [hR u] at h1
    simp only [map_add, map_sum, map_smul, smul_eq_mul, f1, mul_zero, zero_add] at h1
    simp only [hQ, eval_add, eval_finsetSum, eval_mul, eval_C, eval_prod, eval_sub, eval_X, eval_pow, eval_zero]
    rw [← h1]
    congr 1
    · congr 1
      · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _
    · exact Finset.sum_congr rfl fun d _ => mul_comm _ _
  have hc := congrArg (fun p : ℂ[X] => p.coeff (n - 1)) hQ0
  simp only [hQ, coeff_add, finsetSum_coeff, coeff_C_mul, coeff_zero] at hc
  have t1 : ∀ i : Fin n, (∏ l ∈ univ.erase i, (X - C ((l : ℕ) : ℂ))).coeff (n - 1) = 1 := fun i => by
    obtain ⟨hd, hm⟩ := prod_X_sub (univ.erase i)
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at hd
    rw [← hd]; exact hm.coeff_natDegree
  have t2 : ∀ i : Fin n, ∀ j ∈ univ.filter (fun j => i < j),
      (∏ l ∈ (univ.erase i).erase j, (X - C ((l : ℕ) : ℂ))).coeff (n - 1) = 0 := fun i j hj => by
    have hij : i < j := (mem_filter.1 hj).2
    have hj' : (j : ℕ) < n := j.2
    have hi' : (i : ℕ) < j := hij
    obtain ⟨hd, -⟩ := prod_X_sub ((univ.erase i).erase j)
    rw [card_erase_of_mem (mem_erase.2 ⟨hij.ne', mem_univ _⟩), card_erase_of_mem (mem_univ _), card_univ,
      Fintype.card_fin] at hd
    exact coeff_eq_zero_of_natDegree_lt (by omega)
  have t3 : ∀ d ∈ range (n - 2), ((X : ℂ[X]) ^ d).coeff (n - 1) = 0 := fun d hd => by
    rw [coeff_X_pow, if_neg]
    have := mem_range.1 hd
    omega
  have e3 : ∑ d ∈ range (n - 2), f (Rm d) * ((X : ℂ[X]) ^ d).coeff (n - 1) = 0 :=
    Finset.sum_eq_zero fun d hd => by rw [t3 d hd, mul_zero]
  have e2 : ∑ i : Fin n, ∑ j ∈ univ.filter (fun j => i < j), f (M i i * M j j - M j i * M i j) *
      (∏ l ∈ (univ.erase i).erase j, (X - C ((l : ℕ) : ℂ))).coeff (n - 1) = 0 :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j hj => by rw [t2 i j hj, mul_zero]
  have e1 : ∑ i : Fin n, f (M i i) * (∏ l ∈ univ.erase i, (X - C ((l : ℕ) : ℂ))).coeff (n - 1) = ∑ i, f (M i i) :=
    Finset.sum_congr rfl fun i _ => by rw [t1 i, mul_one]
  rw [e1, e2, e3, add_zero, add_zero] at hc
  rw [map_sum]
  exact hc

end GlobalTheory.CompanionTheory.CapelliTrace

namespace GlobalTheory.CompanionTheory.CapelliTrace

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

omit [NumberField E] [IsTotallyComplex E] in
open Classical in
/- English proof (translation)
Apply the tactic sequence `unfold atEmb; split_ifs <;> simp`.
-/
theorem atEmb_one (τ : E →+* ℂ) : atEmb τ 1 = Pi.single (InfinitePlace.mk τ) 1 := by
  unfold atEmb; split_ifs <;> simp

/- English proof (translation)
Establish `e : atEmb τ (-Complex.I) = -atEmb τ Complex.I` using `by rw [atEmb_eq]; simp`. Simplify using `only [Eop, atEmb_conj, map_one, Complex.conj_I, e, map_neg, smul_neg, sub_neg_eq_add]`. Use `module`.
-/
theorem Eop_add_conj (τ : E →+* ℂ) (i j : Fin a) :
    Eop τ i j + Eop (ComplexEmbedding.conjugate τ) i j = lieS E a i j (atEmb τ 1) := by
  have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by rw [atEmb_eq]; simp
  simp only [Eop, atEmb_conj, map_one, Complex.conj_I, e, map_neg, smul_neg, sub_neg_eq_add]
  module

/- English proof (translation)
Use function extensionality and compare the values at `w`. Simplify using `only [atEmb_one, Finset.sum_apply, Pi.single_apply]`. Rewrite using `[Finset.sum_boole]`. Establish `h` using `InfinitePlace.card_filter_mk_eq w`. Establish `h2 : InfinitePlace.mult w = 2`.

Simplify using `[InfinitePlace.mult, InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)]`. Establish `h3 : (Finset.univ.filter fun τ : E →+* ℂ => w = InfinitePlace.mk τ) = Finset.univ.filter fun τ : E →+* ℂ => InfinitePlace.mk τ = w`. Use extensionality with `τ`. Simplify using `[eq_comm]`. Rewrite using `[h3, h, h2]`.

Simplify using the standard rewrite rules.
-/
theorem sum_atEmb_one : ∑ τ : E →+* ℂ, atEmb τ 1 = (2 : Cinf E) := by
  classical
  funext w
  simp only [atEmb_one, Finset.sum_apply, Pi.single_apply]
  rw [Finset.sum_boole]
  have h := InfinitePlace.card_filter_mk_eq w
  have h2 : InfinitePlace.mult w = 2 := by
    simp [InfinitePlace.mult, InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)]
  have h3 : (Finset.univ.filter fun τ : E →+* ℂ => w = InfinitePlace.mk τ) =
      Finset.univ.filter fun τ : E →+* ℂ => InfinitePlace.mk τ = w := by
    ext τ; simp [eq_comm]
  rw [h3, h, h2]
  simp

end GlobalTheory.CompanionTheory.CapelliTrace

namespace GlobalTheory.CompanionTheory.CapelliTrace

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Use `set X := ∑ τ : E →+* ℂ, Eop τ i j`. Establish `hc : ∑ τ : E →+* ℂ, Eop (ComplexEmbedding.conjugate τ) i j = X` using `Equiv.sum_comp (Function.Involutive.toPerm _ (ComplexEmbedding.involutive_conjugate E)) fun τ => Eop τ i j`. Establish `h2 : (2 : ℂ) • X = (2 : ℂ) • lieS E a i j 1`. Rewrite using `[two_smul, two_smul]`. Use `nth_rewrite 2 [← hc]`.

Rewrite using `[← Finset.sum_add_distrib, Finset.sum_congr rfl fun τ _ => Eop_add_conj τ i j, ← map_sum, sum_atEmb_one, show (2 : Cinf E) = 1 + 1 from one_add_one_eq_two.symm, map_add]`. Conclude with `smul_right_injective _ two_ne_zero h2`.
-/
theorem sum_Eop (i j : Fin a) : ∑ τ : E →+* ℂ, Eop τ i j = lieS E a i j 1 := by
  set X := ∑ τ : E →+* ℂ, Eop τ i j
  have hc : ∑ τ : E →+* ℂ, Eop (ComplexEmbedding.conjugate τ) i j = X :=
    Equiv.sum_comp (Function.Involutive.toPerm _ (ComplexEmbedding.involutive_conjugate E)) fun τ => Eop τ i j
  have h2 : (2 : ℂ) • X = (2 : ℂ) • lieS E a i j 1 := by
    rw [two_smul, two_smul]
    nth_rewrite 2 [← hc]
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun τ _ => Eop_add_conj τ i j, ← map_sum, sum_atEmb_one,
      show (2 : Cinf E) = 1 + 1 from one_add_one_eq_two.symm, map_add]
  exact smul_right_injective _ two_ne_zero h2

/- English proof (translation)
Rewrite using `[Finset.sum_comm, Finset.sum_congr rfl fun i _ => sum_Eop i i]`. Establish `e : oneL E a = ∑ i : Fin a, toL (Matrix.single i i (1 : Cinf E))`. Use function extensionality and compare the values at `k l`. Express the relevant statement in the definitionally equal form `(1 : Matrix (Fin a) (Fin a) (Cinf E)) k l = (∑ i : Fin a, Matrix.single i i (1 : Cinf E)) k l`. Rewrite using `[Matrix.sum_apply]`.

Distinguish the cases in `h : k = l`. Substitute `h` using the available equality. Simplify using `[Matrix.single_apply]`. Rewrite using `[Matrix.one_apply_ne h]`. Conclude with `(Finset.sum_eq_zero fun c _ => by`.

Rewrite using `[Matrix.single_apply, if_neg fun hc => h (hc.1.symm.trans hc.2)]).symm`. Rewrite using `[e, map_sum]`. Both sides reduce to the same expression.
-/
theorem lie_oneL_eq : lie E a (oneL E a) = ∑ τ : E →+* ℂ, ∑ i, Eop τ i i := by
  rw [Finset.sum_comm, Finset.sum_congr rfl fun i _ => sum_Eop i i]
  have e : oneL E a = ∑ i : Fin a, toL (Matrix.single i i (1 : Cinf E)) := by
    funext k l
    change (1 : Matrix (Fin a) (Fin a) (Cinf E)) k l = (∑ i : Fin a, Matrix.single i i (1 : Cinf E)) k l
    rw [Matrix.sum_apply]
    by_cases h : k = l
    · subst h; simp [Matrix.single_apply]
    · rw [Matrix.one_apply_ne h]
      exact (Finset.sum_eq_zero fun c _ => by
        rw [Matrix.single_apply, if_neg fun hc => h (hc.1.symm.trans hc.2)]).symm
  rw [e, map_sum]
  rfl

/- English proof (translation)
Introduce `E _ _ _ a`. Rewrite using `[lie_oneL_eq]`. Use `Subalgebra.sum_mem _ fun τ _ => trace_mem (Zalg E a) a (Eop τ) fun u => ?_` and prove the remaining obligations. Establish `h : cap (a` using `a) τ (u - ((a : ℂ) - 1) / 2) ∈ Zalg E a := Algebra.subset_adjoin ⟨τ, _, rfl⟩`. Rewrite `h` using `[cap, sub_add_cancel]`. Then use the resulting hypothesis.
-/
theorem lie_oneL_mem_Zalg : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ),
    lie E a (oneL E a) ∈ Zalg E a := by
  intro E _ _ _ a
  rw [lie_oneL_eq]
  refine Subalgebra.sum_mem _ fun τ _ => trace_mem (Zalg E a) a (Eop τ) fun u => ?_
  have h : cap (a := a) τ (u - ((a : ℂ) - 1) / 2) ∈ Zalg E a := Algebra.subset_adjoin ⟨τ, _, rfl⟩
  rwa [cap, sub_add_cancel] at h

end GlobalTheory.CompanionTheory.CapelliTrace
