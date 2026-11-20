import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VecMulVecComm

noncomputable section

open MvPolynomial TensorProduct

namespace GlobalTheory.GrassModel.TopRead

variable {n : ℕ}

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp [Algebra.TensorProduct.one_def]`. Consider the case `succ m ih`. Rewrite using `[List.ofFn_succ, List.prod_cons, ih (fun j => x j.succ)]`. Simplify using `only [List.ofFn_succ, List.prod_cons, gen, Algebra.TensorProduct.tmul_mul_tmul]`.
-/
theorem list_prod_gen {m : ℕ} (x : Fin m → Fin n × Fin n) :
    (List.ofFn fun j => gen n (x j)).prod =
      (List.ofFn fun j => vec n (x j).1).prod ⊗ₜ (List.ofFn fun j => vec n (x j).2).prod := by
  induction m with
  | zero => simp [Algebra.TensorProduct.one_def]
  | succ m ih =>
    rw [List.ofFn_succ, List.prod_cons, ih (fun j => x j.succ)]
    simp only [List.ofFn_succ, List.prod_cons, gen, Algebra.TensorProduct.tmul_mul_tmul]

/- English proof (translation)
Establish `h1 : ((toEven n (∏ j, X (x j)) : EvenPart n) : Big n) = (List.ofFn fun j => gen n (x j)).prod`. Rewrite using `[map_prod, ← List.prod_ofFn, ← Subalgebra.coe_val, map_list_prod, List.map_ofFn]`. Use `congr 1`. Conclude with `congrArg List.ofFn (funext fun j => by simp [toEven, aeval_X])`. Rewrite using `[h1, list_prod_gen, topBig_tmul]`.

Simplify using `only [topExt, vec]`. Rewrite using `[← ExteriorAlgebra.ιMulti_apply, ← ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.liftAlternating_apply_ιMulti, ExteriorAlgebra.liftAlternating_apply_ιMulti]`.
-/
theorem topBig_toEven_prod {m : ℕ} (x : Fin m → Fin n × Fin n) :
    topBig n ((toEven n (∏ j, X (x j)) : EvenPart n) : Big n) =
      topForm n m (fun j => Pi.single (x j).1 1) * topForm n m (fun j => Pi.single (x j).2 1) := by
  have h1 : ((toEven n (∏ j, X (x j)) : EvenPart n) : Big n) = (List.ofFn fun j => gen n (x j)).prod := by
    rw [map_prod, ← List.prod_ofFn, ← Subalgebra.coe_val, map_list_prod, List.map_ofFn]
    congr 1
    exact congrArg List.ofFn (funext fun j => by simp [toEven, aeval_X])
  rw [h1, list_prod_gen, topBig_tmul]
  simp only [topExt, vec]
  rw [← ExteriorAlgebra.ιMulti_apply, ← ExteriorAlgebra.ιMulti_apply,
    ExteriorAlgebra.liftAlternating_apply_ιMulti, ExteriorAlgebra.liftAlternating_apply_ιMulti]

/- English proof (translation)
Rewrite using `[map_sum, Finset.sum_eq_multiset_sum]`. Simplify using `only [Finsupp.toMultiset_single, one_nsmul]`. Establish `: (fun j => ({x j} : Multiset α)) = (fun a => ({a} : Multiset α)) ∘ x` using `rfl`. Rewrite using `[this, ← Multiset.map_map, Multiset.sum_map_singleton]`.
-/
theorem toMultiset_sum_single {α : Type*} [DecidableEq α] {m : ℕ} (x : Fin m → α) :
    Finsupp.toMultiset (∑ j, Finsupp.single (x j) 1) = Finset.univ.val.map x := by
  rw [map_sum, Finset.sum_eq_multiset_sum]
  simp only [Finsupp.toMultiset_single, one_nsmul]
  have : (fun j => ({x j} : Multiset α)) = (fun a => ({a} : Multiset α)) ∘ x := rfl
  rw [this, ← Multiset.map_map, Multiset.sum_map_singleton]

/- English proof (translation)
Introduce `f g h` and use `by rw [← Finsupp.toMultiset_toFinsupp f, h, Finsupp.toMultiset_toFinsupp]`.
-/
theorem toMultiset_injective' {α : Type*} [DecidableEq α] :
    Function.Injective (Finsupp.toMultiset : (α →₀ ℕ) → Multiset α) := fun f g h => by
  rw [← Finsupp.toMultiset_toFinsupp f, h, Finsupp.toMultiset_toFinsupp]

/- English proof (translation)
Establish `e : (∏ j, X (x j) : MvPolynomial (Fin n × Fin n) ℂ) = monomial (∑ j, Finsupp.single (x j) 1) 1` using `(monomial_sum_one _ _).symm`. Rewrite using `[e, coeff_monomial, ← toMultiset_sum_single]`. Simplify using `only [toMultiset_injective'.eq_iff]`.
-/
theorem coeff_prod_X {m : ℕ} (x : Fin m → Fin n × Fin n) (d : Fin n × Fin n →₀ ℕ) :
    coeff d (∏ j, X (x j) : MvPolynomial (Fin n × Fin n) ℂ) =
      if Finset.univ.val.map x = Finsupp.toMultiset d then 1 else 0 := by
  classical
  have e : (∏ j, X (x j) : MvPolynomial (Fin n × Fin n) ℂ) = monomial (∑ j, Finsupp.single (x j) 1) 1 :=
    (monomial_sum_one _ _).symm
  rw [e, coeff_monomial, ← toMultiset_sum_single]
  simp only [toMultiset_injective'.eq_iff]

/- English proof (translation)
Simplify using `[topForm]`.
-/
theorem topForm_self (v : Fin n → Fin n → ℂ) : topForm n n v = (Pi.basisFun ℂ (Fin n)).det v := by
  simp [topForm]

/- English proof (translation)
Establish `: (fun j => (Pi.single (π j) 1 : Fin n → ℂ)) = (Pi.basisFun ℂ (Fin n)) ∘ π`. Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules. Rewrite using `[this, AlternatingMap.map_perm, Module.Basis.det_self, Units.smul_def, zsmul_eq_mul, mul_one]`.
-/
theorem det_single_perm (π : Equiv.Perm (Fin n)) :
    (Pi.basisFun ℂ (Fin n)).det (fun j => Pi.single (π j) 1) = ((Equiv.Perm.sign π : ℤ) : ℂ) := by
  have : (fun j => (Pi.single (π j) 1 : Fin n → ℂ)) = (Pi.basisFun ℂ (Fin n)) ∘ π := by
    funext j; simp
  rw [this, AlternatingMap.map_perm, Module.Basis.det_self, Units.smul_def, zsmul_eq_mul, mul_one]

/- English proof (translation)
Use `AlternatingMap.map_eq_zero_of_not_injective _ _ fun h => ha fun i j hij => h ?_` and prove the remaining obligations. Simplify using `[hij]`.
-/
theorem det_single_not_inj (a : Fin n → Fin n) (ha : ¬ Function.Injective a) :
    (Pi.basisFun ℂ (Fin n)).det (fun j => Pi.single (a j) 1) = 0 := by
  refine AlternatingMap.map_eq_zero_of_not_injective _ _ fun h => ha fun i j hij => h ?_
  simp [hij]

open Classical in

/- English proof (translation)
Unfold `GlobalTheory.GoodMetric.topCoeff`. Repeatedly rewrite using `[coeff_prod_X, toMultiset_sum_single]`. Distinguish the cases in `hm : m = n`. Use `swap`. Establish `h0 : topForm n m = 0` using `by simp [topForm, hm]`.

Rewrite using `[h0]`. Simplify using `only [AlternatingMap.zero_apply, mul_zero]`. Use `Finset.sum_eq_zero fun w _ => ?_` and prove the remaining obligations. Rewrite using `[if_neg, mul_zero]`. Introduce `heq`.

Use `congrArg Multiset.card heq` as an intermediate fact. Simplify using `at this`. Conclude with `hm this`. Substitute `hm` using the available equality. Rewrite using `[topForm_self, topForm_self]`.

Use `set a : Fin m → Fin m := fun j => (x j).1 with ha_def`. Use `set b : Fin m → Fin m := fun j => (x j).2 with hb_def`. Establish `hcond : ∀ w : Equiv.Perm (Fin m), Finset.univ.val.map x = Finset.univ.val.map (fun c => (c, w c)) → Function.Injective a ∧ Function.Injective b`. Introduce `w heq`. Establish `h1` using `congrArg (Multiset.map Prod.fst) heq`.

Establish `h2` using `congrArg (Multiset.map Prod.snd) heq`. Simplify using `only [Multiset.map_map] at h1 h2`. Establish `e1 : Multiset.map (Prod.fst ∘ fun c => (c, w c)) Finset.univ.val = Finset.univ.val`. Simplify using the standard rewrite rules. Establish `e2 : Multiset.map (Prod.snd ∘ fun c => (c, w c)) Finset.univ.val = Finset.univ.val`.

Simplify using `using Multiset.map_univ_val_equiv w`. Rewrite `h1` using `[e1]`. Rewrite `h2` using `[e2]`. Prove the components needed by the constructor for the conclusion. Establish `hn : (Multiset.map (Prod.fst ∘ x) Finset.univ.val).Nodup` using `by rw [h1]; exact Finset.univ.nodup`.

Conclude with `fun i j hij => (Multiset.nodup_map_iff_inj_on Finset.univ.nodup).mp hn i (by simp) j (by simp) hij`. Establish `hn : (Multiset.map (Prod.snd ∘ x) Finset.univ.val).Nodup` using `by rw [h2]; exact Finset.univ.nodup`. Conclude with `fun i j hij => (Multiset.nodup_map_iff_inj_on Finset.univ.nodup).mp hn i (by simp) j (by simp) hij`. Distinguish the cases in `hab : Function.Injective a ∧ Function.Injective b`. Use `swap`.

Establish `: (Pi.basisFun ℂ (Fin m)).det (fun j => Pi.single (x j).1 1) * (Pi.basisFun ℂ (Fin m)).det (fun j => Pi.single (x j).2 1) = 0`. Break down `not_and_or.mp hab with h | h` into its components or cases. Rewrite using `[det_single_not_inj a h, zero_mul]`. Rewrite using `[det_single_not_inj b h, mul_zero]`. Rewrite using `[this]`.

Use `Finset.sum_eq_zero fun w _ => ?_` and prove the remaining obligations. Rewrite using `[if_neg, mul_zero]`. Conclude with `fun heq => hab (hcond w heq)`. Take `⟨ha, hb⟩` from `hab`. Set `π : Equiv.Perm (Fin m)` to `Equiv.ofBijective a (Finite.injective_iff_bijective.mp ha)`.

Set `τ : Equiv.Perm (Fin m)` to `Equiv.ofBijective b (Finite.injective_iff_bijective.mp hb)`. Establish `hπ : ∀ j, (x j).1 = π j` using `fun j => rfl`. Establish `hτ : ∀ j, (x j).2 = τ j` using `fun j => rfl`. Repeatedly rewrite using `[hπ, hτ, det_single_perm]`. Establish `hx : x = (fun c => (c, (τ * π⁻¹) c)) ∘ π`.

Use function extensionality and compare the values at `j`. Simplify using `[Prod.ext_iff, hπ, hτ]`. Establish `hmap : Finset.univ.val.map x = Finset.univ.val.map (fun c => (c, (τ * π⁻¹) c))`. Rewrite using `[hx, ← Multiset.map_map, Multiset.map_univ_val_equiv]`. Rewrite using `[Finset.sum_eq_single (τ * π⁻¹)]`.

Rewrite using `[if_pos hmap, mul_one, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce `w _ hw`. Rewrite using `[if_neg, mul_zero]`.

Introduce `heq`. Apply `hw` to reduce the goal to its premises. Use extensionality with `c`. Establish `hc : (c, w c) ∈ Finset.univ.val.map (fun c => (c, (τ * π⁻¹) c))`. Rewrite using `[← hmap, heq]`.

Simplify using the standard rewrite rules. Take `⟨c', _, hc'⟩` from `Multiset.mem_map.mp hc`. Simplify using `only [Prod.mk.injEq] at hc'`. Take `⟨rfl, h⟩` from `hc'`. Conclude with `congrArg Fin.val h.symm`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem topCoeff_prod {m : ℕ} (x : Fin m → Fin n × Fin n) :
    GlobalTheory.GoodMetric.topCoeff (∏ j, X (x j) : MvPolynomial (Fin n × Fin n) ℂ) =
      topForm n m (fun j => Pi.single (x j).1 1) * topForm n m (fun j => Pi.single (x j).2 1) := by
  unfold GlobalTheory.GoodMetric.topCoeff
  simp_rw [coeff_prod_X, toMultiset_sum_single]
  by_cases hm : m = n
  swap
  · have h0 : topForm n m = 0 := by simp [topForm, hm]
    rw [h0]
    simp only [AlternatingMap.zero_apply, mul_zero]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [if_neg, mul_zero]
    intro heq
    have := congrArg Multiset.card heq
    simp at this
    exact hm this
  subst hm
  rw [topForm_self, topForm_self]
  set a : Fin m → Fin m := fun j => (x j).1 with ha_def
  set b : Fin m → Fin m := fun j => (x j).2 with hb_def

  have hcond : ∀ w : Equiv.Perm (Fin m),
      Finset.univ.val.map x = Finset.univ.val.map (fun c => (c, w c)) →
        Function.Injective a ∧ Function.Injective b := by
    intro w heq
    have h1 := congrArg (Multiset.map Prod.fst) heq
    have h2 := congrArg (Multiset.map Prod.snd) heq
    simp only [Multiset.map_map] at h1 h2
    have e1 : Multiset.map (Prod.fst ∘ fun c => (c, w c)) Finset.univ.val = Finset.univ.val := by
      simp
    have e2 : Multiset.map (Prod.snd ∘ fun c => (c, w c)) Finset.univ.val = Finset.univ.val := by
      simpa using Multiset.map_univ_val_equiv w
    rw [e1] at h1
    rw [e2] at h2
    constructor
    · have hn : (Multiset.map (Prod.fst ∘ x) Finset.univ.val).Nodup := by rw [h1]; exact Finset.univ.nodup
      exact fun i j hij => (Multiset.nodup_map_iff_inj_on Finset.univ.nodup).mp hn i (by simp) j (by simp) hij
    · have hn : (Multiset.map (Prod.snd ∘ x) Finset.univ.val).Nodup := by rw [h2]; exact Finset.univ.nodup
      exact fun i j hij => (Multiset.nodup_map_iff_inj_on Finset.univ.nodup).mp hn i (by simp) j (by simp) hij
  by_cases hab : Function.Injective a ∧ Function.Injective b
  swap
  · have : (Pi.basisFun ℂ (Fin m)).det (fun j => Pi.single (x j).1 1) *
        (Pi.basisFun ℂ (Fin m)).det (fun j => Pi.single (x j).2 1) = 0 := by
      rcases not_and_or.mp hab with h | h
      · rw [det_single_not_inj a h, zero_mul]
      · rw [det_single_not_inj b h, mul_zero]
    rw [this]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [if_neg, mul_zero]
    exact fun heq => hab (hcond w heq)
  obtain ⟨ha, hb⟩ := hab
  let π : Equiv.Perm (Fin m) := Equiv.ofBijective a (Finite.injective_iff_bijective.mp ha)
  let τ : Equiv.Perm (Fin m) := Equiv.ofBijective b (Finite.injective_iff_bijective.mp hb)
  have hπ : ∀ j, (x j).1 = π j := fun j => rfl
  have hτ : ∀ j, (x j).2 = τ j := fun j => rfl
  simp_rw [hπ, hτ, det_single_perm]
  have hx : x = (fun c => (c, (τ * π⁻¹) c)) ∘ π := by
    funext j
    simp [Prod.ext_iff, hπ, hτ]
  have hmap : Finset.univ.val.map x = Finset.univ.val.map (fun c => (c, (τ * π⁻¹) c)) := by
    rw [hx, ← Multiset.map_map, Multiset.map_univ_val_equiv]
  rw [Finset.sum_eq_single (τ * π⁻¹)]
  · rw [if_pos hmap, mul_one, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv]
    push_cast
    ring
  · intro w _ hw
    rw [if_neg, mul_zero]
    intro heq
    apply hw
    ext c
    have hc : (c, w c) ∈ Finset.univ.val.map (fun c => (c, (τ * π⁻¹) c)) := by
      rw [← hmap, heq]; simp
    obtain ⟨c', _, hc'⟩ := Multiset.mem_map.mp hc
    simp only [Prod.mk.injEq] at hc'
    obtain ⟨rfl, h⟩ := hc'
    exact congrArg Fin.val h.symm
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on' with`. Consider the case `monomial u c`. Take `⟨l, hl⟩ : ∃ l : List (Fin n × Fin n), (l : Multiset _) = Finsupp.toMultiset u` from `⟨_, Multiset.coe_toList _⟩`. Establish `hu : u = ∑ j, Finsupp.single (l.get j) 1`. Apply `toMultiset_injective'` to reduce the goal to its premises.

Rewrite using `[toMultiset_sum_single, Fin.univ_val_map, List.ofFn_get, hl]`. Establish `hmon : (monomial u c : MvPolynomial (Fin n × Fin n) ℂ) = c • ∏ j, X (l.get j)`. Rewrite using `[hu, show (∏ j, X (l.get j) : MvPolynomial (Fin n × Fin n) ℂ) = monomial (∑ j, Finsupp.single (l.get j) 1) 1 from (monomial_sum_one _ _).symm, smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[hmon, map_smul, Subalgebra.coe_smul, map_smul, smul_eq_mul, topBig_toEven_prod, ← topCoeff_prod]`. Unfold `GlobalTheory.GoodMetric.topCoeff`.

Simplify using `only [coeff_smul, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun w _ => by ring` and prove the remaining obligations. Consider the case `add p q hp hq`. Rewrite using `[map_add, Subalgebra.coe_add, map_add, ← hp, ← hq]`. Unfold `GlobalTheory.GoodMetric.topCoeff`.

Simplify using `only [coeff_add, mul_add, Finset.sum_add_distrib]`.
-/
theorem topCoeff_eq_topBig (n : ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ) :
    GlobalTheory.GoodMetric.topCoeff P = topBig n (toEven n P : Big n) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial u c =>
    obtain ⟨l, hl⟩ : ∃ l : List (Fin n × Fin n), (l : Multiset _) = Finsupp.toMultiset u :=
      ⟨_, Multiset.coe_toList _⟩
    have hu : u = ∑ j, Finsupp.single (l.get j) 1 := by
      apply toMultiset_injective'
      rw [toMultiset_sum_single, Fin.univ_val_map, List.ofFn_get, hl]
    have hmon : (monomial u c : MvPolynomial (Fin n × Fin n) ℂ) = c • ∏ j, X (l.get j) := by
      rw [hu, show (∏ j, X (l.get j) : MvPolynomial (Fin n × Fin n) ℂ) = monomial (∑ j, Finsupp.single (l.get j) 1) 1 from
        (monomial_sum_one _ _).symm, smul_monomial, smul_eq_mul, mul_one]
    rw [hmon, map_smul, Subalgebra.coe_smul, map_smul, smul_eq_mul, topBig_toEven_prod, ← topCoeff_prod]
    unfold GlobalTheory.GoodMetric.topCoeff
    simp only [coeff_smul, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => by ring
  | add p q hp hq =>
    rw [map_add, Subalgebra.coe_add, map_add, ← hp, ← hq]
    unfold GlobalTheory.GoodMetric.topCoeff
    simp only [coeff_add, mul_add, Finset.sum_add_distrib]

end GlobalTheory.GrassModel.TopRead
