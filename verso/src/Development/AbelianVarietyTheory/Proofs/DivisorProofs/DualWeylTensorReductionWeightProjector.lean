import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualWeylWeightProjector

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

namespace GlobalTheory.HighWtEmb

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[coeff_weightedHomogeneousComponent, coeff_monomial]`. Apply the tactic sequence `by_cases h : Finsupp.weight w d = n <;> by_cases hd : d = m`. Substitute `hd` using the available equality. Simplify using `[h]`.

Simplify using `[h, hd, coeff_monomial]`. Substitute `hd` using the available equality. Simplify using `[h]`. Simplify using `[h, hd]`.
-/
theorem wComp_monomial_eq_ite {σ R M : Type} [CommSemiring R] [AddCommMonoid M] [DecidableEq M] (w : σ → M) (n : M) (d : σ →₀ ℕ) (c : R) :
    weightedHomogeneousComponent w n (monomial d c) = if Finsupp.weight w d = n then monomial d c else 0 := by
  classical
  ext m
  rw [coeff_weightedHomogeneousComponent, coeff_monomial]
  by_cases h : Finsupp.weight w d = n <;> by_cases hd : d = m
  · subst hd; simp [h]
  · simp [h, hd, coeff_monomial]
  · subst hd; simp [h]
  · simp [h, hd]

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]`. Use `split_ifs with h`. Use `Finset.sum_congr rfl fun x hx => ?_` and prove the remaining obligations. Rewrite using `[coeff_weightedHomogeneousComponent]`.

Distinguish the cases in `hq : coeff x.2 Q = 0`. Simplify using `[hq]`. Establish `h2` using `hQ hq`. Establish `hm : x.1 + x.2 = m` using `Finset.HasAntidiagonal.mem_antidiagonal.1 hx`. Establish `e : Finsupp.weight w x.1 = n` using `by rw [← h, ← hm, map_add, h2, add_zero]`.

Rewrite using `[if_pos e]`. Use `symm`. Use `Finset.sum_eq_zero fun x hx => ?_` and prove the remaining obligations. Rewrite using `[coeff_weightedHomogeneousComponent]`. Distinguish the cases in `hq : coeff x.2 Q = 0`.

Simplify using `[hq]`. Establish `h2` using `hQ hq`. Establish `hm : x.1 + x.2 = m` using `Finset.HasAntidiagonal.mem_antidiagonal.1 hx`. Establish `e : Finsupp.weight w x.1 ≠ n` using `by rw [← hm, map_add, h2, add_zero] at h; exact h`. Rewrite using `[if_neg e, zero_mul]`.
-/
theorem wComp_mul_of_weight_zero {σ R M : Type} [CommSemiring R] [AddCommMonoid M] (w : σ → M) (n : M) (P Q : MvPolynomial σ R)
    (hQ : IsWeightedHomogeneous w Q 0) :
    weightedHomogeneousComponent w n (P * Q) = weightedHomogeneousComponent w n P * Q := by
  classical
  ext m
  rw [coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]
  split_ifs with h
  · refine Finset.sum_congr rfl fun x hx => ?_
    rw [coeff_weightedHomogeneousComponent]
    by_cases hq : coeff x.2 Q = 0
    · simp [hq]
    · have h2 := hQ hq
      have hm : x.1 + x.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
      have e : Finsupp.weight w x.1 = n := by rw [← h, ← hm, map_add, h2, add_zero]
      rw [if_pos e]
  · symm
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [coeff_weightedHomogeneousComponent]
    by_cases hq : coeff x.2 Q = 0
    · simp [hq]
    · have h2 := hQ hq
      have hm : x.1 + x.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
      have e : Finsupp.weight w x.1 ≠ n := by rw [← hm, map_add, h2, add_zero] at h; exact h
      rw [if_neg e, zero_mul]

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp [blockRed, MvPolynomial.algebraMap_eq]`. Consider the case `add p q hp hq => rw [map_add, map_add, map_add, hp, hq]`. Consider the case `mul_X p v hp => rw [map_mul, hp]`. Simplify using `[blockRed]`.
-/
theorem blockRed_eq_rename_map (O : Type) [CommRing O] (N : ℕ) {ι : Type} (ϖ : O) (τ : ι) (f : MvPolynomial (Fin N × Fin N) O) :
    blockRed O N ϖ τ f = rename (fun v => ((τ, v) : BVar N ι)) (map (Ideal.Quotient.mk (Ideal.span {ϖ})) f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [blockRed, MvPolynomial.algebraMap_eq]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p v hp => rw [map_mul, hp]; simp [blockRed]

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum_mapDomain_index (h := fun i c => c • blockW N τ i) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]`. Simplify using `[blockW, rowW]`.
-/
theorem weight_blockW_mapDomain_self (N : ℕ) {ι : Type} [DecidableEq ι] (τ : ι) (d : Fin N × Fin N →₀ ℕ) :
    Finsupp.weight (blockW N τ) (Finsupp.mapDomain (fun v => ((τ, v) : BVar N ι)) d) = Finsupp.weight (rowW N N) d := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum_mapDomain_index (h := fun i c => c • blockW N τ i) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  simp [blockW, rowW]

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_mapDomain_index (h := fun i c => c • blockW N τ i) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]`. Simplify using `[blockW, h]`.
-/
theorem weight_blockW_mapDomain_of_ne (N : ℕ) {ι : Type} [DecidableEq ι] {τ σ : ι} (h : σ ≠ τ) (d : Fin N × Fin N →₀ ℕ) :
    Finsupp.weight (blockW N τ) (Finsupp.mapDomain (fun v => ((σ, v) : BVar N ι)) d) = 0 := by
  rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (h := fun i c => c • blockW N τ i) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  simp [blockW, h]

end GlobalTheory.HighWtEmb

namespace GlobalTheory.HighWtEmb

/- English proof (translation)
Use `conv_rhs => rw [f.as_sum]`. Rewrite using `[weightedHomogeneousComponent_apply, map_sum, map_sum, map_sum, Finset.sum_filter]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Simplify using `only [blockRed_eq_rename_map, map_monomial, rename_monomial]`. Rewrite using `[wComp_monomial_eq_ite, weight_blockW_mapDomain_self]`.
-/
theorem blockRed_wComp_rowW (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (ϖ : O) (τ : ι) (v : Fin N → ℕ)
    (f : MvPolynomial (Fin N × Fin N) O) :
    blockRed O N ϖ τ (weightedHomogeneousComponent (rowW N N) v f) =
      weightedHomogeneousComponent (blockW N τ) v (blockRed O N ϖ τ f) := by
  classical
  conv_rhs => rw [f.as_sum]
  rw [weightedHomogeneousComponent_apply, map_sum, map_sum, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [blockRed_eq_rename_map, map_monomial, rename_monomial]
  rw [wComp_monomial_eq_ite, weight_blockW_mapDomain_self]

/- English proof (translation)
Rewrite using `[blockRed_eq_rename_map, f.as_sum, map_sum, map_sum, ← mem_weightedHomogeneousSubmodule]`. Use `Submodule.sum_mem _ fun d _ => ?_` and prove the remaining obligations. Rewrite using `[mem_weightedHomogeneousSubmodule, map_monomial, rename_monomial]`. Conclude with `isWeightedHomogeneous_monomial _ _ _ (weight_blockW_mapDomain_of_ne N h d)`.
-/
theorem blockRed_isWeightedHomogeneous_zero (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (ϖ : O) {τ σ : ι} (h : σ ≠ τ)
    (f : MvPolynomial (Fin N × Fin N) O) : IsWeightedHomogeneous (blockW N τ) (blockRed O N ϖ σ f) 0 := by
  rw [blockRed_eq_rename_map, f.as_sum, map_sum, map_sum, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun d _ => ?_
  rw [mem_weightedHomogeneousSubmodule, map_monomial, rename_monomial]
  exact isWeightedHomogeneous_monomial _ _ _ (weight_blockW_mapDomain_of_ne N h d)

/- English proof (translation)
Simplify using `[redT]`.
-/
theorem redT_tprod_prod_blockRed (O : Type) [CommRing O] (N : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (ϖ : O)
    (x : ∀ τ, dualWeyl O N N (res N (mu τ))) :
    redT O N mu ϖ (PiTensorProduct.tprod O x) = ∏ σ, blockRed O N ϖ σ (x σ) := by
  simp [redT]

/- English proof (translation)
Introduce `O _ N ι _ _ mu ϖ τ v a ha y`. Establish `key : (redT O N mu ϖ).comp a = ((weightedHomogeneousComponent (blockW N τ) v).restrictScalars O).comp (redT O N mu ϖ)`. Apply `PiTensorProduct.ext` to reduce the goal to its premises. Apply `MultilinearMap.ext` to reduce the goal to its premises. Introduce `x`.

Simplify using `only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply]`. Set `yy : dualWeyl O N N (res N (mu τ))` to `rowProj O N (res N (mu τ)) v (x τ)`. Establish `hQ : IsWeightedHomogeneous (blockW N τ) (∏ σ ∈ ({τ}ᶜ : Finset ι), blockRed O N ϖ σ (x σ)) 0`. Use `IsWeightedHomogeneous.prod ({τ}ᶜ : Finset ι) (fun σ => blockRed O N ϖ σ (x σ)) (fun _ => (0 : Fin N → ℕ)) (fun σ hσ => blockRed_isWeightedHomogeneous_zero O N ϖ (by simpa using hσ) (x σ))` as an intermediate fact. Simplify using `using this`.

Rewrite using `[ha x yy rfl, redT_tprod_prod_blockRed, redT_tprod_prod_blockRed, Fintype.prod_eq_mul_prod_compl τ, Fintype.prod_eq_mul_prod_compl τ, Function.update_self, wComp_mul_of_weight_zero _ _ _ _ hQ]`. Use `congr 1`. Use `show blockRed O N ϖ τ (weightedHomogeneousComponent (rowW N N) v (x τ : MvPolynomial (Fin N × Fin N) O)) = _`. Conclude with `blockRed_wComp_rowW O N ϖ τ v _`. Use `Finset.prod_congr rfl fun σ hσ => ?_` and prove the remaining obligations.

Rewrite using `[Function.update_of_ne (by simpa using hσ)]`. Conclude with `LinearMap.congr_fun key y`.
-/
theorem redT_isProj : ∀ (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (ϖ : O) (τ : ι) (v : Fin N → ℕ) (a : Module.End O (NablaT O N mu)), IsProj O N mu τ v a → ∀ y : NablaT O N mu, redT O N mu ϖ (a y) = weightedHomogeneousComponent (blockW N τ) v (redT O N mu ϖ y) := by
  intro O _ N ι _ _ mu ϖ τ v a ha y
  have key : (redT O N mu ϖ).comp a =
      ((weightedHomogeneousComponent (blockW N τ) v).restrictScalars O).comp (redT O N mu ϖ) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply]
    let yy : dualWeyl O N N (res N (mu τ)) := rowProj O N (res N (mu τ)) v (x τ)
    have hQ : IsWeightedHomogeneous (blockW N τ) (∏ σ ∈ ({τ}ᶜ : Finset ι), blockRed O N ϖ σ (x σ)) 0 := by
      have := IsWeightedHomogeneous.prod ({τ}ᶜ : Finset ι) (fun σ => blockRed O N ϖ σ (x σ)) (fun _ => (0 : Fin N → ℕ))
        (fun σ hσ => blockRed_isWeightedHomogeneous_zero O N ϖ (by simpa using hσ) (x σ))
      simpa using this
    rw [ha x yy rfl, redT_tprod_prod_blockRed, redT_tprod_prod_blockRed, Fintype.prod_eq_mul_prod_compl τ, Fintype.prod_eq_mul_prod_compl τ,
      Function.update_self, wComp_mul_of_weight_zero _ _ _ _ hQ]
    congr 1
    · show blockRed O N ϖ τ (weightedHomogeneousComponent (rowW N N) v (x τ : MvPolynomial (Fin N × Fin N) O)) = _
      exact blockRed_wComp_rowW O N ϖ τ v _
    · refine Finset.prod_congr rfl fun σ hσ => ?_
      rw [Function.update_of_ne (by simpa using hσ)]
  exact LinearMap.congr_fun key y

end GlobalTheory.HighWtEmb
