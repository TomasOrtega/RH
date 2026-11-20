import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnHeckeEisensteinFourierTerm
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.LeibnizProd

/- English proof (translation)
Establish `h1 : (p : Multiset ι).countPerms = Nat.multinomial Finset.univ (fun j => (p : Multiset ι).count j)`. Rewrite using `[Multiset.countPerms, Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)]`. Both sides reduce to the same expression. Establish `h2 : ∑ j, (p : Multiset ι).count j = n`. Rewrite using `[Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)]`.

Conclude with `p.2`. Establish `h3` using `Nat.multinomial_spec Finset.univ (fun j => (p : Multiset ι).count j)`. Rewrite `h3` using `[h2]`. Establish `h4 : (p : Multiset ι).countPerms ≤ n.factorial`. Rewrite using `[h1]`.

Conclude with `Nat.le_of_dvd (Nat.factorial_pos n) (Dvd.intro_left _ h3)`. Conclude with `h4` after adjusting the coercions.
-/
theorem countPerms_le_factorial {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (p : Sym ι n) :
    ((p : Multiset ι).countPerms : ℝ) ≤ (n.factorial : ℝ) := by
  have h1 : (p : Multiset ι).countPerms =
      Nat.multinomial Finset.univ (fun j => (p : Multiset ι).count j) := by
    rw [Multiset.countPerms, Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)]
    rfl
  have h2 : ∑ j, (p : Multiset ι).count j = n := by
    rw [Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)]
    exact p.2
  have h3 := Nat.multinomial_spec Finset.univ (fun j => (p : Multiset ι).count j)
  rw [h2] at h3
  have h4 : (p : Multiset ι).countPerms ≤ n.factorial := by
    rw [h1]
    exact Nat.le_of_dvd (Nat.factorial_pos n) (Dvd.intro_left _ h3)
  exact_mod_cast h4

/- English proof (translation)
Rewrite using `[← Finset.sum_prod_piFinset]`. Set `φ : Sym ι n → (ι → ℕ)` to `fun p j => (p : Multiset ι).count j`. Establish `hinj : Set.InjOn φ ↑((Finset.univ : Finset ι).sym n)`. Introduce `p _ q _ h`. Apply `Sym.coe_injective` to reduce the goal to its premises.

Use extensionality with `j`. Conclude with `congrFun h j`. Establish `hs` using `Finset.sum_image (f := fun c : ι → ℕ => ∏ j, a j (c j)) hinj`. Rewrite using `[← hs]`. Apply `Finset.sum_le_sum_of_subset_of_nonneg` to reduce the goal to its premises.

Introduce `c hc`. Take `⟨p, _, rfl⟩` from `Finset.mem_image.1 hc`. Rewrite using `[Fintype.mem_piFinset]`. Introduce `j`. Rewrite using `[Finset.mem_range, Nat.lt_succ_iff]`.

Combine the equalities or inequalities in the displayed calculation. Introduce `c _ _`. Conclude with `Finset.prod_nonneg fun j _ => ha j _`.
-/
theorem sum_sym_le {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (a : ι → ℕ → ℝ)
    (ha : ∀ i k, 0 ≤ a i k) :
    ∑ p ∈ (Finset.univ : Finset ι).sym n, ∏ j, a j ((p : Multiset ι).count j) ≤
      ∏ j, ∑ k ∈ Finset.range (n + 1), a j k := by
  rw [← Finset.sum_prod_piFinset]
  let φ : Sym ι n → (ι → ℕ) := fun p j => (p : Multiset ι).count j
  have hinj : Set.InjOn φ ↑((Finset.univ : Finset ι).sym n) := by
    intro p _ q _ h
    apply Sym.coe_injective
    ext j
    exact congrFun h j
  have hs := Finset.sum_image (f := fun c : ι → ℕ => ∏ j, a j (c j)) hinj
  rw [← hs]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro c hc
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.1 hc
    rw [Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_range, Nat.lt_succ_iff]
    calc (p : Multiset ι).count j ≤ Multiset.card (p : Multiset ι) := Multiset.count_le_card _ _
      _ = n := p.2
  · intro c _ _
    exact Finset.prod_nonneg fun j _ => ha j _

/- English proof (translation)
Use `set P : (ι → ℂ) →L[ℝ] ℂ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℂ) j`. Establish `hPo : IsOpen (P ⁻¹' U)` using `hU.preimage P.continuous`. Establish `hzP : P z ∈ U` using `hz`. Establish `hzP' : z ∈ P ⁻¹' U` using `hz`. Establish `e` using `P.iteratedFDerivWithin_comp_right hg hU.uniqueDiffOn hPo.uniqueDiffOn hzP (i := k) (by exact_mod_cast le_top)`.

Rewrite `e` using `[iteratedFDerivWithin_of_isOpen k hPo hzP', iteratedFDerivWithin_of_isOpen k hU hzP]`. Establish `hfun : (fun w : ι → ℂ => g (w j)) = g ∘ P` using `rfl`. Rewrite using `[hfun, e]`. Use `(ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_` and prove the remaining obligations. Establish `hP : ‖P‖ ≤ 1` using `ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun w => by simpa [P] using norm_le_pi_norm w j)`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hP)`. Use `_ = ‖iteratedFDeriv ℝ k g (z j)‖ := by rw [mul_one]; rfl`.
-/
theorem norm_iteratedFDeriv_comp_apply_le {ι : Type} [Fintype ι] (g : ℂ → ℂ) (U : Set ℂ)
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) (j : ι) (z : ι → ℂ) (hz : z j ∈ U) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun w : ι → ℂ => g (w j)) z‖ ≤ ‖iteratedFDeriv ℝ k g (z j)‖ := by
  set P : (ι → ℂ) →L[ℝ] ℂ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℂ) j
  have hPo : IsOpen (P ⁻¹' U) := hU.preimage P.continuous
  have hzP : P z ∈ U := hz
  have hzP' : z ∈ P ⁻¹' U := hz
  have e := P.iteratedFDerivWithin_comp_right hg hU.uniqueDiffOn hPo.uniqueDiffOn hzP (i := k)
    (by exact_mod_cast le_top)
  rw [iteratedFDerivWithin_of_isOpen k hPo hzP', iteratedFDerivWithin_of_isOpen k hU hzP] at e
  have hfun : (fun w : ι → ℂ => g (w j)) = g ∘ P := rfl
  rw [hfun, e]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hP : ‖P‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun w => by simpa [P] using norm_le_pi_norm w j)
  calc ‖iteratedFDeriv ℝ k g (P z)‖ * ∏ _i : Fin k, ‖P‖ ≤ ‖iteratedFDeriv ℝ k g (P z)‖ * 1 := by
        gcongr
        exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hP)
    _ = ‖iteratedFDeriv ℝ k g (z j)‖ := by rw [mul_one]; rfl

/- English proof (translation)
Introduce `ι _ g U hU hg z hz n`. Use `set V : Set (ι → ℂ) := ⋂ i, (fun w : ι → ℂ => w i) ⁻¹' U i with hVdef`. Establish `hV : IsOpen V` using `isOpen_iInter_of_finite fun i => (hU i).preimage (continuous_apply i)`. Establish `hzV : z ∈ V` using `Set.mem_iInter.2 hz`. Establish `hf : ∀ i ∈ (Finset.univ : Finset ι), ContDiffOn ℝ ∞ (fun w : ι → ℂ => g i (w i)) V`.

Introduce `i _`. Conclude with `(hg i).comp (contDiff_apply ℝ ℂ i).contDiffOn (fun w hw => Set.mem_iInter.1 hw i)`. Establish `key` using `norm_iteratedFDerivWithin_prod_le (u := Finset.univ) hf hV.uniqueDiffOn hzV (n := n) (by exact_mod_cast le_top)`. Rewrite `key` using `[iteratedFDerivWithin_of_isOpen n hV hzV]`. Use `key.trans ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Conclude with `countPerms_le_factorial p` after adjusting the coercions. Rewrite using `[iteratedFDerivWithin_of_isOpen _ hV hzV]`. Conclude with `norm_iteratedFDeriv_comp_apply_le (g j) (U j) (hU j) (hg j) j z (hz j) _`. Use `_ ≤ _ := by`.

Rewrite using `[← Finset.mul_sum]`. Use `gcongr`. Conclude with `sum_sym_le n (fun j k => ‖iteratedFDeriv ℝ k (g j) (z j)‖) (fun _ _ => norm_nonneg _)`.
-/
theorem norm_iteratedFDeriv_prod_apply_le : ∀ (ι : Type) [Fintype ι] (g : ι → ℂ → ℂ) (U : ι → Set ℂ), (∀ i, IsOpen (U i)) →
    (∀ i, ContDiffOn ℝ ∞ (g i) (U i)) → ∀ z : ι → ℂ, (∀ i, z i ∈ U i) → ∀ n : ℕ,
      ‖iteratedFDeriv ℝ n (fun z : ι → ℂ => ∏ i, g i (z i)) z‖ ≤
        n.factorial * ∏ i, ∑ k ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ k (g i) (z i)‖ := by
  intro ι _ g U hU hg z hz n
  classical
  set V : Set (ι → ℂ) := ⋂ i, (fun w : ι → ℂ => w i) ⁻¹' U i with hVdef
  have hV : IsOpen V := isOpen_iInter_of_finite fun i => (hU i).preimage (continuous_apply i)
  have hzV : z ∈ V := Set.mem_iInter.2 hz
  have hf : ∀ i ∈ (Finset.univ : Finset ι), ContDiffOn ℝ ∞ (fun w : ι → ℂ => g i (w i)) V := by
    intro i _
    exact (hg i).comp (contDiff_apply ℝ ℂ i).contDiffOn (fun w hw => Set.mem_iInter.1 hw i)
  have key := norm_iteratedFDerivWithin_prod_le (u := Finset.univ) hf hV.uniqueDiffOn hzV (n := n)
    (by exact_mod_cast le_top)
  rw [iteratedFDerivWithin_of_isOpen n hV hzV] at key
  refine key.trans ?_
  calc _ ≤ ∑ p ∈ (Finset.univ : Finset ι).sym n, (n.factorial : ℝ) *
        ∏ j, ‖iteratedFDeriv ℝ ((p : Multiset ι).count j) (g j) (z j)‖ := by
        gcongr with p hp j
        · exact_mod_cast countPerms_le_factorial p
        · rw [iteratedFDerivWithin_of_isOpen _ hV hzV]
          exact norm_iteratedFDeriv_comp_apply_le (g j) (U j) (hU j) (hg j) j z (hz j) _
    _ ≤ _ := by
        rw [← Finset.mul_sum]
        gcongr
        exact sum_sym_le n (fun j k => ‖iteratedFDeriv ℝ k (g j) (z j)‖) (fun _ _ => norm_nonneg _)

end GlobalTheory.LeibnizProd
