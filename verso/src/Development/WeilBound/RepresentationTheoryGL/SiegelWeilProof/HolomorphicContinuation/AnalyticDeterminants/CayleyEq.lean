import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.CayleyA

noncomputable section

open Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.CEq

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
/- English proof (translation)
Take `⟨s, hs0, hAs⟩` from `hF.exists_mem_nhds_analyticOnNhd`. Establish `ht : IsOpen (interior s)` using `isOpen_interior`. Establish `h0t : (0 : Matrix κ κ ℂ) ∈ interior s` using `mem_interior_iff_mem_nhds.mpr hs0`. Establish `hcd : ContDiffOn ℂ ω F (interior s)` using `(hAs.mono interior_subset).contDiffOn ht.uniqueDiffOn`. Establish `hpre : IsOpen (L ⁻¹' interior s)` using `ht.preimage L.continuous`.

Establish `hL0 : L 0 ∈ interior s` using `by simpa using h0t`. Establish `h0pre : (0 : Matrix ι ι ℂ) ∈ L ⁻¹' interior s` using `hL0`. Establish `key` using `L.iteratedFDerivWithin_comp_right hcd ht.uniqueDiffOn hpre.uniqueDiffOn hL0 (i := n) le_top`. Establish `e1` using `iteratedFDerivWithin_of_isOpen (𝕜 := ℂ) (f := F ∘ L) n hpre h0pre`. Establish `e2` using `iteratedFDerivWithin_of_isOpen (𝕜 := ℂ) (f := F) n ht h0t`.

Establish `hz : L 0 = 0` using `L.map_zero`. Rewrite using `[← e1, ← e2]`. Use `erw [key]`. Conclude with `congrArg (fun y => iteratedFDerivWithin ℂ n F (interior s) y (fun i => L (v i))) hz`.
-/
theorem iteratedFDeriv_comp_clm (F : Matrix κ κ ℂ → ℂ) (hF : AnalyticAt ℂ F 0)
    (L : Matrix ι ι ℂ →L[ℂ] Matrix κ κ ℂ) (n : ℕ) (v : Fin n → Matrix ι ι ℂ) :
    iteratedFDeriv ℂ n (F ∘ L) 0 v = iteratedFDeriv ℂ n F 0 (fun i => L (v i)) := by
  obtain ⟨s, hs0, hAs⟩ := hF.exists_mem_nhds_analyticOnNhd
  have ht : IsOpen (interior s) := isOpen_interior
  have h0t : (0 : Matrix κ κ ℂ) ∈ interior s := mem_interior_iff_mem_nhds.mpr hs0
  have hcd : ContDiffOn ℂ ω F (interior s) := (hAs.mono interior_subset).contDiffOn ht.uniqueDiffOn
  have hpre : IsOpen (L ⁻¹' interior s) := ht.preimage L.continuous
  have hL0 : L 0 ∈ interior s := by simpa using h0t
  have h0pre : (0 : Matrix ι ι ℂ) ∈ L ⁻¹' interior s := hL0
  have key := L.iteratedFDerivWithin_comp_right hcd ht.uniqueDiffOn hpre.uniqueDiffOn hL0
    (i := n) le_top
  have e1 := iteratedFDerivWithin_of_isOpen (𝕜 := ℂ) (f := F ∘ L) n hpre h0pre
  have e2 := iteratedFDerivWithin_of_isOpen (𝕜 := ℂ) (f := F) n ht h0t
  have hz : L 0 = 0 := L.map_zero
  rw [← e1, ← e2]
  erw [key]
  exact congrArg (fun y => iteratedFDerivWithin ℂ n F (interior s) y (fun i => L (v i))) hz

omit [DecidableEq κ] in
/- English proof (translation)
The claim follows from `(hF.contDiffAt).iteratedFDeriv_comp_perm v π`.
-/
theorem symm_perm (F : Matrix κ κ ℂ → ℂ) (hF : AnalyticAt ℂ F 0) {n : ℕ} (v : Fin n → Matrix κ κ ℂ)
    (π : Equiv.Perm (Fin n)) : iteratedFDeriv ℂ n F 0 (v ∘ π) = iteratedFDeriv ℂ n F 0 v :=
  (hF.contDiffAt).iteratedFDeriv_comp_perm v π

def Dg {n : ℕ} (f : κ ≃ Fin n) (F : Matrix κ κ ℂ → ℂ) : ℂ :=
  ∑ σ : Equiv.Perm κ, (Equiv.Perm.sign σ : ℂ) *
    iteratedFDeriv ℂ n F 0 (fun i => Matrix.single (f.symm i) (σ (f.symm i)) 1)

omit [DecidableEq ι] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem detD_eq_Dg (F : Matrix κ κ ℂ → ℂ) : detD F = Dg (Fintype.equivFin κ) F := rfl

/- English proof (translation)
Establish `hnm : n = m` using `by simpa using Fintype.card_congr (f.symm.trans g)`. Substitute `hnm` using the available equality. Unfold `Dg`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Use `congr 1`.

Establish `hv : (fun i => Matrix.single (f.symm i) (σ (f.symm i)) (1 : ℂ)) = (fun i => Matrix.single (g.symm i) (σ (g.symm i)) (1 : ℂ)) ∘ (f.symm.trans g)`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Rewrite using `[hv]`. Conclude with `symm_perm F hF _ _`.
-/
theorem Dg_indep (F : Matrix κ κ ℂ → ℂ) (hF : AnalyticAt ℂ F 0) {n m : ℕ} (f : κ ≃ Fin n) (g : κ ≃ Fin m) :
    Dg f F = Dg g F := by
  have hnm : n = m := by simpa using Fintype.card_congr (f.symm.trans g)
  subst hnm
  unfold Dg
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  have hv : (fun i => Matrix.single (f.symm i) (σ (f.symm i)) (1 : ℂ)) =
      (fun i => Matrix.single (g.symm i) (σ (g.symm i)) (1 : ℂ)) ∘ (f.symm.trans g) := by
    funext i
    simp
  rw [hv]
  exact symm_perm F hF _ _

omit [DecidableEq ι] [DecidableEq κ] in
/- English proof (translation)
Use extensionality with `x y`. Simplify using `only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.single_apply, Equiv.eq_symm_apply]`.
-/
theorem reindex_single [DecidableEq ι] [DecidableEq κ] (e' : ι ≃ κ) (a b : ι) :
    (Matrix.single a b (1 : ℂ)).reindex e' e' = Matrix.single (e' a) (e' b) 1 := by
  ext x y
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.single_apply, Equiv.eq_symm_apply]

/- English proof (translation)
Introduce `ι κ _ _ _ _ e F hF`. Rewrite using `[detD_eq_Dg, detD_eq_Dg, ← Dg_indep F hF (e.symm.trans (Fintype.equivFin ι)) (Fintype.equivFin κ)]`. Unfold `Dg`. Use `Fintype.sum_equiv (Equiv.permCongr e) _ _ fun σ => ?_` and prove the remaining obligations. Rewrite using `[Equiv.Perm.sign_permCongr]`.

Use `congr 1`. Establish `h1 : iteratedFDeriv ℂ (Fintype.card ι) (fun T => F (Matrix.reindex e e T)) 0 (fun i => Matrix.single ((Fintype.equivFin ι).symm i) (σ ((Fintype.equivFin ι).symm i)) (1 : ℂ)) = iteratedFDeriv ℂ (Fintype.card ι) F 0 (fun i => Matrix.reindex e e (Matrix.single ((Fintype.equivFin ι). …` using `iteratedFDeriv_comp_clm F hF (LinearMap.toContinuousLinearMap (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap) _ _`. Rewrite using `[h1]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Rewrite using `[reindex_single]`. Simplify using the standard rewrite rules.
-/
theorem reindex_thm : Reindex := by
  intro ι κ _ _ _ _ e F hF
  rw [detD_eq_Dg, detD_eq_Dg,
    ← Dg_indep F hF (e.symm.trans (Fintype.equivFin ι)) (Fintype.equivFin κ)]
  unfold Dg
  refine Fintype.sum_equiv (Equiv.permCongr e) _ _ fun σ => ?_
  rw [Equiv.Perm.sign_permCongr]
  congr 1
  have h1 : iteratedFDeriv ℂ (Fintype.card ι) (fun T => F (Matrix.reindex e e T)) 0
      (fun i => Matrix.single ((Fintype.equivFin ι).symm i) (σ ((Fintype.equivFin ι).symm i)) (1 : ℂ)) =
      iteratedFDeriv ℂ (Fintype.card ι) F 0 (fun i =>
        Matrix.reindex e e (Matrix.single ((Fintype.equivFin ι).symm i)
          (σ ((Fintype.equivFin ι).symm i)) (1 : ℂ))) :=
    iteratedFDeriv_comp_clm F hF
      (LinearMap.toContinuousLinearMap (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap) _ _
  rw [h1]
  congr 1
  funext i
  rw [reindex_single]
  simp

omit [Fintype ι] in
/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, ite_and]`.
-/
theorem mul_single_eq [Fintype ι] (A : Matrix ι ι ℂ) (a b : ι) :
    A * Matrix.single a b (1 : ℂ) = ∑ c, A c a • Matrix.single c b (1 : ℂ) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, ite_and]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨i, j, hij, hne⟩ : ∃ i j, r i = r j ∧ i ≠ j := by`. Simplify using `only [Function.Injective, not_forall] at hr`. Take `⟨i, j, h, hne⟩` from `hr`. Conclude with `⟨i, j, h, hne⟩`. Establish `hane : a i ≠ a j` using `fun h => hne (a.injective h)`.

Establish `key : ∀ σ : Equiv.Perm ι, iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (r k) ((σ * Equiv.swap (a i) (a j)) (a k)) (1 : ℂ)) = iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (r k) (σ (a k)) (1 : ℂ))`. Introduce `σ`. Rewrite using `[← symm_perm F hF (fun k => Matrix.single (r k) (σ (a k)) (1 : ℂ)) (Equiv.swap i j)]`. Use `congr 1`. Use function extensionality and compare the values at `k`.

Simplify using `only [Function.comp, Equiv.Perm.mul_apply]`. Distinguish the cases in `hki : k = i`. Substitute `hki` using the available equality. Rewrite using `[Equiv.swap_apply_left, Equiv.swap_apply_left, hij]`. Distinguish the cases in `hkj : k = j`.

Substitute `hkj` using the available equality. Rewrite using `[Equiv.swap_apply_right, Equiv.swap_apply_right, hij]`. Establish `h1 : a k ≠ a i` using `fun h => hki (a.injective h)`. Establish `h2 : a k ≠ a j` using `fun h => hkj (a.injective h)`. Rewrite using `[Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne hki hkj]`.

Establish `hS` using `(Equiv.sum_comp (Equiv.mulRight (Equiv.swap (a i) (a j))) (fun σ : Equiv.Perm ι => ((Equiv.Perm.sign σ : ℤ) : ℂ) * iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (r k) (σ (a k)) (1 : ℂ)))).symm`. Establish `hg : ∀ σ : Equiv.Perm ι, ((Equiv.Perm.sign (σ * Equiv.swap (a i) (a j)) : ℤ) : ℂ) * iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (r k) ((σ * Equiv.swap (a i) (a j)) (a k)) (1 : ℂ)) = -(((Equiv.Perm.sign σ : ℤ) : ℂ) * iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (r k) (σ (a k) …`. Introduce `σ`. Rewrite using `[key σ, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hane]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Equiv.coe_mulRight] at hS`. Rewrite `hS` using `[Finset.sum_congr rfl (fun σ _ => hg σ), Finset.sum_neg_distrib]`. Establish `h2 : (2 : ℂ) * ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) * iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (r k) (σ (a k)) (1 : ℂ)) = 0`. Take the linear combination `hS`.

Simplify using `using h2`.
-/
private theorem sum_sign_iteratedFDeriv_single_eq_zero_of_not_inj (F : Matrix ι ι ℂ → ℂ) (hF : AnalyticAt ℂ F 0) {n : ℕ}
    (a : Fin n ≃ ι) (r : Fin n → ι) (hr : ¬ Function.Injective r) :
    ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (r k) (σ (a k)) (1 : ℂ)) = 0 := by
  obtain ⟨i, j, hij, hne⟩ : ∃ i j, r i = r j ∧ i ≠ j := by
    simp only [Function.Injective, not_forall] at hr
    obtain ⟨i, j, h, hne⟩ := hr
    exact ⟨i, j, h, hne⟩
  have hane : a i ≠ a j := fun h => hne (a.injective h)
  have key : ∀ σ : Equiv.Perm ι, iteratedFDeriv ℂ n F 0
      (fun k => Matrix.single (r k) ((σ * Equiv.swap (a i) (a j)) (a k)) (1 : ℂ)) =
      iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (r k) (σ (a k)) (1 : ℂ)) := by
    intro σ
    rw [← symm_perm F hF (fun k => Matrix.single (r k) (σ (a k)) (1 : ℂ)) (Equiv.swap i j)]
    congr 1
    funext k
    simp only [Function.comp, Equiv.Perm.mul_apply]
    by_cases hki : k = i
    · subst hki
      rw [Equiv.swap_apply_left, Equiv.swap_apply_left, hij]
    · by_cases hkj : k = j
      · subst hkj
        rw [Equiv.swap_apply_right, Equiv.swap_apply_right, hij]
      · have h1 : a k ≠ a i := fun h => hki (a.injective h)
        have h2 : a k ≠ a j := fun h => hkj (a.injective h)
        rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hS := (Equiv.sum_comp (Equiv.mulRight (Equiv.swap (a i) (a j)))
    (fun σ : Equiv.Perm ι => ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (r k) (σ (a k)) (1 : ℂ)))).symm
  have hg : ∀ σ : Equiv.Perm ι, ((Equiv.Perm.sign (σ * Equiv.swap (a i) (a j)) : ℤ) : ℂ) *
      iteratedFDeriv ℂ n F 0
        (fun k => Matrix.single (r k) ((σ * Equiv.swap (a i) (a j)) (a k)) (1 : ℂ)) =
      -(((Equiv.Perm.sign σ : ℤ) : ℂ) *
        iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (r k) (σ (a k)) (1 : ℂ))) := by
    intro σ
    rw [key σ, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hane]
    push_cast
    ring
  simp only [Equiv.coe_mulRight] at hS
  rw [Finset.sum_congr rfl (fun σ _ => hg σ), Finset.sum_neg_distrib] at hS
  have h2 : (2 : ℂ) * ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (r k) (σ (a k)) (1 : ℂ)) = 0 := by
    linear_combination hS
  simpa using h2

/- English proof (translation)
Establish `hterm : ∀ σ : Equiv.Perm ι, iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (ρ (a k)) (σ (a k)) (1 : ℂ)) = iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (a k) ((σ * ρ⁻¹) (a k)) (1 : ℂ))`. Introduce `σ`. Rewrite using `[← symm_perm F hF (fun k => Matrix.single (a k) ((σ * ρ⁻¹) (a k)) (1 : ℂ)) ((a.trans ρ).trans a.symm)]`. Use `congr 1`. Use function extensionality and compare the values at `k`.

Simplify using `[Equiv.Perm.mul_apply]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[mul_inv_cancel_right, Equiv.Perm.sign_mul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem sum_sign_iteratedFDeriv_single_perm_eq_sign_mul (F : Matrix ι ι ℂ → ℂ) (hF : AnalyticAt ℂ F 0) {n : ℕ}
    (a : Fin n ≃ ι) (ρ : Equiv.Perm ι) :
    ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (ρ (a k)) (σ (a k)) (1 : ℂ)) =
    ((Equiv.Perm.sign ρ : ℤ) : ℂ) * ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (a k) (σ (a k)) (1 : ℂ)) := by
  have hterm : ∀ σ : Equiv.Perm ι,
      iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (ρ (a k)) (σ (a k)) (1 : ℂ)) =
      iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (a k) ((σ * ρ⁻¹) (a k)) (1 : ℂ)) := by
    intro σ
    rw [← symm_perm F hF (fun k => Matrix.single (a k) ((σ * ρ⁻¹) (a k)) (1 : ℂ))
      ((a.trans ρ).trans a.symm)]
    congr 1
    funext k
    simp [Equiv.Perm.mul_apply]
  calc ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (ρ (a k)) (σ (a k)) (1 : ℂ))
      = ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (a k) ((σ * ρ⁻¹) (a k)) (1 : ℂ)) :=
        Finset.sum_congr rfl fun σ _ => by rw [hterm σ]
    _ = ∑ τ : Equiv.Perm ι, ((Equiv.Perm.sign (τ * ρ) : ℤ) : ℂ) *
        iteratedFDeriv ℂ n F 0 (fun k => Matrix.single (a k) ((τ * ρ * ρ⁻¹) (a k)) (1 : ℂ)) :=
        (Equiv.sum_comp (Equiv.mulRight ρ) (fun σ : Equiv.Perm ι => ((Equiv.Perm.sign σ : ℤ) : ℂ) *
          iteratedFDeriv ℂ n F 0
            (fun k => Matrix.single (a k) ((σ * ρ⁻¹) (a k)) (1 : ℂ)))).symm
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [mul_inv_cancel_right, Equiv.Perm.sign_mul]
        push_cast
        ring

/- English proof (translation)
Introduce `ι _ _ F A hF`. Set `a : Fin (Fintype.card ι) ≃ ι` to `(Fintype.equivFin ι).symm`. Set `L : Matrix ι ι ℂ →L[ℂ] Matrix ι ι ℂ` to `LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ A)`. Establish `hΦ : ∀ σ : Equiv.Perm ι, iteratedFDeriv ℂ (Fintype.card ι) (fun T => F (A * T)) 0 (fun i => Matrix.single (a i) (σ (a i)) (1 : ℂ)) = ∑ r : Fin (Fintype.card ι) → ι, (∏ i, A (r i) (a i)) * iteratedFDeriv ℂ (Fintype.card ι) F 0 (fun i => Matrix.single (r i) (σ (a i)) (1 : ℂ))`. Introduce `σ`.

Establish `h1 : iteratedFDeriv ℂ (Fintype.card ι) (fun T => F (A * T)) 0 (fun i => Matrix.single (a i) (σ (a i)) (1 : ℂ)) = iteratedFDeriv ℂ (Fintype.card ι) F 0 (fun i => A * Matrix.single (a i) (σ (a i)) (1 : ℂ))` using `iteratedFDeriv_comp_clm F hF L _ _`. Rewrite using `[h1]`. Repeatedly rewrite using `[mul_single_eq]`. Rewrite using `[ContinuousMultilinearMap.map_sum]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations.

Rewrite using `[ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]`. Establish `hswap : detD (fun T => F (A * T)) = ∑ r : Fin (Fintype.card ι) → ι, (∏ i, A (r i) (a i)) * ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) * iteratedFDeriv ℂ (Fintype.card ι) F 0 (fun i => Matrix.single (r i) (σ (a i)) (1 : ℂ))`. Unfold `detD`. Rewrite using `[Finset.sum_congr rfl fun σ _ => by rw [hΦ σ]]`. Repeatedly rewrite using `[Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hswap]`. Establish `hinj : ∀ ρ ∈ (Finset.univ : Finset (Equiv.Perm ι)), ∀ ρ' ∈ (Finset.univ : Finset (Equiv.Perm ι)), (fun i => ρ (a i)) = (fun i => ρ' (a i)) → ρ = ρ'`.

Introduce `ρ _ ρ' _ h`. Use extensionality with `x`. Simplify `congrFun h (Fintype.equivFin ι x)` using `[a]`. Rewrite using `[← Finset.sum_subset (Finset.subset_univ ((Finset.univ : Finset (Equiv.Perm ι)).image fun ρ => (fun i => ρ (a i)))), Finset.sum_image hinj]`. Establish `hD : detD F = ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) * iteratedFDeriv ℂ (Fintype.card ι) F 0 (fun k => Matrix.single (a k) (σ (a k)) (1 : ℂ))` using `rfl`.

Repeatedly rewrite using `[sum_sign_iteratedFDeriv_single_perm_eq_sign_mul F hF a, ← hD]`. Rewrite using `[Matrix.det_apply', Finset.sum_mul]`. Use `Finset.sum_congr rfl fun ρ _ => ?_` and prove the remaining obligations. Rewrite using `[show (∏ i, A (ρ (a i)) (a i)) = ∏ x, A (ρ x) x from Equiv.prod_comp a (fun x => A (ρ x) x)]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `r _ hr`. Rewrite using `[sum_sign_iteratedFDeriv_single_eq_zero_of_not_inj F hF a r ?_, mul_zero]`. Introduce `hr'`. Apply `hr` to reduce the goal to its premises. Rewrite using `[Finset.mem_image]`.

Use `⟨Equiv.ofBijective (fun x => r (a.symm x)) ((hr'.comp a.symm.injective).bijective_of_finite), Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.
-/
theorem equivar_thm : Equivar := by
  intro ι _ _ F A hF
  let a : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let L : Matrix ι ι ℂ →L[ℂ] Matrix ι ι ℂ :=
    LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ A)
  have hΦ : ∀ σ : Equiv.Perm ι,
      iteratedFDeriv ℂ (Fintype.card ι) (fun T => F (A * T)) 0
        (fun i => Matrix.single (a i) (σ (a i)) (1 : ℂ)) =
      ∑ r : Fin (Fintype.card ι) → ι, (∏ i, A (r i) (a i)) *
        iteratedFDeriv ℂ (Fintype.card ι) F 0 (fun i => Matrix.single (r i) (σ (a i)) (1 : ℂ)) := by
    intro σ
    have h1 : iteratedFDeriv ℂ (Fintype.card ι) (fun T => F (A * T)) 0
        (fun i => Matrix.single (a i) (σ (a i)) (1 : ℂ)) =
        iteratedFDeriv ℂ (Fintype.card ι) F 0
          (fun i => A * Matrix.single (a i) (σ (a i)) (1 : ℂ)) :=
      iteratedFDeriv_comp_clm F hF L _ _
    rw [h1]
    simp_rw [mul_single_eq]
    rw [ContinuousMultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]
  have hswap : detD (fun T => F (A * T)) = ∑ r : Fin (Fintype.card ι) → ι,
      (∏ i, A (r i) (a i)) * ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        iteratedFDeriv ℂ (Fintype.card ι) F 0 (fun i => Matrix.single (r i) (σ (a i)) (1 : ℂ)) := by
    unfold detD
    rw [Finset.sum_congr rfl fun σ _ => by rw [hΦ σ]]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun σ _ => ?_
    ring
  rw [hswap]
  have hinj : ∀ ρ ∈ (Finset.univ : Finset (Equiv.Perm ι)), ∀ ρ' ∈ (Finset.univ : Finset (Equiv.Perm ι)),
      (fun i => ρ (a i)) = (fun i => ρ' (a i)) → ρ = ρ' := by
    intro ρ _ ρ' _ h
    ext x
    simpa [a] using congrFun h (Fintype.equivFin ι x)
  rw [← Finset.sum_subset (Finset.subset_univ
      ((Finset.univ : Finset (Equiv.Perm ι)).image fun ρ => (fun i => ρ (a i)))),
    Finset.sum_image hinj]
  · have hD : detD F = ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        iteratedFDeriv ℂ (Fintype.card ι) F 0 (fun k => Matrix.single (a k) (σ (a k)) (1 : ℂ)) := rfl
    simp_rw [sum_sign_iteratedFDeriv_single_perm_eq_sign_mul F hF a, ← hD]
    rw [Matrix.det_apply', Finset.sum_mul]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [show (∏ i, A (ρ (a i)) (a i)) = ∏ x, A (ρ x) x from Equiv.prod_comp a (fun x => A (ρ x) x)]
    ring
  · intro r _ hr
    rw [sum_sign_iteratedFDeriv_single_eq_zero_of_not_inj F hF a r ?_, mul_zero]
    intro hr'
    apply hr
    rw [Finset.mem_image]
    refine ⟨Equiv.ofBijective (fun x => r (a.symm x))
      ((hr'.comp a.symm.injective).bijective_of_finite), Finset.mem_univ _, ?_⟩
    funext i
    simp

end PositivityTheory.Rg.Sw.LVs.CEq

namespace PositivityTheory.Rg.Sw.LVs

/- English proof (translation)
The claim follows from `CEq.equivar_thm`.
-/
theorem equivar : Equivar := CEq.equivar_thm

/- English proof (translation)
The claim follows from `CEq.reindex_thm`.
-/
theorem reindex : Reindex := CEq.reindex_thm

end PositivityTheory.Rg.Sw.LVs
