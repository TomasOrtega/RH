import Formalism.LocalToGlobal.CharacterGerms.AltInv

noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries

namespace Formalism.L2.FormalSeriesBounds.AltInv

variable {C : Type*} [Field C] {v : AddValuation C (WithTop ℝ)}

/- English proof (translation)
Use `set L : Matrix σ σ C := Matrix.of fun x y : σ => coeff (Finsupp.single y 1) (Φ x) with hLdef`. Establish `hdet0 : L.det ≠ 0`. Introduce `h0`. Rewrite `hL` using `[h0, AddValuation.map_zero]`. Conclude with `WithTop.top_ne_coe hL`.

Establish `hord : ∀ s, OrdV 1 (t s)` using `fun s μ hμ => by`. Establish `: μ = 0` using `(Finsupp.degree_eq_zero_iff μ).1 (by omega)`. Substitute `this` using the available equality. Simplify using `using ht0 s`. Establish `hs : HasSubst t` using `hasSubst_of_constantCoeff_zero ht0`.

It suffices to establish `key : ∀ E : ℕ, ∀ y, LowLt (v` using `v) E (t y) by`. Introduce `y μ`. Conclude with `key (μ.degree + 1) y μ (Nat.lt_succ_self _)`. Introduce `E`. Proceed by induction on `E with`.

Consider the case `zero => intro y μ h`. Conclude with `absurd h (Nat.not_lt_zero _)`. Consider the case `succ E ih`. Introduce `y μ hμ`. Break down `Nat.lt_succ_iff_lt_or_eq.mp hμ with hlt | heqd` into its components or cases.

Conclude with `ih y μ hlt`. Consider the cases of `E with`. Consider the case `zero`. Establish `: μ = 0` using `(Finsupp.degree_eq_zero_iff μ).1 heqd`. Substitute `this` using the available equality.

Simplify using `[ht0 y, intC_zero]`. Consider the case `succ E'`. Establish `hlow : ∀ s, LowLt (v` using `v) (E' + 1) (t s) := ih`. Establish `hbig : ∀ d : σ →₀ ℕ, 2 ≤ d.degree → IntC v (coeff μ (d.prod fun s n => t s ^ n))`. Introduce `d hd`.

Establish `hp` using `low_prod (v := v) hord hlow d.support d`. Establish `: (d.prod fun s n => t s ^ n) = ∏ s ∈ d.support, t s ^ d s` using `rfl`. Rewrite using `[this]`. Establish `hdeg : d.degree = ∑ s ∈ d.support, d s` using `rfl`. Conclude with `hp.2 μ (by omega)`.

Establish `heqx : ∀ x, ∑ y', L x y' * coeff μ (t y') = coeff μ (G x) - ∑ᶠ d : σ →₀ ℕ, (if d.degree = 1 then 0 else coeff d (Φ x) • coeff μ (d.prod fun s n => t s ^ n))`. Introduce `x`. Establish `h1` using `congrArg (coeff μ) (heq x)`. Rewrite `h1` using `[coeff_subst hs]`. Establish `hfin` using `coeff_subst_finite hs (Φ x) μ`.

Use `set T : (σ →₀ ℕ) → C := fun d => coeff d (Φ x) • coeff μ (d.prod fun s n => t s ^ n) with hT`. Establish `hsplit : ∀ d, T d = (if d.degree = 1 then T d else 0) + (if d.degree = 1 then 0 else T d)`. Apply the tactic sequence `intro d; split_ifs <;> simp`. Establish `hfg : (Function.support fun d => if d.degree = 1 then T d else 0).Finite` using `hfin.subset (fun d hd => by`. Simplify using `only [Function.mem_support] at hd ⊢`.

Use `split_ifs at hd`. Conclude with `hd`. Conclude with `absurd rfl hd)`. Establish `hfh : (Function.support fun d => if d.degree = 1 then 0 else T d).Finite` using `hfin.subset (fun d hd => by`. Simplify using `only [Function.mem_support] at hd ⊢`.

Use `split_ifs at hd`. Conclude with `absurd rfl hd`. Conclude with `hd)`. Establish `h2 : ∑ᶠ d, T d = (∑ᶠ d, if d.degree = 1 then T d else 0) + ∑ᶠ d, (if d.degree = 1 then 0 else T d)`. Rewrite using `[← finsum_add_distrib hfg hfh]`.

Conclude with `finsum_congr hsplit`. Establish `h3 : (∑ᶠ d, if d.degree = 1 then T d else 0) = ∑ y', L x y' * coeff μ (t y')`. Rewrite using `[finsum_eq_sum_of_support_subset _ (s := Finset.univ.image fun y' => Finsupp.single y' 1) (fun d hd => by`. Simplify using `only [Function.mem_support] at hd`. Use `split_ifs at hd with hd1`.

Take `⟨y', rfl⟩` from `deg_one_single d hd1`. Simplify using the standard rewrite rules. Conclude with `absurd rfl hd)]`. Rewrite using `[Finset.sum_image (fun a _ b _ hab => (Finsupp.single_left_inj one_ne_zero).mp hab)]`. Use `Finset.sum_congr rfl fun y' _ => ?_` and prove the remaining obligations.

Rewrite using `[if_pos (by simp), hT]`. Simplify using `only [smul_eq_mul]`. Rewrite using `[Finsupp.prod_single_index (by simp), pow_one]`. Both sides reduce to the same expression. Rewrite `h1` using `[h2, h3]`.

Conclude with `eq_sub_of_add_eq h1`. Establish `hc : ∀ x, IntC v (coeff μ (G x) - ∑ᶠ d : σ →₀ ℕ, (if d.degree = 1 then 0 else coeff d (Φ x) • coeff μ (d.prod fun s n => t s ^ n)))`. Introduce `x`. Use `intC_sub ?_ (intC_finsum fun d => ?_)` and prove the remaining obligations. Conclude with `hG x μ`.

Use `split_ifs with hd1`. Conclude with `intC_zero`. Distinguish the cases in `hd0 : d = 0`. Substitute `hd0` using the available equality. Rewrite using `[coeff_zero_eq_constantCoeff_apply, hΦ0, zero_smul]`.

Conclude with `intC_zero`. Establish `: 2 ≤ d.degree`. Establish `: d.degree ≠ 0` using `fun h0 => hd0 ((Finsupp.degree_eq_zero_iff d).1 h0)`. Use linear arithmetic over natural numbers and integers. Rewrite using `[smul_eq_mul]`.

Conclude with `intC_mul (hΦ x d) (hbig d this)`. Use `set w : σ → C := fun y' => coeff μ (t y') with hw`. Use `set c : σ → C := fun x => coeff μ (G x) - ∑ᶠ d : σ →₀ ℕ, (if d.degree = 1 then 0 else coeff d (Φ x) • coeff μ (d.prod fun s n => t s ^ n)) with hcdef`. Establish `hLw : L.mulVec w = c`. Use function extensionality and compare the values at `x`.

Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `heqx x`. Establish `hunit : IsUnit L.det` using `isUnit_iff_ne_zero.mpr hdet0`. Establish `hwsol : w = L⁻¹.mulVec c`. Rewrite using `[← hLw, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul L hunit, Matrix.one_mulVec]`.

Establish `hinv : ∀ i j, IntC v (L⁻¹ i j)`. Introduce `i j`. Rewrite using `[Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]`. Use `intC_mul ?_ ?_` and prove the remaining obligations. Unfold `IntC`.

Rewrite using `[AddValuation.map_inv, hL]`. Simplify using the standard rewrite rules. Rewrite using `[Matrix.adjugate_apply]`. Use `intC_det _ fun a b => ?_` and prove the remaining obligations. Rewrite using `[Matrix.updateRow_apply]`.

Use `split_ifs`. Rewrite using `[Pi.single_apply]`. Use `split_ifs`. Conclude with `intC_one`. Conclude with `intC_zero`.

Conclude with `hΦ a _`. Establish `: w y = (L⁻¹.mulVec c) y` using `by rw [← hwsol]`. Use `show IntC v (w y)`. Rewrite using `[this]`. Simplify using `only [Matrix.mulVec, dotProduct]`.

Conclude with `intC_sum _ fun x _ => intC_mul (hinv y x) (hc x)`.
-/
theorem intS_invG {σ : Type*} [Fintype σ] (Φ t G : σ → MvPowerSeries σ C) (hΦ0 : ∀ x, constantCoeff (Φ x) = 0)
    (hΦ : ∀ x, IntS v (Φ x))
    (hL : v (Matrix.of fun x y : σ => coeff (Finsupp.single y 1) (Φ x)).det = 0)
    (ht0 : ∀ y, constantCoeff (t y) = 0) (hG : ∀ x, IntS v (G x)) (heq : ∀ x, subst t (Φ x) = G x) :
    ∀ y, IntS v (t y) := by
  set L : Matrix σ σ C := Matrix.of fun x y : σ => coeff (Finsupp.single y 1) (Φ x) with hLdef
  have hdet0 : L.det ≠ 0 := by
    intro h0; rw [h0, AddValuation.map_zero] at hL; exact WithTop.top_ne_coe hL
  have hord : ∀ s, OrdV 1 (t s) := fun s μ hμ => by
    have : μ = 0 := (Finsupp.degree_eq_zero_iff μ).1 (by omega)
    subst this; simpa using ht0 s
  have hs : HasSubst t := hasSubst_of_constantCoeff_zero ht0
  suffices key : ∀ E : ℕ, ∀ y, LowLt (v := v) E (t y) by
    intro y μ; exact key (μ.degree + 1) y μ (Nat.lt_succ_self _)
  intro E
  induction E with
  | zero => intro y μ h; exact absurd h (Nat.not_lt_zero _)
  | succ E ih =>
    intro y μ hμ
    rcases Nat.lt_succ_iff_lt_or_eq.mp hμ with hlt | heqd
    · exact ih y μ hlt

    cases E with
    | zero =>
      have : μ = 0 := (Finsupp.degree_eq_zero_iff μ).1 heqd
      subst this; simp [ht0 y, intC_zero]
    | succ E' =>

      have hlow : ∀ s, LowLt (v := v) (E' + 1) (t s) := ih
      have hbig : ∀ d : σ →₀ ℕ, 2 ≤ d.degree → IntC v (coeff μ (d.prod fun s n => t s ^ n)) := by
        intro d hd
        have hp := low_prod (v := v) hord hlow d.support d
        have : (d.prod fun s n => t s ^ n) = ∏ s ∈ d.support, t s ^ d s := rfl
        rw [this]
        have hdeg : d.degree = ∑ s ∈ d.support, d s := rfl
        exact hp.2 μ (by omega)

      have heqx : ∀ x, ∑ y', L x y' * coeff μ (t y') = coeff μ (G x) -
          ∑ᶠ d : σ →₀ ℕ, (if d.degree = 1 then 0 else
            coeff d (Φ x) • coeff μ (d.prod fun s n => t s ^ n)) := by
        intro x
        have h1 := congrArg (coeff μ) (heq x)
        rw [coeff_subst hs] at h1
        have hfin := coeff_subst_finite hs (Φ x) μ
        set T : (σ →₀ ℕ) → C := fun d => coeff d (Φ x) • coeff μ (d.prod fun s n => t s ^ n) with hT
        have hsplit : ∀ d, T d = (if d.degree = 1 then T d else 0) + (if d.degree = 1 then 0 else T d) := by
          intro d; split_ifs <;> simp
        have hfg : (Function.support fun d => if d.degree = 1 then T d else 0).Finite :=
          hfin.subset (fun d hd => by
            simp only [Function.mem_support] at hd ⊢; split_ifs at hd; exact hd; exact absurd rfl hd)
        have hfh : (Function.support fun d => if d.degree = 1 then 0 else T d).Finite :=
          hfin.subset (fun d hd => by
            simp only [Function.mem_support] at hd ⊢; split_ifs at hd; exact absurd rfl hd; exact hd)
        have h2 : ∑ᶠ d, T d = (∑ᶠ d, if d.degree = 1 then T d else 0) +
            ∑ᶠ d, (if d.degree = 1 then 0 else T d) := by
          rw [← finsum_add_distrib hfg hfh]; exact finsum_congr hsplit
        have h3 : (∑ᶠ d, if d.degree = 1 then T d else 0) = ∑ y', L x y' * coeff μ (t y') := by
          rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ.image fun y' => Finsupp.single y' 1)
            (fun d hd => by
              simp only [Function.mem_support] at hd
              split_ifs at hd with hd1
              · obtain ⟨y', rfl⟩ := deg_one_single d hd1
                simp
              · exact absurd rfl hd)]
          rw [Finset.sum_image (fun a _ b _ hab => (Finsupp.single_left_inj one_ne_zero).mp hab)]
          refine Finset.sum_congr rfl fun y' _ => ?_
          rw [if_pos (by simp), hT]
          simp only [smul_eq_mul]
          rw [Finsupp.prod_single_index (by simp), pow_one]
          rfl
        rw [h2, h3] at h1
        exact eq_sub_of_add_eq h1

      have hc : ∀ x, IntC v (coeff μ (G x) -
          ∑ᶠ d : σ →₀ ℕ, (if d.degree = 1 then 0 else
            coeff d (Φ x) • coeff μ (d.prod fun s n => t s ^ n))) := by
        intro x
        refine intC_sub ?_ (intC_finsum fun d => ?_)
        · exact hG x μ
        · split_ifs with hd1
          · exact intC_zero
          · by_cases hd0 : d = 0
            · subst hd0; rw [coeff_zero_eq_constantCoeff_apply, hΦ0, zero_smul]; exact intC_zero
            · have : 2 ≤ d.degree := by
                have : d.degree ≠ 0 := fun h0 => hd0 ((Finsupp.degree_eq_zero_iff d).1 h0)
                omega
              rw [smul_eq_mul]; exact intC_mul (hΦ x d) (hbig d this)

      set w : σ → C := fun y' => coeff μ (t y') with hw
      set c : σ → C := fun x => coeff μ (G x) -
          ∑ᶠ d : σ →₀ ℕ, (if d.degree = 1 then 0 else
            coeff d (Φ x) • coeff μ (d.prod fun s n => t s ^ n)) with hcdef
      have hLw : L.mulVec w = c := by
        funext x; simp only [Matrix.mulVec, dotProduct]; exact heqx x
      have hunit : IsUnit L.det := isUnit_iff_ne_zero.mpr hdet0
      have hwsol : w = L⁻¹.mulVec c := by
        rw [← hLw, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul L hunit, Matrix.one_mulVec]
      have hinv : ∀ i j, IntC v (L⁻¹ i j) := by
        intro i j
        rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
        refine intC_mul ?_ ?_
        · unfold IntC; rw [AddValuation.map_inv, hL]; simp
        · rw [Matrix.adjugate_apply]
          refine intC_det _ fun a b => ?_
          rw [Matrix.updateRow_apply]
          split_ifs
          · rw [Pi.single_apply]; split_ifs; exact intC_one; exact intC_zero
          · exact hΦ a _
      have : w y = (L⁻¹.mulVec c) y := by rw [← hwsol]
      show IntC v (w y)
      rw [this]
      simp only [Matrix.mulVec, dotProduct]
      exact intC_sum _ fun x _ => intC_mul (hinv y x) (hc x)

end Formalism.L2.FormalSeriesBounds.AltInv
