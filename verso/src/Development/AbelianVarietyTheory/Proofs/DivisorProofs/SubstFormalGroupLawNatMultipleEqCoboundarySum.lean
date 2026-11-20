import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog.NmulSubst

/- English proof (translation)
Establish `ha : HasSubst (fun _ : σ => (0 : MvPowerSeries τ R))` using `hasSubst_of_constantCoeff_zero fun _ => map_zero _`. Use extensionality with `e`. Rewrite using `[coeff_subst ha, finsum_eq_single _ 0]`. Rewrite using `[Finsupp.prod_zero_index, coeff_one, coeff_C, coeff_zero_eq_constantCoeff_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Introduce `x hx`. Take `⟨i, hi⟩ : ∃ i, x i ≠ 0` from `by by_contra! hc`. Conclude with `hx (Finsupp.ext hc)`. Establish `: (x.prod fun _ n => (0 : MvPowerSeries τ R) ^ n) = 0` using `Finset.prod_eq_zero (i := i) (Finsupp.mem_support_iff.2 hi) (zero_pow hi)`. Rewrite using `[this, map_zero, smul_zero]`.
-/
theorem subst_zero_fun {R : Type} [CommRing R] {σ τ : Type} [Finite σ] (g : MvPowerSeries σ R) :
    subst (fun _ : σ => (0 : MvPowerSeries τ R)) g = C (constantCoeff g) := by
  have ha : HasSubst (fun _ : σ => (0 : MvPowerSeries τ R)) :=
    hasSubst_of_constantCoeff_zero fun _ => map_zero _
  ext e
  rw [coeff_subst ha, finsum_eq_single _ 0]
  · classical
    rw [Finsupp.prod_zero_index, coeff_one, coeff_C, coeff_zero_eq_constantCoeff_apply]
    split_ifs <;> simp
  · intro x hx
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra! hc
      exact hx (Finsupp.ext hc)
    have : (x.prod fun _ n => (0 : MvPowerSeries τ R) ^ n) = 0 :=
      Finset.prod_eq_zero (i := i) (Finsupp.mem_support_iff.2 hi) (zero_pow hi)
    rw [this, map_zero, smul_zero]

/- English proof (translation)
Unfold `nmul`. Conclude with `Function.iterate_succ_apply' _ _ _`.
-/
theorem nmul_succ {R : Type} [CommRing R] {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (k : ℕ) : nmul μ (k + 1) = op μ (nmul μ k) (fun i => X i) := by
  unfold nmul
  exact Function.iterate_succ_apply' _ _ _

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => intro i`. Simplify using `[nmul]`. Consider the case `succ k ih`. Introduce `i`.

Rewrite using `[nmul_succ]`. Establish `hs : ∀ j, constantCoeff (Sum.elim (nmul μ k) (fun i => (X i : MvPowerSeries (Fin d) R)) j) = 0`. Introduce and unpack `(j | j)`. Conclude with `ih j`. Conclude with `constantCoeff_X _`.

Conclude with `constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hs) hs (hμ i)`.
-/
theorem constantCoeff_nmul {R : Type} [CommRing R] {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) :
    ∀ i, constantCoeff (nmul μ n i) = 0 := by
  induction n with
  | zero => intro i; simp [nmul]
  | succ k ih =>
    intro i
    rw [nmul_succ]
    have hs : ∀ j, constantCoeff (Sum.elim (nmul μ k) (fun i => (X i : MvPowerSeries (Fin d) R)) j) = 0 := by
      rintro (j | j)
      · exact ih j
      · exact constantCoeff_X _
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hs) hs (hμ i)

end GlobalTheory.QLog.NmulSubst

open GlobalTheory.QLog.NmulSubst in

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Establish `: nmul μ 0 = fun _ => 0` using `rfl`. Rewrite using `[this, subst_zero_fun]`. Simplify using the standard rewrite rules.

Consider the case `succ k ih`. Establish `hE : ∀ j, constantCoeff (Sum.elim (nmul μ k) (fun i => (X i : MvPowerSeries (Fin d) R)) j) = 0`. Introduce and unpack `(j | j)`. Conclude with `constantCoeff_nmul μ hμ k j`. Conclude with `constantCoeff_X _`.

Establish `hsE` using `hasSubst_of_constantCoeff_zero hE`. Establish `hμs : HasSubst μ` using `hasSubst_of_constantCoeff_zero hμ`. Establish `hX : ∀ (f : Fin d → Fin d ⊕ Fin d), HasSubst (fun i => (X (f i) : MvPowerSeries (Fin d ⊕ Fin d) R))` using `fun _ => hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _`. Rewrite using `[nmul_succ]`. Express the relevant statement in the definitionally equal form `subst (fun i => subst (Sum.elim (nmul μ k) fun i => X i) (μ i)) g = _`.

Rewrite using `[← subst_comp_subst_apply hμs hsE]`. Establish `hsplit : subst μ g = cob1 μ g + inL g + inR g` using `by unfold cob1; abel`. Establish `hL : subst (Sum.elim (nmul μ k) fun i => (X i : MvPowerSeries (Fin d) R)) (inL g) =`. Substitute `(nmul μ k) g := by` using the available equality. Unfold `inL`.

Rewrite using `[subst_comp_subst_apply (hX Sum.inl) hsE]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[subst_X hsE]`. Both sides reduce to the same expression.

Establish `hR : subst (Sum.elim (nmul μ k) fun i => (X i : MvPowerSeries (Fin d) R)) (inR g) = g`. Unfold `inR`. Rewrite using `[subst_comp_subst_apply (hX Sum.inr) hsE]`. Establish `: (fun i => subst (Sum.elim (nmul μ k) fun i => (X i : MvPowerSeries (Fin d) R)) (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) = X`. Use function extensionality and compare the values at `i`.

Rewrite using `[subst_X hsE]`. Both sides reduce to the same expression. Rewrite using `[this, subst_self]`. Both sides reduce to the same expression. Rewrite using `[hsplit, subst_add hsE, subst_add hsE, hL, hR, ih, Finset.sum_range_succ]`.

Express the relevant statement in the definitionally equal form `_ = _ + _ + (_ + subst (Sum.elim (nmul μ k) fun i => X i) (cob1 μ g))`. Use `push_cast`. Rewrite using `[add_smul, one_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem GlobalTheory.QLog.subst_nmul_eq (R : Type) [CommRing R] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (g : MvPowerSeries (Fin d) R) (n : ℕ) :
    subst (nmul μ n) g = C (constantCoeff g) + (n : R) • g +
      ∑ k ∈ Finset.range n, at2 (cob1 μ g) (nmul μ k) (fun i => X i) := by
  induction n with
  | zero =>
    have : nmul μ 0 = fun _ => 0 := rfl
    rw [this, subst_zero_fun]
    simp
  | succ k ih =>
    have hE : ∀ j, constantCoeff (Sum.elim (nmul μ k) (fun i => (X i : MvPowerSeries (Fin d) R)) j) = 0 := by
      rintro (j | j)
      · exact constantCoeff_nmul μ hμ k j
      · exact constantCoeff_X _
    have hsE := hasSubst_of_constantCoeff_zero hE
    have hμs : HasSubst μ := hasSubst_of_constantCoeff_zero hμ
    have hX : ∀ (f : Fin d → Fin d ⊕ Fin d),
        HasSubst (fun i => (X (f i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
      fun _ => hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
    rw [nmul_succ]
    change subst (fun i => subst (Sum.elim (nmul μ k) fun i => X i) (μ i)) g = _
    rw [← subst_comp_subst_apply hμs hsE]
    have hsplit : subst μ g = cob1 μ g + inL g + inR g := by unfold cob1; abel
    have hL : subst (Sum.elim (nmul μ k) fun i => (X i : MvPowerSeries (Fin d) R)) (inL g) =
        subst (nmul μ k) g := by
      unfold inL
      rw [subst_comp_subst_apply (hX Sum.inl) hsE]
      congr 1
      funext i
      rw [subst_X hsE]
      rfl
    have hR : subst (Sum.elim (nmul μ k) fun i => (X i : MvPowerSeries (Fin d) R)) (inR g) = g := by
      unfold inR
      rw [subst_comp_subst_apply (hX Sum.inr) hsE]
      have : (fun i => subst (Sum.elim (nmul μ k) fun i => (X i : MvPowerSeries (Fin d) R))
          (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) = X := by
        funext i
        rw [subst_X hsE]
        rfl
      rw [this, subst_self]
      rfl
    rw [hsplit, subst_add hsE, subst_add hsE, hL, hR, ih, Finset.sum_range_succ]
    change _ = _ + _ + (_ + subst (Sum.elim (nmul μ k) fun i => X i) (cob1 μ g))
    push_cast
    rw [add_smul, one_smul]
    abel
