import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
import Formalism.LocalToGlobal.Columns.PolyFn
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

/- English proof (translation)
Establish `hfix : ∀ t : ℂ, rowAct ℂ (lfockq_mat a b t) q = q`. Introduce `t`. Establish `htri : (lfockq_mat a b t).transpose.BlockTriangular id`. Introduce `i j hij`. Establish `hij' : j < i` using `hij`.

Simplify using `only [Matrix.transpose_apply, lfockq_mat]`. Rewrite using `[if_neg hij'.ne, if_neg, add_zero]`. Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `lt_asymm hab hij'`. Establish `hdiag : ∀ i, (lfockq_mat a b t).transpose i i = 1`.

Introduce `i`. Simplify using `only [Matrix.transpose_apply, lfockq_mat]`. Rewrite using `[if_pos trivial, if_neg, add_zero]`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `hab.ne (h2.symm.trans h1)`.

Establish `hdet : (lfockq_mat a b t).transpose.det = 1`. Rewrite using `[Matrix.det_of_upperTriangular htri]`. Simplify using `only [hdiag, Finset.prod_const_one]`. Set `g : GL (Fin n) ℂ` to `Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hdet ▸ one_ne_zero : (lfockq_mat a b t).transpose.det ≠ 0)`. Establish `hg : (g : Matrix (Fin n) (Fin n) ℂ) = (lfockq_mat a b t).transpose` using `rfl`.

Establish `hd : Matrix.GeneralLinearGroup.det g = 1`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, hg, hdet, Units.val_one]`. Use `hq g htri hdiag` as an intermediate fact. Unfold `sqAct at this`.

Rewrite `this` using `[detPow, hd, one_zpow, Units.val_one, one_smul, hg, Matrix.transpose_transpose]`. Then use the resulting hypothesis. Establish `hP : rowGen ℂ a b q = Polynomial.C q`. Apply `Polynomial.eq_of_infinite_eval_eq` to reduce the goal to its premises. Use `Set.Infinite.mono ?_ (Set.infinite_range_of_injective (C_injective (Fin n × Fin n) ℂ))` and prove the remaining obligations. Introduce and unpack `_ ⟨t, rfl⟩`.

Use `show Polynomial.eval _ _ = Polynomial.eval _ _`. Rewrite using `[lfockq_eval_rowGen, hfix, Polynomial.eval_C]`. Rewrite using `[rowDiv, hP, Polynomial.coeff_C, if_neg (by omega)]`.
-/
theorem rowDiv_eq_zero_of_unipotent_fixed {n : ℕ} (nu : DomWeight n) (q : MvPolynomial (Fin n × Fin n) ℂ)
    (hq : ∀ g : GL (Fin n) ℂ, (g : Matrix (Fin n) (Fin n) ℂ).BlockTriangular id →
      (∀ a, (g : Matrix (Fin n) (Fin n) ℂ) a a = 1) → sqAct ℂ n nu g q = q)
    (a b : Fin n) (hab : a < b) (k : ℕ) (hk : 1 ≤ k) : rowDiv ℂ a b k q = 0 := by
  have hfix : ∀ t : ℂ, rowAct ℂ (lfockq_mat a b t) q = q := by
    intro t
    have htri : (lfockq_mat a b t).transpose.BlockTriangular id := by
      intro i j hij
      have hij' : j < i := hij
      simp only [Matrix.transpose_apply, lfockq_mat]
      rw [if_neg hij'.ne, if_neg, add_zero]
      rintro ⟨rfl, rfl⟩
      exact lt_asymm hab hij'
    have hdiag : ∀ i, (lfockq_mat a b t).transpose i i = 1 := by
      intro i
      simp only [Matrix.transpose_apply, lfockq_mat]
      rw [if_pos trivial, if_neg, add_zero]
      rintro ⟨h1, h2⟩
      exact hab.ne (h2.symm.trans h1)
    have hdet : (lfockq_mat a b t).transpose.det = 1 := by
      rw [Matrix.det_of_upperTriangular htri]
      simp only [hdiag, Finset.prod_const_one]
    let g : GL (Fin n) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hdet ▸ one_ne_zero :
      (lfockq_mat a b t).transpose.det ≠ 0)
    have hg : (g : Matrix (Fin n) (Fin n) ℂ) = (lfockq_mat a b t).transpose := rfl
    have hd : Matrix.GeneralLinearGroup.det g = 1 := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, hg, hdet, Units.val_one]
    have := hq g htri hdiag
    unfold sqAct at this
    rwa [detPow, hd, one_zpow, Units.val_one, one_smul, hg, Matrix.transpose_transpose] at this
  have hP : rowGen ℂ a b q = Polynomial.C q := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective
      (C_injective (Fin n × Fin n) ℂ))
    rintro _ ⟨t, rfl⟩
    show Polynomial.eval _ _ = Polynomial.eval _ _
    rw [lfockq_eval_rowGen, hfix, Polynomial.eval_C]
  rw [rowDiv, hP, Polynomial.coeff_C, if_neg (by omega)]

/- English proof (translation)
Set `f : nablaSq ℂ n mu` to `⟨extremal ℂ n mu, hwMem ℂ n n le_rfl _ (factNatW n mu).1⟩`. Use `⟨f, fun h => hwNe ℂ n n le_rfl mu.natW (congrArg Subtype.val h), ?_⟩` and prove the remaining obligations. Establish `hint : ∀ g x, φ (sqRep ℂ n mu g x) = sqRep ℂ n nu g (φ x)` using `fun g x => Representation.IntertwiningMap.isIntertwining _ _ φ g x`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c : ℂ, (φ f : MvPolynomial (Fin n × Fin n) ℂ) = c • extremal ℂ n nu := by`. Apply `hwLine ℂ n n le_rfl nu.natW (factNatW n nu).1 _ (φ f).2` to reduce the goal to its premises.

Introduce `a b hab k hk`. Use `rowDiv_eq_zero_of_unipotent_fixed nu _ (fun g h1 h2 => ?_) a b hab k hk` and prove the remaining obligations. Establish `e : sqRep ℂ n mu g f = f` using `Subtype.ext ((factSqHighestWeight ℂ n mu).2 g h1 h2)`. Rewrite using `[← sqRep_coe, ← hint, e]`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, mu.w i ≠ nu.w i := by`.

Assume the negation of the conclusion as `h`. Use `push Not at h`. Apply `hne` to reduce the goal to its premises. Take `⟨w, hw⟩` from `mu`. Take `⟨w', hw'⟩` from `nu`.

Establish `: w = w'` using `funext h`. Substitute `this` using the available equality. Both sides reduce to the same expression. Set `u : ℂˣ` to `Units.mk0 2 two_ne_zero`. Set `t : Fin n → ℂˣ` to `fun a => if a = i then u else 1`.

Establish `hprod : ∀ lam : DomWeight n, ((∏ a, (t a) ^ (lam.w a) : ℂˣ) : ℂ) = (2 : ℂ) ^ lam.w i`. Introduce `lam`. Rewrite using `[Finset.prod_eq_single i (fun b _ hb => by simp [t, hb]) (by simp)]`. Simplify using `[t, u]`. Establish `e : sqRep ℂ n mu (diagGL ℂ n t) f = (2 : ℂ) ^ mu.w i • f`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hprod]`. Conclude with `(factSqHighestWeight ℂ n mu).1 t`. Establish `e2 : sqRep ℂ n nu (diagGL ℂ n t) (φ f) = (2 : ℂ) ^ nu.w i • φ f`. Set `h : nablaSq ℂ n nu` to `⟨extremal ℂ n nu, hwMem ℂ n n le_rfl _ (factNatW n nu).1⟩`.

Establish `hc' : φ f = c • h` using `Subtype.ext hc`. Establish `e3 : sqRep ℂ n nu (diagGL ℂ n t) h = (2 : ℂ) ^ nu.w i • h`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hprod]`. Conclude with `(factSqHighestWeight ℂ n nu).1 t`.

Rewrite using `[hc', map_smul, e3, smul_comm]`. Establish `e4` using `hint (diagGL ℂ n t) f`. Rewrite `e4` using `[e, e2, map_smul, ← sub_eq_zero, ← sub_smul, smul_eq_zero, sub_eq_zero]`. Use `e4.resolve_left fun h => hi ?_` and prove the remaining obligations. Establish `h' : ((2 : ℝ) ^ mu.w i) = (2 : ℝ) ^ nu.w i`.

Simplify `congrArg norm h` using `[norm_zpow]`. Conclude with `zpow_right_injective₀ (by norm_num) (by norm_num) h'`.
-/
theorem exists_ne_zero_map_eq_zero_of_weight_ne (n : ℕ) (mu nu : DomWeight n) (hne : mu ≠ nu)
    (φ : (sqRep ℂ n mu).IntertwiningMap (sqRep ℂ n nu)) :
    ∃ f : nablaSq ℂ n mu, f ≠ 0 ∧ φ f = 0 := by
  let f : nablaSq ℂ n mu := ⟨extremal ℂ n mu, hwMem ℂ n n le_rfl _ (factNatW n mu).1⟩
  refine ⟨f, fun h => hwNe ℂ n n le_rfl mu.natW (congrArg Subtype.val h), ?_⟩
  have hint : ∀ g x, φ (sqRep ℂ n mu g x) = sqRep ℂ n nu g (φ x) := fun g x =>
    Representation.IntertwiningMap.isIntertwining _ _ φ g x
  obtain ⟨c, hc⟩ : ∃ c : ℂ, (φ f : MvPolynomial (Fin n × Fin n) ℂ) = c • extremal ℂ n nu := by
    apply hwLine ℂ n n le_rfl nu.natW (factNatW n nu).1 _ (φ f).2
    intro a b hab k hk
    refine rowDiv_eq_zero_of_unipotent_fixed nu _ (fun g h1 h2 => ?_) a b hab k hk
    have e : sqRep ℂ n mu g f = f := Subtype.ext ((factSqHighestWeight ℂ n mu).2 g h1 h2)
    rw [← sqRep_coe, ← hint, e]
  obtain ⟨i, hi⟩ : ∃ i, mu.w i ≠ nu.w i := by
    by_contra h
    push Not at h
    apply hne
    obtain ⟨w, hw⟩ := mu
    obtain ⟨w', hw'⟩ := nu
    have : w = w' := funext h
    subst this
    rfl
  let u : ℂˣ := Units.mk0 2 two_ne_zero
  let t : Fin n → ℂˣ := fun a => if a = i then u else 1
  have hprod : ∀ lam : DomWeight n, ((∏ a, (t a) ^ (lam.w a) : ℂˣ) : ℂ) = (2 : ℂ) ^ lam.w i := by
    intro lam
    rw [Finset.prod_eq_single i (fun b _ hb => by simp [t, hb]) (by simp)]
    simp [t, u]
  have e : sqRep ℂ n mu (diagGL ℂ n t) f = (2 : ℂ) ^ mu.w i • f := by
    apply Subtype.ext
    rw [← hprod]
    exact (factSqHighestWeight ℂ n mu).1 t
  have e2 : sqRep ℂ n nu (diagGL ℂ n t) (φ f) = (2 : ℂ) ^ nu.w i • φ f := by
    let h : nablaSq ℂ n nu := ⟨extremal ℂ n nu, hwMem ℂ n n le_rfl _ (factNatW n nu).1⟩
    have hc' : φ f = c • h := Subtype.ext hc
    have e3 : sqRep ℂ n nu (diagGL ℂ n t) h = (2 : ℂ) ^ nu.w i • h := by
      apply Subtype.ext
      rw [← hprod]
      exact (factSqHighestWeight ℂ n nu).1 t
    rw [hc', map_smul, e3, smul_comm]
  have e4 := hint (diagGL ℂ n t) f
  rw [e, e2, map_smul, ← sub_eq_zero, ← sub_smul, smul_eq_zero, sub_eq_zero] at e4
  refine e4.resolve_left fun h => hi ?_
  have h' : ((2 : ℝ) ^ mu.w i) = (2 : ℝ) ^ nu.w i := by
    simpa [norm_zpow] using congrArg norm h
  exact zpow_right_injective₀ (by norm_num) (by norm_num) h'

end GlobalTheory.Branching
