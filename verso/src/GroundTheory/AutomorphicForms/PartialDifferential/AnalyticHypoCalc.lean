import Mathlib
import GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoBasic

namespace GroundTheory.Automorphic.Sobolev

open scoped ContDiff

noncomputable section

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin n)

/- English proof (translation)
Establish `h : ContDiff ℝ ∞ (iteratedFDeriv ℝ k f)`. Use `contDiff_infty.2 fun m ↦ hf.iteratedFDeriv_right ?_` and prove the remaining obligations. Conclude with `(le_top : ((m + k : ℕ) : ℕ∞) ≤ ⊤)` after adjusting the coercions. Conclude with `(ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ 𝔼) ℂ v).contDiff.comp h`.
-/
theorem contDiff_dT {f : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) {k : ℕ} (v : Fin k → 𝔼) :
    ContDiff ℝ ∞ (dT v f) := by
  have h : ContDiff ℝ ∞ (iteratedFDeriv ℝ k f) := by
    refine contDiff_infty.2 fun m ↦ hf.iteratedFDeriv_right ?_
    exact_mod_cast (le_top : ((m + k : ℕ) : ℕ∞) ≤ ⊤)
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ 𝔼) ℂ v).contDiff.comp h

/- English proof (translation)
The claim follows from `contDiff_dT hf _`.
-/
theorem contDiff_pdT {f : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) {k : ℕ} (J : Fin k → Fin n) :
    ContDiff ℝ ∞ (pdT J f) :=
  contDiff_dT hf _

/- English proof (translation)
The claim follows from `(contDiff_infty_iff_fderiv.1 hf).2`.
-/
theorem contDiff_fderiv {f : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (fderiv ℝ f) :=
  (contDiff_infty_iff_fderiv.1 hf).2

/- English proof (translation)
The claim follows from `(contDiff_fderiv hf).clm_apply contDiff_const`.
-/
theorem contDiff_fderiv_apply {f : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) (a : 𝔼) :
    ContDiff ℝ ∞ (fun x ↦ fderiv ℝ f x a) :=
  (contDiff_fderiv hf).clm_apply contDiff_const

/- English proof (translation)
The claim follows from `contDiff_fderiv_apply hf _`.
-/
theorem contDiff_pd {f : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) (i : Fin n) : ContDiff ℝ ∞ (pd i f) :=
  contDiff_fderiv_apply hf _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pderiv_eq_dT' (α : Fin n → ℕ) (f : 𝔼 → ℂ) : pderiv α f = dT (mdir α) f := rfl

/- English proof (translation)
The claim follows from `contDiff_dT hf _`.
-/
theorem contDiff_pderiv {f : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) (α : Fin n → ℕ) :
    ContDiff ℝ ∞ (pderiv α f) :=
  contDiff_dT hf _

/- English proof (translation)
Use function extensionality and compare the values at `x`. Establish `hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) x` using `(hf.differentiable_iteratedFDeriv (m := k) (by exact_mod_cast WithTop.coe_lt_top _)) x`. Rewrite using `[dT, iteratedFDeriv_succ_apply_left, Fin.cons_zero, Fin.tail_cons]`. Conclude with `(fderiv_continuousMultilinear_apply_const_apply hd v a).symm`.
-/
theorem dT_cons {f : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) {k : ℕ} (a : 𝔼) (v : Fin k → 𝔼) :
    dT (Fin.cons a v) f = fun x ↦ fderiv ℝ (dT v f) x a := by
  funext x
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) x :=
    (hf.differentiable_iteratedFDeriv (m := k) (by exact_mod_cast WithTop.coe_lt_top _)) x
  rw [dT, iteratedFDeriv_succ_apply_left, Fin.cons_zero, Fin.tail_cons]
  exact (fderiv_continuousMultilinear_apply_const_apply hd v a).symm

/- English proof (translation)
Use function extensionality and compare the values at `x`. Rewrite using `[dT, iteratedFDeriv_succ_apply_right, Fin.init_snoc, Fin.snoc_last]`. Establish `h1 : (fun y ↦ fderiv ℝ f y a) = (ContinuousLinearMap.apply ℝ ℂ a) ∘ (fun y ↦ fderiv ℝ f y)` using `rfl`. Establish `hfd : ContDiff ℝ ∞ (fun y ↦ fderiv ℝ f y)` using `contDiff_fderiv hf`. Rewrite using `[dT, h1, (ContinuousLinearMap.apply ℝ ℂ a).iteratedFDeriv_comp_left hfd.contDiffAt (by exact_mod_cast le_top)]`.

Both sides reduce to the same expression.
-/
theorem dT_snoc {f : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) {k : ℕ} (v : Fin k → 𝔼) (a : 𝔼) :
    dT (Fin.snoc v a) f = dT v (fun x ↦ fderiv ℝ f x a) := by
  funext x
  rw [dT, iteratedFDeriv_succ_apply_right, Fin.init_snoc, Fin.snoc_last]
  have h1 : (fun y ↦ fderiv ℝ f y a) =
      (ContinuousLinearMap.apply ℝ ℂ a) ∘ (fun y ↦ fderiv ℝ f y) := rfl
  have hfd : ContDiff ℝ ∞ (fun y ↦ fderiv ℝ f y) := contDiff_fderiv hf
  rw [dT, h1, (ContinuousLinearMap.apply ℝ ℂ a).iteratedFDeriv_comp_left hfd.contDiffAt
    (by exact_mod_cast le_top)]
  rfl

/- English proof (translation)
Establish `h : (fun l ↦ ev (Fin.snoc (α` using `fun _ ↦ Fin n) J i l)) = Fin.snoc (fun l ↦ ev (J l)) (ev i : 𝔼) := by`. Use function extensionality and compare the values at `l`. Apply the tactic sequence `refine Fin.lastCases ?_ (fun j ↦ ?_) l <;> simp`. Rewrite using `[pdT, h, dT_snoc hf]`. Both sides reduce to the same expression.
-/
theorem pdT_snoc {f : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) {k : ℕ} (J : Fin k → Fin n) (i : Fin n) :
    pdT (Fin.snoc J i) f = pdT J (pd i f) := by
  have h : (fun l ↦ ev (Fin.snoc (α := fun _ ↦ Fin n) J i l)) =
      Fin.snoc (fun l ↦ ev (J l)) (ev i : 𝔼) := by
    funext l
    refine Fin.lastCases ?_ (fun j ↦ ?_) l <;> simp
  rw [pdT, h, dT_snoc hf]
  rfl

/- English proof (translation)
Establish `h : (fun l ↦ ev (Fin.cons (α` using `fun _ ↦ Fin n) i J l)) = Fin.cons (ev i : 𝔼) (fun l ↦ ev (J l)) := by`. Use function extensionality and compare the values at `l`. Apply the tactic sequence `refine Fin.cases ?_ (fun j ↦ ?_) l <;> simp`. Rewrite using `[pdT, h, dT_cons hf]`. Both sides reduce to the same expression.
-/
theorem pdT_cons {f : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) {k : ℕ} (i : Fin n) (J : Fin k → Fin n) :
    pdT (Fin.cons i J) f = pd i (pdT J f) := by
  have h : (fun l ↦ ev (Fin.cons (α := fun _ ↦ Fin n) i J l)) =
      Fin.cons (ev i : 𝔼) (fun l ↦ ev (J l)) := by
    funext l
    refine Fin.cases ?_ (fun j ↦ ?_) l <;> simp
  rw [pdT, h, dT_cons hf]
  rfl

/- English proof (translation)
Establish `hd : DifferentiableAt ℝ (fderiv ℝ g) x` using `(contDiff_fderiv hg).differentiable (by simp) x`. Establish `e : ∀ c d : 𝔼, fderiv ℝ (fun y ↦ fderiv ℝ g y d) x c = fderiv ℝ (fderiv ℝ g) x c d`. Introduce `c d`. Rewrite using `[fderiv_clm_apply hd (differentiableAt_const d)]`. Simplify using the standard rewrite rules.

Rewrite using `[e, e]`. Conclude with `((contDiff_infty.1 hg 2).contDiffAt.isSymmSndFDerivAt (by simp)) a b`.
-/
theorem fderiv_fderiv_apply_comm {g : 𝔼 → ℂ} (hg : ContDiff ℝ ∞ g) (x a b : 𝔼) :
    fderiv ℝ (fun y ↦ fderiv ℝ g y b) x a = fderiv ℝ (fun y ↦ fderiv ℝ g y a) x b := by
  have hd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (contDiff_fderiv hg).differentiable (by simp) x
  have e : ∀ c d : 𝔼, fderiv ℝ (fun y ↦ fderiv ℝ g y d) x c = fderiv ℝ (fderiv ℝ g) x c d := by
    intro c d
    rw [fderiv_clm_apply hd (differentiableAt_const d)]
    simp
  rw [e, e]
  exact ((contDiff_infty.1 hg 2).contDiffAt.isSymmSndFDerivAt (by simp)) a b

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Introduce `f _`. Establish `: (Fin.cons a w : Fin 1 → 𝔼) = Fin.snoc w a`. Use function extensionality and compare the values at `i`.

Use `fin_cases i`. Both sides reduce to the same expression. Rewrite using `[this]`. Consider the case `succ k ih`. Introduce `f hf`.

Rewrite using `[← Fin.cons_self_tail w]`. Use `set b := w 0`. Use `set w' := Fin.tail w`. Establish `h1 : dT (Fin.cons a (Fin.cons b w')) f = fun x ↦ fderiv ℝ (fun y ↦ fderiv ℝ (dT w' f) y a) x b`. Rewrite using `[dT_cons hf, dT_cons hf]`.

Use function extensionality and compare the values at `x`. Conclude with `fderiv_fderiv_apply_comm (contDiff_dT hf w') x a b`. Establish `h2 : (fun y ↦ fderiv ℝ (dT w' f) y a) = dT (Fin.snoc w' a) f`. Rewrite using `[← ih w' hf, dT_cons hf]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem dT_cons_eq_snoc {k : ℕ} (a : 𝔼) (w : Fin k → 𝔼) :
    ∀ {f : 𝔼 → ℂ}, ContDiff ℝ ∞ f → dT (Fin.cons a w) f = dT (Fin.snoc w a) f := by
  induction k with
  | zero =>
    intro f _
    have : (Fin.cons a w : Fin 1 → 𝔼) = Fin.snoc w a := by
      funext i
      fin_cases i
      rfl
    rw [this]
  | succ k ih =>
    intro f hf
    rw [← Fin.cons_self_tail w]
    set b := w 0
    set w' := Fin.tail w
    have h1 : dT (Fin.cons a (Fin.cons b w')) f =
        fun x ↦ fderiv ℝ (fun y ↦ fderiv ℝ (dT w' f) y a) x b := by
      rw [dT_cons hf, dT_cons hf]
      funext x
      exact fderiv_fderiv_apply_comm (contDiff_dT hf w') x a b
    have h2 : (fun y ↦ fderiv ℝ (dT w' f) y a) = dT (Fin.snoc w' a) f := by
      rw [← ih w' hf, dT_cons hf]
    calc dT (Fin.cons a (Fin.cons b w')) f
        = fun x ↦ fderiv ℝ (fun y ↦ fderiv ℝ (dT w' f) y a) x b := h1
      _ = fun x ↦ fderiv ℝ (dT (Fin.snoc w' a) f) x b := by rw [h2]
      _ = dT (Fin.cons b (Fin.snoc w' a)) f := (dT_cons hf _ _).symm
      _ = dT (Fin.snoc (Fin.cons b w') a) f := by rw [Fin.cons_snoc_eq_snoc_cons]

/- English proof (translation)
Rewrite using `[← dT_snoc hf, ← dT_cons_eq_snoc a w hf, dT_cons hf]`.
-/
theorem fderiv_dT_apply {f : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) {k : ℕ} (w : Fin k → 𝔼) (a x : 𝔼) :
    fderiv ℝ (dT w f) x a = dT w (fun y ↦ fderiv ℝ f y a) x := by
  rw [← dT_snoc hf, ← dT_cons_eq_snoc a w hf, dT_cons hf]

/- English proof (translation)
Proceed by induction on `k generalizing f with`. Consider the case `zero => rw [dT_zero, dT_zero]`. Consider the case `succ k ih`. Rewrite using `[← Fin.cons_self_tail v, dT_cons (contDiff_dT hf w), dT_cons hf]`. Use function extensionality and compare the values at `x`.

Rewrite using `[ih hf (Fin.tail v)]`. Conclude with `fderiv_dT_apply (contDiff_dT hf _) w _ x`.
-/
theorem dT_comm {f : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) {k l : ℕ} (v : Fin k → 𝔼) (w : Fin l → 𝔼) :
    dT v (dT w f) = dT w (dT v f) := by
  induction k generalizing f with
  | zero => rw [dT_zero, dT_zero]
  | succ k ih =>
    rw [← Fin.cons_self_tail v, dT_cons (contDiff_dT hf w), dT_cons hf]
    funext x
    rw [ih hf (Fin.tail v)]
    exact fderiv_dT_apply (contDiff_dT hf _) w _ x

/- English proof (translation)
Rewrite using `[pderiv_eq_dT', pderiv_eq_dT', pdT, pdT, dT_comm hf]`.
-/
theorem pdT_pderiv_comm {f : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) {k : ℕ} (I : Fin k → Fin n)
    (α : Fin n → ℕ) : pdT I (pderiv α f) = pderiv α (pdT I f) := by
  rw [pderiv_eq_dT', pderiv_eq_dT', pdT, pdT, dT_comm hf]

/- English proof (translation)
The claim follows from `(contDiff_infty.1 hf k).contDiffAt`.
-/
theorem contDiffAt_nat {f : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) (k : ℕ) (x : 𝔼) :
    ContDiffAt ℝ k f x :=
  (contDiff_infty.1 hf k).contDiffAt

/- English proof (translation)
Use function extensionality and compare the values at `x`. Establish `h : (fun y ↦ f y + g y) = f + g` using `rfl`. Rewrite using `[dT, h, iteratedFDeriv_add_apply (contDiffAt_nat hf k x) (contDiffAt_nat hg k x)]`. Both sides reduce to the same expression.
-/
theorem dT_add {f g : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {k : ℕ}
    (v : Fin k → 𝔼) : dT v (fun y ↦ f y + g y) = fun x ↦ dT v f x + dT v g x := by
  funext x
  have h : (fun y ↦ f y + g y) = f + g := rfl
  rw [dT, h, iteratedFDeriv_add_apply (contDiffAt_nat hf k x) (contDiffAt_nat hg k x)]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `x`. Establish `h : (fun y ↦ f y - g y) = f - g` using `rfl`. Rewrite using `[dT, h, iteratedFDeriv_sub_apply (contDiffAt_nat hf k x) (contDiffAt_nat hg k x)]`. Both sides reduce to the same expression.
-/
theorem dT_sub {f g : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {k : ℕ}
    (v : Fin k → 𝔼) : dT v (fun y ↦ f y - g y) = fun x ↦ dT v f x - dT v g x := by
  funext x
  have h : (fun y ↦ f y - g y) = f - g := rfl
  rw [dT, h, iteratedFDeriv_sub_apply (contDiffAt_nat hf k x) (contDiffAt_nat hg k x)]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `x`. Establish `h : (fun y ↦ c * f y) = c • f` using `rfl`. Rewrite using `[dT, h, iteratedFDeriv_const_smul_apply (contDiffAt_nat hf k x)]`. Both sides reduce to the same expression.
-/
theorem dT_const_mul {f : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) {k : ℕ} (v : Fin k → 𝔼) (c : ℂ) :
    dT v (fun y ↦ c * f y) = fun x ↦ c * dT v f x := by
  funext x
  have h : (fun y ↦ c * f y) = c • f := rfl
  rw [dT, h, iteratedFDeriv_const_smul_apply (contDiffAt_nat hf k x)]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `x`. Establish `h : (fun y ↦ ∑ i ∈ s, F i y) = ∑ i ∈ s, F i`. Use function extensionality and compare the values at `y`. Simplify using the standard rewrite rules. Rewrite using `[dT, h, iteratedFDeriv_sum_apply (fun i hi ↦ contDiffAt_nat (hF i hi) k x)]`.

Simplify using `[dT]`.
-/
theorem dT_sum {ι : Type*} (s : Finset ι) (F : ι → 𝔼 → ℂ) (hF : ∀ i ∈ s, ContDiff ℝ ∞ (F i))
    {k : ℕ} (v : Fin k → 𝔼) :
    dT v (fun y ↦ ∑ i ∈ s, F i y) = fun x ↦ ∑ i ∈ s, dT v (F i) x := by
  funext x
  have h : (fun y ↦ ∑ i ∈ s, F i y) = ∑ i ∈ s, F i := by
    funext y
    simp
  rw [dT, h, iteratedFDeriv_sum_apply (fun i hi ↦ contDiffAt_nat (hF i hi) k x)]
  simp [dT]

/- English proof (translation)
Rewrite using `[dT, dT, (h.iteratedFDeriv ℝ k).eq_of_nhds]`.
-/
theorem dT_congr_of_eventuallyEq {f g : 𝔼 → ℂ} {x : 𝔼} (h : f =ᶠ[nhds x] g) {k : ℕ}
    (v : Fin k → 𝔼) : dT v f x = dT v g x := by
  rw [dT, dT, (h.iteratedFDeriv ℝ k).eq_of_nhds]

/- English proof (translation)
Simplify using `only [hsD, pdT, dT_congr_of_eventuallyEq h]`.
-/
theorem hsD_congr_of_eventuallyEq {f g : 𝔼 → ℂ} {x : 𝔼} (h : f =ᶠ[nhds x] g) (k : ℕ) :
    hsD k f x = hsD k g x := by
  simp only [hsD, pdT, dT_congr_of_eventuallyEq h]

/- English proof (translation)
The claim follows from `(iteratedFDeriv ℝ k f x).le_opNorm v`.
-/
theorem norm_dT_le (f : 𝔼 → ℂ) {k : ℕ} (v : Fin k → 𝔼) (x : 𝔼) :
    ‖dT v f x‖ ≤ ‖iteratedFDeriv ℝ k f x‖ * ∏ l, ‖v l‖ :=
  (iteratedFDeriv ℝ k f x).le_opNorm v

/- English proof (translation)
Establish `hmem : mdir α l ∈ mdirList α` using `List.get_mem _ _`. Simplify using `only [mdirList, List.mem_flatMap, List.mem_replicate] at hmem`. Take `⟨i, -, -, h⟩` from `hmem`. Rewrite using `[h]`. Simplify using the standard rewrite rules.
-/
theorem norm_mdir (α : Fin n → ℕ) (l : Fin (mabs α)) : ‖mdir α l‖ = 1 := by
  have hmem : mdir α l ∈ mdirList α := List.get_mem _ _
  simp only [mdirList, List.mem_flatMap, List.mem_replicate] at hmem
  obtain ⟨i, -, -, h⟩ := hmem
  rw [h]
  simp

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_pderiv_le (f : 𝔼 → ℂ) (α : Fin n → ℕ) (x : 𝔼) :
    ‖pderiv α f x‖ ≤ ‖iteratedFDeriv ℝ (mabs α) f x‖ := by
  calc ‖pderiv α f x‖ ≤ ‖iteratedFDeriv ℝ (mabs α) f x‖ * ∏ l, ‖mdir α l‖ :=
        norm_dT_le f (mdir α) x
    _ = ‖iteratedFDeriv ℝ (mabs α) f x‖ := by simp [norm_mdir]

/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_eq]`. Simplify using the standard rewrite rules.
-/
theorem calc_sqrt_sum_sq_eq_norm {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    Real.sqrt (∑ i, a i ^ 2) = ‖(WithLp.toLp 2 a : EuclideanSpace ℝ ι)‖ := by
  rw [EuclideanSpace.norm_eq]
  simp

/- English proof (translation)
Use `T.opNorm_le_bound (Real.sqrt_nonneg _) fun m ↦ ?_` and prove the remaining obligations. Establish `hm : ∀ l, m l = ∑ i, (m l i) • ev i` using `fun l ↦ by`. Simplify `((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr (m l)).symm` using `[ev]`. Establish `hT : T m = ∑ J : Fin k → Fin n, (∏ l, m l (J l)) • T (fun l ↦ ev (J l))` using `by conv_lhs => rw [show m = fun l ↦ ∑ i, (m l i) • ev i from funext hm]`. Rewrite using `[T.map_sum]`.

Use `Finset.sum_congr rfl fun J _ ↦ ?_` and prove the remaining obligations. Rewrite using `[T.map_smul_univ]`. Establish `hprod : ∑ J : Fin k → Fin n, (∏ l, m l (J l)) ^ 2 = ∏ l, ‖m l‖ ^ 2`. Establish `: ∀ l, ‖m l‖ ^ 2 = ∑ i, m l i ^ 2` using `fun l ↦ by`. Rewrite using `[EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]`.

Simplify using the standard rewrite rules. Repeatedly rewrite using `[this, Finset.prod_univ_sum, ← Finset.prod_pow]`. Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hT]`.

Conclude with `norm_sum_le _ _`. Use `_ = ∑ J : Fin k → Fin n, |∏ l, m l (J l)| * ‖T (fun l ↦ ev (J l))‖ := Finset.sum_congr rfl fun J _ ↦ by rw [norm_smul, Real.norm_eq_abs]`. Use `_ ≤ Real.sqrt (∑ J : Fin k → Fin n, |∏ l, m l (J l)| ^ 2) * Real.sqrt (∑ J : Fin k → Fin n, ‖T (fun l ↦ ev (J l))‖ ^ 2) := Real.sum_mul_le_sqrt_mul_sqrt _ _ _`. Use `_ = Real.sqrt (∑ J : Fin k → Fin n, ‖T (fun l ↦ ev (J l))‖ ^ 2) * ∏ l, ‖m l‖ := by`. Establish `e : ∑ J : Fin k → Fin n, |∏ l, m l (J l)| ^ 2 = (∏ l, ‖m l‖) ^ 2`.

Repeatedly rewrite using `[sq_abs]`. Rewrite using `[hprod, Finset.prod_pow]`. Rewrite using `[e, Real.sqrt_sq (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _), mul_comm]`.
-/
theorem norm_le_sqrt_sum_basis {k : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ 𝔼) ℂ) :
    ‖T‖ ≤ Real.sqrt (∑ J : Fin k → Fin n, ‖T (fun l ↦ ev (J l))‖ ^ 2) := by
  classical
  refine T.opNorm_le_bound (Real.sqrt_nonneg _) fun m ↦ ?_
  have hm : ∀ l, m l = ∑ i, (m l i) • ev i := fun l ↦ by
    simpa [ev] using ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr (m l)).symm
  have hT : T m = ∑ J : Fin k → Fin n, (∏ l, m l (J l)) • T (fun l ↦ ev (J l)) := by
    conv_lhs => rw [show m = fun l ↦ ∑ i, (m l i) • ev i from funext hm]
    rw [T.map_sum]
    refine Finset.sum_congr rfl fun J _ ↦ ?_
    rw [T.map_smul_univ]
  have hprod : ∑ J : Fin k → Fin n, (∏ l, m l (J l)) ^ 2 = ∏ l, ‖m l‖ ^ 2 := by
    have : ∀ l, ‖m l‖ ^ 2 = ∑ i, m l i ^ 2 := fun l ↦ by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]
      simp
    simp_rw [this, Finset.prod_univ_sum, ← Finset.prod_pow]
    simp
  calc ‖T m‖ ≤ ∑ J : Fin k → Fin n, ‖(∏ l, m l (J l)) • T (fun l ↦ ev (J l))‖ := by
        rw [hT]; exact norm_sum_le _ _
    _ = ∑ J : Fin k → Fin n, |∏ l, m l (J l)| * ‖T (fun l ↦ ev (J l))‖ :=
        Finset.sum_congr rfl fun J _ ↦ by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ Real.sqrt (∑ J : Fin k → Fin n, |∏ l, m l (J l)| ^ 2) *
          Real.sqrt (∑ J : Fin k → Fin n, ‖T (fun l ↦ ev (J l))‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = Real.sqrt (∑ J : Fin k → Fin n, ‖T (fun l ↦ ev (J l))‖ ^ 2) * ∏ l, ‖m l‖ := by
        have e : ∑ J : Fin k → Fin n, |∏ l, m l (J l)| ^ 2 = (∏ l, ‖m l‖) ^ 2 := by
          simp_rw [sq_abs]
          rw [hprod, Finset.prod_pow]
        rw [e, Real.sqrt_sq (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _), mul_comm]

/- English proof (translation)
The claim follows from `norm_le_sqrt_sum_basis _`.
-/
theorem norm_iteratedFDeriv_le_hsD (k : ℕ) (f : 𝔼 → ℂ) (x : 𝔼) :
    ‖iteratedFDeriv ℝ k f x‖ ≤ hsD k f x :=
  norm_le_sqrt_sum_basis _

/- English proof (translation)
Use `set T := iteratedFDeriv ℝ k f x`. Establish `h1 : ∀ J : Fin k → Fin n, ‖pdT J f x‖ ≤ ‖T‖` using `fun J ↦ by`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : ∑ J : Fin k → Fin n, ‖pdT J f x‖ ^ 2 ≤ ((n : ℝ) ^ k * ‖T‖) ^ 2`. Combine the equalities or inequalities in the displayed calculation.

Establish `: ((n ^ k : ℕ) : ℝ) ≤ ((n ^ k : ℕ) : ℝ) ^ 2`. Break down `Nat.eq_zero_or_pos (n ^ k) with h | h` into its components or cases. Simplify using `[h]`. Establish `: (1 : ℝ) ≤ ((n ^ k : ℕ) : ℝ)` using `by exact_mod_cast h`. Use the polynomial consequences of the given equalities and inequalities.

Conclude with `this` after adjusting the coercions. Use `_ = ((n : ℝ) ^ k * ‖T‖) ^ 2 := by ring`. Rewrite using `[hsD]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem hsD_le_norm_iteratedFDeriv (k : ℕ) (f : 𝔼 → ℂ) (x : 𝔼) :
    hsD k f x ≤ (n : ℝ) ^ k * ‖iteratedFDeriv ℝ k f x‖ := by
  set T := iteratedFDeriv ℝ k f x
  have h1 : ∀ J : Fin k → Fin n, ‖pdT J f x‖ ≤ ‖T‖ := fun J ↦ by
    calc ‖pdT J f x‖ ≤ ‖T‖ * ∏ l, ‖ev (J l)‖ := norm_dT_le f _ x
      _ = ‖T‖ := by simp [norm_ev]
  have h2 : ∑ J : Fin k → Fin n, ‖pdT J f x‖ ^ 2 ≤ ((n : ℝ) ^ k * ‖T‖) ^ 2 := by
    calc ∑ J : Fin k → Fin n, ‖pdT J f x‖ ^ 2 ≤ ∑ _J : Fin k → Fin n, ‖T‖ ^ 2 :=
          Finset.sum_le_sum fun J _ ↦ pow_le_pow_left₀ (norm_nonneg _) (h1 J) 2
      _ = (n : ℝ) ^ k * ‖T‖ ^ 2 := by simp
      _ ≤ ((n : ℝ) ^ k) ^ 2 * ‖T‖ ^ 2 := by
          gcongr
          have : ((n ^ k : ℕ) : ℝ) ≤ ((n ^ k : ℕ) : ℝ) ^ 2 := by
            rcases Nat.eq_zero_or_pos (n ^ k) with h | h
            · simp [h]
            · have : (1 : ℝ) ≤ ((n ^ k : ℕ) : ℝ) := by exact_mod_cast h
              nlinarith
          exact_mod_cast this
      _ = ((n : ℝ) ^ k * ‖T‖) ^ 2 := by ring
  rw [hsD]
  calc Real.sqrt (∑ J : Fin k → Fin n, ‖pdT J f x‖ ^ 2)
      ≤ Real.sqrt (((n : ℝ) ^ k * ‖T‖) ^ 2) := Real.sqrt_le_sqrt h2
    _ = (n : ℝ) ^ k * ‖T‖ := Real.sqrt_sq (by positivity)

/- English proof (translation)
Establish `h : ∀ J : Fin k → Fin n, Continuous (pdT J f)` using `fun J ↦ (contDiff_pdT hf J).continuous`. Unfold `hsD`. Use `fun_prop`.
-/
theorem continuous_hsD {f : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) (k : ℕ) : Continuous (hsD k f) := by
  have h : ∀ J : Fin k → Fin n, Continuous (pdT J f) := fun J ↦ (contDiff_pdT hf J).continuous
  unfold hsD
  fun_prop

/- English proof (translation)
Repeatedly rewrite using `[hsD_sq]`. Rewrite using `[← (Fin.snocEquiv (fun _ : Fin (k + 1) ↦ Fin n)).sum_comp, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun J _ ↦ ?_` and prove the remaining obligations. Simplify using `[Fin.snocEquiv, pdT_snoc hf]`.
-/
theorem hsD_succ_sq {f : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) (k : ℕ) (x : 𝔼) :
    hsD (k + 1) f x ^ 2 = ∑ i, hsD k (pd i f) x ^ 2 := by
  simp_rw [hsD_sq]
  rw [← (Fin.snocEquiv (fun _ : Fin (k + 1) ↦ Fin n)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun J _ ↦ ?_
  simp [Fin.snocEquiv, pdT_snoc hf]

/- English proof (translation)
Proceed by induction on `k generalizing f with`. Consider the case `zero => simp [pdT_zero]`. Consider the case `succ k ih`. Rewrite using `[show m + (k + 1) = (m + k) + 1 from rfl, hsD_succ_sq hf]`. Repeatedly rewrite using `[ih (contDiff_pd hf _)]`.

Rewrite using `[← (Fin.snocEquiv (fun _ : Fin (k + 1) ↦ Fin n)).sum_comp, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun J _ ↦ ?_` and prove the remaining obligations. Simplify using `[Fin.snocEquiv, pdT_snoc hf]`.
-/
theorem hsD_add_sq {f : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) (m k : ℕ) (x : 𝔼) :
    hsD (m + k) f x ^ 2 = ∑ I : Fin k → Fin n, hsD m (pdT I f) x ^ 2 := by
  induction k generalizing f with
  | zero => simp [pdT_zero]
  | succ k ih =>
    rw [show m + (k + 1) = (m + k) + 1 from rfl, hsD_succ_sq hf]
    simp_rw [ih (contDiff_pd hf _)]
    rw [← (Fin.snocEquiv (fun _ : Fin (k + 1) ↦ Fin n)).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun J _ ↦ ?_
    simp [Fin.snocEquiv, pdT_snoc hf]

/- English proof (translation)
Use `(pow_le_pow_iff_left₀ (hsD_nonneg _ _ _) (hsD_nonneg _ _ _) two_ne_zero).1 ?_` and prove the remaining obligations. Rewrite using `[hsD_add_sq hf]`. Conclude with `Finset.single_le_sum (f := fun I ↦ hsD m (pdT I f) x ^ 2) (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ I)`.
-/
theorem hsD_pdT_le {f : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) (m : ℕ) {k : ℕ} (I : Fin k → Fin n)
    (x : 𝔼) : hsD m (pdT I f) x ≤ hsD (m + k) f x := by
  refine (pow_le_pow_iff_left₀ (hsD_nonneg _ _ _) (hsD_nonneg _ _ _) two_ne_zero).1 ?_
  rw [hsD_add_sq hf]
  exact Finset.single_le_sum (f := fun I ↦ hsD m (pdT I f) x ^ 2)
    (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ I)

def hsVec (k : ℕ) (f : 𝔼 → ℂ) (x : 𝔼) : EuclideanSpace ℂ (Fin k → Fin n) :=
  WithLp.toLp 2 (fun J ↦ pdT J f x)

/- English proof (translation)
Rewrite using `[hsD, EuclideanSpace.norm_eq]`. Simplify using `[hsVec]`.
-/
theorem hsD_eq_norm (k : ℕ) (f : 𝔼 → ℂ) (x : 𝔼) : hsD k f x = ‖hsVec k f x‖ := by
  rw [hsD, EuclideanSpace.norm_eq]
  simp [hsVec]

/- English proof (translation)
Use extensionality with `J`. Simplify using `[hsVec, pdT, dT_add hf hg]`.
-/
theorem hsVec_add {f g : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (k : ℕ) (x : 𝔼) :
    hsVec k (fun y ↦ f y + g y) x = hsVec k f x + hsVec k g x := by
  ext J
  simp [hsVec, pdT, dT_add hf hg]

/- English proof (translation)
Use extensionality with `J`. Simplify using `[hsVec, pdT, dT_sub hf hg]`.
-/
theorem hsVec_sub {f g : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (k : ℕ) (x : 𝔼) :
    hsVec k (fun y ↦ f y - g y) x = hsVec k f x - hsVec k g x := by
  ext J
  simp [hsVec, pdT, dT_sub hf hg]

/- English proof (translation)
Use extensionality with `J`. Simplify using `[hsVec, pdT, dT_const_mul hf]`.
-/
theorem hsVec_const_mul {f : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) (c : ℂ) (k : ℕ) (x : 𝔼) :
    hsVec k (fun y ↦ c * f y) x = c • hsVec k f x := by
  ext J
  simp [hsVec, pdT, dT_const_mul hf]

/- English proof (translation)
Use extensionality with `J`. Simplify using `[hsVec, pdT, dT_sum s F hF]`.
-/
theorem hsVec_sum {ι : Type*} (s : Finset ι) (F : ι → 𝔼 → ℂ)
    (hF : ∀ i ∈ s, ContDiff ℝ ∞ (F i)) (k : ℕ) (x : 𝔼) :
    hsVec k (fun y ↦ ∑ i ∈ s, F i y) x = ∑ i ∈ s, hsVec k (F i) x := by
  ext J
  simp [hsVec, pdT, dT_sum s F hF]

/- English proof (translation)
Repeatedly rewrite using `[hsD_eq_norm, hsVec_add hf hg]`. Conclude with `norm_add_le _ _`.
-/
theorem hsD_add_le {f g : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (k : ℕ) (x : 𝔼) :
    hsD k (fun y ↦ f y + g y) x ≤ hsD k f x + hsD k g x := by
  simp_rw [hsD_eq_norm, hsVec_add hf hg]
  exact norm_add_le _ _

/- English proof (translation)
Repeatedly rewrite using `[hsD_eq_norm, hsVec_sub hf hg]`. Conclude with `norm_sub_le _ _`.
-/
theorem hsD_sub_le {f g : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (k : ℕ) (x : 𝔼) :
    hsD k (fun y ↦ f y - g y) x ≤ hsD k f x + hsD k g x := by
  simp_rw [hsD_eq_norm, hsVec_sub hf hg]
  exact norm_sub_le _ _

/- English proof (translation)
Repeatedly rewrite using `[hsD_eq_norm, hsVec_const_mul hf, norm_smul]`.
-/
theorem hsD_const_mul {f : 𝔼 → ℂ} (hf : ContDiff ℝ ∞ f) (c : ℂ) (k : ℕ) (x : 𝔼) :
    hsD k (fun y ↦ c * f y) x = ‖c‖ * hsD k f x := by
  simp_rw [hsD_eq_norm, hsVec_const_mul hf, norm_smul]

/- English proof (translation)
Repeatedly rewrite using `[hsD_eq_norm, hsVec_sum s F hF]`. Conclude with `norm_sum_le _ _`.
-/
theorem hsD_sum_le {ι : Type*} (s : Finset ι) (F : ι → 𝔼 → ℂ)
    (hF : ∀ i ∈ s, ContDiff ℝ ∞ (F i)) (k : ℕ) (x : 𝔼) :
    hsD k (fun y ↦ ∑ i ∈ s, F i y) x ≤ ∑ i ∈ s, hsD k (F i) x := by
  simp_rw [hsD_eq_norm, hsVec_sum s F hF]
  exact norm_sum_le _ _

end

end GroundTheory.Automorphic.Sobolev
