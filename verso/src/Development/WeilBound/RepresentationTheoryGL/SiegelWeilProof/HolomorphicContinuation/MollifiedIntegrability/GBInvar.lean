import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsGainBSt

noncomputable section

open Matrix Finset

namespace PositivityTheory.Rg.Sw.WR.K.GB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

namespace Inv

def E (p : Fin n × Fin n) : Mc n := Matrix.single p.1 p.2 1

def dd (H : Mc n) (F : Mc n → ℂ) : Mc n → ℂ := fun b => fderiv ℂ F b H

def wd (L : List (Mc n)) (F : Mc n → ℂ) : Mc n → ℂ := L.foldr (fun H g => dd H g) F

/- English proof (translation)
Rewrite using `[← WithTop.coe_one, ← WithTop.coe_add]`. Conclude with `WithTop.coe_le_coe.2 le_top`.
-/
theorem top_succ_le : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  rw [← WithTop.coe_one, ← WithTop.coe_add]
  exact WithTop.coe_le_coe.2 le_top

/- English proof (translation)
The claim follows from `(hF.fderiv_of_isOpen hU top_succ_le).clm_apply contDiffOn_const`.
-/
theorem dd_smooth {F : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U)
    (H : Mc n) : ContDiffOn ℂ (⊤ : ℕ∞) (dd H F) U :=
  (hF.fderiv_of_isOpen hU top_succ_le).clm_apply contDiffOn_const

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => exact hF`. Consider the case `cons H L ih => exact dd_smooth hU ih H`.
-/
theorem wd_smooth {F : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U)
    (L : List (Mc n)) : ContDiffOn ℂ (⊤ : ℕ∞) (wd L F) U := by
  induction L with
  | nil => exact hF
  | cons H L ih => exact dd_smooth hU ih H

/- English proof (translation)
The claim follows from `(hG.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)`.
-/
theorem diffAt {G : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U) (hG : ContDiffOn ℂ (⊤ : ℕ∞) G U)
    {x : Mc n} (hx : x ∈ U) : DifferentiableAt ℂ G x :=
  (hG.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)

/- English proof (translation)
Unfold `dd`. Rewrite using `[Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (hU.mem_nhds hx) h)]`.
-/
theorem dd_congr {f g : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U) (h : ∀ y ∈ U, f y = g y) (H : Mc n)
    {x : Mc n} (hx : x ∈ U) : dd H f x = dd H g x := by
  unfold dd
  rw [Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (hU.mem_nhds hx) h)]

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => exact h`. Consider the case `cons H L ih => intro x hx`. Conclude with `dd_congr hU ih H hx`.
-/
theorem wd_congr {f g : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U) (h : ∀ y ∈ U, f y = g y)
    (L : List (Mc n)) : ∀ x ∈ U, wd L f x = wd L g x := by
  induction L with
  | nil => exact h
  | cons H L ih => intro x hx; exact dd_congr hU ih H hx

/- English proof (translation)
Unfold `dd`. Establish `h : HasFDerivAt (fun y => ∑ i ∈ s, a i * g i y) (∑ i ∈ s, a i • fderiv ℂ (g i) x) x` using `HasFDerivAt.fun_sum fun i hi => (hg i hi).hasFDerivAt.const_mul (a i)`. Rewrite using `[h.fderiv]`. Simplify using the standard rewrite rules.
-/
theorem dd_sum {ι : Type*} (s : Finset ι) (a : ι → ℂ) (g : ι → Mc n → ℂ) (H : Mc n) {x : Mc n}
    (hg : ∀ i ∈ s, DifferentiableAt ℂ (g i) x) :
    dd H (fun y => ∑ i ∈ s, a i * g i y) x = ∑ i ∈ s, a i * dd H (g i) x := by
  unfold dd
  have h : HasFDerivAt (fun y => ∑ i ∈ s, a i * g i y) (∑ i ∈ s, a i • fderiv ℂ (g i) x) x :=
    HasFDerivAt.fun_sum fun i hi => (hg i hi).hasFDerivAt.const_mul (a i)
  rw [h.fderiv]
  simp

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[E, Matrix.sum_apply, Matrix.single_apply, Fintype.sum_prod_type, ite_and]`.
-/
theorem eq_sum_E (H : Mc n) : H = ∑ p : Fin n × Fin n, H p.1 p.2 • E p := by
  ext a b
  simp [E, Matrix.sum_apply, Matrix.single_apply, Fintype.sum_prod_type, ite_and]

/- English proof (translation)
Use `conv_lhs => rw [eq_sum_E H]`. Simplify using `[dd, map_sum, map_smul]`.
-/
theorem dd_expand (H : Mc n) (f : Mc n → ℂ) (x : Mc n) :
    dd H f x = ∑ p : Fin n × Fin n, H p.1 p.2 * dd (E p) f x := by
  conv_lhs => rw [eq_sum_E H]
  simp [dd, map_sum, map_smul]

/- English proof (translation)
Rewrite using `[show (2 : WithTop ℕ∞) = ((2 : ℕ∞) : WithTop ℕ∞) from rfl]`. Conclude with `WithTop.coe_le_coe.2 le_top`.
-/
theorem two_le_top' : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  rw [show (2 : WithTop ℕ∞) = ((2 : ℕ∞) : WithTop ℕ∞) from rfl]
  exact WithTop.coe_le_coe.2 le_top

/- English proof (translation)
Establish `hc : ContDiffAt ℂ (⊤ : ℕ∞) g x` using `hg.contDiffAt (hU.mem_nhds hx)`. Establish `hsymm : IsSymmSndFDerivAt ℂ g x` using `hc.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; exact two_le_top')`. Establish `hd : DifferentiableAt ℂ (fderiv ℂ g) x` using `(hc.fderiv_right top_succ_le).differentiableAt (by simp)`. Establish `key : ∀ v w : Mc n, fderiv ℂ (fun y => fderiv ℂ g y v) x w = fderiv ℂ (fderiv ℂ g) x w v`. Introduce `v w`.

Establish `h` using `(ContinuousLinearMap.apply ℂ ℂ v).hasFDerivAt.comp x hd.hasFDerivAt`. Conclude with `congrArg (fun L => L w) h.fderiv`. Unfold `dd`. Rewrite using `[key, key]`. Conclude with `hsymm b a`.
-/
theorem dd_swap {g : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U) (hg : ContDiffOn ℂ (⊤ : ℕ∞) g U)
    (a b : Mc n) {x : Mc n} (hx : x ∈ U) : dd b (dd a g) x = dd a (dd b g) x := by
  have hc : ContDiffAt ℂ (⊤ : ℕ∞) g x := hg.contDiffAt (hU.mem_nhds hx)
  have hsymm : IsSymmSndFDerivAt ℂ g x :=
    hc.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; exact two_le_top')
  have hd : DifferentiableAt ℂ (fderiv ℂ g) x := (hc.fderiv_right top_succ_le).differentiableAt (by simp)
  have key : ∀ v w : Mc n, fderiv ℂ (fun y => fderiv ℂ g y v) x w = fderiv ℂ (fderiv ℂ g) x w v := by
    intro v w
    have h := (ContinuousLinearMap.apply ℂ ℂ v).hasFDerivAt.comp x hd.hasFDerivAt
    exact congrArg (fun L => L w) h.fderiv
  unfold dd
  rw [key, key]
  exact hsymm b a

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `nil => intro x _`. Both sides reduce to the same expression. Consider the case `cons a _ ih => intro x hx`. Conclude with `dd_congr hU ih a hx`.

Consider the case `swap a b l => intro x hx`. Conclude with `dd_swap hU (wd_smooth hU hF l) a b hx`. Consider the case `trans _ _ ih1 ih2 => intro x hx`. Rewrite using `[ih1 x hx, ih2 x hx]`.
-/
theorem wd_perm {F : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U)
    {L L' : List (Mc n)} (h : L.Perm L') : ∀ x ∈ U, wd L F x = wd L' F x := by
  induction h with
  | nil => intro x _; rfl
  | cons a _ ih => intro x hx; exact dd_congr hU ih a hx
  | swap a b l => intro x hx; exact dd_swap hU (wd_smooth hU hF l) a b hx
  | trans _ _ ih1 ih2 => intro x hx; rw [ih1 x hx, ih2 x hx]

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => intro x _`. Both sides reduce to the same expression. Consider the case `cons H L ih`. Introduce `x hx`.

Establish `hV : IsOpen (T ⁻¹' U)` using `hU.preimage T.continuous`. Use `show dd H (wd L (fun c => F (T c))) x = dd (T H) (wd (L.map T) F) (T x)`. Rewrite using `[dd_congr hV (g := fun c => wd (L.map T) F (T c)) (fun y hy => ih y hy) H hx]`. Unfold `dd`. Establish `hG : DifferentiableAt ℂ (wd (L.map T) F) (T x)` using `diffAt hU (wd_smooth hU hF _) hx`.

Establish `h` using `hG.hasFDerivAt.comp x T.hasFDerivAt`. Conclude with `congrArg (fun L => L H) h.fderiv`.
-/
theorem wd_comp (T : Mc n →L[ℂ] Mc n) {F : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U)
    (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) (L : List (Mc n)) :
    ∀ x, T x ∈ U → wd L (fun c => F (T c)) x = wd (L.map T) F (T x) := by
  induction L with
  | nil => intro x _; rfl
  | cons H L ih =>
    intro x hx
    have hV : IsOpen (T ⁻¹' U) := hU.preimage T.continuous
    show dd H (wd L (fun c => F (T c))) x = dd (T H) (wd (L.map T) F) (T x)
    rw [dd_congr hV (g := fun c => wd (L.map T) F (T c)) (fun y hy => ih y hy) H hx]
    unfold dd
    have hG : DifferentiableAt ℂ (wd (L.map T) F) (T x) := diffAt hU (wd_smooth hU hF _) hx
    have h := hG.hasFDerivAt.comp x T.hasFDerivAt
    exact congrArg (fun L => L H) h.fderiv

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro v x _`. Simplify using `[wd]`. Consider the case `succ m ih`.

Introduce `v x hx`. Rewrite using `[List.ofFn_succ]`. Use `show dd (v 0) (wd (List.ofFn fun i => v i.succ) F) x = _`. Rewrite using `[dd_congr hU (fun y hy => ih (fun i => v i.succ) y hy) (v 0) hx]`. Rewrite using `[dd_sum _ _ _ _ (fun r _ => diffAt hU (wd_smooth hU hF _) hx)]`.

Repeatedly rewrite using `[dd_expand (v 0), Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `conv_rhs => rw [← (Fin.consEquiv fun _ : Fin (m + 1) => Fin n × Fin n).sum_comp (fun r : Fin (m + 1) → Fin n × Fin n => (∏ t, v t (r t).1 (r t).2) * wd (List.ofFn fun t => E (r t)) F x), Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r' _ => ?_` and prove the remaining obligations. Simplify using `only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, List.ofFn_succ]`.

Use `show _ = _ * dd (E p) (wd (List.ofFn fun t => E (r' t)) F) x`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wd_expand {F : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) :
    ∀ (m : ℕ) (v : Fin m → Mc n), ∀ x ∈ U, wd (List.ofFn v) F x =
      ∑ r : Fin m → Fin n × Fin n, (∏ t, v t (r t).1 (r t).2) * wd (List.ofFn fun t => E (r t)) F x := by
  intro m
  induction m with
  | zero => intro v x _; simp [wd]
  | succ m ih =>
    intro v x hx
    rw [List.ofFn_succ]
    show dd (v 0) (wd (List.ofFn fun i => v i.succ) F) x = _
    rw [dd_congr hU (fun y hy => ih (fun i => v i.succ) y hy) (v 0) hx]
    rw [dd_sum _ _ _ _ (fun r _ => diffAt hU (wd_smooth hU hF _) hx)]
    simp_rw [dd_expand (v 0), Finset.mul_sum]
    rw [Finset.sum_comm]
    conv_rhs => rw [← (Fin.consEquiv fun _ : Fin (m + 1) => Fin n × Fin n).sum_comp
      (fun r : Fin (m + 1) → Fin n × Fin n => (∏ t, v t (r t).1 (r t).2) * wd (List.ofFn fun t => E (r t)) F x),
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r' _ => ?_
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, List.ofFn_succ]
    show _ = _ * dd (E p) (wd (List.ofFn fun t => E (r' t)) F) x
    ring

/- English proof (translation)
Rewrite using `[← Finset.sum_filter_of_ne (f := h) (p := Function.Injective) (fun c _ hc => by_contra fun hn => hc (h0 c hn))]`. Use `Finset.sum_bij' (fun c hc => Equiv.ofBijective c ((Finite.injective_iff_bijective).1 (Finset.mem_filter.1 hc).2)) (fun π _ => ⇑π) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `c _`. Conclude with `Finset.mem_univ _`. Introduce `π _`.

Conclude with `Finset.mem_filter.2 ⟨Finset.mem_univ _, π.injective⟩`. Introduce `c _`. Both sides reduce to the same expression. Introduce `π _`. Use `ext`.

Both sides reduce to the same expression. Introduce `c _`. Both sides reduce to the same expression.
-/
theorem sum_perm_of_noninj {α : Type*} [AddCommMonoid α] (h : (Fin n → Fin n) → α)
    (h0 : ∀ c, ¬ Function.Injective c → h c = 0) :
    ∑ c : Fin n → Fin n, h c = ∑ π : Equiv.Perm (Fin n), h π := by
  classical
  rw [← Finset.sum_filter_of_ne (f := h) (p := Function.Injective) (fun c _ hc => by_contra fun hn => hc (h0 c hn))]
  refine Finset.sum_bij' (fun c hc => Equiv.ofBijective c
      ((Finite.injective_iff_bijective).1 (Finset.mem_filter.1 hc).2)) (fun π _ => ⇑π) ?_ ?_ ?_ ?_ ?_
  · intro c _; exact Finset.mem_univ _
  · intro π _; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, π.injective⟩
  · intro c _; rfl
  · intro π _; ext; rfl
  · intro c _; rfl

/- English proof (translation)
Take `⟨i, j, hij, hne⟩` from `Function.not_injective_iff.1 hc`. Conclude with `Matrix.det_zero_of_row_eq hne (by ext k; simp [hij])`.
-/
theorem det_sub_zero (A : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → Fin n) (hc : ¬ Function.Injective c) :
    (A.submatrix c id).det = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.1 hc
  exact Matrix.det_zero_of_row_eq hne (by ext k; simp [hij])

/- English proof (translation)
Establish `s1 : ∀ r : Fin n → Fin n × Fin n, ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((∏ t, (A (r t).1 (σ t) * B (r t).2 t)) * Φ r) = (A.submatrix (fun t => (r t).1) id).det * (∏ t, B (r t).2 t) * Φ r`. Introduce `r`. Rewrite using `[← Matrix.det_transpose, Matrix.det_apply', Finset.sum_mul, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_mul_distrib]`.

Simplify using `only [Matrix.transpose_apply, Matrix.submatrix_apply, id]`. Expand and normalize the polynomial expressions, which then agree. Establish `e1 : ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∑ r : Fin n → Fin n × Fin n, (∏ t, (A (r t).1 (σ t) * B (r t).2 t)) * Φ r = ∑ r : Fin n → Fin n × Fin n, (A.submatrix (fun t => (r t).1) id).det * (∏ t, B (r t).2 t) * Φ r`. Repeatedly rewrite using `[Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Conclude with `Finset.sum_congr rfl fun r _ => s1 r`. Rewrite using `[e1]`. Set `eP` to `Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Fin n) (fun _ => Fin n)`. Rewrite using `[← eP.symm.sum_comp, Fintype.sum_prod_type]`. Establish `e2 : ∀ c : Fin n → Fin n, ∑ d : Fin n → Fin n, (A.submatrix (fun t => ((eP.symm (c, d)) t).1) id).det * (∏ t, B ((eP.symm (c, d)) t).2 t) * Φ (eP.symm (c, d)) = (A.submatrix c id).det * ∑ d : Fin n → Fin n, (∏ t, B (d t) t) * Φ (fun t => (c t, d t))`.

Introduce `c`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Simplify using `only [eP, Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk]`. Expand and normalize the polynomial expressions, which then agree.

Repeatedly rewrite using `[e2]`. Rewrite using `[sum_perm_of_noninj _ (fun c hc => by rw [det_sub_zero A c hc, zero_mul])]`. Establish `e3 : ∀ π : Equiv.Perm (Fin n), (A.submatrix π id).det * ∑ d : Fin n → Fin n, (∏ t, B (d t) t) * Φ (fun t => (π t, d t)) = ((Equiv.Perm.sign π : ℤ) : ℂ) * A.det * ∑ e : Fin n → Fin n, (∏ t, B (e (π t)) t) * Φ (fun i => (i, e i))`. Introduce `π`. Rewrite using `[Matrix.det_permute]`.

Establish `: ∑ d : Fin n → Fin n, (∏ t, B (d t) t) * Φ (fun t => (π t, d t)) = ∑ e : Fin n → Fin n, (∏ t, B (e (π t)) t) * Φ (fun i => (i, e i))`. Use `Fintype.sum_equiv (Equiv.arrowCongr π (Equiv.refl (Fin n))) _ _ fun d => ?_` and prove the remaining obligations. Establish `h1 : (fun t => (π t, d t)) = (fun i => (i, (Equiv.arrowCongr π (Equiv.refl (Fin n)) d) i)) ∘ π`. Use function extensionality and compare the values at `t`. Simplify using `[Equiv.arrowCongr_apply]`.

Rewrite using `[h1, hΦ]`. Use `congr 1`. Use `Finset.prod_congr rfl fun t _ => ?_` and prove the remaining obligations. Simplify using `[Equiv.arrowCongr_apply]`. Rewrite using `[this]`.

Repeatedly rewrite using `[e3]`. Establish `e4 : ∑ π : Equiv.Perm (Fin n), ((Equiv.Perm.sign π : ℤ) : ℂ) * A.det * ∑ e : Fin n → Fin n, (∏ t, B (e (π t)) t) * Φ (fun i => (i, e i)) = A.det * ∑ e : Fin n → Fin n, (B.submatrix e id).det * Φ (fun i => (i, e i))`. Repeatedly rewrite using `[Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.det_apply' (B.submatrix e id), Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun π _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.submatrix_apply, id]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e4, sum_perm_of_noninj _ (fun c hc => by rw [det_sub_zero B c hc, zero_mul])]`.

Establish `e5 : ∀ ρ : Equiv.Perm (Fin n), (B.submatrix ρ id).det * Φ (fun i => (i, ρ i)) = B.det * (((Equiv.Perm.sign ρ⁻¹ : ℤ) : ℂ) * Φ (fun t => (ρ⁻¹ t, t)))`. Introduce `ρ`. Rewrite using `[Matrix.det_permute, Equiv.Perm.sign_inv]`. Establish `h2 : (fun i => (i, ρ i)) = (fun t => (ρ⁻¹ t, t)) ∘ ρ`. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules. Rewrite using `[h2, hΦ]`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[e5, ← Finset.mul_sum]`. Rewrite using `[Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n))) (fun ρ => ((Equiv.Perm.sign ρ⁻¹ : ℤ) : ℂ) * Φ (fun t => (ρ⁻¹ t, t))) (fun σ => ((Equiv.Perm.sign σ : ℤ) : ℂ) * Φ (fun t => (σ t, t))) (fun ρ => rfl)]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem alg (A B : Matrix (Fin n) (Fin n) ℂ) (Φ : (Fin n → Fin n × Fin n) → ℂ)
    (hΦ : ∀ r (π : Equiv.Perm (Fin n)), Φ (r ∘ π) = Φ r) :
    ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∑ r : Fin n → Fin n × Fin n, (∏ t, (A (r t).1 (σ t) * B (r t).2 t)) * Φ r =
      A.det * B.det * ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * Φ (fun t => (σ t, t)) := by
  classical
  have s1 : ∀ r : Fin n → Fin n × Fin n, ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      ((∏ t, (A (r t).1 (σ t) * B (r t).2 t)) * Φ r) =
      (A.submatrix (fun t => (r t).1) id).det * (∏ t, B (r t).2 t) * Φ r := by
    intro r
    rw [← Matrix.det_transpose, Matrix.det_apply', Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.prod_mul_distrib]
    simp only [Matrix.transpose_apply, Matrix.submatrix_apply, id]
    ring
  have e1 : ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∑ r : Fin n → Fin n × Fin n, (∏ t, (A (r t).1 (σ t) * B (r t).2 t)) * Φ r =
      ∑ r : Fin n → Fin n × Fin n, (A.submatrix (fun t => (r t).1) id).det * (∏ t, B (r t).2 t) * Φ r := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun r _ => s1 r
  rw [e1]
  let eP := Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Fin n) (fun _ => Fin n)
  rw [← eP.symm.sum_comp, Fintype.sum_prod_type]
  have e2 : ∀ c : Fin n → Fin n, ∑ d : Fin n → Fin n,
      (A.submatrix (fun t => ((eP.symm (c, d)) t).1) id).det * (∏ t, B ((eP.symm (c, d)) t).2 t) * Φ (eP.symm (c, d)) =
      (A.submatrix c id).det * ∑ d : Fin n → Fin n, (∏ t, B (d t) t) * Φ (fun t => (c t, d t)) := by
    intro c
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [eP, Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk]
    ring
  simp_rw [e2]
  rw [sum_perm_of_noninj _ (fun c hc => by rw [det_sub_zero A c hc, zero_mul])]
  have e3 : ∀ π : Equiv.Perm (Fin n), (A.submatrix π id).det * ∑ d : Fin n → Fin n,
      (∏ t, B (d t) t) * Φ (fun t => (π t, d t)) =
      ((Equiv.Perm.sign π : ℤ) : ℂ) * A.det * ∑ e : Fin n → Fin n, (∏ t, B (e (π t)) t) * Φ (fun i => (i, e i)) := by
    intro π
    rw [Matrix.det_permute]
    have : ∑ d : Fin n → Fin n, (∏ t, B (d t) t) * Φ (fun t => (π t, d t)) =
        ∑ e : Fin n → Fin n, (∏ t, B (e (π t)) t) * Φ (fun i => (i, e i)) := by
      refine Fintype.sum_equiv (Equiv.arrowCongr π (Equiv.refl (Fin n))) _ _ fun d => ?_
      have h1 : (fun t => (π t, d t)) = (fun i => (i, (Equiv.arrowCongr π (Equiv.refl (Fin n)) d) i)) ∘ π := by
        funext t; simp [Equiv.arrowCongr_apply]
      rw [h1, hΦ]
      congr 1
      refine Finset.prod_congr rfl fun t _ => ?_
      simp [Equiv.arrowCongr_apply]
    rw [this]
  simp_rw [e3]
  have e4 : ∑ π : Equiv.Perm (Fin n), ((Equiv.Perm.sign π : ℤ) : ℂ) * A.det *
        ∑ e : Fin n → Fin n, (∏ t, B (e (π t)) t) * Φ (fun i => (i, e i)) =
      A.det * ∑ e : Fin n → Fin n, (B.submatrix e id).det * Φ (fun i => (i, e i)) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Matrix.det_apply' (B.submatrix e id), Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun π _ => ?_
    simp only [Matrix.submatrix_apply, id]
    ring
  rw [e4, sum_perm_of_noninj _ (fun c hc => by rw [det_sub_zero B c hc, zero_mul])]
  have e5 : ∀ ρ : Equiv.Perm (Fin n), (B.submatrix ρ id).det * Φ (fun i => (i, ρ i)) =
      B.det * (((Equiv.Perm.sign ρ⁻¹ : ℤ) : ℂ) * Φ (fun t => (ρ⁻¹ t, t))) := by
    intro ρ
    rw [Matrix.det_permute, Equiv.Perm.sign_inv]
    have h2 : (fun i => (i, ρ i)) = (fun t => (ρ⁻¹ t, t)) ∘ ρ := by
      funext i; simp
    rw [h2, hΦ]
    ring
  simp_rw [e5, ← Finset.mul_sum]
  rw [Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n))) (fun ρ => ((Equiv.Perm.sign ρ⁻¹ : ℤ) : ℂ) * Φ (fun t => (ρ⁻¹ t, t)))
    (fun σ => ((Equiv.Perm.sign σ : ℤ) : ℂ) * Φ (fun t => (σ t, t))) (fun ρ => rfl)]
  ring

/- English proof (translation)
Unfold `DeltaC`. Rewrite using `[Finset.sum_apply]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, smul_eq_mul]`. Use `congr 1`.

Rewrite using `[List.ofFn_eq_map, wd, List.foldr_map]`. Both sides reduce to the same expression.
-/
theorem deltaC_eq (F : Mc n → ℂ) (x : Mc n) : DeltaC F x = ∑ σ : Equiv.Perm (Fin n),
    ((Equiv.Perm.sign σ : ℤ) : ℂ) * wd (List.ofFn fun t => E (σ t, t)) F x := by
  unfold DeltaC
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  congr 1
  rw [List.ofFn_eq_map, wd, List.foldr_map]
  rfl

/- English proof (translation)
Establish `: DeltaC F = fun x => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * wd (List.ofFn fun t => E (σ t, t)) F x` using `funext (deltaC_eq F)`. Rewrite using `[this]`. Conclude with `ContDiffOn.sum fun σ _ => contDiffOn_const.mul (wd_smooth hU hF _)`.
-/
theorem deltaC_smooth {F : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) :
    ContDiffOn ℂ (⊤ : ℕ∞) (DeltaC F) U := by
  have : DeltaC F = fun x => ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * wd (List.ofFn fun t => E (σ t, t)) F x := funext (deltaC_eq F)
  rw [this]
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (wd_smooth hU hF _)

/- English proof (translation)
Rewrite using `[deltaC_eq, deltaC_eq]`. Conclude with `Finset.sum_congr rfl fun σ _ => by rw [wd_congr hV h _ x hx]`.
-/
theorem deltaC_congr {f g : Mc n → ℂ} {V : Set (Mc n)} (hV : IsOpen V) (h : ∀ y ∈ V, f y = g y)
    {x : Mc n} (hx : x ∈ V) : DeltaC f x = DeltaC g x := by
  rw [deltaC_eq, deltaC_eq]
  exact Finset.sum_congr rfl fun σ _ => by rw [wd_congr hV h _ x hx]

/- English proof (translation)
Simplify using `[E, Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Finset.sum_ite_eq', Finset.sum_ite_eq, ite_and]`.
-/
theorem conj_single (k : Mc n) (p : Fin n × Fin n) (c d : Fin n) :
    (k * E p * kᴴ) c d = k c p.1 * (k.map star) d p.2 := by
  simp [E, Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, Matrix.map_apply,
    Finset.sum_ite_eq', Finset.sum_ite_eq, ite_and]

/- English proof (translation)
Set `Tl : Mc n →ₗ[ℂ] Mc n` to `{ toFun := fun c => k * c * kᴴ map_add' := fun x y => by simp [Matrix.mul_add, Matrix.add_mul] map_smul' := fun a x => by simp [Matrix.mul_smul, Matrix.smul_mul] }`. Set `T : Mc n →L[ℂ] Mc n` to `LinearMap.toContinuousLinearMap Tl`. Establish `hT : ∀ c, T c = k * c * kᴴ` using `fun c => rfl`. Establish `hFT : (fun c => F (k * c * kᴴ)) = fun c => F (T c)` using `by funext c; rw [hT]`. Establish `hTb : T b ∈ U` using `by rw [hT]; exact hb`.

Rewrite using `[deltaC_eq, deltaC_eq, hFT]`. Establish `h1 : ∀ σ : Equiv.Perm (Fin n), wd (List.ofFn fun t => E (σ t, t)) (fun c => F (T c)) b = ∑ r : Fin n → Fin n × Fin n, (∏ t, (k (r t).1 (σ t) * (k.map star) (r t).2 t)) * wd (List.ofFn fun t => E (r t)) F (k * b * kᴴ)`. Introduce `σ`. Rewrite using `[wd_comp T hU hF _ b hTb, List.map_ofFn, hT b, wd_expand hU hF n _ _ hb]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations.

Use `congr 1`. Use `Finset.prod_congr rfl fun t _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, hT]`. Conclude with `conj_single k (σ t, t) (r t).1 (r t).2`. Repeatedly rewrite using `[h1]`.

Rewrite using `[alg k (k.map star) (fun r => wd (List.ofFn fun t => E (r t)) F (k * b * kᴴ)) (fun r π => wd_perm hU hF (Equiv.Perm.ofFn_comp_perm π fun t => E (r t)) _ hb)]`. Establish `hu : star k * k = 1` using `(Matrix.mem_unitaryGroup_iff').1 hk`. Establish `hdet : k.det * (k.map star).det = 1`. Establish `h2 : (k.map star).det = star k.det`. Rewrite using `[← Matrix.det_conjTranspose, ← Matrix.det_transpose]`.

Both sides reduce to the same expression. Establish `h3` using `congrArg Matrix.det hu`. Rewrite `h3` using `[Matrix.det_mul, Matrix.det_one, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose]`. Rewrite using `[h2, mul_comm]`. Conclude with `h3`.

Rewrite using `[hdet, one_mul]`.
-/
theorem invar_one {F : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U)
    {k : Mc n} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (b : Mc n) (hb : k * b * kᴴ ∈ U) :
    DeltaC (fun c => F (k * c * kᴴ)) b = DeltaC F (k * b * kᴴ) := by
  let Tl : Mc n →ₗ[ℂ] Mc n :=
    { toFun := fun c => k * c * kᴴ
      map_add' := fun x y => by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun a x => by simp [Matrix.mul_smul, Matrix.smul_mul] }
  let T : Mc n →L[ℂ] Mc n := LinearMap.toContinuousLinearMap Tl
  have hT : ∀ c, T c = k * c * kᴴ := fun c => rfl
  have hFT : (fun c => F (k * c * kᴴ)) = fun c => F (T c) := by funext c; rw [hT]
  have hTb : T b ∈ U := by rw [hT]; exact hb
  rw [deltaC_eq, deltaC_eq, hFT]
  have h1 : ∀ σ : Equiv.Perm (Fin n), wd (List.ofFn fun t => E (σ t, t)) (fun c => F (T c)) b =
      ∑ r : Fin n → Fin n × Fin n, (∏ t, (k (r t).1 (σ t) * (k.map star) (r t).2 t)) *
        wd (List.ofFn fun t => E (r t)) F (k * b * kᴴ) := by
    intro σ
    rw [wd_comp T hU hF _ b hTb, List.map_ofFn, hT b, wd_expand hU hF n _ _ hb]
    refine Finset.sum_congr rfl fun r _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun t _ => ?_
    simp only [Function.comp_apply, hT]
    exact conj_single k (σ t, t) (r t).1 (r t).2
  simp_rw [h1]
  rw [alg k (k.map star) (fun r => wd (List.ofFn fun t => E (r t)) F (k * b * kᴴ))
    (fun r π => wd_perm hU hF (Equiv.Perm.ofFn_comp_perm π fun t => E (r t)) _ hb)]
  have hu : star k * k = 1 := (Matrix.mem_unitaryGroup_iff').1 hk
  have hdet : k.det * (k.map star).det = 1 := by
    have h2 : (k.map star).det = star k.det := by
      rw [← Matrix.det_conjTranspose, ← Matrix.det_transpose]
      rfl
    have h3 := congrArg Matrix.det hu
    rw [Matrix.det_mul, Matrix.det_one, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose] at h3
    rw [h2, mul_comm]
    exact h3
  rw [hdet, one_mul]

/- English proof (translation)
Introduce `N`. Proceed by induction on `N with`. Consider the case `zero => exact hF`. Consider the case `succ N ih => rw [Function.iterate_succ_apply']`. Conclude with `deltaC_smooth hU ih`.
-/
theorem invar_iter {F : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) :
    ∀ N : ℕ, ContDiffOn ℂ (⊤ : ℕ∞) (DeltaC^[N] F) U := by
  intro N
  induction N with
  | zero => exact hF
  | succ N ih => rw [Function.iterate_succ_apply']; exact deltaC_smooth hU ih

end Inv

open PositivityTheory.Rg.Sw.WR.K.GB.Inv in
/- English proof (translation)
Introduce `n F U hU hF k hk N`. Proceed by induction on `N with`. Consider the case `zero => intro b _`. Both sides reduce to the same expression. Consider the case `succ N ih`.

Introduce `b hb`. Rewrite using `[Function.iterate_succ_apply', Function.iterate_succ_apply']`. Establish `hV : IsOpen {c : Mc n | k * c * kᴴ ∈ U}` using `hU.preimage ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)`. Rewrite using `[deltaC_congr hV (g := fun c => (DeltaC^[N] F) (k * c * kᴴ)) (fun y hy => ih y hy) hb]`. Conclude with `invar_one hU (invar_iter hU hF N) hk b hb`.
-/
theorem invar : Invar := by
  intro n F U hU hF k hk N
  induction N with
  | zero => intro b _; rfl
  | succ N ih =>
    intro b hb
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hV : IsOpen {c : Mc n | k * c * kᴴ ∈ U} :=
      hU.preimage ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
    rw [deltaC_congr hV (g := fun c => (DeltaC^[N] F) (k * c * kᴴ)) (fun y hy => ih y hy) hb]
    exact invar_one hU (invar_iter hU hF N) hk b hb

end PositivityTheory.Rg.Sw.WR.K.GB
