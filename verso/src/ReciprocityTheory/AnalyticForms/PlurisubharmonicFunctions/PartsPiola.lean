import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsCalc

namespace ReciprocityTheory.AnForm.A

open MeasureTheory ReciprocityTheory.AnForm Matrix Filter Topology

noncomputable section

/- English proof (translation)
Apply the tactic sequence `have h2 : ContDiffAt ℝ 2 (fderiv ℝ φ) z := h.fderiv_right (by first | norm_num | simp | rfl)`. Apply the tactic sequence `exact h2.isSymmSndFDerivAt (by first | simp | norm_num | (simp only [minSmoothness_of_isRCLikeNormedField]; norm_num)) u x`.
-/
theorem third_fderiv_symm_one_two {D : ℕ} (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (h : ContDiffAt ℝ 3 φ z)
    (u x : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) z u x = fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) z x u := by
  have h2 : ContDiffAt ℝ 2 (fderiv ℝ φ) z := h.fderiv_right (by first | norm_num | simp | rfl)
  exact h2.isSymmSndFDerivAt (by first | simp | norm_num | (simp only [minSmoothness_of_isRCLikeNormedField]; norm_num)) u x

/- English proof (translation)
Apply the tactic sequence `have h2 : ContDiffAt ℝ 2 (fderiv ℝ φ) z := h.fderiv_right (by first | norm_num | simp | rfl)`. Apply the tactic sequence `have h1 : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ φ)) z := h2.fderiv_right (by first | norm_num | simp | rfl)`. Apply the tactic sequence `exact h1.differentiableAt (by first | norm_num | simp | exact one_ne_zero)`.
-/
theorem differentiableAt_snd_fderiv {D : ℕ} (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ)
    (h : ContDiffAt ℝ 3 φ z) : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ φ)) z := by
  have h2 : ContDiffAt ℝ 2 (fderiv ℝ φ) z := h.fderiv_right (by first | norm_num | simp | rfl)
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ φ)) z := h2.fderiv_right (by first | norm_num | simp | rfl)
  exact h1.differentiableAt (by first | norm_num | simp | exact one_ne_zero)

/- English proof (translation)
Establish `hd` using `differentiableAt_snd_fderiv φ z h`. Establish `key : ∀ x y : Fin D → ℂ, fderiv ℝ (⇑(evalL x y) ∘ fderiv ℝ (fderiv ℝ φ)) z = (evalL x y).comp (fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) z)` using `fun x y => ((evalL x y).hasFDerivAt.comp z hd.hasFDerivAt).fderiv`. Apply the tactic sequence `have h2 : ContDiffAt ℝ 2 φ z := h.of_le (by first | norm_num | simp | rfl)`. Apply the tactic sequence `have hev : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ 2 φ w := h2.eventually (by first | simp | norm_num | decide | exact ENat.coe_ne_top _)`. Establish `ev : (⇑(evalL x y) ∘ fderiv ℝ (fderiv ℝ φ)) =ᶠ[𝓝 z] (⇑(evalL y x) ∘ fderiv ℝ (fderiv ℝ φ))` using `by filter_upwards [hev] with w hw`.

Simplify using `only [Function.comp_apply, evalL, ContinuousLinearMap.coe_comp', ContinuousLinearMap.apply_apply]`. Apply the tactic sequence `exact hw.isSymmSndFDerivAt (by first | simp | norm_num | (simp only [minSmoothness_of_isRCLikeNormedField]; norm_num)) x y`. Establish `e` using `Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) ev`. Rewrite `e` using `[key x y, key y x]`. Establish `e2` using `congrArg (fun L => L u) e`.

Simplify `e2` using `only [evalL, ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.apply_apply]`.
-/
theorem third_fderiv_symm_two_three {D : ℕ} (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (h : ContDiffAt ℝ 3 φ z)
    (u x y : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) z u x y = fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) z u y x := by
  have hd := differentiableAt_snd_fderiv φ z h
  have key : ∀ x y : Fin D → ℂ,
      fderiv ℝ (⇑(evalL x y) ∘ fderiv ℝ (fderiv ℝ φ)) z =
        (evalL x y).comp (fderiv ℝ (fderiv ℝ (fderiv ℝ φ)) z) :=
    fun x y => ((evalL x y).hasFDerivAt.comp z hd.hasFDerivAt).fderiv
  have h2 : ContDiffAt ℝ 2 φ z := h.of_le (by first | norm_num | simp | rfl)
  have hev : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ 2 φ w := h2.eventually (by first | simp | norm_num | decide | exact ENat.coe_ne_top _)
  have ev : (⇑(evalL x y) ∘ fderiv ℝ (fderiv ℝ φ)) =ᶠ[𝓝 z]
      (⇑(evalL y x) ∘ fderiv ℝ (fderiv ℝ φ)) := by
    filter_upwards [hev] with w hw
    simp only [Function.comp_apply, evalL, ContinuousLinearMap.coe_comp',
      ContinuousLinearMap.apply_apply]
    exact hw.isSymmSndFDerivAt (by first | simp | norm_num | (simp only [minSmoothness_of_isRCLikeNormedField]; norm_num)) x y
  have e := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) ev
  rw [key x y, key y x] at e
  have e2 := congrArg (fun L => L u) e
  simpa only [evalL, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.apply_apply] using e2

/- English proof (translation)
Establish `e1` using `hT (Pi.single j 1) (Pi.single a 1)`. Establish `e2` using `hT (Pi.single j 1) (Complex.I • Pi.single a 1)`. Establish `e3` using `hT (Complex.I • Pi.single j 1) (Pi.single a 1)`. Establish `e4` using `hT (Complex.I • Pi.single j 1) (Complex.I • Pi.single a 1)`. Simplify using `only [hessEntry_apply, e1, e2, e3, e4]`.

Use `push_cast`. Take the linear combination `((T (Complex.I • Pi.single a 1) (Pi.single j 1) (Complex.I • Pi.single b 1) : ℂ) - (T (Pi.single a 1) (Complex.I • Pi.single j 1) (Complex.I • Pi.single b 1) : ℂ)) / 8 * Complex.I_sq`.
-/
theorem dzEntry_symm {D : ℕ} (T : (Fin D → ℂ) →L[ℝ] BilinSp D) (hT : ∀ u x, T u x = T x u)
    (j a b : Fin D) :
    (1 / 2 : ℂ) * hessEntry a b (T (Pi.single j 1)) +
        (-(Complex.I / 2)) * hessEntry a b (T (Complex.I • Pi.single j 1)) =
      (1 / 2 : ℂ) * hessEntry j b (T (Pi.single a 1)) +
        (-(Complex.I / 2)) * hessEntry j b (T (Complex.I • Pi.single a 1)) := by
  have e1 := hT (Pi.single j 1) (Pi.single a 1)
  have e2 := hT (Pi.single j 1) (Complex.I • Pi.single a 1)
  have e3 := hT (Complex.I • Pi.single j 1) (Pi.single a 1)
  have e4 := hT (Complex.I • Pi.single j 1) (Complex.I • Pi.single a 1)
  simp only [hessEntry_apply, e1, e2, e3, e4]
  push_cast
  linear_combination
    ((T (Complex.I • Pi.single a 1) (Pi.single j 1) (Complex.I • Pi.single b 1) : ℂ) -
      (T (Pi.single a 1) (Complex.I • Pi.single j 1) (Complex.I • Pi.single b 1) : ℂ)) / 8 *
      Complex.I_sq

/- English proof (translation)
Establish `e1` using `hT (Pi.single b 1) (Pi.single a 1) (Pi.single k 1)`. Establish `e2` using `hT (Pi.single b 1) (Complex.I • Pi.single a 1) (Complex.I • Pi.single k 1)`. Establish `e3` using `hT (Pi.single b 1) (Pi.single a 1) (Complex.I • Pi.single k 1)`. Establish `e4` using `hT (Pi.single b 1) (Complex.I • Pi.single a 1) (Pi.single k 1)`. Establish `e5` using `hT (Complex.I • Pi.single b 1) (Pi.single a 1) (Pi.single k 1)`.

Establish `e6` using `hT (Complex.I • Pi.single b 1) (Complex.I • Pi.single a 1) (Complex.I • Pi.single k 1)`. Establish `e7` using `hT (Complex.I • Pi.single b 1) (Pi.single a 1) (Complex.I • Pi.single k 1)`. Establish `e8` using `hT (Complex.I • Pi.single b 1) (Complex.I • Pi.single a 1) (Pi.single k 1)`. Simplify using `only [hessEntry_apply, e1, e2, e3, e4, e5, e6, e7, e8]`. Use `push_cast`.

Take the linear combination `((T (Pi.single k 1) (Complex.I • Pi.single a 1) (Complex.I • Pi.single b 1) : ℂ) - (T (Complex.I • Pi.single k 1) (Complex.I • Pi.single a 1) (Pi.single b 1) : ℂ)) / 8 * Complex.I_sq`.
-/
theorem dzbEntry_symm {D : ℕ} (T : (Fin D → ℂ) →L[ℝ] BilinSp D)
    (hT : ∀ u x y, T u x y = T y x u) (k a b : Fin D) :
    (1 / 2 : ℂ) * hessEntry a b (T (Pi.single k 1)) +
        (Complex.I / 2) * hessEntry a b (T (Complex.I • Pi.single k 1)) =
      (1 / 2 : ℂ) * hessEntry a k (T (Pi.single b 1)) +
        (Complex.I / 2) * hessEntry a k (T (Complex.I • Pi.single b 1)) := by
  have e1 := hT (Pi.single b 1) (Pi.single a 1) (Pi.single k 1)
  have e2 := hT (Pi.single b 1) (Complex.I • Pi.single a 1) (Complex.I • Pi.single k 1)
  have e3 := hT (Pi.single b 1) (Pi.single a 1) (Complex.I • Pi.single k 1)
  have e4 := hT (Pi.single b 1) (Complex.I • Pi.single a 1) (Pi.single k 1)
  have e5 := hT (Complex.I • Pi.single b 1) (Pi.single a 1) (Pi.single k 1)
  have e6 := hT (Complex.I • Pi.single b 1) (Complex.I • Pi.single a 1)
    (Complex.I • Pi.single k 1)
  have e7 := hT (Complex.I • Pi.single b 1) (Pi.single a 1) (Complex.I • Pi.single k 1)
  have e8 := hT (Complex.I • Pi.single b 1) (Complex.I • Pi.single a 1) (Pi.single k 1)
  simp only [hessEntry_apply, e1, e2, e3, e4, e5, e6, e7, e8]
  push_cast
  linear_combination
    ((T (Pi.single k 1) (Complex.I • Pi.single a 1) (Complex.I • Pi.single b 1) : ℂ) -
      (T (Complex.I • Pi.single k 1) (Complex.I • Pi.single a 1) (Pi.single b 1) : ℂ)) / 8 *
      Complex.I_sq

/- English proof (translation)
Introduce `n φ U hU hφ z hz`. Establish `hφz : ∀ i, ContDiffAt ℝ 3 (φ i) z` using `fun i => (hφ i).contDiffAt (hU.mem_nhds hz)`. Establish `hdiff : ∀ i, DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ (φ i))) z` using `fun i => differentiableAt_snd_fderiv _ z (hφz i)`. Use `set T : Fin n → (Fin (n + 1) → ℂ) →L[ℝ] BilinSp (n + 1) := fun i => fderiv ℝ (fderiv ℝ (fderiv ℝ (φ i))) z with hTdef`. Use `set H : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := fun l => hessC (φ l) z with hH`.

Prove the components needed by the constructor for the conclusion. Introduce `k`. Establish `hj : ∀ j, dz j (fun y => hessCof φ y j k) z = ∑ i, mdisc (Function.update (Function.update (Fin.cons 0 H) 0 (Matrix.single j k 1)) i.succ ((1 / 2 : ℂ) • hessMat (T i (Pi.single j 1)) + (-(Complex.I / 2)) • hessMat (T i (Complex.I • Pi.single j 1))))`. Introduce `j`. Take `⟨_, hD⟩` from `hessCof_hasDeriv φ z hdiff j k`.

Rewrite using `[Fin.update_cons_zero]`. Simplify using `only [mdisc_update_comb, Finset.sum_add_distrib, ← Finset.mul_sum]`. Use `show (fderiv ℝ _ z _ - Complex.I * fderiv ℝ _ z _) / 2 = _`. Rewrite using `[hD, hD]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Finset.sum_congr rfl fun j _ => hj j, Finset.sum_comm]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Use `mdisc_sum_row _ 0 i.succ (Fin.succ_ne_zero i).symm k _ fun j a b => ?_` and prove the remaining obligations. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, hessMat_apply, smul_eq_mul]`. Conclude with `dzEntry_symm (T i) (third_fderiv_symm_one_two _ z (hφz i)) j a b`.

Introduce `j`. Establish `hk : ∀ k, dzb k (fun y => hessCof φ y j k) z = ∑ i, mdisc (Function.update (Function.update (Fin.cons 0 H) 0 (Matrix.single j k 1)) i.succ ((1 / 2 : ℂ) • hessMat (T i (Pi.single k 1)) + (Complex.I / 2) • hessMat (T i (Complex.I • Pi.single k 1))))`. Introduce `k`. Take `⟨_, hD⟩` from `hessCof_hasDeriv φ z hdiff j k`. Rewrite using `[Fin.update_cons_zero]`.

Simplify using `only [mdisc_update_comb, Finset.sum_add_distrib, ← Finset.mul_sum]`. Use `show (fderiv ℝ _ z _ + Complex.I * fderiv ℝ _ z _) / 2 = _`. Rewrite using `[hD, hD]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl fun k _ => hk k, Finset.sum_comm]`.

Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Use `mdisc_sum_col _ 0 i.succ (Fin.succ_ne_zero i).symm j _ fun k a b => ?_` and prove the remaining obligations. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, hessMat_apply, smul_eq_mul]`. Use `dzbEntry_symm (T i) (fun u x y => ?_) k a b` and prove the remaining obligations. Rewrite using `[third_fderiv_symm_one_two _ z (hφz i), third_fderiv_symm_two_three _ z (hφz i), third_fderiv_symm_one_two _ z (hφz i)]`.
-/
theorem piolaStatement_statement : PiolaStatement := by
  intro n φ U hU hφ z hz
  have hφz : ∀ i, ContDiffAt ℝ 3 (φ i) z := fun i => (hφ i).contDiffAt (hU.mem_nhds hz)
  have hdiff : ∀ i, DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ (φ i))) z :=
    fun i => differentiableAt_snd_fderiv _ z (hφz i)
  set T : Fin n → (Fin (n + 1) → ℂ) →L[ℝ] BilinSp (n + 1) :=
    fun i => fderiv ℝ (fderiv ℝ (fderiv ℝ (φ i))) z with hTdef
  set H : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := fun l => hessC (φ l) z with hH
  constructor
  · intro k
    have hj : ∀ j, dz j (fun y => hessCof φ y j k) z = ∑ i, mdisc (Function.update
        (Function.update (Fin.cons 0 H) 0 (Matrix.single j k 1)) i.succ
        ((1 / 2 : ℂ) • hessMat (T i (Pi.single j 1)) +
          (-(Complex.I / 2)) • hessMat (T i (Complex.I • Pi.single j 1)))) := by
      intro j
      obtain ⟨_, hD⟩ := hessCof_hasDeriv φ z hdiff j k
      rw [Fin.update_cons_zero]
      simp only [mdisc_update_comb, Finset.sum_add_distrib, ← Finset.mul_sum]
      show (fderiv ℝ _ z _ - Complex.I * fderiv ℝ _ z _) / 2 = _
      rw [hD, hD]; ring
    rw [Finset.sum_congr rfl fun j _ => hj j, Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    refine mdisc_sum_row _ 0 i.succ (Fin.succ_ne_zero i).symm k _ fun j a b => ?_
    simp only [Matrix.add_apply, Matrix.smul_apply, hessMat_apply, smul_eq_mul]
    exact dzEntry_symm (T i) (third_fderiv_symm_one_two _ z (hφz i)) j a b
  · intro j
    have hk : ∀ k, dzb k (fun y => hessCof φ y j k) z = ∑ i, mdisc (Function.update
        (Function.update (Fin.cons 0 H) 0 (Matrix.single j k 1)) i.succ
        ((1 / 2 : ℂ) • hessMat (T i (Pi.single k 1)) +
          (Complex.I / 2) • hessMat (T i (Complex.I • Pi.single k 1)))) := by
      intro k
      obtain ⟨_, hD⟩ := hessCof_hasDeriv φ z hdiff j k
      rw [Fin.update_cons_zero]
      simp only [mdisc_update_comb, Finset.sum_add_distrib, ← Finset.mul_sum]
      show (fderiv ℝ _ z _ + Complex.I * fderiv ℝ _ z _) / 2 = _
      rw [hD, hD]; ring
    rw [Finset.sum_congr rfl fun k _ => hk k, Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    refine mdisc_sum_col _ 0 i.succ (Fin.succ_ne_zero i).symm j _ fun k a b => ?_
    simp only [Matrix.add_apply, Matrix.smul_apply, hessMat_apply, smul_eq_mul]
    refine dzbEntry_symm (T i) (fun u x y => ?_) k a b
    rw [third_fderiv_symm_one_two _ z (hφz i), third_fderiv_symm_two_three _ z (hφz i), third_fderiv_symm_one_two _ z (hφz i)]

section DzCalc

variable {D : ℕ} {j : Fin D} {f g : (Fin D → ℂ) → ℂ} {z : Fin D → ℂ}

/- English proof (translation)
Establish `e : fderiv ℝ f z = fderiv ℝ g z` using `Filter.EventuallyEq.fderiv_eq h`. Unfold `dz`. Rewrite using `[e]`.
-/
theorem dz_congr (h : f =ᶠ[𝓝 z] g) : dz j f z = dz j g z := by
  have e : fderiv ℝ f z = fderiv ℝ g z := Filter.EventuallyEq.fderiv_eq h
  unfold dz
  rw [e]

/- English proof (translation)
Establish `e : fderiv ℝ f z = fderiv ℝ g z` using `Filter.EventuallyEq.fderiv_eq h`. Unfold `dzb`. Rewrite using `[e]`.
-/
theorem dzb_congr (h : f =ᶠ[𝓝 z] g) : dzb j f z = dzb j g z := by
  have e : fderiv ℝ f z = fderiv ℝ g z := Filter.EventuallyEq.fderiv_eq h
  unfold dzb
  rw [e]

/- English proof (translation)
Establish `e : fderiv ℝ (fun y => f y + g y) z = fderiv ℝ f z + fderiv ℝ g z` using `by first`. Consider the case `(exact (hf.hasFDerivAt.add hg.hasFDerivAt).fderiv)`. Consider the case `(exact (hf.hasFDerivAt.fun_add hg.hasFDerivAt).fderiv)`. Consider the case `(exact fderiv_add hf hg)`. Consider the case `(exact fderiv_fun_add hf hg)`.

Unfold `dz`. Rewrite using `[e, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dz_add (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dz j (fun y => f y + g y) z = dz j f z + dz j g z := by
  have e : fderiv ℝ (fun y => f y + g y) z = fderiv ℝ f z + fderiv ℝ g z := by
    first
    | (exact (hf.hasFDerivAt.add hg.hasFDerivAt).fderiv)
    | (exact (hf.hasFDerivAt.fun_add hg.hasFDerivAt).fderiv)
    | (exact fderiv_add hf hg)
    | (exact fderiv_fun_add hf hg)
  unfold dz
  rw [e, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]
  ring

/- English proof (translation)
Establish `e : fderiv ℝ (fun y => f y * g y) z = f z • fderiv ℝ g z + g z • fderiv ℝ f z` using `by first`. Consider the case `(exact (hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv)`. Consider the case `(exact (hf.hasFDerivAt.fun_mul hg.hasFDerivAt).fderiv)`. Consider the case `(exact fderiv_mul hf hg)`. Consider the case `(exact fderiv_fun_mul hf hg)`.

Unfold `dz`. Rewrite using `[e]`. Simplify using `only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dz_mul (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dz j (fun y => f y * g y) z = dz j f z * g z + f z * dz j g z := by
  have e : fderiv ℝ (fun y => f y * g y) z = f z • fderiv ℝ g z + g z • fderiv ℝ f z := by
    first
    | (exact (hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv)
    | (exact (hf.hasFDerivAt.fun_mul hg.hasFDerivAt).fderiv)
    | (exact fderiv_mul hf hg)
    | (exact fderiv_fun_mul hf hg)
  unfold dz
  rw [e]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Rewrite using `[dz_congr h]`. Unfold `dz`. Simplify using the standard rewrite rules.
-/
theorem dz_of_eventually_zero (h : f =ᶠ[𝓝 z] fun _ => 0) : dz j f z = 0 := by
  rw [dz_congr h]
  unfold dz
  simp

/- English proof (translation)
Rewrite using `[dzb_congr h]`. Unfold `dzb`. Simplify using the standard rewrite rules.
-/
theorem dzb_of_eventually_zero (h : f =ᶠ[𝓝 z] fun _ => 0) : dzb j f z = 0 := by
  rw [dzb_congr h]
  unfold dzb
  simp

/- English proof (translation)
Apply the tactic sequence `have hd : DifferentiableAt ℝ (fderiv ℝ f) z := (hf.fderiv_right (m := 1) (by first | norm_num | simp | rfl)).differentiableAt (by first | norm_num | simp | exact one_ne_zero)`. Establish `h1 : DifferentiableAt ℝ (fun y => fderiv ℝ f y (Pi.single j 1)) z` using `hd.clm_apply (differentiableAt_const _)`. Establish `h2 : DifferentiableAt ℝ (fun y => fderiv ℝ f y (Complex.I • Pi.single j 1)) z` using `hd.clm_apply (differentiableAt_const _)`. Establish `h3 : DifferentiableAt ℝ (fun y => Complex.I * fderiv ℝ f y (Complex.I • Pi.single j 1)) z` using `(differentiableAt_const _).mul h2`. Establish `h4 : DifferentiableAt ℝ (fun y => fderiv ℝ f y (Pi.single j 1) + Complex.I * fderiv ℝ f y (Complex.I • Pi.single j 1)) z` using `h1.add h3`.

Establish `h5 : DifferentiableAt ℝ (fun y => (fderiv ℝ f y (Pi.single j 1) + Complex.I * fderiv ℝ f y (Complex.I • Pi.single j 1)) / 2) z` using `by first`. Consider the case `(exact h4.div_const (2 : ℂ))`. Consider the case `(simpa only [div_eq_mul_inv] using h4.mul_const (2⁻¹ : ℂ))`. Consider the case `(fun_prop)`. Conclude with `h5`.
-/
theorem differentiableAt_dzb (hf : ContDiffAt ℝ 2 f z) : DifferentiableAt ℝ (dzb j f) z := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by first | norm_num | simp | rfl)).differentiableAt (by first | norm_num | simp | exact one_ne_zero)
  have h1 : DifferentiableAt ℝ (fun y => fderiv ℝ f y (Pi.single j 1)) z :=
    hd.clm_apply (differentiableAt_const _)
  have h2 : DifferentiableAt ℝ (fun y => fderiv ℝ f y (Complex.I • Pi.single j 1)) z :=
    hd.clm_apply (differentiableAt_const _)
  have h3 : DifferentiableAt ℝ (fun y => Complex.I * fderiv ℝ f y (Complex.I • Pi.single j 1)) z :=
    (differentiableAt_const _).mul h2
  have h4 : DifferentiableAt ℝ (fun y => fderiv ℝ f y (Pi.single j 1) +
      Complex.I * fderiv ℝ f y (Complex.I • Pi.single j 1)) z := h1.add h3
  have h5 : DifferentiableAt ℝ (fun y => (fderiv ℝ f y (Pi.single j 1) +
      Complex.I * fderiv ℝ f y (Complex.I • Pi.single j 1)) / 2) z := by
    first
      | (exact h4.div_const (2 : ℂ))
      | (simpa only [div_eq_mul_inv] using h4.mul_const (2⁻¹ : ℂ))
      | (fun_prop)
  exact h5

end DzCalc

/- English proof (translation)
Rewrite using `[← (Equiv.mk (compl : Finset (Fin N) → Finset (Fin N)) compl compl_compl compl_compl).sum_comp]`. Simplify using `only [Equiv.coe_fn_mk]`. Establish `hc : ∀ S : Finset (Fin N), N - Sᶜ.card = S.card`. Introduce `S`. Establish `h1` using `Finset.card_le_univ S`.

Rewrite `h1` using `[Fintype.card_fin]`. Rewrite using `[Finset.card_compl, Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers. Establish `hsub : ∀ S : Finset (Fin N), (T ⊆ Sᶜ) ↔ (S ⊆ Tᶜ)` using `fun S => by`. Prove the components needed by the constructor for the conclusion.

Introduce `h x hx`. Rewrite using `[Finset.mem_compl]`. Introduce `hxT`. Conclude with `(Finset.mem_compl.mp (h hxT)) hx`. Introduce `h x hx`.

Rewrite using `[Finset.mem_compl]`. Introduce `hxS`. Conclude with `(Finset.mem_compl.mp (h hxS)) hx`. Simplify using `only [hc, hsub]`. Rewrite using `[← Finset.sum_filter]`.

Establish `hf : Finset.univ.filter (fun S : Finset (Fin N) => S ⊆ Tᶜ) = Tᶜ.powerset`. Use extensionality with `S`. Simplify using the standard rewrite rules. Rewrite using `[hf]`. Establish `h0 : (∑ m ∈ Tᶜ.powerset, (-1 : ℤ) ^ m.card) = if Tᶜ = ∅ then 1 else 0` using `Finset.sum_powerset_neg_one_pow_card`.

Establish `h1 : (∑ m ∈ Tᶜ.powerset, (-1 : ℂ) ^ m.card) = ((∑ m ∈ Tᶜ.powerset, (-1 : ℤ) ^ m.card : ℤ) : ℂ)` using `by simp`. Rewrite using `[h1, h0]`. Distinguish the cases in `hT : T = Finset.univ`. Establish `h2 : Tᶜ = ∅` using `by rw [hT]; simp`. Simplify using `[h2, hT]`.

Establish `h2 : Tᶜ ≠ ∅`. Introduce `h`. Apply `hT` to reduce the goal to its premises. Use extensionality with `x`. Simplify using `only [Finset.mem_univ, iff_true]`.

Assume the negation of the conclusion as `hx`. Establish `hx' : x ∈ Tᶜ` using `Finset.mem_compl.mpr hx`. Rewrite `hx'` using `[h]`. Simplify using `at hx'`. Simplify using `[h2, hT]`.
-/
private lemma sum_superset_neg_one_pow_fin_eq_ite_univ (N : ℕ) (T : Finset (Fin N)) :
    ∑ S : Finset (Fin N), (if T ⊆ S then (-1 : ℂ) ^ (N - S.card) else 0) =
      if T = Finset.univ then 1 else 0 := by
  rw [← (Equiv.mk (compl : Finset (Fin N) → Finset (Fin N)) compl compl_compl
    compl_compl).sum_comp]
  simp only [Equiv.coe_fn_mk]
  have hc : ∀ S : Finset (Fin N), N - Sᶜ.card = S.card := by
    intro S
    have h1 := Finset.card_le_univ S
    rw [Fintype.card_fin] at h1
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  have hsub : ∀ S : Finset (Fin N), (T ⊆ Sᶜ) ↔ (S ⊆ Tᶜ) := fun S => by
    constructor
    · intro h x hx
      rw [Finset.mem_compl]
      intro hxT
      exact (Finset.mem_compl.mp (h hxT)) hx
    · intro h x hx
      rw [Finset.mem_compl]
      intro hxS
      exact (Finset.mem_compl.mp (h hxS)) hx
  simp only [hc, hsub]
  rw [← Finset.sum_filter]
  have hf : Finset.univ.filter (fun S : Finset (Fin N) => S ⊆ Tᶜ) = Tᶜ.powerset := by
    ext S; simp
  rw [hf]
  have h0 : (∑ m ∈ Tᶜ.powerset, (-1 : ℤ) ^ m.card) = if Tᶜ = ∅ then 1 else 0 :=
    Finset.sum_powerset_neg_one_pow_card
  have h1 : (∑ m ∈ Tᶜ.powerset, (-1 : ℂ) ^ m.card) =
      ((∑ m ∈ Tᶜ.powerset, (-1 : ℤ) ^ m.card : ℤ) : ℂ) := by simp
  rw [h1, h0]
  by_cases hT : T = Finset.univ
  · have h2 : Tᶜ = ∅ := by rw [hT]; simp
    simp [h2, hT]
  · have h2 : Tᶜ ≠ ∅ := by
      intro h
      apply hT
      ext x
      simp only [Finset.mem_univ, iff_true]
      by_contra hx
      have hx' : x ∈ Tᶜ := Finset.mem_compl.mpr hx
      rw [h] at hx'
      simp at hx'
    simp [h2, hT]

/- English proof (translation)
Unfold `mdisc`. Use `congr 1`. Establish `hdet : ∀ S : Finset (Fin N), (∑ k ∈ S, M k).det = ∑ σ : Equiv.Perm (Fin N), ∑ f : Fin N → Fin N, (if ∀ i, f i ∈ S then ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M (f i) (σ i) i else 0)`. Introduce `S`. Rewrite using `[Matrix.det_apply']`.

Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Establish `hpf : Fintype.piFinset (fun _ : Fin N => S) = Finset.univ.filter (fun f : Fin N → Fin N => ∀ i, f i ∈ S)`. Use extensionality with `f`. Simplify using `[Fintype.mem_piFinset]`. Establish `hp : ∏ i, (∑ k ∈ S, M k) (σ i) i = ∑ f ∈ Fintype.piFinset (fun _ : Fin N => S), ∏ i, M (f i) (σ i) i`.

Simplify using `only [Matrix.sum_apply]`. Rewrite using `[Finset.prod_univ_sum]`. Rewrite using `[hp, hpf, Finset.sum_filter, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun f _ => ?_` and prove the remaining obligations. Rewrite using `[mul_ite, mul_zero]`.

Simplify using `only [hdet, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm (s := (Finset.univ : Finset (Finset (Fin N))))]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm (s := (Finset.univ : Finset (Finset (Fin N))))]`. Use `Finset.sum_congr rfl fun f _ => ?_` and prove the remaining obligations.

Establish `hiff : ∀ S : Finset (Fin N), (∀ i, f i ∈ S) ↔ Finset.univ.image f ⊆ S` using `fun S => by`. Simplify using `[Finset.image_subset_iff]`. Establish `hS : ∀ S : Finset (Fin N), (-1 : ℂ) ^ (N - S.card) * (if ∀ i, f i ∈ S then ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M (f i) (σ i) i else 0) = (if Finset.univ.image f ⊆ S then (-1 : ℂ) ^ (N - S.card) else 0) * (((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M (f i) (σ i) i)`. Introduce `S`. Distinguish the cases in `h : ∀ i, f i ∈ S`.

Rewrite using `[if_pos h, if_pos ((hiff S).mp h)]`. Rewrite using `[if_neg h, if_neg (fun h' => h ((hiff S).mpr h')), mul_zero, zero_mul]`. Rewrite using `[Finset.sum_congr rfl fun S _ => hS S, ← Finset.sum_mul, sum_superset_neg_one_pow_fin_eq_ite_univ]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private lemma mdisc_eq_inv_factorial_mul_sum_sign_prod {N : ℕ} (M : Fin N → Matrix (Fin N) (Fin N) ℂ) :
    mdisc M = (1 / (N.factorial : ℂ)) * ∑ σ : Equiv.Perm (Fin N), ∑ f : Fin N → Fin N,
      (if Finset.univ.image f = Finset.univ then
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M (f i) (σ i) i else 0) := by
  unfold mdisc
  congr 1
  have hdet : ∀ S : Finset (Fin N), (∑ k ∈ S, M k).det =
      ∑ σ : Equiv.Perm (Fin N), ∑ f : Fin N → Fin N,
        (if ∀ i, f i ∈ S then ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M (f i) (σ i) i else 0) := by
    intro S
    rw [Matrix.det_apply']
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hpf : Fintype.piFinset (fun _ : Fin N => S) =
        Finset.univ.filter (fun f : Fin N → Fin N => ∀ i, f i ∈ S) := by
      ext f; simp [Fintype.mem_piFinset]
    have hp : ∏ i, (∑ k ∈ S, M k) (σ i) i =
        ∑ f ∈ Fintype.piFinset (fun _ : Fin N => S), ∏ i, M (f i) (σ i) i := by
      simp only [Matrix.sum_apply]
      rw [Finset.prod_univ_sum]
    rw [hp, hpf, Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [mul_ite, mul_zero]
  simp only [hdet, Finset.mul_sum]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Finset (Fin N))))]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Finset (Fin N))))]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hiff : ∀ S : Finset (Fin N), (∀ i, f i ∈ S) ↔ Finset.univ.image f ⊆ S := fun S => by
    simp [Finset.image_subset_iff]
  have hS : ∀ S : Finset (Fin N), (-1 : ℂ) ^ (N - S.card) *
      (if ∀ i, f i ∈ S then ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M (f i) (σ i) i else 0) =
      (if Finset.univ.image f ⊆ S then (-1 : ℂ) ^ (N - S.card) else 0) *
        (((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M (f i) (σ i) i) := by
    intro S
    by_cases h : ∀ i, f i ∈ S
    · rw [if_pos h, if_pos ((hiff S).mp h)]
    · rw [if_neg h, if_neg (fun h' => h ((hiff S).mpr h')), mul_zero, zero_mul]
  rw [Finset.sum_congr rfl fun S _ => hS S, ← Finset.sum_mul, sum_superset_neg_one_pow_fin_eq_ite_univ]
  split_ifs <;> simp

/- English proof (translation)
Establish `hs : Function.Surjective f` using `fun y => by`. Establish `hy : y ∈ Finset.univ.image f` using `by rw [hf]; exact Finset.mem_univ y`. Simplify using `using hy`. Establish `hi : Function.Injective f` using `Finite.injective_iff_surjective.mpr hs`. Take `⟨i0, hi0⟩` from `hs 0`.

Establish `hne : ∀ i ∈ Finset.univ.erase i0, f i ≠ 0` using `fun i hi' h => (Finset.mem_erase.mp hi').1 (hi (h.trans hi0.symm))`. Establish `hrest : ∀ X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, ∏ i ∈ Finset.univ.erase i0, (Fin.cons X B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (f i) (σ i) i = ∏ i ∈ Finset.univ.erase i0, (Fin.cons 0 B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (f i) (σ i) i`. Introduce `X`. Use `Finset.prod_congr rfl fun i hi' => ?_` and prove the remaining obligations. Take `⟨m, hm⟩` from `Fin.exists_succ_eq.mpr (hne i hi')`.

Rewrite using `[← hm, Fin.cons_succ, Fin.cons_succ]`. Establish `hsplit : ∀ X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, ∏ i, (Fin.cons X B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (f i) (σ i) i = X (σ i0) i0 * ∏ i ∈ Finset.univ.erase i0, (Fin.cons 0 B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (f i) (σ i) i`. Introduce `X`. Rewrite using `[← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i0), hrest X, hi0, Fin.cons_zero]`. Simplify using `only [hsplit]`.

Simplify using `only [← mul_assoc, ← Finset.sum_mul]`. Use `congr 1`. Simplify using `only [Matrix.single_apply]`. Use `first`. Consider the case `(rw [Finset.sum_eq_single (σ i0) (fun x _ hx => by simp [hx]) (by simp)]`.

Rewrite using `[Finset.sum_eq_single i0 (fun x _ hx => by simp [hx]) (by simp)]`. Use the proof step `simp)`. Consider the case `(simp [ite_and])`. Consider the case `(simp [ite_and, Finset.sum_ite_eq', Finset.sum_ite_eq])`.
-/
private lemma prod_cons_eq_sum_mul_prod_cons_single {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (σ : Equiv.Perm (Fin (n + 1)))
    (f : Fin (n + 1) → Fin (n + 1)) (hf : Finset.univ.image f = Finset.univ) :
    ∏ i, (Fin.cons A B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (f i) (σ i) i =
      ∑ j, ∑ k, A j k * ∏ i, (Fin.cons (Matrix.single j k 1) B :
        Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (f i) (σ i) i := by
  have hs : Function.Surjective f := fun y => by
    have hy : y ∈ Finset.univ.image f := by rw [hf]; exact Finset.mem_univ y
    simpa using hy
  have hi : Function.Injective f := Finite.injective_iff_surjective.mpr hs
  obtain ⟨i0, hi0⟩ := hs 0
  have hne : ∀ i ∈ Finset.univ.erase i0, f i ≠ 0 := fun i hi' h =>
    (Finset.mem_erase.mp hi').1 (hi (h.trans hi0.symm))
  have hrest : ∀ X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      ∏ i ∈ Finset.univ.erase i0,
        (Fin.cons X B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (f i) (σ i) i =
      ∏ i ∈ Finset.univ.erase i0,
        (Fin.cons 0 B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (f i) (σ i) i := by
    intro X
    refine Finset.prod_congr rfl fun i hi' => ?_
    obtain ⟨m, hm⟩ := Fin.exists_succ_eq.mpr (hne i hi')
    rw [← hm, Fin.cons_succ, Fin.cons_succ]
  have hsplit : ∀ X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      ∏ i, (Fin.cons X B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (f i) (σ i) i =
        X (σ i0) i0 * ∏ i ∈ Finset.univ.erase i0,
          (Fin.cons 0 B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (f i) (σ i) i := by
    intro X
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i0), hrest X, hi0, Fin.cons_zero]
  simp only [hsplit]
  simp only [← mul_assoc, ← Finset.sum_mul]
  congr 1
  simp only [Matrix.single_apply]
  first
    | (rw [Finset.sum_eq_single (σ i0) (fun x _ hx => by simp [hx]) (by simp)]
       rw [Finset.sum_eq_single i0 (fun x _ hx => by simp [hx]) (by simp)]
       simp)
    | (simp [ite_and])
    | (simp [ite_and, Finset.sum_ite_eq', Finset.sum_ite_eq])

/- English proof (translation)
Establish `e1 : ∀ g : Fin (n + 1) → Fin (n + 1) → Equiv.Perm (Fin (n + 1)) → (Fin (n + 1) → Fin (n + 1)) → ℂ, ∑ j, ∑ k, ∑ σ, ∑ f, g j k σ f = ∑ σ, ∑ f, ∑ j, ∑ k, g j k σ f`. Introduce `g`. Combine the equalities or inequalities in the displayed calculation. Establish `ht : ∀ (σ : Equiv.Perm (Fin (n + 1))) (f : Fin (n + 1) → Fin (n + 1)), (if Finset.univ.image f = Finset.univ then ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, (Fin.cons A B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (f i) (σ i) i else 0) = ∑ j, ∑ k, A j k * (if Finset.univ.ima …`. Introduce `σ f`.

Distinguish the cases in `hf : Finset.univ.image f = Finset.univ`. Simplify using `only [if_pos hf]`. Rewrite using `[prod_cons_eq_sum_mul_prod_cons_single A B σ f hf, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Simplify using `[if_neg hf]`. Rewrite using `[mdisc_eq_inv_factorial_mul_sum_sign_prod]`. Simplify using `only [mixedCof, mdisc_eq_inv_factorial_mul_sum_sign_prod]`.

Simplify using `only [ht]`. Simplify using `only [Finset.mul_sum, e1]`. Use `Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mixedDisc_cons_eq_sum {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    mdisc (Fin.cons A B) = ∑ j, ∑ k, A j k * mixedCof B j k := by
  have e1 : ∀ g : Fin (n + 1) → Fin (n + 1) → Equiv.Perm (Fin (n + 1)) →
      (Fin (n + 1) → Fin (n + 1)) → ℂ,
      ∑ j, ∑ k, ∑ σ, ∑ f, g j k σ f = ∑ σ, ∑ f, ∑ j, ∑ k, g j k σ f := by
    intro g
    calc ∑ j, ∑ k, ∑ σ, ∑ f, g j k σ f = ∑ j, ∑ σ, ∑ k, ∑ f, g j k σ f :=
          Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = ∑ σ, ∑ j, ∑ k, ∑ f, g j k σ f := Finset.sum_comm
      _ = ∑ σ, ∑ j, ∑ f, ∑ k, g j k σ f :=
          Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = ∑ σ, ∑ f, ∑ j, ∑ k, g j k σ f := Finset.sum_congr rfl fun σ _ => Finset.sum_comm
  have ht : ∀ (σ : Equiv.Perm (Fin (n + 1))) (f : Fin (n + 1) → Fin (n + 1)),
      (if Finset.univ.image f = Finset.univ then ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ i, (Fin.cons A B : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (f i) (σ i) i
        else 0) =
      ∑ j, ∑ k, A j k * (if Finset.univ.image f = Finset.univ then
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, (Fin.cons (Matrix.single j k 1) B :
          Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (f i) (σ i) i else 0) := by
    intro σ f
    by_cases hf : Finset.univ.image f = Finset.univ
    · simp only [if_pos hf]
      rw [prod_cons_eq_sum_mul_prod_cons_single A B σ f hf, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    · simp [if_neg hf]
  rw [mdisc_eq_inv_factorial_mul_sum_sign_prod]
  simp only [mixedCof, mdisc_eq_inv_factorial_mul_sum_sign_prod]
  simp only [ht]
  simp only [Finset.mul_sum, e1]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun f _ =>
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/- English proof (translation)
Establish `e : (fun k => hessC ((Fin.cons v φ : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℝ) k) z) = Fin.cons (hessC v z) fun i => hessC (φ i) z`. Use function extensionality and compare the values at `k`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) k <;> simp`. Rewrite using `[maDens, e]`.
-/
theorem maDens_cons_eq {n : ℕ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (v : (Fin (n + 1) → ℂ) → ℝ)
    (z : Fin (n + 1) → ℂ) :
    maDens (Fin.cons v φ) z = ((n + 1).factorial : ℝ) * (2 / Real.pi) ^ (n + 1) *
      (mdisc (Fin.cons (hessC v z) fun i => hessC (φ i) z)).re := by
  have e : (fun k => hessC ((Fin.cons v φ : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℝ) k) z) =
      Fin.cons (hessC v z) fun i => hessC (φ i) z := by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k <;> simp
  rw [maDens, e]

/- English proof (translation)
Introduce `n φ v U hU hv z hz`. Establish `hs : ∀ j k : Fin (n + 1), hessC v z j k = dz j (dzb k (cplx v)) z`. Introduce `j k`. Establish `hv2 : ContDiffAt ℝ 2 v z` using `hv.contDiffAt (hU.mem_nhds hz)`. Apply the tactic sequence `have hDv : DifferentiableAt ℝ (fderiv ℝ v) z := (hv2.fderiv_right (m := 1) (by first | norm_num | simp | rfl)).differentiableAt (by first | norm_num | simp | exact one_ne_zero)`.

Establish `hw : ∀ w : Fin (n + 1) → ℂ, HasFDerivAt (fun y => ((fderiv ℝ v y w : ℝ) : ℂ)) (Complex.ofRealCLM.comp ((ContinuousLinearMap.apply ℝ ℝ w).comp (fderiv ℝ (fderiv ℝ v) z))) z` using `fun w => Complex.ofRealCLM.hasFDerivAt.comp z ((ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp z hDv.hasFDerivAt)`. Establish `hg : HasFDerivAt (fun y => (1 / 2 : ℂ) * (((fderiv ℝ v y (Pi.single k 1) : ℝ) : ℂ) + Complex.I * ((fderiv ℝ v y (Complex.I • Pi.single k 1) : ℝ) : ℂ))) ((1 / 2 : ℂ) • (Complex.ofRealCLM.comp ((ContinuousLinearMap.apply ℝ ℝ (Pi.single k 1)).comp (fderiv ℝ (fderiv ℝ v) z)) + Comple …` using `by first`. Consider the case `(exact ((hw _).add ((hw _).const_mul Complex.I)).const_mul (1 / 2 : ℂ))`. Consider the case `(exact ((hw _).fun_add ((hw _).const_mul Complex.I)).const_mul (1 / 2 : ℂ))`. Consider the case `(exact ((hw _).add ((hw _).fun_const_mul Complex.I)).fun_const_mul (1 / 2 : ℂ))`.

Consider the case `(exact ((hw _).fun_add ((hw _).fun_const_mul Complex.I)).fun_const_mul (1 / 2 : ℂ))`. Establish `heq : dzb k (cplx v) =ᶠ[𝓝 z] fun y => (1 / 2 : ℂ) * (((fderiv ℝ v y (Pi.single k 1) : ℝ) : ℂ) + Complex.I * ((fderiv ℝ v y (Complex.I • Pi.single k 1) : ℝ) : ℂ))` using `by filter_upwards [hU.mem_nhds hz] with y hy`. Apply the tactic sequence `have hdy : DifferentiableAt ℝ v y := (hv.contDiffAt (hU.mem_nhds hy)).differentiableAt (by first | norm_num | simp | exact one_ne_zero)`. Establish `hf : fderiv ℝ (cplx v) y = Complex.ofRealCLM.comp (fderiv ℝ v y)` using `(Complex.ofRealCLM.hasFDerivAt.comp y hdy.hasFDerivAt).fderiv`. Unfold `dzb`.

Rewrite using `[hf]`. Simplify using `only [ContinuousLinearMap.coe_comp', Function.comp_apply, Complex.ofRealCLM_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[dz_congr heq]`. Unfold `dz`.

Rewrite using `[hg.fderiv]`. Simplify using `only [hessC, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.apply_apply, Complex.ofRealCLM_apply, smul_eq_mul]`. Use `push_cast`. Take the linear combination `((fderiv ℝ (fderiv ℝ v) z (Complex.I • Pi.single j 1) (Complex.I • Pi.single k 1) : ℝ) : ℂ) / 4 * Complex.I_sq`. Rewrite using `[maDens_cons_eq, mixedDisc_cons_eq_sum]`.

Establish `hsum : (∑ j, ∑ k, hessC v z j k * mixedCof (fun i => hessC (φ i) z) j k) = ∑ j, ∑ k, hessCof φ z j k * dz j (dzb k (cplx v)) z`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hs j k]`. Simplify using `only [hessCof]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hsum]`.
-/
theorem monge_ampere_density_cofactor : MaDensCofStatement := by
  intro n φ v U hU hv z hz
  have hs : ∀ j k : Fin (n + 1), hessC v z j k = dz j (dzb k (cplx v)) z := by
    intro j k
    have hv2 : ContDiffAt ℝ 2 v z := hv.contDiffAt (hU.mem_nhds hz)
    have hDv : DifferentiableAt ℝ (fderiv ℝ v) z :=
      (hv2.fderiv_right (m := 1) (by first | norm_num | simp | rfl)).differentiableAt (by first | norm_num | simp | exact one_ne_zero)
    have hw : ∀ w : Fin (n + 1) → ℂ, HasFDerivAt (fun y => ((fderiv ℝ v y w : ℝ) : ℂ))
        (Complex.ofRealCLM.comp
          ((ContinuousLinearMap.apply ℝ ℝ w).comp (fderiv ℝ (fderiv ℝ v) z))) z :=
      fun w => Complex.ofRealCLM.hasFDerivAt.comp z
        ((ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp z hDv.hasFDerivAt)
    have hg : HasFDerivAt (fun y => (1 / 2 : ℂ) * (((fderiv ℝ v y (Pi.single k 1) : ℝ) : ℂ) +
        Complex.I * ((fderiv ℝ v y (Complex.I • Pi.single k 1) : ℝ) : ℂ)))
        ((1 / 2 : ℂ) • (Complex.ofRealCLM.comp ((ContinuousLinearMap.apply ℝ ℝ (Pi.single k 1)).comp
            (fderiv ℝ (fderiv ℝ v) z)) +
          Complex.I • Complex.ofRealCLM.comp
            ((ContinuousLinearMap.apply ℝ ℝ (Complex.I • Pi.single k 1)).comp
              (fderiv ℝ (fderiv ℝ v) z)))) z := by
      first
        | (exact ((hw _).add ((hw _).const_mul Complex.I)).const_mul (1 / 2 : ℂ))
        | (exact ((hw _).fun_add ((hw _).const_mul Complex.I)).const_mul (1 / 2 : ℂ))
        | (exact ((hw _).add ((hw _).fun_const_mul Complex.I)).fun_const_mul (1 / 2 : ℂ))
        | (exact ((hw _).fun_add ((hw _).fun_const_mul Complex.I)).fun_const_mul (1 / 2 : ℂ))
    have heq : dzb k (cplx v) =ᶠ[𝓝 z] fun y => (1 / 2 : ℂ) *
        (((fderiv ℝ v y (Pi.single k 1) : ℝ) : ℂ) +
          Complex.I * ((fderiv ℝ v y (Complex.I • Pi.single k 1) : ℝ) : ℂ)) := by
      filter_upwards [hU.mem_nhds hz] with y hy
      have hdy : DifferentiableAt ℝ v y :=
        (hv.contDiffAt (hU.mem_nhds hy)).differentiableAt (by first | norm_num | simp | exact one_ne_zero)
      have hf : fderiv ℝ (cplx v) y = Complex.ofRealCLM.comp (fderiv ℝ v y) :=
        (Complex.ofRealCLM.hasFDerivAt.comp y hdy.hasFDerivAt).fderiv
      unfold dzb
      rw [hf]
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, Complex.ofRealCLM_apply]
      ring
    rw [dz_congr heq]
    unfold dz
    rw [hg.fderiv]
    simp only [hessC, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.apply_apply,
      Complex.ofRealCLM_apply, smul_eq_mul]
    push_cast
    linear_combination ((fderiv ℝ (fderiv ℝ v) z (Complex.I • Pi.single j 1)
      (Complex.I • Pi.single k 1) : ℝ) : ℂ) / 4 * Complex.I_sq
  rw [maDens_cons_eq, mixedDisc_cons_eq_sum]
  have hsum : (∑ j, ∑ k, hessC v z j k * mixedCof (fun i => hessC (φ i) z) j k) =
      ∑ j, ∑ k, hessCof φ z j k * dz j (dzb k (cplx v)) z := by
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hs j k]
    simp only [hessCof]
    ring
  rw [hsum]

def insL {n : ℕ} (j : Fin (n + 1)) : (Fin n → ℂ) →L[ℝ] (Fin (n + 1) → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => Fin.insertNth (α := fun _ => ℂ) j 0 y
      map_add' := fun x y => by
        ext i; refine Fin.succAboveCases j ?_ (fun l => ?_) i <;> simp
      map_smul' := fun c x => by
        ext i; refine Fin.succAboveCases j ?_ (fun l => ?_) i <;> simp }

end

end ReciprocityTheory.AnForm.A
