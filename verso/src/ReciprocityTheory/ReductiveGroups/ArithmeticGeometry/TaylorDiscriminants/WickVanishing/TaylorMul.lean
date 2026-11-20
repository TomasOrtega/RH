import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Taylor

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.TM

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.PullbackSections
open scoped ContDiff Topology

variable {g : ℕ}

/- English proof (translation)
Unfold `mD lD`. Rewrite using `[((hfh.iteratedFDeriv ℂ _).eq_of_nhds)]`.
-/
theorem mD_local {f h : (Fin g → ℂ) → ℂ} (hfh : f =ᶠ[𝓝 0] h) (s : Multiset (Fin g → ℂ)) :
    mD f 0 s = mD h 0 s := by
  unfold mD lD
  rw [((hfh.iteratedFDeriv ℂ _).eq_of_nhds)]

/- English proof (translation)
Use extensionality with `n`. Use `show mD f 0 (dirs n + s) / fct n = mD h 0 (dirs n + s) / fct n`. Rewrite using `[mD_local hfh]`.
-/
theorem tay_local {f h : (Fin g → ℂ) → ℂ} (hfh : f =ᶠ[𝓝 0] h) (s : Multiset (Fin g → ℂ)) : tay f s = tay h s := by
  ext n
  show mD f 0 (dirs n + s) / fct n = mD h 0 (dirs n + s) / fct n
  rw [mD_local hfh]

/- English proof (translation)
Unfold `mD lD`. Rewrite using `[iteratedFDeriv_add_apply (hf.of_le le_top) (hh.of_le le_top)]`. Both sides reduce to the same expression.
-/
theorem mD_add {f h : (Fin g → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) (hh : ContDiffAt ℂ ω h 0)
    (s : Multiset (Fin g → ℂ)) : mD (f + h) 0 s = mD f 0 s + mD h 0 s := by
  unfold mD lD
  rw [iteratedFDeriv_add_apply (hf.of_le le_top) (hh.of_le le_top)]
  rfl

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[map_add]`. Use `show mD (f + h) 0 (dirs n + s) / fct n = mD f 0 (dirs n + s) / fct n + mD h 0 (dirs n + s) / fct n`. Rewrite using `[mD_add hf hh, add_div]`.
-/
theorem tay_add {f h : (Fin g → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) (hh : ContDiffAt ℂ ω h 0)
    (s : Multiset (Fin g → ℂ)) : tay (f + h) s = tay f s + tay h s := by
  ext n
  rw [map_add]
  show mD (f + h) 0 (dirs n + s) / fct n = mD f 0 (dirs n + s) / fct n + mD h 0 (dirs n + s) / fct n
  rw [mD_add hf hh, add_div]

/- English proof (translation)
Establish `key : ∀ l : List (Fin g → ℂ), l = [] → iteratedFDeriv ℂ l.length θ 0 (fun i => l.get i) = θ 0`. Introduce and unpack `l rfl`. Simplify using the standard rewrite rules. Conclude with `key _ (Multiset.toList_eq_nil.2 rfl)`.
-/
theorem mD_zero (θ : (Fin g → ℂ) → ℂ) : mD θ 0 0 = θ 0 := by
  have key : ∀ l : List (Fin g → ℂ), l = [] →
      iteratedFDeriv ℂ l.length θ 0 (fun i => l.get i) = θ 0 := by
    rintro l rfl
    simp
  exact key _ (Multiset.toList_eq_nil.2 rfl)

/- English proof (translation)
Distinguish the cases in `hs : s = 0`. Substitute `hs` using the available equality. Establish `key : ∀ l : List (Fin g → ℂ), l = [] → iteratedFDeriv ℂ l.length (fun _ : Fin g → ℂ => c) 0 (fun i => l.get i) = c`. Introduce and unpack `l rfl`. Simplify using the standard rewrite rules.

Rewrite using `[if_pos rfl]`. Conclude with `key _ (Multiset.toList_eq_nil.2 rfl)`. Establish `hlen : s.toList.length ≠ 0`. Rewrite using `[Multiset.length_toList]`. Conclude with `fun h0 => hs (Multiset.card_eq_zero.1 h0)`.

Unfold `mD lD`. Rewrite using `[iteratedFDeriv_const_of_ne hlen, if_neg hs]`. Both sides reduce to the same expression.
-/
theorem mD_const (c : ℂ) (s : Multiset (Fin g → ℂ)) :
    mD (fun _ : Fin g → ℂ => c) 0 s = if s = 0 then c else 0 := by
  by_cases hs : s = 0
  · subst hs
    have key : ∀ l : List (Fin g → ℂ), l = [] →
        iteratedFDeriv ℂ l.length (fun _ : Fin g → ℂ => c) 0 (fun i => l.get i) = c := by
      rintro l rfl
      simp
    rw [if_pos rfl]
    exact key _ (Multiset.toList_eq_nil.2 rfl)
  · have hlen : s.toList.length ≠ 0 := by
      rw [Multiset.length_toList]
      exact fun h0 => hs (Multiset.card_eq_zero.1 h0)
    unfold mD lD
    rw [iteratedFDeriv_const_of_ne hlen, if_neg hs]
    rfl

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[MvPowerSeries.coeff_C]`. Use `show mD (fun _ => c) 0 (dirs n + 0) / fct n = _`. Rewrite using `[add_zero, mD_const]`. Distinguish the cases in `hn : n = 0`.

Substitute `hn` using the available equality. Simplify using `[dirs, fct]`. Establish `hd : dirs n ≠ 0`. Introduce `h0`. Apply `hn` to reduce the goal to its premises.

Establish `h1 : Finsupp.toMultiset n = 0` using `by simpa [dirs] using h0`. Simplify using `using congrArg Multiset.toFinsupp h1`. Rewrite using `[if_neg hd, if_neg hn, zero_div]`.
-/
theorem tay_const (c : ℂ) : tay (g := g) (fun _ => c) 0 = C c := by
  ext n
  rw [MvPowerSeries.coeff_C]
  show mD (fun _ => c) 0 (dirs n + 0) / fct n = _
  rw [add_zero, mD_const]
  by_cases hn : n = 0
  · subst hn
    simp [dirs, fct]
  · have hd : dirs n ≠ 0 := by
      intro h0
      apply hn
      have h1 : Finsupp.toMultiset n = 0 := by simpa [dirs] using h0
      simpa using congrArg Multiset.toFinsupp h1
    rw [if_neg hd, if_neg hn, zero_div]

/- English proof (translation)
Establish `ht : ((t.toList : List (Fin g → ℂ)) : Multiset (Fin g → ℂ)) = t` using `Multiset.coe_toList t`. Establish `hperm : (v ::ₘ t) = ((t.toList ++ [v] : List (Fin g → ℂ)) : Multiset (Fin g → ℂ))` using `by conv_lhs => rw [← ht]`. Rewrite using `[Multiset.cons_coe, Multiset.coe_eq_coe]`. Conclude with `(List.perm_append_singleton v t.toList).symm`. Establish `hlen : (t.toList ++ [v]).length = t.toList.length + 1` using `by simp`.

Rewrite using `[hperm, mD_coe hθ, lD_eq θ 0 (t.toList ++ [v]) hlen, iteratedFDeriv_succ_apply_right]`. Establish `hf : ContDiffAt ℂ ω (fderiv ℂ θ) 0` using `hθ.fderiv_right (by simp)`. Establish `hcomp : (fun y => fderiv ℂ θ y v) = (ContinuousLinearMap.apply ℂ ℂ v) ∘ (fderiv ℂ θ)` using `rfl`. Unfold `mD lD`. Rewrite using `[hcomp, ContinuousLinearMap.iteratedFDeriv_comp_left _ hf le_top]`.

Simplify using `only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply, ContinuousLinearMap.apply_apply]`. Use `congr 1`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `only [Fin.init]`.

Conclude with `List.getElem_append_left i.isLt`. Simplify using the standard rewrite rules.
-/
theorem mD_cons_deriv {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) (v : Fin g → ℂ) (t : Multiset (Fin g → ℂ)) :
    mD θ 0 (v ::ₘ t) = mD (fun y => fderiv ℂ θ y v) 0 t := by
  have ht : ((t.toList : List (Fin g → ℂ)) : Multiset (Fin g → ℂ)) = t := Multiset.coe_toList t
  have hperm : (v ::ₘ t) = ((t.toList ++ [v] : List (Fin g → ℂ)) : Multiset (Fin g → ℂ)) := by
    conv_lhs => rw [← ht]
    rw [Multiset.cons_coe, Multiset.coe_eq_coe]
    exact (List.perm_append_singleton v t.toList).symm
  have hlen : (t.toList ++ [v]).length = t.toList.length + 1 := by simp
  rw [hperm, mD_coe hθ, lD_eq θ 0 (t.toList ++ [v]) hlen, iteratedFDeriv_succ_apply_right]
  have hf : ContDiffAt ℂ ω (fderiv ℂ θ) 0 := hθ.fderiv_right (by simp)
  have hcomp : (fun y => fderiv ℂ θ y v) = (ContinuousLinearMap.apply ℂ ℂ v) ∘ (fderiv ℂ θ) := rfl
  unfold mD lD
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_left _ hf le_top]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousLinearMap.apply_apply]
  congr 1
  · congr 1
    funext i
    simp only [Fin.init]
    exact List.getElem_append_left i.isLt
  · simp

/- English proof (translation)
The claim follows from `(hθ.fderiv_right (by simp)).clm_apply contDiffAt_const`.
-/
theorem deriv_analytic {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) (v : Fin g → ℂ) :
    ContDiffAt ℂ ω (fun y => fderiv ℂ θ y v) 0 :=
  (hθ.fderiv_right (by simp)).clm_apply contDiffAt_const

/- English proof (translation)
Use extensionality with `n`. Use `show mD θ 0 (dirs n + v ::ₘ s) / fct n = mD (fun y => fderiv ℂ θ y v) 0 (dirs n + s) / fct n`. Rewrite using `[Multiset.add_cons, mD_cons_deriv hθ]`.
-/
theorem tay_cons_deriv {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) (v : Fin g → ℂ) (s : Multiset (Fin g → ℂ)) :
    tay θ (v ::ₘ s) = tay (fun y => fderiv ℂ θ y v) s := by
  ext n
  show mD θ 0 (dirs n + v ::ₘ s) / fct n = mD (fun y => fderiv ℂ θ y v) 0 (dirs n + s) / fct n
  rw [Multiset.add_cons, mD_cons_deriv hθ]

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[MvPowerSeries.coeff_pderiv]`. Use `show mD θ 0 (dirs (n + Finsupp.single ((0 : Fin 1), j) 1) + 0) / fct (n + Finsupp.single ((0 : Fin 1), j) 1) * ((n ((0 : Fin 1), j) : ℂ) + 1) = mD (fun y => fderiv ℂ θ y (Pi.single j 1)) 0 (dirs n + 0) / fct n`. Establish `hd : dirs (n + Finsupp.single ((0 : Fin 1), j) 1) = (Pi.single j 1 : Fin g → ℂ) ::ₘ dirs n`. Unfold `dirs`.

Rewrite using `[Finsupp.toMultiset_add, Finsupp.toMultiset_single, one_nsmul, Multiset.map_add, Multiset.map_singleton, add_comm, Multiset.singleton_add]`. Establish `hf : fct (n + Finsupp.single ((0 : Fin 1), j) 1) = fct n * ((n ((0 : Fin 1), j) : ℂ) + 1)`. Unfold `fct`. Rewrite using `[← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ ((0 : Fin 1), j)), ← Finset.mul_prod_erase Finset.univ (fun p => ((n p).factorial : ℂ)) (Finset.mem_univ ((0 : Fin 1), j))]`. Establish `hrest : ∏ x ∈ Finset.univ.erase ((0 : Fin 1), j), (((n + Finsupp.single ((0 : Fin 1), j) 1 : Fin 1 × Fin g →₀ ℕ) x).factorial : ℂ) = ∏ x ∈ Finset.univ.erase ((0 : Fin 1), j), ((n x).factorial : ℂ)`.

Use `Finset.prod_congr rfl fun x hx => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.add_apply, Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hx), add_zero]`. Rewrite using `[hrest, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hne : ((n ((0 : Fin 1), j) : ℂ) + 1) ≠ 0` using `Nat.cast_add_one_ne_zero _`. Rewrite using `[add_zero, add_zero, hd, mD_cons_deriv hθ, hf, ← div_div, div_mul_cancel₀ _ hne]`.
-/
theorem pderiv_tay {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) (j : Fin g) :
    pderiv ℂ ((0 : Fin 1), j) (tay θ 0) = tay (fun y => fderiv ℂ θ y (Pi.single j 1)) 0 := by
  ext n
  rw [MvPowerSeries.coeff_pderiv]
  show mD θ 0 (dirs (n + Finsupp.single ((0 : Fin 1), j) 1) + 0) / fct (n + Finsupp.single ((0 : Fin 1), j) 1) * ((n ((0 : Fin 1), j) : ℂ) + 1) =
    mD (fun y => fderiv ℂ θ y (Pi.single j 1)) 0 (dirs n + 0) / fct n
  have hd : dirs (n + Finsupp.single ((0 : Fin 1), j) 1) = (Pi.single j 1 : Fin g → ℂ) ::ₘ dirs n := by
    unfold dirs
    rw [Finsupp.toMultiset_add, Finsupp.toMultiset_single, one_nsmul, Multiset.map_add,
      Multiset.map_singleton, add_comm, Multiset.singleton_add]
  have hf : fct (n + Finsupp.single ((0 : Fin 1), j) 1) = fct n * ((n ((0 : Fin 1), j) : ℂ) + 1) := by
    unfold fct
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ ((0 : Fin 1), j)),
      ← Finset.mul_prod_erase Finset.univ (fun p => ((n p).factorial : ℂ)) (Finset.mem_univ ((0 : Fin 1), j))]
    have hrest : ∏ x ∈ Finset.univ.erase ((0 : Fin 1), j), (((n + Finsupp.single ((0 : Fin 1), j) 1 : Fin 1 × Fin g →₀ ℕ) x).factorial : ℂ) =
        ∏ x ∈ Finset.univ.erase ((0 : Fin 1), j), ((n x).factorial : ℂ) := by
      refine Finset.prod_congr rfl fun x hx => ?_
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hx), add_zero]
    rw [hrest, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
    push_cast
    ring
  have hne : ((n ((0 : Fin 1), j) : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero _
  rw [add_zero, add_zero, hd, mD_cons_deriv hθ, hf, ← div_div, div_mul_cancel₀ _ hne]

/- English proof (translation)
Use `filter_upwards [hf.eventually (by simp), hh.eventually (by simp)] with y hy1 hy2`. Rewrite using `[fderiv_mul (hy1.differentiableAt (by simp)) (hy2.differentiableAt (by simp))]`. Simplify using `only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, Pi.add_apply, Pi.mul_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem deriv_mul_ev {f h : (Fin g → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) (hh : ContDiffAt ℂ ω h 0) (v : Fin g → ℂ) :
    (fun y => fderiv ℂ (f * h) y v) =ᶠ[𝓝 0]
      (fun y => fderiv ℂ f y v) * h + f * (fun y => fderiv ℂ h y v) := by
  filter_upwards [hf.eventually (by simp), hh.eventually (by simp)] with y hy1 hy2
  rw [fderiv_mul (hy1.differentiableAt (by simp)) (hy2.differentiableAt (by simp))]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    Pi.add_apply, Pi.mul_apply]
  ring

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero`. Introduce `f h _ _ n hn`. Conclude with `absurd hn (Nat.not_lt_zero _)`. Consider the case `succ N ih`.

Introduce `f h hf hh n hn`. Distinguish the cases in `h0 : n = 0`. Substitute `h0` using the available equality. Simplify using `only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul]`. Simplify using `only [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]`.

Use `show mD (f * h) 0 (dirs 0 + 0) / fct 0 = (mD f 0 (dirs 0 + 0) / fct 0) * (mD h 0 (dirs 0 + 0) / fct 0)`. Simplify using `[dirs, fct, mD_zero]`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x, n x ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Conclude with `h0 (Finsupp.ext hc)`. Take `⟨i, j⟩` from `x`. Establish `hi : i = 0` using `Subsingleton.elim _ _`. Substitute `hi` using the available equality. Take `⟨m, hm⟩ : ∃ m, m = n - Finsupp.single ((0 : Fin 1), j) 1` from `⟨_, rfl⟩`.

Establish `hnm : n = m + Finsupp.single ((0 : Fin 1), j) 1`. Rewrite using `[hm]`. Conclude with `(tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hx))).symm`. Establish `hmdeg : m.degree < N`. Establish `h1 : n.degree = m.degree + 1`.

Rewrite using `[hnm, map_add, Finsupp.degree_single]`. Use linear arithmetic over natural numbers and integers. Establish `key : ∀ F : MvPowerSeries (Fin 1 × Fin g) ℂ, coeff m (pderiv ℂ ((0 : Fin 1), j) F) = coeff n F * ((m ((0 : Fin 1), j) : ℂ) + 1)` using `fun F => by`. Rewrite using `[MvPowerSeries.coeff_pderiv, ← hnm]`. Establish `hc : ((m ((0 : Fin 1), j) : ℂ) + 1) ≠ 0` using `Nat.cast_add_one_ne_zero _`.

Apply `mul_right_cancel₀ hc` to reduce the goal to its premises. Rewrite using `[← key, ← key]`. Establish `hfh : ContDiffAt ℂ ω (f * h) 0` using `hf.mul hh`. Establish `hf'` using `deriv_analytic hf (Pi.single j 1)`. Establish `hh'` using `deriv_analytic hh (Pi.single j 1)`.

Rewrite using `[pderiv_tay hfh, tay_local (deriv_mul_ev hf hh (Pi.single j 1)), tay_add (f := (fun y => fderiv ℂ f y (Pi.single j 1)) * h) (h := f * fun y => fderiv ℂ h y (Pi.single j 1)) (hf'.mul hh) (hf.mul hh'), map_add, Derivation.leibniz, pderiv_tay hf, pderiv_tay hh, ih _ _ hf' hh m hmdeg …`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem taylor_mul_coeff_low_degree (N : ℕ) : ∀ (f h : (Fin g → ℂ) → ℂ), ContDiffAt ℂ ω f 0 → ContDiffAt ℂ ω h 0 →
    ∀ n : Fin 1 × Fin g →₀ ℕ, n.degree < N → coeff n (tay (f * h) 0) = coeff n (tay f 0 * tay h 0) := by
  induction N with
  | zero =>
    intro f h _ _ n hn
    exact absurd hn (Nat.not_lt_zero _)
  | succ N ih =>
    intro f h hf hh n hn
    by_cases h0 : n = 0
    · subst h0
      simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul]
      simp only [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
      show mD (f * h) 0 (dirs 0 + 0) / fct 0 = (mD f 0 (dirs 0 + 0) / fct 0) * (mD h 0 (dirs 0 + 0) / fct 0)
      simp [dirs, fct, mD_zero]
    · obtain ⟨x, hx⟩ : ∃ x, n x ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact h0 (Finsupp.ext hc)
      obtain ⟨i, j⟩ := x
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      obtain ⟨m, hm⟩ : ∃ m, m = n - Finsupp.single ((0 : Fin 1), j) 1 := ⟨_, rfl⟩
      have hnm : n = m + Finsupp.single ((0 : Fin 1), j) 1 := by
        rw [hm]
        exact (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hx))).symm
      have hmdeg : m.degree < N := by
        have h1 : n.degree = m.degree + 1 := by
          rw [hnm, map_add, Finsupp.degree_single]
        omega
      have key : ∀ F : MvPowerSeries (Fin 1 × Fin g) ℂ,
          coeff m (pderiv ℂ ((0 : Fin 1), j) F) = coeff n F * ((m ((0 : Fin 1), j) : ℂ) + 1) := fun F => by
        rw [MvPowerSeries.coeff_pderiv, ← hnm]
      have hc : ((m ((0 : Fin 1), j) : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero _
      apply mul_right_cancel₀ hc
      rw [← key, ← key]
      have hfh : ContDiffAt ℂ ω (f * h) 0 := hf.mul hh
      have hf' := deriv_analytic hf (Pi.single j 1)
      have hh' := deriv_analytic hh (Pi.single j 1)
      rw [pderiv_tay hfh, tay_local (deriv_mul_ev hf hh (Pi.single j 1)), tay_add (f := (fun y => fderiv ℂ f y (Pi.single j 1)) * h)
        (h := f * fun y => fderiv ℂ h y (Pi.single j 1)) (hf'.mul hh) (hf.mul hh'),
        map_add, Derivation.leibniz, pderiv_tay hf, pderiv_tay hh, ih _ _ hf' hh m hmdeg,
        ih _ _ hf hh' m hmdeg, smul_eq_mul, smul_eq_mul, map_add, mul_comm (tay h 0)]
      ring

/- English proof (translation)
Use `⟨fun g f h hf hh => ⟨?_, tay_add hf hh 0⟩, fun g c => tay_const c, fun g f h hfh => tay_local hfh 0⟩` and prove the remaining obligations. Use extensionality with `n`. Conclude with `taylor_mul_coeff_low_degree (n.degree + 1) f h hf hh n (Nat.lt_succ_self _)`.
-/
theorem taylor_multiplication : TaylorMulSt := by
  refine ⟨fun g f h hf hh => ⟨?_, tay_add hf hh 0⟩, fun g c => tay_const c,
    fun g f h hfh => tay_local hfh 0⟩
  ext n
  exact taylor_mul_coeff_low_degree (n.degree + 1) f h hf hh n (Nat.lt_succ_self _)

end ReciprocityTheory.ChartRestriction.G.PullbackSections.TM
