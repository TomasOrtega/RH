import Development.WeilBound.CoreStatements.VolumeEquality.RootBranches

noncomputable section

namespace SheetDecomposition

open Filter Topology Polynomial

/- English proof (translation)
Simplify using `[monicOf, eval_finsetSum]`.
-/
theorem eval_monicOf {d : ℕ} (a : Fin d → ℂ) (x : ℂ) : (monicOf a).eval x = x ^ d + ∑ i, a i * x ^ (i : ℕ) := by
  simp [monicOf, eval_finsetSum]

/- English proof (translation)
The claim follows from `degree_sum_fin_lt a`.
-/
theorem degree_low_lt {d : ℕ} (a : Fin d → ℂ) : (∑ i, C (a i) * X ^ (i : ℕ) : ℂ[X]).degree < d :=
  degree_sum_fin_lt a

/- English proof (translation)
The claim follows from `monic_X_pow_add (degree_low_lt a)`.
-/
theorem monic_monicOf {d : ℕ} (a : Fin d → ℂ) : (monicOf a).Monic :=
  monic_X_pow_add (degree_low_lt a)

/- English proof (translation)
Apply `natDegree_eq_of_degree_eq_some` to reduce the goal to its premises. Unfold `monicOf`. Rewrite using `[degree_add_eq_left_of_degree_lt, degree_X_pow]`. Rewrite using `[degree_X_pow]`. Conclude with `degree_low_lt a`.
-/
theorem natDegree_monicOf {d : ℕ} (a : Fin d → ℂ) : (monicOf a).natDegree = d := by
  apply natDegree_eq_of_degree_eq_some
  unfold monicOf
  rw [degree_add_eq_left_of_degree_lt, degree_X_pow]
  rw [degree_X_pow]
  exact degree_low_lt a

/- English proof (translation)
Use `set f : (Fin d → ℂ) × ℂ → ℂ := fun u => u.2 ^ d + ∑ i, u.1 i * u.2 ^ (i : ℕ) with hf`. Establish `cdf : ContDiffAt ℂ 1 f (a₀, x₀)`. Rewrite using `[hf]`. Use `fun_prop`. Establish `hD : fderiv ℂ f (a₀, x₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ = ContinuousLinearMap.toSpanSingleton ℂ ((derivative (monicOf a₀)).eval x₀)`.

Establish `e1 : HasFDerivAt (f ∘ fun x : ℂ => (a₀, x)) (fderiv ℂ f (a₀, x₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ) x₀` using `HasFDerivAt.comp x₀ (cdf.differentiableAt one_ne_zero).hasFDerivAt (hasFDerivAt_prodMk_right a₀ x₀)`. Establish `e2 : (f ∘ fun x : ℂ => (a₀, x)) = fun x => (monicOf a₀).eval x`. Use function extensionality and compare the values at `x`. Simplify using `[hf, eval_monicOf]`. Rewrite `e1` using `[e2]`.

Conclude with `e1.unique ((monicOf a₀).hasDerivAt x₀).hasFDerivAt`. Establish `if₂ : (fderiv ℂ f (a₀, x₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ).IsInvertible`. Rewrite using `[hD]`. Use `⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ h1), ?_⟩` and prove the remaining obligations. Use `ext`.

Simplify using the standard rewrite rules. Use `⟨cdf.implicitFunction one_ne_zero if₂, cdf.implicitFunction_apply_self one_ne_zero if₂, ?_⟩` and prove the remaining obligations. Establish `hc` using `cdf.contDiffAt_implicitFunction one_ne_zero if₂`. Establish `hv` using `cdf.eventually_apply_implicitFunction one_ne_zero if₂`. Use `filter_upwards [hc.eventually (by simp), hv] with a ha hb`.

Use `⟨ha.differentiableAt one_ne_zero, ?_⟩` and prove the remaining obligations. Establish `: f (a₀, x₀) = 0`. Use `h0` as an intermediate fact. Rewrite `this` using `[IsRoot.def, eval_monicOf]`. Conclude with `this`.

Rewrite `hb` using `[this]`. Rewrite using `[IsRoot.def, eval_monicOf]`. Conclude with `hb`.
-/
theorem root_branch {d : ℕ} (a₀ : Fin d → ℂ) (x₀ : ℂ) (h0 : (monicOf a₀).IsRoot x₀)
    (h1 : (derivative (monicOf a₀)).eval x₀ ≠ 0) :
    ∃ ψ : (Fin d → ℂ) → ℂ, ψ a₀ = x₀ ∧ ∀ᶠ a in 𝓝 a₀, DifferentiableAt ℂ ψ a ∧ (monicOf a).IsRoot (ψ a) := by
  set f : (Fin d → ℂ) × ℂ → ℂ := fun u => u.2 ^ d + ∑ i, u.1 i * u.2 ^ (i : ℕ) with hf
  have cdf : ContDiffAt ℂ 1 f (a₀, x₀) := by
    rw [hf]
    fun_prop
  have hD : fderiv ℂ f (a₀, x₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ =
      ContinuousLinearMap.toSpanSingleton ℂ ((derivative (monicOf a₀)).eval x₀) := by
    have e1 : HasFDerivAt (f ∘ fun x : ℂ => (a₀, x))
        (fderiv ℂ f (a₀, x₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ) x₀ :=
      HasFDerivAt.comp x₀ (cdf.differentiableAt one_ne_zero).hasFDerivAt (hasFDerivAt_prodMk_right a₀ x₀)
    have e2 : (f ∘ fun x : ℂ => (a₀, x)) = fun x => (monicOf a₀).eval x := by
      funext x
      simp [hf, eval_monicOf]
    rw [e2] at e1
    exact e1.unique ((monicOf a₀).hasDerivAt x₀).hasFDerivAt
  have if₂ : (fderiv ℂ f (a₀, x₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ).IsInvertible := by
    rw [hD]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ h1), ?_⟩
    ext
    simp
  refine ⟨cdf.implicitFunction one_ne_zero if₂, cdf.implicitFunction_apply_self one_ne_zero if₂, ?_⟩
  have hc := cdf.contDiffAt_implicitFunction one_ne_zero if₂
  have hv := cdf.eventually_apply_implicitFunction one_ne_zero if₂
  filter_upwards [hc.eventually (by simp), hv] with a ha hb
  refine ⟨ha.differentiableAt one_ne_zero, ?_⟩
  have : f (a₀, x₀) = 0 := by
    have := h0
    rw [IsRoot.def, eval_monicOf] at this
    exact this
  rw [this] at hb
  rw [IsRoot.def, eval_monicOf]
  exact hb

/- English proof (translation)
Use `⟨fun hx => ?_, fun ⟨i, hi⟩ => hi ▸ h i⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Establish `hsub : insert x (Finset.univ.image r) ⊆ (monicOf a).roots.toFinset`. Introduce `z hz`.

Rewrite using `[Multiset.mem_toFinset, mem_roots (monic_monicOf a).ne_zero]`. Break down `Finset.mem_insert.mp hz with rfl | hz` into its components or cases. Conclude with `hx`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.mp hz`. Conclude with `h i`.

Establish `h1` using `Finset.card_le_card hsub`. Rewrite using `[Finset.card_insert_of_notMem (by`. Introduce `hz`. Take `⟨i, -, hi⟩` from `Finset.mem_image.mp hz`. Conclude with `hne i hi.symm), Finset.card_image_of_injective _ hr, Finset.card_univ, Fintype.card_fin] at h1`.

Establish `h2` using `(Multiset.toFinset_card_le (monicOf a).roots).trans (card_roots' (monicOf a))`. Rewrite `h2` using `[natDegree_monicOf]`. Use linear arithmetic over natural numbers and integers.
-/
theorem root_iff_of_injective {d : ℕ} (a : Fin d → ℂ) (r : Fin d → ℂ) (hr : Function.Injective r)
    (h : ∀ i, (monicOf a).IsRoot (r i)) (x : ℂ) : (monicOf a).IsRoot x ↔ ∃ i, x = r i := by
  classical
  refine ⟨fun hx => ?_, fun ⟨i, hi⟩ => hi ▸ h i⟩
  by_contra hne
  push Not at hne
  have hsub : insert x (Finset.univ.image r) ⊆ (monicOf a).roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, mem_roots (monic_monicOf a).ne_zero]
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hx
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
      exact h i
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by
    intro hz
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hz
    exact hne i hi.symm), Finset.card_image_of_injective _ hr, Finset.card_univ, Fintype.card_fin] at h1
  have h2 := (Multiset.toFinset_card_le (monicOf a).roots).trans (card_roots' (monicOf a))
  rw [natDegree_monicOf] at h2
  omega

/- English proof (translation)
Establish `hc : (monicOf a).roots.toFinset.card = d`. Rewrite using `[Multiset.toFinset_card_of_nodup (nodup_roots hs), IsAlgClosed.card_roots_eq_natDegree, natDegree_monicOf]`. Set `e` to `Finset.equivFinOfCardEq hc`. Use `⟨fun i => (e.symm i : ℂ), Subtype.val_injective.comp e.symm.injective, fun i => ?_⟩` and prove the remaining obligations. Use `(e.symm i).2` as an intermediate fact.

Rewrite `this` using `[Multiset.mem_toFinset, mem_roots (monic_monicOf a).ne_zero]`. Conclude with `this`.
-/
theorem exists_roots {d : ℕ} (a : Fin d → ℂ) (hs : (monicOf a).Separable) :
    ∃ r : Fin d → ℂ, Function.Injective r ∧ ∀ i, (monicOf a).IsRoot (r i) := by
  classical
  have hc : (monicOf a).roots.toFinset.card = d := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hs), IsAlgClosed.card_roots_eq_natDegree, natDegree_monicOf]
  let e := Finset.equivFinOfCardEq hc
  refine ⟨fun i => (e.symm i : ℂ), Subtype.val_injective.comp e.symm.injective, fun i => ?_⟩
  have := (e.symm i).2
  rw [Multiset.mem_toFinset, mem_roots (monic_monicOf a).ne_zero] at this
  exact this

/- English proof (translation)
Introduce `n d T a hT ha hs t₀ ht₀`. Take `⟨r, hr, hroot⟩` from `exists_roots (a t₀) (hs t₀ ht₀)`. Establish `hder : ∀ i, (derivative (monicOf (a t₀))).eval (r i) ≠ 0` using `fun i => by`. Use `(hs t₀ ht₀).aeval_derivative_ne_zero (x := r i) (by simpa using hroot i)` as an intermediate fact. Simplify using `using this`.

Use `choose ψ hψ0 hψ using fun i => root_branch (a t₀) (r i) (hroot i) (hder i)`. Establish `hca : ContinuousAt a t₀` using `(ha.differentiableAt (hT.mem_nhds ht₀)).continuousAt`. Establish `hcθ : ∀ i, ContinuousAt (fun t => ψ i (a t)) t₀` using `fun i => ContinuousAt.comp (f := a) (hψ i).self_of_nhds.1.continuousAt hca`. Establish `hev : ∀ᶠ t in 𝓝 t₀, t ∈ T ∧ (∀ i, DifferentiableAt ℂ (ψ i) (a t) ∧ (monicOf (a t)).IsRoot (ψ i (a t))) ∧ ∀ i j, i ≠ j → ψ i (a t) ≠ ψ j (a t)`. Use `(hT.eventually_mem ht₀).and (Eventually.and (eventually_all.mpr fun i => hca.tendsto.eventually (hψ i)) ?_)` and prove the remaining obligations.

Use `eventually_all.mpr fun i => eventually_all.mpr fun j => ?_` and prove the remaining obligations. Distinguish the cases in `hij : i = j`. Conclude with `Eventually.of_forall fun _ h => (h hij).elim`. Establish `: ∀ᶠ t in 𝓝 t₀, ψ i (a t) - ψ j (a t) ≠ 0` using `((hcθ i).sub (hcθ j)).eventually_ne (by show ψ i (a t₀) - ψ j (a t₀) ≠ 0`. Rewrite using `[hψ0, hψ0]`.

Conclude with `sub_ne_zero.mpr (hr.ne hij))`. Use `filter_upwards [this] with t ht _ using sub_ne_zero.mp ht`. Take `⟨V, hV, hVo, hVt⟩` from `eventually_nhds_iff.mp hev`. Use `⟨V, fun i t => ψ i (a t), hVo, hVt, fun t ht => (hV t ht).1, fun i t ht => ?_, fun t ht => ?_⟩` and prove the remaining obligations. Conclude with `(((hV t ht).2.1 i).1.comp t (ha.differentiableAt (hT.mem_nhds (hV t ht).1))).differentiableWithinAt`.

Establish `hi : Function.Injective fun i => ψ i (a t)` using `fun i j h => by`. Assume the negation of the conclusion as `hij`. Conclude with `(hV t ht).2.2 i j hij h`. Conclude with `⟨hi, root_iff_of_injective (a t) _ hi fun i => ((hV t ht).2.1 i).2⟩`.
-/
theorem rootBranches : RootBranches := by
  intro n d T a hT ha hs t₀ ht₀
  obtain ⟨r, hr, hroot⟩ := exists_roots (a t₀) (hs t₀ ht₀)
  have hder : ∀ i, (derivative (monicOf (a t₀))).eval (r i) ≠ 0 := fun i => by
    have := (hs t₀ ht₀).aeval_derivative_ne_zero (x := r i) (by simpa using hroot i)
    simpa using this
  choose ψ hψ0 hψ using fun i => root_branch (a t₀) (r i) (hroot i) (hder i)
  have hca : ContinuousAt a t₀ := (ha.differentiableAt (hT.mem_nhds ht₀)).continuousAt
  have hcθ : ∀ i, ContinuousAt (fun t => ψ i (a t)) t₀ := fun i =>
    ContinuousAt.comp (f := a) (hψ i).self_of_nhds.1.continuousAt hca
  have hev : ∀ᶠ t in 𝓝 t₀, t ∈ T ∧ (∀ i, DifferentiableAt ℂ (ψ i) (a t) ∧ (monicOf (a t)).IsRoot (ψ i (a t))) ∧
      ∀ i j, i ≠ j → ψ i (a t) ≠ ψ j (a t) := by
    refine (hT.eventually_mem ht₀).and (Eventually.and (eventually_all.mpr fun i => hca.tendsto.eventually (hψ i)) ?_)
    refine eventually_all.mpr fun i => eventually_all.mpr fun j => ?_
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ h => (h hij).elim
    · have : ∀ᶠ t in 𝓝 t₀, ψ i (a t) - ψ j (a t) ≠ 0 :=
        ((hcθ i).sub (hcθ j)).eventually_ne (by
          show ψ i (a t₀) - ψ j (a t₀) ≠ 0
          rw [hψ0, hψ0]
          exact sub_ne_zero.mpr (hr.ne hij))
      filter_upwards [this] with t ht _ using sub_ne_zero.mp ht
  obtain ⟨V, hV, hVo, hVt⟩ := eventually_nhds_iff.mp hev
  refine ⟨V, fun i t => ψ i (a t), hVo, hVt, fun t ht => (hV t ht).1, fun i t ht => ?_, fun t ht => ?_⟩
  · exact (((hV t ht).2.1 i).1.comp t (ha.differentiableAt (hT.mem_nhds (hV t ht).1))).differentiableWithinAt
  · have hi : Function.Injective fun i => ψ i (a t) := fun i j h => by
      by_contra hij
      exact (hV t ht).2.2 i j hij h
    exact ⟨hi, root_iff_of_injective (a t) _ hi fun i => ((hV t ht).2.1 i).2⟩

end SheetDecomposition
