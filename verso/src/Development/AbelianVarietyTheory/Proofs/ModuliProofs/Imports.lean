import Mathlib

namespace GlobalTheory.AnalyticLineDerivative

open MvPolynomial

universe u_1 u_2 u_3 u_4

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a`. Simplify using `only [eval₂Hom_C, pderiv_C, map_zero, mul_zero, Finset.sum_const_zero]`. Conclude with `hasDerivAt_const _ _`. Consider the case `add p q hp hq`.

Simplify using `only [map_add, mul_add, Finset.sum_add_distrib]`. Conclude with `hp.add hq`. Consider the case `mul_X p i hp`. Establish `hlin : HasDerivAt (fun t : ℂ => u i + t * v i) (v i) 0`. Simplify using `using ((hasDerivAt_id (0 : ℂ)).mul_const (v i)).const_add (u i)`.

Establish `hX : ∀ j, eval₂Hom φ u (pderiv j (X i : MvPolynomial J S)) = if j = i then 1 else 0`. Introduce `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using `[pderiv_X]`.

Simplify using `[pderiv_X, h, Ne.symm h]`. Establish `key : ∀ j, v j * eval₂Hom φ u (pderiv j (p * X i)) = (if j = i then v i * eval₂Hom φ u p else 0) + v j * eval₂Hom φ u (pderiv j p) * u i`. Introduce `j`. Rewrite using `[Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, eval₂Hom_X', hX]`. Use `split_ifs with h`.

Substitute `h` using the available equality. Expand and normalize the polynomial expressions, which then agree. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [map_mul, eval₂Hom_X', Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Use `(hp.mul hlin).congr_deriv ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_congr rfl fun j _ => key j, Finset.sum_add_distrib, ← Finset.sum_mul]`. Simplify using `only [Finset.sum_ite_eq', Finset.mem_univ, if_true, zero_smul, add_zero, zero_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasDerivAt_line {S : Type*} {J : Type*} [CommRing S] [Fintype J] (φ : S →+* ℂ)
    (u v : J → ℂ) (p : MvPolynomial J S) :
    HasDerivAt (fun t : ℂ => eval₂Hom φ (u + t • v) p)
      (∑ j, v j * eval₂Hom φ u (pderiv j p)) 0 := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [eval₂Hom_C, pderiv_C, map_zero, mul_zero, Finset.sum_const_zero]
    exact hasDerivAt_const _ _
  | add p q hp hq =>
    simp only [map_add, mul_add, Finset.sum_add_distrib]
    exact hp.add hq
  | mul_X p i hp =>
    have hlin : HasDerivAt (fun t : ℂ => u i + t * v i) (v i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (v i)).const_add (u i)
    have hX : ∀ j, eval₂Hom φ u (pderiv j (X i : MvPolynomial J S)) = if j = i then 1 else 0 := by
      intro j
      by_cases h : j = i
      · subst h; simp [pderiv_X]
      · simp [pderiv_X, h, Ne.symm h]

    have key : ∀ j, v j * eval₂Hom φ u (pderiv j (p * X i)) =
        (if j = i then v i * eval₂Hom φ u p else 0) + v j * eval₂Hom φ u (pderiv j p) * u i := by
      intro j
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, eval₂Hom_X', hX]
      split_ifs with h
      · subst h; ring
      · ring
    simp only [map_mul, eval₂Hom_X', Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (hp.mul hlin).congr_deriv ?_
    rw [Finset.sum_congr rfl fun j _ => key j, Finset.sum_add_distrib, ← Finset.sum_mul]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, zero_smul,
      add_zero, zero_mul]
    ring

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a`. Simplify using `only [eval₂Hom_C]`. Conclude with `(h a).comp_of_eq analyticAt_fst rfl`. Consider the case `add p q hp hq`.

Simplify using `only [map_add]`. Conclude with `hp.add hq`. Consider the case `mul_X p i hp`. Simplify using `only [map_mul, eval₂Hom_X']`. Conclude with `hp.mul (((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℂ E (J → ℂ))).analyticAt _)`.
-/
theorem analyticAt_eval {E : Type*} {S : Type*} {J : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CommRing S] [Fintype J] (χ : E → S →+* ℂ) (z₀ : E) (u₀ : J → ℂ)
    (h : ∀ a : S, AnalyticAt ℂ (fun z : E => χ z a) z₀) (p : MvPolynomial J S) :
    AnalyticAt ℂ (fun w : E × (J → ℂ) => eval₂Hom (χ w.1) w.2 p) (z₀, u₀) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [eval₂Hom_C]
    exact (h a).comp_of_eq analyticAt_fst rfl
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, eval₂Hom_X']
    exact hp.mul (((ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.snd ℂ E (J → ℂ))).analyticAt _)

/- English proof (translation)
Establish `: CompleteSpace E` using `FiniteDimensional.complete ℂ E`. Use `set G : E × (J → ℂ) → (σ → ℂ) := fun w r => eval₂Hom (χ w.1) w.2 (rel r)`. Use `set F : E × (J → ℂ) → E × (σ → ℂ) := fun w => (w.1, G w)`. Use `set a₀ : E × (J → ℂ) := (z₀, u₀)`. Establish `hGan : AnalyticAt ℂ G a₀` using `AnalyticAt.pi fun r => analyticAt_eval χ z₀ u₀ han (rel r)`.

Establish `hFan : AnalyticAt ℂ F a₀` using `analyticAt_fst.prod hGan`. Establish `hGd : HasFDerivAt G (fderiv ℂ G a₀) a₀` using `hGan.differentiableAt.hasFDerivAt`. Establish `hdirG : ∀ v : J → ℂ, fderiv ℂ G a₀ (0, v) = fun r => ∑ j, v j * eval₂Hom (χ z₀) u₀ (pderiv j (rel r))`. Introduce `v`. Establish `hℓ : HasDerivAt (fun t : ℂ => ((z₀, u₀ + t • v) : E × (J → ℂ))) ((0 : E), (1 : ℂ) • v) 0` using `(hasDerivAt_const (0 : ℂ) z₀).prodMk (((hasDerivAt_id (0 : ℂ)).smul_const v).const_add u₀)`.

Establish `hcomp` using `hGd.comp_hasDerivAt_of_eq 0 hℓ (by simp [a₀])`. Rewrite `hcomp` using `[one_smul]`. Use function extensionality and compare the values at `r`. Conclude with `((hasDerivAt_pi.mp hcomp) r).unique (hasDerivAt_line (χ z₀) u₀ v (rel r))`. Use `set L : E × (J → ℂ) →L[ℂ] E × (σ → ℂ) := (ContinuousLinearMap.fst ℂ E (J → ℂ)).prod (fderiv ℂ G a₀)`.

Establish `hFd : HasFDerivAt F L a₀` using `hasFDerivAt_fst.prodMk hGd`. Establish `hLinj : Function.Injective L`. Use `(injective_iff_map_eq_zero L).mpr ?_` and prove the remaining obligations. Introduce and unpack `⟨h, v⟩ hw`. Establish `hh : h = 0` using `by simpa [L] using congrArg Prod.fst hw`.

Substitute `hh` using the available equality. Establish `hv : fderiv ℂ G a₀ (0, v) = 0` using `by simpa [L] using congrArg Prod.snd hw`. Rewrite `hv` using `[hdirG]`. Establish `hzero : Matrix.vecMul (fun s => v (c s)) (Matrix.of fun s r : σ => eval₂Hom (χ z₀) u₀ (pderiv (c s) (rel r))) = 0`. Use function extensionality and compare the values at `r`.

Establish `hr` using `congrFun hv r`. Simplify using `only [Pi.zero_apply] at hr ⊢`. Rewrite using `[← hr]`. Simplify using `only [Matrix.vecMul, dotProduct, Matrix.of_apply]`. Conclude with `(Equiv.ofBijective c hc).sum_comp (fun j => v j * eval₂Hom (χ z₀) u₀ (pderiv j (rel r)))`.

Establish `hvc : (fun s => v (c s)) = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hdet (Matrix.exists_vecMul_eq_zero_iff.mp ⟨_, hne, hzero⟩)`. Establish `hv0 : v = 0`. Use function extensionality and compare the values at `j`.

Take `⟨s, rfl⟩` from `hc.2 j`. Conclude with `congrFun hvc s`. Substitute `hv0` using the available equality. Both sides reduce to the same expression. Establish `hrank : Module.finrank ℂ (E × (J → ℂ)) = Module.finrank ℂ (E × (σ → ℂ))`.

Simplify using `[Module.finrank_prod, Fintype.card_of_bijective hc]`. Establish `hLsurj : Function.Surjective L` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank (f := (L : E × (J → ℂ) →ₗ[ℂ] E × (σ → ℂ)))).mp hLinj`. Set `i : (E × (J → ℂ)) ≃L[ℂ] (E × (σ → ℂ))` to `(LinearEquiv.ofBijective (L : E × (J → ℂ) →ₗ[ℂ] E × (σ → ℂ)) ⟨hLinj, hLsurj⟩).toContinuousLinearEquiv`. Establish `hi : (i : E × (J → ℂ) →L[ℂ] E × (σ → ℂ)) = L` using `ContinuousLinearMap.ext fun _ => rfl`. Establish `hstrict : HasStrictFDerivAt F (i : E × (J → ℂ) →L[ℂ] E × (σ → ℂ)) a₀`.

Rewrite using `[hi, ← hFd.fderiv]`. Conclude with `hFan.hasStrictFDerivAt`. Establish `hev : ∀ᶠ w in nhds a₀, AnalyticAt ℂ F w ∧ ∃ j : (E × (J → ℂ)) ≃L[ℂ] (E × (σ → ℂ)), fderiv ℂ F w = j`. Use `hFan.eventually_analyticAt.and ?_` and prove the remaining obligations. Establish `hmem : fderiv ℂ F a₀ ∈ Set.range ((↑) : ((E × (J → ℂ)) ≃L[ℂ] (E × (σ → ℂ))) → E × (J → ℂ) →L[ℂ] E × (σ → ℂ))` using `⟨i, by rw [hi, hFd.fderiv]⟩`.

Use `(hFan.fderiv.continuousAt.eventually_mem (ContinuousLinearEquiv.isOpen.mem_nhds hmem)).mono fun w hw => ?_` and prove the remaining obligations. Take `⟨j, hj⟩` from `hw`. Conclude with `⟨j, hj.symm⟩`. Take `⟨U, hUsub, hUopen, ha₀U⟩` from `mem_nhds_iff.mp hev`. Use `⟨(hstrict.toOpenPartialHomeomorph F).restrOpen U hUopen, fun w => rfl, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[OpenPartialHomeomorph.restrOpen_source]`. Conclude with `⟨hstrict.mem_toOpenPartialHomeomorph_source, ha₀U⟩`. Introduce `b hb`. Establish `hsrc` using `((hstrict.toOpenPartialHomeomorph F).restrOpen U hUopen).map_target hb`. Rewrite `hsrc` using `[OpenPartialHomeomorph.restrOpen_source]`.

Take `⟨hA, j, hj⟩` from `hUsub hsrc.2`. Conclude with `((hstrict.toOpenPartialHomeomorph F).restrOpen U hUopen).analyticAt_symm hb hA hj`.
-/
theorem main {E : Type u_1} {S : Type u_2} {J : Type u_3} {σ : Type u_4}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [CommRing S] [Fintype J]
    [Fintype σ] [DecidableEq σ] (χ : E → S →+* ℂ) (rel : σ → MvPolynomial J S) (c : σ → J)
    (hc : Function.Bijective c) (z₀ : E) (u₀ : J → ℂ)
    (han : ∀ a : S, AnalyticAt ℂ (fun z : E => χ z a) z₀)
    (hdet : Matrix.det (Matrix.of fun s r : σ =>
      eval₂Hom (χ z₀) u₀ (pderiv (c s) (rel r))) ≠ 0) :
    ∃ Φ : OpenPartialHomeomorph (E × (J → ℂ)) (E × (σ → ℂ)),
      (∀ w : E × (J → ℂ), Φ w = (w.1, fun r : σ => eval₂Hom (χ w.1) w.2 (rel r))) ∧
        (z₀, u₀) ∈ Φ.source ∧ AnalyticOnNhd ℂ Φ.symm Φ.target := by
  classical
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  set G : E × (J → ℂ) → (σ → ℂ) := fun w r => eval₂Hom (χ w.1) w.2 (rel r)
  set F : E × (J → ℂ) → E × (σ → ℂ) := fun w => (w.1, G w)
  set a₀ : E × (J → ℂ) := (z₀, u₀)
  have hGan : AnalyticAt ℂ G a₀ := AnalyticAt.pi fun r => analyticAt_eval χ z₀ u₀ han (rel r)
  have hFan : AnalyticAt ℂ F a₀ := analyticAt_fst.prod hGan
  have hGd : HasFDerivAt G (fderiv ℂ G a₀) a₀ := hGan.differentiableAt.hasFDerivAt

  have hdirG : ∀ v : J → ℂ, fderiv ℂ G a₀ (0, v) =
      fun r => ∑ j, v j * eval₂Hom (χ z₀) u₀ (pderiv j (rel r)) := by
    intro v
    have hℓ : HasDerivAt (fun t : ℂ => ((z₀, u₀ + t • v) : E × (J → ℂ))) ((0 : E), (1 : ℂ) • v) 0 :=
      (hasDerivAt_const (0 : ℂ) z₀).prodMk (((hasDerivAt_id (0 : ℂ)).smul_const v).const_add u₀)
    have hcomp := hGd.comp_hasDerivAt_of_eq 0 hℓ (by simp [a₀])
    rw [one_smul] at hcomp
    funext r
    exact ((hasDerivAt_pi.mp hcomp) r).unique (hasDerivAt_line (χ z₀) u₀ v (rel r))
  set L : E × (J → ℂ) →L[ℂ] E × (σ → ℂ) :=
    (ContinuousLinearMap.fst ℂ E (J → ℂ)).prod (fderiv ℂ G a₀)
  have hFd : HasFDerivAt F L a₀ := hasFDerivAt_fst.prodMk hGd

  have hLinj : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).mpr ?_
    rintro ⟨h, v⟩ hw
    have hh : h = 0 := by simpa [L] using congrArg Prod.fst hw
    subst hh
    have hv : fderiv ℂ G a₀ (0, v) = 0 := by simpa [L] using congrArg Prod.snd hw
    rw [hdirG] at hv
    have hzero : Matrix.vecMul (fun s => v (c s))
        (Matrix.of fun s r : σ => eval₂Hom (χ z₀) u₀ (pderiv (c s) (rel r))) = 0 := by
      funext r
      have hr := congrFun hv r
      simp only [Pi.zero_apply] at hr ⊢
      rw [← hr]
      simp only [Matrix.vecMul, dotProduct, Matrix.of_apply]
      exact (Equiv.ofBijective c hc).sum_comp
        (fun j => v j * eval₂Hom (χ z₀) u₀ (pderiv j (rel r)))
    have hvc : (fun s => v (c s)) = 0 := by
      by_contra hne
      exact hdet (Matrix.exists_vecMul_eq_zero_iff.mp ⟨_, hne, hzero⟩)
    have hv0 : v = 0 := by
      funext j
      obtain ⟨s, rfl⟩ := hc.2 j
      exact congrFun hvc s
    subst hv0
    rfl
  have hrank : Module.finrank ℂ (E × (J → ℂ)) = Module.finrank ℂ (E × (σ → ℂ)) := by
    simp [Module.finrank_prod, Fintype.card_of_bijective hc]
  have hLsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank
      (f := (L : E × (J → ℂ) →ₗ[ℂ] E × (σ → ℂ)))).mp hLinj
  let i : (E × (J → ℂ)) ≃L[ℂ] (E × (σ → ℂ)) :=
    (LinearEquiv.ofBijective (L : E × (J → ℂ) →ₗ[ℂ] E × (σ → ℂ))
      ⟨hLinj, hLsurj⟩).toContinuousLinearEquiv
  have hi : (i : E × (J → ℂ) →L[ℂ] E × (σ → ℂ)) = L := ContinuousLinearMap.ext fun _ => rfl
  have hstrict : HasStrictFDerivAt F (i : E × (J → ℂ) →L[ℂ] E × (σ → ℂ)) a₀ := by
    rw [hi, ← hFd.fderiv]
    exact hFan.hasStrictFDerivAt

  have hev : ∀ᶠ w in nhds a₀, AnalyticAt ℂ F w ∧
      ∃ j : (E × (J → ℂ)) ≃L[ℂ] (E × (σ → ℂ)), fderiv ℂ F w = j := by
    refine hFan.eventually_analyticAt.and ?_
    have hmem : fderiv ℂ F a₀ ∈
        Set.range ((↑) : ((E × (J → ℂ)) ≃L[ℂ] (E × (σ → ℂ))) → E × (J → ℂ) →L[ℂ] E × (σ → ℂ)) :=
      ⟨i, by rw [hi, hFd.fderiv]⟩
    refine (hFan.fderiv.continuousAt.eventually_mem
      (ContinuousLinearEquiv.isOpen.mem_nhds hmem)).mono fun w hw => ?_
    obtain ⟨j, hj⟩ := hw
    exact ⟨j, hj.symm⟩
  obtain ⟨U, hUsub, hUopen, ha₀U⟩ := mem_nhds_iff.mp hev
  refine ⟨(hstrict.toOpenPartialHomeomorph F).restrOpen U hUopen, fun w => rfl, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hstrict.mem_toOpenPartialHomeomorph_source, ha₀U⟩
  · intro b hb
    have hsrc := ((hstrict.toOpenPartialHomeomorph F).restrOpen U hUopen).map_target hb
    rw [OpenPartialHomeomorph.restrOpen_source] at hsrc
    obtain ⟨hA, j, hj⟩ := hUsub hsrc.2
    exact ((hstrict.toOpenPartialHomeomorph F).restrOpen U hUopen).analyticAt_symm hb hA hj

end GlobalTheory.AnalyticLineDerivative
