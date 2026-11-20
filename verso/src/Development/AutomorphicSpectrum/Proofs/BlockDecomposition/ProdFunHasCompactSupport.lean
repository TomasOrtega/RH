import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.LiftUnit
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SiegelConj

noncomputable section

open NumberField NumberField.mixedEmbedding IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical ContDiff

set_option synthInstance.maxSize 1000

namespace GlobalTheory.CompanionTheory.EisTF

open PositivityTheory.RgEis PositivityTheory.RgEis.TF GroundTheory.Global GroundTheory.Automorphic GroundTheory.Global.IdeleGroup

variable {k : Type} [Field k] [NumberField k]

def prodFun {κ : Type} (F : {w : InfinitePlace k // w.IsReal} → (κ → ℝ) → ℝ) (G : (κ → ℂ) → ℝ)
    (x : κ → mixedSpace k) : ℝ :=
  (∏ w, F w (fun j => (x j).1 w)) * ∏ w : {w : InfinitePlace k // w.IsComplex}, G (fun j => (x j).2 w)

/- English proof (translation)
Unfold `prodFun`. Use `ContDiff.mul (contDiff_prod fun w _ => ContDiff.comp (hF w) (f := fun x : κ → mixedSpace k => fun j => (x j).1 w) ?_) (contDiff_prod fun w _ => ContDiff.comp hG (f := fun x : κ → mixedSpace k => fun j => (x j).2 w) ?_)` and prove the remaining obligations. Use `fun_prop`. Use `fun_prop`.
-/
theorem prodFun_contDiff {κ : Type} [Fintype κ] {F : {w : InfinitePlace k // w.IsReal} → (κ → ℝ) → ℝ}
    {G : (κ → ℂ) → ℝ} (hF : ∀ w, ContDiff ℝ (⊤ : ℕ∞) (F w)) (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    ContDiff ℝ (⊤ : ℕ∞) (prodFun F G) := by
  unfold prodFun
  refine ContDiff.mul (contDiff_prod fun w _ => ContDiff.comp (hF w) (f := fun x : κ → mixedSpace k => fun j => (x j).1 w) ?_)
    (contDiff_prod fun w _ => ContDiff.comp hG (f := fun x : κ → mixedSpace k => fun j => (x j).2 w) ?_)
  · fun_prop
  · fun_prop

/- English proof (translation)
Set `Φ : ({w : InfinitePlace k // w.IsReal} → κ → ℝ) × ({w : InfinitePlace k // w.IsComplex} → κ → ℂ) → (κ → mixedSpace k)` to `fun p j => (fun w => p.1 w j, fun w => p.2 w j)`. Establish `hΦ : Continuous Φ` using `by fun_prop`. Use `HasCompactSupport.intro (((isCompact_univ_pi fun w => (hF w).isCompact).prod (isCompact_univ_pi fun _ : {w : InfinitePlace k // w.IsComplex} => hG.isCompact)).image hΦ) ?_` and prove the remaining obligations. Introduce `x hx`. Assume the negation of the conclusion as `h`.

Apply `hx` to reduce the goal to its premises. Use `⟨(fun w j => (x j).1 w, fun w j => (x j).2 w), ?_, rfl⟩` and prove the remaining obligations. Unfold `prodFun at h`. Establish `h1` using `left_ne_zero_of_mul h`. Establish `h2` using `right_ne_zero_of_mul h`.

Rewrite `h1`, `h2` using `[Finset.prod_ne_zero_iff]`. Conclude with `⟨fun w _ => subset_tsupport _ (h1 w (Finset.mem_univ _)), fun w _ => subset_tsupport _ (h2 w (Finset.mem_univ _))⟩`.
-/
theorem prodFun_hasCompactSupport {κ : Type} [Fintype κ]
    {F : {w : InfinitePlace k // w.IsReal} → (κ → ℝ) → ℝ}
    {G : (κ → ℂ) → ℝ} (hF : ∀ w, HasCompactSupport (F w)) (hG : HasCompactSupport G) :
    HasCompactSupport (prodFun F G) := by
  classical
  let Φ : ({w : InfinitePlace k // w.IsReal} → κ → ℝ) × ({w : InfinitePlace k // w.IsComplex} → κ → ℂ) →
      (κ → mixedSpace k) := fun p j => (fun w => p.1 w j, fun w => p.2 w j)
  have hΦ : Continuous Φ := by fun_prop
  refine HasCompactSupport.intro (((isCompact_univ_pi fun w => (hF w).isCompact).prod
    (isCompact_univ_pi fun _ : {w : InfinitePlace k // w.IsComplex} => hG.isCompact)).image hΦ) ?_
  intro x hx
  by_contra h
  apply hx
  refine ⟨(fun w j => (x j).1 w, fun w j => (x j).2 w), ?_, rfl⟩
  unfold prodFun at h
  have h1 := left_ne_zero_of_mul h
  have h2 := right_ne_zero_of_mul h
  rw [Finset.prod_ne_zero_iff] at h1 h2
  exact ⟨fun w _ => subset_tsupport _ (h1 w (Finset.mem_univ _)),
    fun w _ => subset_tsupport _ (h2 w (Finset.mem_univ _))⟩

/- English proof (translation)
Use `⟨((prodFun_hasCompactSupport hFc hGc).comp_left Complex.ofReal_zero).toSchwartzMap (Complex.ofRealCLM.contDiff.comp (prodFun_contDiff hF hG)), fun x => ?_⟩` and prove the remaining obligations. Conclude with `HasCompactSupport.toSchwartzMap_toFun _ _ x`.
-/
theorem exists_schwartz {κ : Type} [Fintype κ] {F : {w : InfinitePlace k // w.IsReal} → (κ → ℝ) → ℝ}
    {G : (κ → ℂ) → ℝ} (hF : ∀ w, ContDiff ℝ (⊤ : ℕ∞) (F w)) (hFc : ∀ w, HasCompactSupport (F w))
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G) :
    ∃ φ : 𝓢(κ → mixedSpace k, ℂ), ∀ x, φ x = (prodFun F G x : ℂ) := by
  refine ⟨((prodFun_hasCompactSupport hFc hGc).comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (prodFun_contDiff hF hG)), fun x => ?_⟩
  exact HasCompactSupport.toSchwartzMap_toFun _ _ x

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem homeomorphMixedSpace_apply_eq_ringEquiv (x : InfiniteAdeleRing k) :
    homeomorphMixedSpace k x = InfiniteAdeleRing.ringEquiv_mixedSpace k x := by
  rfl

/- English proof (translation)
Simplify using `only [homeomorphMixedSpace_apply_eq_ringEquiv, map_mul]`.
-/
theorem hms_mul (x y : InfiniteAdeleRing k) :
    homeomorphMixedSpace k (x * y) = homeomorphMixedSpace k x * homeomorphMixedSpace k y := by
  simp only [homeomorphMixedSpace_apply_eq_ringEquiv, map_mul]

/- English proof (translation)
Rewrite using `[homeomorphMixedSpace_apply_eq_ringEquiv, map_one]`.
-/
theorem hms_one : homeomorphMixedSpace k (1 : InfiniteAdeleRing k) = 1 := by
  rw [homeomorphMixedSpace_apply_eq_ringEquiv, map_one]

/- English proof (translation)
Rewrite using `[homeomorphMixedSpace_apply_eq_ringEquiv, map_zero]`.
-/
theorem hms_zero : homeomorphMixedSpace k (0 : InfiniteAdeleRing k) = 0 := by
  rw [homeomorphMixedSpace_apply_eq_ringEquiv, map_zero]

/- English proof (translation)
Simplify using `only [homeomorphMixedSpace_apply_eq_ringEquiv, map_sub]`.
-/
theorem hms_sub (x y : InfiniteAdeleRing k) :
    homeomorphMixedSpace k (x - y) = homeomorphMixedSpace k x - homeomorphMixedSpace k y := by
  simp only [homeomorphMixedSpace_apply_eq_ringEquiv, map_sub]

/- English proof (translation)
Rewrite using `[homeomorphMixedSpace_apply_eq_ringEquiv, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]`. Conclude with `(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal w.2).norm_map_of_map_zero (map_zero _) _`.
-/
theorem norm_fst (x : InfiniteAdeleRing k) (w : {w : InfinitePlace k // w.IsReal}) :
    ‖(homeomorphMixedSpace k x).1 w‖ = ‖x w.1‖ := by
  rw [homeomorphMixedSpace_apply_eq_ringEquiv, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal w.2).norm_map_of_map_zero (map_zero _) _

/- English proof (translation)
Rewrite using `[homeomorphMixedSpace_apply_eq_ringEquiv, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]`. Conclude with `(InfinitePlace.Completion.isometry_extensionEmbedding w.1).norm_map_of_map_zero (map_zero _) _`.
-/
theorem norm_snd (x : InfiniteAdeleRing k) (w : {w : InfinitePlace k // w.IsComplex}) :
    ‖(homeomorphMixedSpace k x).2 w‖ = ‖x w.1‖ := by
  rw [homeomorphMixedSpace_apply_eq_ringEquiv, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  exact (InfinitePlace.Completion.isometry_extensionEmbedding w.1).norm_map_of_map_zero (map_zero _) _

variable {ι' : Type}

/- English proof (translation)
Rewrite using `[← norm_fst (v j) w, Real.norm_eq_abs, sq_abs]`.
-/
theorem sq_fst (v : ι' → InfiniteAdeleRing k) (w : {w : InfinitePlace k // w.IsReal})
    (j : ι') : ((homeomorphMixedSpace k (v j)).1 w) ^ 2 = ‖v j w.1‖ ^ 2 := by
  rw [← norm_fst (v j) w, Real.norm_eq_abs, sq_abs]

/- English proof (translation)
Simplify using `only [sq_fst]`. Conclude with `hv w.1`.
-/
theorem unit_fst [Fintype ι'] {v : ι' → InfiniteAdeleRing k} (hv : UnitVec v)
    (w : {w : InfinitePlace k // w.IsReal}) :
    ∑ j, ((homeomorphMixedSpace k (v j)).1 w) ^ 2 = 1 := by
  simp only [sq_fst]
  exact hv w.1

/- English proof (translation)
Simplify using `only [norm_snd]`. Conclude with `hv w.1`.
-/
theorem unit_snd [Fintype ι'] {v : ι' → InfiniteAdeleRing k} (hv : UnitVec v)
    (w : {w : InfinitePlace k // w.IsComplex}) :
    ∑ j, ‖(homeomorphMixedSpace k (v j)).2 w‖ ^ 2 = 1 := by
  simp only [norm_snd]
  exact hv w.1

/- English proof (translation)
Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = i₀`. Substitute `hj` using the available equality. Simplify using `[hms_one]`. Simplify using `[Pi.single_eq_of_ne hj, hms_zero]`.
-/
theorem single_fst [DecidableEq ι'] (i₀ : ι') (w : {w : InfinitePlace k // w.IsReal}) :
    (fun j => (homeomorphMixedSpace k ((Pi.single i₀ 1 : ι' → InfiniteAdeleRing k) j)).1 w) =
      Pi.single i₀ 1 := by
  funext j
  by_cases hj : j = i₀
  · subst hj
    simp [hms_one]
  · simp [Pi.single_eq_of_ne hj, hms_zero]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = i₀`. Substitute `hj` using the available equality. Simplify using `[hms_one]`. Simplify using `[Pi.single_eq_of_ne hj, hms_zero]`.
-/
theorem single_snd [DecidableEq ι'] (i₀ : ι') (w : {w : InfinitePlace k // w.IsComplex}) :
    (fun j => (homeomorphMixedSpace k ((Pi.single i₀ 1 : ι' → InfiniteAdeleRing k) j)).2 w) =
      Pi.single i₀ 1 := by
  funext j
  by_cases hj : j = i₀
  · subst hj
    simp [hms_one]
  · simp [Pi.single_eq_of_ne hj, hms_zero]

/- English proof (translation)
Establish `h1` using `norm_fst (x - 1) w`. Rewrite `h1` using `[hms_sub, hms_one]`. Establish `h2 : ‖(homeomorphMixedSpace k x).1 w - 1‖ < 1`. Establish `h3 : (homeomorphMixedSpace k x - 1).1 w = (homeomorphMixedSpace k x).1 w - 1` using `rfl`. Rewrite using `[← h3, h1]`.

Conclude with `h`. Rewrite `h2` using `[Real.norm_eq_abs, abs_sub_lt_iff]`. Combine the linear relations using `[h2.2]`.
-/
theorem fst_pos {x : InfiniteAdeleRing k} (w : {w : InfinitePlace k // w.IsReal})
    (h : ‖x w.1 - 1‖ < 1) : 0 < (homeomorphMixedSpace k x).1 w := by
  have h1 := norm_fst (x - 1) w
  rw [hms_sub, hms_one] at h1
  have h2 : ‖(homeomorphMixedSpace k x).1 w - 1‖ < 1 := by
    have h3 : (homeomorphMixedSpace k x - 1).1 w = (homeomorphMixedSpace k x).1 w - 1 := rfl
    rw [← h3, h1]
    exact h
  rw [Real.norm_eq_abs, abs_sub_lt_iff] at h2
  linarith [h2.2]

/- English proof (translation)
Use `split_ifs with hx`. Simplify using `using hpos x hx.le`. Establish `h` using `hpar (-x)`. Rewrite `h` using `[neg_neg]`. Establish `hm : ((-1 : ℝ) ^ m) * (-1) ^ m = 1`.

Rewrite using `[← mul_pow]`. Evaluate the numerical expressions. Establish `h2 : f x * (-1) ^ m = f (-x)`. Rewrite using `[h, mul_comm ((-1 : ℝ) ^ m) (f (-x)), mul_assoc, hm, mul_one]`. Rewrite using `[h2]`.

Conclude with `hpos _ (by linarith [not_lt.mp hx])`.
-/
theorem parity_nonneg {f : ℝ → ℝ} {m : ℕ} (hpos : ∀ t, 0 ≤ t → 0 ≤ f t)
    (hpar : ∀ t, f (-t) = (-1) ^ m * f t) (x : ℝ) :
    0 ≤ f x * (if 0 < x then (1 : ℝ) else (-1) ^ m) := by
  split_ifs with hx
  · simpa using hpos x hx.le
  · have h := hpar (-x)
    rw [neg_neg] at h
    have hm : ((-1 : ℝ) ^ m) * (-1) ^ m = 1 := by
      rw [← mul_pow]
      norm_num
    have h2 : f x * (-1) ^ m = f (-x) := by
      rw [h, mul_comm ((-1 : ℝ) ^ m) (f (-x)), mul_assoc, hm, mul_one]
    rw [h2]
    exact hpos _ (by linarith [not_lt.mp hx])

/- English proof (translation)
Establish `hx' : |x| = 1` using `by rwa [Real.norm_eq_abs] at hx`. Break down `(abs_eq zero_le_one).mp hx' with rfl | rfl` into its components or cases. Rewrite using `[if_pos one_pos, h1]`. Rewrite using `[if_neg (by norm_num), hpar 1, h1, mul_one]`.
-/
theorem parity_one {f : ℝ → ℝ} {m : ℕ} (h1 : f 1 = 1)
    (hpar : ∀ t, f (-t) = (-1) ^ m * f t) {x : ℝ} (hx : ‖x‖ = 1) :
    f x = if 0 < x then (1 : ℝ) else (-1) ^ m := by
  have hx' : |x| = 1 := by rwa [Real.norm_eq_abs] at hx
  rcases (abs_eq zero_le_one).mp hx' with rfl | rfl
  · rw [if_pos one_pos, h1]
  · rw [if_neg (by norm_num), hpar 1, h1, mul_one]

/- English proof (translation)
Take `⟨R, hR⟩` from `hfc.isCompact.isBounded.subset_closedBall (0 : E)`. Set `β : ContDiffBump (0 : κ → E)` to `⟨max R 1, max R 1 + 1, lt_max_of_lt_right one_pos, by linarith⟩`. Use `⟨fun y => f (y i₀) * β y, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(hf.comp (f := fun y : κ → E => y i₀) (by fun_prop)).mul β.contDiff`. Conclude with `HasCompactSupport.mul_left (f := fun y : κ → E => f (y i₀)) β.hasCompactSupport`.

Introduce `s`. Distinguish the cases in `hs : f s = 0`. Simplify using `[hs]`. Establish `hs' : s ∈ Metric.closedBall (0 : E) R` using `hR (subset_tsupport f hs)`. Establish `hb : β (fun _ => s) = 1`.

Apply `β.one_of_mem_closedBall` to reduce the goal to its premises. Rewrite `hs'`, the goal using `[Metric.mem_closedBall, dist_zero_right]`. Conclude with `(pi_norm_const_le s).trans (hs'.trans (le_max_left _ _))`. Simplify using `[hb]`.
-/
private theorem exists_diag_lemma_2 {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {κ : Type} [Fintype κ] (i₀ : κ) {f : E → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) :
    ∃ F : (κ → E) → ℝ, ContDiff ℝ (⊤ : ℕ∞) F ∧ HasCompactSupport F ∧
      ∀ s : E, F (fun _ => s) = f s := by
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall (0 : E)
  let β : ContDiffBump (0 : κ → E) :=
    ⟨max R 1, max R 1 + 1, lt_max_of_lt_right one_pos, by linarith⟩
  refine ⟨fun y => f (y i₀) * β y, ?_, ?_, ?_⟩
  · exact (hf.comp (f := fun y : κ → E => y i₀) (by fun_prop)).mul β.contDiff
  · exact HasCompactSupport.mul_left (f := fun y : κ → E => f (y i₀)) β.hasCompactSupport
  · intro s
    by_cases hs : f s = 0
    · simp [hs]
    · have hs' : s ∈ Metric.closedBall (0 : E) R := hR (subset_tsupport f hs)
      have hb : β (fun _ => s) = 1 := by
        apply β.one_of_mem_closedBall
        rw [Metric.mem_closedBall, dist_zero_right] at hs' ⊢
        exact (pi_norm_const_le s).trans (hs'.trans (le_max_left _ _))
      simp [hb]

/- English proof (translation)
Introduce `hR hC hS k _ _ ι _ _ i₀ χ hχ δ hδ`. Take `⟨m, hm⟩` from `hS k χ hχ`. Use `choose F f hFc hFcs hfc hfcs hF1 hf1 hfpos hfpar hFv using fun w : {w : InfinitePlace k // w.IsReal} => hR ι i₀ (m w) δ hδ`. Take `⟨G, g, hGc, hGcs, hgc, hgcs, hG1, hg1, hgpos, hGpos, hGv⟩` from `hC ι i₀ δ hδ`. Use `choose F' hF'c hF'cs hF'd using fun w => exists_diag_lemma_2 (κ := Unit) () (hfc w) (hfcs w)`.

Take `⟨G', hG'c, hG'cs, hG'd⟩` from `exists_diag_lemma_2 (κ := Unit) () hgc hgcs`. Take `⟨φ, hφ⟩` from `exists_schwartz hFc hFcs hGc hGcs`. Take `⟨φ₁, hφ₁⟩` from `exists_schwartz hF'c hF'cs hG'c hG'cs`. Establish `hdiag : ∀ t : InfiniteAdeleRing k, rd φ₁ (fun _ : Unit => t) = (((∏ w, f w ((homeomorphMixedSpace k t).1 w)) * ∏ w : {w : InfinitePlace k // w.IsComplex}, g ((homeomorphMixedSpace k t).2 w) : ℝ) : ℂ)`. Introduce `t`.

Simplify using `only [rd, hφ₁, prodFun, hF'd, hG'd]`. Establish `hrd : ∀ v : ι → InfiniteAdeleRing k, rd φ v = ((prodFun F G (fun j => homeomorphMixedSpace k (v j)) : ℝ) : ℂ)` using `fun v => hφ _`. Establish `hite : ∀ a : InfiniteAdeleRing k, (∏ w, if 0 < (homeomorphMixedSpace k a).1 w then (1 : ℂ) else (-1) ^ m w) = (((∏ w, if 0 < (homeomorphMixedSpace k a).1 w then (1 : ℝ) else (-1) ^ m w) : ℝ) : ℂ)`. Introduce `a`. Rewrite using `[Complex.ofReal_prod]`.

Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`. Use `⟨φ, φ₁, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hrd]`. Simplify using `only [prodFun, single_fst, single_snd, hF1, hG1, Finset.prod_const_one, mul_one, Complex.ofReal_one]`.

Introduce `a ha`. Establish `hg' : ∀ w : {w : InfinitePlace k // w.IsComplex}, g ((homeomorphMixedSpace k (a : InfiniteAdeleRing k)).2 w) = 1` using `fun w => hg1 _ ((norm_snd _ w).trans (ha w.1))`. Establish `hf' : ∀ w, f w ((homeomorphMixedSpace k (a : InfiniteAdeleRing k)).1 w) = if 0 < (homeomorphMixedSpace k (a : InfiniteAdeleRing k)).1 w then 1 else (-1) ^ m w` using `fun w => parity_one (hf1 w) (hfpar w) ((norm_fst _ w).trans (ha w.1))`. Rewrite using `[hdiag, hm a, hite]`. Simplify using `only [hg', hf', Finset.prod_const_one, mul_one]`.

Introduce `a`. Use `⟨(∏ w, f w ((homeomorphMixedSpace k (a : InfiniteAdeleRing k)).1 w) * (if 0 < (homeomorphMixedSpace k (a : InfiniteAdeleRing k)).1 w then (1 : ℝ) else (-1) ^ m w)) * ∏ w : {w : InfinitePlace k // w.IsComplex}, g ((homeomorphMixedSpace k (a : InfiniteAdeleRing k)).2 w), ?_, ?_⟩` and prove the remaining obligations. Conclude with `mul_nonneg (Finset.prod_nonneg fun w _ => parity_nonneg (hfpos w) (hfpar w) _) (Finset.prod_nonneg fun w _ => hgpos _)`. Rewrite using `[hdiag, hm a, hite, ← Complex.ofReal_mul, Finset.prod_mul_distrib]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Introduce `v hv`. Use `⟨fun t => ?_, fun hne w => ?_, fun hpos => ?_⟩` and prove the remaining obligations. Establish `h1 : ∀ w : {w : InfinitePlace k // w.IsReal}, (fun j => (homeomorphMixedSpace k ((t • v) j)).1 w) = (homeomorphMixedSpace k t).1 w • fun j => (homeomorphMixedSpace k (v j)).1 w`. Introduce `w`.

Use function extensionality and compare the values at `j`. Simplify using `[Pi.smul_apply, smul_eq_mul, hms_mul]`. Establish `h2 : ∀ w : {w : InfinitePlace k // w.IsComplex}, (fun j => (homeomorphMixedSpace k ((t • v) j)).2 w) = (homeomorphMixedSpace k t).2 w • fun j => (homeomorphMixedSpace k (v j)).2 w`. Introduce `w`. Use function extensionality and compare the values at `j`.

Simplify using `[Pi.smul_apply, smul_eq_mul, hms_mul]`. Establish `hF' : ∀ w (s : ℝ), F w (s • fun j => (homeomorphMixedSpace k (v j)).1 w) = f w s * F w (fun j => (homeomorphMixedSpace k (v j)).1 w)` using `fun w s => (hFv w _ (unit_fst hv w)).1 s`. Establish `hG' : ∀ w (z : ℂ), G (z • fun j => (homeomorphMixedSpace k (v j)).2 w) = g z * G (fun j => (homeomorphMixedSpace k (v j)).2 w)` using `fun w z => (hGv _ (unit_snd hv w)).1 z`. Rewrite using `[hrd, hrd, hdiag, ← Complex.ofReal_mul]`. Use `congr 1`.

Simplify using `only [prodFun, h1, h2, hF', hG', Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hne` using `[hrd]`. Establish `hne' : prodFun F G (fun j => homeomorphMixedSpace k (v j)) ≠ 0` using `by exact_mod_cast hne`. Unfold `prodFun at hne'`.

Establish `hA` using `left_ne_zero_of_mul hne'`. Establish `hB` using `right_ne_zero_of_mul hne'`. Rewrite `hA`, `hB` using `[Finset.prod_ne_zero_iff]`. Distinguish the cases in `hw : w.IsReal`. Establish `h` using `(hFv ⟨w, hw⟩ _ (unit_fst hv ⟨w, hw⟩)).2.1 (hA ⟨w, hw⟩ (Finset.mem_univ _))`.

Simplify using `only [sq_fst] at h`. Conclude with `h`. Establish `hw' : w.IsComplex` using `InfinitePlace.not_isReal_iff_isComplex.mp hw`. Establish `h` using `(hGv _ (unit_snd hv ⟨w, hw'⟩)).2 (hB ⟨w, hw'⟩ (Finset.mem_univ _))`. Simplify using `only [norm_snd] at h`.

Conclude with `h`. Use `⟨prodFun F G (fun j => homeomorphMixedSpace k (v j)), ?_, hrd v⟩` and prove the remaining obligations. Unfold `prodFun`. Use `mul_nonneg (Finset.prod_nonneg fun w _ => ?_) (Finset.prod_nonneg fun w _ => hGpos _)` and prove the remaining obligations. Conclude with `(hFv w _ (unit_fst hv w)).2.2 (fst_pos w (hpos w.1))`.
-/
theorem archFun_of_bumps : RealBump → CplxBump → SignChar → ArchFun := by
  intro hR hC hS k _ _ ι _ _ i₀ χ hχ δ hδ
  obtain ⟨m, hm⟩ := hS k χ hχ
  choose F f hFc hFcs hfc hfcs hF1 hf1 hfpos hfpar hFv using
    fun w : {w : InfinitePlace k // w.IsReal} => hR ι i₀ (m w) δ hδ
  obtain ⟨G, g, hGc, hGcs, hgc, hgcs, hG1, hg1, hgpos, hGpos, hGv⟩ := hC ι i₀ δ hδ
  choose F' hF'c hF'cs hF'd using fun w => exists_diag_lemma_2 (κ := Unit) () (hfc w) (hfcs w)
  obtain ⟨G', hG'c, hG'cs, hG'd⟩ := exists_diag_lemma_2 (κ := Unit) () hgc hgcs
  obtain ⟨φ, hφ⟩ := exists_schwartz hFc hFcs hGc hGcs
  obtain ⟨φ₁, hφ₁⟩ := exists_schwartz hF'c hF'cs hG'c hG'cs
  have hdiag : ∀ t : InfiniteAdeleRing k, rd φ₁ (fun _ : Unit => t) =
      (((∏ w, f w ((homeomorphMixedSpace k t).1 w)) *
        ∏ w : {w : InfinitePlace k // w.IsComplex}, g ((homeomorphMixedSpace k t).2 w) : ℝ) : ℂ) := by
    intro t
    simp only [rd, hφ₁, prodFun, hF'd, hG'd]
  have hrd : ∀ v : ι → InfiniteAdeleRing k,
      rd φ v = ((prodFun F G (fun j => homeomorphMixedSpace k (v j)) : ℝ) : ℂ) := fun v => hφ _
  have hite : ∀ a : InfiniteAdeleRing k,
      (∏ w, if 0 < (homeomorphMixedSpace k a).1 w then (1 : ℂ) else (-1) ^ m w) =
        (((∏ w, if 0 < (homeomorphMixedSpace k a).1 w then (1 : ℝ) else (-1) ^ m w) : ℝ) : ℂ) := by
    intro a
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    split_ifs <;> simp
  refine ⟨φ, φ₁, ?_, ?_, ?_, ?_⟩
  · rw [hrd]
    simp only [prodFun, single_fst, single_snd, hF1, hG1, Finset.prod_const_one, mul_one,
      Complex.ofReal_one]
  · intro a ha
    have hg' : ∀ w : {w : InfinitePlace k // w.IsComplex},
        g ((homeomorphMixedSpace k (a : InfiniteAdeleRing k)).2 w) = 1 :=
      fun w => hg1 _ ((norm_snd _ w).trans (ha w.1))
    have hf' : ∀ w, f w ((homeomorphMixedSpace k (a : InfiniteAdeleRing k)).1 w) =
        if 0 < (homeomorphMixedSpace k (a : InfiniteAdeleRing k)).1 w then 1 else (-1) ^ m w :=
      fun w => parity_one (hf1 w) (hfpar w) ((norm_fst _ w).trans (ha w.1))
    rw [hdiag, hm a, hite]
    simp only [hg', hf', Finset.prod_const_one, mul_one]
  · intro a
    refine ⟨(∏ w, f w ((homeomorphMixedSpace k (a : InfiniteAdeleRing k)).1 w) *
        (if 0 < (homeomorphMixedSpace k (a : InfiniteAdeleRing k)).1 w then (1 : ℝ) else (-1) ^ m w)) *
        ∏ w : {w : InfinitePlace k // w.IsComplex}, g ((homeomorphMixedSpace k (a : InfiniteAdeleRing k)).2 w),
      ?_, ?_⟩
    · exact mul_nonneg (Finset.prod_nonneg fun w _ => parity_nonneg (hfpos w) (hfpar w) _)
        (Finset.prod_nonneg fun w _ => hgpos _)
    · rw [hdiag, hm a, hite, ← Complex.ofReal_mul, Finset.prod_mul_distrib]
      congr 1
      ring
  · intro v hv
    refine ⟨fun t => ?_, fun hne w => ?_, fun hpos => ?_⟩
    · have h1 : ∀ w : {w : InfinitePlace k // w.IsReal},
          (fun j => (homeomorphMixedSpace k ((t • v) j)).1 w) =
            (homeomorphMixedSpace k t).1 w • fun j => (homeomorphMixedSpace k (v j)).1 w := by
        intro w
        funext j
        simp [Pi.smul_apply, smul_eq_mul, hms_mul]
      have h2 : ∀ w : {w : InfinitePlace k // w.IsComplex},
          (fun j => (homeomorphMixedSpace k ((t • v) j)).2 w) =
            (homeomorphMixedSpace k t).2 w • fun j => (homeomorphMixedSpace k (v j)).2 w := by
        intro w
        funext j
        simp [Pi.smul_apply, smul_eq_mul, hms_mul]
      have hF' : ∀ w (s : ℝ), F w (s • fun j => (homeomorphMixedSpace k (v j)).1 w) =
          f w s * F w (fun j => (homeomorphMixedSpace k (v j)).1 w) :=
        fun w s => (hFv w _ (unit_fst hv w)).1 s
      have hG' : ∀ w (z : ℂ), G (z • fun j => (homeomorphMixedSpace k (v j)).2 w) =
          g z * G (fun j => (homeomorphMixedSpace k (v j)).2 w) :=
        fun w z => (hGv _ (unit_snd hv w)).1 z
      rw [hrd, hrd, hdiag, ← Complex.ofReal_mul]
      congr 1
      simp only [prodFun, h1, h2, hF', hG', Finset.prod_mul_distrib]
      ring
    · rw [hrd] at hne
      have hne' : prodFun F G (fun j => homeomorphMixedSpace k (v j)) ≠ 0 := by exact_mod_cast hne
      unfold prodFun at hne'
      have hA := left_ne_zero_of_mul hne'
      have hB := right_ne_zero_of_mul hne'
      rw [Finset.prod_ne_zero_iff] at hA hB
      by_cases hw : w.IsReal
      · have h := (hFv ⟨w, hw⟩ _ (unit_fst hv ⟨w, hw⟩)).2.1 (hA ⟨w, hw⟩ (Finset.mem_univ _))
        simp only [sq_fst] at h
        exact h
      · have hw' : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
        have h := (hGv _ (unit_snd hv ⟨w, hw'⟩)).2 (hB ⟨w, hw'⟩ (Finset.mem_univ _))
        simp only [norm_snd] at h
        exact h
    · refine ⟨prodFun F G (fun j => homeomorphMixedSpace k (v j)), ?_, hrd v⟩
      unfold prodFun
      refine mul_nonneg (Finset.prod_nonneg fun w _ => ?_) (Finset.prod_nonneg fun w _ => hGpos _)
      exact (hFv w _ (unit_fst hv w)).2.2 (fst_pos w (hpos w.1))

end GlobalTheory.CompanionTheory.EisTF
