import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitHeightSummableExpNegAbs
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousMultilinearMapExtHilbertBasisStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsHilbertSchmidtOrthonormalApplyStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumTupleProdOfSummableNormComplexStatement

open ContinuousLinearMap
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory

open GlobalTheory.OpTrace

/- English proof (translation)
Establish `hs` using `(splitHeight_summable_pi_prod (α := fun i => stdIndex (Hs i)) (f := fun i k => ‖A i (stdBasis (Hs i) k)‖ ^ 2) (fun _ _ => sq_nonneg _) hA).mul_left c.re`. Use `hs.congr fun j => ?_` and prove the remaining obligations. Establish `h1` using `hΨ (fun i => A i (stdBasis (Hs i) (j i))) (fun i => A i (stdBasis (Hs i) (j i)))`. Simplify using `only [inner_self_eq_norm_sq_to_K] at h1`. Establish `h2 : ((‖Ψ (fun i => A i (stdBasis (Hs i) (j i)))‖ ^ 2 : ℝ) : ℂ) = c * ((∏ i, ‖A i (stdBasis (Hs i) (j i))‖ ^ 2 : ℝ) : ℂ)` using `by push_cast; exact h1`.

Establish `h3` using `congrArg Complex.re h2`. Rewrite `h3` using `[Complex.ofReal_re, Complex.re_mul_ofReal]`. Conclude with `h3.symm`.
-/
theorem tensorTrace_summable_sq {ι : Type} [Fintype ι] {Hs : ι → Type} [∀ i, NormedAddCommGroup (Hs i)]
    [∀ i, InnerProductSpace ℂ (Hs i)] [∀ i, CompleteSpace (Hs i)] {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (Ψ : ContinuousMultilinearMap ℂ Hs H) (c : ℂ)
    (hΨ : ∀ y y', ⟪Ψ y', Ψ y⟫_ℂ = c * ∏ i, ⟪y' i, y i⟫_ℂ) (A : ∀ i, Hs i →L[ℂ] Hs i)
    (hA : ∀ i, IsHilbertSchmidt (A i)) :
    Summable fun j : ∀ i, stdIndex (Hs i) => ‖Ψ (fun i => A i (stdBasis (Hs i) (j i)))‖ ^ 2 := by
  have hs := (splitHeight_summable_pi_prod (α := fun i => stdIndex (Hs i))
    (f := fun i k => ‖A i (stdBasis (Hs i) k)‖ ^ 2) (fun _ _ => sq_nonneg _) hA).mul_left c.re
  refine hs.congr fun j => ?_
  have h1 := hΨ (fun i => A i (stdBasis (Hs i) (j i))) (fun i => A i (stdBasis (Hs i) (j i)))
  simp only [inner_self_eq_norm_sq_to_K] at h1
  have h2 : ((‖Ψ (fun i => A i (stdBasis (Hs i) (j i)))‖ ^ 2 : ℝ) : ℂ)
      = c * ((∏ i, ‖A i (stdBasis (Hs i) (j i))‖ ^ 2 : ℝ) : ℂ) := by
    push_cast; exact h1
  have h3 := congrArg Complex.re h2
  rw [Complex.ofReal_re, Complex.re_mul_ofReal] at h3
  exact h3.symm

/- English proof (translation)
Introduce `ι _ _ Hs _ _ _ H _ _ _ Φ Φ' κ κ' hΦ hΦΦ' hΦ' B b hB X hX hX0`. Set `J : ι → Type` to `fun i => stdIndex (Hs i)`. Set `e : ∀ i, HilbertBasis (J i) ℂ (Hs i)` to `fun i => stdBasis (Hs i)`. Set `u : (∀ i, J i) → H` to `fun j => Φ (fun i => e i (j i))`. Establish `hu : Orthonormal ℂ u`.

Rewrite using `[orthonormal_iff_ite]`. Introduce `j' j`. Express the relevant statement in the definitionally equal form `⟪Φ _, Φ _⟫_ℂ = _`. Rewrite using `[hΦ]`. Establish `: ∀ i, ⟪e i (j' i), e i (j i)⟫_ℂ = if j' i = j i then 1 else 0` using `fun i => (orthonormal_iff_ite.1 (e i).orthonormal) _ _`.

Simplify using `only [this]`. Distinguish the cases in `h : ∀ x, j' x = j x`. Rewrite using `[if_pos (funext h)]`. Conclude with `Finset.prod_eq_one fun i _ => if_pos (h i)`. Rewrite `h` using `[if_neg fun h' => h (congrFun h')] push_neg`.

Take `⟨i, hi⟩` from `h`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)`. Establish `hperp : ∀ x : H, (∀ j, ⟪u j, x⟫_ℂ = 0) → ∀ y, ⟪Φ y, x⟫_ℂ = 0`. Introduce `x hx y`. Establish `hL` using `GlobalTheory.T.continuousMultilinearMap_ext_hilbertBasis' ι Hs J e ℂ ((innerSL ℂ x).compContinuousMultilinearMap Φ) 0 fun j => by`.

Simplify using `only [compContinuousMultilinearMap_coe, Function.comp_apply, innerSL_apply_apply, ContinuousMultilinearMap.zero_apply]`. Rewrite using `[← inner_conj_symm]`. Simplify using `[u] at hx`. Simplify using `[hx]`. Use `congrArg (fun L : ContinuousMultilinearMap ℂ Hs ℂ => L y) hL` as an intermediate fact.

Simplify using `only [compContinuousMultilinearMap_coe, Function.comp_apply, innerSL_apply_apply, ContinuousMultilinearMap.zero_apply] at this`. Rewrite using `[← inner_conj_symm, this, map_zero]`. Establish `hinj : Function.Injective u` using `hu.linearIndependent.injective`. Take `⟨w, bH, hsw, hb⟩` from `Orthonormal.exists_hilbertBasis_extension ((orthonormal_subtype_range hinj).2 hu)`. Establish `hoff : ∀ x ∈ w, x ∉ Set.range u → ∀ y, ⟪Φ y, x⟫_ℂ = 0`.

Introduce `x hxw hxu`. Use `hperp x fun j => ?_` and prove the remaining obligations. Establish `hne : (⟨u j, hsw ⟨j, rfl⟩⟩ : w) ≠ ⟨x, hxw⟩` using `fun h => hxu ⟨j, congrArg Subtype.val h⟩`. Use `bH.orthonormal.2 hne` as an intermediate fact. Simplify `this` using `[hb]`.

Use `choose n C D hC hD hBeq using fun i => (hB i).1`. Establish `hG : ∀ (Ψ : ContinuousMultilinearMap ℂ Hs H) (c : ℂ), (∀ y y', ⟪Ψ y', Ψ y⟫_ℂ = c * ∏ i, ⟪y' i, y i⟫_ℂ) → ∀ A : ∀ i, Hs i →L[ℂ] Hs i, (∀ i, IsHilbertSchmidt (A i)) → ∃ G : H →L[ℂ] H, (∀ y, G (Φ y) = Ψ (fun i => A i (y i))) ∧ (∀ v, (∀ y, ⟪Φ y, v⟫_ℂ = 0) → G v = 0) ∧ IsHilbertSchmid …`. Introduce `Ψ c hΨ A hA`. Take `⟨G, hG1, hG2, hG3⟩` from `GlobalTheory.T.exists_isHilbertSchmidt_orthonormal_apply_alt H H (∀ i, J i) u (fun j => Ψ (fun i => A i (e i (j i)))) hu (tensorTrace_summable_sq Ψ c hΨ A hA)`. Use `⟨G, fun y => ?_, fun v hv => hG2 v fun j => hv _, hG3⟩` and prove the remaining obligations.

Use `GlobalTheory.T.continuousMultilinearMap_ext_hilbertBasis' ι Hs J e H (G.compContinuousMultilinearMap Φ) (Ψ.compContinuousLinearMap A) fun j => by simpa using hG1 j` as an intermediate fact. Simplify using `using congrArg (fun L : ContinuousMultilinearMap ℂ Hs H => L y) this`. Establish `hΦ1 : ∀ y y', ⟪Φ y', Φ y⟫_ℂ = 1 * ∏ i, ⟪y' i, y i⟫_ℂ` using `fun y y' => by rw [one_mul, hΦ]`. Use `choose GD hGD1 hGD2 hGD3 using fun k : ∀ i, Fin (n i) => hG Φ 1 hΦ1 (fun i => D i (k i)) fun i => hD i _`. Use `choose GC hGC1 hGC2 hGC3 using fun k : ∀ i, Fin (n i) => hG Φ' κ' hΦ' (fun i => C i (k i)) fun i => hC i _`.

Establish `hXeq : X = ∑ k, GC k ∘L GD k`. Establish `hd : Dense (Submodule.span ℂ w : Set H)`. Use `bH.dense_span` as an intermediate fact. Rewrite `this` using `[hb, Subtype.range_coe]`. Conclude with `Submodule.dense_iff_topologicalClosure_eq_top.2 this`.

Use `ContinuousLinearMap.ext_on hd fun x hx => ?_` and prove the remaining obligations. Distinguish the cases in `hxu : x ∈ Set.range u`. Take `⟨j, rfl⟩` from `hxu`. Express the relevant statement in the definitionally equal form `X (Φ _) = _`. Rewrite using `[hX, ContinuousLinearMap.sum_apply]`.

Simplify using `only [comp_apply]`. Rewrite using `[show (fun i => B i (e i (j i))) = fun i => ∑ m, C i m (D i m (e i (j i))) from`. Use function extensionality and compare the values at `fun i => by rw [hBeq i]; simp]`. Rewrite using `[Φ'.map_sum (fun i m => C i m (D i m (e i (j i))))]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `_ = GC k (GD k (Φ fun i => e i (j i)))`. Rewrite using `[hGD1, hGC1]`. Establish `h0` using `hoff x hx hxu`. Rewrite using `[hX0 x h0, ContinuousLinearMap.sum_apply]`. Simplify using `[hGD2 _ x h0]`.

Establish `hTC : IsTraceClass X`. Rewrite using `[hXeq]`. Conclude with `isTraceClass_sum _ fun k _ => (hGC3 k).isTraceClass_comp (hGD3 k)`. Use `⟨hTC, ?_⟩` and prove the remaining obligations. Establish `htr` using `hTC.hasSum_trace bH`.

Set `g : (∀ i, J i) → w` to `fun j => ⟨u j, hsw ⟨j, rfl⟩⟩`. Establish `hg : Function.Injective g` using `fun j j' h => hinj (congrArg Subtype.val h)`. Establish `hz : ∀ x ∉ Set.range g, ⟪bH x, X (bH x)⟫_ℂ = 0`. Introduce `x hx`. Establish `hxu : x.1 ∉ Set.range u` using `fun ⟨j, hj⟩ => hx ⟨j, Subtype.ext hj⟩`.

Simplify using `[hb, hX0 _ (hoff x.1 x.2 hxu)]`. Rewrite `htr` using `[← hg.hasSum_iff hz]`. Establish `hval : ∀ j, ⟪bH (g j), X (bH (g j))⟫_ℂ = κ * ∏ i, ⟪e i (j i), B i (e i (j i))⟫_ℂ`. Introduce `j`. Simplify using `only [hb, g]`.

Express the relevant statement in the definitionally equal form `⟪Φ _, X (Φ _)⟫_ℂ = _`. Rewrite using `[hX, hΦΦ']`. Establish `hprod` using `(GlobalTheory.T.hasSum_tuple_prod_of_summable_norm_complex ι J (fun i k => ⟪e i k, B i (e i k)⟫_ℂ) fun i => (hB i).1.summable_norm (e i)).mul_left κ`. Establish `hb' : ∀ i, ∑' k, ⟪e i k, B i (e i k)⟫_ℂ = b i` using `fun i => ((hB i).1.hasSum_trace (e i)).tsum_eq.trans (hB i).2`. Simplify using `only [hb'] at hprod`.

Use `htr.unique ?_` and prove the remaining obligations. Simplify `hprod` using `only [Function.comp_def, hval]`.
-/
theorem tensorTrace_hasTrace : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Hs : ι → Type) [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)] [∀ i, CompleteSpace (Hs i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Φ Φ' : ContinuousMultilinearMap ℂ Hs H) (κ κ' : ℂ), (∀ y y', inner ℂ (Φ y') (Φ y) = ∏ i, inner ℂ (y' i) (y i)) → (∀ y y', inner ℂ (Φ y') (Φ' y) = κ * ∏ i, inner ℂ (y' i) (y i)) → (∀ y y', inner ℂ (Φ' y') (Φ' y) = κ' * ∏ i, inner ℂ (y' i) (y i)) → ∀ (B : ∀ i, Hs i →L[ℂ] Hs i) (b : ι → ℂ), (∀ i, HasTrace (B i) (b i)) → ∀ X : H →L[ℂ] H, (∀ y, X (Φ y) = Φ' fun i => B i (y i)) → (∀ v, (∀ y, inner ℂ (Φ y) v = 0) → X v = 0) → HasTrace X (κ * ∏ i, b i) := by
  intro ι _ _ Hs _ _ _ H _ _ _ Φ Φ' κ κ' hΦ hΦΦ' hΦ' B b hB X hX hX0
  classical
  let J : ι → Type := fun i => stdIndex (Hs i)
  let e : ∀ i, HilbertBasis (J i) ℂ (Hs i) := fun i => stdBasis (Hs i)
  let u : (∀ i, J i) → H := fun j => Φ (fun i => e i (j i))

  have hu : Orthonormal ℂ u := by
    rw [orthonormal_iff_ite]
    intro j' j
    change ⟪Φ _, Φ _⟫_ℂ = _
    rw [hΦ]
    have : ∀ i, ⟪e i (j' i), e i (j i)⟫_ℂ = if j' i = j i then 1 else 0 := fun i =>
      (orthonormal_iff_ite.1 (e i).orthonormal) _ _
    simp only [this]
    by_cases h : ∀ x, j' x = j x
    · rw [if_pos (funext h)]
      exact Finset.prod_eq_one fun i _ => if_pos (h i)
    · rw [if_neg fun h' => h (congrFun h')]
      push_neg at h
      obtain ⟨i, hi⟩ := h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

  have hperp : ∀ x : H, (∀ j, ⟪u j, x⟫_ℂ = 0) → ∀ y, ⟪Φ y, x⟫_ℂ = 0 := by
    intro x hx y
    have hL := GlobalTheory.T.continuousMultilinearMap_ext_hilbertBasis' ι Hs J e ℂ
      ((innerSL ℂ x).compContinuousMultilinearMap Φ) 0 fun j => by
        simp only [compContinuousMultilinearMap_coe, Function.comp_apply, innerSL_apply_apply,
          ContinuousMultilinearMap.zero_apply]
        rw [← inner_conj_symm]; simp [u] at hx; simp [hx]
    have := congrArg (fun L : ContinuousMultilinearMap ℂ Hs ℂ => L y) hL
    simp only [compContinuousMultilinearMap_coe, Function.comp_apply, innerSL_apply_apply,
      ContinuousMultilinearMap.zero_apply] at this
    rw [← inner_conj_symm, this, map_zero]

  have hinj : Function.Injective u := hu.linearIndependent.injective
  obtain ⟨w, bH, hsw, hb⟩ :=
    Orthonormal.exists_hilbertBasis_extension ((orthonormal_subtype_range hinj).2 hu)
  have hoff : ∀ x ∈ w, x ∉ Set.range u → ∀ y, ⟪Φ y, x⟫_ℂ = 0 := by
    intro x hxw hxu
    refine hperp x fun j => ?_
    have hne : (⟨u j, hsw ⟨j, rfl⟩⟩ : w) ≠ ⟨x, hxw⟩ := fun h => hxu ⟨j, congrArg Subtype.val h⟩
    have := bH.orthonormal.2 hne
    simpa [hb] using this

  choose n C D hC hD hBeq using fun i => (hB i).1

  have hG : ∀ (Ψ : ContinuousMultilinearMap ℂ Hs H) (c : ℂ),
      (∀ y y', ⟪Ψ y', Ψ y⟫_ℂ = c * ∏ i, ⟪y' i, y i⟫_ℂ) → ∀ A : ∀ i, Hs i →L[ℂ] Hs i,
      (∀ i, IsHilbertSchmidt (A i)) → ∃ G : H →L[ℂ] H, (∀ y, G (Φ y) = Ψ (fun i => A i (y i))) ∧
        (∀ v, (∀ y, ⟪Φ y, v⟫_ℂ = 0) → G v = 0) ∧ IsHilbertSchmidt G := by
    intro Ψ c hΨ A hA
    obtain ⟨G, hG1, hG2, hG3⟩ := GlobalTheory.T.exists_isHilbertSchmidt_orthonormal_apply_alt H H (∀ i, J i) u
      (fun j => Ψ (fun i => A i (e i (j i)))) hu (tensorTrace_summable_sq Ψ c hΨ A hA)
    refine ⟨G, fun y => ?_, fun v hv => hG2 v fun j => hv _, hG3⟩
    have := GlobalTheory.T.continuousMultilinearMap_ext_hilbertBasis' ι Hs J e H (G.compContinuousMultilinearMap Φ)
      (Ψ.compContinuousLinearMap A) fun j => by simpa using hG1 j
    simpa using congrArg (fun L : ContinuousMultilinearMap ℂ Hs H => L y) this
  have hΦ1 : ∀ y y', ⟪Φ y', Φ y⟫_ℂ = 1 * ∏ i, ⟪y' i, y i⟫_ℂ := fun y y' => by rw [one_mul, hΦ]
  choose GD hGD1 hGD2 hGD3 using fun k : ∀ i, Fin (n i) => hG Φ 1 hΦ1 (fun i => D i (k i)) fun i => hD i _
  choose GC hGC1 hGC2 hGC3 using fun k : ∀ i, Fin (n i) => hG Φ' κ' hΦ' (fun i => C i (k i)) fun i => hC i _

  have hXeq : X = ∑ k, GC k ∘L GD k := by
    have hd : Dense (Submodule.span ℂ w : Set H) := by
      have := bH.dense_span
      rw [hb, Subtype.range_coe] at this
      exact Submodule.dense_iff_topologicalClosure_eq_top.2 this
    refine ContinuousLinearMap.ext_on hd fun x hx => ?_
    by_cases hxu : x ∈ Set.range u
    · obtain ⟨j, rfl⟩ := hxu
      change X (Φ _) = _
      rw [hX, ContinuousLinearMap.sum_apply]
      simp only [comp_apply]
      rw [show (fun i => B i (e i (j i))) = fun i => ∑ m, C i m (D i m (e i (j i))) from
        funext fun i => by rw [hBeq i]; simp]
      rw [Φ'.map_sum (fun i m => C i m (D i m (e i (j i))))]
      refine Finset.sum_congr rfl fun k _ => ?_
      change _ = GC k (GD k (Φ fun i => e i (j i)))
      rw [hGD1, hGC1]
    · have h0 := hoff x hx hxu
      rw [hX0 x h0, ContinuousLinearMap.sum_apply]
      simp [hGD2 _ x h0]
  have hTC : IsTraceClass X := by
    rw [hXeq]; exact isTraceClass_sum _ fun k _ => (hGC3 k).isTraceClass_comp (hGD3 k)
  refine ⟨hTC, ?_⟩

  have htr := hTC.hasSum_trace bH
  let g : (∀ i, J i) → w := fun j => ⟨u j, hsw ⟨j, rfl⟩⟩
  have hg : Function.Injective g := fun j j' h => hinj (congrArg Subtype.val h)
  have hz : ∀ x ∉ Set.range g, ⟪bH x, X (bH x)⟫_ℂ = 0 := by
    intro x hx
    have hxu : x.1 ∉ Set.range u := fun ⟨j, hj⟩ => hx ⟨j, Subtype.ext hj⟩
    simp [hb, hX0 _ (hoff x.1 x.2 hxu)]
  rw [← hg.hasSum_iff hz] at htr
  have hval : ∀ j, ⟪bH (g j), X (bH (g j))⟫_ℂ = κ * ∏ i, ⟪e i (j i), B i (e i (j i))⟫_ℂ := by
    intro j
    simp only [hb, g]
    change ⟪Φ _, X (Φ _)⟫_ℂ = _
    rw [hX, hΦΦ']
  have hprod := (GlobalTheory.T.hasSum_tuple_prod_of_summable_norm_complex ι J (fun i k => ⟪e i k, B i (e i k)⟫_ℂ)
    fun i => (hB i).1.summable_norm (e i)).mul_left κ
  have hb' : ∀ i, ∑' k, ⟪e i k, B i (e i k)⟫_ℂ = b i := fun i =>
    ((hB i).1.hasSum_trace (e i)).tsum_eq.trans (hB i).2
  simp only [hb'] at hprod
  refine htr.unique ?_
  simpa only [Function.comp_def, hval] using hprod

end GlobalTheory
