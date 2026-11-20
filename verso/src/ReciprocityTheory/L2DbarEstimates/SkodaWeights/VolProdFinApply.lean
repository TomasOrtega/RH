import ReciprocityTheory.L2DbarEstimates.SkodaWeights.NeedBergmanClosed
import ReciprocityTheory.L2DbarEstimates.SkodaWeights.SkodaOps
import ReciprocityTheory.L2DbarEstimates.SkodaWeights.NearContinuousOfSmoothR
import ReciprocityTheory.L2DbarEstimates.MinimalSolutions.OntoWithBoundTop

namespace ReciprocityTheory.L2DbarEstimates.H

open MeasureTheory ReciprocityTheory.L2DbarEstimates
open scoped ENNReal InnerProductSpace

section SlopeTestRemainingChoices

variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]

/- English proof (translation)
Establish `hfst : IsLocalHomeomorph (Prod.fst : M × Fin p → M)`. Rewrite using `[isLocalHomeomorph_iff_isOpenEmbedding_restrict]`. Introduce `q`. Use `⟨Prod.snd ⁻¹' {q.2}, ((isOpen_discrete _).preimage continuous_snd).mem_nhds (by simp), ?_⟩` and prove the remaining obligations. Set `H : (Prod.snd ⁻¹' {q.2} : Set (M × Fin p)) ≃ₜ M` to `{ toFun := fun u => u.1.1 invFun := fun x => ⟨(x, q.2), by simp⟩ left_inv := fun u => by`.

Take `⟨⟨x, j⟩, hj⟩` from `u`. Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff] at hj`. Substitute `hj` using the available equality. Both sides reduce to the same expression. Use `right_inv := fun x => rfl`.

Use `continuous_toFun := continuous_fst.comp continuous_subtype_val`. Use `continuous_invFun := Continuous.subtype_mk (by fun_prop) fun x => by simp }`. Conclude with `H.isOpenEmbedding`. Conclude with `hz.comp hfst`.
-/
private theorem isLocalHomeomorph_fun_prod_fin_fst (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z)
    (p : ℕ) : IsLocalHomeomorph (fun q : M × Fin p => z q.1) := by
  have hfst : IsLocalHomeomorph (Prod.fst : M × Fin p → M) := by
    rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
    intro q
    refine ⟨Prod.snd ⁻¹' {q.2}, ((isOpen_discrete _).preimage continuous_snd).mem_nhds (by simp), ?_⟩
    let H : (Prod.snd ⁻¹' {q.2} : Set (M × Fin p)) ≃ₜ M :=
      { toFun := fun u => u.1.1
        invFun := fun x => ⟨(x, q.2), by simp⟩
        left_inv := fun u => by
          obtain ⟨⟨x, j⟩, hj⟩ := u
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at hj
          subst hj
          rfl
        right_inv := fun x => rfl
        continuous_toFun := continuous_fst.comp continuous_subtype_val
        continuous_invFun := Continuous.subtype_mk (by fun_prop) fun x => by simp }
    exact H.isOpenEmbedding
  exact hz.comp hfst

/- English proof (translation)
Establish `hzq` using `isLocalHomeomorph_fun_prod_fin_fst n z hz p`. Establish `hcover : S = ⋃ i, S ∩ Prod.snd ⁻¹' {i}`. Use extensionality with `q`. Simplify using the standard rewrite rules. Establish `hmeas : ∀ i : Fin p, MeasurableSet (S ∩ Prod.snd ⁻¹' {i})` using `fun i => hS.inter (measurable_snd (measurableSet_singleton i))`.

Establish `hdisj : Pairwise (Function.onFun Disjoint fun i : Fin p => S ∩ Prod.snd ⁻¹' {i})`. Introduce `i j hij`. Use `Set.disjoint_left.2 ?_` and prove the remaining obligations. Introduce and unpack `q ⟨_, hi⟩ ⟨_, hj⟩`. Conclude with `hij ((Set.mem_singleton_iff.1 hi).symm.trans (Set.mem_singleton_iff.1 hj))`.

Use `conv_lhs => rw [hcover]`. Rewrite using `[measure_iUnion hdisj hmeas, tsum_fintype]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[vol_apply n _ hzq _ (hmeas i), vol_apply n z hz _ (hS.preimage (by fun_prop : Measurable fun x : M => (x, i)))]`. Unfold `volFun`.

Use `lintegral_congr fun y => ?_` and prove the remaining obligations. Establish `hset : (S ∩ Prod.snd ⁻¹' {i}) ∩ (fun q : M × Fin p => z q.1) ⁻¹' {y} = (fun x : M => (x, i)) '' ((fun x : M => (x, i)) ⁻¹' S ∩ z ⁻¹' {y})`. Use extensionality with `⟨x, j⟩`. Simplify using `only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_image, Prod.mk.injEq]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨hxS, rfl⟩, hy⟩`. Conclude with `⟨x, ⟨hxS, hy⟩, rfl, rfl⟩`. Introduce and unpack `⟨x', ⟨hxS, hy⟩, rfl, rfl⟩`. Conclude with `⟨⟨hxS, rfl⟩, hy⟩`. Rewrite using `[hset, Set.InjOn.encard_image (fun a _ b _ h => congrArg Prod.fst h)]`.
-/
theorem vol_prodFin_apply (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ)
    (S : Set (M × Fin p)) (hS : MeasurableSet S) :
    vol n (fun q : M × Fin p => z q.1) S = ∑ i, vol n z ((fun x => (x, i)) ⁻¹' S) := by
  have hzq := isLocalHomeomorph_fun_prod_fin_fst n z hz p
  have hcover : S = ⋃ i, S ∩ Prod.snd ⁻¹' {i} := by
    ext q
    simp
  have hmeas : ∀ i : Fin p, MeasurableSet (S ∩ Prod.snd ⁻¹' {i}) := fun i =>
    hS.inter (measurable_snd (measurableSet_singleton i))
  have hdisj : Pairwise (Function.onFun Disjoint fun i : Fin p => S ∩ Prod.snd ⁻¹' {i}) := by
    intro i j hij
    refine Set.disjoint_left.2 ?_
    rintro q ⟨_, hi⟩ ⟨_, hj⟩
    exact hij ((Set.mem_singleton_iff.1 hi).symm.trans (Set.mem_singleton_iff.1 hj))
  conv_lhs => rw [hcover]
  rw [measure_iUnion hdisj hmeas, tsum_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [vol_apply n _ hzq _ (hmeas i),
    vol_apply n z hz _ (hS.preimage (by fun_prop : Measurable fun x : M => (x, i)))]
  unfold volFun
  refine lintegral_congr fun y => ?_
  have hset : (S ∩ Prod.snd ⁻¹' {i}) ∩ (fun q : M × Fin p => z q.1) ⁻¹' {y} =
      (fun x : M => (x, i)) '' ((fun x : M => (x, i)) ⁻¹' S ∩ z ⁻¹' {y}) := by
    ext ⟨x, j⟩
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_image,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hxS, rfl⟩, hy⟩
      exact ⟨x, ⟨hxS, hy⟩, rfl, rfl⟩
    · rintro ⟨x', ⟨hxS, hy⟩, rfl, rfl⟩
      exact ⟨⟨hxS, rfl⟩, hy⟩
  rw [hset, Set.InjOn.encard_image (fun a _ b _ h => congrArg Prod.fst h)]

/- English proof (translation)
Rewrite `h`, the goal using `[ae_iff]`. Take `⟨T, hsub, hT, hT0⟩` from `exists_measurable_superset_of_null h`. Establish `hsub' : {q : M × Fin p | ¬P q.1} ⊆ Prod.fst ⁻¹' T` using `fun q hq => hsub hq`. Use `measure_mono_null hsub' ?_` and prove the remaining obligations. Rewrite using `[vol_prodFin_apply n z hz p _ (hT.preimage measurable_fst)]`.

Conclude with `Finset.sum_eq_zero fun i _ => hT0`.
-/
theorem ae_fst_prodFin (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) {P : M → Prop}
    (h : ∀ᵐ x ∂vol n z, P x) : ∀ᵐ q ∂vol n (fun q : M × Fin p => z q.1), P q.1 := by
  rw [ae_iff] at h ⊢
  obtain ⟨T, hsub, hT, hT0⟩ := exists_measurable_superset_of_null h
  have hsub' : {q : M × Fin p | ¬P q.1} ⊆ Prod.fst ⁻¹' T := fun q hq => hsub hq
  refine measure_mono_null hsub' ?_
  rw [vol_prodFin_apply n z hz p _ (hT.preimage measurable_fst)]
  exact Finset.sum_eq_zero fun i _ => hT0

/- English proof (translation)
Rewrite `h`, the goal using `[ae_iff]`. Take `⟨T, hsub, hT, hT0⟩` from `exists_measurable_superset_of_null h`. Establish `hsub' : {x : M | ¬P (x, i)} ⊆ (fun x : M => (x, i)) ⁻¹' T` using `fun x hx => hsub hx`. Use `measure_mono_null hsub' ?_` and prove the remaining obligations. Establish `hsum` using `vol_prodFin_apply n z hz p T hT`.

Rewrite `hsum` using `[hT0]`. Conclude with `(Finset.sum_eq_zero_iff.1 hsum.symm) i (Finset.mem_univ i)`.
-/
theorem ae_slice_prodFin (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ)
    {P : M × Fin p → Prop} (h : ∀ᵐ q ∂vol n (fun q : M × Fin p => z q.1), P q) (i : Fin p) :
    ∀ᵐ x ∂vol n z, P (x, i) := by
  rw [ae_iff] at h ⊢
  obtain ⟨T, hsub, hT, hT0⟩ := exists_measurable_superset_of_null h
  have hsub' : {x : M | ¬P (x, i)} ⊆ (fun x : M => (x, i)) ⁻¹' T := fun x hx => hsub hx
  refine measure_mono_null hsub' ?_
  have hsum := vol_prodFin_apply n z hz p T hT
  rw [hT0] at hsum
  exact (Finset.sum_eq_zero_iff.1 hsum.symm) i (Finset.mem_univ i)

/- English proof (translation)
Establish `h : Holo n z (∑ i, F i)` using `Finset.sum_induction F (fun f : M → ℂ => Holo n z f) (fun a b ha hb => Holo.add n z a b ha hb) (Holo.const n z 0) (fun i _ => hF i)`. Establish `e : (fun x => ∑ i, F i x) = ∑ i, F i`. Use extensionality with `x`. Simplify using `[Finset.sum_apply]`. Rewrite using `[e]`.

Conclude with `h`.
-/
theorem holo_finsum (n : ℕ) (z : M → V n) {p : ℕ} (F : Fin p → M → ℂ) (hF : ∀ i, Holo n z (F i)) :
    Holo n z (fun x => ∑ i, F i x) := by
  have h : Holo n z (∑ i, F i) :=
    Finset.sum_induction F (fun f : M → ℂ => Holo n z f)
      (fun a b ha hb => Holo.add n z a b ha hb) (Holo.const n z 0) (fun i _ => hF i)
  have e : (fun x => ∑ i, F i x) = ∑ i, F i := by
    ext x
    simp [Finset.sum_apply]
  rw [e]
  exact h

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `X p g ph0 t f hp hg hnz hs hl ht hf hA`. Establish `hz` using `X.isLocalHomeomorph`. Establish `hz' : IsLocalHomeomorph (fun q : M × Fin p => X.z q.1)` using `isLocalHomeomorph_comp_fst n X.z hz p`. Establish `hp1 : 1 ≤ p` using `by omega`. Establish `hp1r : (1 : ℝ) ≤ p` using `by exact_mod_cast hp1`.

Establish `ht0 : 0 < t` using `by linarith`. Establish `hgv : ∀ x, gv g x ≠ 0` using `fun x h => by`. Take `⟨i, hi⟩` from `hnz x`. Conclude with `hi (congrFun h i)`. Establish `hN : ∀ x, 0 < vsq (gv g x)` using `fun x => by`.

Take `⟨i, hi⟩` from `hnz x`. Conclude with `Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hi) 2⟩`. Establish `hgc : ∀ i, Continuous (g i)` using `fun i => Smooth.continuous n X.z hz _ (Holo.smooth n X.z _ (hg i))`. Establish `hfc : Continuous f` using `Smooth.continuous n X.z hz _ (Holo.smooth n X.z _ hf)`. Establish `hNc : Continuous fun x => vsq (gv g x)` using `continuous_finsetSum _ fun i _ => ((hgc i).norm.pow 2)`.

Establish `hW` using `skodaWeight n M X.z hz p g ph0 t hg hgv hs hl ht0.le`. Establish `hφc : Continuous (skW g ph0 t)` using `(Complex.continuous_re.comp (Smooth.continuous n X.z hz _ hW.1)).congr fun x => Complex.ofReal_re _`. Establish `hψ₂c : Continuous fun x => skW g ph0 t x + Real.log (vsq (gv g x))` using `hφc.add (hNc.log fun x => (hN x).ne')`. Establish `hψ₁c : Continuous fun x : M × Fin p => skW g ph0 t x.1` using `hφc.comp continuous_fst`. Establish `hl2` using `l2w n M X.z _ hψ₂c.measurable`.

Establish `hl1` using `l2w n (M × Fin p) (fun q => X.z q.1) _ hψ₁c.measurable`. Take `⟨G, Gs, hG, hGs, hadj, hiso⟩` from `skodaOps n M X p g (skW g ph0 t) hg hgv hφc`. Establish `hKc` using `hB p (fun q => X.z q.1) hz' _ hψ₁c`. Establish `: CompleteSpace (holSub n (fun q : M × Fin p => X.z q.1) (fun x => skW g ph0 t x.1))` using `hKc.completeSpace_coe`. Use `set K := holSub n (fun q : M × Fin p => X.z q.1) (fun x => skW g ph0 t x.1) with hKdef`.

Use `set Q := holSub n X.z (fun x => skW g ph0 t x + Real.log (vsq (gv g x))) with hQdef`. Use `set c : ℝ := (t - ((p : ℝ) - 1)) / t with hcdef`. Establish `hc : 0 < c` using `div_pos (by linarith) ht0`. Establish `hc' : ∀ r : ℝ, c * r = r - ((p : ℝ) - 1) / t * r` using `fun r => by`. Rewrite using `[hcdef]`.

Clear the denominators using the available nonvanishing facts. Establish `hnear : ∀ u ∈ Q, c * ‖u‖ ^ 2 ≤ ‖K.orthogonalProjectionOnto (Gs u)‖ ^ 2`. Introduce `u hu`. Take `⟨u', hu', huu'⟩` from `hu`. Establish `huv : (u : M → ℂ) =ᵐ[vol n X.z] u'` using `(hl2.1 _).1 huu'`.

Establish `hF0 : (Gs u : M × Fin p → ℂ) =ᵐ[vol n (fun q : M × Fin p => X.z q.1)] fun x => u' x.1 * (starRingEnd ℂ) (g x.2 x.1) / ((vsq (gv g x.1) : ℝ) : ℂ)` using `by filter_upwards [hGs u, ae_fst_prodFin n X.z hz p huv] with q h1 h2`. Rewrite using `[h1, h2]`. Take `⟨F, hFK, hFd⟩` from `skodaNear n M X p g ph0 t (hH p) hp1 hg hgv hs hl ht0 u u' hu' huv (Gs u) hF0`. Establish `hya : Gs u - K.starProjection (Gs u) ∈ Kᗮ` using `K.sub_starProjection_mem_orthogonal (Gs u)`. Establish `hperp : ⟪K.starProjection (Gs u), Gs u - K.starProjection (Gs u)⟫_ℂ = 0` using `Submodule.inner_right_of_mem_orthogonal (K.orthogonalProjectionOnto (Gs u)).2 hya`.

Establish `hpy` using `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hperp`. Rewrite `hpy` using `[add_sub_cancel, hiso u]`. Establish `hmin : ‖Gs u - K.starProjection (Gs u)‖ ≤ ‖Gs u - F‖`. Rewrite using `[Submodule.starProjection_minimal (U := K) (Gs u)]`. Conclude with `ciInf_le ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩ (⟨F, hFK⟩ : K)`.

Establish `hmin2` using `pow_le_pow_left₀ (norm_nonneg _) hmin 2`. Establish `hnorm : ‖K.orthogonalProjectionOnto (Gs u)‖ = ‖K.starProjection (Gs u)‖` using `rfl`. Rewrite using `[hnorm, hc']`. Use polynomial arithmetic with `[hpy, hmin2, hFd]`. Establish `hAeq : ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2 * (∑ i, ‖g i x‖ ^ 2) ^ (-(t + 1)) * Real.exp (-ph0 x)) ∂vol n X.z = wint n X.z f (fun x => skW g ph0 t x + Real.log (vsq (gv g x)))`.

Unfold `wint`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Rewrite using `[show (∑ i, ‖g i x‖ ^ 2) = vsq (gv g x) from rfl, Real.rpow_def_of_pos (hN x), mul_assoc, ← Real.exp_add]`. Use `congr 3`. Simplify using `only [skW]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨fL, hfL⟩` from `hl2.2.2 f hfc.aestronglyMeasurable (hAeq ▸ hA)`. Establish `hfLQ : fL ∈ Q` using `⟨f, hf, (hl2.1 _).2 hfL⟩`. Take `⟨⟨hv, hvK⟩, hhG, -, hhn⟩` from `ontoWithBound ℂ K _ ((G : _ →ₗ[ℂ] _).comp K.subtype) ((K.orthogonalProjectionOnto.comp Gs : _ →L[ℂ] K) : _ →ₗ[ℂ] K) 0 Q c hc (fun u _ x => by simp [hadj]) (fun u hu e => by simpa using hnear u hu) fL hfLQ`. Establish `hhn' : c * ‖hv‖ ^ 2 ≤ ‖fL‖ ^ 2` using `hhn`.

Take `⟨hh', hhol', hae'⟩` from `hvK`. Establish `hae'v : (hv : M × Fin p → ℂ) =ᵐ[vol n (fun q : M × Fin p => X.z q.1)] hh'` using `(hl1.1 _).1 hae'`. Establish `hslice : ∀ᵐ x ∂vol n X.z, ∀ i, (hv : M × Fin p → ℂ) (x, i) = hh' (x, i)` using `ae_all_iff.2 fun i => ae_slice_prodFin n X.z hz p hae'v i`. Establish `hhol : ∀ i, Holo n X.z (fun x => hh' (x, i))` using `(holo_prodFin_iff n X.z hz p hh').1 hhol'`. Establish `hSh : Holo n X.z (fun x => ∑ i, g i x * hh' (x, i))` using `holo_finsum n X.z _ fun i => Holo.mul n X.z _ _ (hg i) (hhol i)`.

Establish `hGS : (G hv : M → ℂ) =ᵐ[vol n X.z] fun x => ∑ i, g i x * hh' (x, i)` using `by filter_upwards [hG hv, hslice] with x h1 h2`. Rewrite using `[h1]; exact Finset.sum_congr rfl fun i _ => by rw [h2 i]`. Establish `hGQ : G hv ∈ Q` using `⟨_, hSh, (hl2.1 _).2 hGS⟩`. Establish `hGf : G hv = fL`. Establish `h1` using `hhG (G hv - fL) (Q.sub_mem hGQ hfLQ)`.

Simplify using `only [LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply, Submodule.coe_subtype] at h1`. Rewrite `h1` using `[← sub_eq_zero, ← inner_sub_right]`. Conclude with `sub_eq_zero.1 (inner_self_eq_zero.1 h1)`. Establish `hfS : ∀ x, f x = ∑ i, g i x * hh' (x, i)`. Establish `hae : ∀ᵐ x ∂vol n X.z, f x = ∑ i, g i x * hh' (x, i)` using `by filter_upwards [hGS, hfL] with x h1 h2`.

Rewrite using `[← h2, ← hGf, h1]`. Establish `hSc : Continuous fun x => ∑ i, g i x * hh' (x, i)` using `Smooth.continuous n X.z hz _ (Holo.smooth n X.z _ hSh)`. Assume the negation of the conclusion as `hne`. Take `⟨x0, hx0⟩` from `not_forall.1 hne`. Establish `hpos` using `volOpenPos n M X.z hz _ (isOpen_ne_fun hfc hSc) ⟨x0, hx0⟩`.

Rewrite `hae` using `[ae_iff]`. Conclude with `hpos.ne' hae`. Establish `hh'c : Continuous hh'` using `Smooth.continuous n _ hz' _ (Holo.smooth n _ _ hhol')`. Establish `hmeas : ∀ i, Measurable fun x => ENNReal.ofReal (‖hh' (x, i)‖ ^ 2 * Real.exp (-skW g ph0 t x))` using `fun i => (ENNReal.continuous_ofReal.comp (((hh'c.comp (continuous_id.prodMk continuous_const)).norm.pow 2).mul (Real.continuous_exp.comp hφc.neg))).measurable`. Use `⟨fun i x => hh' (x, i), hhol, hfS, ?_⟩` and prove the remaining obligations.

Use `beta_reduce`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← lintegral_finsetSum _ (fun i _ => hmeas i)]`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Rewrite using `[← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]`.

Use `congr 1`. Rewrite using `[show (∑ i, ‖g i x‖ ^ 2) = vsq (gv g x) from rfl, Real.rpow_def_of_pos (hN x), Finset.sum_mul, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, ← Real.exp_add]`. Use `congr 2`.

Simplify using `only [skW]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = wint n (fun q : M × Fin p => X.z q.1) hh' (fun x => skW g ph0 t x.1) := by`. Unfold `wint`. Establish `hm : Measurable fun q : M × Fin p => ENNReal.ofReal (‖hh' q‖ ^ 2 * Real.exp (-skW g ph0 t q.1))` using `(ENNReal.continuous_ofReal.comp ((hh'c.norm.pow 2).mul (Real.continuous_exp.comp hψ₁c.neg))).measurable`.

Rewrite using `[lintegral_vol_prodFin n X.z hz p _ hm]`. Use `_ = wint n (fun q : M × Fin p => X.z q.1) hv (fun x => skW g ph0 t x.1) := by`. Unfold `wint`. Conclude with `lintegral_congr_ae (by filter_upwards [hae'v] with q hq; rw [hq])`. Use `_ = ENNReal.ofReal (‖hv‖ ^ 2) := by`.

Rewrite using `[(hl1.2.1 hv).2, ENNReal.ofReal_toReal (hl1.2.1 hv).1.ne]`. Use `_ ≤ ENNReal.ofReal (t / (t - ((p : ℝ) - 1)) * ‖fL‖ ^ 2) := by`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Establish `hci : t / (t - ((p : ℝ) - 1)) = c⁻¹` using `by rw [hcdef, inv_div]`. Rewrite using `[hci, ← div_eq_inv_mul, le_div_iff₀ hc]`.

Combine the linear relations using `[hhn']`. Use `_ = ENNReal.ofReal (t / (t - ((p : ℝ) - 1))) * wint n X.z f (fun x => skW g ph0 t x + Real.log (vsq (gv g x))) := by`. Rewrite using `[ENNReal.ofReal_mul (div_nonneg ht0.le (by linarith)), (hl2.2.1 fL).2, ENNReal.ofReal_toReal (hl2.2.1 fL).1.ne]`. Use `congr 1`. Unfold `wint`.

Conclude with `lintegral_congr_ae (by filter_upwards [hfL] with x hx; rw [hx])`. Use `_ = _ := by rw [hAeq]`.
-/
theorem skoda (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    (hH : ∀ p : ℕ, HStatement n (M × Fin p))
    (hB : ∀ p : ℕ, NeedBergmanClosed n (M × Fin p)) :
    SStatement n M := by
  intro X p g ph0 t f hp hg hnz hs hl ht hf hA
  have hz := X.isLocalHomeomorph
  have hz' : IsLocalHomeomorph (fun q : M × Fin p => X.z q.1) :=
    isLocalHomeomorph_comp_fst n X.z hz p
  have hp1 : 1 ≤ p := by omega
  have hp1r : (1 : ℝ) ≤ p := by exact_mod_cast hp1
  have ht0 : 0 < t := by linarith
  have hgv : ∀ x, gv g x ≠ 0 := fun x h => by
    obtain ⟨i, hi⟩ := hnz x; exact hi (congrFun h i)
  have hN : ∀ x, 0 < vsq (gv g x) := fun x => by
    obtain ⟨i, hi⟩ := hnz x
    exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hi) 2⟩
  have hgc : ∀ i, Continuous (g i) := fun i => Smooth.continuous n X.z hz _ (Holo.smooth n X.z _ (hg i))
  have hfc : Continuous f := Smooth.continuous n X.z hz _ (Holo.smooth n X.z _ hf)
  have hNc : Continuous fun x => vsq (gv g x) :=
    continuous_finsetSum _ fun i _ => ((hgc i).norm.pow 2)
  have hW := skodaWeight n M X.z hz p g ph0 t hg hgv hs hl ht0.le
  have hφc : Continuous (skW g ph0 t) :=
    (Complex.continuous_re.comp (Smooth.continuous n X.z hz _ hW.1)).congr fun x => Complex.ofReal_re _
  have hψ₂c : Continuous fun x => skW g ph0 t x + Real.log (vsq (gv g x)) :=
    hφc.add (hNc.log fun x => (hN x).ne')
  have hψ₁c : Continuous fun x : M × Fin p => skW g ph0 t x.1 := hφc.comp continuous_fst
  have hl2 := l2w n M X.z _ hψ₂c.measurable
  have hl1 := l2w n (M × Fin p) (fun q => X.z q.1) _ hψ₁c.measurable
  obtain ⟨G, Gs, hG, hGs, hadj, hiso⟩ := skodaOps n M X p g (skW g ph0 t) hg hgv hφc
  have hKc := hB p (fun q => X.z q.1) hz' _ hψ₁c
  have : CompleteSpace (holSub n (fun q : M × Fin p => X.z q.1) (fun x => skW g ph0 t x.1)) :=
    hKc.completeSpace_coe
  set K := holSub n (fun q : M × Fin p => X.z q.1) (fun x => skW g ph0 t x.1) with hKdef
  set Q := holSub n X.z (fun x => skW g ph0 t x + Real.log (vsq (gv g x))) with hQdef
  set c : ℝ := (t - ((p : ℝ) - 1)) / t with hcdef
  have hc : 0 < c := div_pos (by linarith) ht0
  have hc' : ∀ r : ℝ, c * r = r - ((p : ℝ) - 1) / t * r := fun r => by
    rw [hcdef]; field_simp

  have hnear : ∀ u ∈ Q, c * ‖u‖ ^ 2 ≤ ‖K.orthogonalProjectionOnto (Gs u)‖ ^ 2 := by
    intro u hu
    obtain ⟨u', hu', huu'⟩ := hu
    have huv : (u : M → ℂ) =ᵐ[vol n X.z] u' := (hl2.1 _).1 huu'
    have hF0 : (Gs u : M × Fin p → ℂ) =ᵐ[vol n (fun q : M × Fin p => X.z q.1)]
        fun x => u' x.1 * (starRingEnd ℂ) (g x.2 x.1) / ((vsq (gv g x.1) : ℝ) : ℂ) := by
      filter_upwards [hGs u, ae_fst_prodFin n X.z hz p huv] with q h1 h2
      rw [h1, h2]
    obtain ⟨F, hFK, hFd⟩ :=
      skodaNear n M X p g ph0 t (hH p) hp1 hg hgv hs hl ht0 u u' hu' huv (Gs u) hF0
    have hya : Gs u - K.starProjection (Gs u) ∈ Kᗮ := K.sub_starProjection_mem_orthogonal (Gs u)
    have hperp : ⟪K.starProjection (Gs u), Gs u - K.starProjection (Gs u)⟫_ℂ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (K.orthogonalProjectionOnto (Gs u)).2 hya
    have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hperp
    rw [add_sub_cancel, hiso u] at hpy
    have hmin : ‖Gs u - K.starProjection (Gs u)‖ ≤ ‖Gs u - F‖ := by
      rw [Submodule.starProjection_minimal (U := K) (Gs u)]
      exact ciInf_le ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩ (⟨F, hFK⟩ : K)
    have hmin2 := pow_le_pow_left₀ (norm_nonneg _) hmin 2
    have hnorm : ‖K.orthogonalProjectionOnto (Gs u)‖ = ‖K.starProjection (Gs u)‖ := rfl
    rw [hnorm, hc']
    nlinarith [hpy, hmin2, hFd]

  have hAeq : ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2 * (∑ i, ‖g i x‖ ^ 2) ^ (-(t + 1)) *
      Real.exp (-ph0 x)) ∂vol n X.z =
      wint n X.z f (fun x => skW g ph0 t x + Real.log (vsq (gv g x))) := by
    unfold wint
    refine lintegral_congr fun x => ?_
    rw [show (∑ i, ‖g i x‖ ^ 2) = vsq (gv g x) from rfl, Real.rpow_def_of_pos (hN x), mul_assoc,
      ← Real.exp_add]
    congr 3
    simp only [skW]; ring
  obtain ⟨fL, hfL⟩ := hl2.2.2 f hfc.aestronglyMeasurable (hAeq ▸ hA)
  have hfLQ : fL ∈ Q := ⟨f, hf, (hl2.1 _).2 hfL⟩
  obtain ⟨⟨hv, hvK⟩, hhG, -, hhn⟩ := ontoWithBound ℂ K _ ((G : _ →ₗ[ℂ] _).comp K.subtype)
    ((K.orthogonalProjectionOnto.comp Gs : _ →L[ℂ] K) : _ →ₗ[ℂ] K) 0 Q c hc
    (fun u _ x => by simp [hadj]) (fun u hu e => by simpa using hnear u hu) fL hfLQ
  have hhn' : c * ‖hv‖ ^ 2 ≤ ‖fL‖ ^ 2 := hhn
  obtain ⟨hh', hhol', hae'⟩ := hvK
  have hae'v : (hv : M × Fin p → ℂ) =ᵐ[vol n (fun q : M × Fin p => X.z q.1)] hh' :=
    (hl1.1 _).1 hae'
  have hslice : ∀ᵐ x ∂vol n X.z, ∀ i, (hv : M × Fin p → ℂ) (x, i) = hh' (x, i) :=
    ae_all_iff.2 fun i => ae_slice_prodFin n X.z hz p hae'v i
  have hhol : ∀ i, Holo n X.z (fun x => hh' (x, i)) := (holo_prodFin_iff n X.z hz p hh').1 hhol'
  have hSh : Holo n X.z (fun x => ∑ i, g i x * hh' (x, i)) :=
    holo_finsum n X.z _ fun i => Holo.mul n X.z _ _ (hg i) (hhol i)
  have hGS : (G hv : M → ℂ) =ᵐ[vol n X.z] fun x => ∑ i, g i x * hh' (x, i) := by
    filter_upwards [hG hv, hslice] with x h1 h2
    rw [h1]; exact Finset.sum_congr rfl fun i _ => by rw [h2 i]
  have hGQ : G hv ∈ Q := ⟨_, hSh, (hl2.1 _).2 hGS⟩
  have hGf : G hv = fL := by
    have h1 := hhG (G hv - fL) (Q.sub_mem hGQ hfLQ)
    simp only [LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Function.comp_apply,
      Submodule.coe_subtype] at h1
    rw [← sub_eq_zero, ← inner_sub_right] at h1
    exact sub_eq_zero.1 (inner_self_eq_zero.1 h1)
  have hfS : ∀ x, f x = ∑ i, g i x * hh' (x, i) := by
    have hae : ∀ᵐ x ∂vol n X.z, f x = ∑ i, g i x * hh' (x, i) := by
      filter_upwards [hGS, hfL] with x h1 h2
      rw [← h2, ← hGf, h1]
    have hSc : Continuous fun x => ∑ i, g i x * hh' (x, i) :=
      Smooth.continuous n X.z hz _ (Holo.smooth n X.z _ hSh)
    by_contra hne
    obtain ⟨x0, hx0⟩ := not_forall.1 hne
    have hpos := volOpenPos n M X.z hz _ (isOpen_ne_fun hfc hSc) ⟨x0, hx0⟩
    rw [ae_iff] at hae
    exact hpos.ne' hae
  have hh'c : Continuous hh' := Smooth.continuous n _ hz' _ (Holo.smooth n _ _ hhol')
  have hmeas : ∀ i, Measurable fun x =>
      ENNReal.ofReal (‖hh' (x, i)‖ ^ 2 * Real.exp (-skW g ph0 t x)) := fun i =>
    (ENNReal.continuous_ofReal.comp (((hh'c.comp (continuous_id.prodMk continuous_const)).norm.pow 2).mul
      (Real.continuous_exp.comp hφc.neg))).measurable
  refine ⟨fun i x => hh' (x, i), hhol, hfS, ?_⟩
  beta_reduce
  calc ∫⁻ x, ENNReal.ofReal ((∑ i, ‖hh' (x, i)‖ ^ 2) * (∑ i, ‖g i x‖ ^ 2) ^ (-t) *
          Real.exp (-ph0 x)) ∂vol n X.z
        = ∑ i, ∫⁻ x, ENNReal.ofReal (‖hh' (x, i)‖ ^ 2 * Real.exp (-skW g ph0 t x)) ∂vol n X.z := by
        rw [← lintegral_finsetSum _ (fun i _ => hmeas i)]
        refine lintegral_congr fun x => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
        congr 1
        rw [show (∑ i, ‖g i x‖ ^ 2) = vsq (gv g x) from rfl, Real.rpow_def_of_pos (hN x),
          Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        simp only [skW]; ring
    _ = wint n (fun q : M × Fin p => X.z q.1) hh' (fun x => skW g ph0 t x.1) := by
        unfold wint
        have hm : Measurable fun q : M × Fin p =>
            ENNReal.ofReal (‖hh' q‖ ^ 2 * Real.exp (-skW g ph0 t q.1)) :=
          (ENNReal.continuous_ofReal.comp
            ((hh'c.norm.pow 2).mul (Real.continuous_exp.comp hψ₁c.neg))).measurable
        rw [lintegral_vol_prodFin n X.z hz p _ hm]
    _ = wint n (fun q : M × Fin p => X.z q.1) hv (fun x => skW g ph0 t x.1) := by
        unfold wint
        exact lintegral_congr_ae (by filter_upwards [hae'v] with q hq; rw [hq])
    _ = ENNReal.ofReal (‖hv‖ ^ 2) := by
        rw [(hl1.2.1 hv).2, ENNReal.ofReal_toReal (hl1.2.1 hv).1.ne]
    _ ≤ ENNReal.ofReal (t / (t - ((p : ℝ) - 1)) * ‖fL‖ ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        have hci : t / (t - ((p : ℝ) - 1)) = c⁻¹ := by rw [hcdef, inv_div]
        rw [hci, ← div_eq_inv_mul, le_div_iff₀ hc]
        linarith [hhn']
    _ = ENNReal.ofReal (t / (t - ((p : ℝ) - 1))) *
          wint n X.z f (fun x => skW g ph0 t x + Real.log (vsq (gv g x))) := by
        rw [ENNReal.ofReal_mul (div_nonneg ht0.le (by linarith)), (hl2.2.1 fL).2,
          ENNReal.ofReal_toReal (hl2.2.1 fL).1.ne]
        congr 1
        unfold wint
        exact lintegral_congr_ae (by filter_upwards [hfL] with x hx; rw [hx])
    _ = _ := by rw [hAeq]

end ReciprocityTheory.L2DbarEstimates.H
