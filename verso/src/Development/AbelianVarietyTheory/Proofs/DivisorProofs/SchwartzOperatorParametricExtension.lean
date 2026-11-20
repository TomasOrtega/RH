import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTemperateGrowthProdMkConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSliceSeminormLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasFderivAtSchwartzOperatorFirstStatement

noncomputable section

open scoped SchwartzMap ContDiff

namespace GlobalTheory.SchwartzFstOp

section Bounds

variable {X Y F G : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => rw [Finset.sup_empty]`. Conclude with `continuous_const`. Consider the case `insert i s _ ih`. Rewrite using `[Finset.sup_insert]`.

Conclude with `(((schwartz_withSeminorms ℂ Y G).continuous_seminorm i).max ih).congr fun x => (Seminorm.sup_apply _ _ _).symm`.
-/
theorem continuous_finset_sup_schwartz (s : Finset (ℕ × ℕ)) :
    Continuous ⇑(s.sup (schwartzSeminormFamily ℂ Y G)) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sup_empty]; exact continuous_const
  | insert i s _ ih =>
    rw [Finset.sup_insert]
    exact (((schwartz_withSeminorms ℂ Y G).continuous_seminorm i).max ih).congr
      fun x => (Seminorm.sup_apply _ _ _).symm

/- English proof (translation)
Take `⟨t, C, -, hC⟩` from `Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ X F) ((s.sup (schwartzSeminormFamily ℂ Y G)).comp A.toLinearMap) ((continuous_finset_sup_schwartz s).comp A.continuous)`. Conclude with `⟨t, C, C.2, fun f => by simpa [Seminorm.comp_apply, Seminorm.smul_apply, NNReal.smul_def] using hC f⟩`.
-/
theorem exists_sup_bound (A : 𝓢(X, F) →L[ℂ] 𝓢(Y, G)) (s : Finset (ℕ × ℕ)) :
    ∃ (t : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ f, (s.sup (schwartzSeminormFamily ℂ Y G)) (A f) ≤
      C * (t.sup (schwartzSeminormFamily ℂ X F)) f := by
  obtain ⟨t, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ X F)
    ((s.sup (schwartzSeminormFamily ℂ Y G)).comp A.toLinearMap)
    ((continuous_finset_sup_schwartz s).comp A.continuous)
  exact ⟨t, C, C.2, fun f => by simpa [Seminorm.comp_apply, Seminorm.smul_apply, NNReal.smul_def] using hC f⟩

/- English proof (translation)
The claim follows from `Seminorm.le_def.1 (Finset.sup_mono h) f`.
-/
theorem sup_apply_mono {s t : Finset (ℕ × ℕ)} (h : s ⊆ t) (f : 𝓢(X, F)) :
    (s.sup (schwartzSeminormFamily ℂ X F)) f ≤ (t.sup (schwartzSeminormFamily ℂ X F)) f :=
  Seminorm.le_def.1 (Finset.sup_mono h) f

end Bounds

variable {V W V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']

/- English proof (translation)
Use `set c : ℝ := ‖x'‖ ^ k with hc`. Establish `c0 : 0 ≤ c` using `by positivity`. Use `set R := ((s.image fun m : ℕ × ℕ => ((m.1 + k, m.2) : ℕ × ℕ)).sup (schwartzSeminormFamily ℂ (V × V') ℂ)) f`. Establish `h1 : ∀ m ∈ s, c * schwartzSeminormFamily ℂ V ℂ m (sliceCLM x' f) ≤ R`. Introduce `m hm`.

Establish `a1 : ‖x'‖ ^ k * SchwartzMap.seminorm ℂ m.1 m.2 (sliceCLM x' f) ≤ SchwartzMap.seminorm ℂ (m.1 + k) m.2 f` using `GlobalTheory.T.schwartz_slice_seminorm_le f x' m.1 k m.2`. Establish `a2 : schwartzSeminormFamily ℂ (V × V') ℂ ((m.1 + k, m.2) : ℕ × ℕ) f ≤ R` using `Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ (V × V') ℂ) (Finset.mem_image_of_mem (fun m : ℕ × ℕ => ((m.1 + k, m.2) : ℕ × ℕ)) hm)`. Conclude with `a1.trans a2`. Break down `c0.eq_or_lt with h | h` into its components or cases. Rewrite using `[← h, zero_mul]`.

Conclude with `apply_nonneg _ _`. Rewrite using `[← le_div_iff₀' h]`. Use `Seminorm.finset_sup_apply_le (div_nonneg (apply_nonneg _ _) c0) fun m hm => ?_` and prove the remaining obligations. Rewrite using `[le_div_iff₀' h]`. Conclude with `h1 m hm`.
-/
theorem slice_sup_le (f : 𝓢(V × V', ℂ)) (x' : V') (s : Finset (ℕ × ℕ)) (k : ℕ) :
    ‖x'‖ ^ k * (s.sup (schwartzSeminormFamily ℂ V ℂ)) (sliceCLM x' f) ≤
      ((s.image fun m : ℕ × ℕ => ((m.1 + k, m.2) : ℕ × ℕ)).sup (schwartzSeminormFamily ℂ (V × V') ℂ)) f := by
  set c : ℝ := ‖x'‖ ^ k with hc
  have c0 : 0 ≤ c := by positivity
  set R := ((s.image fun m : ℕ × ℕ => ((m.1 + k, m.2) : ℕ × ℕ)).sup (schwartzSeminormFamily ℂ (V × V') ℂ)) f
  have h1 : ∀ m ∈ s, c * schwartzSeminormFamily ℂ V ℂ m (sliceCLM x' f) ≤ R := by
    intro m hm
    have a1 : ‖x'‖ ^ k * SchwartzMap.seminorm ℂ m.1 m.2 (sliceCLM x' f) ≤
        SchwartzMap.seminorm ℂ (m.1 + k) m.2 f := GlobalTheory.T.schwartz_slice_seminorm_le f x' m.1 k m.2
    have a2 : schwartzSeminormFamily ℂ (V × V') ℂ ((m.1 + k, m.2) : ℕ × ℕ) f ≤ R :=
      Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ (V × V') ℂ)
        (Finset.mem_image_of_mem (fun m : ℕ × ℕ => ((m.1 + k, m.2) : ℕ × ℕ)) hm)
    exact a1.trans a2
  rcases c0.eq_or_lt with h | h
  · rw [← h, zero_mul]; exact apply_nonneg _ _
  · rw [← le_div_iff₀' h]
    refine Seminorm.finset_sup_apply_le (div_nonneg (apply_nonneg _ _) c0) fun m hm => ?_
    rw [le_div_iff₀' h]
    exact h1 m hm

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Take `⟨s₁, C₁, hC₁, h₁⟩` from `exists_sup_bound T {(k, 0)}`. Take `⟨s₂, C₂, hC₂, h₂⟩` from `exists_sup_bound T {(0, 0)}`. Use `set t₁ := s₁.image fun m : ℕ × ℕ => ((m.1 + 0, m.2) : ℕ × ℕ)`. Use `set t₂ := s₂.image fun m : ℕ × ℕ => ((m.1 + k, m.2) : ℕ × ℕ)`. Use `⟨t₁ ∪ t₂, C₁ + C₂, by positivity, fun f p => ?_⟩` and prove the remaining obligations.

Take `⟨y, x'⟩` from `p`. Use `set h := sliceCLM x' f`. Establish `e1 : ‖y‖ ^ k * ‖T h y‖ ≤ C₁ * (s₁.sup (schwartzSeminormFamily ℂ V ℂ)) h`. Use `(SchwartzMap.norm_pow_mul_le_seminorm ℂ (T h) k y).trans ?_` and prove the remaining obligations. Use `h₁ h` as an intermediate fact.

Simplify `this` using `[schwartzSeminormFamily]`. Establish `e2 : ‖T h y‖ ≤ C₂ * (s₂.sup (schwartzSeminormFamily ℂ V ℂ)) h`. Establish `a` using `SchwartzMap.norm_pow_mul_le_seminorm ℂ (T h) 0 y`. Simplify using `only [pow_zero, one_mul] at a`. Use `a.trans ?_` and prove the remaining obligations.

Use `h₂ h` as an intermediate fact. Simplify `this` using `[schwartzSeminormFamily]`. Establish `f1 : (s₁.sup (schwartzSeminormFamily ℂ V ℂ)) h ≤ ((t₁ ∪ t₂).sup (schwartzSeminormFamily ℂ (V × V') ℂ)) f`. Use `slice_sup_le f x' s₁ 0` as an intermediate fact. Rewrite `this` using `[pow_zero, one_mul]`.

Conclude with `this.trans (sup_apply_mono Finset.subset_union_left f)`. Establish `f2 : ‖x'‖ ^ k * (s₂.sup (schwartzSeminormFamily ℂ V ℂ)) h ≤ ((t₁ ∪ t₂).sup (schwartzSeminormFamily ℂ (V × V') ℂ)) f` using `(slice_sup_le f x' s₂ k).trans (sup_apply_mono Finset.subset_union_right f)`. Establish `hp : ‖(y, x')‖ ^ k ≤ ‖y‖ ^ k + ‖x'‖ ^ k`. Rewrite using `[Prod.norm_mk]`. Break down `le_total ‖y‖ ‖x'‖ with hl | hl` into its components or cases.

Rewrite using `[max_eq_right hl]`. Combine the linear relations using `[pow_nonneg (norm_nonneg y) k]`. Rewrite using `[max_eq_left hl]`. Combine the linear relations using `[pow_nonneg (norm_nonneg x') k]`. Use `set S := ((t₁ ∪ t₂).sup (schwartzSeminormFamily ℂ (V × V') ℂ)) f`.

Express the relevant statement in the definitionally equal form `‖(y, x')‖ ^ k * ‖T h y‖ ≤ (C₁ + C₂) * S`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem base_bound (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (k : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (f : 𝓢(V × V', ℂ)) (p : W × V'),
      ‖p‖ ^ k * ‖opFst T f p‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ (V × V') ℂ)) f := by
  obtain ⟨s₁, C₁, hC₁, h₁⟩ := exists_sup_bound T {(k, 0)}
  obtain ⟨s₂, C₂, hC₂, h₂⟩ := exists_sup_bound T {(0, 0)}
  set t₁ := s₁.image fun m : ℕ × ℕ => ((m.1 + 0, m.2) : ℕ × ℕ)
  set t₂ := s₂.image fun m : ℕ × ℕ => ((m.1 + k, m.2) : ℕ × ℕ)
  refine ⟨t₁ ∪ t₂, C₁ + C₂, by positivity, fun f p => ?_⟩
  obtain ⟨y, x'⟩ := p
  set h := sliceCLM x' f
  have e1 : ‖y‖ ^ k * ‖T h y‖ ≤ C₁ * (s₁.sup (schwartzSeminormFamily ℂ V ℂ)) h := by
    refine (SchwartzMap.norm_pow_mul_le_seminorm ℂ (T h) k y).trans ?_
    have := h₁ h
    simpa [schwartzSeminormFamily] using this
  have e2 : ‖T h y‖ ≤ C₂ * (s₂.sup (schwartzSeminormFamily ℂ V ℂ)) h := by
    have a := SchwartzMap.norm_pow_mul_le_seminorm ℂ (T h) 0 y
    simp only [pow_zero, one_mul] at a
    refine a.trans ?_
    have := h₂ h
    simpa [schwartzSeminormFamily] using this
  have f1 : (s₁.sup (schwartzSeminormFamily ℂ V ℂ)) h ≤
      ((t₁ ∪ t₂).sup (schwartzSeminormFamily ℂ (V × V') ℂ)) f := by
    have := slice_sup_le f x' s₁ 0
    rw [pow_zero, one_mul] at this
    exact this.trans (sup_apply_mono Finset.subset_union_left f)
  have f2 : ‖x'‖ ^ k * (s₂.sup (schwartzSeminormFamily ℂ V ℂ)) h ≤
      ((t₁ ∪ t₂).sup (schwartzSeminormFamily ℂ (V × V') ℂ)) f :=
    (slice_sup_le f x' s₂ k).trans (sup_apply_mono Finset.subset_union_right f)
  have hp : ‖(y, x')‖ ^ k ≤ ‖y‖ ^ k + ‖x'‖ ^ k := by
    rw [Prod.norm_mk]
    rcases le_total ‖y‖ ‖x'‖ with hl | hl
    · rw [max_eq_right hl]; linarith [pow_nonneg (norm_nonneg y) k]
    · rw [max_eq_left hl]; linarith [pow_nonneg (norm_nonneg x') k]
  set S := ((t₁ ∪ t₂).sup (schwartzSeminormFamily ℂ (V × V') ℂ)) f
  change ‖(y, x')‖ ^ k * ‖T h y‖ ≤ (C₁ + C₂) * S
  calc ‖(y, x')‖ ^ k * ‖T h y‖ ≤ (‖y‖ ^ k + ‖x'‖ ^ k) * ‖T h y‖ := by gcongr
    _ = ‖y‖ ^ k * ‖T h y‖ + ‖x'‖ ^ k * ‖T h y‖ := by ring
    _ ≤ C₁ * (s₁.sup (schwartzSeminormFamily ℂ V ℂ)) h +
          ‖x'‖ ^ k * (C₂ * (s₂.sup (schwartzSeminormFamily ℂ V ℂ)) h) := by gcongr
    _ = C₁ * (s₁.sup (schwartzSeminormFamily ℂ V ℂ)) h +
          C₂ * (‖x'‖ ^ k * (s₂.sup (schwartzSeminormFamily ℂ V ℂ)) h) := by ring
    _ ≤ C₁ * S + C₂ * S := by gcongr
    _ = (C₁ + C₂) * S := by ring

variable [FiniteDimensional ℝ V']

/- English proof (translation)
Introduce `p` and use `(GlobalTheory.T.has_fderiv_at_schwartz_operator_first T f p.1 p.2).differentiableAt`.
-/
theorem differentiable_opFst (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ)) :
    Differentiable ℝ (opFst T f) := fun p => (GlobalTheory.T.has_fderiv_at_schwartz_operator_first T f p.1 p.2).differentiableAt

variable (W V' E) in

def compFst : (W →L[ℝ] E) →L[ℝ] (W × V' →L[ℝ] E) :=
  (ContinuousLinearMap.compL ℝ (W × V') W E).flip (ContinuousLinearMap.fst ℝ W V')

variable (W V' E) in

def coordSnd (i : Fin (Module.finrank ℝ V')) : E →L[ℝ] (W × V' →L[ℝ] E) :=
  ContinuousLinearMap.smulRightL ℝ (W × V') E
    ((LinearMap.toContinuousLinearMap ((Module.finBasis ℝ V').coord i)).comp (ContinuousLinearMap.snd ℝ W V'))

/- English proof (translation)
Use function extensionality and compare the values at `p`. Rewrite using `[(GlobalTheory.T.has_fderiv_at_schwartz_operator_first T f p.1 p.2).fderiv]`. Use `ContinuousLinearMap.ext fun q => ?_` and prove the remaining obligations. Establish `hv : q.2 = ∑ i, (Module.finBasis ℝ V').repr q.2 i • Module.finBasis ℝ V' i` using `((Module.finBasis ℝ V').sum_repr q.2).symm`. Simplify using `[compFst, coordSnd]`.

Use `congr 1`. Use `conv_lhs => rw [hv]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, dSndCLM_apply]`.
-/
theorem fderiv_opFst (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ)) :
    fderiv ℝ (opFst T f) = fun p =>
      compFst W V' E (opFst ((SchwartzMap.fderivCLM ℂ W E).comp T) f p) +
        ∑ i, coordSnd W V' E i (opFst T (lineSnd (Module.finBasis ℝ V' i) f) p) := by
  funext p
  rw [(GlobalTheory.T.has_fderiv_at_schwartz_operator_first T f p.1 p.2).fderiv]
  refine ContinuousLinearMap.ext fun q => ?_
  have hv : q.2 = ∑ i, (Module.finBasis ℝ V').repr q.2 i • Module.finBasis ℝ V' i :=
    ((Module.finBasis ℝ V').sum_repr q.2).symm
  simp [compFst, coordSnd]
  congr 1
  conv_lhs => rw [hv]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, dSndCLM_apply]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `E' _ _ T`. Use `⟨fun f => contDiff_zero.2 (differentiable_opFst T f).continuous, fun k => ?_⟩` and prove the remaining obligations. Take `⟨s, C, hC, h⟩` from `base_bound (V' := V') T k`.

Conclude with `⟨s, C, hC, fun f p => by rw [norm_iteratedFDeriv_zero]; exact h f p⟩`. Consider the case `succ n ih`. Introduce `E' _ _ T`. Use `set b := Module.finBasis ℝ V'`. Use `set T₁ := (SchwartzMap.fderivCLM ℂ W E').comp T`.

Take `⟨c₁, b₁⟩` from `ih _ T₁`. Take `⟨c₂, b₂⟩` from `ih E' T`. Establish `hA : ∀ f : 𝓢(V × V', ℂ), ContDiff ℝ n (fun p => compFst W V' E' (opFst T₁ f p))` using `fun f => (compFst W V' E').contDiff.comp (c₁ f)`. Establish `hB : ∀ (f : 𝓢(V × V', ℂ)) (i : Fin (Module.finrank ℝ V')), ContDiff ℝ n (fun p => coordSnd W V' E' i (opFst T (lineSnd (b i) f) p))` using `fun f i => (coordSnd W V' E' i).contDiff.comp (c₂ _)`. Establish `hG : ∀ f : 𝓢(V × V', ℂ), ContDiff ℝ n (fderiv ℝ (opFst T f))` using `fun f => by`.

Rewrite using `[fderiv_opFst]`. Conclude with `(hA f).add (ContDiff.sum fun i _ => hB f i)`. Use `⟨fun f => ?_, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.cast_succ, contDiff_succ_iff_fderiv]`. Conclude with `⟨differentiable_opFst T f, by simp, hG f⟩`.

Take `⟨s₁, C₁, hC₁, h₁⟩` from `b₁ k`. Take `⟨s₂, C₂, hC₂, h₂⟩` from `b₂ k`. Use `choose t Ct hCt ht using fun i : Fin (Module.finrank ℝ V') => exists_sup_bound (lineSnd (b i) : 𝓢(V × V', ℂ) →L[ℂ] 𝓢(V × V', ℂ)) s₂`. Use `⟨s₁ ∪ Finset.univ.biUnion t, ‖compFst W V' E'‖ * C₁ + ∑ i, ‖coordSnd W V' E' i‖ * (C₂ * Ct i), ?_, fun f p => ?_⟩` and prove the remaining obligations. Conclude with `add_nonneg (mul_nonneg (norm_nonneg _) hC₁) (Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (mul_nonneg hC₂ (hCt i)))`.

Use `set S := ((s₁ ∪ Finset.univ.biUnion t).sup (schwartzSeminormFamily ℂ (V × V') ℂ)) f`. Rewrite using `[← norm_iteratedFDeriv_fderiv, fderiv_opFst]`. Establish `e : iteratedFDeriv ℝ n (fun p => compFst W V' E' (opFst T₁ f p) + ∑ i, coordSnd W V' E' i (opFst T (lineSnd (b i) f) p)) p = iteratedFDeriv ℝ n (fun p => compFst W V' E' (opFst T₁ f p)) p + ∑ i, iteratedFDeriv ℝ n (fun p => coordSnd W V' E' i (opFst T (lineSnd (b i) f) p)) p`. Rewrite using `[show (fun p => compFst W V' E' (opFst T₁ f p) + ∑ i, coordSnd W V' E' i (opFst T (lineSnd (b i) f) p)) = (fun p => compFst W V' E' (opFst T₁ f p)) + (fun p => ∑ i, coordSnd W V' E' i (opFst T (lineSnd (b i) f) p)) from rfl]`. Rewrite using `[iteratedFDeriv_add_apply (f := fun p => compFst W V' E' (opFst T₁ f p)) (g := fun p => ∑ i, coordSnd W V' E' i (opFst T (lineSnd (b i) f) p)) (hA f).contDiffAt (ContDiff.sum fun i _ => hB f i).contDiffAt, iteratedFDeriv_fun_sum_apply fun i _ => (hB f i).contDiffAt]`.

Rewrite using `[e]`. Establish `kA : ‖p‖ ^ k * ‖iteratedFDeriv ℝ n (fun p => compFst W V' E' (opFst T₁ f p)) p‖ ≤ ‖compFst W V' E'‖ * C₁ * S`. Establish `a` using `(compFst W V' E').norm_iteratedFDeriv_comp_left (c₁ f).contDiffAt (x := p) le_rfl`. Establish `a2` using `h₁ f p`. Establish `a3` using `sup_apply_mono (Finset.subset_union_left (s₁ := s₁) (s₂ := Finset.univ.biUnion t)) f`.

Combine the equalities or inequalities in the displayed calculation. Establish `kB : ∀ i, ‖p‖ ^ k * ‖iteratedFDeriv ℝ n (fun p => coordSnd W V' E' i (opFst T (lineSnd (b i) f) p)) p‖ ≤ ‖coordSnd W V' E' i‖ * (C₂ * Ct i) * S`. Introduce `i`. Establish `a` using `(coordSnd W V' E' i).norm_iteratedFDeriv_comp_left (c₂ (lineSnd (b i) f)).contDiffAt (x := p) le_rfl`. Establish `a2` using `h₂ (lineSnd (b i) f) p`.

Establish `a3` using `ht i f`. Establish `a4 : ((t i).sup (schwartzSeminormFamily ℂ (V × V') ℂ)) f ≤ S` using `sup_apply_mono (Finset.subset_union_right.trans' (Finset.subset_biUnion_of_mem t (Finset.mem_univ i))) f`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Finset.mul_sum, ← mul_add]`.

Use `gcongr`. Conclude with `(norm_add_le _ _).trans (by gcongr; exact norm_sum_le _ _)`. Use `_ ≤ ‖compFst W V' E'‖ * C₁ * S + ∑ i, ‖coordSnd W V' E' i‖ * (C₂ * Ct i) * S := by`. Conclude with `add_le_add kA (Finset.sum_le_sum fun i _ => kB i)`. Use `_ = _ := by rw [← Finset.sum_mul, ← add_mul]`.
-/
theorem finiteRing_sq_sub_mul_sq_eq_of_card (n : ℕ) : ∀ (E' : Type) [NormedAddCommGroup E'] [NormedSpace ℂ E']
    (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E')),
    (∀ f : 𝓢(V × V', ℂ), ContDiff ℝ n (opFst T f)) ∧
    ∀ k : ℕ, ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (f : 𝓢(V × V', ℂ)) (p : W × V'),
      ‖p‖ ^ k * ‖iteratedFDeriv ℝ n (opFst T f) p‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ (V × V') ℂ)) f := by
  induction n with
  | zero =>
    intro E' _ _ T
    refine ⟨fun f => contDiff_zero.2 (differentiable_opFst T f).continuous, fun k => ?_⟩
    obtain ⟨s, C, hC, h⟩ := base_bound (V' := V') T k
    exact ⟨s, C, hC, fun f p => by rw [norm_iteratedFDeriv_zero]; exact h f p⟩
  | succ n ih =>
    intro E' _ _ T
    set b := Module.finBasis ℝ V'
    set T₁ := (SchwartzMap.fderivCLM ℂ W E').comp T
    obtain ⟨c₁, b₁⟩ := ih _ T₁
    obtain ⟨c₂, b₂⟩ := ih E' T
    have hA : ∀ f : 𝓢(V × V', ℂ), ContDiff ℝ n (fun p => compFst W V' E' (opFst T₁ f p)) :=
      fun f => (compFst W V' E').contDiff.comp (c₁ f)
    have hB : ∀ (f : 𝓢(V × V', ℂ)) (i : Fin (Module.finrank ℝ V')),
        ContDiff ℝ n (fun p => coordSnd W V' E' i (opFst T (lineSnd (b i) f) p)) :=
      fun f i => (coordSnd W V' E' i).contDiff.comp (c₂ _)
    have hG : ∀ f : 𝓢(V × V', ℂ), ContDiff ℝ n (fderiv ℝ (opFst T f)) := fun f => by
      rw [fderiv_opFst]
      exact (hA f).add (ContDiff.sum fun i _ => hB f i)
    refine ⟨fun f => ?_, fun k => ?_⟩
    · rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
      exact ⟨differentiable_opFst T f, by simp, hG f⟩
    · obtain ⟨s₁, C₁, hC₁, h₁⟩ := b₁ k
      obtain ⟨s₂, C₂, hC₂, h₂⟩ := b₂ k
      choose t Ct hCt ht using fun i : Fin (Module.finrank ℝ V') =>
        exists_sup_bound (lineSnd (b i) : 𝓢(V × V', ℂ) →L[ℂ] 𝓢(V × V', ℂ)) s₂
      refine ⟨s₁ ∪ Finset.univ.biUnion t,
        ‖compFst W V' E'‖ * C₁ + ∑ i, ‖coordSnd W V' E' i‖ * (C₂ * Ct i), ?_, fun f p => ?_⟩
      · exact add_nonneg (mul_nonneg (norm_nonneg _) hC₁)
          (Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (mul_nonneg hC₂ (hCt i)))
      set S := ((s₁ ∪ Finset.univ.biUnion t).sup (schwartzSeminormFamily ℂ (V × V') ℂ)) f
      rw [← norm_iteratedFDeriv_fderiv, fderiv_opFst]
      have e : iteratedFDeriv ℝ n (fun p => compFst W V' E' (opFst T₁ f p) +
            ∑ i, coordSnd W V' E' i (opFst T (lineSnd (b i) f) p)) p =
          iteratedFDeriv ℝ n (fun p => compFst W V' E' (opFst T₁ f p)) p +
            ∑ i, iteratedFDeriv ℝ n (fun p => coordSnd W V' E' i (opFst T (lineSnd (b i) f) p)) p := by
        rw [show (fun p => compFst W V' E' (opFst T₁ f p) +
            ∑ i, coordSnd W V' E' i (opFst T (lineSnd (b i) f) p)) =
            (fun p => compFst W V' E' (opFst T₁ f p)) +
            (fun p => ∑ i, coordSnd W V' E' i (opFst T (lineSnd (b i) f) p)) from rfl]
        rw [iteratedFDeriv_add_apply (f := fun p => compFst W V' E' (opFst T₁ f p))
          (g := fun p => ∑ i, coordSnd W V' E' i (opFst T (lineSnd (b i) f) p))
          (hA f).contDiffAt (ContDiff.sum fun i _ => hB f i).contDiffAt,
          iteratedFDeriv_fun_sum_apply fun i _ => (hB f i).contDiffAt]
      rw [e]
      have kA : ‖p‖ ^ k * ‖iteratedFDeriv ℝ n (fun p => compFst W V' E' (opFst T₁ f p)) p‖ ≤
          ‖compFst W V' E'‖ * C₁ * S := by
        have a := (compFst W V' E').norm_iteratedFDeriv_comp_left (c₁ f).contDiffAt (x := p) le_rfl
        have a2 := h₁ f p
        have a3 := sup_apply_mono (Finset.subset_union_left (s₁ := s₁) (s₂ := Finset.univ.biUnion t)) f
        calc _ ≤ ‖p‖ ^ k * (‖compFst W V' E'‖ * ‖iteratedFDeriv ℝ n (opFst T₁ f) p‖) := by
              gcongr; exact a
          _ = ‖compFst W V' E'‖ * (‖p‖ ^ k * ‖iteratedFDeriv ℝ n (opFst T₁ f) p‖) := by ring
          _ ≤ ‖compFst W V' E'‖ * (C₁ * S) :=
              mul_le_mul_of_nonneg_left (a2.trans (mul_le_mul_of_nonneg_left a3 hC₁)) (norm_nonneg _)
          _ = _ := by ring
      have kB : ∀ i, ‖p‖ ^ k *
          ‖iteratedFDeriv ℝ n (fun p => coordSnd W V' E' i (opFst T (lineSnd (b i) f) p)) p‖ ≤
          ‖coordSnd W V' E' i‖ * (C₂ * Ct i) * S := by
        intro i
        have a := (coordSnd W V' E' i).norm_iteratedFDeriv_comp_left (c₂ (lineSnd (b i) f)).contDiffAt
          (x := p) le_rfl
        have a2 := h₂ (lineSnd (b i) f) p
        have a3 := ht i f
        have a4 : ((t i).sup (schwartzSeminormFamily ℂ (V × V') ℂ)) f ≤ S :=
          sup_apply_mono (Finset.subset_union_right.trans' (Finset.subset_biUnion_of_mem t (Finset.mem_univ i))) f
        calc _ ≤ ‖p‖ ^ k * (‖coordSnd W V' E' i‖ *
                ‖iteratedFDeriv ℝ n (opFst T (lineSnd (b i) f)) p‖) := by
              gcongr; exact a
          _ = ‖coordSnd W V' E' i‖ * (‖p‖ ^ k * ‖iteratedFDeriv ℝ n (opFst T (lineSnd (b i) f)) p‖) := by ring
          _ ≤ ‖coordSnd W V' E' i‖ * (C₂ * (Ct i * S)) :=
              mul_le_mul_of_nonneg_left (a2.trans (mul_le_mul_of_nonneg_left
                (a3.trans (mul_le_mul_of_nonneg_left a4 (hCt i))) hC₂)) (norm_nonneg _)
          _ = _ := by ring
      calc ‖p‖ ^ k * ‖iteratedFDeriv ℝ n (fun p => compFst W V' E' (opFst T₁ f p)) p +
            ∑ i, iteratedFDeriv ℝ n (fun p => coordSnd W V' E' i (opFst T (lineSnd (b i) f) p)) p‖
          ≤ ‖p‖ ^ k * ‖iteratedFDeriv ℝ n (fun p => compFst W V' E' (opFst T₁ f p)) p‖ +
            ∑ i, ‖p‖ ^ k *
              ‖iteratedFDeriv ℝ n (fun p => coordSnd W V' E' i (opFst T (lineSnd (b i) f) p)) p‖ := by
            rw [← Finset.mul_sum, ← mul_add]
            gcongr
            exact (norm_add_le _ _).trans (by gcongr; exact norm_sum_le _ _)
        _ ≤ ‖compFst W V' E'‖ * C₁ * S + ∑ i, ‖coordSnd W V' E' i‖ * (C₂ * Ct i) * S := by
            exact add_le_add kA (Finset.sum_le_sum fun i _ => kB i)
        _ = _ := by rw [← Finset.sum_mul, ← add_mul]

def tensorId (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, ℂ)) : 𝓢(V × V', ℂ) →L[ℂ] 𝓢(W × V', ℂ) :=
  SchwartzMap.mkCLM (σ := RingHom.id ℂ) (fun f p => opFst T f p)
    (fun f g p => by simp [opFst, map_add])
    (fun a f p => by simp [opFst, map_smul])
    (fun f => contDiff_infty.2 fun n => (finiteRing_sq_sub_mul_sq_eq_of_card n ℂ T).1 f)
    (fun m => (finiteRing_sq_sub_mul_sq_eq_of_card m.2 ℂ T).2 m.1)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tensorId_apply (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, ℂ)) (f : 𝓢(V × V', ℂ)) (y : W) (x' : V') :
    tensorId T f (y, x') = T (sliceCLM x' f) y := rfl

/- English proof (translation)
Introduce `V W V' _ _ _ _ _ _ _ _ _ T`. Use `⟨tensorId T, fun f x' h hh y => ?_⟩` and prove the remaining obligations. Establish `e : sliceCLM x' f = h`. Use extensionality with `x`. Rewrite using `[sliceCLM_apply, hh]`.

Rewrite using `[tensorId_apply, e]`.
-/
theorem exists_tensorId : ∀ {V W V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [NormedAddCommGroup V']
    [NormedSpace ℝ V'] [FiniteDimensional ℝ V'] (T : SchwartzMap V ℂ →L[ℂ] SchwartzMap W ℂ),
    ∃ P : SchwartzMap (V × V') ℂ →L[ℂ] SchwartzMap (W × V') ℂ, ∀ (f : SchwartzMap (V × V') ℂ) (x' : V')
      (h : SchwartzMap V ℂ), (∀ x, h x = f (x, x')) → ∀ y, P f (y, x') = T h y := by
  intro V W V' _ _ _ _ _ _ _ _ _ T
  refine ⟨tensorId T, fun f x' h hh y => ?_⟩
  have e : sliceCLM x' f = h := by
    ext x
    rw [sliceCLM_apply, hh]
  rw [tensorId_apply, e]

end GlobalTheory.SchwartzFstOp
