import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

variable {K : Type}

/- English proof (translation)
Simplify `Filter.tendsto_atTop_add_const_right Filter.atTop (-s) Filter.tendsto_id` using `[sub_eq_add_neg]`.
-/
theorem tendsto_sub_const_atTop (s : K → ℤ) :
    Filter.Tendsto (fun m : K → ℤ => m - s) Filter.atTop Filter.atTop := by
  simpa [sub_eq_add_neg] using
    Filter.tendsto_atTop_add_const_right Filter.atTop (-s) Filter.tendsto_id

/- English proof (translation)
Establish `h' : ∀ᶠ m in Filter.atTop, F (m - b) = G (m - b)` using `(tendsto_sub_const_atTop b).eventually h`. Use `filter_upwards [h, h'] with m hm hm'`. Simplify using `only [diffStep, hm, hm']`.
-/
theorem diffStep_eventuallyEq (b : K → ℤ) {F G : (K → ℤ) → ℤ} (h : F =ᶠ[Filter.atTop] G) :
    diffStep b F =ᶠ[Filter.atTop] diffStep b G := by
  have h' : ∀ᶠ m in Filter.atTop, F (m - b) = G (m - b) := (tendsto_sub_const_atTop b).eventually h
  filter_upwards [h, h'] with m hm hm'
  simp only [diffStep, hm, hm']

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simpa using h`. Consider the case `cons b l ih`. Simplify using `only [List.foldr_cons]`. Conclude with `diffStep_eventuallyEq b ih`.
-/
theorem foldr_diffStep_eventuallyEq (l : List (K → ℤ)) {F G : (K → ℤ) → ℤ}
    (h : F =ᶠ[Filter.atTop] G) :
    l.foldr diffStep F =ᶠ[Filter.atTop] l.foldr diffStep G := by
  induction l with
  | nil => simpa using h
  | cons b l ih =>
    simp only [List.foldr_cons]
    exact diffStep_eventuallyEq b ih

/- English proof (translation)
Introduce `K n f g c s`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `hf hg bs filter_upwards [hf bs, hg bs] with m hm hm'`. Rewrite using `[(h1 K n bs f g c s 0).1, Pi.add_apply, hm, hm', add_zero]`. Introduce `hf bs filter_upwards [hf bs] with m hm`.

Rewrite using `[(h1 K n bs f g c s 0).2.1, Pi.smul_apply, hm, smul_zero]`. Introduce `hf bs`. Establish `h'` using `(tendsto_sub_const_atTop s).eventually (hf bs)`. Use `filter_upwards [h'] with m hm`. Rewrite using `[(h1 K n bs f g c s 0).2.2.1]`.

Conclude with `hm`. Introduce `hf bs`. Establish `hz : ∀ᶠ m in Filter.atTop, mixedDiff (fun i : Fin n => bs i.succ) f m = 0` using `hf (fun i => bs i.succ)`. Establish `hz'` using `(tendsto_sub_const_atTop (bs 0)).eventually hz`. Use `filter_upwards [hz, hz'] with m hm hm'`.

Establish `e : mixedDiff bs f = diffStep (bs 0) (mixedDiff (fun i : Fin n => bs i.succ) f)`. Unfold `mixedDiff`. Rewrite using `[List.ofFn_succ, List.foldr_cons]`. Rewrite using `[e]`. Simplify using `only [diffStep, hm, hm', sub_zero]`.

Introduce `hfg hf bs`. Establish `e : mixedDiff bs f =ᶠ[Filter.atTop] mixedDiff bs g` using `foldr_diffStep_eventuallyEq (List.ofFn bs) hfg`. Use `filter_upwards [e, hf bs] with m hm hm'`. Rewrite using `[← hm, hm']`.
-/
theorem DegLTClosure.proof (h1 : MixedDiffLinear.Statement) : DegLTClosure.Statement := by
  intro K n f g c s
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hf hg bs
    filter_upwards [hf bs, hg bs] with m hm hm'
    rw [(h1 K n bs f g c s 0).1, Pi.add_apply, hm, hm', add_zero]
  · intro hf bs
    filter_upwards [hf bs] with m hm
    rw [(h1 K n bs f g c s 0).2.1, Pi.smul_apply, hm, smul_zero]
  · intro hf bs
    have h' := (tendsto_sub_const_atTop s).eventually (hf bs)
    filter_upwards [h'] with m hm
    rw [(h1 K n bs f g c s 0).2.2.1]
    exact hm
  · intro hf bs
    have hz : ∀ᶠ m in Filter.atTop, mixedDiff (fun i : Fin n => bs i.succ) f m = 0 :=
      hf (fun i => bs i.succ)
    have hz' := (tendsto_sub_const_atTop (bs 0)).eventually hz
    filter_upwards [hz, hz'] with m hm hm'
    have e : mixedDiff bs f = diffStep (bs 0) (mixedDiff (fun i : Fin n => bs i.succ) f) := by
      unfold mixedDiff
      rw [List.ofFn_succ, List.foldr_cons]
    rw [e]
    simp only [diffStep, hm, hm', sub_zero]
  · intro hfg hf bs
    have e : mixedDiff bs f =ᶠ[Filter.atTop] mixedDiff bs g :=
      foldr_diffStep_eventuallyEq (List.ofFn bs) hfg
    filter_upwards [e, hf bs] with m hm hm'
    rw [← hm, hm']

end

end GroundTheory.Heights₂.Heights.NumbersDVR
