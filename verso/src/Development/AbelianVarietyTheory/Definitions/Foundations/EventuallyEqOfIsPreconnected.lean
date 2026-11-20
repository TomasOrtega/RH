import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentConstEqOfTendsto

noncomputable section

namespace GlobalTheory.Cont

open Filter Topology Set GlobalTheory.ThetaInner

def rightOf (σ : ℝ) : Set ℂ := {s | σ < s.re}

def IsRightDomain (U : Set ℂ) : Prop := (∃ σ, rightOf σ ⊆ U) ∧ ∀ s ∈ U, ∀ t : ℝ, 0 ≤ t → s + t ∈ U

def EqRight (H h : ℂ → ℂ) : Prop := ∃ σ, EqOn H h (rightOf σ)

variable {σ τ : ℝ} {U U' : Set ℂ} {h h' H H' : ℂ → ℂ} {s s₀ c c' : ℂ} {n : ℤ} {k : ℕ}

/- English proof (translation)
Conclude with `Iff.rfl`.
-/
@[simp] theorem mem_rightOf : s ∈ rightOf σ ↔ σ < s.re := by exact Iff.rfl

/- English proof (translation)
The claim follows from `isOpen_lt continuous_const Complex.continuous_re`.
-/
theorem isOpen_rightOf (σ : ℝ) : IsOpen (rightOf σ) := isOpen_lt continuous_const Complex.continuous_re

/- English proof (translation)
Introduce `_ hs` and use `lt_of_le_of_lt e hs`.
-/
theorem rightOf_subset (e : σ ≤ τ) : rightOf τ ⊆ rightOf σ := fun _ hs => lt_of_le_of_lt e hs

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨0, subset_univ _⟩, fun _ _ _ _ => mem_univ _⟩`.
-/
theorem isRightDomain_univ : IsRightDomain univ := ⟨⟨0, subset_univ _⟩, fun _ _ _ _ => mem_univ _⟩

/- English proof (translation)
Use `⟨⟨σ, subset_rfl⟩, fun s hs t ht => ?_⟩` and prove the remaining obligations. Simplify using `only [mem_rightOf, Complex.add_re, Complex.ofReal_re] at hs ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem isRightDomain_rightOf (σ : ℝ) : IsRightDomain (rightOf σ) := by
  refine ⟨⟨σ, subset_rfl⟩, fun s hs t ht => ?_⟩
  simp only [mem_rightOf, Complex.add_re, Complex.ofReal_re] at hs ⊢
  linarith

/- English proof (translation)
Use `⟨⟨σ, fun s hs => ?_⟩, fun s hs t ht => ?_⟩` and prove the remaining obligations. Simplify using `only [mem_rightOf] at hs`. Conclude with `le_of_lt hs`. Use `show σ ≤ (s + t).re`. Establish `hs' : σ ≤ s.re` using `hs`.

Simplify using `only [Complex.add_re, Complex.ofReal_re]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem isRightDomain_re_ge (σ : ℝ) : IsRightDomain {s | σ ≤ s.re} := by
  refine ⟨⟨σ, fun s hs => ?_⟩, fun s hs t ht => ?_⟩
  · simp only [mem_rightOf] at hs
    exact le_of_lt hs
  · show σ ≤ (s + t).re
    have hs' : σ ≤ s.re := hs
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith

/- English proof (translation)
Take `⟨⟨σ₁, h₁⟩, a₂⟩` from `a`. Take `⟨⟨σ₂, h₂⟩, b₂⟩` from `b`. Conclude with `⟨⟨max σ₁ σ₂, fun s hs => ⟨h₁ (rightOf_subset (le_max_left _ _) hs), h₂ (rightOf_subset (le_max_right _ _) hs)⟩⟩, fun s hs t ht => ⟨a₂ s hs.1 t ht, b₂ s hs.2 t ht⟩⟩`.
-/
theorem IsRightDomain.inter (a : IsRightDomain U) (b : IsRightDomain U') : IsRightDomain (U ∩ U') := by
  obtain ⟨⟨σ₁, h₁⟩, a₂⟩ := a
  obtain ⟨⟨σ₂, h₂⟩, b₂⟩ := b
  exact ⟨⟨max σ₁ σ₂, fun s hs => ⟨h₁ (rightOf_subset (le_max_left _ _) hs),
    h₂ (rightOf_subset (le_max_right _ _) hs)⟩⟩, fun s hs t ht => ⟨a₂ s hs.1 t ht, b₂ s hs.2 t ht⟩⟩

/- English proof (translation)
Take `⟨⟨σ₁, h₁⟩, a₂⟩` from `a`. Use `⟨⟨σ₁ - z.re, fun s hs => ?_⟩, fun s hs t ht => ?_⟩` and prove the remaining obligations. Use `show s + z ∈ U`. Apply `h₁` to reduce the goal to its premises. Simplify using `only [mem_rightOf, Complex.add_re] at hs ⊢`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `show s + t + z ∈ U`. Use `a₂ _ hs t ht` as an intermediate fact. Rewrite `this` using `[add_right_comm]`. Then use the resulting hypothesis.
-/
theorem IsRightDomain.preimage_add (a : IsRightDomain U) (z : ℂ) : IsRightDomain ((· + z) ⁻¹' U) := by
  obtain ⟨⟨σ₁, h₁⟩, a₂⟩ := a
  refine ⟨⟨σ₁ - z.re, fun s hs => ?_⟩, fun s hs t ht => ?_⟩
  · show s + z ∈ U
    apply h₁
    simp only [mem_rightOf, Complex.add_re] at hs ⊢
    linarith
  · show s + t + z ∈ U
    have := a₂ _ hs t ht
    rwa [add_right_comm] at this

/- English proof (translation)
Take `⟨⟨σ, hσ⟩, a₂⟩` from `a`. Establish `hconv : IsPreconnected (rightOf σ)` using `(convex_halfSpace_re_gt σ).isPreconnected`. Use `isPreconnected_of_forall ((σ + 1 : ℝ) : ℂ) fun y hy => ?_` and prove the remaining obligations. Establish `hray : IsPreconnected ((fun t : ℝ => y + t) '' Ici 0)` using `isPreconnected_Ici.image _ (by fun_prop : Continuous fun t : ℝ => y + (t : ℂ)).continuousOn`. Establish `hT : (0 : ℝ) ≤ |σ - y.re| + 1` using `by positivity`.

Establish `hmem : y + ((|σ - y.re| + 1 : ℝ) : ℂ) ∈ rightOf σ`. Simplify using `only [mem_rightOf, Complex.add_re, Complex.ofReal_re]`. Use `le_abs_self (σ - y.re)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨(fun t : ℝ => y + t) '' Ici 0 ∪ rightOf σ, union_subset ?_ hσ, Or.inr ?_, Or.inl ⟨0, mem_Ici.mpr le_rfl, by simp⟩, IsPreconnected.union _ ⟨_, hT, rfl⟩ hmem hray hconv⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨t, ht, rfl⟩`. Conclude with `a₂ y hy t ht`. Simplify using `only [mem_rightOf, Complex.ofReal_re]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem IsRightDomain.isPreconnected (a : IsRightDomain U) : IsPreconnected U := by
  obtain ⟨⟨σ, hσ⟩, a₂⟩ := a
  have hconv : IsPreconnected (rightOf σ) := (convex_halfSpace_re_gt σ).isPreconnected
  refine isPreconnected_of_forall ((σ + 1 : ℝ) : ℂ) fun y hy => ?_
  have hray : IsPreconnected ((fun t : ℝ => y + t) '' Ici 0) :=
    isPreconnected_Ici.image _ (by fun_prop : Continuous fun t : ℝ => y + (t : ℂ)).continuousOn
  have hT : (0 : ℝ) ≤ |σ - y.re| + 1 := by positivity
  have hmem : y + ((|σ - y.re| + 1 : ℝ) : ℂ) ∈ rightOf σ := by
    simp only [mem_rightOf, Complex.add_re, Complex.ofReal_re]
    have := le_abs_self (σ - y.re)
    linarith
  refine ⟨(fun t : ℝ => y + t) '' Ici 0 ∪ rightOf σ, union_subset ?_ hσ, Or.inr ?_,
    Or.inl ⟨0, mem_Ici.mpr le_rfl, by simp⟩, IsPreconnected.union _ ⟨_, hT, rfl⟩ hmem hray hconv⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact a₂ y hy t ht
  · simp only [mem_rightOf, Complex.ofReal_re]
    linarith

namespace EqRight

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, fun _ _ => rfl⟩`.
-/
@[refl] theorem refl (h : ℂ → ℂ) : EqRight h h := ⟨0, fun _ _ => rfl⟩

/- English proof (translation)
Take `⟨σ, e⟩` from `a`. Conclude with `⟨σ, e.symm⟩`.
-/
theorem symm (a : EqRight H h) : EqRight h H := by
  obtain ⟨σ, e⟩ := a
  exact ⟨σ, e.symm⟩

/- English proof (translation)
Take `⟨σ₁, e₁⟩` from `a`. Take `⟨σ₂, e₂⟩` from `b`. Use `⟨max σ₁ σ₂, fun s hs => ?_⟩` and prove the remaining obligations. Establish `h1` using `e₁ (rightOf_subset (le_max_left _ _) hs)`. Establish `h2` using `e₂ (rightOf_subset (le_max_right _ _) hs)`.

Simplify using `only [h1, h2]`.
-/
theorem map₂ (f : ℂ → ℂ → ℂ) (a : EqRight H h) (b : EqRight H' h') :
    EqRight (fun s => f (H s) (H' s)) fun s => f (h s) (h' s) := by
  obtain ⟨σ₁, e₁⟩ := a
  obtain ⟨σ₂, e₂⟩ := b
  refine ⟨max σ₁ σ₂, fun s hs => ?_⟩
  have h1 := e₁ (rightOf_subset (le_max_left _ _) hs)
  have h2 := e₂ (rightOf_subset (le_max_right _ _) hs)
  simp only [h1, h2]

/- English proof (translation)
Take `⟨σ₁, e₁⟩` from `a`. Take `⟨σ₂, e₂⟩` from `b`. Conclude with `⟨max σ₁ σ₂, fun s hs => (e₁ (rightOf_subset (le_max_left _ _) hs)).trans (e₂ (rightOf_subset (le_max_right _ _) hs))⟩`.
-/
theorem trans (a : EqRight H h) (b : EqRight h h') : EqRight H h' := by
  obtain ⟨σ₁, e₁⟩ := a
  obtain ⟨σ₂, e₂⟩ := b
  exact ⟨max σ₁ σ₂, fun s hs => (e₁ (rightOf_subset (le_max_left _ _) hs)).trans
    (e₂ (rightOf_subset (le_max_right _ _) hs))⟩

end EqRight

/- English proof (translation)
Take `⟨τ, eτ⟩` from `e`. Establish `hxσ : ((max σ τ + 1 : ℝ) : ℂ) ∈ rightOf σ`. Simplify using `only [mem_rightOf, Complex.ofReal_re]`. Combine the linear relations using `[le_max_left σ τ]`. Establish `hxτ : ((max σ τ + 1 : ℝ) : ℂ) ∈ rightOf τ`.

Simplify using `only [mem_rightOf, Complex.ofReal_re]`. Combine the linear relations using `[le_max_right σ τ]`. Establish `hd : MeromorphicOn (H - H') U` using `a.sub b`. Establish `htop : meromorphicOrderAt (H - H') ((max σ τ + 1 : ℝ) : ℂ) = ⊤`. Rewrite using `[meromorphicOrderAt_eq_top_iff]`.

Apply `nhdsWithin_le_nhds` to reduce the goal to its premises. Use `filter_upwards [(isOpen_rightOf τ).mem_nhds hxτ] with z hz`. Simplify using `[eτ hz]`. Establish `hs' : meromorphicOrderAt (H - H') s = ⊤`. Assume the negation of the conclusion as `hne`.

Conclude with `hd.meromorphicOrderAt_ne_top_of_isPreconnected hU hs (hσ hxσ) hne htop`. Rewrite `hs'` using `[meromorphicOrderAt_eq_top_iff]`. Use `filter_upwards [hs'] with z hz`. Simplify `hz` using `[sub_eq_zero]`.
-/
theorem eventuallyEq_of_isPreconnected (hU : IsPreconnected U) (hσ : rightOf σ ⊆ U) (a : MeromorphicOn H U)
    (b : MeromorphicOn H' U) (e : EqRight H H') (hs : s ∈ U) : H =ᶠ[𝓝[≠] s] H' := by
  obtain ⟨τ, eτ⟩ := e
  have hxσ : ((max σ τ + 1 : ℝ) : ℂ) ∈ rightOf σ := by
    simp only [mem_rightOf, Complex.ofReal_re]
    linarith [le_max_left σ τ]
  have hxτ : ((max σ τ + 1 : ℝ) : ℂ) ∈ rightOf τ := by
    simp only [mem_rightOf, Complex.ofReal_re]
    linarith [le_max_right σ τ]
  have hd : MeromorphicOn (H - H') U := a.sub b
  have htop : meromorphicOrderAt (H - H') ((max σ τ + 1 : ℝ) : ℂ) = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    apply nhdsWithin_le_nhds
    filter_upwards [(isOpen_rightOf τ).mem_nhds hxτ] with z hz
    simp [eτ hz]
  have hs' : meromorphicOrderAt (H - H') s = ⊤ := by
    by_contra hne
    exact hd.meromorphicOrderAt_ne_top_of_isPreconnected hU hs (hσ hxσ) hne htop
  rw [meromorphicOrderAt_eq_top_iff] at hs'
  filter_upwards [hs'] with z hz
  simpa [sub_eq_zero] using hz

def LaurentCoeff (H : ℂ → ℂ) (s₀ : ℂ) (n : ℤ) (c : ℂ) : Prop := LaurentConst (fun s => (s - s₀) ^ (-n) * H s) s₀ c

/- English proof (translation)
Take `⟨p, hp, t⟩` from `a`. Conclude with `⟨p, hp, t.congr' (e.mono fun s hs => by simp only [hs])⟩`.
-/
theorem laurentConst_congr (a : LaurentConst H s₀ c) (e : H =ᶠ[𝓝[≠] s₀] H') : LaurentConst H' s₀ c := by
  obtain ⟨p, hp, t⟩ := a
  exact ⟨p, hp, t.congr' (e.mono fun s hs => by simp only [hs])⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, by simp, by simpa using a⟩`.
-/
theorem laurentConst_of_tendsto (a : Tendsto H (𝓝[≠] s₀) (𝓝 c)) : LaurentConst H s₀ c := ⟨0, by simp, by simpa using a⟩

/- English proof (translation)
Take `⟨p, hp, tp⟩` from `a`. Take `⟨q, hq, tq⟩` from `b`. Use `⟨p + q, by simp [hp, hq], (tp.add tq).congr fun s => ?_⟩` and prove the remaining obligations. Simplify using `only [Polynomial.eval_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem laurentConst_add (a : LaurentConst H s₀ c) (b : LaurentConst H' s₀ c') :
    LaurentConst (fun s => H s + H' s) s₀ (c + c') := by
  obtain ⟨p, hp, tp⟩ := a
  obtain ⟨q, hq, tq⟩ := b
  refine ⟨p + q, by simp [hp, hq], (tp.add tq).congr fun s => ?_⟩
  simp only [Polynomial.eval_add]
  ring

/- English proof (translation)
Take `⟨p, hp, tp⟩` from `a`. Use `⟨Polynomial.C z * p, by simp [hp], (tp.const_mul z).congr fun s => ?_⟩` and prove the remaining obligations. Simplify using `only [Polynomial.eval_mul, Polynomial.eval_C]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem laurentConst_const_mul (z : ℂ) (a : LaurentConst H s₀ c) : LaurentConst (fun s => z * H s) s₀ (z * c) := by
  obtain ⟨p, hp, tp⟩ := a
  refine ⟨Polynomial.C z * p, by simp [hp], (tp.const_mul z).congr fun s => ?_⟩
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  ring

/- English proof (translation)
Take `⟨q, hq, tq⟩` from `b`. Take `⟨p, hp, tp⟩` from `a`. Use `laurentConst_eq_of_tendsto (fun s => H s - q.eval (s - s₀)⁻¹) s₀ c c' ⟨p - q, by simp [hp, hq], tp.congr fun s => ?_⟩ tq` and prove the remaining obligations. Simplify using `only [Polynomial.eval_sub]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem laurentConst_unique (a : LaurentConst H s₀ c) (b : LaurentConst H s₀ c') : c = c' := by
  obtain ⟨q, hq, tq⟩ := b
  obtain ⟨p, hp, tp⟩ := a
  refine laurentConst_eq_of_tendsto (fun s => H s - q.eval (s - s₀)⁻¹) s₀ c c'
    ⟨p - q, by simp [hp, hq], tp.congr fun s => ?_⟩ tq
  simp only [Polynomial.eval_sub]
  ring

/- English proof (translation)
Take `⟨p, hp, tp⟩` from `a`. Use `⟨p + q, by simp [hp, hq], tp.congr fun s => ?_⟩` and prove the remaining obligations. Simplify using `only [Polynomial.eval_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem laurentConst_add_poly_eval_inv {F : ℂ → ℂ} {s₀ c : ℂ} (a : LaurentConst F s₀ c) (q : Polynomial ℂ)
    (hq : q.coeff 0 = 0) : LaurentConst (fun s => F s + q.eval (s - s₀)⁻¹) s₀ c := by
  obtain ⟨p, hp, tp⟩ := a
  refine ⟨p + q, by simp [hp, hq], tp.congr fun s => ?_⟩
  simp only [Polynomial.eval_add]
  ring

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Introduce `g p hp`. Apply `laurentConst_of_tendsto` to reduce the goal to its premises. Establish `hp0 : p.coeff 0 = g s₀` using `hp.coeff_zero 1`.

Rewrite using `[hp0]`. Simplify using `only [pow_zero, div_one]`. Conclude with `hp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds`. Consider the case `succ k ih`. Introduce `g p hp`.

Establish `h1` using `ih hp.has_fpower_series_dslope_fslope`. Rewrite `h1` using `[FormalMultilinearSeries.coeff_fslope]`. Establish `h2` using `laurentConst_add_poly_eval_inv h1 (Polynomial.C (g s₀) * Polynomial.X ^ (k + 1)) (by simp [Polynomial.coeff_X_pow])`. Use `laurentConst_congr h2 ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with s hs`.

Establish `hd : s - s₀ ≠ 0` using `sub_ne_zero.mpr hs`. Rewrite using `[dslope_of_ne _ hs, slope_def_field]`. Simplify using `only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]`. Generalize the expression as in `s - s₀ = d at hd ⊢`. Rewrite using `[inv_pow, pow_succ]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem laurentConst_div_pow (k : ℕ) : ∀ {g : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}, HasFPowerSeriesAt g p s₀ →
    LaurentConst (fun s => g s / (s - s₀) ^ k) s₀ (p.coeff k) := by
  induction k with
  | zero =>
    intro g p hp
    apply laurentConst_of_tendsto
    have hp0 : p.coeff 0 = g s₀ := hp.coeff_zero 1
    rw [hp0]
    simp only [pow_zero, div_one]
    exact hp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  | succ k ih =>
    intro g p hp
    have h1 := ih hp.has_fpower_series_dslope_fslope
    rw [FormalMultilinearSeries.coeff_fslope] at h1
    have h2 := laurentConst_add_poly_eval_inv h1 (Polynomial.C (g s₀) * Polynomial.X ^ (k + 1))
      (by simp [Polynomial.coeff_X_pow])
    refine laurentConst_congr h2 ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hd : s - s₀ ≠ 0 := sub_ne_zero.mpr hs
    rw [dslope_of_ne _ hs, slope_def_field]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    generalize s - s₀ = d at hd ⊢
    rw [inv_pow, pow_succ]
    field_simp
    ring

/- English proof (translation)
Unfold `LaurentCoeff`. Use `laurentConst_congr (laurentConst_div_pow i hg) ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with s hs`. Establish `hd : s - s₀ ≠ 0` using `sub_ne_zero.mpr hs`. Rewrite using `[neg_sub, zpow_sub₀ hd, zpow_natCast, zpow_natCast]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem laurentCoeff_div_pow {g : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} (hg : HasFPowerSeriesAt g p s₀) (i k : ℕ) :
    LaurentCoeff (fun s => g s / (s - s₀) ^ k) s₀ (i - k) (p.coeff i) := by
  unfold LaurentCoeff
  refine laurentConst_congr (laurentConst_div_pow i hg) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hd : s - s₀ ≠ 0 := sub_ne_zero.mpr hs
  rw [neg_sub, zpow_sub₀ hd, zpow_natCast, zpow_natCast]
  field_simp

/- English proof (translation)
Take `⟨n, hn⟩` from `a`. Take `⟨p, hp⟩` from `hn`. Use `⟨_, laurentConst_congr (laurentConst_div_pow n hp) ?_⟩` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with s hs`. Establish `hd : s - s₀ ≠ 0` using `sub_ne_zero.mpr hs`.

Simplify using `only [smul_eq_mul]`. Conclude with `mul_div_cancel_left₀ _ (pow_ne_zero _ hd)`.
-/
theorem exists_laurentConst (a : MeromorphicAt H s₀) : ∃ c, LaurentConst H s₀ c := by
  obtain ⟨n, hn⟩ := a
  obtain ⟨p, hp⟩ := hn
  refine ⟨_, laurentConst_congr (laurentConst_div_pow n hp) ?_⟩
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hd : s - s₀ ≠ 0 := sub_ne_zero.mpr hs
  simp only [smul_eq_mul]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ hd)

/- English proof (translation)
Establish `hm : MeromorphicAt (fun s => (s - s₀) ^ (-n) * H s) s₀` using `((analyticAt_id.sub analyticAt_const).meromorphicAt.zpow (-n)).mul a`. Conclude with `exists_laurentConst hm`.
-/
theorem exists_laurentCoeff (a : MeromorphicAt H s₀) (n : ℤ) : ∃ c, LaurentCoeff H s₀ n c := by
  have hm : MeromorphicAt (fun s => (s - s₀) ^ (-n) * H s) s₀ :=
    ((analyticAt_id.sub analyticAt_const).meromorphicAt.zpow (-n)).mul a
  exact exists_laurentConst hm

/- English proof (translation)
Unfold `LaurentCoeff`. Simplify using `only [neg_zero, zpow_zero, one_mul]`.
-/
@[simp] theorem laurentCoeff_zero : LaurentCoeff H s₀ 0 c ↔ LaurentConst H s₀ c := by
  unfold LaurentCoeff
  simp only [neg_zero, zpow_zero, one_mul]

/- English proof (translation)
The claim follows from `laurentConst_congr a (e.mono fun s hs => by simp only [hs])`.
-/
theorem LaurentCoeff.congr (a : LaurentCoeff H s₀ n c) (e : H =ᶠ[𝓝[≠] s₀] H') : LaurentCoeff H' s₀ n c := laurentConst_congr a (e.mono fun s hs => by simp only [hs])

def IsMerExt (h : ℂ → ℂ) (U : Set ℂ) (H : ℂ → ℂ) : Prop := IsRightDomain U ∧ MeromorphicOn H U ∧ EqRight H h

def IsHolExt (h : ℂ → ℂ) (U : Set ℂ) (H : ℂ → ℂ) : Prop := IsRightDomain U ∧ AnalyticOnNhd ℂ H U ∧ EqRight H h

def IsExtAt (h : ℂ → ℂ) (s₀ : ℂ) (H : ℂ → ℂ) : Prop := ∃ U, s₀ ∈ U ∧ IsMerExt h U H

def Continues (h : ℂ → ℂ) : Prop := ∃ H, IsMerExt h univ H

def contDom (h : ℂ → ℂ) : Set ℂ := {s | ∃ H, IsExtAt h s H}

def CoeffAt (h : ℂ → ℂ) (s₀ : ℂ) (n : ℤ) (c : ℂ) : Prop := ∃ H, IsExtAt h s₀ H ∧ LaurentCoeff H s₀ n c

def ValueAt (h : ℂ → ℂ) (s₀ c : ℂ) : Prop := ∃ H, IsExtAt h s₀ H ∧ LaurentConst H s₀ c

def HolValueAt (h : ℂ → ℂ) (s₀ c : ℂ) : Prop := ∃ H, IsExtAt h s₀ H ∧ AnalyticAt ℂ H s₀ ∧ H s₀ = c

abbrev ResidueAt (h : ℂ → ℂ) (s₀ c : ℂ) : Prop := CoeffAt h s₀ (-1) c

def PoleLE (h : ℂ → ℂ) (s₀ : ℂ) (k : ℕ) : Prop := ∃ H, IsExtAt h s₀ H ∧ ((-k : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt H s₀

open Classical in

def laurent (h : ℂ → ℂ) (s₀ : ℂ) (n : ℤ) : ℂ := if e : ∃ c, CoeffAt h s₀ n c then e.choose else 0

def cont (h : ℂ → ℂ) (s : ℂ) : ℂ := laurent h s 0

/- English proof (translation)
Assemble the required witnesses or components as `⟨a.1, a.2.1.meromorphicOn, a.2.2⟩`.
-/
theorem IsHolExt.isMerExt (a : IsHolExt h U H) : IsMerExt h U H := ⟨a.1, a.2.1.meromorphicOn, a.2.2⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨U, hs, a⟩`.
-/
theorem IsMerExt.isExtAt (a : IsMerExt h U H) (hs : s₀ ∈ U) : IsExtAt h s₀ H := ⟨U, hs, a⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨b, fun x hx => a.2.1 x (e hx), a.2.2⟩`.
-/
theorem IsMerExt.mono (a : IsMerExt h U H) (b : IsRightDomain U') (e : U' ⊆ U) : IsMerExt h U' H := ⟨b, fun x hx => a.2.1 x (e hx), a.2.2⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun a => ⟨fun x => a.2.1 x (mem_univ x), a.2.2⟩, fun a => ⟨isRightDomain_univ, fun x _ => a.1 x, a.2⟩⟩`.
-/
theorem isMerExt_univ : IsMerExt h univ H ↔ Meromorphic H ∧ EqRight H h := ⟨fun a => ⟨fun x => a.2.1 x (mem_univ x), a.2.2⟩, fun a => ⟨isRightDomain_univ, fun x _ => a.1 x, a.2⟩⟩

/- English proof (translation)
The claim follows from `GlobalTheory.Cont.eventuallyEq_of_isPreconnected hU hσ (fun x hx => a.2.1 x (e hx)) b (a.2.2.trans e'.symm) hs`.
-/
theorem IsMerExt.eventuallyEq_of_isPreconnected (a : IsMerExt h U H) (e : U' ⊆ U) (hU : IsPreconnected U') (hσ : rightOf σ ⊆ U')
    (b : MeromorphicOn H' U') (e' : EqRight H' h) (hs : s ∈ U') : H =ᶠ[𝓝[≠] s] H' := GlobalTheory.Cont.eventuallyEq_of_isPreconnected hU hσ (fun x hx => a.2.1 x (e hx)) b (a.2.2.trans e'.symm) hs

namespace IsExtAt

/- English proof (translation)
Take `⟨U, hs, hU⟩` from `a`. Conclude with `hU.2.1 s₀ hs`.
-/
theorem meromorphicAt (a : IsExtAt h s₀ H) : MeromorphicAt H s₀ := by
  obtain ⟨U, hs, hU⟩ := a
  exact hU.2.1 s₀ hs

/- English proof (translation)
Take `⟨U, hs, hU⟩` from `a`. Conclude with `hU.2.2`.
-/
theorem eqRight (a : IsExtAt h s₀ H) : EqRight H h := by
  obtain ⟨U, hs, hU⟩ := a
  exact hU.2.2

/- English proof (translation)
Take `⟨U, hs, hU, hm, he⟩` from `a`. Take `⟨U', hs', hU', hm', he'⟩` from `b`. Establish `hI` using `hU.inter hU'`. Take `⟨σ, hσ⟩` from `hI.1`. Conclude with `eventuallyEq_of_isPreconnected hI.isPreconnected hσ (fun x hx => hm x hx.1) (fun x hx => hm' x hx.2) (he.trans he'.symm) ⟨hs, hs'⟩`.
-/
theorem eventuallyEq (a : IsExtAt h s₀ H) (b : IsExtAt h s₀ H') : H =ᶠ[𝓝[≠] s₀] H' := by
  obtain ⟨U, hs, hU, hm, he⟩ := a
  obtain ⟨U', hs', hU', hm', he'⟩ := b
  have hI := hU.inter hU'
  obtain ⟨σ, hσ⟩ := hI.1
  exact eventuallyEq_of_isPreconnected hI.isPreconnected hσ (fun x hx => hm x hx.1) (fun x hx => hm' x hx.2)
    (he.trans he'.symm) ⟨hs, hs'⟩

/- English proof (translation)
Take `⟨U, hs, hU, hm, he⟩` from `a`. Conclude with `⟨U, hs, hU, hm, he.trans e⟩`.
-/
theorem congr (a : IsExtAt h s₀ H) (e : EqRight h h') : IsExtAt h' s₀ H := by
  obtain ⟨U, hs, hU, hm, he⟩ := a
  exact ⟨U, hs, hU, hm, he.trans e⟩

/- English proof (translation)
Take `⟨U, hs, hU, hm, he⟩` from `a`. Take `⟨U', hs', hU', hm', he'⟩` from `b`. Conclude with `⟨U ∩ U', ⟨hs, hs'⟩, hU.inter hU', fun x hx => hf x (hm x hx.1) (hm' x hx.2), he.map₂ f he'⟩`.
-/
theorem map₂ (f : ℂ → ℂ → ℂ) (hf : ∀ s, MeromorphicAt H s → MeromorphicAt H' s → MeromorphicAt (fun s => f (H s) (H' s)) s)
    (a : IsExtAt h s₀ H) (b : IsExtAt h' s₀ H') : IsExtAt (fun s => f (h s) (h' s)) s₀ fun s => f (H s) (H' s) := by
  obtain ⟨U, hs, hU, hm, he⟩ := a
  obtain ⟨U', hs', hU', hm', he'⟩ := b
  exact ⟨U ∩ U', ⟨hs, hs'⟩, hU.inter hU', fun x hx => hf x (hm x hx.1) (hm' x hx.2), he.map₂ f he'⟩

/- English proof (translation)
The claim follows from `map₂ (fun x y => x + y) (fun _ h1 h2 => h1.add h2) a b`.
-/
theorem add (a : IsExtAt h s₀ H) (b : IsExtAt h' s₀ H') : IsExtAt (fun s => h s + h' s) s₀ fun s => H s + H' s := map₂ (fun x y => x + y) (fun _ h1 h2 => h1.add h2) a b

/- English proof (translation)
The claim follows from `map₂ (fun x y => x * y) (fun _ h1 h2 => h1.mul h2) a b`.
-/
theorem mul (a : IsExtAt h s₀ H) (b : IsExtAt h' s₀ H') : IsExtAt (fun s => h s * h' s) s₀ fun s => H s * H' s := map₂ (fun x y => x * y) (fun _ h1 h2 => h1.mul h2) a b

/- English proof (translation)
The claim follows from `map₂ (fun x y => x / y) (fun _ h1 h2 => h1.div h2) a b`.
-/
theorem div (a : IsExtAt h s₀ H) (b : IsExtAt h' s₀ H') : IsExtAt (fun s => h s / h' s) s₀ fun s => H s / H' s := map₂ (fun x y => x / y) (fun _ h1 h2 => h1.div h2) a b

/- English proof (translation)
Take `⟨U, hs, hU, hm, σ, he⟩` from `a`. Use `⟨(· + z) ⁻¹' U, hs, hU.preimage_add z, fun x hx => ?_, σ - z.re, fun x hx => he ?_⟩` and prove the remaining obligations. Conclude with `(hm (x + z) hx).comp_analyticAt (g := fun w => w + z) (by fun_prop)`. Simplify using `only [mem_rightOf, Complex.add_re] at hx ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem comp_add {z : ℂ} (a : IsExtAt h (s₀ + z) H) : IsExtAt (fun s => h (s + z)) s₀ fun s => H (s + z) := by
  obtain ⟨U, hs, hU, hm, σ, he⟩ := a
  refine ⟨(· + z) ⁻¹' U, hs, hU.preimage_add z, fun x hx => ?_, σ - z.re, fun x hx => he ?_⟩
  · exact (hm (x + z) hx).comp_analyticAt (g := fun w => w + z) (by fun_prop)
  · simp only [mem_rightOf, Complex.add_re] at hx ⊢
    linarith

/- English proof (translation)
Take `⟨U, hs, hU, hm, σ, he⟩` from `a`. Establish `hev : ∀ x, Function.update H s₀ c =ᶠ[𝓝[≠] x] H`. Introduce `x`. Distinguish the cases in `hx : x = s₀`. Rewrite using `[hx] filter_upwards [self_mem_nhdsWithin] with y hy`.

Conclude with `Function.update_of_ne hy _ _`. Use `filter_upwards [nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hx)] with y hy`. Conclude with `Function.update_of_ne hy _ _`. Use `⟨U, hs, hU, fun x hx => (hm x hx).congr (hev x).symm, max σ s₀.re, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hne : x ≠ s₀`.

Introduce and unpack `rfl`. Simplify using `[mem_rightOf] at hx`. Rewrite using `[Function.update_of_ne hne]`. Conclude with `he (rightOf_subset (le_max_left _ _) hx)`.
-/
theorem update (a : IsExtAt h s₀ H) (c : ℂ) : IsExtAt h s₀ (Function.update H s₀ c) := by
  obtain ⟨U, hs, hU, hm, σ, he⟩ := a
  have hev : ∀ x, Function.update H s₀ c =ᶠ[𝓝[≠] x] H := by
    intro x
    by_cases hx : x = s₀
    · rw [hx]
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact Function.update_of_ne hy _ _
    · filter_upwards [nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hx)] with y hy
      exact Function.update_of_ne hy _ _
  refine ⟨U, hs, hU, fun x hx => (hm x hx).congr (hev x).symm, max σ s₀.re, fun x hx => ?_⟩
  have hne : x ≠ s₀ := by
    rintro rfl
    simp [mem_rightOf] at hx
  rw [Function.update_of_ne hne]
  exact he (rightOf_subset (le_max_left _ _) hx)

/- English proof (translation)
Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `x hx`. Establish `h1` using `(hx : MeromorphicAt H x).eventually_analyticAt`. Rewrite `h1` using `[eventually_nhdsWithin_iff]`. Use `filter_upwards [h1] with y hy`.

Distinguish the cases in `hyx : y = x`. Rewrite using `[hyx]`. Conclude with `hx`. Conclude with `(hy hyx).meromorphicAt`.
-/
private theorem isOpen_setOf_meromorphicAt (H : ℂ → ℂ) : IsOpen {x | MeromorphicAt H x} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have h1 := (hx : MeromorphicAt H x).eventually_analyticAt
  rw [eventually_nhdsWithin_iff] at h1
  filter_upwards [h1] with y hy
  by_cases hyx : y = x
  · rw [hyx]
    exact hx
  · exact (hy hyx).meromorphicAt

/- English proof (translation)
Rewrite using `[Metric.isOpen_iff]`. Introduce `x hx`. Take `⟨T, hT0, hT⟩ : ∃ T : ℝ, 0 ≤ T ∧ σ + 1 < x.re + T` from `⟨|σ + 1 - x.re| + 1, by positivity, by linarith [le_abs_self (σ + 1 - x.re)]⟩`. Establish `hK : IsCompact ((fun t : ℝ => x + t) '' Icc 0 T)` using `isCompact_Icc.image (by fun_prop : Continuous fun t : ℝ => x + (t : ℂ))`. Establish `hKW : (fun t : ℝ => x + t) '' Icc 0 T ⊆ W`.

Introduce and unpack `_ ⟨t, ht, rfl⟩`. Conclude with `hx t ht.1`. Take `⟨δ, hδ, hδW⟩` from `hK.exists_thickening_subset_open hW hKW`. Use `⟨min δ 1, lt_min hδ one_pos, fun y hy t ht => ?_⟩` and prove the remaining obligations. Rewrite `hy` using `[Metric.mem_ball]`.

Break down `le_or_gt t T with htT | htT` into its components or cases. Apply `hδW` to reduce the goal to its premises. Rewrite using `[Metric.mem_thickening_iff]`. Use `⟨x + t, ⟨t, ⟨ht, htT⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[dist_add_right]`.

Conclude with `lt_of_lt_of_le hy (min_le_left _ _)`. Apply `hσ` to reduce the goal to its premises. Establish `h1 : |(y - x).re| ≤ ‖y - x‖` using `Complex.abs_re_le_norm _`. Rewrite `h1` using `[← dist_eq_norm, Complex.sub_re]`. Establish `h2` using `abs_lt.mp (lt_of_le_of_lt h1 (lt_of_lt_of_le hy (min_le_right _ _)))`.

Simplify using `only [mem_rightOf, Complex.add_re, Complex.ofReal_re]`. Combine the linear relations using `[h2.1]`.
-/
private theorem isOpen_setOf_add_nonneg_real_mem {W : Set ℂ} {σ : ℝ} (hW : IsOpen W) (hσ : rightOf σ ⊆ W) :
    IsOpen {x : ℂ | ∀ t : ℝ, 0 ≤ t → x + t ∈ W} := by
  rw [Metric.isOpen_iff]
  intro x hx
  obtain ⟨T, hT0, hT⟩ : ∃ T : ℝ, 0 ≤ T ∧ σ + 1 < x.re + T :=
    ⟨|σ + 1 - x.re| + 1, by positivity, by linarith [le_abs_self (σ + 1 - x.re)]⟩
  have hK : IsCompact ((fun t : ℝ => x + t) '' Icc 0 T) :=
    isCompact_Icc.image (by fun_prop : Continuous fun t : ℝ => x + (t : ℂ))
  have hKW : (fun t : ℝ => x + t) '' Icc 0 T ⊆ W := by
    rintro _ ⟨t, ht, rfl⟩
    exact hx t ht.1
  obtain ⟨δ, hδ, hδW⟩ := hK.exists_thickening_subset_open hW hKW
  refine ⟨min δ 1, lt_min hδ one_pos, fun y hy t ht => ?_⟩
  rw [Metric.mem_ball] at hy
  rcases le_or_gt t T with htT | htT
  · apply hδW
    rw [Metric.mem_thickening_iff]
    refine ⟨x + t, ⟨t, ⟨ht, htT⟩, rfl⟩, ?_⟩
    rw [dist_add_right]
    exact lt_of_lt_of_le hy (min_le_left _ _)
  · apply hσ
    have h1 : |(y - x).re| ≤ ‖y - x‖ := Complex.abs_re_le_norm _
    rw [← dist_eq_norm, Complex.sub_re] at h1
    have h2 := abs_lt.mp (lt_of_le_of_lt h1 (lt_of_lt_of_le hy (min_le_right _ _)))
    simp only [mem_rightOf, Complex.add_re, Complex.ofReal_re]
    linarith [h2.1]

/- English proof (translation)
Take `⟨U, hs, ⟨⟨σ, hσ⟩, hst⟩, hm, he⟩` from `a`. Establish `hUW : ∀ x ∈ U, ∀ t : ℝ, 0 ≤ t → x + t ∈ {x | MeromorphicAt H x}` using `fun x hx t ht => hm _ (hst x hx t ht)`. Establish `hσW : rightOf σ ⊆ {x | MeromorphicAt H x}` using `fun x hx => hm x (hσ hx)`. Use `⟨{x : ℂ | ∀ t : ℝ, 0 ≤ t → x + t ∈ {x | MeromorphicAt H x}}, isOpen_setOf_add_nonneg_real_mem (isOpen_setOf_meromorphicAt H) hσW, hUW s₀ hs, ⟨⟨σ, fun x hx => hUW x (hσ hx)⟩, fun x hx t ht t' ht' => ?_⟩, fun x hx => ?_, he⟩` and prove the remaining obligations. Use `hx (t + t') (add_nonneg ht ht')` as an intermediate fact.

Rewrite `this` using `[Complex.ofReal_add, ← add_assoc]`. Then use the resulting hypothesis. Simplify using `using hx 0 le_rfl`.
-/
private theorem exists_isOpen_isMerExt_of_isExtAt (a : IsExtAt h s₀ H) : ∃ U, IsOpen U ∧ s₀ ∈ U ∧ IsMerExt h U H := by
  obtain ⟨U, hs, ⟨⟨σ, hσ⟩, hst⟩, hm, he⟩ := a
  have hUW : ∀ x ∈ U, ∀ t : ℝ, 0 ≤ t → x + t ∈ {x | MeromorphicAt H x} :=
    fun x hx t ht => hm _ (hst x hx t ht)
  have hσW : rightOf σ ⊆ {x | MeromorphicAt H x} := fun x hx => hm x (hσ hx)
  refine ⟨{x : ℂ | ∀ t : ℝ, 0 ≤ t → x + t ∈ {x | MeromorphicAt H x}},
    isOpen_setOf_add_nonneg_real_mem (isOpen_setOf_meromorphicAt H) hσW, hUW s₀ hs,
    ⟨⟨σ, fun x hx => hUW x (hσ hx)⟩, fun x hx t ht t' ht' => ?_⟩, fun x hx => ?_, he⟩
  · have := hx (t + t') (add_nonneg ht ht')
    rwa [Complex.ofReal_add, ← add_assoc] at this
  · simpa using hx 0 le_rfl

/- English proof (translation)
Take `⟨U, hU, hs, hm⟩` from `exists_isOpen_isMerExt_of_isExtAt a`. Use `filter_upwards [hU.mem_nhds hs] with s hs' using ⟨U, hs', hm⟩`.
-/
theorem eventually (a : IsExtAt h s₀ H) : ∀ᶠ s in 𝓝 s₀, IsExtAt h s H := by
  obtain ⟨U, hU, hs, hm⟩ := exists_isOpen_isMerExt_of_isExtAt a
  filter_upwards [hU.mem_nhds hs] with s hs' using ⟨U, hs', hm⟩

/- English proof (translation)
The claim follows from `exists_isOpen_isMerExt_of_isExtAt a`.
-/
theorem exists_isOpen (a : IsExtAt h s₀ H) : ∃ U, IsOpen U ∧ s₀ ∈ U ∧ IsMerExt h U H := exists_isOpen_isMerExt_of_isExtAt a

end IsExtAt

/- English proof (translation)
Assemble the required witnesses or components as `⟨a, b, EqRight.refl h⟩`.
-/
theorem isMerExt_self (a : IsRightDomain U) (b : MeromorphicOn h U) : IsMerExt h U h := ⟨a, b, EqRight.refl h⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨univ, mem_univ _, isRightDomain_univ, fun x _ => MeromorphicAt.const z x, EqRight.refl _⟩`.
-/
theorem isExtAt_const (z s₀ : ℂ) : IsExtAt (fun _ => z) s₀ fun _ => z := ⟨univ, mem_univ _, isRightDomain_univ, fun x _ => MeromorphicAt.const z x, EqRight.refl _⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨H', b, hc⟩`. Conclude with `hc.congr (b.eventuallyEq a)`. Introduce `hc`. Conclude with `⟨H, a, hc⟩`.
-/
theorem IsExtAt.coeffAt_iff (a : IsExtAt h s₀ H) : CoeffAt h s₀ n c ↔ LaurentCoeff H s₀ n c := by
  constructor
  · rintro ⟨H', b, hc⟩
    exact hc.congr (b.eventuallyEq a)
  · intro hc
    exact ⟨H, a, hc⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨H', b, hc⟩`. Conclude with `laurentConst_congr hc (b.eventuallyEq a)`. Introduce `hc`. Conclude with `⟨H, a, hc⟩`.
-/
theorem IsExtAt.valueAt_iff (a : IsExtAt h s₀ H) : ValueAt h s₀ c ↔ LaurentConst H s₀ c := by
  constructor
  · rintro ⟨H', b, hc⟩
    exact laurentConst_congr hc (b.eventuallyEq a)
  · intro hc
    exact ⟨H, a, hc⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨H', b, han, hv⟩`. Establish `t : Tendsto H' (𝓝[≠] s₀) (𝓝 c)`. Rewrite using `[← hv]`. Conclude with `han.continuousAt.tendsto.mono_left nhdsWithin_le_nhds`.

Conclude with `t.congr' (b.eventuallyEq a)`. Introduce `t`. Use `⟨Function.update H s₀ c, a.update c, ?_, by simp⟩` and prove the remaining obligations. Conclude with `(a.update c).meromorphicAt.analyticAt (continuousAt_update_same.mpr t)`.
-/
theorem IsExtAt.holValueAt_iff (a : IsExtAt h s₀ H) : HolValueAt h s₀ c ↔ Tendsto H (𝓝[≠] s₀) (𝓝 c) := by
  constructor
  · rintro ⟨H', b, han, hv⟩
    have t : Tendsto H' (𝓝[≠] s₀) (𝓝 c) := by
      rw [← hv]
      exact han.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact t.congr' (b.eventuallyEq a)
  · intro t
    refine ⟨Function.update H s₀ c, a.update c, ?_, by simp⟩
    exact (a.update c).meromorphicAt.analyticAt (continuousAt_update_same.mpr t)

/- English proof (translation)
Establish `hH` using `a.meromorphicAt`. Establish `hP : MeromorphicAt (fun s : ℂ => (s - s₀) ^ k) s₀` using `(analyticAt_id.sub analyticAt_const).meromorphicAt.pow k`. Establish `hF : MeromorphicAt (fun s => (s - s₀) ^ k * H s) s₀` using `hP.mul hH`. Establish `hPord : meromorphicOrderAt (fun s : ℂ => (s - s₀) ^ k) s₀ = (k : WithTop ℤ)` using `meromorphicOrderAt_pow_id_sub_const`. Establish `hord : meromorphicOrderAt (fun s => (s - s₀) ^ k * H s) s₀ = (k : WithTop ℤ) + meromorphicOrderAt H s₀`.

Rewrite using `[← hPord]`. Conclude with `meromorphicOrderAt_mul hP hH`. Establish `key : ∀ o : WithTop ℤ, (0 ≤ (k : WithTop ℤ) + o ↔ ((-k : ℤ) : WithTop ℤ) ≤ o)`. Introduce `o`. Proceed by induction on `o using WithTop.recTopCoe with`.

Consider the case `top => simp`. Consider the case `coe m`. Use `norm_cast`. Use linear arithmetic over natural numbers and integers. Rewrite using `[tendsto_nhds_iff_meromorphicOrderAt_nonneg hF, hord, key]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨H', b, hb⟩`. Rewrite using `[meromorphicOrderAt_congr (a.eventuallyEq b)]` and apply the resulting hypothesis. Introduce `hk`. Conclude with `⟨H, a, hk⟩`.
-/
theorem IsExtAt.poleLE_iff (a : IsExtAt h s₀ H) :
    PoleLE h s₀ k ↔ ∃ c, Tendsto (fun s => (s - s₀) ^ k * H s) (𝓝[≠] s₀) (𝓝 c) := by
  have hH := a.meromorphicAt
  have hP : MeromorphicAt (fun s : ℂ => (s - s₀) ^ k) s₀ := (analyticAt_id.sub analyticAt_const).meromorphicAt.pow k
  have hF : MeromorphicAt (fun s => (s - s₀) ^ k * H s) s₀ := hP.mul hH
  have hPord : meromorphicOrderAt (fun s : ℂ => (s - s₀) ^ k) s₀ = (k : WithTop ℤ) :=
    meromorphicOrderAt_pow_id_sub_const
  have hord : meromorphicOrderAt (fun s => (s - s₀) ^ k * H s) s₀ =
      (k : WithTop ℤ) + meromorphicOrderAt H s₀ := by
    rw [← hPord]
    exact meromorphicOrderAt_mul hP hH
  have key : ∀ o : WithTop ℤ, (0 ≤ (k : WithTop ℤ) + o ↔ ((-k : ℤ) : WithTop ℤ) ≤ o) := by
    intro o
    induction o using WithTop.recTopCoe with
    | top => simp
    | coe m =>
      norm_cast
      omega
  rw [tendsto_nhds_iff_meromorphicOrderAt_nonneg hF, hord, key]
  constructor
  · rintro ⟨H', b, hb⟩
    rwa [meromorphicOrderAt_congr (a.eventuallyEq b)]
  · intro hk
    exact ⟨H, a, hk⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨H, a, laurentConst_of_tendsto (by simpa using e)⟩`.
-/
theorem IsExtAt.coeffAt_of_tendsto (a : IsExtAt h s₀ H) (e : Tendsto (fun s => (s - s₀) ^ k * H s) (𝓝[≠] s₀) (𝓝 c)) :
    CoeffAt h s₀ (-k) c := ⟨H, a, laurentConst_of_tendsto (by simpa using e)⟩

/- English proof (translation)
Take `⟨c', hc'⟩` from `a.poleLE_iff.mp b`. Establish `h1` using `a.coeffAt_iff.mp e`. Establish `h2` using `a.coeffAt_iff.mp (a.coeffAt_of_tendsto hc')`. Rewrite using `[laurentConst_unique h1 h2]`. Conclude with `hc'`.
-/
theorem IsExtAt.tendsto_of_poleLE (a : IsExtAt h s₀ H) (b : PoleLE h s₀ k) (e : CoeffAt h s₀ (-k) c) :
    Tendsto (fun s => (s - s₀) ^ k * H s) (𝓝[≠] s₀) (𝓝 c) := by
  obtain ⟨c', hc'⟩ := a.poleLE_iff.mp b
  have h1 := a.coeffAt_iff.mp e
  have h2 := a.coeffAt_iff.mp (a.coeffAt_of_tendsto hc')
  rw [laurentConst_unique h1 h2]
  exact hc'

/- English proof (translation)
Simplify using `only [CoeffAt, ValueAt, laurentCoeff_zero]`.
-/
@[simp] theorem coeffAt_zero : CoeffAt h s₀ 0 c ↔ ValueAt h s₀ c := by
  simp only [CoeffAt, ValueAt, laurentCoeff_zero]

/- English proof (translation)
Take `⟨H, ha, hca⟩` from `a`. Conclude with `laurentConst_unique hca (ha.coeffAt_iff.mp b)`.
-/
theorem CoeffAt.unique (a : CoeffAt h s₀ n c) (b : CoeffAt h s₀ n c') : c = c' := by
  obtain ⟨H, ha, hca⟩ := a
  exact laurentConst_unique hca (ha.coeffAt_iff.mp b)

/- English proof (translation)
Take `⟨H, ha, hca⟩` from `a`. Conclude with `laurentConst_unique hca (ha.valueAt_iff.mp b)`.
-/
theorem ValueAt.unique (a : ValueAt h s₀ c) (b : ValueAt h s₀ c') : c = c' := by
  obtain ⟨H, ha, hca⟩ := a
  exact laurentConst_unique hca (ha.valueAt_iff.mp b)

/- English proof (translation)
Take `⟨H, ha, han, hv⟩` from `a`. Substitute `hv` using the available equality. Conclude with `⟨H, ha, laurentConst_of_tendsto (han.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)⟩`.
-/
theorem HolValueAt.valueAt (a : HolValueAt h s₀ c) : ValueAt h s₀ c := by
  obtain ⟨H, ha, han, hv⟩ := a
  subst hv
  exact ⟨H, ha, laurentConst_of_tendsto (han.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)⟩

/- English proof (translation)
The claim follows from `ValueAt.unique a.valueAt b.valueAt`.
-/
theorem HolValueAt.unique (a : HolValueAt h s₀ c) (b : HolValueAt h s₀ c') : c = c' := ValueAt.unique a.valueAt b.valueAt

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `a`. Use `⟨?_, a.valueAt⟩` and prove the remaining obligations. Take `⟨H, ha, han, -⟩` from `a`. Conclude with `⟨H, ha, by simpa using han.meromorphicOrderAt_nonneg⟩`.

Introduce and unpack `⟨hp, hv⟩`. Take `⟨H, ha, hk⟩` from `id hp`. Take `⟨c', hc'⟩` from `ha.poleLE_iff.mp hp`. Simplify using `only [pow_zero, one_mul] at hc'`. Establish `hcc` using `laurentConst_eq_of_tendsto H s₀ c c' (ha.valueAt_iff.mp hv) hc'`.

Substitute `hcc` using the available equality. Conclude with `ha.holValueAt_iff.mpr hc'`.
-/
theorem holValueAt_iff_poleLE : HolValueAt h s₀ c ↔ PoleLE h s₀ 0 ∧ ValueAt h s₀ c := by
  constructor
  · intro a
    refine ⟨?_, a.valueAt⟩
    obtain ⟨H, ha, han, -⟩ := a
    exact ⟨H, ha, by simpa using han.meromorphicOrderAt_nonneg⟩
  · rintro ⟨hp, hv⟩
    obtain ⟨H, ha, hk⟩ := id hp
    obtain ⟨c', hc'⟩ := ha.poleLE_iff.mp hp
    simp only [pow_zero, one_mul] at hc'
    have hcc := laurentConst_eq_of_tendsto H s₀ c c' (ha.valueAt_iff.mp hv) hc'
    subst hcc
    exact ha.holValueAt_iff.mpr hc'

/- English proof (translation)
Assemble the required witnesses or components as `⟨H, a.isMerExt.isExtAt hs, a.2.1 s₀ hs, rfl⟩`.
-/
theorem IsHolExt.holValueAt (a : IsHolExt h U H) (hs : s₀ ∈ U) : HolValueAt h s₀ (H s₀) := ⟨H, a.isMerExt.isExtAt hs, a.2.1 s₀ hs, rfl⟩

/- English proof (translation)
The claim follows from `(show IsHolExt h (rightOf σ) h from ⟨isRightDomain_rightOf σ, a, EqRight.refl h⟩).holValueAt hs`.
-/
theorem holValueAt_self (a : AnalyticOnNhd ℂ h (rightOf σ)) (hs : σ < s₀.re) : HolValueAt h s₀ (h s₀) := (show IsHolExt h (rightOf σ) h from ⟨isRightDomain_rightOf σ, a, EqRight.refl h⟩).holValueAt hs

/- English proof (translation)
Take `⟨H0, hH0⟩` from `a`. Establish `ha` using `hH0.isExtAt (mem_univ s₀)`. Rewrite using `[ha.holValueAt_iff]`. Establish `heq : H0 =ᶠ[𝓝[≠] s₀] H` using `eventuallyEq_of_isPreconnected hU hσ (fun x _ => hH0.2.1 x (mem_univ x)) b.meromorphicOn (hH0.2.2.trans e.symm) hs`. Conclude with `((b s₀ hs).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm`.
-/
theorem Continues.holValueAt (a : Continues h) (hU : IsPreconnected U) (hσ : rightOf σ ⊆ U) (b : AnalyticOnNhd ℂ H U)
    (e : EqRight H h) (hs : s₀ ∈ U) : HolValueAt h s₀ (H s₀) := by
  obtain ⟨H0, hH0⟩ := a
  have ha := hH0.isExtAt (mem_univ s₀)
  rw [ha.holValueAt_iff]
  have heq : H0 =ᶠ[𝓝[≠] s₀] H := eventuallyEq_of_isPreconnected hU hσ (fun x _ => hH0.2.1 x (mem_univ x))
    b.meromorphicOn (hH0.2.2.trans e.symm) hs
  exact ((b s₀ hs).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm

/- English proof (translation)
Take `⟨H, ha, hc⟩` from `a`. Conclude with `⟨H, ha.congr e, hc⟩`.
-/
theorem CoeffAt.congr (a : CoeffAt h s₀ n c) (e : EqRight h h') : CoeffAt h' s₀ n c := by
  obtain ⟨H, ha, hc⟩ := a
  exact ⟨H, ha.congr e, hc⟩

/- English proof (translation)
Take `⟨H, ha, hc⟩` from `a`. Conclude with `⟨H, ha.congr e, hc⟩`.
-/
theorem ValueAt.congr (a : ValueAt h s₀ c) (e : EqRight h h') : ValueAt h' s₀ c := by
  obtain ⟨H, ha, hc⟩ := a
  exact ⟨H, ha.congr e, hc⟩

/- English proof (translation)
Take `⟨H, ha, han, hv⟩` from `a`. Conclude with `⟨H, ha.congr e, han, hv⟩`.
-/
theorem HolValueAt.congr (a : HolValueAt h s₀ c) (e : EqRight h h') : HolValueAt h' s₀ c := by
  obtain ⟨H, ha, han, hv⟩ := a
  exact ⟨H, ha.congr e, han, hv⟩

/- English proof (translation)
Take `⟨H, ha, hk⟩` from `a`. Conclude with `⟨H, ha.congr e, hk⟩`.
-/
theorem PoleLE.congr (a : PoleLE h s₀ k) (e : EqRight h h') : PoleLE h' s₀ k := by
  obtain ⟨H, ha, hk⟩ := a
  exact ⟨H, ha.congr e, hk⟩

/- English proof (translation)
Take `⟨H, hU, hm, he⟩` from `a`. Conclude with `⟨H, hU, hm, he.trans e⟩`.
-/
theorem Continues.congr (a : Continues h) (e : EqRight h h') : Continues h' := by
  obtain ⟨H, hU, hm, he⟩ := a
  exact ⟨H, hU, hm, he.trans e⟩

/- English proof (translation)
Take `⟨H, ha, hca⟩` from `a`. Take `⟨H', hb, hcb⟩` from `b`. Use `⟨fun s => H s + H' s, ha.add hb, ?_⟩` and prove the remaining obligations. Use `laurentConst_add hca hcb` as an intermediate fact. Unfold `LaurentCoeff`.

Simplify `this` using `only [mul_add]`.
-/
theorem CoeffAt.add (a : CoeffAt h s₀ n c) (b : CoeffAt h' s₀ n c') : CoeffAt (fun s => h s + h' s) s₀ n (c + c') := by
  obtain ⟨H, ha, hca⟩ := a
  obtain ⟨H', hb, hcb⟩ := b
  refine ⟨fun s => H s + H' s, ha.add hb, ?_⟩
  have := laurentConst_add hca hcb
  unfold LaurentCoeff
  simpa only [mul_add] using this

/- English proof (translation)
Take `⟨H, ha, hca⟩` from `a`. Use `⟨fun s => z * H s, (isExtAt_const z s₀).mul ha, ?_⟩` and prove the remaining obligations. Use `laurentConst_const_mul z hca` as an intermediate fact. Unfold `LaurentCoeff`. Simplify `this` using `only [mul_left_comm]`.
-/
theorem CoeffAt.const_mul (z : ℂ) (a : CoeffAt h s₀ n c) : CoeffAt (fun s => z * h s) s₀ n (z * c) := by
  obtain ⟨H, ha, hca⟩ := a
  refine ⟨fun s => z * H s, (isExtAt_const z s₀).mul ha, ?_⟩
  have := laurentConst_const_mul z hca
  unfold LaurentCoeff
  simpa only [mul_left_comm] using this

/- English proof (translation)
Take `⟨H, ha, hca⟩` from `a`. Take `⟨H', hb, hcb⟩` from `b`. Conclude with `⟨fun s => H s + H' s, ha.add hb, laurentConst_add hca hcb⟩`.
-/
theorem ValueAt.add (a : ValueAt h s₀ c) (b : ValueAt h' s₀ c') : ValueAt (fun s => h s + h' s) s₀ (c + c') := by
  obtain ⟨H, ha, hca⟩ := a
  obtain ⟨H', hb, hcb⟩ := b
  exact ⟨fun s => H s + H' s, ha.add hb, laurentConst_add hca hcb⟩

/- English proof (translation)
Take `⟨H, ha, hca⟩` from `a`. Conclude with `⟨fun s => z * H s, (isExtAt_const z s₀).mul ha, laurentConst_const_mul z hca⟩`.
-/
theorem ValueAt.const_mul (z : ℂ) (a : ValueAt h s₀ c) : ValueAt (fun s => z * h s) s₀ (z * c) := by
  obtain ⟨H, ha, hca⟩ := a
  exact ⟨fun s => z * H s, (isExtAt_const z s₀).mul ha, laurentConst_const_mul z hca⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ => z, isExtAt_const z s₀, analyticAt_const, rfl⟩`.
-/
theorem holValueAt_const (z s₀ : ℂ) : HolValueAt (fun _ => z) s₀ z := ⟨fun _ => z, isExtAt_const z s₀, analyticAt_const, rfl⟩

/- English proof (translation)
Take `⟨H, ha, han, rfl⟩` from `a`. Take `⟨H', hb, hbn, rfl⟩` from `b`. Conclude with `⟨fun s => H s + H' s, ha.add hb, han.add hbn, rfl⟩`.
-/
theorem HolValueAt.add (a : HolValueAt h s₀ c) (b : HolValueAt h' s₀ c') : HolValueAt (fun s => h s + h' s) s₀ (c + c') := by
  obtain ⟨H, ha, han, rfl⟩ := a
  obtain ⟨H', hb, hbn, rfl⟩ := b
  exact ⟨fun s => H s + H' s, ha.add hb, han.add hbn, rfl⟩

/- English proof (translation)
Take `⟨H, ha, han, rfl⟩` from `a`. Take `⟨H', hb, hbn, rfl⟩` from `b`. Conclude with `⟨fun s => H s * H' s, ha.mul hb, han.mul hbn, rfl⟩`.
-/
theorem HolValueAt.mul (a : HolValueAt h s₀ c) (b : HolValueAt h' s₀ c') : HolValueAt (fun s => h s * h' s) s₀ (c * c') := by
  obtain ⟨H, ha, han, rfl⟩ := a
  obtain ⟨H', hb, hbn, rfl⟩ := b
  exact ⟨fun s => H s * H' s, ha.mul hb, han.mul hbn, rfl⟩

/- English proof (translation)
Take `⟨H, ha, han, rfl⟩` from `a`. Take `⟨H', hb, hbn, rfl⟩` from `b`. Conclude with `⟨fun s => H s / H' s, ha.div hb, han.div hbn h0, rfl⟩`.
-/
theorem HolValueAt.div (a : HolValueAt h s₀ c) (b : HolValueAt h' s₀ c') (h0 : c' ≠ 0) :
    HolValueAt (fun s => h s / h' s) s₀ (c / c') := by
  obtain ⟨H, ha, han, rfl⟩ := a
  obtain ⟨H', hb, hbn, rfl⟩ := b
  exact ⟨fun s => H s / H' s, ha.div hb, han.div hbn h0, rfl⟩

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => simpa using holValueAt_const 1 s₀`. Consider the case `@insert j T hj ih`. Simplify using `only [Finset.prod_insert hj]`. Conclude with `(a j (Finset.mem_insert_self j T)).mul (ih fun i hi => a i (Finset.mem_insert_of_mem hi))`.
-/
theorem holValueAt_prod {ι : Type*} (T : Finset ι) {f : ι → ℂ → ℂ} {z : ι → ℂ} (a : ∀ i ∈ T, HolValueAt (f i) s₀ (z i)) :
    HolValueAt (fun s => ∏ i ∈ T, f i s) s₀ (∏ i ∈ T, z i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using holValueAt_const 1 s₀
  | @insert j T hj ih =>
    simp only [Finset.prod_insert hj]
    exact (a j (Finset.mem_insert_self j T)).mul (ih fun i hi => a i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Take `⟨H, ha, han, hv⟩` from `a`. Conclude with `⟨fun s => H (s + z), ha.comp_add, han.comp (f := fun s => s + z) (by fun_prop), hv⟩`.
-/
theorem HolValueAt.comp_add {z : ℂ} (a : HolValueAt h (s₀ + z) c) : HolValueAt (fun s => h (s + z)) s₀ c := by
  obtain ⟨H, ha, han, hv⟩ := a
  exact ⟨fun s => H (s + z), ha.comp_add, han.comp (f := fun s => s + z) (by fun_prop), hv⟩

/- English proof (translation)
Take `⟨H, ha, hk⟩` from `id a`. Take `⟨H', hb, hbn, rfl⟩` from `b`. Establish `t1` using `ha.tendsto_of_poleLE a e`. Establish `t2 : Tendsto H' (𝓝[≠] s₀) (𝓝 (H' s₀))` using `hbn.continuousAt.tendsto.mono_left nhdsWithin_le_nhds`. Establish `hm` using `ha.mul hb`.

Establish `t3 : Tendsto (fun s => (s - s₀) ^ k * (H s * H' s)) (𝓝[≠] s₀) (𝓝 (c * H' s₀))` using `(t1.mul t2).congr fun s => by ring`. Conclude with `⟨hm.poleLE_iff.mpr ⟨_, t3⟩, hm.coeffAt_of_tendsto t3⟩`.
-/
theorem PoleLE.mul_hol (a : PoleLE h s₀ k) (e : CoeffAt h s₀ (-k) c) (b : HolValueAt h' s₀ c') :
    PoleLE (fun s => h s * h' s) s₀ k ∧ CoeffAt (fun s => h s * h' s) s₀ (-k) (c * c') := by
  obtain ⟨H, ha, hk⟩ := id a
  obtain ⟨H', hb, hbn, rfl⟩ := b
  have t1 := ha.tendsto_of_poleLE a e
  have t2 : Tendsto H' (𝓝[≠] s₀) (𝓝 (H' s₀)) := hbn.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hm := ha.mul hb
  have t3 : Tendsto (fun s => (s - s₀) ^ k * (H s * H' s)) (𝓝[≠] s₀) (𝓝 (c * H' s₀)) :=
    (t1.mul t2).congr fun s => by ring
  exact ⟨hm.poleLE_iff.mpr ⟨_, t3⟩, hm.coeffAt_of_tendsto t3⟩

/- English proof (translation)
Rewrite using `[isOpen_iff_mem_nhds]`. Introduce and unpack `s ⟨H, hs⟩`. Conclude with `hs.eventually.mono fun s' hs' => ⟨H, hs'⟩`.
-/
theorem isOpen_contDom (h : ℂ → ℂ) : IsOpen (contDom h) := by
  rw [isOpen_iff_mem_nhds]
  rintro s ⟨H, hs⟩
  exact hs.eventually.mono fun s' hs' => ⟨H, hs'⟩

/- English proof (translation)
Introduce `_ hs` and use `⟨H, a.isExtAt hs⟩`.
-/
theorem IsMerExt.subset_contDom (a : IsMerExt h U H) : U ⊆ contDom h := fun _ hs => ⟨H, a.isExtAt hs⟩

/- English proof (translation)
Take `⟨H, U, hsU, hU, hm, he⟩` from `hs`. Take `⟨σ, hσ⟩` from `hU.1`. Use `⟨⟨σ, hσ.trans (IsMerExt.subset_contDom ⟨hU, hm, he⟩)⟩, fun s hs t ht => ?_⟩` and prove the remaining obligations. Take `⟨H', U', hsU', hU', hm', he'⟩` from `hs`. Conclude with `⟨H', U', hU'.2 s hsU' t ht, hU', hm', he'⟩`.
-/
theorem isRightDomain_contDom (hs : s₀ ∈ contDom h) : IsRightDomain (contDom h) := by
  obtain ⟨H, U, hsU, hU, hm, he⟩ := hs
  obtain ⟨σ, hσ⟩ := hU.1
  refine ⟨⟨σ, hσ.trans (IsMerExt.subset_contDom ⟨hU, hm, he⟩)⟩, fun s hs t ht => ?_⟩
  obtain ⟨H', U', hsU', hU', hm', he'⟩ := hs
  exact ⟨H', U', hU'.2 s hsU' t ht, hU', hm', he'⟩

/- English proof (translation)
Establish `hex : ∃ c, CoeffAt h s₀ n c` using `⟨c, a⟩`. Unfold `laurent`. Rewrite using `[dif_pos hex]`. Conclude with `CoeffAt.unique hex.choose_spec a`.
-/
theorem CoeffAt.laurent_eq (a : CoeffAt h s₀ n c) : laurent h s₀ n = c := by
  have hex : ∃ c, CoeffAt h s₀ n c := ⟨c, a⟩
  unfold laurent
  rw [dif_pos hex]
  exact CoeffAt.unique hex.choose_spec a

/- English proof (translation)
Take `⟨H, ha⟩` from `hs`. Take `⟨c, hc⟩` from `exists_laurentCoeff ha.meromorphicAt n`. Establish `hC : CoeffAt h s₀ n c` using `⟨H, ha, hc⟩`. Rewrite using `[hC.laurent_eq]`. Conclude with `hC`.
-/
theorem coeffAt_laurent (hs : s₀ ∈ contDom h) (n : ℤ) : CoeffAt h s₀ n (laurent h s₀ n) := by
  obtain ⟨H, ha⟩ := hs
  obtain ⟨c, hc⟩ := exists_laurentCoeff ha.meromorphicAt n
  have hC : CoeffAt h s₀ n c := ⟨H, ha, hc⟩
  rw [hC.laurent_eq]
  exact hC

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `a`. Take `⟨H, ha, -⟩` from `id a`. Conclude with `⟨⟨H, ha⟩, a.laurent_eq⟩`. Introduce and unpack `⟨hs, rfl⟩`.

Conclude with `coeffAt_laurent hs n`.
-/
theorem coeffAt_iff : CoeffAt h s₀ n c ↔ s₀ ∈ contDom h ∧ laurent h s₀ n = c := by
  constructor
  · intro a
    obtain ⟨H, ha, -⟩ := id a
    exact ⟨⟨H, ha⟩, a.laurent_eq⟩
  · rintro ⟨hs, rfl⟩
    exact coeffAt_laurent hs n

/- English proof (translation)
Rewrite using `[← coeffAt_zero, coeffAt_iff]`. Conclude with `Iff.rfl`.
-/
theorem valueAt_iff : ValueAt h s₀ c ↔ s₀ ∈ contDom h ∧ cont h s₀ = c := by
  rw [← coeffAt_zero, coeffAt_iff]
  exact Iff.rfl

/- English proof (translation)
The claim follows from `(valueAt_iff.mp a).2`.
-/
theorem ValueAt.cont_eq (a : ValueAt h s₀ c) : cont h s₀ = c := (valueAt_iff.mp a).2

/- English proof (translation)
Establish `h1` using `a.meromorphicAt.eventually_analyticAt`. Establish `h2 : ∀ᶠ s in 𝓝[≠] s₀, IsExtAt h s H` using `nhdsWithin_le_nhds a.eventually`. Use `filter_upwards [h1, h2] with s hs1 hs2`. Conclude with `(HolValueAt.valueAt ⟨H, hs2, hs1, rfl⟩).cont_eq`.
-/
theorem IsExtAt.cont_eventuallyEq (a : IsExtAt h s₀ H) : cont h =ᶠ[𝓝[≠] s₀] H := by
  have h1 := a.meromorphicAt.eventually_analyticAt
  have h2 : ∀ᶠ s in 𝓝[≠] s₀, IsExtAt h s H := nhdsWithin_le_nhds a.eventually
  filter_upwards [h1, h2] with s hs1 hs2
  exact (HolValueAt.valueAt ⟨H, hs2, hs1, rfl⟩).cont_eq

/- English proof (translation)
Introduce `s hs`. Take `⟨H, ha⟩` from `hs`. Conclude with `ha.meromorphicAt.congr ha.cont_eventuallyEq.symm`.
-/
theorem meromorphicOn_cont (h : ℂ → ℂ) : MeromorphicOn (cont h) (contDom h) := by
  intro s hs
  obtain ⟨H, ha⟩ := hs
  exact ha.meromorphicAt.congr ha.cont_eventuallyEq.symm

/- English proof (translation)
Take `⟨H, ha, han, hv⟩` from `id a`. Establish `e1` using `ha.cont_eventuallyEq`. Establish `e2 : cont h s₀ = H s₀` using `by rw [a.valueAt.cont_eq, hv]`. Establish `e3 : H =ᶠ[𝓝 s₀] cont h`. Establish `e4` using `e1.symm`.

Rewrite `e4` using `[EventuallyEq, eventually_nhdsWithin_iff]`. Use `filter_upwards [e4] with s hs`. Distinguish the cases in `hss : s = s₀`. Rewrite using `[hss]`. Conclude with `e2.symm`.

Conclude with `hs hss`. Conclude with `han.congr e3`.
-/
theorem HolValueAt.analyticAt_cont (a : HolValueAt h s₀ c) : AnalyticAt ℂ (cont h) s₀ := by
  obtain ⟨H, ha, han, hv⟩ := id a
  have e1 := ha.cont_eventuallyEq
  have e2 : cont h s₀ = H s₀ := by rw [a.valueAt.cont_eq, hv]
  have e3 : H =ᶠ[𝓝 s₀] cont h := by
    have e4 := e1.symm
    rw [EventuallyEq, eventually_nhdsWithin_iff] at e4
    filter_upwards [e4] with s hs
    by_cases hss : s = s₀
    · rw [hss]
      exact e2.symm
    · exact hs hss
  exact han.congr e3

/- English proof (translation)
Introduce `_ hs` and use `(holValueAt_self a hs).valueAt.cont_eq`.
-/
theorem eqOn_cont (a : AnalyticOnNhd ℂ h (rightOf σ)) : EqOn (cont h) h (rightOf σ) := fun _ hs => (holValueAt_self a hs).valueAt.cont_eq

/- English proof (translation)
Establish `hsub : rightOf σ ⊆ contDom h` using `(isMerExt_self (isRightDomain_rightOf σ) a.meromorphicOn).subset_contDom`. Establish `hmem : ((σ + 1 : ℝ) : ℂ) ∈ rightOf σ`. Simplify using `only [mem_rightOf, Complex.ofReal_re]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `⟨isRightDomain_contDom (hsub hmem), meromorphicOn_cont h, ⟨σ, eqOn_cont a⟩⟩`.
-/
theorem isMerExt_cont (a : AnalyticOnNhd ℂ h (rightOf σ)) : IsMerExt h (contDom h) (cont h) := by
  have hsub : rightOf σ ⊆ contDom h :=
    (isMerExt_self (isRightDomain_rightOf σ) a.meromorphicOn).subset_contDom
  have hmem : ((σ + 1 : ℝ) : ℂ) ∈ rightOf σ := by
    simp only [mem_rightOf, Complex.ofReal_re]
    linarith
  exact ⟨isRightDomain_contDom (hsub hmem), meromorphicOn_cont h, ⟨σ, eqOn_cont a⟩⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨H, hH⟩`. Conclude with `eq_univ_of_univ_subset hH.subset_contDom`. Introduce `e`. Use `⟨cont h, ?_⟩` and prove the remaining obligations.

Rewrite using `[← e]`. Conclude with `isMerExt_cont a`.
-/
theorem continues_iff (a : AnalyticOnNhd ℂ h (rightOf σ)) : Continues h ↔ contDom h = univ := by
  constructor
  · rintro ⟨H, hH⟩
    exact eq_univ_of_univ_subset hH.subset_contDom
  · intro e
    refine ⟨cont h, ?_⟩
    rw [← e]
    exact isMerExt_cont a

/- English proof (translation)
Use `⟨isRightDomain_univ, fun s _ => ?_, ⟨1, fun s hs => zeta_eq_tsum_one_div_nat_add_one_cpow hs⟩⟩` and prove the remaining obligations. Break down `eq_or_ne s 1 with rfl | hs` into its components or cases. Establish `hGa : AnalyticAt ℂ (Function.update (fun s => (s - 1) * riemannZeta s) 1 1) 1`. Use `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with z hz`.

Use `DifferentiableAt.congr_of_eventuallyEq ((differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hz)) ?_` and prove the remaining obligations. Use `filter_upwards [isOpen_compl_singleton.mem_nhds hz] with w hw`. Conclude with `Function.update_of_ne hw _ _`. Conclude with `continuousAt_update_same.mpr riemannZeta_residue_one`. Establish `hm : MeromorphicAt (fun s => Function.update (fun s => (s - 1) * riemannZeta s) 1 1 s * (s - 1)⁻¹) 1` using `hGa.meromorphicAt.mul (analyticAt_id.sub analyticAt_const).meromorphicAt.inv`.

Use `hm.congr ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with z hz`. Establish `hd : z - 1 ≠ 0` using `sub_ne_zero.mpr hz`. Rewrite using `[Function.update_of_ne hz]`. Clear the denominators using the available nonvanishing facts.

Establish `hd : DifferentiableOn ℂ riemannZeta {1}ᶜ` using `fun x hx => (differentiableAt_riemannZeta hx).differentiableWithinAt`. Conclude with `(hd.analyticAt (isOpen_compl_singleton.mem_nhds hs)).meromorphicAt`.
-/
theorem isMerExt_riemannZeta : IsMerExt (fun s => ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s) univ riemannZeta := by
  refine ⟨isRightDomain_univ, fun s _ => ?_, ⟨1, fun s hs => zeta_eq_tsum_one_div_nat_add_one_cpow hs⟩⟩
  rcases eq_or_ne s 1 with rfl | hs
  · have hGa : AnalyticAt ℂ (Function.update (fun s => (s - 1) * riemannZeta s) 1 1) 1 := by
      refine Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with z hz
        refine DifferentiableAt.congr_of_eventuallyEq
          ((differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hz)) ?_
        filter_upwards [isOpen_compl_singleton.mem_nhds hz] with w hw
        exact Function.update_of_ne hw _ _
      · exact continuousAt_update_same.mpr riemannZeta_residue_one
    have hm : MeromorphicAt (fun s => Function.update (fun s => (s - 1) * riemannZeta s) 1 1 s * (s - 1)⁻¹) 1 :=
      hGa.meromorphicAt.mul (analyticAt_id.sub analyticAt_const).meromorphicAt.inv
    refine hm.congr ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hd : z - 1 ≠ 0 := sub_ne_zero.mpr hz
    rw [Function.update_of_ne hz]
    field_simp
  · have hd : DifferentiableOn ℂ riemannZeta {1}ᶜ := fun x hx => (differentiableAt_riemannZeta hx).differentiableWithinAt
    exact (hd.analyticAt (isOpen_compl_singleton.mem_nhds hs)).meromorphicAt

/- English proof (translation)
Establish `h1 : Tendsto (fun s => (s - 1) ^ 1 * riemannZeta s) (𝓝[≠] 1) (𝓝 1)` using `by simpa using riemannZeta_residue_one`. Establish `a` using `fun s => isMerExt_riemannZeta.isExtAt (mem_univ s)`. Use `⟨(a 0).holValueAt_iff.2 ?_, (a 1).poleLE_iff.2 ⟨1, h1⟩, (a 1).coeffAt_of_tendsto h1, _, a 1, Polynomial.X, by simp, by simpa using tendsto_riemannZeta_sub_one_div⟩` and prove the remaining obligations. Conclude with `riemannZeta_zero ▸ (differentiableAt_riemannZeta zero_ne_one).continuousAt.tendsto.mono_left nhdsWithin_le_nhds`.
-/
example : HolValueAt (fun s => ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s) 0 (-1 / 2) ∧
    PoleLE (fun s => ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s) 1 1 ∧ ResidueAt (fun s => ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s) 1 1 ∧
    ValueAt (fun s => ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s) 1 Real.eulerMascheroniConstant := by
  have h1 : Tendsto (fun s => (s - 1) ^ 1 * riemannZeta s) (𝓝[≠] 1) (𝓝 1) := by simpa using riemannZeta_residue_one
  have a := fun s => isMerExt_riemannZeta.isExtAt (mem_univ s)
  refine ⟨(a 0).holValueAt_iff.2 ?_, (a 1).poleLE_iff.2 ⟨1, h1⟩, (a 1).coeffAt_of_tendsto h1,
    _, a 1, Polynomial.X, by simp, by simpa using tendsto_riemannZeta_sub_one_div⟩
  exact riemannZeta_zero ▸ (differentiableAt_riemannZeta zero_ne_one).continuousAt.tendsto.mono_left nhdsWithin_le_nhds

/- English proof (translation)
Establish `a : IsExtAt (fun s : ℂ => s⁻¹) 0 fun s => s⁻¹` using `(isMerExt_self isRightDomain_univ fun s _ => (MeromorphicAt.id s).inv).isExtAt trivial`. Conclude with `⟨⟨_, a, Polynomial.X, by simp, by simp⟩, fun c e => not_tendsto_atTop_of_tendsto_nhds (a.holValueAt_iff.1 e).norm (tendsto_norm_cobounded_atTop.comp tendsto_inv₀_nhdsNE_zero)⟩`.
-/
example : ValueAt (fun s => s⁻¹) 0 0 ∧ ∀ c, ¬ HolValueAt (fun s => s⁻¹) 0 c := by
  have a : IsExtAt (fun s : ℂ => s⁻¹) 0 fun s => s⁻¹ :=
    (isMerExt_self isRightDomain_univ fun s _ => (MeromorphicAt.id s).inv).isExtAt trivial
  exact ⟨⟨_, a, Polynomial.X, by simp, by simp⟩, fun c e => not_tendsto_atTop_of_tendsto_nhds (a.holValueAt_iff.1 e).norm
    (tendsto_norm_cobounded_atTop.comp tendsto_inv₀_nhdsNE_zero)⟩

end GlobalTheory.Cont

end
