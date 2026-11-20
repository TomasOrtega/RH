import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates

noncomputable section

open MeasureTheory

namespace UpperTheory.Esk.LinearTraceLemmas

variable {A Y : Type} [MeasurableSpace Y] (ν : Measure Y) (V : Submodule ℂ (A → ℂ))

def evl (a : A) : Module.Dual ℂ V := (LinearMap.proj a : (A → ℂ) →ₗ[ℂ] ℂ) ∘ₗ V.subtype

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evl_apply (a : A) (f : V) : evl V a f = f.1 a := rfl

/- English proof (translation)
Assume the negation of the conclusion as `h`. Take `⟨f, hf0, hfk⟩` from `Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr h)`. Take `⟨v, rfl⟩` from `(Module.evalEquiv ℂ V).surjective f`. Establish `hv : v = 0`. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `a`. Establish `h1 : (Module.evalEquiv ℂ V v) (evl V a) = 0` using `LinearMap.mem_ker.mp (hfk (Submodule.subset_span ⟨a, rfl⟩))`. Establish `h2 : (Module.evalEquiv ℂ V v) (evl V a) = v.1 a`. Both sides reduce to the same expression. Establish `h3 : v.1 a = 0` using `h2.symm.trans h1`.

Simplify using `using h3`. Conclude with `hf0 (by rw [hv, map_zero])`.
-/
theorem span_evl [FiniteDimensional ℂ V] : Submodule.span ℂ (Set.range (evl V)) = ⊤ := by
  by_contra h
  obtain ⟨f, hf0, hfk⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr h)
  obtain ⟨v, rfl⟩ := (Module.evalEquiv ℂ V).surjective f
  have hv : v = 0 := by
    apply Subtype.ext
    funext a
    have h1 : (Module.evalEquiv ℂ V v) (evl V a) = 0 :=
      LinearMap.mem_ker.mp (hfk (Submodule.subset_span ⟨a, rfl⟩))
    have h2 : (Module.evalEquiv ℂ V v) (evl V a) = v.1 a := by
      rfl
    have h3 : v.1 a = 0 := h2.symm.trans h1
    simpa using h3
  exact hf0 (by rw [hv, map_zero])

omit [MeasurableSpace Y] in
/- English proof (translation)
Establish `hn'` using `hn y`. Establish `hC0 : 0 ≤ C`. Assume the negation of the conclusion as `hneg`. Establish `hlt : C < 0` using `not_le.mp hneg`. Establish `: C * n y < 0` using `mul_neg_of_neg_of_pos hlt hn'`.

Combine the linear relations using `[norm_nonneg (g y), hC y]`. Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem bound_mul {g h : Y → ℂ} {n : Y → ℝ} (hn : ∀ y, 0 < n y) (C D : ℝ)
    (hC : ∀ y, ‖g y‖ ≤ C * n y) (hD : ∀ y, ‖h y‖ * n y ≤ D) (y : Y) : ‖g y * h y‖ ≤ C * D := by
  have hn' := hn y
  have hC0 : 0 ≤ C := by
    by_contra hneg
    have hlt : C < 0 := not_le.mp hneg
    have : C * n y < 0 := mul_neg_of_neg_of_pos hlt hn'
    linarith [norm_nonneg (g y), hC y]
  rw [norm_mul]
  calc ‖g y‖ * ‖h y‖ ≤ (C * n y) * ‖h y‖ := mul_le_mul_of_nonneg_right (hC y) (norm_nonneg _)
    _ = C * (‖h y‖ * n y) := by ring
    _ ≤ C * D := mul_le_mul_of_nonneg_left (hD y) hC0

/- English proof (translation)
Conclude with `(integrable_const (C * D)).mono' (hg.mul hh).aestronglyMeasurable (ae_of_all _ fun y => bound_mul hn C D hC hD y)`.
-/
theorem integrable_mul [IsFiniteMeasure ν] {g h : Y → ℂ} {n : Y → ℝ} (hn : ∀ y, 0 < n y)
    (hg : Measurable g) (hh : Measurable h) (C D : ℝ) (hC : ∀ y, ‖g y‖ ≤ C * n y)
    (hD : ∀ y, ‖h y‖ * n y ≤ D) : Integrable (fun y => g y * h y) ν := by
  exact (integrable_const (C * D)).mono' (hg.mul hh).aestronglyMeasurable
    (ae_of_all _ fun y => bound_mul hn C D hC hD y)

def Good (K : Y → V) (ev : Y → A) (n : Y → ℝ) (φ : Module.Dual ℂ V) : Prop :=
  Measurable (fun y => φ (K y)) ∧ (∃ C, ∀ y, ‖φ (K y)‖ ≤ C * n y) ∧
    ∀ f : V, ∫ y, φ (K y) * f.1 (ev y) ∂ν = φ f

/- English proof (translation)
Establish `hint : ∀ ψ : Module.Dual ℂ V, Good ν V K ev n ψ → ∀ f : V, Integrable (fun y => ψ (K y) * f.1 (ev y)) ν`. Introduce `ψ hψ f`. Take `⟨C, hC⟩` from `hψ.2.1`. Take `⟨D, hD⟩` from `hevb f`. Conclude with `integrable_mul ν hn hψ.1 (hev f) C D hC hD`.

Establish `hadd : ∀ φ₁ φ₂, Good ν V K ev n φ₁ → Good ν V K ev n φ₂ → Good ν V K ev n (φ₁ + φ₂)`. Introduce `φ₁ φ₂ h₁ h₂`. Take `⟨C₁, hC₁⟩` from `h₁.2.1`. Take `⟨C₂, hC₂⟩` from `h₂.2.1`. Use `⟨h₁.1.add h₂.1, ⟨C₁ + C₂, fun y => ?_⟩, fun f => ?_⟩` and prove the remaining obligations.

Rewrite using `[LinearMap.add_apply, add_mul]`. Conclude with `(norm_add_le _ _).trans (add_le_add (hC₁ y) (hC₂ y))`. Simplify using `only [LinearMap.add_apply, add_mul]`. Rewrite using `[integral_add (hint φ₁ h₁ f) (hint φ₂ h₂ f), h₁.2.2 f, h₂.2.2 f]`. Establish `hzero : Good ν V K ev n 0`.

Use `⟨?_, ⟨0, fun y => ?_⟩, fun f => ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish `hsmul : ∀ (c : ℂ) φ, Good ν V K ev n φ → Good ν V K ev n (c • φ)`.

Introduce `c φ h`. Take `⟨C, hC⟩` from `h.2.1`. Use `⟨h.1.const_mul c, ⟨‖c‖ * C, fun y => ?_⟩, fun f => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, smul_eq_mul, norm_mul, mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left (hC y) (norm_nonneg c)`.

Simplify using `only [LinearMap.smul_apply, smul_eq_mul, mul_assoc]`. Rewrite using `[integral_const_mul, h.2.2 f]`. Take `⟨Sg, hSg⟩ : ∃ Sg : Submodule ℂ (Module.Dual ℂ V), ∀ ψ, ψ ∈ Sg ↔ Good ν V K ev n ψ` from `⟨{ carrier := {ψ | Good ν V K ev n ψ} add_mem' := fun {a b} ha hb => hadd a b ha hb zero_mem' := hzero smul_mem' := fun c ψ h => hsmul c ψ h }, fun _ => Iff.rfl⟩`. Establish `hev' : ∀ a, Good ν V K ev n (evl V a)`. Introduce `a`.

Use `⟨?_, ?_, fun f => ?_⟩` and prove the remaining obligations. Simplify `hK a` using `only [evl_apply]`. Simplify `hKb a` using `only [evl_apply]`. Simplify `hrep f a` using `only [evl_apply]`. Establish `htop : Sg = ⊤`.

Rewrite using `[eq_top_iff, ← span_evl V, Submodule.span_le]`. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `(hSg _).mpr (hev' a)`. Conclude with `(hSg φ).mp (by rw [htop]; exact Submodule.mem_top)`.
-/
theorem good_all [IsFiniteMeasure ν] [FiniteDimensional ℂ V] (K : Y → V) (ev : Y → A) (n : Y → ℝ)
    (hn : ∀ y, 0 < n y) (hK : ∀ a, Measurable fun y => (K y).1 a)
    (hev : ∀ f : V, Measurable fun y => f.1 (ev y)) (hKb : ∀ a, ∃ C, ∀ y, ‖(K y).1 a‖ ≤ C * n y)
    (hevb : ∀ f : V, ∃ C, ∀ y, ‖f.1 (ev y)‖ * n y ≤ C)
    (hrep : ∀ (f : V) a, ∫ y, (K y).1 a * f.1 (ev y) ∂ν = f.1 a) (φ : Module.Dual ℂ V) :
    Good ν V K ev n φ := by
  have hint : ∀ ψ : Module.Dual ℂ V, Good ν V K ev n ψ → ∀ f : V,
      Integrable (fun y => ψ (K y) * f.1 (ev y)) ν := by
    intro ψ hψ f
    obtain ⟨C, hC⟩ := hψ.2.1
    obtain ⟨D, hD⟩ := hevb f
    exact integrable_mul ν hn hψ.1 (hev f) C D hC hD
  have hadd : ∀ φ₁ φ₂, Good ν V K ev n φ₁ → Good ν V K ev n φ₂ → Good ν V K ev n (φ₁ + φ₂) := by
    intro φ₁ φ₂ h₁ h₂
    obtain ⟨C₁, hC₁⟩ := h₁.2.1
    obtain ⟨C₂, hC₂⟩ := h₂.2.1
    refine ⟨h₁.1.add h₂.1, ⟨C₁ + C₂, fun y => ?_⟩, fun f => ?_⟩
    · rw [LinearMap.add_apply, add_mul]
      exact (norm_add_le _ _).trans (add_le_add (hC₁ y) (hC₂ y))
    · simp only [LinearMap.add_apply, add_mul]
      rw [integral_add (hint φ₁ h₁ f) (hint φ₂ h₂ f), h₁.2.2 f, h₂.2.2 f]
  have hzero : Good ν V K ev n 0 := by
    refine ⟨?_, ⟨0, fun y => ?_⟩, fun f => ?_⟩
    · simp
    · simp
    · simp
  have hsmul : ∀ (c : ℂ) φ, Good ν V K ev n φ → Good ν V K ev n (c • φ) := by
    intro c φ h
    obtain ⟨C, hC⟩ := h.2.1
    refine ⟨h.1.const_mul c, ⟨‖c‖ * C, fun y => ?_⟩, fun f => ?_⟩
    · rw [LinearMap.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hC y) (norm_nonneg c)
    · simp only [LinearMap.smul_apply, smul_eq_mul, mul_assoc]
      rw [integral_const_mul, h.2.2 f]
  obtain ⟨Sg, hSg⟩ : ∃ Sg : Submodule ℂ (Module.Dual ℂ V), ∀ ψ, ψ ∈ Sg ↔ Good ν V K ev n ψ :=
    ⟨{ carrier := {ψ | Good ν V K ev n ψ}
       add_mem' := fun {a b} ha hb => hadd a b ha hb
       zero_mem' := hzero
       smul_mem' := fun c ψ h => hsmul c ψ h }, fun _ => Iff.rfl⟩
  have hev' : ∀ a, Good ν V K ev n (evl V a) := by
    intro a
    refine ⟨?_, ?_, fun f => ?_⟩
    · simpa only [evl_apply] using hK a
    · simpa only [evl_apply] using hKb a
    · simpa only [evl_apply] using hrep f a
  have htop : Sg = ⊤ := by
    rw [eq_top_iff, ← span_evl V, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact (hSg _).mpr (hev' a)
  exact (hSg φ).mp (by rw [htop]; exact Submodule.mem_top)

/- English proof (translation)
Introduce `A Y _ ν _ V _ T K ev n _ hn hK hev hKb hevb hrep`. Establish `hgood : ∀ φ : Module.Dual ℂ V, Good ν V K ev n φ` using `good_all ν V K ev n hn hK hev hKb hevb hrep`. Set `b` to `Module.finBasis ℂ V`. Establish `hexp : ∀ y, (T (K y)).1 (ev y) = ∑ i, b.coord i (K y) * (T (b i)).1 (ev y)`. Introduce `y`.

Establish `e : T (K y) = ∑ i, b.repr (K y) i • T (b i)` using `by conv_lhs => rw [← b.sum_repr (K y)]`. Rewrite using `[map_sum]`. Simplify using `only [map_smul]`. Rewrite using `[e]`. Simplify using `[Module.Basis.coord_apply]`.

Establish `hmeas : Measurable fun y => (T (K y)).1 (ev y)`. Repeatedly rewrite using `[hexp]`. Conclude with `Finset.measurable_sum _ fun i _ => (hgood (b.coord i)).1.mul (hev (T (b i)))`. Establish `hbd : ∃ C, ∀ y, ‖(T (K y)).1 (ev y)‖ ≤ C` using `by choose Cs hCs using fun i => (hgood (b.coord i)).2.1 choose Ds hDs using fun i => hevb (T (b i))`. Use `⟨∑ i, Cs i * Ds i, fun y => ?_⟩` and prove the remaining obligations.

Rewrite using `[hexp]`. Conclude with `(norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => bound_mul hn (Cs i) (Ds i) (hCs i) (hDs i) y)`. Establish `hintg : ∀ i, Integrable (fun y => b.coord i (K y) * (T (b i)).1 (ev y)) ν`. Introduce `i`. Take `⟨C, hC⟩` from `(hgood (b.coord i)).2.1`.

Take `⟨D, hD⟩` from `hevb (T (b i))`. Conclude with `integrable_mul ν hn (hgood (b.coord i)).1 (hev (T (b i))) C D hC hD`. Use `⟨hmeas, hbd, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.trace_eq_matrix_trace ℂ b T, Matrix.trace]`. Repeatedly rewrite using `[hexp]`.

Rewrite using `[integral_finsetSum _ fun i _ => hintg i]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[(hgood (b.coord i)).2.2 (T (b i))]`. Simplify using `[LinearMap.toMatrix_apply, Module.Basis.coord_apply]`.
-/
theorem main : UpperTheory.Esk.LinTr := by
  intro A Y _ ν _ V _ T K ev n _ hn hK hev hKb hevb hrep
  have hgood : ∀ φ : Module.Dual ℂ V, Good ν V K ev n φ :=
    good_all ν V K ev n hn hK hev hKb hevb hrep
  let b := Module.finBasis ℂ V
  have hexp : ∀ y, (T (K y)).1 (ev y) = ∑ i, b.coord i (K y) * (T (b i)).1 (ev y) := by
    intro y
    have e : T (K y) = ∑ i, b.repr (K y) i • T (b i) := by
      conv_lhs => rw [← b.sum_repr (K y)]
      rw [map_sum]
      simp only [map_smul]
    rw [e]
    simp [Module.Basis.coord_apply]
  have hmeas : Measurable fun y => (T (K y)).1 (ev y) := by
    simp_rw [hexp]
    exact Finset.measurable_sum _ fun i _ => (hgood (b.coord i)).1.mul (hev (T (b i)))
  have hbd : ∃ C, ∀ y, ‖(T (K y)).1 (ev y)‖ ≤ C := by
    choose Cs hCs using fun i => (hgood (b.coord i)).2.1
    choose Ds hDs using fun i => hevb (T (b i))
    refine ⟨∑ i, Cs i * Ds i, fun y => ?_⟩
    rw [hexp]
    exact (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun i _ => bound_mul hn (Cs i) (Ds i) (hCs i) (hDs i) y)
  have hintg : ∀ i, Integrable (fun y => b.coord i (K y) * (T (b i)).1 (ev y)) ν := by
    intro i
    obtain ⟨C, hC⟩ := (hgood (b.coord i)).2.1
    obtain ⟨D, hD⟩ := hevb (T (b i))
    exact integrable_mul ν hn (hgood (b.coord i)).1 (hev (T (b i))) C D hC hD
  refine ⟨hmeas, hbd, ?_⟩
  rw [LinearMap.trace_eq_matrix_trace ℂ b T, Matrix.trace]
  simp_rw [hexp]
  rw [integral_finsetSum _ fun i _ => hintg i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(hgood (b.coord i)).2.2 (T (b i))]
  simp [LinearMap.toMatrix_apply, Module.Basis.coord_apply]

end UpperTheory.Esk.LinearTraceLemmas

/- English proof (translation)
Conclude with `UpperTheory.Esk.LinearTraceLemmas.main`.
-/
theorem UpperTheory.Esk.pf_LinTr : UpperTheory.Esk.LinTr := by
  exact UpperTheory.Esk.LinearTraceLemmas.main
