import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Rewrite using `[HT.LatBasic.expand_dual z]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Establish `hk` using `h (RingOfIntegers.basis E k)`. Rewrite using `[integralBasis_apply, mul_comm, ← RingOfIntegers.coe_eq_algebraMap, hk, zero_smul]`.
-/
theorem eq_zero_of_trace_pairing_zero {z : E} (h : ∀ c : 𝓞 E, Algebra.trace ℚ E ((c : E) * z) = 0) : z = 0 := by
  rw [HT.LatBasic.expand_dual z]
  refine Finset.sum_eq_zero fun k _ => ?_
  have hk := h (RingOfIntegers.basis E k)
  rw [integralBasis_apply, mul_comm, ← RingOfIntegers.coe_eq_algebraMap, hk, zero_smul]

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Conclude with `eq_zero_of_trace_pairing_zero fun c => by rw [mul_sub, map_sub, h c, sub_self]`.
-/
theorem eq_of_trace_pairing_eq {z w : E} (h : ∀ c : 𝓞 E, Algebra.trace ℚ E ((c : E) * z) = Algebra.trace ℚ E ((c : E) * w)) :
    z = w := by
  rw [← sub_eq_zero]
  exact eq_zero_of_trace_pairing_zero fun c => by rw [mul_sub, map_sub, h c, sub_self]

/- English proof (translation)
Establish `e : ∀ k, Algebra.trace ℚ E ((a : E) * ((D.EF (RingOfIntegers.basis E k • x) y : E) * HT.dualInt E k)) = (D.EF (RingOfIntegers.basis E k • x) y : ℚ) * ((RingOfIntegers.basis E).repr a k : ℚ)`. Introduce `k`. Rewrite using `[show (a : E) * ((D.EF (RingOfIntegers.basis E k • x) y : E) * HT.dualInt E k) = (D.EF (RingOfIntegers.basis E k • x) y : ℤ) • (HT.dualInt E k * (a : E)) by rw [zsmul_eq_mul]; ring, map_zsmul, zsmul_eq_mul, HT.LatBasic.repr_eq_trace]`. Simplify using `only [sesq, Finset.mul_sum, map_sum, e]`. Establish `ha : a • x = ∑ k, ((RingOfIntegers.basis E).repr a k : ℤ) • (RingOfIntegers.basis E k • x)` using `by conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr a]`.

Rewrite using `[Finset.sum_smul]`. Conclude with `Finset.sum_congr rfl fun k _ => smul_assoc _ _ _`. Rewrite using `[ha, map_sum, LinearMap.sum_apply]`. Use `push_cast`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[map_zsmul, LinearMap.smul_apply, smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem trace_mul_sesq_eq_form (D : Datum H) (a : 𝓞 E) (x y : D.La) :
    Algebra.trace ℚ E ((a : E) * sesq D x y) = (D.EF (a • x) y : ℚ) := by
  classical
  have e : ∀ k, Algebra.trace ℚ E ((a : E) * ((D.EF (RingOfIntegers.basis E k • x) y : E) * HT.dualInt E k)) =
      (D.EF (RingOfIntegers.basis E k • x) y : ℚ) * ((RingOfIntegers.basis E).repr a k : ℚ) := by
    intro k
    rw [show (a : E) * ((D.EF (RingOfIntegers.basis E k • x) y : E) * HT.dualInt E k) =
        (D.EF (RingOfIntegers.basis E k • x) y : ℤ) • (HT.dualInt E k * (a : E)) by rw [zsmul_eq_mul]; ring,
      map_zsmul, zsmul_eq_mul, HT.LatBasic.repr_eq_trace]
  simp only [sesq, Finset.mul_sum, map_sum, e]
  have ha : a • x = ∑ k, ((RingOfIntegers.basis E).repr a k : ℤ) • (RingOfIntegers.basis E k • x) := by
    conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr a]
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun k _ => smul_assoc _ _ _
  rw [ha, map_sum, LinearMap.sum_apply]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, LinearMap.smul_apply, smul_eq_mul]
  push_cast
  ring

/- English proof (translation)
Establish `h` using `D.alt (x + y)`. Simplify using `only [map_add, LinearMap.add_apply, D.alt x, D.alt y, zero_add, add_zero] at h`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem Datum_EF_antisymm (D : Datum H) (x y : D.La) : D.EF y x = -D.EF x y := by
  have h := D.alt (x + y)
  simp only [map_add, LinearMap.add_apply, D.alt x, D.alt y, zero_add, add_zero] at h
  linarith

/- English proof (translation)
Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Use `show ((H.bar (H.bar a) : 𝓞 E) : E) = (a : E)`. Rewrite using `[H.bar_eq, H.bar_eq]`. Conclude with `IsCMField.complexConj_apply_apply E (a : E)`.
-/
theorem Host_bar_bar (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.coe_injective
  show ((H.bar (H.bar a) : 𝓞 E) : E) = (a : E)
  rw [H.bar_eq, H.bar_eq]
  exact IsCMField.complexConj_apply_apply E (a : E)

/- English proof (translation)
Set `σ : E ≃ₐ[ℚ] E` to `(IsCMField.complexConj E).restrictScalars ℚ`. Establish `hσ : ∀ w, σ w = IsCMField.complexConj E w` using `fun _ => rfl`. Rewrite using `[← hσ, Algebra.trace_apply, Algebra.trace_apply]`. Establish `: Algebra.lmul ℚ E (σ z) = σ.toLinearEquiv.conj (Algebra.lmul ℚ E z)`. Use extensionality with `w`.

Use `show σ z * w = σ (z * σ.symm w)`. Rewrite using `[map_mul, AlgEquiv.apply_symm_apply]`. Rewrite using `[this, LinearMap.trace_conj']`.
-/
theorem trace_complexConj (z : E) :
    Algebra.trace ℚ E (IsCMField.complexConj E z) = Algebra.trace ℚ E z := by
  let σ : E ≃ₐ[ℚ] E := (IsCMField.complexConj E).restrictScalars ℚ
  have hσ : ∀ w, σ w = IsCMField.complexConj E w := fun _ => rfl
  rw [← hσ, Algebra.trace_apply, Algebra.trace_apply]
  have : Algebra.lmul ℚ E (σ z) = σ.toLinearEquiv.conj (Algebra.lmul ℚ E z) := by
    ext w
    show σ z * w = σ (z * σ.symm w)
    rw [map_mul, AlgEquiv.apply_symm_apply]
  rw [this, LinearMap.trace_conj']

/- English proof (translation)
Use `⟨trace_mul_sesq_eq_form D, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x x' y`. Simplify using `only [sesq, smul_add, map_add, LinearMap.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]`. Introduce `x y y'`. Simplify using `only [sesq, map_add, Int.cast_add, add_mul, Finset.sum_add_distrib]`.

Introduce `a x y`. Apply `eq_of_trace_pairing_eq` to reduce the goal to its premises. Introduce `c`. Rewrite using `[trace_mul_sesq_eq_form, ← _root_.mul_assoc, ← map_mul, trace_mul_sesq_eq_form, smul_smul]`. Introduce `a x y`.

Apply `eq_of_trace_pairing_eq` to reduce the goal to its premises. Introduce `c`. Establish `h1 : D.EF (c • x) (a • y) = D.EF ((H.bar a * c) • x) y` using `by conv_lhs => rw [← Host_bar_bar (H := H) a]`. Rewrite using `[← D.adj, smul_smul]`. Rewrite using `[trace_mul_sesq_eq_form, h1, ← _root_.mul_assoc, mul_comm (c : E), ← H.bar_eq, ← map_mul, trace_mul_sesq_eq_form]`.

Introduce `x y`. Apply `eq_of_trace_pairing_eq` to reduce the goal to its premises. Introduce `c`. Establish `h1 : D.EF (c • y) x = -D.EF ((H.bar c) • x) y`. Rewrite using `[Datum_EF_antisymm, D.adj, Host_bar_bar]`.

Rewrite using `[trace_mul_sesq_eq_form, h1, mul_neg, map_neg, Int.cast_neg, neg_inj]`. Establish `h2 : (c : E) * IsCMField.complexConj E (sesq D x y) = IsCMField.complexConj E (((H.bar c : 𝓞 E) : E) * sesq D x y)`. Rewrite using `[map_mul, H.bar_eq, IsCMField.complexConj_apply_apply]`. Rewrite using `[h2, trace_complexConj, trace_mul_sesq_eq_form]`. Introduce `δ hδ x y`.

Establish `hdual : sesq D x y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)`. Rewrite using `[FractionalIdeal.mem_dual (@one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 E)) E) _ _ _)]`. Introduce `c hc`. Take `⟨c, rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 hc`. Use `⟨D.EF (c • x) y, ?_⟩` and prove the remaining obligations.

Rewrite using `[Algebra.traceForm_apply, mul_comm, ← RingOfIntegers.coe_eq_algebraMap, trace_mul_sesq_eq_form]`. Simplify using the standard rewrite rules. Establish `hmul : (δ : E) * sesq D x y ∈ ((differentIdeal ℤ (𝓞 E) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * FractionalIdeal.dual ℤ ℚ 1)` using `FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).2 ⟨δ, hδ, rfl⟩) hdual`. Rewrite `hmul` using `[coeIdeal_differentIdeal ℤ ℚ, inv_mul_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ (@one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 E)) E) _ _ _))]`. Take `⟨b, hb⟩` from `(FractionalIdeal.mem_one_iff _).1 hmul`.

Conclude with `⟨b, hb.symm⟩`.
-/
theorem sesq_sesquilinear_properties (D : Datum H) :
    (∀ (a : 𝓞 E) x y, Algebra.trace ℚ E ((a : E) * sesq D x y) = (D.EF (a • x) y : ℚ)) ∧
      (∀ x x' y, sesq D (x + x') y = sesq D x y + sesq D x' y) ∧
      (∀ x y y', sesq D x (y + y') = sesq D x y + sesq D x y') ∧
      (∀ (a : 𝓞 E) x y, sesq D (a • x) y = a * sesq D x y) ∧
      (∀ (a : 𝓞 E) x y, sesq D x (a • y) = IsCMField.complexConj E (a : E) * sesq D x y) ∧
      (∀ x y, sesq D y x = -IsCMField.complexConj E (sesq D x y)) ∧
      ∀ δ ∈ differentIdeal ℤ (𝓞 E), ∀ x y, ∃ b : 𝓞 E, (δ : E) * sesq D x y = b := by
  refine ⟨trace_mul_sesq_eq_form D, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x x' y
    simp only [sesq, smul_add, map_add, LinearMap.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]
  · intro x y y'
    simp only [sesq, map_add, Int.cast_add, add_mul, Finset.sum_add_distrib]
  · intro a x y
    apply eq_of_trace_pairing_eq
    intro c
    rw [trace_mul_sesq_eq_form, ← _root_.mul_assoc, ← map_mul, trace_mul_sesq_eq_form, smul_smul]
  · intro a x y
    apply eq_of_trace_pairing_eq
    intro c
    have h1 : D.EF (c • x) (a • y) = D.EF ((H.bar a * c) • x) y := by
      conv_lhs => rw [← Host_bar_bar (H := H) a]
      rw [← D.adj, smul_smul]
    rw [trace_mul_sesq_eq_form, h1, ← _root_.mul_assoc, mul_comm (c : E), ← H.bar_eq, ← map_mul, trace_mul_sesq_eq_form]
  · intro x y
    apply eq_of_trace_pairing_eq
    intro c
    have h1 : D.EF (c • y) x = -D.EF ((H.bar c) • x) y := by
      rw [Datum_EF_antisymm, D.adj, Host_bar_bar]
    rw [trace_mul_sesq_eq_form, h1, mul_neg, map_neg, Int.cast_neg, neg_inj]
    have h2 : (c : E) * IsCMField.complexConj E (sesq D x y) =
        IsCMField.complexConj E (((H.bar c : 𝓞 E) : E) * sesq D x y) := by
      rw [map_mul, H.bar_eq, IsCMField.complexConj_apply_apply]
    rw [h2, trace_complexConj, trace_mul_sesq_eq_form]
  · intro δ hδ x y
    have hdual : sesq D x y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
      rw [FractionalIdeal.mem_dual (@one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 E)) E) _ _ _)]
      intro c hc
      obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hc
      refine ⟨D.EF (c • x) y, ?_⟩
      rw [Algebra.traceForm_apply, mul_comm, ← RingOfIntegers.coe_eq_algebraMap, trace_mul_sesq_eq_form]
      simp
    have hmul : (δ : E) * sesq D x y ∈ ((differentIdeal ℤ (𝓞 E) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) *
        FractionalIdeal.dual ℤ ℚ 1) :=
      FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).2 ⟨δ, hδ, rfl⟩) hdual
    rw [coeIdeal_differentIdeal ℤ ℚ, inv_mul_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ (@one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 E)) E) _ _ _))] at hmul
    obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).1 hmul
    exact ⟨b, hb.symm⟩

end GlobalTheory.CompanionTheory.Ar.Fl

namespace PositivityTheory.Xgf

/- English proof (translation)
Introduce `_ _ _ _ _ D` and use `GlobalTheory.CompanionTheory.Ar.Fl.sesq_sesquilinear_properties D`.
-/
theorem sesq_sesquilinear_skew_hermitian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), (∀ (a : 𝓞 E) x y, Algebra.trace ℚ E ((a : E) * sesq D x y) = (D.EF (a • x) y : ℚ)) ∧ (∀ x x' y, sesq D (x + x') y = sesq D x y + sesq D x' y) ∧ (∀ x y y', sesq D x (y + y') = sesq D x y + sesq D x y') ∧ (∀ (a : 𝓞 E) x y, sesq D (a • x) y = a * sesq D x y) ∧ (∀ (a : 𝓞 E) x y, sesq D x (a • y) = IsCMField.complexConj E (a : E) * sesq D x y) ∧ (∀ x y, sesq D y x = -IsCMField.complexConj E (sesq D x y)) ∧ ∀ δ ∈ differentIdeal ℤ (𝓞 E), ∀ x y, ∃ b : 𝓞 E, (δ : E) * sesq D x y = b :=
  fun _ _ _ _ _ D => GlobalTheory.CompanionTheory.Ar.Fl.sesq_sesquilinear_properties D

end PositivityTheory.Xgf
