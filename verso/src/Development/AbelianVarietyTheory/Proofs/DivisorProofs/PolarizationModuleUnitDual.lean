import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex

namespace GlobalTheory.PolModLattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def altForm (x y : E) : E := x * bar y - bar x * y

def formSpan (L : Submodule (OF E) E) : Submodule (OF E) E :=
  Submodule.span (OF E) {w | ∃ x ∈ L, ∃ y ∈ L, w = altForm x y}

variable (E) in

def invDiff : Submodule (OF E) E where
  carrier := {v | ∃ w : maximalRealSubfield E, (w : E) = v ∧
    ∀ a : OF E, ∃ n : ℤ, Algebra.trace ℚ (maximalRealSubfield E) (w * (a : maximalRealSubfield E)) = n}
  zero_mem' := ⟨0, by simp, fun a => ⟨0, by simp⟩⟩
  add_mem' := by
    rintro _ _ ⟨w, rfl, hw⟩ ⟨w', rfl, hw'⟩
    refine ⟨w + w', by simp, fun a => ?_⟩
    obtain ⟨m, hm⟩ := hw a
    obtain ⟨n, hn⟩ := hw' a
    exact ⟨m + n, by rw [add_mul, map_add, hm, hn]; push_cast; rfl⟩
  smul_mem' := by
    rintro c _ ⟨w, rfl, hw⟩
    refine ⟨(c : maximalRealSubfield E) * w, ?_, fun a => ?_⟩
    · rw [Algebra.smul_def]; rfl
    · obtain ⟨n, hn⟩ := hw (c * a)
      exact ⟨n, by rw [← hn]; congr 1; push_cast; ring⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_OF (a : OF E) : (((a : maximalRealSubfield E)) : E) = algebraMap (OF E) E a := rfl

/- English proof (translation)
The claim follows from `IsCMField.complexConj_apply_eq_self E w`.
-/
theorem bar_real (w : maximalRealSubfield E) : bar (w : E) = w := IsCMField.complexConj_apply_eq_self E w

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨v, (IsCMField.complexConj_eq_self_iff E v).1 h⟩, rfl⟩`.
-/
theorem real_of_bar {v : E} (h : bar v = v) : ∃ w : maximalRealSubfield E, (w : E) = v :=
  ⟨⟨v, (IsCMField.complexConj_eq_self_iff E v).1 h⟩, rfl⟩

/- English proof (translation)
Rewrite using `[Algebra.smul_def, Algebra.smul_def, bar, map_mul, ← bar, ← bar, ← coe_OF, bar_real]`.
-/
theorem bar_smul (a : OF E) (x : E) : bar (a • x) = a • bar x := by
  rw [Algebra.smul_def, Algebra.smul_def, bar, map_mul, ← bar, ← bar, ← coe_OF, bar_real]

/- English proof (translation)
Simplify using `only [altForm, bar, map_sub, map_mul, IsCMField.complexConj_apply_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem altForm_bar (x y : E) : bar (altForm x y) = - altForm x y := by
  simp only [altForm, bar, map_sub, map_mul, IsCMField.complexConj_apply_apply]; ring

open Classical in
/- English proof (translation)
Establish `hc : Nat.card (E ≃ₐ[maximalRealSubfield E] E) = 2` using `(Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E) ▸ IsGalois.card_aut_eq_finrank _ E`. Take `⟨τ, hτ, hu⟩` from `(Nat.card_eq_two_iff' 1).1 hc`. Use extensionality with `σ`. Simplify using `only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]`. Distinguish the cases in `h : σ = 1`.

Conclude with `Or.inl h`. Conclude with `Or.inr (by rw [hu σ h, hu _ (IsCMField.complexConj_ne_one E)])`.
-/
theorem univ_aut : (Finset.univ : Finset (E ≃ₐ[maximalRealSubfield E] E)) = {1, IsCMField.complexConj E} := by
  have hc : Nat.card (E ≃ₐ[maximalRealSubfield E] E) = 2 :=
    (Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E) ▸ IsGalois.card_aut_eq_finrank _ E
  obtain ⟨τ, hτ, hu⟩ := (Nat.card_eq_two_iff' 1).1 hc
  ext σ
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  by_cases h : σ = 1
  · exact Or.inl h
  · exact Or.inr (by rw [hu σ h, hu _ (IsCMField.complexConj_ne_one E)])

/- English proof (translation)
Rewrite using `[← Algebra.trace_trace (S := maximalRealSubfield E)]`. Use `congr 1`. Apply `FaithfulSMul.algebraMap_injective (maximalRealSubfield E) E` to reduce the goal to its premises. Rewrite using `[trace_eq_sum_automorphisms, univ_aut, Finset.sum_pair (Ne.symm (IsCMField.complexConj_ne_one E))]`. Simplify using `only [AlgEquiv.one_apply]`.

Conclude with `hw.symm`.
-/
theorem trace_eq (u : E) (w : maximalRealSubfield E) (hw : (w : E) = u + bar u) :
    Algebra.trace ℚ E u = Algebra.trace ℚ (maximalRealSubfield E) w := by
  rw [← Algebra.trace_trace (S := maximalRealSubfield E)]
  congr 1
  apply FaithfulSMul.algebraMap_injective (maximalRealSubfield E) E
  classical
  rw [trace_eq_sum_automorphisms, univ_aut, Finset.sum_pair (Ne.symm (IsCMField.complexConj_ne_one E))]
  simp only [AlgEquiv.one_apply]
  exact hw.symm

open scoped nonZeroDivisors in
/- English proof (translation)
Set `K` to `maximalRealSubfield E`. Set `f : K →ₐ[OF E] E` to `IsScalarTower.toAlgHom (OF E) K E`. Use `haveI : NeZero (1 : FractionalIdeal (OF E)⁰ K) := ⟨one_ne_zero⟩`. Set `𝔡 : FractionalIdeal (OF E)⁰ K` to `FractionalIdeal.dual ℤ ℚ 1`. Establish `h0 : 𝔡 ≠ 0` using `FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero`.

Establish `hmul : (𝔡 : Submodule (OF E) K) * ((𝔡⁻¹ : FractionalIdeal (OF E)⁰ K) : Submodule (OF E) K) = 1`. Rewrite using `[← FractionalIdeal.coe_mul, mul_inv_cancel₀ h0, FractionalIdeal.coe_one]`. Establish `heq : invDiff E = (𝔡 : Submodule (OF E) K).map f.toLinearMap`. Use extensionality with `v`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨w, rfl, hw⟩`. Use `⟨w, ?_, rfl⟩` and prove the remaining obligations. Use `show w ∈ 𝔡`. Rewrite using `[FractionalIdeal.mem_dual one_ne_zero]`. Introduce `a ha`.

Take `⟨b, rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 ha`. Take `⟨n, hn⟩` from `hw b`. Conclude with `⟨n, by rw [Algebra.traceForm_apply]; simpa using hn.symm⟩`. Introduce and unpack `⟨w, hw, rfl⟩`. Use `⟨w, rfl, fun a => ?_⟩` and prove the remaining obligations.

Establish `hw' : w ∈ 𝔡` using `hw`. Rewrite `hw'` using `[FractionalIdeal.mem_dual one_ne_zero]`. Take `⟨n, hn⟩` from `hw' (algebraMap (OF E) K a) ((FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩)`. Conclude with `⟨n, by rw [Algebra.traceForm_apply] at hn; simpa using hn.symm⟩`. Use `⟨⟨invDiff E, ((𝔡⁻¹ : FractionalIdeal (OF E)⁰ K) : Submodule (OF E) K).map f.toLinearMap, ?_, ?_⟩, rfl⟩` and prove the remaining obligations.

Rewrite using `[heq, ← Submodule.map_mul, hmul, Submodule.map_one]`. Rewrite using `[heq, ← Submodule.map_mul, mul_comm, hmul, Submodule.map_one]`.
-/
theorem isUnit_invDiff : IsUnit (invDiff E) := by
  let K := maximalRealSubfield E
  let f : K →ₐ[OF E] E := IsScalarTower.toAlgHom (OF E) K E
  haveI : NeZero (1 : FractionalIdeal (OF E)⁰ K) := ⟨one_ne_zero⟩
  let 𝔡 : FractionalIdeal (OF E)⁰ K := FractionalIdeal.dual ℤ ℚ 1
  have h0 : 𝔡 ≠ 0 := FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero
  have hmul : (𝔡 : Submodule (OF E) K) * ((𝔡⁻¹ : FractionalIdeal (OF E)⁰ K) : Submodule (OF E) K) = 1 := by
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ h0, FractionalIdeal.coe_one]
  have heq : invDiff E = (𝔡 : Submodule (OF E) K).map f.toLinearMap := by
    ext v
    constructor
    · rintro ⟨w, rfl, hw⟩
      refine ⟨w, ?_, rfl⟩
      show w ∈ 𝔡
      rw [FractionalIdeal.mem_dual one_ne_zero]
      intro a ha
      obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
      obtain ⟨n, hn⟩ := hw b
      exact ⟨n, by rw [Algebra.traceForm_apply]; simpa using hn.symm⟩
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w, rfl, fun a => ?_⟩
      have hw' : w ∈ 𝔡 := hw
      rw [FractionalIdeal.mem_dual one_ne_zero] at hw'
      obtain ⟨n, hn⟩ := hw' (algebraMap (OF E) K a) ((FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩)
      exact ⟨n, by rw [Algebra.traceForm_apply] at hn; simpa using hn.symm⟩
  refine ⟨⟨invDiff E, ((𝔡⁻¹ : FractionalIdeal (OF E)⁰ K) : Submodule (OF E) K).map f.toLinearMap, ?_, ?_⟩, rfl⟩
  · rw [heq, ← Submodule.map_mul, hmul, Submodule.map_one]
  · rw [heq, ← Submodule.map_mul, mul_comm, hmul, Submodule.map_one]

def imagPart (E : Type) [Field E] [NumberField E] [IsCMField E] : Submodule (OF E) E where
  carrier := {j | bar j = -j}
  zero_mem' := by simp [bar]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, bar, map_add] at ha hb ⊢
    rw [ha, hb]; ring
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [bar_smul, ha, smul_neg]

/- English proof (translation)
Rewrite using `[formSpan, Submodule.span_le]`. Introduce and unpack `_ ⟨x, -, y, -, rfl⟩`. Conclude with `altForm_bar x y`.
-/
theorem formSpan_le_imag (L : Submodule (OF E) E) : formSpan L ≤ imagPart E := by
  rw [formSpan, Submodule.span_le]
  rintro _ ⟨x, -, y, -, rfl⟩
  exact altForm_bar x y

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x : E, bar x ≠ x := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `IsCMField.complexConj_ne_one E (AlgEquiv.ext fun x => h x)`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 E) x`.

Establish `key : ∃ c : 𝓞 E, bar (c : E) ≠ c`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Apply `hx` to reduce the goal to its premises. Simplify using `only [bar, map_div₀] at h ⊢`.

Rewrite using `[h a, h b]`. Take `⟨c, hc⟩` from `key`. Use `⟨c - IsCMField.ringOfIntegersComplexConj E c, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [map_sub, IsCMField.coe_ringOfIntegersComplexConj]`. Conclude with `sub_ne_zero.2 (Ne.symm hc)`.

Simplify using `only [map_sub, IsCMField.coe_ringOfIntegersComplexConj, bar, IsCMField.complexConj_apply_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_imag_int : ∃ δ : 𝓞 E, (δ : E) ≠ 0 ∧ bar (δ : E) = -(δ : E) := by
  obtain ⟨x, hx⟩ : ∃ x : E, bar x ≠ x := by
    by_contra h
    push_neg at h
    exact IsCMField.complexConj_ne_one E (AlgEquiv.ext fun x => h x)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  have key : ∃ c : 𝓞 E, bar (c : E) ≠ c := by
    by_contra h
    push_neg at h
    apply hx
    simp only [bar, map_div₀] at h ⊢
    rw [h a, h b]
  obtain ⟨c, hc⟩ := key
  refine ⟨c - IsCMField.ringOfIntegersComplexConj E c, ?_, ?_⟩
  · simp only [map_sub, IsCMField.coe_ringOfIntegersComplexConj]
    exact sub_ne_zero.2 (Ne.symm hc)
  · simp only [map_sub, IsCMField.coe_ringOfIntegersComplexConj, bar, IsCMField.complexConj_apply_apply]
    ring

/- English proof (translation)
Introduce `w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem w hw`. Take `⟨x, hx, y, hy, rfl⟩` from `hw`. Establish `hb : ∀ t : E, IsIntegral ℤ t → IsIntegral ℤ (bar t)` using `fun t ht => ht.map ((IsCMField.complexConj E).toAlgHom.restrictScalars ℤ)`.

Establish `e : (N : E) ^ 2 * altForm x y = (N * x) * bar (N * y) - bar (N * x) * (N * y)`. Simplify using `only [altForm, bar, map_mul, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `((hN x hx).mul (hb _ (hN y hy))).sub ((hb _ (hN x hx)).mul (hN y hy))`.

Consider the case `zero => simpa using isIntegral_zero`. Consider the case `add a b _ _ ha hb => rw [mul_add]`. Conclude with `ha.add hb`. Consider the case `smul c a _ ha`. Rewrite using `[Algebra.smul_def, mul_left_comm]`.

Conclude with `(c.2.map (IsScalarTower.toAlgHom ℤ (maximalRealSubfield E) E)).mul ha`.
-/
theorem isIntegral_formSpan (L : Submodule (OF E) E) (N : ℕ) (hN : ∀ x ∈ L, IsIntegral ℤ ((N : E) * x)) :
    ∀ w ∈ formSpan L, IsIntegral ℤ ((N : E) ^ 2 * w) := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hw
    have hb : ∀ t : E, IsIntegral ℤ t → IsIntegral ℤ (bar t) := fun t ht =>
      ht.map ((IsCMField.complexConj E).toAlgHom.restrictScalars ℤ)
    have e : (N : E) ^ 2 * altForm x y = (N * x) * bar (N * y) - bar (N * x) * (N * y) := by
      simp only [altForm, bar, map_mul, map_natCast]; ring
    rw [e]
    exact ((hN x hx).mul (hb _ (hN y hy))).sub ((hb _ (hN x hx)).mul (hN y hy))
  | zero => simpa using isIntegral_zero
  | add a b _ _ ha hb => rw [mul_add]; exact ha.add hb
  | smul c a _ ha =>
    rw [Algebra.smul_def, mul_left_comm]
    exact (c.2.map (IsScalarTower.toAlgHom ℤ (maximalRealSubfield E) E)).mul ha

open scoped nonZeroDivisors in
/- English proof (translation)
Take `⟨N, hN0, hNL, hNi⟩` from `hL`. Take `⟨δ, hδ0, hδb⟩` from `exists_imag_int (E := E)`. Set `K` to `maximalRealSubfield E`. Set `f : K →ₐ[OF E] E` to `IsScalarTower.toAlgHom (OF E) K E`. Set `g : K →ₗ[OF E] E` to `(LinearMap.mulRight (OF E) (δ : E)).comp f.toLinearMap`.

Set `IK : Submodule (OF E) K` to `(formSpan L).comap g`. Establish `hg : ∀ a : K, g a = (a : E) * δ` using `fun a => rfl`. Establish `hsplit : formSpan L = IK.map f.toLinearMap * Submodule.span (OF E) {(δ : E)}`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `w hw`.

Establish `hwi : bar w = -w` using `formSpan_le_imag L hw`. Establish `hr : bar (w / δ) = w / δ`. Simplify using `only [bar, map_div₀] at hwi hδb ⊢`. Rewrite using `[hwi, hδb, neg_div_neg_eq]`. Take `⟨a, ha⟩` from `real_of_bar hr`.

Establish `haI : a ∈ IK` using `by show g a ∈ formSpan L`. Rewrite using `[hg, ha, div_mul_cancel₀ _ hδ0]`. Conclude with `hw`. Establish `: w = f a * δ` using `by show w = (a : E) * δ`. Rewrite using `[ha, div_mul_cancel₀ _ hδ0]`.

Rewrite using `[this]`. Conclude with `Submodule.mul_mem_mul ⟨a, haI, rfl⟩ (Submodule.mem_span_singleton_self _)`. Use `Submodule.mul_le.2 fun u hu s hs => ?_` and prove the remaining obligations. Take `⟨a, ha, rfl⟩` from `hu`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hs`.

Rewrite using `[mul_smul_comm]`. Conclude with `(formSpan L).smul_mem c ha`. Establish `hδ2 : bar ((δ : E) * δ) = (δ : E) * δ`. Simplify using `only [bar, map_mul] at hδb ⊢`. Rewrite using `[hδb]`.

Expand and normalize the polynomial expressions, which then agree. Choose the witnesses or unpack the hypotheses as in `⟨d, hd⟩ : ∃ d : OF E, algebraMap (OF E) E d = (δ : E) * δ := by`. Take `⟨d, hd⟩` from `(IsCMField.RingOfIntegers.complexConj_eq_self_iff E (δ * δ)).1 (by push_cast; exact hδ2)`. Conclude with `⟨d, by rw [hd]; push_cast; rfl⟩`. Establish `hd0 : d ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hd` using `[map_zero]`. Conclude with `mul_self_ne_zero.2 hδ0 hd.symm`. Establish `hfrac : IsFractional (OF E)⁰ IK`. Use `⟨(N : OF E) ^ 2 * d, mem_nonZeroDivisors_of_ne_zero (mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hN0.ne')) hd0), ?_⟩` and prove the remaining obligations.

Introduce `a ha`. Establish `h1` using `isIntegral_formSpan L N hNi _ ha`. Rewrite `h1` using `[hg]`. Establish `h2 : IsIntegral ℤ (f (((N : OF E) ^ 2 * d) • a))`. Establish `e : f (((N : OF E) ^ 2 * d) • a) = (N : E) ^ 2 * ((a : E) * δ) * δ`.

Rewrite using `[Algebra.smul_def, map_mul, AlgHom.commutes, map_mul, map_pow, map_natCast, hd]`. Express the relevant statement in the definitionally equal form `(N : E) ^ 2 * (δ * δ) * (a : E) = _`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `h1.mul δ.2`.

Establish `h3 : IsIntegral ℤ (((N : OF E) ^ 2 * d) • a)` using `(isIntegral_algHom_iff (f.restrictScalars ℤ) f.toRingHom.injective).1 h2`. Conclude with `⟨⟨_, h3⟩, rfl⟩`. Set `𝔦 : FractionalIdeal (OF E)⁰ K` to `⟨IK, hfrac⟩`. Establish `h𝔦 : 𝔦 ≠ 0`. Introduce `h`.

Establish `hm : (-(N : K) ^ 2 - (N : K) ^ 2 : K) ∈ IK` using `by show g _ ∈ formSpan L`. Establish `hx` using `hNL 1`. Establish `hy : (N : E) * (δ : E) ∈ L` using `hNL δ`. Rewrite `hx` using `[map_one, mul_one]`. Establish `hmem : altForm (N : E) ((N : E) * (δ : E)) ∈ formSpan L` using `Submodule.subset_span ⟨_, hx, _, hy, rfl⟩`.

Use `hmem using 1` and compare the differences between its conclusion and the goal. Rewrite using `[hg]`. Simplify using `only [altForm, bar, map_mul, map_natCast] at hδb ⊢`. Rewrite using `[hδb]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `: (-(N : K) ^ 2 - (N : K) ^ 2 : K) ∈ (𝔦 : Submodule (OF E) K)` using `hm`. Rewrite `this` using `[h, FractionalIdeal.coe_zero, Submodule.mem_bot]`. Establish `hN : (N : K) ≠ 0` using `by exact_mod_cast hN0.ne'`. Rewrite `this` using `[show (-(N : K) ^ 2 - (N : K) ^ 2 : K) = -2 * (N : K) ^ 2 by ring]`.

Conclude with `(mul_ne_zero (by norm_num) (pow_ne_zero 2 hN)) this`. Establish `hmul : IK * ((𝔦⁻¹ : FractionalIdeal (OF E)⁰ K) : Submodule (OF E) K) = 1`. Rewrite using `[show IK = (𝔦 : Submodule (OF E) K) from rfl, ← FractionalIdeal.coe_mul, mul_inv_cancel₀ h𝔦, FractionalIdeal.coe_one]`. Use `⟨((𝔦⁻¹ : FractionalIdeal (OF E)⁰ K) : Submodule (OF E) K).map f.toLinearMap * Submodule.span (OF E) {(δ : E)⁻¹}, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hsplit, mul_mul_mul_comm, ← Submodule.map_mul, hmul, Submodule.map_one, Submodule.span_mul_span, Set.singleton_mul_singleton, mul_inv_cancel₀ hδ0, ← Submodule.one_eq_span, mul_one]`.

Introduce `j hj`. Establish `hle : ((𝔦⁻¹ : FractionalIdeal (OF E)⁰ K) : Submodule (OF E) K).map f.toLinearMap * Submodule.span (OF E) {(δ : E)⁻¹} ≤ imagPart E`. Use `Submodule.mul_le.2 fun u hu s hs => ?_` and prove the remaining obligations. Take `⟨a, -, rfl⟩` from `hu`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hs`.

Use `show bar _ = -_`. Rewrite using `[mul_smul_comm, bar_smul]`. Simplify using `only [bar, map_mul, map_inv₀] at hδb ⊢`. Rewrite using `[hδb]`. Establish `: IsCMField.complexConj E (f.toLinearMap a) = f.toLinearMap a` using `IsCMField.complexConj_apply_eq_self E a`.

Rewrite using `[this, inv_neg, mul_neg, smul_neg]`. Conclude with `hle hj`.
-/
theorem exists_inv (L : Submodule (OF E) E)
    (hL : ∃ N : ℕ, 0 < N ∧ (∀ x : 𝓞 E, (N : E) * algebraMap (𝓞 E) E x ∈ L) ∧ ∀ x ∈ L, IsIntegral ℤ ((N : E) * x)) :
    ∃ J : Submodule (OF E) E, formSpan L * J = 1 ∧ ∀ j ∈ J, bar j = -j := by
  obtain ⟨N, hN0, hNL, hNi⟩ := hL
  obtain ⟨δ, hδ0, hδb⟩ := exists_imag_int (E := E)
  let K := maximalRealSubfield E
  let f : K →ₐ[OF E] E := IsScalarTower.toAlgHom (OF E) K E
  let g : K →ₗ[OF E] E := (LinearMap.mulRight (OF E) (δ : E)).comp f.toLinearMap
  let IK : Submodule (OF E) K := (formSpan L).comap g
  have hg : ∀ a : K, g a = (a : E) * δ := fun a => rfl

  have hsplit : formSpan L = IK.map f.toLinearMap * Submodule.span (OF E) {(δ : E)} := by
    apply le_antisymm
    · intro w hw
      have hwi : bar w = -w := formSpan_le_imag L hw
      have hr : bar (w / δ) = w / δ := by
        simp only [bar, map_div₀] at hwi hδb ⊢
        rw [hwi, hδb, neg_div_neg_eq]
      obtain ⟨a, ha⟩ := real_of_bar hr
      have haI : a ∈ IK := by
        show g a ∈ formSpan L
        rw [hg, ha, div_mul_cancel₀ _ hδ0]
        exact hw
      have : w = f a * δ := by
        show w = (a : E) * δ
        rw [ha, div_mul_cancel₀ _ hδ0]
      rw [this]
      exact Submodule.mul_mem_mul ⟨a, haI, rfl⟩ (Submodule.mem_span_singleton_self _)
    · refine Submodule.mul_le.2 fun u hu s hs => ?_
      obtain ⟨a, ha, rfl⟩ := hu
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hs
      rw [mul_smul_comm]
      exact (formSpan L).smul_mem c ha

  have hδ2 : bar ((δ : E) * δ) = (δ : E) * δ := by
    simp only [bar, map_mul] at hδb ⊢; rw [hδb]; ring
  obtain ⟨d, hd⟩ : ∃ d : OF E, algebraMap (OF E) E d = (δ : E) * δ := by
    obtain ⟨d, hd⟩ := (IsCMField.RingOfIntegers.complexConj_eq_self_iff E (δ * δ)).1 (by
      push_cast; exact hδ2)
    exact ⟨d, by rw [hd]; push_cast; rfl⟩
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [map_zero] at hd
    exact mul_self_ne_zero.2 hδ0 hd.symm
  have hfrac : IsFractional (OF E)⁰ IK := by
    refine ⟨(N : OF E) ^ 2 * d, mem_nonZeroDivisors_of_ne_zero (mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hN0.ne')) hd0), ?_⟩
    intro a ha
    have h1 := isIntegral_formSpan L N hNi _ ha
    rw [hg] at h1
    have h2 : IsIntegral ℤ (f (((N : OF E) ^ 2 * d) • a)) := by
      have e : f (((N : OF E) ^ 2 * d) • a) = (N : E) ^ 2 * ((a : E) * δ) * δ := by
        rw [Algebra.smul_def, map_mul, AlgHom.commutes, map_mul, map_pow, map_natCast, hd]
        change (N : E) ^ 2 * (δ * δ) * (a : E) = _
        ring
      rw [e]
      exact h1.mul δ.2
    have h3 : IsIntegral ℤ (((N : OF E) ^ 2 * d) • a) :=
      (isIntegral_algHom_iff (f.restrictScalars ℤ) f.toRingHom.injective).1 h2
    exact ⟨⟨_, h3⟩, rfl⟩
  let 𝔦 : FractionalIdeal (OF E)⁰ K := ⟨IK, hfrac⟩
  have h𝔦 : 𝔦 ≠ 0 := by
    intro h
    have hm : (-(N : K) ^ 2 - (N : K) ^ 2 : K) ∈ IK := by
      show g _ ∈ formSpan L
      have hx := hNL 1
      have hy : (N : E) * (δ : E) ∈ L := hNL δ
      rw [map_one, mul_one] at hx
      have hmem : altForm (N : E) ((N : E) * (δ : E)) ∈ formSpan L := Submodule.subset_span ⟨_, hx, _, hy, rfl⟩
      convert hmem using 1
      rw [hg]
      simp only [altForm, bar, map_mul, map_natCast] at hδb ⊢
      rw [hδb]
      push_cast
      ring
    have : (-(N : K) ^ 2 - (N : K) ^ 2 : K) ∈ (𝔦 : Submodule (OF E) K) := hm
    rw [h, FractionalIdeal.coe_zero, Submodule.mem_bot] at this
    have hN : (N : K) ≠ 0 := by exact_mod_cast hN0.ne'
    rw [show (-(N : K) ^ 2 - (N : K) ^ 2 : K) = -2 * (N : K) ^ 2 by ring] at this
    exact (mul_ne_zero (by norm_num) (pow_ne_zero 2 hN)) this
  have hmul : IK * ((𝔦⁻¹ : FractionalIdeal (OF E)⁰ K) : Submodule (OF E) K) = 1 := by
    rw [show IK = (𝔦 : Submodule (OF E) K) from rfl, ← FractionalIdeal.coe_mul, mul_inv_cancel₀ h𝔦,
      FractionalIdeal.coe_one]
  refine ⟨((𝔦⁻¹ : FractionalIdeal (OF E)⁰ K) : Submodule (OF E) K).map f.toLinearMap *
    Submodule.span (OF E) {(δ : E)⁻¹}, ?_, ?_⟩
  · rw [hsplit, mul_mul_mul_comm, ← Submodule.map_mul, hmul, Submodule.map_one,
      Submodule.span_mul_span, Set.singleton_mul_singleton, mul_inv_cancel₀ hδ0, ← Submodule.one_eq_span, mul_one]
  · intro j hj
    have hle : ((𝔦⁻¹ : FractionalIdeal (OF E)⁰ K) : Submodule (OF E) K).map f.toLinearMap *
        Submodule.span (OF E) {(δ : E)⁻¹} ≤ imagPart E := by
      refine Submodule.mul_le.2 fun u hu s hs => ?_
      obtain ⟨a, -, rfl⟩ := hu
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hs
      show bar _ = -_
      rw [mul_smul_comm, bar_smul]
      simp only [bar, map_mul, map_inv₀] at hδb ⊢
      rw [hδb]
      have : IsCMField.complexConj E (f.toLinearMap a) = f.toLinearMap a := IsCMField.complexConj_apply_eq_self E a
      rw [this, inv_neg, mul_neg, smul_neg]
    exact hle hj

end GlobalTheory.PolModLattice

open GlobalTheory.PolModLattice in

/- English proof (translation)
Introduce `E _ _ _ L hL`. Take `⟨J, hIJ, hJ⟩` from `exists_inv L hL`. Establish `hJI : J * formSpan L = 1` using `by rw [mul_comm]; exact hIJ`. Establish `hM : polMod L = J * invDiff E`. Apply `le_antisymm` to reduce the goal to its premises.

Introduce `ξ hξ`. Establish `h1 : Submodule.span (OF E) {ξ} * formSpan L ≤ invDiff E`. Rewrite using `[formSpan, Submodule.span_mul_span, Submodule.span_le]`. Introduce and unpack `_ ⟨a, ha, b, ⟨x, hx, y, hy, rfl⟩, rfl⟩`. Rewrite using `[Set.mem_singleton_iff.1 ha]`.

Establish `hr : bar (ξ * altForm x y) = ξ * altForm x y`. Rewrite using `[bar, map_mul, ← bar, ← bar, altForm_bar, hξ.1]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨w, hw⟩` from `real_of_bar hr`. Use `⟨w, hw, fun c => ?_⟩` and prove the remaining obligations.

Take `⟨n, hn⟩` from `hξ.2 (c • x) (L.smul_mem c hx) y hy`. Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[← hn]`. Use `symm`. Apply `trace_eq` to reduce the goal to its premises.

Use `push_cast`. Rewrite using `[hw, coe_OF]`. Establish `hb : IsCMField.complexConj E ξ = -ξ` using `hξ.1`. Simplify using `only [altForm, bar, map_mul, IsCMField.complexConj_apply_apply, Algebra.smul_def]`. Rewrite using `[hb, show IsCMField.complexConj E (algebraMap (OF E) E c) = _ from bar_algebraMap c]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h2 : Submodule.span (OF E) {ξ} ≤ J * invDiff E` using `calc Submodule.span (OF E) {ξ} = Submodule.span (OF E) {ξ} * (formSpan L * J) := by rw [hIJ, mul_one] _ = (Submodule.span (OF E) {ξ} * formSpan L) * J := (mul_assoc _ _ _).symm _ ≤ invDiff E * J := mul_le_mul_left h1 _ _ = J * invDiff E := mul_comm _ _`. Conclude with `h2 (Submodule.mem_span_singleton_self ξ)`. Use `Submodule.mul_le.2 fun j hj v hv => ?_` and prove the remaining obligations. Take `⟨w, rfl, hw⟩` from `hv`.

Use `⟨by rw [bar, map_mul, ← bar, ← bar, hJ j hj, bar_real]; ring, fun x hx y hy => ?_⟩` and prove the remaining obligations. Establish `hm : j * altForm x y ∈ (1 : Submodule (OF E) E)` using `hJI ▸ Submodule.mul_mem_mul hj (Submodule.subset_span ⟨x, hx, y, hy, rfl⟩)`. Take `⟨a, ha⟩` from `Submodule.mem_one.1 hm`. Take `⟨n, hn⟩` from `hw a`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hn]`. Apply `trace_eq` to reduce the goal to its premises. Use `push_cast`. Rewrite using `[coe_OF, ha]`. Establish `hb : IsCMField.complexConj E j = -j` using `hJ j hj`.

Simplify using `only [altForm, bar, map_mul, IsCMField.complexConj_apply_apply]`. Rewrite using `[hb, show IsCMField.complexConj E (w : E) = w from bar_real w]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨?_, le_antisymm (polMod_mul_le L) ?_⟩` and prove the remaining obligations. Rewrite using `[hM]`.

Conclude with `(show IsUnit J from ⟨⟨J, formSpan L, hJI, hIJ⟩, rfl⟩).mul isUnit_invDiff`. Rewrite using `[hM]`. Introduce `z hz`. Establish `h1 : Submodule.span (OF E) {z} * formSpan L ≤ invDiff E * L`. Rewrite using `[formSpan, Submodule.span_mul_span, Submodule.span_le]`.

Introduce and unpack `_ ⟨a, ha, b, ⟨x, hx, y, hy, rfl⟩, rfl⟩`. Rewrite using `[Set.mem_singleton_iff.1 ha]`. Establish `key : ∀ t ∈ L, z * bar t + bar z * t ∈ invDiff E`. Introduce `t ht`. Establish `hr : bar (z * bar t + bar z * t) = z * bar t + bar z * t`.

Simplify using `only [bar, map_add, map_mul, IsCMField.complexConj_apply_apply]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨w, hw⟩` from `real_of_bar hr`. Use `⟨w, hw, fun c => ?_⟩` and prove the remaining obligations. Take `⟨n, hn⟩` from `hz (c • t) (L.smul_mem c ht)`.

Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[← hn]`. Use `symm`. Apply `trace_eq` to reduce the goal to its premises. Use `push_cast`.

Rewrite using `[hw, coe_OF, bar_smul]`. Simplify using `only [bar, map_mul, IsCMField.complexConj_apply_apply, Algebra.smul_def]`. Rewrite using `[show IsCMField.complexConj E (algebraMap (OF E) E c) = _ from bar_algebraMap c]`. Expand and normalize the polynomial expressions, which then agree. Establish `e : z * altForm x y = (z * bar y + bar z * y) * x - (z * bar x + bar z * x) * y`.

Simplify using `only [altForm]`. Expand and normalize the polynomial expressions, which then agree. Use `show z * altForm x y ∈ _`. Rewrite using `[e]`. Conclude with `sub_mem (Submodule.mul_mem_mul (key y hy) hx) (Submodule.mul_mem_mul (key x hx) hy)`.

Establish `h2 : Submodule.span (OF E) {z} ≤ J * invDiff E * L` using `calc Submodule.span (OF E) {z} = Submodule.span (OF E) {z} * (formSpan L * J) := by rw [hIJ, mul_one] _ = (Submodule.span (OF E) {z} * formSpan L) * J := (mul_assoc _ _ _).symm _ ≤ invDiff E * L * J := mul_le_mul_left h1 _ _ = J * invDiff E * L := by rw [mul_comm, mul_assoc]`. Conclude with `h2 (Submodule.mem_span_singleton_self z)`.
-/
theorem GlobalTheory.PolModLattice.polMod_isUnit_mul_eq_dual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule (OF E) E),
    (∃ N : ℕ, 0 < N ∧ (∀ x : 𝓞 E, (N : E) * algebraMap (𝓞 E) E x ∈ L) ∧ ∀ x ∈ L, IsIntegral ℤ ((N : E) * x)) →
    IsUnit (polMod L) ∧ polMod L * L = dualLat L := by
  intro E _ _ _ L hL
  obtain ⟨J, hIJ, hJ⟩ := exists_inv L hL
  have hJI : J * formSpan L = 1 := by rw [mul_comm]; exact hIJ
  have hM : polMod L = J * invDiff E := by
    apply le_antisymm
    · intro ξ hξ
      have h1 : Submodule.span (OF E) {ξ} * formSpan L ≤ invDiff E := by
        rw [formSpan, Submodule.span_mul_span, Submodule.span_le]
        rintro _ ⟨a, ha, b, ⟨x, hx, y, hy, rfl⟩, rfl⟩
        rw [Set.mem_singleton_iff.1 ha]
        have hr : bar (ξ * altForm x y) = ξ * altForm x y := by
          rw [bar, map_mul, ← bar, ← bar, altForm_bar, hξ.1]; ring
        obtain ⟨w, hw⟩ := real_of_bar hr
        refine ⟨w, hw, fun c => ?_⟩
        obtain ⟨n, hn⟩ := hξ.2 (c • x) (L.smul_mem c hx) y hy
        refine ⟨n, ?_⟩
        rw [← hn]
        symm
        apply trace_eq
        push_cast
        rw [hw, coe_OF]
        have hb : IsCMField.complexConj E ξ = -ξ := hξ.1
        simp only [altForm, bar, map_mul, IsCMField.complexConj_apply_apply, Algebra.smul_def]
        rw [hb, show IsCMField.complexConj E (algebraMap (OF E) E c) = _ from bar_algebraMap c]
        ring
      have h2 : Submodule.span (OF E) {ξ} ≤ J * invDiff E := calc
        Submodule.span (OF E) {ξ} = Submodule.span (OF E) {ξ} * (formSpan L * J) := by rw [hIJ, mul_one]
        _ = (Submodule.span (OF E) {ξ} * formSpan L) * J := (mul_assoc _ _ _).symm
        _ ≤ invDiff E * J := mul_le_mul_left h1 _
        _ = J * invDiff E := mul_comm _ _
      exact h2 (Submodule.mem_span_singleton_self ξ)
    · refine Submodule.mul_le.2 fun j hj v hv => ?_
      obtain ⟨w, rfl, hw⟩ := hv
      refine ⟨by rw [bar, map_mul, ← bar, ← bar, hJ j hj, bar_real]; ring, fun x hx y hy => ?_⟩
      have hm : j * altForm x y ∈ (1 : Submodule (OF E) E) := hJI ▸ Submodule.mul_mem_mul hj (Submodule.subset_span ⟨x, hx, y, hy, rfl⟩)
      obtain ⟨a, ha⟩ := Submodule.mem_one.1 hm
      obtain ⟨n, hn⟩ := hw a
      refine ⟨n, ?_⟩
      rw [← hn]
      apply trace_eq
      push_cast
      rw [coe_OF, ha]
      have hb : IsCMField.complexConj E j = -j := hJ j hj
      simp only [altForm, bar, map_mul, IsCMField.complexConj_apply_apply]
      rw [hb, show IsCMField.complexConj E (w : E) = w from bar_real w]
      ring
  refine ⟨?_, le_antisymm (polMod_mul_le L) ?_⟩
  · rw [hM]
    exact (show IsUnit J from ⟨⟨J, formSpan L, hJI, hIJ⟩, rfl⟩).mul isUnit_invDiff
  · rw [hM]
    intro z hz
    have h1 : Submodule.span (OF E) {z} * formSpan L ≤ invDiff E * L := by
      rw [formSpan, Submodule.span_mul_span, Submodule.span_le]
      rintro _ ⟨a, ha, b, ⟨x, hx, y, hy, rfl⟩, rfl⟩
      rw [Set.mem_singleton_iff.1 ha]
      have key : ∀ t ∈ L, z * bar t + bar z * t ∈ invDiff E := by
        intro t ht
        have hr : bar (z * bar t + bar z * t) = z * bar t + bar z * t := by
          simp only [bar, map_add, map_mul, IsCMField.complexConj_apply_apply]; ring
        obtain ⟨w, hw⟩ := real_of_bar hr
        refine ⟨w, hw, fun c => ?_⟩
        obtain ⟨n, hn⟩ := hz (c • t) (L.smul_mem c ht)
        refine ⟨n, ?_⟩
        rw [← hn]
        symm
        apply trace_eq
        push_cast
        rw [hw, coe_OF, bar_smul]
        simp only [bar, map_mul, IsCMField.complexConj_apply_apply, Algebra.smul_def]
        rw [show IsCMField.complexConj E (algebraMap (OF E) E c) = _ from bar_algebraMap c]
        ring
      have e : z * altForm x y = (z * bar y + bar z * y) * x - (z * bar x + bar z * x) * y := by
        simp only [altForm]; ring
      show z * altForm x y ∈ _
      rw [e]
      exact sub_mem (Submodule.mul_mem_mul (key y hy) hx) (Submodule.mul_mem_mul (key x hx) hy)
    have h2 : Submodule.span (OF E) {z} ≤ J * invDiff E * L := calc
      Submodule.span (OF E) {z} = Submodule.span (OF E) {z} * (formSpan L * J) := by rw [hIJ, mul_one]
      _ = (Submodule.span (OF E) {z} * formSpan L) * J := (mul_assoc _ _ _).symm
      _ ≤ invDiff E * L * J := mul_le_mul_left h1 _
      _ = J * invDiff E * L := by rw [mul_comm, mul_assoc]
    exact h2 (Submodule.mem_span_singleton_self z)
