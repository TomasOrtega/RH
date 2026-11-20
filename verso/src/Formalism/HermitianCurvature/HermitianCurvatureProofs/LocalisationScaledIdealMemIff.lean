import Formalism.HermitianCurvature.PrimeToDifferent
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DualIdealInclusion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstEmbeddingOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DualVolumePowerIdentity

namespace Formalism.FourierDecayAlt.P.S6x2

open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module MeasureTheory
open scoped nonZeroDivisors

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
The claim follows from `Algebra.trace_eq_of_algEquiv ((complexConj E).restrictScalars ℚ) x`.
-/
theorem trace_conj (x : E) :
    Algebra.trace ℚ E (complexConj E x) = Algebra.trace ℚ E x :=
  Algebra.trace_eq_of_algEquiv ((complexConj E).restrictScalars ℚ) x

/- English proof (translation)
Introduce `x hx`. Rewrite `hx`, the goal using `[FractionalIdeal.mem_one_iff]`. Take `⟨y, rfl⟩` from `hx`. Conclude with `⟨ringOfIntegersComplexConj E y, by simp⟩`.
-/
theorem conjStable_one : ConjStable E 1 := by
  intro x hx
  rw [FractionalIdeal.mem_one_iff] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  exact ⟨ringOfIntegersComplexConj E y, by simp⟩

/- English proof (translation)
Introduce `x hx`. Use `FractionalIdeal.mul_induction_on (C := fun x => complexConj E x ∈ A * B) hx (fun i hi j hj => ?_) (fun x y hx hy => ?_)` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `FractionalIdeal.mul_mem_mul (hA i hi) (hB j hj)`. Rewrite using `[map_add]`.

Conclude with `(A * B).coeToSubmodule.add_mem hx hy`.
-/
theorem conjStable_mul (A B : FI E) (hA : ConjStable E A) (hB : ConjStable E B) :
    ConjStable E (A * B) := by
  intro x hx
  refine FractionalIdeal.mul_induction_on (C := fun x => complexConj E x ∈ A * B) hx
    (fun i hi j hj => ?_) (fun x y hx hy => ?_)
  · rw [map_mul]; exact FractionalIdeal.mul_mem_mul (hA i hi) (hB j hj)
  · rw [map_add]; exact (A * B).coeToSubmodule.add_mem hx hy

/- English proof (translation)
Introduce `x hx`. Rewrite `hx`, the goal using `[FractionalIdeal.mem_inv_iff hA0]`. Introduce `y hy`. Use `conjStable_one E _ (hx _ (hA y hy))` as an intermediate fact. Rewrite `this` using `[map_mul, complexConj_apply_apply]`. Then use the resulting hypothesis.
-/
theorem conjStable_inv (A : FI E) (hA0 : A ≠ 0) (hA : ConjStable E A) : ConjStable E A⁻¹ := by
  intro x hx
  rw [FractionalIdeal.mem_inv_iff hA0] at hx ⊢
  intro y hy
  have := conjStable_one E _ (hx _ (hA y hy))
  rwa [map_mul, complexConj_apply_apply] at this

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero]`. Conclude with `conjStable_one E`. Consider the case `succ n ih => rw [pow_succ]`. Conclude with `conjStable_mul E _ _ ih hA`.
-/
theorem conjStable_pow (A : FI E) (hA : ConjStable E A) (n : ℕ) : ConjStable E (A ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact conjStable_one E
  | succ n ih => rw [pow_succ]; exact conjStable_mul E _ _ ih hA

/- English proof (translation)
Consider the cases of `n with`. Consider the case `ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast]`. Conclude with `conjStable_pow E A hA n`. Consider the case `negSucc n`. Rewrite using `[zpow_negSucc]`.

Conclude with `conjStable_inv E _ (pow_ne_zero _ hA0) (conjStable_pow E A hA _)`.
-/
theorem conjStable_zpow (A : FI E) (hA0 : A ≠ 0) (hA : ConjStable E A) (n : ℤ) :
    ConjStable E (A ^ n) := by
  cases n with
  | ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast]; exact conjStable_pow E A hA n
  | negSucc n =>
    rw [zpow_negSucc]
    exact conjStable_inv E _ (pow_ne_zero _ hA0) (conjStable_pow E A hA _)

/- English proof (translation)
Unfold `dd`. Rewrite using `[Ne, FractionalIdeal.coeIdeal_eq_zero]`. Conclude with `differentIdeal_ne_bot`.
-/
theorem dd_ne_zero : dd E ≠ 0 := by
  unfold dd
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
  exact differentIdeal_ne_bot

/- English proof (translation)
Unfold `dd`. Rewrite using `[coeIdeal_differentIdeal ℤ ℚ, inv_inv]`.
-/
theorem dual_one : FractionalIdeal.dual ℤ ℚ (1 : FI E) = (dd E)⁻¹ := by
  unfold dd
  rw [coeIdeal_differentIdeal ℤ ℚ, inv_inv]

/- English proof (translation)
Establish `h : ConjStable E (dd E)⁻¹`. Rewrite using `[← dual_one]`. Introduce `x hx`. Rewrite `hx`, the goal using `[FractionalIdeal.mem_dual (one_ne_zero : (1 : FI E) ≠ 0)]`. Introduce `a ha`.

Use `hx _ (conjStable_one E a ha)` as an intermediate fact. Rewrite `this`, the goal using `[Algebra.traceForm_apply]`. Rewrite `this` using `[← trace_conj, map_mul, complexConj_apply_apply]`. Conclude with `this`. Use `conjStable_inv E _ (inv_ne_zero (dd_ne_zero E)) h` as an intermediate fact.

Rewrite `this` using `[inv_inv]`. Then use the resulting hypothesis.
-/
theorem conjStable_dd : ConjStable E (dd E) := by
  have h : ConjStable E (dd E)⁻¹ := by
    rw [← dual_one]
    intro x hx
    rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FI E) ≠ 0)] at hx ⊢
    intro a ha
    have := hx _ (conjStable_one E a ha)
    rw [Algebra.traceForm_apply] at this ⊢
    rw [← trace_conj, map_mul, complexConj_apply_apply] at this
    exact this
  have := conjStable_inv E _ (inv_ne_zero (dd_ne_zero E)) h
  rwa [inv_inv] at this

/- English proof (translation)
Introduce `y hy`. Rewrite `hy`, the goal using `[FractionalIdeal.mem_spanSingleton]`. Take `⟨z, rfl⟩` from `hy`. Use `⟨ringOfIntegersComplexConj E z, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_mul, hx]`.

Both sides reduce to the same expression.
-/
theorem conjStable_span (x : E) (hx : complexConj E x = x) :
    ConjStable E (FractionalIdeal.spanSingleton _ x) := by
  intro y hy
  rw [FractionalIdeal.mem_spanSingleton] at hy ⊢
  obtain ⟨z, rfl⟩ := hy
  refine ⟨ringOfIntegersComplexConj E z, ?_⟩
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, hx]
  rfl

/- English proof (translation)
Introduce `E _ _ _ g k ν`. Unfold `idl`. Conclude with `conjStable_mul E _ _ (conjStable_zpow E _ (dd_ne_zero E) (conjStable_dd E) ν) (conjStable_span E _ (by rw [map_zpow₀, map_natCast]))`.
-/
theorem powConjStable : PowConjStable := by
  intro E _ _ _ g k ν
  unfold idl
  exact conjStable_mul E _ _ (conjStable_zpow E _ (dd_ne_zero E) (conjStable_dd E) ν)
    (conjStable_span E _ (by rw [map_zpow₀, map_natCast]))

/- English proof (translation)
Take `⟨x, hx, y, hy, hxy⟩` from `Submodule.mem_sup.1 ((Ideal.isCoprime_iff_sup_eq.1 hpd) ▸ (Submodule.mem_top : (1 : 𝓞 E) ∈ ⊤))`. Take `⟨w, rfl⟩` from `Ideal.mem_span_singleton'.1 hy`. Establish `hfix : complexConj E ((x * ringOfIntegersComplexConj E x : 𝓞 E) : E) = ((x * ringOfIntegersComplexConj E x : 𝓞 E) : E)`. Simplify using `[mul_comm]`. Take `⟨b, hb⟩` from `(RingOfIntegers.complexConj_eq_self_iff E _).1 hfix`.

Use `⟨b, ?_, ?_⟩` and prove the remaining obligations. Introduce `hbP`. Take `⟨Q, hQ, hQP⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal (𝓞 E)) (by simp)`. Establish `hb' : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) b = x * ringOfIntegersComplexConj E x` using `RingOfIntegers.ext hb`. Establish `h1 : x * ringOfIntegersComplexConj E x ∈ Q`.

Rewrite using `[← hb', ← Ideal.mem_comap, hQP.2]`. Conclude with `hbP`. Establish `h2 : (g : 𝓞 E) ∈ Q`. Establish `: algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (g : 𝓞 (maximalRealSubfield E)) ∈ Q`. Rewrite using `[← Ideal.mem_comap, hQP.2]`.

Conclude with `hgP`. Simplify using `using this`. Establish `hx1 : x = 1 - w * g` using `by rw [← hxy]; ring`. Apply `hQP.1.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`.

Establish `e : (1 : 𝓞 E) = x * ringOfIntegersComplexConj E x + (g : 𝓞 E) * (w + ringOfIntegersComplexConj E w - w * ringOfIntegersComplexConj E w * g)`. Rewrite using `[hx1, map_sub, map_mul, map_one, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Q.add_mem h1 (Q.mul_mem_right _ h2)`.

Rewrite using `[hb]`. Unfold `dd`. Rewrite using `[FractionalIdeal.mem_coeIdeal]`. Conclude with `⟨_, Ideal.mul_mem_right _ _ hx, rfl⟩`.
-/
theorem exists_real_mem_dd (g : ℕ) (hpd : PrimeToDifferent E g)
    (P : Ideal (𝓞 (maximalRealSubfield E))) (hP : P.IsPrime)
    (hgP : (g : 𝓞 (maximalRealSubfield E)) ∈ P) :
    ∃ b : 𝓞 (maximalRealSubfield E), b ∉ P ∧
      algebraMap (𝓞 (maximalRealSubfield E)) E b ∈ dd E := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1
    ((Ideal.isCoprime_iff_sup_eq.1 hpd) ▸ (Submodule.mem_top : (1 : 𝓞 E) ∈ ⊤))
  obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  have hfix : complexConj E ((x * ringOfIntegersComplexConj E x : 𝓞 E) : E)
      = ((x * ringOfIntegersComplexConj E x : 𝓞 E) : E) := by
    simp [mul_comm]
  obtain ⟨b, hb⟩ := (RingOfIntegers.complexConj_eq_self_iff E _).1 hfix
  refine ⟨b, ?_, ?_⟩
  · intro hbP
    obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal (𝓞 E)) (by simp)
    have hb' : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) b
        = x * ringOfIntegersComplexConj E x := RingOfIntegers.ext hb
    have h1 : x * ringOfIntegersComplexConj E x ∈ Q := by
      rw [← hb', ← Ideal.mem_comap, hQP.2]; exact hbP
    have h2 : (g : 𝓞 E) ∈ Q := by
      have : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (g : 𝓞 (maximalRealSubfield E)) ∈ Q := by
        rw [← Ideal.mem_comap, hQP.2]; exact hgP
      simpa using this
    have hx1 : x = 1 - w * g := by rw [← hxy]; ring
    apply hQP.1.ne_top
    rw [Ideal.eq_top_iff_one]
    have e : (1 : 𝓞 E) = x * ringOfIntegersComplexConj E x
        + (g : 𝓞 E) * (w + ringOfIntegersComplexConj E w - w * ringOfIntegersComplexConj E w * g) := by
      rw [hx1, map_sub, map_mul, map_one, map_natCast]; ring
    rw [e]
    exact Q.add_mem h1 (Q.mul_mem_right _ h2)
  · rw [hb]
    unfold dd
    rw [FractionalIdeal.mem_coeIdeal]
    exact ⟨_, Ideal.mul_mem_right _ _ hx, rfl⟩

/- English proof (translation)
Introduce `y hy`. Rewrite `hy` using `[FractionalIdeal.mem_spanSingleton]`. Take `⟨z, rfl⟩` from `hy`. Conclude with `A.coeToSubmodule.smul_mem z hc`.
-/
theorem span_le_of_mem (A : FI E) (c : E) (hc : c ∈ A) :
    FractionalIdeal.spanSingleton (𝓞 E)⁰ c ≤ A := by
  intro y hy
  rw [FractionalIdeal.mem_spanSingleton] at hy
  obtain ⟨z, rfl⟩ := hy
  exact A.coeToSubmodule.smul_mem z hc

/- English proof (translation)
Unfold `dd`. Conclude with `FractionalIdeal.coeIdeal_le_one`.
-/
theorem dd_le_one : dd E ≤ 1 := by
  unfold dd
  exact FractionalIdeal.coeIdeal_le_one

/- English proof (translation)
Establish `hC` using `span_le_of_mem E _ c hc`. Establish `hD : dd E ^ ν.natAbs ≤ 1` using `pow_le_one' (dd_le_one E) _`. Establish `hD0 : dd E ^ ν.natAbs ≠ 0` using `pow_ne_zero _ (dd_ne_zero E)`. Break down `Int.natAbs_eq ν with h | h` into its components or cases. Establish `e : dd E ^ ν = dd E ^ ν.natAbs` using `by conv_lhs => rw [h, zpow_natCast]`.

Rewrite using `[e]`. Conclude with `⟨(mul_le_mul' (hC.trans hD) hD).trans (by rw [one_mul]), hC⟩`. Establish `e : dd E ^ ν = (dd E ^ ν.natAbs)⁻¹` using `by conv_lhs => rw [h, zpow_neg, zpow_natCast]`. Rewrite using `[e]`. Use `⟨(mul_le_mul' hC le_rfl).trans (by rw [mul_inv_cancel₀ hD0]), (hC.trans hD).trans ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem span_zpow (c : E) (ν : ℤ) (hc : c ∈ dd E ^ ν.natAbs) :
    FractionalIdeal.spanSingleton (𝓞 E)⁰ c * dd E ^ ν ≤ 1 ∧
      FractionalIdeal.spanSingleton (𝓞 E)⁰ c ≤ dd E ^ ν := by
  have hC := span_le_of_mem E _ c hc
  have hD : dd E ^ ν.natAbs ≤ 1 := pow_le_one' (dd_le_one E) _
  have hD0 : dd E ^ ν.natAbs ≠ 0 := pow_ne_zero _ (dd_ne_zero E)
  rcases Int.natAbs_eq ν with h | h
  · have e : dd E ^ ν = dd E ^ ν.natAbs := by conv_lhs => rw [h, zpow_natCast]
    rw [e]
    exact ⟨(mul_le_mul' (hC.trans hD) hD).trans (by rw [one_mul]), hC⟩
  · have e : dd E ^ ν = (dd E ^ ν.natAbs)⁻¹ := by conv_lhs => rw [h, zpow_neg, zpow_natCast]
    rw [e]
    refine ⟨(mul_le_mul' hC le_rfl).trans (by rw [mul_inv_cancel₀ hD0]), (hC.trans hD).trans ?_⟩
    calc (1 : FI E) = dd E ^ ν.natAbs * (dd E ^ ν.natAbs)⁻¹ := (mul_inv_cancel₀ hD0).symm
      _ ≤ 1 * (dd E ^ ν.natAbs)⁻¹ := mul_le_mul' hD le_rfl
      _ = _ := one_mul _

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero, pow_zero]`. Conclude with `FractionalIdeal.one_mem_one _`. Consider the case `succ n ih => rw [pow_succ, pow_succ]`. Conclude with `FractionalIdeal.mul_mem_mul ih hx`.
-/
theorem pow_mem_pow (A : FI E) (x : E) (hx : x ∈ A) (n : ℕ) : x ^ n ∈ A ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact FractionalIdeal.one_mem_one _
  | succ n ih => rw [pow_succ, pow_succ]; exact FractionalIdeal.mul_mem_mul ih hx

/- English proof (translation)
Introduce `E _ _ _ g k ν hg hpd P hP hgP`. Take `⟨b, hbP, hb⟩` from `exists_real_mem_dd E g hpd P hP hgP`. Establish `hc : algebraMap (𝓞 (maximalRealSubfield E)) E (b ^ ν.natAbs) ∈ dd E ^ ν.natAbs`. Rewrite using `[map_pow]`. Conclude with `pow_mem_pow E _ _ hb _`.

Establish `hcP : b ^ ν.natAbs ∉ P` using `fun h => hbP (hP.mem_of_pow_mem _ h)`. Take `⟨h1, h2⟩` from `span_zpow E _ ν hc`. Use `set c := b ^ ν.natAbs`. Use extensionality with `t`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨a, ha, h⟩`. Use `⟨c * a, fun hh => (hP.mem_or_mem hh).elim hcP ha, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ ∈ idl E g k ν at h`. Use `show _ ∈ idl E g k 0`. Unfold `idl at h ⊢`.

Rewrite using `[map_mul, mul_assoc, zpow_zero]`. Use `FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self (𝓞 E)⁰ (algebraMap (𝓞 (maximalRealSubfield E)) E c)) h` as an intermediate fact. Rewrite `this` using `[← mul_assoc]`. Conclude with `mul_le_mul' h1 le_rfl this`. Introduce and unpack `⟨a, ha, h⟩`.

Use `⟨c * a, fun hh => (hP.mem_or_mem hh).elim hcP ha, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ ∈ idl E g k 0 at h`. Use `show _ ∈ idl E g k ν`. Unfold `idl at h ⊢`. Rewrite `h` using `[zpow_zero, one_mul]`.

Rewrite using `[map_mul, mul_assoc]`. Conclude with `mul_le_mul' h2 le_rfl (FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self (𝓞 E)⁰ (algebraMap (𝓞 (maximalRealSubfield E)) E c)) h)`.
-/
theorem locTyped : LocTyped := by
  intro E _ _ _ g k ν hg hpd P hP hgP
  obtain ⟨b, hbP, hb⟩ := exists_real_mem_dd E g hpd P hP hgP
  have hc : algebraMap (𝓞 (maximalRealSubfield E)) E (b ^ ν.natAbs) ∈ dd E ^ ν.natAbs := by
    rw [map_pow]; exact pow_mem_pow E _ _ hb _
  have hcP : b ^ ν.natAbs ∉ P := fun h => hbP (hP.mem_of_pow_mem _ h)
  obtain ⟨h1, h2⟩ := span_zpow E _ ν hc
  set c := b ^ ν.natAbs
  ext t
  constructor
  · rintro ⟨a, ha, h⟩
    refine ⟨c * a, fun hh => (hP.mem_or_mem hh).elim hcP ha, ?_⟩
    change _ ∈ idl E g k ν at h
    show _ ∈ idl E g k 0
    unfold idl at h ⊢
    rw [map_mul, mul_assoc, zpow_zero]
    have := FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self (𝓞 E)⁰
      (algebraMap (𝓞 (maximalRealSubfield E)) E c)) h
    rw [← mul_assoc] at this
    exact mul_le_mul' h1 le_rfl this
  · rintro ⟨a, ha, h⟩
    refine ⟨c * a, fun hh => (hP.mem_or_mem hh).elim hcP ha, ?_⟩
    change _ ∈ idl E g k 0 at h
    show _ ∈ idl E g k ν
    unfold idl at h ⊢
    rw [zpow_zero, one_mul] at h
    rw [map_mul, mul_assoc]
    exact mul_le_mul' h2 le_rfl (FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self (𝓞 E)⁰
      (algebraMap (𝓞 (maximalRealSubfield E)) E c)) h)

/- English proof (translation)
Unfold `twLat`. Rewrite using `[Submodule.mem_inf, Submodule.mem_comap]`. Establish `: ((LinearMap.id : E →ₗ[ℤ] E) - ((-1 : ℤ) ^ s) • conjZ E) t = t - (-1) ^ s * complexConj E t`. Rewrite using `[LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, zsmul_eq_mul]`. Use `push_cast`.

Both sides reduce to the same expression. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem mem_twLat (A B : FI E) (s : ℕ) (t : E) :
    t ∈ twLat E A B s ↔ t ∈ A ∧ t - (-1) ^ s * complexConj E t ∈ B := by
  unfold twLat
  rw [Submodule.mem_inf, Submodule.mem_comap]
  have : ((LinearMap.id : E →ₗ[ℤ] E) - ((-1 : ℤ) ^ s) • conjZ E) t
      = t - (-1) ^ s * complexConj E t := by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, zsmul_eq_mul]
    push_cast
    rfl
  rw [this]; rfl

/- English proof (translation)
The claim follows from `complexConj_apply_eq_self E (a : maximalRealSubfield E)`.
-/
theorem conj_real (a : 𝓞 (maximalRealSubfield E)) :
    complexConj E (algebraMap (𝓞 (maximalRealSubfield E)) E a)
      = algebraMap (𝓞 (maximalRealSubfield E)) E a :=
  complexConj_apply_eq_self E (a : maximalRealSubfield E)

/- English proof (translation)
Use `(A : Submodule (𝓞 E) E).smul_mem (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) a) ht` as an intermediate fact. Rewrite `this` using `[Algebra.smul_def]`. Conclude with `this`.
-/
theorem smul_mem_FI (A : FI E) (a : 𝓞 (maximalRealSubfield E)) (t : E) (ht : t ∈ A) :
    algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ A := by
  have := (A : Submodule (𝓞 E) E).smul_mem (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) a) ht
  rw [Algebra.smul_def] at this
  exact this

/- English proof (translation)
Introduce `E _ _ _ A B s P hP t`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, h⟩`. Rewrite `h` using `[mem_twLat]`. Use `⟨⟨a, ha, h.1⟩, ⟨a, ha, ?_⟩⟩` and prove the remaining obligations.

Use `h.2` as an intermediate fact. Rewrite `this` using `[map_mul, conj_real]`. Use `show _ ∈ B`. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Introduce and unpack `⟨⟨a, ha, h1⟩, ⟨b, hb, h2⟩⟩`. Use `⟨a * b, fun h => (hP.mem_or_mem h).elim ha hb, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_twLat]`. Prove the components needed by the constructor for the conclusion. Use `smul_mem_FI E A b _ h1` as an intermediate fact.

Rewrite using `[map_mul]`. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Use `smul_mem_FI E B a _ h2` as an intermediate fact. Rewrite using `[map_mul, map_mul, map_mul, conj_real, conj_real]`.

Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem locTw : LocTw := by
  intro E _ _ _ A B s P hP t
  constructor
  · rintro ⟨a, ha, h⟩
    rw [mem_twLat] at h
    refine ⟨⟨a, ha, h.1⟩, ⟨a, ha, ?_⟩⟩
    have := h.2
    rw [map_mul, conj_real] at this
    show _ ∈ B
    convert this using 1; ring
  · rintro ⟨⟨a, ha, h1⟩, ⟨b, hb, h2⟩⟩
    refine ⟨a * b, fun h => (hP.mem_or_mem h).elim ha hb, ?_⟩
    rw [mem_twLat]
    constructor
    · have := smul_mem_FI E A b _ h1
      rw [map_mul]; convert this using 1; ring
    · have := smul_mem_FI E B a _ h2
      rw [map_mul, map_mul, map_mul, conj_real, conj_real]; convert this using 1; ring

/- English proof (translation)
Introduce `E _ _ _ A B s hBA hB`. Use `⟨fun t ht => ?_, fun t ht => ((mem_twLat E A B s t).1 ht).1⟩` and prove the remaining obligations. Rewrite using `[mem_twLat]`. Use `⟨hBA ht, ?_⟩` and prove the remaining obligations. Establish `h1 : complexConj E t ∈ B` using `hB t ht`.

Establish `h2 : (-1 : E) ^ s * complexConj E t ∈ B`. Apply the tactic sequence `rcases neg_one_pow_eq_or E s with h | h <;> rw [h]`. Simplify using `using h1`. Rewrite using `[neg_one_mul]`. Conclude with `B.coeToSubmodule.neg_mem h1`.

Conclude with `B.coeToSubmodule.sub_mem ht h2`.
-/
theorem between : Between := by
  intro E _ _ _ A B s hBA hB
  refine ⟨fun t ht => ?_, fun t ht => ((mem_twLat E A B s t).1 ht).1⟩
  rw [mem_twLat]
  refine ⟨hBA ht, ?_⟩
  have h1 : complexConj E t ∈ B := hB t ht
  have h2 : (-1 : E) ^ s * complexConj E t ∈ B := by
    rcases neg_one_pow_eq_or E s with h | h <;> rw [h]
    · simpa using h1
    · rw [neg_one_mul]; exact B.coeToSubmodule.neg_mem h1
  exact B.coeToSubmodule.sub_mem ht h2

/- English proof (translation)
Introduce `E _ _ _`. Establish `h2 : finrank (maximalRealSubfield E) E = 2` using `Algebra.IsQuadraticExtension.finrank_eq_two _ _`. Establish `h3` using `finrank_mul_finrank ℚ (maximalRealSubfield E) E`. Establish `h4 : 0 < finrank ℚ (maximalRealSubfield E)` using `finrank_pos`. Rewrite `h3` using `[h2]`.

Use `⟨by unfold deg; omega, ?_, h4⟩` and prove the remaining obligations. Establish `h5` using `IsTotallyComplex.finrank E`. Establish `h6` using `InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces E`. Establish `h7 : InfinitePlace.nrRealPlaces E = 0` using `IsTotallyComplex.nrRealPlaces_eq_zero E`. Unfold `deg`.

Use linear arithmetic over natural numbers and integers.
-/
theorem degreeFacts : DegreeFacts := by
  intro E _ _ _
  have h2 : finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have h3 := finrank_mul_finrank ℚ (maximalRealSubfield E) E
  have h4 : 0 < finrank ℚ (maximalRealSubfield E) := finrank_pos
  rw [h2] at h3
  refine ⟨by unfold deg; omega, ?_, h4⟩
  have h5 := IsTotallyComplex.finrank E
  have h6 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces E
  have h7 : InfinitePlace.nrRealPlaces E = 0 := IsTotallyComplex.nrRealPlaces_eq_zero E
  unfold deg
  omega

/- English proof (translation)
Unfold `rd`. Apply `Real.rpow_pos_of_pos` to reduce the goal to its premises. Establish `: (0 : ℤ) < |discr E|` using `abs_pos.2 (discr_ne_zero E)`. Conclude with `this` after adjusting the coercions.
-/
theorem rd_pos : 0 < rd E := by
  unfold rd
  apply Real.rpow_pos_of_pos
  have : (0 : ℤ) < |discr E| := abs_pos.2 (discr_ne_zero E)
  exact_mod_cast this

/- English proof (translation)
Introduce `E _ _ _ g k ν hg`. Establish `hdeg` using `degreeFacts E`. Establish `hgR : (0 : ℝ) < g` using `by exact_mod_cast hg`. Establish `hD0 : (0 : ℝ) ≤ ((|discr E| : ℤ) : ℝ)` using `by exact_mod_cast abs_nonneg _`. Establish `hrd : 0 < rd E` using `rd_pos E`.

Establish `hD : ((|discr E| : ℤ) : ℝ) = rd E ^ (2 * deg E)`. Unfold `rd`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hD0, hdeg.1]`. Establish `: ((2 * deg E : ℕ) : ℝ) ≠ 0`. Use `hdeg.2.2` as an intermediate fact.

Check the signs of the components of the expression. Rewrite using `[inv_mul_cancel₀ this, Real.rpow_one]`. Establish `h1 : FractionalIdeal.absNorm (dd E) = ((|discr E| : ℤ) : ℚ)`. Unfold `dd`. Rewrite using `[FractionalIdeal.coeIdeal_absNorm, absNorm_differentIdeal E, Nat.cast_natAbs]`.

Establish `h2 : FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 E)⁰ ((g : E) ^ k)) = ((g : ℚ) ^ (2 * deg E)) ^ k`. Rewrite using `[FractionalIdeal.absNorm_span_singleton, show (g : E) ^ k = algebraMap ℚ E ((g : ℚ) ^ k) by rw [map_zpow₀, map_natCast], Algebra.norm_algebraMap, hdeg.1, abs_of_nonneg (by positivity)]`. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]`. Unfold `idl`. Rewrite using `[map_mul, map_zpow₀, h1, h2]`.

Use `push_cast`. Establish `hD' : (|(discr E : ℝ)|) = rd E ^ (2 * deg E)` using `by rw [← hD]; push_cast; rfl`. Rewrite using `[hD']`. Establish `: (rd E ^ (2 * deg E)) ^ ν * ((g : ℝ) ^ (2 * deg E)) ^ k = (((g : ℝ) ^ k * rd E ^ ν) ^ deg E) ^ 2`. Rewrite using `[← zpow_natCast (rd E), ← zpow_natCast (g : ℝ), ← zpow_mul, ← zpow_mul, ← pow_mul, mul_pow, ← zpow_natCast (((g : ℝ) ^ k)), ← zpow_natCast ((rd E ^ ν)), ← zpow_mul, ← zpow_mul, mul_comm]`.

Apply the tactic sequence `congr 2 <;> (push_cast; ring)`. Rewrite using `[this, Real.sqrt_sq (by positivity)]`.
-/
theorem normIdl : NormIdl := by
  intro E _ _ _ g k ν hg
  have hdeg := degreeFacts E
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hD0 : (0 : ℝ) ≤ ((|discr E| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg _
  have hrd : 0 < rd E := rd_pos E
  have hD : ((|discr E| : ℤ) : ℝ) = rd E ^ (2 * deg E) := by
    unfold rd
    rw [← Real.rpow_natCast, ← Real.rpow_mul hD0, hdeg.1]
    have : ((2 * deg E : ℕ) : ℝ) ≠ 0 := by
      have := hdeg.2.2
      positivity
    rw [inv_mul_cancel₀ this, Real.rpow_one]
  have h1 : FractionalIdeal.absNorm (dd E) = ((|discr E| : ℤ) : ℚ) := by
    unfold dd
    rw [FractionalIdeal.coeIdeal_absNorm, absNorm_differentIdeal E, Nat.cast_natAbs]
  have h2 : FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 E)⁰ ((g : E) ^ k))
      = ((g : ℚ) ^ (2 * deg E)) ^ k := by
    rw [FractionalIdeal.absNorm_span_singleton,
      show (g : E) ^ k = algebraMap ℚ E ((g : ℚ) ^ k) by rw [map_zpow₀, map_natCast],
      Algebra.norm_algebraMap, hdeg.1, abs_of_nonneg (by positivity)]
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  unfold idl
  rw [map_mul, map_zpow₀, h1, h2]
  push_cast
  have hD' : (|(discr E : ℝ)|) = rd E ^ (2 * deg E) := by rw [← hD]; push_cast; rfl
  rw [hD']
  have : (rd E ^ (2 * deg E)) ^ ν * ((g : ℝ) ^ (2 * deg E)) ^ k
      = (((g : ℝ) ^ k * rd E ^ ν) ^ deg E) ^ 2 := by
    rw [← zpow_natCast (rd E), ← zpow_natCast (g : ℝ), ← zpow_mul, ← zpow_mul, ← pow_mul, mul_pow,
      ← zpow_natCast (((g : ℝ) ^ k)), ← zpow_natCast ((rd E ^ ν)), ← zpow_mul, ← zpow_mul, mul_comm]
    congr 2 <;> (push_cast; ring)
  rw [this, Real.sqrt_sq (by positivity)]

/- English proof (translation)
Establish `hg' : ((g : E) ^ k) ≠ 0` using `zpow_ne_zero _ (by exact_mod_cast hg.ne')`. Unfold `idl`. Rewrite using `[mul_comm, FractionalIdeal.mem_singleton_mul]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl⟩`.

Rewrite using `[mul_div_cancel_left₀ _ hg']` and apply the resulting hypothesis. Introduce `h`. Conclude with `⟨_, h, by field_simp⟩`.
-/
theorem mem_idl (g : ℕ) (k ν : ℤ) (t : E) (hg : 0 < g) :
    t ∈ idl E g k ν ↔ t / (g : E) ^ k ∈ dd E ^ ν := by
  have hg' : ((g : E) ^ k) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast hg.ne')
  unfold idl
  rw [mul_comm, FractionalIdeal.mem_singleton_mul]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rwa [mul_div_cancel_left₀ _ hg']
  · intro h
    exact ⟨_, h, by field_simp⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, h⟩`. Use `⟨a, ha, ?_⟩` and prove the remaining obligations. Use `(mem_idl E g k 0 _ hg).1 h` as an intermediate fact. Rewrite `this` using `[zpow_zero]`.

Use `show _ ∈ (1 : FI E)`. Rewrite `this` using `[mul_div_assoc]`. Then use the resulting hypothesis. Introduce and unpack `⟨a, ha, h⟩`. Use `⟨a, ha, ?_⟩` and prove the remaining obligations. Use `show _ ∈ idl E g k 0`.

Rewrite using `[mem_idl E g k 0 _ hg, zpow_zero, mul_div_assoc]`. Conclude with `h`.
-/
theorem localisation_scaled_ideal_mem_iff (g : ℕ) (k : ℤ) (hg : 0 < g)
    (P : Ideal (𝓞 (maximalRealSubfield E))) (t : E) :
    t ∈ locAt E P (zsub E (idl E g k 0)) ↔ t / (g : E) ^ k ∈ locAt E P (zsub E 1) := by
  constructor
  · rintro ⟨a, ha, h⟩
    refine ⟨a, ha, ?_⟩
    have := (mem_idl E g k 0 _ hg).1 h
    rw [zpow_zero] at this
    show _ ∈ (1 : FI E)
    rwa [mul_div_assoc] at this
  · rintro ⟨a, ha, h⟩
    refine ⟨a, ha, ?_⟩
    show _ ∈ idl E g k 0
    rw [mem_idl E g k 0 _ hg, zpow_zero, mul_div_assoc]
    exact h

/- English proof (translation)
Introduce `E _ _ _ g ν s hg hpd P hP hgP K _ o σ hσ t`. Establish `hgK : (g : K) ≠ 0`. Establish `: σ (g : E) ≠ 0`. Rewrite using `[Ne, map_eq_zero]`. Conclude with `hg.ne'` after adjusting the coercions.

Simplify using `using this`. Unfold `perLat`. Rewrite using `[h1 E _ _ s P hP t, h2 E g 1 ν hg hpd P hP hgP, h2 E g 2 ν hg hpd P hP hgP, localisation_scaled_ideal_mem_iff E g 1 hg, localisation_scaled_ideal_mem_iff E g 2 hg, hσ, hσ]`. Simplify using `only [map_div₀, map_sub, map_mul, map_pow, map_neg, map_one, map_zpow₀, map_natCast, complexConj_apply_apply, zpow_one]`. Establish `e2 : ((g : K) ^ (2 : ℤ)) = (g : K) * g`.

Rewrite using `[show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`. Unfold `Formalism.FourierDecayAlt.I.orderR`. Simplify using `only [Set.mem_ofPred_eq]`.

Use `set a := σ t / (g : K) with ha`. Use `set b := σ (complexConj E t) / (g : K) with hb`. Apply the tactic sequence `rcases neg_one_pow_eq_or K s with h | h <;> rw [h]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨x1, x2⟩, x3, _⟩`.

Use `⟨x1, by simpa [one_mul] using x2, _, x3, ?_⟩` and prove the remaining obligations. Rewrite using `[ha]`. Clear the denominators using the available nonvanishing facts. Introduce and unpack `⟨x1, x2, u, hu, hh⟩`. Establish `x2' : b ∈ o` using `by simpa [one_mul] using x2`.

Establish `e : (σ t - 1 * σ (complexConj E t)) / ((g : K) * g) = u`. Rewrite `hh` using `[ha]`. Clear denominators, using `at hh ⊢` for the nonvanishing conditions. Take the linear combination `hh`. Establish `e' : (σ (complexConj E t) - 1 * σ t) / ((g : K) * g) = -u`.

Rewrite `hh` using `[ha]`. Clear denominators, using `at hh ⊢` for the nonvanishing conditions. Take the linear combination `-hh`. Conclude with `⟨⟨x1, x2'⟩, e ▸ hu, e' ▸ o.neg_mem hu⟩`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨x1, x2⟩, x3, _⟩`. Use `⟨x1, ?_, _, x3, ?_⟩` and prove the remaining obligations. Establish `: -1 * σ (complexConj E t) / (g : K) = -b` using `by rw [hb]; ring`. Rewrite using `[this]`. Conclude with `o.neg_mem x2`.

Rewrite using `[ha]`. Clear the denominators using the available nonvanishing facts. Introduce and unpack `⟨x1, x2, u, hu, hh⟩`. Establish `x2' : b ∈ o`. Establish `: b = -(-1 * σ (complexConj E t) / (g : K))` using `by rw [hb]; ring`.

Rewrite using `[this]`. Conclude with `o.neg_mem x2`. Establish `e : (σ t - -1 * σ (complexConj E t)) / ((g : K) * g) = u`. Rewrite `hh` using `[ha]`. Clear denominators, using `at hh ⊢` for the nonvanishing conditions.

Take the linear combination `hh`. Establish `e' : (σ (complexConj E t) - -1 * σ t) / ((g : K) * g) = u`. Rewrite `hh` using `[ha]`. Clear denominators, using `at hh ⊢` for the nonvanishing conditions. Take the linear combination `hh`.

Conclude with `⟨⟨x1, x2'⟩, e ▸ hu, e' ▸ hu⟩`.
-/
theorem typedModel (h1 : LocTw) (h2 : LocTyped) : TypedModel := by
  intro E _ _ _ g ν s hg hpd P hP hgP K _ o σ hσ t
  have hgK : (g : K) ≠ 0 := by
    have : σ (g : E) ≠ 0 := by
      rw [Ne, map_eq_zero]; exact_mod_cast hg.ne'
    simpa using this
  unfold perLat
  rw [h1 E _ _ s P hP t, h2 E g 1 ν hg hpd P hP hgP, h2 E g 2 ν hg hpd P hP hgP,
    localisation_scaled_ideal_mem_iff E g 1 hg, localisation_scaled_ideal_mem_iff E g 2 hg, hσ, hσ]
  simp only [map_div₀, map_sub, map_mul, map_pow, map_neg, map_one, map_zpow₀, map_natCast,
    complexConj_apply_apply, zpow_one]
  have e2 : ((g : K) ^ (2 : ℤ)) = (g : K) * g := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]; ring
  rw [e2]
  unfold Formalism.FourierDecayAlt.I.orderR
  simp only [Set.mem_ofPred_eq]
  set a := σ t / (g : K) with ha
  set b := σ (complexConj E t) / (g : K) with hb
  rcases neg_one_pow_eq_or K s with h | h <;> rw [h]
  · constructor
    · rintro ⟨⟨x1, x2⟩, x3, _⟩
      refine ⟨x1, by simpa [one_mul] using x2, _, x3, ?_⟩
      rw [ha]; field_simp
    · rintro ⟨x1, x2, u, hu, hh⟩
      have x2' : b ∈ o := by simpa [one_mul] using x2
      have e : (σ t - 1 * σ (complexConj E t)) / ((g : K) * g) = u := by
        rw [ha] at hh; field_simp at hh ⊢; linear_combination hh
      have e' : (σ (complexConj E t) - 1 * σ t) / ((g : K) * g) = -u := by
        rw [ha] at hh; field_simp at hh ⊢; linear_combination -hh
      exact ⟨⟨x1, x2'⟩, e ▸ hu, e' ▸ o.neg_mem hu⟩
  · constructor
    · rintro ⟨⟨x1, x2⟩, x3, _⟩
      refine ⟨x1, ?_, _, x3, ?_⟩
      · have : -1 * σ (complexConj E t) / (g : K) = -b := by rw [hb]; ring
        rw [this]; exact o.neg_mem x2
      · rw [ha]; field_simp
    · rintro ⟨x1, x2, u, hu, hh⟩
      have x2' : b ∈ o := by
        have : b = -(-1 * σ (complexConj E t) / (g : K)) := by rw [hb]; ring
        rw [this]; exact o.neg_mem x2
      have e : (σ t - -1 * σ (complexConj E t)) / ((g : K) * g) = u := by
        rw [ha] at hh; field_simp at hh ⊢; linear_combination hh
      have e' : (σ (complexConj E t) - -1 * σ t) / ((g : K) * g) = u := by
        rw [ha] at hh; field_simp at hh ⊢; linear_combination hh
      exact ⟨⟨x1, x2'⟩, e ▸ hu, e' ▸ hu⟩

/- English proof (translation)
Unfold `idl`. Establish `: FractionalIdeal.spanSingleton (𝓞 E)⁰ ((g : E) ^ (2 : ℤ)) = FractionalIdeal.spanSingleton (𝓞 E)⁰ ((g : E) ^ (1 : ℤ)) * FractionalIdeal.spanSingleton (𝓞 E)⁰ (g : E)`. Rewrite using `[FractionalIdeal.spanSingleton_mul_spanSingleton]`. Use `congr 1`. Rewrite using `[show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, zpow_one]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, ← mul_assoc]`. Use `FractionalIdeal.mul_le.2 fun i hi j hj => ?_` and prove the remaining obligations. Rewrite `hj` using `[FractionalIdeal.mem_spanSingleton]`. Take `⟨z, rfl⟩` from `hj`.

Establish `h` using `(dd E ^ ν * FractionalIdeal.spanSingleton (𝓞 E)⁰ ((g : E) ^ (1 : ℤ)) : FI E).coeToSubmodule.smul_mem (z * (g : 𝓞 E)) hi`. Rewrite `h` using `[Algebra.smul_def]`. Establish `e : i * z • (g : E) = (algebraMap (𝓞 E) E) (z * (g : 𝓞 E)) * i`. Rewrite using `[Algebra.smul_def]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `h`.
-/
theorem idl_le (g : ℕ) (ν : ℤ) : idl E g 2 ν ≤ idl E g 1 ν := by
  unfold idl
  have : FractionalIdeal.spanSingleton (𝓞 E)⁰ ((g : E) ^ (2 : ℤ)) =
      FractionalIdeal.spanSingleton (𝓞 E)⁰ ((g : E) ^ (1 : ℤ))
        * FractionalIdeal.spanSingleton (𝓞 E)⁰ (g : E) := by
    rw [FractionalIdeal.spanSingleton_mul_spanSingleton]; congr 1
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, zpow_one]; ring
  rw [this, ← mul_assoc]
  refine FractionalIdeal.mul_le.2 fun i hi j hj => ?_
  rw [FractionalIdeal.mem_spanSingleton] at hj
  obtain ⟨z, rfl⟩ := hj
  have h := (dd E ^ ν * FractionalIdeal.spanSingleton (𝓞 E)⁰
    ((g : E) ^ (1 : ℤ)) : FI E).coeToSubmodule.smul_mem (z * (g : 𝓞 E)) hi
  rw [Algebra.smul_def] at h
  have e : i * z • (g : E) = (algebraMap (𝓞 E) E) (z * (g : 𝓞 E)) * i := by
    rw [Algebra.smul_def]; push_cast; ring
  rw [e]; exact h

/- English proof (translation)
Unfold `idl`. Apply `mul_ne_zero` to reduce the goal to its premises. Conclude with `zpow_ne_zero _ (dd_ne_zero E)`. Rewrite using `[Ne, FractionalIdeal.spanSingleton_eq_zero_iff]`. Conclude with `zpow_ne_zero _ (by exact_mod_cast hg.ne')`.
-/
theorem idl_ne_zero (g : ℕ) (k ν : ℤ) (hg : 0 < g) : idl E g k ν ≠ 0 := by
  unfold idl
  apply mul_ne_zero
  · exact zpow_ne_zero _ (dd_ne_zero E)
  · rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact zpow_ne_zero _ (by exact_mod_cast hg.ne')

/- English proof (translation)
Establish `hgE : (g : E) ≠ 0` using `by exact_mod_cast hg.ne'`. Unfold `idl`. Rewrite using `[mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, ← zpow_add_one₀ hgE]`.
-/
theorem idl_mul (g : ℕ) (k ν : ℤ) (hg : 0 < g) :
    idl E g k ν * FractionalIdeal.spanSingleton _ (g : E) = idl E g (k + 1) ν := by
  have hgE : (g : E) ≠ 0 := by exact_mod_cast hg.ne'
  unfold idl
  rw [mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, ← zpow_add_one₀ hgE]

/- English proof (translation)
Introduce `x hx`. Use `h1 E (dd E) (dual_one E) ν (g : ℤ) (by exact_mod_cast hg.ne') (perLat E g ν s) ?_ x ?_` as an intermediate fact. Use `show x ∈ dualIdl E g ν`. Unfold `dualIdl idl`. Rewrite using `[zpow_neg_one]`.

Simplify using `using this`. Introduce `y hy`. Use `(h3 E (idl E g 1 ν) (idl E g 2 ν) s (idl_le E g ν) (h2 E g 2 ν)).1 ?_` and prove the remaining obligations. Use `show y ∈ idl E g 2 ν`. Unfold `idl`.

Rewrite using `[show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]`. Simplify using `using hy`. Introduce `y hy`. Simplify using `using hx y hy`.
-/
theorem dual_le (h1 : Formalism.FourierDecayAlt.L.DualLatticeInclusion) (h2 : PowConjStable) (h3 : Between)
    (g : ℕ) (ν : ℤ) (s : ℕ) (hg : 0 < g) :
    dualLat E g (perLat E g ν s) ≤ zsub E (dualIdl E g ν) := by
  intro x hx
  have := h1 E (dd E) (dual_one E) ν (g : ℤ) (by exact_mod_cast hg.ne') (perLat E g ν s) ?_ x ?_
  · show x ∈ dualIdl E g ν
    unfold dualIdl idl
    rw [zpow_neg_one]
    simpa using this
  · intro y hy
    refine (h3 E (idl E g 1 ν) (idl E g 2 ν) s (idl_le E g ν) (h2 E g 2 ν)).1 ?_
    show y ∈ idl E g 2 ν
    unfold idl
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
    simpa using hy
  · intro y hy
    simpa using hx y hy

/- English proof (translation)
Introduce `E _ _ _ g ν s hg l hl hl0`. Establish `h` using `hW E (dualIdl E g ν) l (dual_le E h1 h2 h3 g ν s hg hl) hl0`. Establish `hn` using `hN E g (-1) (-(ν + 1)) hg`. Use `le_trans (le_of_eq ?_) h` and prove the remaining obligations. Unfold `dualIdl`.

Rewrite using `[hn, zpow_neg, zpow_neg, zpow_neg, zpow_one, ← mul_inv, inv_pow, zpow_natCast]`.
-/
theorem leastNorm (h1 : Formalism.FourierDecayAlt.L.DualLatticeInclusion) (hW : Formalism.FourierDecayAlt.W.NormLower) (h2 : PowConjStable)
    (h3 : Between) (hN : NormIdl) : LeastNorm := by
  intro E _ _ _ g ν s hg l hl hl0
  have h := hW E (dualIdl E g ν) l (dual_le E h1 h2 h3 g ν s hg hl) hl0
  have hn := hN E g (-1) (-(ν + 1)) hg
  refine le_trans (le_of_eq ?_) h
  unfold dualIdl
  rw [hn, zpow_neg, zpow_neg, zpow_neg, zpow_one, ← mul_inv, inv_pow, zpow_natCast]

/- English proof (translation)
Introduce `E _ _ _ g r i c hg hc l hl hl0`. Establish `h` using `hL E g (nuBlock r i 1) 1 hg l hl hl0`. Establish `hrd : 0 < rd E` using `rd_pos E`. Establish `hgR : (0 : ℝ) < g` using `by exact_mod_cast hg`. Establish `hid` using `hD (InfinitePlace E) c g (rd E) r i hgR hrd`.

Rewrite `hid` using `[(hdeg E).2.1]`. Rewrite using `[← hid]`. Establish `e : nuBlock (r : ℤ) (i : ℤ) 1 + 1 = (2 * r : ℤ) + 3 - 2 * i` using `by unfold nuBlock; ring`. Rewrite `h` using `[e]`. Establish `hpos : 0 < ((g : ℝ) * rd E ^ ((2 * r : ℤ) + 3 - 2 * i)) ^ (-(deg E : ℤ))` using `by positivity`.

Apply `div_le_div_of_nonneg_left _ hpos h` to reduce the goal to its premises. Conclude with `Finset.prod_nonneg fun v _ => mul_nonneg (hc v) (by positivity)`.
-/
theorem sizeQuotient (hL : LeastNorm) (hD : Formalism.FourierDecayAlt.DualSizeIdentity) (hdeg : DegreeFacts) :
    SizeQuotient := by
  intro E _ _ _ g r i c hg hc l hl hl0
  have h := hL E g (nuBlock r i 1) 1 hg l hl hl0
  have hrd : 0 < rd E := rd_pos E
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hid := hD (InfinitePlace E) c g (rd E) r i hgR hrd
  rw [(hdeg E).2.1] at hid
  rw [← hid]
  have e : nuBlock (r : ℤ) (i : ℤ) 1 + 1 = (2 * r : ℤ) + 3 - 2 * i := by unfold nuBlock; ring
  rw [e] at h
  have hpos : 0 < ((g : ℝ) * rd E ^ ((2 * r : ℤ) + 3 - 2 * i)) ^ (-(deg E : ℤ)) := by positivity
  apply div_le_div_of_nonneg_left _ hpos h
  exact Finset.prod_nonneg fun v _ => mul_nonneg (hc v) (by positivity)

/- English proof (translation)
Rewrite using `[FractionalIdeal.dual_eq_mul_inv, dual_one, neg_add, zpow_add₀ (dd_ne_zero E), zpow_neg, zpow_neg, zpow_one, mul_comm]`.
-/
theorem dual_pow (ν : ℤ) :
    FractionalIdeal.dual ℤ ℚ (dd E ^ ν) = dd E ^ (-(ν + 1)) := by
  rw [FractionalIdeal.dual_eq_mul_inv, dual_one, neg_add, zpow_add₀ (dd_ne_zero E), zpow_neg,
    zpow_neg, zpow_one, mul_comm]

/- English proof (translation)
Introduce `E _ _ _ g ν s hg l hl`. Establish `hgE : (g : E) ≠ 0` using `by exact_mod_cast hg.ne'`. Establish `hd : dd E ≠ 0` using `dd_ne_zero E`. Rewrite using `[mem_twLat]`. Use `⟨dual_le E h1 h2 h3 g ν s hg hl, ?_⟩` and prove the remaining obligations.

Establish `e0 : idl E g 0 (-(ν + 1)) = FractionalIdeal.dual ℤ ℚ (dd E ^ ν)`. Rewrite using `[dual_pow]`. Unfold `idl`. Simplify using the standard rewrite rules. Rewrite using `[e0, FractionalIdeal.mem_dual (zpow_ne_zero _ hd)]`.

Introduce `i hi`. Establish `hic : complexConj E i ∈ dd E ^ ν`. Use `h2 E g 0 ν i (by unfold idl; simpa using hi)` as an intermediate fact. Unfold `idl at this`. Simplify using `using this`.

Use `set ε : E := (-1) ^ s with hε`. Establish `hεε : ε * ε = 1` using `by rw [hε, ← pow_add, ← two_mul, pow_mul]; simp`. Establish `hεc : complexConj E ε = ε` using `by rw [hε, map_pow, map_neg, map_one]`. Establish `hεi : ε * complexConj E i ∈ dd E ^ ν`. Break down `neg_one_pow_eq_or E s with h | h` into its components or cases.

Rewrite using `[hε, h, one_mul]`. Conclude with `hic`. Rewrite using `[hε, h, neg_one_mul]`. Conclude with `(dd E ^ ν : FI E).coeToSubmodule.neg_mem hic`. Establish `ht : (g : E) * (i + ε * complexConj E i) ∈ perLat E g ν s`.

Unfold `perLat`. Rewrite using `[mem_twLat]`. Prove the components needed by the constructor for the conclusion. Unfold `idl`. Rewrite using `[mul_comm (dd E ^ ν), FractionalIdeal.mem_singleton_mul]`.

Conclude with `⟨_, (dd E ^ ν : FI E).coeToSubmodule.add_mem hi hεi, by rw [zpow_one]⟩`. Establish `: (g : E) * (i + ε * complexConj E i) - (-1) ^ s * complexConj E ((g : E) * (i + ε * complexConj E i)) = 0`. Rewrite using `[← hε, map_mul, map_add, map_mul, hεc, complexConj_apply_apply, map_natCast]`. Take the linear combination `(-(g : E) * i) * hεε`. Rewrite using `[this]`.

Conclude with `(idl E g 2 ν).coeToSubmodule.zero_mem`. Use `hl _ ht` as an intermediate fact. Rewrite using `[Algebra.traceForm_apply]`. Establish `e1 : l * ((g : E) * (i + ε * complexConj E i)) / g = l * i + ε * (l * complexConj E i)`. Clear the denominators using the available nonvanishing facts.

Establish `e2 : Algebra.trace ℚ E (ε * (l * complexConj E i)) = Algebra.trace ℚ E (ε * complexConj E l * i)`. Rewrite using `[← trace_conj]`. Use `congr 1`. Rewrite using `[map_mul, map_mul, hεc, complexConj_apply_apply]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `this` using `[e1, map_add, e2, ← map_add]`. Use `this using 2` and compare the differences between its conclusion and the goal. Rewrite using `[pow_succ, ← hε]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dualSubset (h1 : Formalism.FourierDecayAlt.L.DualLatticeInclusion) (h2 : PowConjStable) (h3 : Between) : DualSubset := by
  intro E _ _ _ g ν s hg l hl
  have hgE : (g : E) ≠ 0 := by exact_mod_cast hg.ne'
  have hd : dd E ≠ 0 := dd_ne_zero E
  rw [mem_twLat]
  refine ⟨dual_le E h1 h2 h3 g ν s hg hl, ?_⟩
  have e0 : idl E g 0 (-(ν + 1)) = FractionalIdeal.dual ℤ ℚ (dd E ^ ν) := by
    rw [dual_pow]; unfold idl; simp
  rw [e0, FractionalIdeal.mem_dual (zpow_ne_zero _ hd)]
  intro i hi
  have hic : complexConj E i ∈ dd E ^ ν := by
    have := h2 E g 0 ν i (by unfold idl; simpa using hi)
    unfold idl at this; simpa using this
  set ε : E := (-1) ^ s with hε
  have hεε : ε * ε = 1 := by rw [hε, ← pow_add, ← two_mul, pow_mul]; simp
  have hεc : complexConj E ε = ε := by rw [hε, map_pow, map_neg, map_one]
  have hεi : ε * complexConj E i ∈ dd E ^ ν := by
    rcases neg_one_pow_eq_or E s with h | h
    · rw [hε, h, one_mul]; exact hic
    · rw [hε, h, neg_one_mul]; exact (dd E ^ ν : FI E).coeToSubmodule.neg_mem hic
  have ht : (g : E) * (i + ε * complexConj E i) ∈ perLat E g ν s := by
    unfold perLat
    rw [mem_twLat]
    constructor
    · unfold idl
      rw [mul_comm (dd E ^ ν), FractionalIdeal.mem_singleton_mul]
      exact ⟨_, (dd E ^ ν : FI E).coeToSubmodule.add_mem hi hεi, by rw [zpow_one]⟩
    · have : (g : E) * (i + ε * complexConj E i)
          - (-1) ^ s * complexConj E ((g : E) * (i + ε * complexConj E i)) = 0 := by
        rw [← hε, map_mul, map_add, map_mul, hεc, complexConj_apply_apply, map_natCast]
        linear_combination (-(g : E) * i) * hεε
      rw [this]; exact (idl E g 2 ν).coeToSubmodule.zero_mem
  have := hl _ ht
  rw [Algebra.traceForm_apply]
  have e1 : l * ((g : E) * (i + ε * complexConj E i)) / g = l * i + ε * (l * complexConj E i) := by
    field_simp
  have e2 : Algebra.trace ℚ E (ε * (l * complexConj E i))
      = Algebra.trace ℚ E (ε * complexConj E l * i) := by
    rw [← trace_conj]
    congr 1
    rw [map_mul, map_mul, hεc, complexConj_apply_apply]; ring
  rw [e1, map_add, e2, ← map_add] at this
  convert this using 2
  rw [pow_succ, ← hε]; ring

/- English proof (translation)
Introduce `hC hS hTw hO hT hF hLG E _ _ _ g₁ g₂ h₁ h₂ ν s _`. Establish `hg : 0 < g₁ * g₂` using `Nat.mul_pos h₁.1.pos h₂.1.pos`. Establish `hpd : PrimeToDifferent E (g₁ * g₂)`. Establish `a` using `hS E g₁ h₁`. Establish `b` using `hS E g₂ h₂`.

Unfold `PrimeToDifferent at a b ⊢`. Establish `: Ideal.span {((g₁ * g₂ : ℕ) : 𝓞 E)} = Ideal.span {(g₁ : 𝓞 E)} * Ideal.span {(g₂ : 𝓞 E)}`. Rewrite using `[Ideal.span_singleton_mul_span_singleton]`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite using `[this]`. Conclude with `IsCoprime.mul_right a b`. Use `⟨fun P hP hgP => ?_, fun P hP hgP t => ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `t`. Unfold `perLat`.

Rewrite using `[hTw E _ _ s P hP.isPrime t, hO E _ 1 ν P hP.isPrime hgP, hO E _ 2 ν P hP.isPrime hgP]`. Use `⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩` and prove the remaining obligations. Take `⟨a, ha, hat⟩` from `h`. Use `⟨a, ha, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ ∈ idl E (g₁ * g₂) 0 ν at hat`.

Use `show _ ∈ idl E (g₁ * g₂) 0 ν`. Establish `hc` using `hC E (g₁ * g₂) 0 ν _ hat`. Rewrite `hc` using `[map_mul, conj_real]`. Apply the tactic sequence `rcases neg_one_pow_eq_or E s with h | h <;> rw [h]`. Use `(idl E (g₁ * g₂) 0 ν).coeToSubmodule.sub_mem hat hc` as an intermediate fact.

Establish `e : algebraMap (𝓞 (maximalRealSubfield E)) E a * (t - 1 * complexConj E t) = algebraMap (𝓞 (maximalRealSubfield E)) E a * t - algebraMap (𝓞 (maximalRealSubfield E)) E a * complexConj E t` using `by ring`. Rewrite using `[e]`. Conclude with `this`. Use `(idl E (g₁ * g₂) 0 ν).coeToSubmodule.add_mem hat hc` as an intermediate fact. Establish `e : algebraMap (𝓞 (maximalRealSubfield E)) E a * (t - -1 * complexConj E t) = algebraMap (𝓞 (maximalRealSubfield E)) E a * t + algebraMap (𝓞 (maximalRealSubfield E)) E a * complexConj E t` using `by ring`.

Rewrite using `[e]`. Conclude with `this`. Unfold `perLat`. Rewrite using `[hTw E _ _ s P hP.isPrime t, hT E _ 1 ν hg hpd P hP.isPrime hgP, hT E _ 2 ν hg hpd P hP.isPrime hgP]`. Conclude with `hLG E _ (hF E _ _ s (idl_ne_zero E _ 2 ν hg) (idl_le E _ ν) (hC E _ 2 ν))`.
-/
theorem assembleLocal : AssembleLocal := by
  intro hC hS hTw hO hT hF hLG E _ _ _ g₁ g₂ h₁ h₂ ν s _
  have hg : 0 < g₁ * g₂ := Nat.mul_pos h₁.1.pos h₂.1.pos
  have hpd : PrimeToDifferent E (g₁ * g₂) := by
    have a := hS E g₁ h₁
    have b := hS E g₂ h₂
    unfold PrimeToDifferent at a b ⊢
    have : Ideal.span {((g₁ * g₂ : ℕ) : 𝓞 E)}
        = Ideal.span {(g₁ : 𝓞 E)} * Ideal.span {(g₂ : 𝓞 E)} := by
      rw [Ideal.span_singleton_mul_span_singleton]; push_cast; rfl
    rw [this]
    exact IsCoprime.mul_right a b
  refine ⟨fun P hP hgP => ?_, fun P hP hgP t => ?_, ?_⟩
  · ext t
    unfold perLat
    rw [hTw E _ _ s P hP.isPrime t, hO E _ 1 ν P hP.isPrime hgP, hO E _ 2 ν P hP.isPrime hgP]
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    obtain ⟨a, ha, hat⟩ := h
    refine ⟨a, ha, ?_⟩
    change _ ∈ idl E (g₁ * g₂) 0 ν at hat
    show _ ∈ idl E (g₁ * g₂) 0 ν
    have hc := hC E (g₁ * g₂) 0 ν _ hat
    rw [map_mul, conj_real] at hc
    rcases neg_one_pow_eq_or E s with h | h <;> rw [h]
    · have := (idl E (g₁ * g₂) 0 ν).coeToSubmodule.sub_mem hat hc
      have e : algebraMap (𝓞 (maximalRealSubfield E)) E a * (t - 1 * complexConj E t)
          = algebraMap (𝓞 (maximalRealSubfield E)) E a * t
            - algebraMap (𝓞 (maximalRealSubfield E)) E a * complexConj E t := by ring
      rw [e]; exact this
    · have := (idl E (g₁ * g₂) 0 ν).coeToSubmodule.add_mem hat hc
      have e : algebraMap (𝓞 (maximalRealSubfield E)) E a * (t - -1 * complexConj E t)
          = algebraMap (𝓞 (maximalRealSubfield E)) E a * t
            + algebraMap (𝓞 (maximalRealSubfield E)) E a * complexConj E t := by ring
      rw [e]; exact this
  · unfold perLat
    rw [hTw E _ _ s P hP.isPrime t, hT E _ 1 ν hg hpd P hP.isPrime hgP,
      hT E _ 2 ν hg hpd P hP.isPrime hgP]
  · exact hLG E _ (hF E _ _ s (idl_ne_zero E _ 2 ν hg) (idl_le E _ ν) (hC E _ 2 ν))

/- English proof (translation)
Introduce `hdeg hC hU hB hI hDs hDp hN hCov E _ _ _ hUn g ν s hg`. Establish `hUA` using `(hU E hUn).2 g`. Establish `hb` using `hB E (idl E g 1 ν) (idl E g 2 ν) s (idl_le E g ν) (hC E g 2 ν)`. Establish `hi` using `hI E (idl E g 1 ν) g s (idl_ne_zero E g 1 ν hg) (hC E g 1 ν) hg hUA`. Rewrite `hi` using `[idl_mul E g 1 ν hg, show (1 : ℤ) + 1 = 2 from rfl]`.

Establish `hd : dualLat E g (perLat E g ν s) = twLat E (dualIdl E g ν) (idl E g 0 (-(ν + 1))) (s + 1)` using `le_antisymm (hDs E g ν s hg) (hDp E hUn g ν s hg)`. Establish `hi2` using `hI E (dualIdl E g ν) g (s + 1) (idl_ne_zero E g _ _ hg) (hC E g _ _) hg hUA`. Establish `hi3` using `hI E (liftIdl E g ν) g s (idl_ne_zero E g _ _ hg) (hC E g _ _) hg hUA`. Unfold `dualIdl at hi2`. Unfold `liftIdl at hi3`.

Rewrite `hi2`, `hi3` using `[idl_mul E g (-1) _ hg, show (-1 : ℤ) + 1 = 0 from rfl]`. Establish `hrd : 0 < rd E` using `rd_pos E`. Establish `hgR : (0 : ℝ) < g` using `by exact_mod_cast hg`. Establish `hcov` using `hCov E (idl E g 2 ν) (perLat E g ν s) (rd E ^ (-ν)) (idl_ne_zero E g 2 ν hg) (zpow_ne_zero _ hrd.ne') hb.1 (by`. Establish `: idx E (zsub E (idl E g 2 ν)) (perLat E g ν s) = g ^ deg E` using `hi.2`.

Rewrite using `[this]`. Use the proof step `positivity)`. Use `⟨hb.1, hb.2, hi.1, hi.2, ?_, ?_, inf_le_left, hi3.1, ?_, hcov.1, hcov.2.1, ?_⟩` and prove the remaining obligations. Rewrite using `[hd]`. Conclude with `inf_le_left`.

Rewrite using `[hd]`. Conclude with `hi2.1`. Unfold `dualIdl`. Rewrite using `[hN E g (-1) (-(ν + 1)) hg, zpow_neg, zpow_neg, zpow_neg, zpow_one, ← mul_inv, inv_pow, zpow_natCast]`. Rewrite using `[hcov.2.2]`.

Establish `h4 : idx E (zsub E (idl E g 2 ν)) (perLat E g ν s) = g ^ deg E` using `hi.2`. Rewrite using `[h4]`. Establish `hD0 : (0 : ℝ) ≤ ((|discr E| : ℤ) : ℝ)` using `by exact_mod_cast abs_nonneg _`. Establish `hsq : √((|discr E| : ℤ) : ℝ) = rd E ^ deg E`. Unfold `rd`.

Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hD0, Real.sqrt_eq_rpow]`. Use `congr 1`. Rewrite using `[(hdeg E).1]`. Establish `: (deg E : ℝ) ≠ 0` using `by exact_mod_cast (hdeg E).2.2.ne'`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Establish `hNB : (FractionalIdeal.absNorm (idl E g 2 ν) : ℝ) = (((g : ℝ) ^ (2 : ℤ) * rd E ^ ν) ^ deg E) ^ 2`. Rewrite using `[← hN E g 2 ν hg, Real.sq_sqrt]`. Conclude with `(FractionalIdeal.absNorm_nonneg _)` after adjusting the coercions. Rewrite using `[hsq, hNB, abs_of_pos (zpow_pos hrd _), zpow_neg]`.

Establish `ha : 0 < rd E ^ ν` using `zpow_pos hrd _`. Use `set a := rd E ^ ν`. Rewrite using `[show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]`. Use `push_cast`. Establish `hG : (g : ℝ) ^ deg E ≠ 0` using `by positivity`.

Establish `hA : a ^ deg E ≠ 0` using `by positivity`. Rewrite using `[inv_pow, inv_pow, div_pow, pow_mul, mul_pow, mul_pow]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem assembleLattices : AssembleLattices := by
  intro hdeg hC hU hB hI hDs hDp hN hCov E _ _ _ hUn g ν s hg
  have hUA := (hU E hUn).2 g
  have hb := hB E (idl E g 1 ν) (idl E g 2 ν) s (idl_le E g ν) (hC E g 2 ν)
  have hi := hI E (idl E g 1 ν) g s (idl_ne_zero E g 1 ν hg) (hC E g 1 ν) hg hUA
  rw [idl_mul E g 1 ν hg, show (1 : ℤ) + 1 = 2 from rfl] at hi
  have hd : dualLat E g (perLat E g ν s)
      = twLat E (dualIdl E g ν) (idl E g 0 (-(ν + 1))) (s + 1) :=
    le_antisymm (hDs E g ν s hg) (hDp E hUn g ν s hg)
  have hi2 := hI E (dualIdl E g ν) g (s + 1) (idl_ne_zero E g _ _ hg) (hC E g _ _) hg hUA
  have hi3 := hI E (liftIdl E g ν) g s (idl_ne_zero E g _ _ hg) (hC E g _ _) hg hUA
  unfold dualIdl at hi2
  unfold liftIdl at hi3
  rw [idl_mul E g (-1) _ hg, show (-1 : ℤ) + 1 = 0 from rfl] at hi2 hi3
  have hrd : 0 < rd E := rd_pos E
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hcov := hCov E (idl E g 2 ν) (perLat E g ν s) (rd E ^ (-ν)) (idl_ne_zero E g 2 ν hg)
    (zpow_ne_zero _ hrd.ne') hb.1 (by
      have : idx E (zsub E (idl E g 2 ν)) (perLat E g ν s) = g ^ deg E := hi.2
      rw [this]; positivity)
  refine ⟨hb.1, hb.2, hi.1, hi.2, ?_, ?_, inf_le_left, hi3.1, ?_, hcov.1, hcov.2.1, ?_⟩
  · rw [hd]; exact inf_le_left
  · rw [hd]; exact hi2.1
  · unfold dualIdl
    rw [hN E g (-1) (-(ν + 1)) hg, zpow_neg, zpow_neg, zpow_neg, zpow_one, ← mul_inv, inv_pow,
      zpow_natCast]
  · rw [hcov.2.2]
    have h4 : idx E (zsub E (idl E g 2 ν)) (perLat E g ν s) = g ^ deg E := hi.2
    rw [h4]
    have hD0 : (0 : ℝ) ≤ ((|discr E| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg _
    have hsq : √((|discr E| : ℤ) : ℝ) = rd E ^ deg E := by
      unfold rd
      rw [← Real.rpow_natCast, ← Real.rpow_mul hD0, Real.sqrt_eq_rpow]
      congr 1
      rw [(hdeg E).1]
      have : (deg E : ℝ) ≠ 0 := by exact_mod_cast (hdeg E).2.2.ne'
      push_cast; field_simp
    have hNB : (FractionalIdeal.absNorm (idl E g 2 ν) : ℝ)
        = (((g : ℝ) ^ (2 : ℤ) * rd E ^ ν) ^ deg E) ^ 2 := by
      rw [← hN E g 2 ν hg, Real.sq_sqrt]
      exact_mod_cast (FractionalIdeal.absNorm_nonneg _)
    rw [hsq, hNB, abs_of_pos (zpow_pos hrd _), zpow_neg]
    have ha : 0 < rd E ^ ν := zpow_pos hrd _
    set a := rd E ^ ν
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
    push_cast
    have hG : (g : ℝ) ^ deg E ≠ 0 := by positivity
    have hA : a ^ deg E ≠ 0 := by positivity
    rw [inv_pow, inv_pow, div_pow, pow_mul, mul_pow, mul_pow]
    field_simp
    ring

end Formalism.FourierDecayAlt.P.S6x2

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.S6 Formalism.FourierDecayAlt.P.S6x2

/- English proof (translation)
The claim follows from `powConjStable`.
-/
theorem different_power_conj_stable : Formalism.FourierDecayAlt.S6.PowConjStable := powConjStable

/- English proof (translation)
The claim follows from `dualSubset dual_third_group_holds powConjStable between`.
-/
theorem dual_lattice_subset : Formalism.FourierDecayAlt.S6.DualSubset :=
  dualSubset dual_third_group_holds powConjStable between

/- English proof (translation)
The claim follows from `leastNorm dual_third_group_holds norm_lower_bound powConjStable between normIdl`.
-/
theorem least_norm_in_ideal : Formalism.FourierDecayAlt.S6.LeastNorm :=
  leastNorm dual_third_group_holds norm_lower_bound powConjStable between normIdl

/- English proof (translation)
The claim follows from `sizeQuotient least_norm_in_ideal dual_size_identity degreeFacts`.
-/
theorem size_quotient_identity : Formalism.FourierDecayAlt.S6.SizeQuotient :=
  sizeQuotient least_norm_in_ideal dual_size_identity degreeFacts

/- English proof (translation)
Introduce `h1 hW hD hdeg h2 h3 hN` and use `⟨leastNorm h1 hW h2 h3 hN, sizeQuotient (leastNorm h1 hW h2 h3 hN) hD hdeg⟩`.
-/
theorem assemble_least_norm_and_sizes : Formalism.FourierDecayAlt.S6.AssembleLeast :=
  fun h1 hW hD hdeg h2 h3 hN =>
    ⟨leastNorm h1 hW h2 h3 hN, sizeQuotient (leastNorm h1 hW h2 h3 hN) hD hdeg⟩

/- English proof (translation)
The claim follows from `assembleLocal`.
-/
theorem assemble_local_conditions : Formalism.FourierDecayAlt.S6.AssembleLocal := assembleLocal

/- English proof (translation)
The claim follows from `assembleLattices`.
-/
theorem assemble_lattice_facts : Formalism.FourierDecayAlt.S6.AssembleLattices := assembleLattices

/- English proof (translation)
The claim follows from `typedModel locTw locTyped`.
-/
theorem typed_local_model : Formalism.FourierDecayAlt.S6.TypedModel := typedModel locTw locTyped

end Formalism.FourierDecayAlt.P
