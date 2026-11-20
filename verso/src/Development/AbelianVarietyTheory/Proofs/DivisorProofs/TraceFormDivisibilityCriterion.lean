import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormEqNegOne

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.SkewTrace

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev Jd (E : Type) [Field E] [NumberField E] : FractionalIdeal (𝓞 E)⁰ E :=
  FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)

/- English proof (translation)
The claim follows from `FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero`.
-/
theorem Jd_ne_zero : Jd E ≠ 0 := FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero

/- English proof (translation)
Rewrite using `[FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0)]`. Prove the components needed by the constructor for the conclusion. Introduce `h b`. Take `⟨m, hm⟩` from `h (b : E) (by simpa using FractionalIdeal.coe_mem_one (𝓞 E)⁰ b)`. Conclude with `⟨m, by simpa using hm.symm⟩`.

Introduce `h a ha`. Take `⟨b, rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 ha`. Take `⟨m, hm⟩` from `h b`. Conclude with `⟨m, by simp [Algebra.traceForm_apply, hm]⟩`.
-/
theorem mem_Jd_iff (y : E) : y ∈ Jd E ↔ ∀ b : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (y * b) = m := by
  rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0)]
  constructor
  · intro h b
    obtain ⟨m, hm⟩ := h (b : E) (by simpa using FractionalIdeal.coe_mem_one (𝓞 E)⁰ b)
    exact ⟨m, by simpa using hm.symm⟩
  · intro h a ha
    obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    obtain ⟨m, hm⟩ := h b
    exact ⟨m, by simp [Algebra.traceForm_apply, hm]⟩

/- English proof (translation)
The claim follows from `Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) y`.
-/
theorem trace_conj (y : E) : Algebra.trace ℚ E (IsCMField.complexConj E y) = Algebra.trace ℚ E y :=
  Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) y

/- English proof (translation)
The claim follows from `(H.bar_eq a).symm`.
-/
theorem conj_coe (H : Host E) (a : 𝓞 E) : IsCMField.complexConj E (a : E) = ((H.bar a : 𝓞 E) : E) :=
  (H.bar_eq a).symm

local notation "cj" => IsCMField.complexConj E

/- English proof (translation)
Rewrite `hy`, the goal using `[mem_Jd_iff]`. Introduce `b`. Take `⟨m, hm⟩` from `hy (H.bar b)`. Use `⟨m, ?_⟩` and prove the remaining obligations. Rewrite using `[← trace_conj, map_mul, IsCMField.complexConj_apply_apply, conj_coe H, hm]`.
-/
theorem conj_mem_Jd (H : Host E) {y : E} (hy : y ∈ Jd E) : cj y ∈ Jd E := by
  rw [mem_Jd_iff] at hy ⊢
  intro b
  obtain ⟨m, hm⟩ := hy (H.bar b)
  refine ⟨m, ?_⟩
  rw [← trace_conj, map_mul, IsCMField.complexConj_apply_apply, conj_coe H, hm]

/- English proof (translation)
Use `(I : Submodule (𝓞 E) E).smul_mem a hz` as an intermediate fact. Rewrite `this` using `[Algebra.smul_def]`. Then use the resulting hypothesis.
-/
theorem mul_mem_of_mem (I : FractionalIdeal (𝓞 E)⁰ E) (a : 𝓞 E) {z : E} (hz : z ∈ I) : (a : E) * z ∈ I := by
  have := (I : Submodule (𝓞 E) E).smul_mem a hz
  rwa [Algebra.smul_def] at this

/- English proof (translation)
The claim follows from `(I : Submodule (𝓞 E) E).add_mem ha hb`.
-/
theorem fadd {I : FractionalIdeal (𝓞 E)⁰ E} {a b : E} (ha : a ∈ I) (hb : b ∈ I) : a + b ∈ I :=
  (I : Submodule (𝓞 E) E).add_mem ha hb

/- English proof (translation)
The claim follows from `(I : Submodule (𝓞 E) E).sub_mem ha hb`.
-/
theorem fsub {I : FractionalIdeal (𝓞 E)⁰ E} {a b : E} (ha : a ∈ I) (hb : b ∈ I) : a - b ∈ I :=
  (I : Submodule (𝓞 E) E).sub_mem ha hb

/- English proof (translation)
The claim follows from `(I : Submodule (𝓞 E) E).neg_mem ha`.
-/
theorem fneg {I : FractionalIdeal (𝓞 E)⁰ E} {a : E} (ha : a ∈ I) : -a ∈ I :=
  (I : Submodule (𝓞 E) E).neg_mem ha

/- English proof (translation)
The claim follows from `FractionalIdeal.mem_coeIdeal_of_mem _ ha`.
-/
theorem coe_mem_coeIdeal {P : Ideal (𝓞 E)} {a : 𝓞 E} (ha : a ∈ P) : (a : E) ∈ (P : FractionalIdeal (𝓞 E)⁰ E) :=
  FractionalIdeal.mem_coeIdeal_of_mem _ ha

/- English proof (translation)
Take `⟨u, π, hπ, hu⟩` from `hP.exists_inv he`. Establish `e1 : z = (u : E) * ((e : E) * z) + (π : E) * z`. Establish `: ((u * e + π : 𝓞 E) : E) = 1` using `by rw [hu]; simp`. Move the coercions through the operations in `at this`. Take the linear combination `(-z) * this`.

Rewrite using `[e1]`. Conclude with `fadd (mul_mem_of_mem _ u hez) (FractionalIdeal.mul_mem_mul (coe_mem_coeIdeal hπ) hz)`.
-/
theorem mem_of_mul_mem {P : Ideal (𝓞 E)} (hP : P.IsMaximal) {e : 𝓞 E} (he : e ∉ P) {z : E} (hz : z ∈ Jd E)
    (hez : (e : E) * z ∈ (P : FractionalIdeal (𝓞 E)⁰ E) * Jd E) : z ∈ (P : FractionalIdeal (𝓞 E)⁰ E) * Jd E := by
  obtain ⟨u, π, hπ, hu⟩ := hP.exists_inv he
  have e1 : z = (u : E) * ((e : E) * z) + (π : E) * z := by
    have : ((u * e + π : 𝓞 E) : E) = 1 := by rw [hu]; simp
    push_cast at this
    linear_combination (-z) * this
  rw [e1]
  exact fadd (mul_mem_of_mem _ u hez) (FractionalIdeal.mul_mem_mul (coe_mem_coeIdeal hπ) hz)

/- English proof (translation)
Introduce `h`. Establish `h1 : 1 * Jd E ≤ (P : FractionalIdeal (𝓞 E)⁰ E) * Jd E` using `by rwa [one_mul]`. Establish `h2` using `mul_le_mul' h1 (le_refl (Jd E)⁻¹)`. Rewrite `h2` using `[mul_assoc, mul_assoc, mul_inv_cancel₀ Jd_ne_zero, mul_one, mul_one, ← FractionalIdeal.coeIdeal_top, FractionalIdeal.coeIdeal_le_coeIdeal]`. Establish `h1` using `h2`.

Conclude with `hP (top_le_iff.1 h1)`.
-/
theorem Jd_not_le {P : Ideal (𝓞 E)} (hP : P ≠ ⊤) : ¬ Jd E ≤ (P : FractionalIdeal (𝓞 E)⁰ E) * Jd E := by
  intro h
  have h1 : 1 * Jd E ≤ (P : FractionalIdeal (𝓞 E)⁰ E) * Jd E := by rwa [one_mul]
  have h2 := mul_le_mul' h1 (le_refl (Jd E)⁻¹)
  rw [mul_assoc, mul_assoc, mul_inv_cancel₀ Jd_ne_zero, mul_one, mul_one, ← FractionalIdeal.coeIdeal_top,
    FractionalIdeal.coeIdeal_le_coeIdeal] at h2
  have h1 := h2
  exact hP (top_le_iff.1 h1)

/- English proof (translation)
Take `⟨w0, hw0, hw0P⟩` from `Set.not_subset.1 (Jd_not_le (E := E) hP.ne_top)`. Assume the negation of the conclusion as `hno`. Use `push_neg at hno`. Establish `key : ∀ w ∈ Jd E, w - cj w ∈ (P : FractionalIdeal (𝓞 E)⁰ E) * Jd E` using `fun w hw => hno _ (fsub hw (conj_mem_Jd H hw)) (by rw [map_sub, IsCMField.complexConj_apply_apply]; ring)`. Take `⟨y, hy⟩` from `GlobalTheory.IsoCols.exists_sub_bar_notMem H hP.ne_top`.

Establish `h1` using `key _ (mul_mem_of_mem _ y hw0)`. Establish `h2` using `key _ hw0`. Establish `e : ((y - H.bar y : 𝓞 E) : E) * w0 = ((y : E) * w0 - cj ((y : E) * w0)) - (H.bar y : E) * (w0 - cj w0)`. Rewrite using `[map_mul, conj_coe H]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `h3 : ((y - H.bar y : 𝓞 E) : E) * w0 ∈ (P : FractionalIdeal (𝓞 E)⁰ E) * Jd E`. Rewrite using `[e]`. Conclude with `fsub h1 (mul_mem_of_mem _ _ h2)`. Conclude with `hw0P (mem_of_mul_mem hP hy hw0 h3)`.
-/
theorem exists_skew_notMem (H : Host E) {P : Ideal (𝓞 E)} (hP : P.IsMaximal) :
    ∃ z ∈ Jd E, cj z = -z ∧ z ∉ (P : FractionalIdeal (𝓞 E)⁰ E) * Jd E := by
  obtain ⟨w0, hw0, hw0P⟩ := Set.not_subset.1 (Jd_not_le (E := E) hP.ne_top)
  by_contra hno
  push_neg at hno
  have key : ∀ w ∈ Jd E, w - cj w ∈ (P : FractionalIdeal (𝓞 E)⁰ E) * Jd E := fun w hw =>
    hno _ (fsub hw (conj_mem_Jd H hw)) (by rw [map_sub, IsCMField.complexConj_apply_apply]; ring)
  obtain ⟨y, hy⟩ := GlobalTheory.IsoCols.exists_sub_bar_notMem H hP.ne_top
  have h1 := key _ (mul_mem_of_mem _ y hw0)
  have h2 := key _ hw0
  have e : ((y - H.bar y : 𝓞 E) : E) * w0 = ((y : E) * w0 - cj ((y : E) * w0)) - (H.bar y : E) * (w0 - cj w0) := by
    rw [map_mul, conj_coe H]; push_cast; ring
  have h3 : ((y - H.bar y : 𝓞 E) : E) * w0 ∈ (P : FractionalIdeal (𝓞 E)⁰ E) * Jd E := by
    rw [e]; exact fsub h1 (mul_mem_of_mem _ _ h2)
  exact hw0P (mem_of_mul_mem hP hy hw0 h3)

/- English proof (translation)
Use `FractionalIdeal.mul_induction_on hy (fun i hi j hj => ?_) (fun a b ha hb => ?_)` and prove the remaining obligations. Take `⟨a, ha, rfl⟩` from `(FractionalIdeal.mem_coeIdeal _).1 hi`. Rewrite using `[map_mul]`. Establish `: IsCMField.complexConj E (algebraMap (𝓞 E) E a) = ((H.bar a : 𝓞 E) : E)` using `conj_coe H a`. Rewrite using `[this]`.

Use `FractionalIdeal.mul_mem_mul (coe_mem_coeIdeal ?_) (conj_mem_Jd H hj)` and prove the remaining obligations. Rewrite using `[Ideal.mem_comap]`. Simplify `ha` using `[GlobalTheory.IsoCols.bar_bar]`. Rewrite using `[map_add]`. Conclude with `fadd ha hb`.
-/
theorem conj_mem_mul (H : Host E) {P : Ideal (𝓞 E)} {y : E} (hy : y ∈ (P : FractionalIdeal (𝓞 E)⁰ E) * Jd E) :
    cj y ∈ ((P.comap (H.bar : 𝓞 E →+* 𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) * Jd E := by
  refine FractionalIdeal.mul_induction_on hy (fun i hi j hj => ?_) (fun a b ha hb => ?_)
  · obtain ⟨a, ha, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hi
    rw [map_mul]
    have : IsCMField.complexConj E (algebraMap (𝓞 E) E a) = ((H.bar a : 𝓞 E) : E) := conj_coe H a
    rw [this]
    refine FractionalIdeal.mul_mem_mul (coe_mem_coeIdeal ?_) (conj_mem_Jd H hj)
    rw [Ideal.mem_comap]
    simpa [GlobalTheory.IsoCols.bar_bar] using ha
  · rw [map_add]; exact fadd ha hb

/- English proof (translation)
Establish `key : ∀ C : Ideal (𝓞 E), C.IsPrime → C ∉ S → ∃ f : 𝓞 E, (∀ Q ∈ S, f ∈ Q) ∧ f ∉ C`. Introduce `C hC hCS`. Establish `h1 : ¬ S.inf id ≤ C`. Rewrite using `[hC.inf_le']`. Introduce and unpack `⟨Q, hQ, hle⟩`.

Conclude with `hCS (((hS Q hQ).eq_of_le hC.ne_top hle) ▸ hQ)`. Take `⟨f, hf, hfC⟩` from `Set.not_subset.1 h1`. Use `⟨f, fun Q hQ => ?_, hfC⟩` and prove the remaining obligations. Conclude with `(Finset.inf_le hQ : S.inf id ≤ id Q) hf`. Take `⟨f1, h1S, h1A⟩` from `key A hA hAS`.

Take `⟨f2, h2S, h2B⟩` from `key B hB hBS`. Distinguish the cases in `h1B : f1 ∈ B`. Distinguish the cases in `h2A : f2 ∈ A`. Use `⟨f1 + f2, fun Q hQ => Q.add_mem (h1S Q hQ) (h2S Q hQ), fun h => h1A ?_, fun h => h2B ?_⟩` and prove the remaining obligations. Simplify using `using A.sub_mem h h2A`.

Simplify using `using B.sub_mem h h1B`. Conclude with `⟨f2, h2S, h2A, h2B⟩`. Conclude with `⟨f1, h1S, h1A, h1B⟩`.
-/
theorem exists_avoid2 (S : Finset (Ideal (𝓞 E))) (hS : ∀ Q ∈ S, Q.IsMaximal) {A B : Ideal (𝓞 E)}
    (hA : A.IsPrime) (hB : B.IsPrime) (hAS : A ∉ S) (hBS : B ∉ S) :
    ∃ f : 𝓞 E, (∀ Q ∈ S, f ∈ Q) ∧ f ∉ A ∧ f ∉ B := by
  have key : ∀ C : Ideal (𝓞 E), C.IsPrime → C ∉ S → ∃ f : 𝓞 E, (∀ Q ∈ S, f ∈ Q) ∧ f ∉ C := by
    intro C hC hCS
    have h1 : ¬ S.inf id ≤ C := by
      rw [hC.inf_le']
      rintro ⟨Q, hQ, hle⟩
      exact hCS (((hS Q hQ).eq_of_le hC.ne_top hle) ▸ hQ)
    obtain ⟨f, hf, hfC⟩ := Set.not_subset.1 h1
    refine ⟨f, fun Q hQ => ?_, hfC⟩
    exact (Finset.inf_le hQ : S.inf id ≤ id Q) hf
  obtain ⟨f1, h1S, h1A⟩ := key A hA hAS
  obtain ⟨f2, h2S, h2B⟩ := key B hB hBS
  by_cases h1B : f1 ∈ B
  · by_cases h2A : f2 ∈ A
    · refine ⟨f1 + f2, fun Q hQ => Q.add_mem (h1S Q hQ) (h2S Q hQ), fun h => h1A ?_, fun h => h2B ?_⟩
      · simpa using A.sub_mem h h2A
      · simpa using B.sub_mem h h1B
    · exact ⟨f2, h2S, h2A, h2B⟩
  · exact ⟨f1, h1S, h1A, h1B⟩

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact ⟨0, (Jd E : Submodule (𝓞 E) E).zero_mem, by simp, by simp⟩`. Consider the case `@insert P S hPS ih`. Take `⟨x, hxJ, hxs, hxS⟩` from `ih (fun Q hQ => hS Q (Finset.mem_insert_of_mem hQ))`. Establish `hP` using `hS P (Finset.mem_insert_self P S)`.

Distinguish the cases in `hxP : x ∈ (P : FractionalIdeal (𝓞 E)⁰ E) * Jd E`. Use `swap`. Use `⟨x, hxJ, hxs, fun Q hQ => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hQ with rfl | hQ` into its components or cases. Use `exacts [hxP, hxS Q hQ]`.

Use `set P' := P.comap (H.bar : 𝓞 E →+* 𝓞 E) with hP'def`. Establish `hP'p : P'.IsPrime` using `Ideal.comap_isPrime _ _`. Distinguish the cases in `hP' : P' ∈ S`. It suffices to derive a contradiction. Apply `hxS P' hP'` to reduce the goal to its premises.

Use `fneg (conj_mem_mul H hxP)` as an intermediate fact. Rewrite `this` using `[hxs, neg_neg]`. Then use the resulting hypothesis. Take `⟨f, hfS, hfP, hfP'⟩` from `exists_avoid2 S (fun Q hQ => hS Q (Finset.mem_insert_of_mem hQ)) hP.isPrime hP'p hPS hP'`. Use `set e : 𝓞 E := f * H.bar f with hedef`. Establish `he : H.bar e = e` using `by rw [hedef, map_mul, GlobalTheory.IsoCols.bar_bar, mul_comm]`.

Establish `heP : e ∉ P`. Use `hP.isPrime.mul_notMem hfP ?_` and prove the remaining obligations. Simplify `hfP'` using `[hP'def, Ideal.mem_comap]`. Take `⟨z, hzJ, hzs, hzP⟩` from `exists_skew_notMem H hP`. Use `⟨x + (e : E) * z, fadd hxJ (mul_mem_of_mem _ e hzJ), ?_, fun Q hQ hmem => ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add, map_mul, conj_coe H, he, hxs, hzs]`. Expand and normalize the polynomial expressions, which then agree. Break down `Finset.mem_insert.1 hQ with rfl | hQ` into its components or cases. Establish `h1 : (e : E) * z ∈ (Q : FractionalIdeal (𝓞 E)⁰ E) * Jd E`. Use `fsub hmem hxP` as an intermediate fact.

Rewrite `this` using `[add_sub_cancel_left]`. Then use the resulting hypothesis. Conclude with `hzP (mem_of_mul_mem hP heP hzJ h1)`. Establish `h1 : (e : E) * z ∈ (Q : FractionalIdeal (𝓞 E)⁰ E) * Jd E` using `FractionalIdeal.mul_mem_mul (coe_mem_coeIdeal (Q.mul_mem_right _ (hfS Q hQ))) hzJ`. Apply `hxS Q hQ` to reduce the goal to its premises. Use `fsub hmem h1` as an intermediate fact.

Rewrite `this` using `[add_sub_cancel_right]`. Then use the resulting hypothesis.
-/
theorem exists_skew_avoid (H : Host E) (S : Finset (Ideal (𝓞 E))) (hS : ∀ P ∈ S, P.IsMaximal) :
    ∃ x ∈ Jd E, cj x = -x ∧ ∀ P ∈ S, x ∉ (P : FractionalIdeal (𝓞 E)⁰ E) * Jd E := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, (Jd E : Submodule (𝓞 E) E).zero_mem, by simp, by simp⟩
  | @insert P S hPS ih =>
    obtain ⟨x, hxJ, hxs, hxS⟩ := ih (fun Q hQ => hS Q (Finset.mem_insert_of_mem hQ))
    have hP := hS P (Finset.mem_insert_self P S)
    by_cases hxP : x ∈ (P : FractionalIdeal (𝓞 E)⁰ E) * Jd E
    swap
    · refine ⟨x, hxJ, hxs, fun Q hQ => ?_⟩
      rcases Finset.mem_insert.1 hQ with rfl | hQ
      exacts [hxP, hxS Q hQ]
    set P' := P.comap (H.bar : 𝓞 E →+* 𝓞 E) with hP'def
    have hP'p : P'.IsPrime := Ideal.comap_isPrime _ _
    by_cases hP' : P' ∈ S
    · exfalso
      apply hxS P' hP'
      have := fneg (conj_mem_mul H hxP)
      rwa [hxs, neg_neg] at this
    obtain ⟨f, hfS, hfP, hfP'⟩ := exists_avoid2 S (fun Q hQ => hS Q (Finset.mem_insert_of_mem hQ))
      hP.isPrime hP'p hPS hP'
    set e : 𝓞 E := f * H.bar f with hedef
    have he : H.bar e = e := by rw [hedef, map_mul, GlobalTheory.IsoCols.bar_bar, mul_comm]
    have heP : e ∉ P := by
      refine hP.isPrime.mul_notMem hfP ?_
      simpa [hP'def, Ideal.mem_comap] using hfP'
    obtain ⟨z, hzJ, hzs, hzP⟩ := exists_skew_notMem H hP
    refine ⟨x + (e : E) * z, fadd hxJ (mul_mem_of_mem _ e hzJ), ?_, fun Q hQ hmem => ?_⟩
    · rw [map_add, map_mul, conj_coe H, he, hxs, hzs]; ring
    · rcases Finset.mem_insert.1 hQ with rfl | hQ
      · have h1 : (e : E) * z ∈ (Q : FractionalIdeal (𝓞 E)⁰ E) * Jd E := by
          have := fsub hmem hxP; rwa [add_sub_cancel_left] at this
        exact hzP (mem_of_mul_mem hP heP hzJ h1)
      · have h1 : (e : E) * z ∈ (Q : FractionalIdeal (𝓞 E)⁰ E) * Jd E :=
          FractionalIdeal.mul_mem_mul (coe_mem_coeIdeal (Q.mul_mem_right _ (hfS Q hQ))) hzJ
        apply hxS Q hQ
        have := fsub hmem h1; rwa [add_sub_cancel_right] at this

/- English proof (translation)
Introduce `E _ _ _ H N hN`. Establish `hN0 : (N : 𝓞 E) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `hspan : Ideal.span {(N : 𝓞 E)} ≠ 0`. Rewrite using `[Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hN0`.

Establish `hfin` using `Ideal.finite_factors hspan`. Set `S : Finset (Ideal (𝓞 E))` to `hfin.toFinset.image (fun v => v.asIdeal)`. Establish `hS : ∀ P ∈ S, P.IsMaximal`. Introduce `P hP`. Take `⟨v, -, rfl⟩` from `Finset.mem_image.1 hP`.

Conclude with `v.isMaximal`. Establish `hSmem : ∀ P : Ideal (𝓞 E), P.IsMaximal → (N : 𝓞 E) ∈ P → P ∈ S`. Introduce `P hP hNP`. Establish `hPb : P ≠ ⊥` using `fun h => hN0 (by rw [h] at hNP; exact (Ideal.mem_bot).1 hNP)`. Use `Finset.mem_image.2 ⟨⟨P, hP.isPrime, hPb⟩, ?_, rfl⟩` and prove the remaining obligations.

Rewrite using `[Set.Finite.mem_toFinset]`. Use `show P ∣ _`. Rewrite using `[Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]`. Conclude with `hNP`. Take `⟨x, hxJ, hxs, hxS⟩` from `exists_skew_avoid H S hS`.

Establish `htr : ∀ c : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (x * c) = m` using `(mem_Jd_iff x).1 hxJ`. Set `T : 𝓞 E →+ ℤ` to `{ toFun := fun c => ⌊Algebra.trace ℚ E (x * c)⌋ map_zero' := by simp map_add' := by`. Introduce `a b`. Take `⟨m1, h1⟩` from `htr a`. Take `⟨m2, h2⟩` from `htr b`.

Take `⟨m3, h3⟩` from `htr (a + b)`. Establish `e : (m3 : ℚ) = m1 + m2`. Rewrite using `[← h1, ← h2, ← h3]`. Use `push_cast`. Rewrite using `[mul_add, map_add]`.

Use `show ⌊Algebra.trace ℚ E (x * ((a + b : 𝓞 E) : E))⌋ = ⌊Algebra.trace ℚ E (x * (a : E))⌋ + ⌊Algebra.trace ℚ E (x * (b : E))⌋`. Rewrite using `[h1, h2, h3, Int.floor_intCast, Int.floor_intCast, Int.floor_intCast]`. Conclude with `e }` after adjusting the coercions. Establish `hT : ∀ c, ((T c : ℤ) : ℚ) = Algebra.trace ℚ E (x * c)` using `fun c => by`. Take `⟨m, hm⟩` from `htr c`.

Use `show ((⌊Algebra.trace ℚ E (x * c)⌋ : ℤ) : ℚ) = _`. Rewrite using `[hm, Int.floor_intCast]`. Use `⟨T, fun c => ?_, fun c hc => ?_⟩` and prove the remaining obligations. Establish `: ((T (H.bar c) : ℤ) : ℚ) = -((T c : ℤ) : ℚ)`. Rewrite using `[hT, hT]`.

Establish `ec : IsCMField.complexConj E (IsCMField.complexConj E x * c) = x * ((H.bar c : 𝓞 E) : E)`. Rewrite using `[map_mul (IsCMField.complexConj E), IsCMField.complexConj_apply_apply, conj_coe H]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ec]`. Use `_ = Algebra.trace ℚ E (IsCMField.complexConj E x * c) := trace_conj _`.

Use `_ = -Algebra.trace ℚ E (x * c) := by rw [hxs, neg_mul, map_neg]`. Conclude with `this` after adjusting the coercions. Establish `hNq : (N : ℚ) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `hy : x * c / (N : E) ∈ Jd E`. Rewrite using `[mem_Jd_iff]`.

Introduce `d`. Take `⟨k, hk⟩` from `hc d`. Use `⟨k, ?_⟩` and prove the remaining obligations. Establish `h1` using `hT (c * d)`. Rewrite `h1` using `[hk]`.

Establish `e : x * c / (N : E) * d = (N : ℚ)⁻¹ • (x * ((c * d : 𝓞 E) : E))`. Rewrite using `[Algebra.smul_def]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, LinearMap.map_smul, ← h1, smul_eq_mul]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Use `set J := Jd E with hJdef`. Establish `hJ0 : J ≠ 0` using `Jd_ne_zero`. Establish `hxc : x * (c : E) ∈ FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E) * J`.

Establish `e : x * (c : E) = (N : E) * (x * c / (N : E))`. Establish `: (N : E) ≠ 0` using `by exact_mod_cast hN.ne'`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) hy`.

Set `I` to `FractionalIdeal.spanSingleton (𝓞 E)⁰ x * J⁻¹`. Establish `hIle : I ≤ 1`. Establish `h1 : FractionalIdeal.spanSingleton (𝓞 E)⁰ x ≤ J` using `(FractionalIdeal.spanSingleton_le_iff_mem).2 hxJ`. Combine the equalities or inequalities in the displayed calculation. Take `⟨I0, hI0⟩` from `FractionalIdeal.le_one_iff_exists_coeIdeal.1 hIle`.

Establish `hIJ : I * J = FractionalIdeal.spanSingleton (𝓞 E)⁰ x` using `by show FractionalIdeal.spanSingleton (𝓞 E)⁰ x * J⁻¹ * J = _`. Rewrite using `[mul_assoc, inv_mul_cancel₀ hJ0, mul_one]`. Establish `hI0P : ∀ P ∈ S, ¬ I0 ≤ P`. Introduce `P hP hle`. Apply `hxS P hP` to reduce the goal to its premises.

Establish `h1` using `mul_le_mul' ((FractionalIdeal.coeIdeal_le_coeIdeal E).2 hle) (le_refl J)`. Rewrite `h1` using `[hI0, hIJ]`. Conclude with `h1 (FractionalIdeal.mem_spanSingleton_self _ x)`. Establish `hcop : I0 ⊔ Ideal.span {(N : 𝓞 E)} = ⊤`. Assume the negation of the conclusion as `h`.

Take `⟨P, hP, hle⟩` from `Ideal.exists_le_maximal _ h`. Use `hI0P P (hSmem P hP ?_) (le_sup_left.trans hle)` and prove the remaining obligations. Conclude with `hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))`. Establish `hmul : I0 * Ideal.span {c} ≤ Ideal.span {(N : 𝓞 E)}`. Rewrite using `[← FractionalIdeal.coeIdeal_le_coeIdeal E, FractionalIdeal.coeIdeal_mul, hI0, FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton]`.

Establish `h1 : FractionalIdeal.spanSingleton (𝓞 E)⁰ x * FractionalIdeal.spanSingleton (𝓞 E)⁰ (c : E) ≤ FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E) * J`. Rewrite using `[FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.spanSingleton_le_iff_mem]`. Conclude with `hxc`. Establish `hc' : algebraMap (𝓞 E) E c = (c : E)` using `rfl`. Establish `hN' : algebraMap (𝓞 E) E (N : 𝓞 E) = (N : E)` using `map_natCast _ _`.

Rewrite using `[hc', hN']`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_right_comm]`. Use `_ ≤ (FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E) * J) * J⁻¹ := mul_le_mul' h1 le_rfl`. Use `_ = FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E) := by rw [mul_assoc, mul_inv_cancel₀ hJ0, mul_one]`.

Establish `hle : Ideal.span {c} ≤ Ideal.span {(N : 𝓞 E)}`. Combine the equalities or inequalities in the displayed calculation. Take `⟨b, hb⟩` from `Ideal.mem_span_singleton'.1 (hle (Ideal.mem_span_singleton_self c))`. Conclude with `⟨b, by rw [nsmul_eq_mul, ← hb, mul_comm]⟩`.
-/
theorem exists_skew_perfect : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (N : ℕ), 0 < N →
    ∃ T : 𝓞 E →+ ℤ, (∀ c, T (H.bar c) = - T c) ∧
      ∀ c : 𝓞 E, (∀ d : 𝓞 E, (N : ℤ) ∣ T (c * d)) → ∃ b : 𝓞 E, c = N • b := by
  intro E _ _ _ H N hN
  classical
  have hN0 : (N : 𝓞 E) ≠ 0 := by exact_mod_cast hN.ne'
  have hspan : Ideal.span {(N : 𝓞 E)} ≠ 0 := by
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]; exact hN0
  have hfin := Ideal.finite_factors hspan
  let S : Finset (Ideal (𝓞 E)) := hfin.toFinset.image (fun v => v.asIdeal)
  have hS : ∀ P ∈ S, P.IsMaximal := by
    intro P hP
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hP
    exact v.isMaximal
  have hSmem : ∀ P : Ideal (𝓞 E), P.IsMaximal → (N : 𝓞 E) ∈ P → P ∈ S := by
    intro P hP hNP
    have hPb : P ≠ ⊥ := fun h => hN0 (by rw [h] at hNP; exact (Ideal.mem_bot).1 hNP)
    refine Finset.mem_image.2 ⟨⟨P, hP.isPrime, hPb⟩, ?_, rfl⟩
    rw [Set.Finite.mem_toFinset]
    show P ∣ _
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hNP
  obtain ⟨x, hxJ, hxs, hxS⟩ := exists_skew_avoid H S hS
  have htr : ∀ c : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (x * c) = m := (mem_Jd_iff x).1 hxJ
  let T : 𝓞 E →+ ℤ :=
    { toFun := fun c => ⌊Algebra.trace ℚ E (x * c)⌋
      map_zero' := by simp
      map_add' := by
        intro a b
        obtain ⟨m1, h1⟩ := htr a
        obtain ⟨m2, h2⟩ := htr b
        obtain ⟨m3, h3⟩ := htr (a + b)
        have e : (m3 : ℚ) = m1 + m2 := by
          rw [← h1, ← h2, ← h3]; push_cast; rw [mul_add, map_add]
        show ⌊Algebra.trace ℚ E (x * ((a + b : 𝓞 E) : E))⌋ = ⌊Algebra.trace ℚ E (x * (a : E))⌋ + ⌊Algebra.trace ℚ E (x * (b : E))⌋
        rw [h1, h2, h3, Int.floor_intCast, Int.floor_intCast, Int.floor_intCast]
        exact_mod_cast e }
  have hT : ∀ c, ((T c : ℤ) : ℚ) = Algebra.trace ℚ E (x * c) := fun c => by
    obtain ⟨m, hm⟩ := htr c
    show ((⌊Algebra.trace ℚ E (x * c)⌋ : ℤ) : ℚ) = _
    rw [hm, Int.floor_intCast]
  refine ⟨T, fun c => ?_, fun c hc => ?_⟩
  · have : ((T (H.bar c) : ℤ) : ℚ) = -((T c : ℤ) : ℚ) := by
      rw [hT, hT]
      have ec : IsCMField.complexConj E (IsCMField.complexConj E x * c) = x * ((H.bar c : 𝓞 E) : E) := by
        rw [map_mul (IsCMField.complexConj E), IsCMField.complexConj_apply_apply, conj_coe H]
      calc Algebra.trace ℚ E (x * ((H.bar c : 𝓞 E) : E))
          = Algebra.trace ℚ E (IsCMField.complexConj E (IsCMField.complexConj E x * c)) := by
            rw [ec]
        _ = Algebra.trace ℚ E (IsCMField.complexConj E x * c) := trace_conj _
        _ = -Algebra.trace ℚ E (x * c) := by rw [hxs, neg_mul, map_neg]
    exact_mod_cast this
  · have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
    have hy : x * c / (N : E) ∈ Jd E := by
      rw [mem_Jd_iff]
      intro d
      obtain ⟨k, hk⟩ := hc d
      refine ⟨k, ?_⟩
      have h1 := hT (c * d)
      rw [hk] at h1
      have e : x * c / (N : E) * d = (N : ℚ)⁻¹ • (x * ((c * d : 𝓞 E) : E)) := by
        rw [Algebra.smul_def]; push_cast; ring
      rw [e, LinearMap.map_smul, ← h1, smul_eq_mul]
      push_cast
      field_simp
    set J := Jd E with hJdef
    have hJ0 : J ≠ 0 := Jd_ne_zero
    have hxc : x * (c : E) ∈ FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E) * J := by
      have e : x * (c : E) = (N : E) * (x * c / (N : E)) := by
        have : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
        field_simp
      rw [e]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) hy
    let I := FractionalIdeal.spanSingleton (𝓞 E)⁰ x * J⁻¹
    have hIle : I ≤ 1 := by
      have h1 : FractionalIdeal.spanSingleton (𝓞 E)⁰ x ≤ J := (FractionalIdeal.spanSingleton_le_iff_mem).2 hxJ
      calc I ≤ J * J⁻¹ := mul_le_mul' h1 le_rfl
        _ = 1 := mul_inv_cancel₀ hJ0
    obtain ⟨I0, hI0⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hIle
    have hIJ : I * J = FractionalIdeal.spanSingleton (𝓞 E)⁰ x := by
      show FractionalIdeal.spanSingleton (𝓞 E)⁰ x * J⁻¹ * J = _
      rw [mul_assoc, inv_mul_cancel₀ hJ0, mul_one]
    have hI0P : ∀ P ∈ S, ¬ I0 ≤ P := by
      intro P hP hle
      apply hxS P hP
      have h1 := mul_le_mul' ((FractionalIdeal.coeIdeal_le_coeIdeal E).2 hle) (le_refl J)
      rw [hI0, hIJ] at h1
      exact h1 (FractionalIdeal.mem_spanSingleton_self _ x)
    have hcop : I0 ⊔ Ideal.span {(N : 𝓞 E)} = ⊤ := by
      by_contra h
      obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ h
      refine hI0P P (hSmem P hP ?_) (le_sup_left.trans hle)
      exact hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hmul : I0 * Ideal.span {c} ≤ Ideal.span {(N : 𝓞 E)} := by
      rw [← FractionalIdeal.coeIdeal_le_coeIdeal E, FractionalIdeal.coeIdeal_mul, hI0,
        FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton]
      have h1 : FractionalIdeal.spanSingleton (𝓞 E)⁰ x * FractionalIdeal.spanSingleton (𝓞 E)⁰ (c : E) ≤
          FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E) * J := by
        rw [FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.spanSingleton_le_iff_mem]
        exact hxc
      have hc' : algebraMap (𝓞 E) E c = (c : E) := rfl
      have hN' : algebraMap (𝓞 E) E (N : 𝓞 E) = (N : E) := map_natCast _ _
      rw [hc', hN']
      calc FractionalIdeal.spanSingleton (𝓞 E)⁰ x * J⁻¹ * FractionalIdeal.spanSingleton (𝓞 E)⁰ (c : E)
          = (FractionalIdeal.spanSingleton (𝓞 E)⁰ x * FractionalIdeal.spanSingleton (𝓞 E)⁰ (c : E)) * J⁻¹ := by
            rw [mul_right_comm]
        _ ≤ (FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E) * J) * J⁻¹ := mul_le_mul' h1 le_rfl
        _ = FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E) := by rw [mul_assoc, mul_inv_cancel₀ hJ0, mul_one]
    have hle : Ideal.span {c} ≤ Ideal.span {(N : 𝓞 E)} := by
      calc Ideal.span {c} = Ideal.span {c} * ⊤ := (Ideal.mul_top _).symm
        _ = Ideal.span {c} * (I0 ⊔ Ideal.span {(N : 𝓞 E)}) := by rw [hcop]
        _ = Ideal.span {c} * I0 ⊔ Ideal.span {c} * Ideal.span {(N : 𝓞 E)} := Ideal.mul_sup _ _ _
        _ ≤ Ideal.span {(N : 𝓞 E)} := sup_le (by rw [mul_comm]; exact hmul) (Ideal.mul_le_inf.trans inf_le_right)
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (hle (Ideal.mem_span_singleton_self c))
    exact ⟨b, by rw [nsmul_eq_mul, ← hb, mul_comm]⟩

end GlobalTheory.SkewTrace
