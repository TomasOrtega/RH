import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.CharacterValuation

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.CharVal

open Formalism.HermitianLatticesTheory Formalism.L2.Col

variable {E : Type} [Field E] [NumberField E]

def detLat [StarRing E] {n : ℕ} (N : Submodule (𝓞 E) (Sp E n)) : Submodule (𝓞 E) E :=
  Submodule.span (𝓞 E) {x | ∃ A : Matrix (Fin n) (Fin n) E, (∀ v ∈ stdLat E n, A.mulVec v ∈ N) ∧ x = A.det}

def MaxV (P : HeightOneSpectrum (𝓞 E)) (I : Submodule (𝓞 E) E) (γ : WithZero (Multiplicative ℤ)) : Prop :=
  (∀ a ∈ I, P.valuation E a ≤ γ) ∧ ∃ a ∈ I, P.valuation E a = γ

variable {P : HeightOneSpectrum (𝓞 E)} {I J : Submodule (𝓞 E) E} {γ δ : WithZero (Multiplicative ℤ)}

open NumberField IsDedekindDomain in
open scoped Pointwise in
variable {E : Type} [Field E] [NumberField E] in
variable {P : HeightOneSpectrum (𝓞 E)} {I J : Submodule (𝓞 E) E} {γ δ : WithZero (Multiplicative ℤ)} in
/- English proof (translation)
Take `⟨a, ha, hγ⟩` from `h.2`. Take `⟨b, hb, hδ⟩` from `h'.2`. Conclude with `le_antisymm (hγ ▸ h'.1 a ha) (hδ ▸ h.1 b hb)`.
-/
theorem _root_.GlobalTheory.CharVal.MaxV.unique (h : _root_.GlobalTheory.CharVal.MaxV P I γ)
    (h' : _root_.GlobalTheory.CharVal.MaxV P I δ) : γ = δ := by
  obtain ⟨a, ha, hγ⟩ := h.2
  obtain ⟨b, hb, hδ⟩ := h'.2
  exact le_antisymm (hγ ▸ h'.1 a ha) (hδ ▸ h.1 b hb)

/- English proof (translation)
Rewrite using `[Algebra.smul_def, map_mul]`. Conclude with `mul_le_of_le_one_left' (P.valuation_le_one r)`.
-/
theorem val_smul_le (r : 𝓞 E) (a : E) : P.valuation E (r • a) ≤ P.valuation E a := by
  rw [Algebra.smul_def, map_mul]
  exact mul_le_of_le_one_left' (P.valuation_le_one r)

open NumberField IsDedekindDomain in
open scoped Pointwise in
variable {E : Type} [Field E] [NumberField E] in
variable {P : HeightOneSpectrum (𝓞 E)} {I J : Submodule (𝓞 E) E} {γ δ : WithZero (Multiplicative ℤ)} in
/- English proof (translation)
Introduce `a ha`. Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem x hx => exact h x hx`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_le'`.

Consider the case `add x y _ _ hx hy => exact (Valuation.map_add _ x y).trans (max_le hx hy)`. Consider the case `smul r x _ hx`. Rewrite using `[Algebra.smul_def, map_mul]`. Conclude with `(mul_le_of_le_one_left' (P.valuation_le_one r)).trans hx`.
-/
theorem _root_.GlobalTheory.CharVal.val_le_of_span {S : Set E} (h : ∀ a ∈ S, P.valuation E a ≤ γ) :
    ∀ a ∈ Submodule.span (𝓞 E) S, P.valuation E a ≤ γ := by
  intro a ha
  induction ha using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => rw [map_zero]; exact zero_le'
  | add x y _ _ hx hy => exact (Valuation.map_add _ x y).trans (max_le hx hy)
  | smul r x _ hx =>
    rw [Algebra.smul_def, map_mul]
    exact (mul_le_of_le_one_left' (P.valuation_le_one r)).trans hx

open NumberField IsDedekindDomain in
open scoped Pointwise in
variable {E : Type} [Field E] [NumberField E] in
variable {P : HeightOneSpectrum (𝓞 E)} {I J : Submodule (𝓞 E) E} {γ δ : WithZero (Multiplicative ℤ)} in
/- English proof (translation)
Assemble the required witnesses or components as `⟨_root_.GlobalTheory.CharVal.val_le_of_span fun a ha => by rw [Set.mem_singleton_iff.1 ha], y, Submodule.mem_span_singleton_self y, rfl⟩`.
-/
theorem _root_.GlobalTheory.CharVal.maxV_span_singleton (y : E) :
    _root_.GlobalTheory.CharVal.MaxV P (Submodule.span (𝓞 E) {y}) (P.valuation E y) :=
  ⟨_root_.GlobalTheory.CharVal.val_le_of_span fun a ha => by rw [Set.mem_singleton_iff.1 ha],
    y, Submodule.mem_span_singleton_self y, rfl⟩

open NumberField IsDedekindDomain in
open scoped Pointwise in
variable {E : Type} [Field E] [NumberField E] in
variable {P : HeightOneSpectrum (𝓞 E)} {I J : Submodule (𝓞 E) E} {γ δ : WithZero (Multiplicative ℤ)} in
/- English proof (translation)
Use `⟨fun a ha => ?_, 1, Submodule.mem_one.2 ⟨1, map_one _⟩, map_one _⟩` and prove the remaining obligations. Take `⟨r, rfl⟩` from `Submodule.mem_one.1 ha`. Conclude with `P.valuation_le_one r`.
-/
theorem _root_.GlobalTheory.CharVal.maxV_one : _root_.GlobalTheory.CharVal.MaxV P (1 : Submodule (𝓞 E) E) 1 := by
  refine ⟨fun a ha => ?_, 1, Submodule.mem_one.2 ⟨1, map_one _⟩, map_one _⟩
  obtain ⟨r, rfl⟩ := Submodule.mem_one.1 ha
  exact P.valuation_le_one r

open NumberField IsDedekindDomain in
open scoped Pointwise in
variable {E : Type} [Field E] [NumberField E] in
variable {P : HeightOneSpectrum (𝓞 E)} {I J : Submodule (𝓞 E) E} {γ δ : WithZero (Multiplicative ℤ)} in
/- English proof (translation)
Take `⟨a, ha, hγ⟩` from `h.2`. Take `⟨b, hb, hδ⟩` from `h'.2`. Use `⟨fun x hx => ?_, a * b, Submodule.mul_mem_mul ha hb, by rw [map_mul, hγ, hδ]⟩` and prove the remaining obligations. Rewrite `hx` using `[Submodule.mul_eq_span_mul_set]`. Use `_root_.GlobalTheory.CharVal.val_le_of_span (fun z hz => ?_) x hx` and prove the remaining obligations.

Take `⟨u, hu, w, hw, rfl⟩` from `Set.mem_mul.1 hz`. Rewrite using `[map_mul]`. Conclude with `mul_le_mul' (h.1 u hu) (h'.1 w hw)`.
-/
theorem _root_.GlobalTheory.CharVal.MaxV.mul (h : _root_.GlobalTheory.CharVal.MaxV P I γ)
    (h' : _root_.GlobalTheory.CharVal.MaxV P J δ) : _root_.GlobalTheory.CharVal.MaxV P (I * J) (γ * δ) := by
  obtain ⟨a, ha, hγ⟩ := h.2
  obtain ⟨b, hb, hδ⟩ := h'.2
  refine ⟨fun x hx => ?_, a * b, Submodule.mul_mem_mul ha hb, by rw [map_mul, hγ, hδ]⟩
  rw [Submodule.mul_eq_span_mul_set] at hx
  refine _root_.GlobalTheory.CharVal.val_le_of_span (fun z hz => ?_) x hx
  obtain ⟨u, hu, w, hw, rfl⟩ := Set.mem_mul.1 hz
  rw [map_mul]
  exact mul_le_mul' (h.1 u hu) (h'.1 w hw)

open NumberField IsDedekindDomain in
open scoped Pointwise in
variable {E : Type} [Field E] [NumberField E] in
variable {P : HeightOneSpectrum (𝓞 E)} {I J : Submodule (𝓞 E) E} {γ δ : WithZero (Multiplicative ℤ)} in
/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero, pow_zero]`. Conclude with `_root_.GlobalTheory.CharVal.maxV_one`. Consider the case `succ n ih => rw [pow_succ, pow_succ]`. Conclude with `ih.mul h`.
-/
theorem _root_.GlobalTheory.CharVal.MaxV.pow (h : _root_.GlobalTheory.CharVal.MaxV P I γ) (n : ℕ) :
    _root_.GlobalTheory.CharVal.MaxV P (I ^ n) (γ ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact _root_.GlobalTheory.CharVal.maxV_one
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

open NumberField IsDedekindDomain in
open scoped Pointwise in
variable {E : Type} [Field E] [NumberField E] in
variable {P : HeightOneSpectrum (𝓞 E)} {I J : Submodule (𝓞 E) E} {γ δ : WithZero (Multiplicative ℤ)} in
/- English proof (translation)
Introduce `a ha`. Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem x hx => exact h x hx`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_lt_one`.

Consider the case `add x y _ _ hx hy => exact (Valuation.map_add _ x y).trans_lt (max_lt hx hy)`. Consider the case `smul r x _ hx`. Rewrite using `[Algebra.smul_def, map_mul]`. Conclude with `(mul_le_of_le_one_left' (P.valuation_le_one r)).trans_lt hx`.
-/
private lemma valuation_lt_one_of_mem_span {S : Set E} (h : ∀ a ∈ S, P.valuation E a < 1) :
    ∀ a ∈ Submodule.span (𝓞 E) S, P.valuation E a < 1 := by
  intro a ha
  induction ha using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => rw [map_zero]; exact zero_lt_one
  | add x y _ _ hx hy => exact (Valuation.map_add _ x y).trans_lt (max_lt hx hy)
  | smul r x _ hx =>
    rw [Algebra.smul_def, map_mul]
    exact (mul_le_of_le_one_left' (P.valuation_le_one r)).trans_lt hx

open NumberField IsDedekindDomain in
open scoped Pointwise in
variable {E : Type} [Field E] [NumberField E] in
variable {P : HeightOneSpectrum (𝓞 E)} {I J : Submodule (𝓞 E) E} {γ δ : WithZero (Multiplicative ℤ)} in
/- English proof (translation)
Take `⟨a, ha, hγ⟩` from `h.2`. Establish `hle : ∀ b ∈ J, P.valuation E b ≤ γ⁻¹`. Introduce `b hb`. Establish `hab : a * b ∈ (1 : Submodule (𝓞 E) E)` using `hIJ ▸ Submodule.mul_mem_mul ha hb`. Take `⟨r, hr⟩` from `Submodule.mem_one.1 hab`.

Establish `h1 : γ * P.valuation E b ≤ 1`. Rewrite using `[← hγ, ← map_mul, ← hr]`. Conclude with `P.valuation_le_one r`. Rewrite using `[← mul_le_mul_iff_of_pos_left (zero_lt_iff.2 h0), mul_inv_cancel₀ h0]` and apply the resulting hypothesis. Use `⟨hle, ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `hlt : ∀ b ∈ J, P.valuation E b < γ⁻¹` using `fun b hb => lt_of_le_of_ne (hle b hb) (hne b hb)`. Establish `hS : ∀ z ∈ (I : Set E) * (J : Set E), P.valuation E z < 1`. Introduce `z hz`.

Take `⟨u, hu, w, hw, rfl⟩` from `Set.mem_mul.1 hz`. Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `h1 : (1 : E) ∈ I * J`. Rewrite using `[hIJ]`.

Conclude with `Submodule.mem_one.2 ⟨1, map_one _⟩`. Rewrite `h1` using `[Submodule.mul_eq_span_mul_set]`. Use `valuation_lt_one_of_mem_span hS 1 h1` as an intermediate fact. Rewrite `this` using `[map_one]`. Conclude with `lt_irrefl _ this`.
-/
theorem _root_.GlobalTheory.CharVal.MaxV.inv (h : _root_.GlobalTheory.CharVal.MaxV P I γ) (h0 : γ ≠ 0)
    (hIJ : I * J = 1) : _root_.GlobalTheory.CharVal.MaxV P J γ⁻¹ := by
  obtain ⟨a, ha, hγ⟩ := h.2
  have hle : ∀ b ∈ J, P.valuation E b ≤ γ⁻¹ := by
    intro b hb
    have hab : a * b ∈ (1 : Submodule (𝓞 E) E) := hIJ ▸ Submodule.mul_mem_mul ha hb
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 hab
    have h1 : γ * P.valuation E b ≤ 1 := by
      rw [← hγ, ← map_mul, ← hr]
      exact P.valuation_le_one r
    rwa [← mul_le_mul_iff_of_pos_left (zero_lt_iff.2 h0), mul_inv_cancel₀ h0]
  refine ⟨hle, ?_⟩
  by_contra hne
  push_neg at hne
  have hlt : ∀ b ∈ J, P.valuation E b < γ⁻¹ := fun b hb => lt_of_le_of_ne (hle b hb) (hne b hb)
  have hS : ∀ z ∈ (I : Set E) * (J : Set E), P.valuation E z < 1 := by
    intro z hz
    obtain ⟨u, hu, w, hw, rfl⟩ := Set.mem_mul.1 hz
    rw [map_mul]
    calc P.valuation E u * P.valuation E w ≤ γ * P.valuation E w :=
          mul_le_mul' (h.1 u hu) le_rfl
      _ < γ * γ⁻¹ := mul_lt_mul_of_pos_left (hlt w hw) (zero_lt_iff.2 h0)
      _ = 1 := mul_inv_cancel₀ h0
  have h1 : (1 : E) ∈ I * J := by
    rw [hIJ]
    exact Submodule.mem_one.2 ⟨1, map_one _⟩
  rw [Submodule.mul_eq_span_mul_set] at h1
  have := valuation_lt_one_of_mem_span hS 1 h1
  rw [map_one] at this
  exact lt_irrefl _ this

open NumberField IsDedekindDomain in
open scoped Pointwise in
variable {E : Type} [Field E] [NumberField E] in
variable {P : HeightOneSpectrum (𝓞 E)} {I J : Submodule (𝓞 E) E} {γ δ : WithZero (Multiplicative ℤ)} in
/- English proof (translation)
The claim follows from `le_antisymm (P.valuation_le_one s) (not_lt.1 fun h => hs ((P.valuation_lt_one_iff_mem s).1 h))`.
-/
private lemma valuation_algebraMap_eq_one_of_notMem' {s : 𝓞 E} (hs : s ∉ P.asIdeal) :
    P.valuation E (algebraMap (𝓞 E) E s) = 1 :=
  le_antisymm (P.valuation_le_one s) (not_lt.1 fun h => hs ((P.valuation_lt_one_iff_mem s).1 h))

open NumberField IsDedekindDomain in
open scoped Pointwise in
variable {E : Type} [Field E] [NumberField E] in
variable {P : HeightOneSpectrum (𝓞 E)} {I J : Submodule (𝓞 E) E} {γ δ : WithZero (Multiplicative ℤ)} in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, s, hs, hsr⟩`. Establish `h` using `congrArg (P.valuation E) hsr`. Rewrite `h` using `[map_mul, valuation_algebraMap_eq_one_of_notMem' hs, one_mul]`. Rewrite using `[h]`.

Conclude with `P.valuation_le_one r`. Introduce `hx`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (𝓞 E) x`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Establish `hb' : algebraMap (𝓞 E) E b ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb`.

Use `set k := (Associates.mk P.asIdeal).count (Associates.mk (Ideal.span {b})).factors with hk`. Establish `hbv` using `P.intValuation_if_neg hb0`. Rewrite `hbv` using `[← hk]`. Establish `hbk : b ∈ P.asIdeal ^ k` using `(P.intValuation_le_pow_iff_mem b k).1 hbv.le`. Establish `hbk1 : b ∉ P.asIdeal ^ (k + 1)`.

Rewrite using `[← P.intValuation_le_pow_iff_mem, hbv, WithZero.exp_le_exp]`. Use `push_cast`. Use linear arithmetic over natural numbers and integers. Establish `hak : a ∈ P.asIdeal ^ k`. Rewrite using `[← P.intValuation_le_pow_iff_mem, ← hbv, ← P.valuation_of_algebraMap (K := E), ← P.valuation_of_algebraMap (K := E)]`.

Rewrite `hx` using `[map_div₀]`. Conclude with `(div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hb'))).1 hx`. Take `⟨Q, hQ⟩` from `Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hbk)`. Establish `hQP : ¬ Q ≤ P.asIdeal`. Introduce `hle`.

Apply `hbk1` to reduce the goal to its premises. Rewrite using `[pow_succ, ← Ideal.span_singleton_le_iff_mem, hQ]`. Conclude with `Ideal.mul_mono_right hle`. Take `⟨s, hsQ, hsP⟩` from `Set.not_subset.1 hQP`. Establish `hsa : a * s ∈ Ideal.span {b}`.

Rewrite using `[hQ]`. Conclude with `Ideal.mul_mem_mul hak hsQ`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 hsa`. Use `⟨c, s, hsP, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_div_assoc', div_eq_iff hb', ← map_mul, ← map_mul, hc, mul_comm s a]`.
-/
theorem _root_.GlobalTheory.CharVal.intAt_iff (x : E) :
    _root_.Formalism.L2.Col.IntAt P x ↔ P.valuation E x ≤ 1 := by
  constructor
  · rintro ⟨r, s, hs, hsr⟩
    have h := congrArg (P.valuation E) hsr
    rw [map_mul, valuation_algebraMap_eq_one_of_notMem' hs, one_mul] at h
    rw [h]
    exact P.valuation_le_one r
  · intro hx
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (𝓞 E) x
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hb' : algebraMap (𝓞 E) E b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    set k := (Associates.mk P.asIdeal).count (Associates.mk (Ideal.span {b})).factors with hk
    have hbv := P.intValuation_if_neg hb0
    rw [← hk] at hbv
    have hbk : b ∈ P.asIdeal ^ k := (P.intValuation_le_pow_iff_mem b k).1 hbv.le
    have hbk1 : b ∉ P.asIdeal ^ (k + 1) := by
      rw [← P.intValuation_le_pow_iff_mem, hbv, WithZero.exp_le_exp]
      push_cast
      omega
    have hak : a ∈ P.asIdeal ^ k := by
      rw [← P.intValuation_le_pow_iff_mem, ← hbv, ← P.valuation_of_algebraMap (K := E),
        ← P.valuation_of_algebraMap (K := E)]
      rw [map_div₀] at hx
      exact (div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hb'))).1 hx
    obtain ⟨Q, hQ⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hbk)
    have hQP : ¬ Q ≤ P.asIdeal := by
      intro hle
      apply hbk1
      rw [pow_succ, ← Ideal.span_singleton_le_iff_mem, hQ]
      exact Ideal.mul_mono_right hle
    obtain ⟨s, hsQ, hsP⟩ := Set.not_subset.1 hQP
    have hsa : a * s ∈ Ideal.span {b} := by
      rw [hQ]
      exact Ideal.mul_mem_mul hak hsQ
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hsa
    refine ⟨c, s, hsP, ?_⟩
    rw [mul_div_assoc', div_eq_iff hb', ← map_mul, ← map_mul, hc, mul_comm s a]

open NumberField IsDedekindDomain in
open scoped Pointwise in
variable {E : Type} [Field E] [NumberField E] in
variable {P : HeightOneSpectrum (𝓞 E)} {I J : Submodule (𝓞 E) E} {γ δ : WithZero (Multiplicative ℤ)} in
/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem _root_.GlobalTheory.CharVal.mem_locP' (I : Submodule (𝓞 E) E) (x : E) :
    x ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal I ↔ ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ I :=
  Iff.rfl

open NumberField IsDedekindDomain in
open scoped Pointwise in
variable {E : Type} [Field E] [NumberField E] in
variable {P : HeightOneSpectrum (𝓞 E)} {I J : Submodule (𝓞 E) E} {γ δ : WithZero (Multiplicative ℤ)} in

/- English proof (translation)
Rewrite using `[_root_.GlobalTheory.CharVal.mem_locP']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, hsx⟩`. Use `h.1 _ hsx` as an intermediate fact. Rewrite `this` using `[Algebra.smul_def, map_mul, valuation_algebraMap_eq_one_of_notMem' hs, one_mul]`. Then use the resulting hypothesis.

Introduce `hx`. Take `⟨a, ha, hγ⟩` from `h.2`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Conclude with `h0 (by rw [← hγ, map_zero])`.

Establish `hint : _root_.Formalism.L2.Col.IntAt P (x / a)`. Rewrite using `[_root_.GlobalTheory.CharVal.intAt_iff, map_div₀, hγ]`. Conclude with `(div_le_one₀ (zero_lt_iff.2 h0)).2 hx`. Take `⟨r, s, hs, hsr⟩` from `hint`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations.

Establish `hsx : s • x = r • a`. Rewrite using `[Algebra.smul_def, Algebra.smul_def, ← hsr, mul_assoc, div_mul_cancel₀ x ha0]`. Rewrite using `[hsx]`. Conclude with `I.smul_mem r ha`.
-/
theorem _root_.GlobalTheory.CharVal.MaxV.mem_locP (h : _root_.GlobalTheory.CharVal.MaxV P I γ) (h0 : γ ≠ 0) (x : E) :
    x ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal I ↔ P.valuation E x ≤ γ := by
  rw [_root_.GlobalTheory.CharVal.mem_locP']
  constructor
  · rintro ⟨s, hs, hsx⟩
    have := h.1 _ hsx
    rwa [Algebra.smul_def, map_mul, valuation_algebraMap_eq_one_of_notMem' hs, one_mul] at this
  · intro hx
    obtain ⟨a, ha, hγ⟩ := h.2
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact h0 (by rw [← hγ, map_zero])
    have hint : _root_.Formalism.L2.Col.IntAt P (x / a) := by
      rw [_root_.GlobalTheory.CharVal.intAt_iff, map_div₀, hγ]
      exact (div_le_one₀ (zero_lt_iff.2 h0)).2 hx
    obtain ⟨r, s, hs, hsr⟩ := hint
    refine ⟨s, hs, ?_⟩
    have hsx : s • x = r • a := by
      rw [Algebra.smul_def, Algebra.smul_def, ← hsr, mul_assoc, div_mul_cancel₀ x ha0]
    rw [hsx]
    exact I.smul_mem r ha

open NumberField IsDedekindDomain in
open scoped Pointwise in
variable {E : Type} [Field E] [NumberField E] in
variable {P : HeightOneSpectrum (𝓞 E)} {I J : Submodule (𝓞 E) E} {γ δ : WithZero (Multiplicative ℤ)} in
/- English proof (translation)
Establish `h1P : (1 : 𝓞 E) ∉ P.asIdeal` using `P.asIdeal.ne_top_iff_one.1 P.isPrime.ne_top`. Prove the components needed by the constructor for the conclusion. Introduce `a ha`. Establish `hmem : a ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 E) E)`. Rewrite using `[← h]`.

Conclude with `(_root_.GlobalTheory.CharVal.mem_locP' I a).2 ⟨1, h1P, by rwa [one_smul]⟩`. Take `⟨s, hs, hsa⟩` from `(_root_.GlobalTheory.CharVal.mem_locP' _ a).1 hmem`. Take `⟨r, hr⟩` from `Submodule.mem_one.1 hsa`. Establish `hv` using `congrArg (P.valuation E) hr`. Rewrite `hv` using `[Algebra.smul_def, map_mul, valuation_algebraMap_eq_one_of_notMem' hs, one_mul]`.

Rewrite using `[← hv]`. Conclude with `P.valuation_le_one r`. Establish `hmem : (1 : E) ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal I`. Rewrite using `[h]`. Conclude with `(_root_.GlobalTheory.CharVal.mem_locP' _ 1).2 ⟨1, h1P, by rw [one_smul]; exact Submodule.mem_one.2 ⟨1, map_one _⟩⟩`.

Take `⟨s, hs, hs1⟩` from `(_root_.GlobalTheory.CharVal.mem_locP' I 1).1 hmem`. Use `⟨s • 1, hs1, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, mul_one, valuation_algebraMap_eq_one_of_notMem' hs]`.
-/
theorem _root_.GlobalTheory.CharVal.maxV_of_localization_eq
    (h : _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal I = _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 E) E)) :
    _root_.GlobalTheory.CharVal.MaxV P I 1 := by
  have h1P : (1 : 𝓞 E) ∉ P.asIdeal := P.asIdeal.ne_top_iff_one.1 P.isPrime.ne_top
  constructor
  · intro a ha
    have hmem : a ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 E) E) := by
      rw [← h]
      exact (_root_.GlobalTheory.CharVal.mem_locP' I a).2 ⟨1, h1P, by rwa [one_smul]⟩
    obtain ⟨s, hs, hsa⟩ := (_root_.GlobalTheory.CharVal.mem_locP' _ a).1 hmem
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 hsa
    have hv := congrArg (P.valuation E) hr
    rw [Algebra.smul_def, map_mul, valuation_algebraMap_eq_one_of_notMem' hs, one_mul] at hv
    rw [← hv]
    exact P.valuation_le_one r
  · have hmem : (1 : E) ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal I := by
      rw [h]
      exact (_root_.GlobalTheory.CharVal.mem_locP' _ 1).2
        ⟨1, h1P, by rw [one_smul]; exact Submodule.mem_one.2 ⟨1, map_one _⟩⟩
    obtain ⟨s, hs, hs1⟩ := (_root_.GlobalTheory.CharVal.mem_locP' I 1).1 hmem
    refine ⟨s • 1, hs1, ?_⟩
    rw [Algebra.smul_def, mul_one, valuation_algebraMap_eq_one_of_notMem' hs]

end GlobalTheory.CharVal
