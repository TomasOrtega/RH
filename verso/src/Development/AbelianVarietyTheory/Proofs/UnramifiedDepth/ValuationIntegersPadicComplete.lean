import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Formalism.LocalToGlobal.CharacterGerms.RowTieTop
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyPadicIntRingHomOfIsAdicComplete

open scoped BigOperators TensorProduct
open NumberField IsLocalRing Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs

namespace GlobalTheory.ValExp

noncomputable def halfPow (t : WithTop ℝ) : NNReal :=
  WithTop.recTopCoe (0 : NNReal) (fun r : ℝ => (2⁻¹ : NNReal) ^ r) t

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem halfPow_top : halfPow ⊤ = 0 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem halfPow_coe (r : ℝ) : halfPow (r : WithTop ℝ) = (2⁻¹ : NNReal) ^ r := rfl

/- English proof (translation)
Rewrite using `[← WithTop.coe_zero, halfPow_coe, NNReal.rpow_zero]`.
-/
theorem halfPow_zero : halfPow 0 = 1 := by
  rw [← WithTop.coe_zero, halfPow_coe, NNReal.rpow_zero]

/- English proof (translation)
Rewrite using `[← WithTop.coe_one, halfPow_coe, NNReal.rpow_one]`.
-/
theorem halfPow_one : halfPow 1 = 2⁻¹ := by
  rw [← WithTop.coe_one, halfPow_coe, NNReal.rpow_one]

/- English proof (translation)
Proceed by induction on `a using WithTop.recTopCoe with`. Consider the case `top => simp [halfPow_top]`. Consider the case `coe a`. Proceed by induction on `b using WithTop.recTopCoe with`. Consider the case `top => simp [halfPow_top]`.

Consider the case `coe b => rw [← WithTop.coe_add, halfPow_coe, halfPow_coe, halfPow_coe, NNReal.rpow_add (by norm_num)]`.
-/
theorem halfPow_add (a b : WithTop ℝ) : halfPow (a + b) = halfPow a * halfPow b := by
  induction a using WithTop.recTopCoe with
  | top => simp [halfPow_top]
  | coe a =>
    induction b using WithTop.recTopCoe with
    | top => simp [halfPow_top]
    | coe b => rw [← WithTop.coe_add, halfPow_coe, halfPow_coe, halfPow_coe, NNReal.rpow_add (by norm_num)]

/- English proof (translation)
Introduce `a b hab`. Proceed by induction on `a using WithTop.recTopCoe with`. Consider the case `top => exact absurd hab not_top_lt`. Consider the case `coe a`. Proceed by induction on `b using WithTop.recTopCoe with`.

Consider the case `top => rw [halfPow_top, halfPow_coe]; exact NNReal.rpow_pos (by norm_num)`. Consider the case `coe b`. Rewrite using `[halfPow_coe, halfPow_coe]`. Conclude with `NNReal.rpow_lt_rpow_of_exponent_gt (by norm_num) (by norm_num) (by exact_mod_cast hab)`.
-/
theorem halfPow_strictAnti : StrictAnti halfPow := by
  intro a b hab
  induction a using WithTop.recTopCoe with
  | top => exact absurd hab not_top_lt
  | coe a =>
    induction b using WithTop.recTopCoe with
    | top => rw [halfPow_top, halfPow_coe]; exact NNReal.rpow_pos (by norm_num)
    | coe b =>
      rw [halfPow_coe, halfPow_coe]
      exact NNReal.rpow_lt_rpow_of_exponent_gt (by norm_num) (by norm_num) (by exact_mod_cast hab)

variable {C : Type} [Field C]

noncomputable def mulVal (V : VF C) : Valuation C NNReal where
  toFun x := halfPow (V.v x)
  map_zero' := by rw [V.v.map_zero, halfPow_top]
  map_one' := by rw [V.v.map_one, halfPow_zero]
  map_mul' x y := by rw [V.v.map_mul, halfPow_add]
  map_add_le_max' x y := by
    refine (halfPow_strictAnti.antitone (V.v.map_add x y)).trans ?_
    rcases le_total (V.v x) (V.v y) with h | h
    · rw [min_eq_left h]; exact le_max_left _ _
    · rw [min_eq_right h]; exact le_max_right _ _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mulVal_apply (V : VF C) (x : C) : mulVal V x = halfPow (V.v x) := rfl

/- English proof (translation)
Rewrite using `[mulVal_apply, V.v_l, halfPow_one]`.
-/
theorem mulVal_l (V : VF C) : mulVal V (V.l : C) = 2⁻¹ := by
  rw [mulVal_apply, V.v_l, halfPow_one]

/- English proof (translation)
Rewrite using `[mulVal_apply, ← halfPow_zero, halfPow_strictAnti.le_iff_ge]`. Both sides reduce to the same expression.
-/
theorem mulVal_le_one_iff (V : VF C) (x : C) : mulVal V x ≤ 1 ↔ V.Ge 0 x := by
  rw [mulVal_apply, ← halfPow_zero, halfPow_strictAnti.le_iff_ge]; rfl

/- English proof (translation)
Rewrite using `[mulVal_apply, ← halfPow_zero, halfPow_strictAnti.lt_iff_gt]`. Both sides reduce to the same expression.
-/
theorem mulVal_lt_one_iff (V : VF C) (x : C) : mulVal V x < 1 ↔ V.MM x := by
  rw [mulVal_apply, ← halfPow_zero, halfPow_strictAnti.lt_iff_gt]; rfl

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using VF.Ge.one`. Consider the case `succ n ih => rw [pow_succ]`. Use `push_cast`. Conclude with `ih.mul VF.ge_l`.
-/
theorem ge_l_pow (V : VF C) (n : ℕ) : V.Ge n ((V.l : C) ^ n) := by
  induction n with
  | zero => simpa using VF.Ge.one
  | succ n ih => rw [pow_succ]; push_cast; exact ih.mul VF.ge_l

/- English proof (translation)
Proceed by induction on `n generalizing w with`. Consider the case `zero => simpa using h`. Consider the case `succ n ih`. Rewrite `h` using `[pow_succ', mul_assoc]`. Use `(ih h.of_l_mul).mono (le_of_eq ?_)` and prove the remaining obligations.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ge_of_l_pow_mul (V : VF C) (n : ℕ) {w : ℝ} {a : C} (h : V.Ge w ((V.l : C) ^ n * a)) :
    V.Ge (w - n) a := by
  induction n generalizing w with
  | zero => simpa using h
  | succ n ih =>
    rw [pow_succ', mul_assoc] at h
    refine (ih h.of_l_mul).mono (le_of_eq ?_)
    push_cast; ring

/- English proof (translation)
Rewrite using `[smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Establish `hy : V.Ge 0 (y : C)` using `(mulVal_le_one_iff V _).1 y.2`. Simplify using `using (ge_l_pow V n).mul hy`.

Introduce `h`. Establish `hl : (V.l : C) ^ n ≠ 0` using `pow_ne_zero _ VF.l_ne_zero`. Establish `hy : V.Ge 0 (((V.l : C) ^ n)⁻¹ * x)`. Use `ge_of_l_pow_mul V n (w := n) (a := ((V.l : C) ^ n)⁻¹ * x) (by rwa [mul_inv_cancel_left₀ hl])` as an intermediate fact. Simplify using `using this`.

Use `⟨⟨_, (mulVal_le_one_iff V _).2 hy⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Simplify using `[mul_inv_cancel_left₀ hl]`.
-/
theorem mem_pow_iff (V : VF C) (n : ℕ) (x : (mulVal V).integer) :
    x ∈ (Ideal.span {((V.l : ℕ) : (mulVal V).integer)} ^ n • ⊤ :
      Submodule (mulVal V).integer (mulVal V).integer) ↔ V.Ge n (x : C) := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, rfl⟩
    have hy : V.Ge 0 (y : C) := (mulVal_le_one_iff V _).1 y.2
    simpa using (ge_l_pow V n).mul hy
  · intro h
    have hl : (V.l : C) ^ n ≠ 0 := pow_ne_zero _ VF.l_ne_zero
    have hy : V.Ge 0 (((V.l : C) ^ n)⁻¹ * x) := by
      have := ge_of_l_pow_mul V n (w := n) (a := ((V.l : C) ^ n)⁻¹ * x)
        (by rwa [mul_inv_cancel_left₀ hl])
      simpa using this
    refine ⟨⟨_, (mulVal_le_one_iff V _).2 hy⟩, Subtype.ext ?_⟩
    simp [mul_inv_cancel_left₀ hl]

/- English proof (translation)
Assume the negation of the conclusion as `h0`. Establish `h1 : (x : C) ≠ 0` using `fun h => h0 (Subtype.ext h)`. Take `⟨t, ht⟩` from `WithTop.ne_top_iff_exists.1 ((AddValuation.ne_top_iff V.v).2 h1)`. Take `⟨n, hn⟩` from `exists_nat_gt t`. Use `(mem_pow_iff V n x).1 (SModEq.zero.1 (hx n))` as an intermediate fact.

Rewrite `this` using `[VF.Ge, ← ht]`. Conclude with `hn.not_ge (by exact_mod_cast this)`. Use the proof step `prec' f hf := by`. Take `⟨x, hx⟩` from `hc (fun n => (f n : C)) fun n => by`. Use `(mem_pow_iff V n _).1 (SModEq.sub_mem.1 (hf (Nat.le_succ n)).symm)` as an intermediate fact.

Simplify using `using this`. Establish `h0 : V.Ge 0 x`. Establish `h1 : V.Ge 0 (x - f 0)` using `by simpa using hx 0`. Simplify using `using h1.add ((mulVal_le_one_iff V _).1 (f 0).2)`. Use `⟨⟨x, (mulVal_le_one_iff V _).2 h0⟩, fun n => SModEq.symm (SModEq.sub_mem.2 ?_)⟩` and prove the remaining obligations.

Rewrite using `[mem_pow_iff]`. Simplify using `using hx n`.
-/
theorem isAdicComplete (V : VF C)
    (hc : ∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) :
    IsAdicComplete (Ideal.span {((V.l : ℕ) : (mulVal V).integer)}) (mulVal V).integer where
  haus' x hx := by
    by_contra h0
    have h1 : (x : C) ≠ 0 := fun h => h0 (Subtype.ext h)
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 ((AddValuation.ne_top_iff V.v).2 h1)
    obtain ⟨n, hn⟩ := exists_nat_gt t
    have := (mem_pow_iff V n x).1 (SModEq.zero.1 (hx n))
    rw [VF.Ge, ← ht] at this
    exact hn.not_ge (by exact_mod_cast this)
  prec' f hf := by
    obtain ⟨x, hx⟩ := hc (fun n => (f n : C)) fun n => by
      have := (mem_pow_iff V n _).1 (SModEq.sub_mem.1 (hf (Nat.le_succ n)).symm)
      simpa using this
    have h0 : V.Ge 0 x := by
      have h1 : V.Ge 0 (x - f 0) := by simpa using hx 0
      simpa using h1.add ((mulVal_le_one_iff V _).1 (f 0).2)
    refine ⟨⟨x, (mulVal_le_one_iff V _).2 h0⟩, fun n => SModEq.symm (SModEq.sub_mem.2 ?_)⟩
    rw [mem_pow_iff]
    simpa using hx n

/- English proof (translation)
Introduce `C _ V _ hc`. Use `haveI := isAdicComplete V hc`. Use `⟨mulVal V, fun x hx => ?_, ?_, ?_, mulVal_le_one_iff V, mulVal_lt_one_iff V, this, ?_⟩` and prove the remaining obligations. Take `⟨t, ht⟩` from `WithTop.ne_top_iff_exists.1 ((AddValuation.ne_top_iff V.v).2 hx)`. Use `⟨t, ht.symm, ?_⟩` and prove the remaining obligations.

Rewrite using `[mulVal_l, mulVal_apply, ← ht, halfPow_coe, NNReal.coe_rpow]`. Rewrite using `[mulVal_l]`. Evaluate the numerical expressions. Rewrite using `[mulVal_l]`. Evaluate the numerical expressions.

Take `⟨φ⟩` from `nonempty_padicInt_ringHom_of_isAdicComplete (Ideal.span {((V.l : ℕ) : (mulVal V).integer)}) V.l (Ideal.mem_span_singleton_self _)`. Conclude with `⟨φ.toAlgebra⟩`.
-/
theorem exists_mulVal : ∀ (C : Type) [Field C] (V : VF C) [Fact V.l.Prime], (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) → ∃ vm : Valuation C NNReal, ValuationFitting.ValTie V vm ∧ 0 < (vm (V.l : C) : ℝ) ∧ (vm (V.l : C) : ℝ) < 1 ∧ (∀ x : C, vm x ≤ 1 ↔ V.Ge 0 x) ∧ (∀ x : C, vm x < 1 ↔ V.MM x) ∧ IsAdicComplete (Ideal.span {((V.l : ℕ) : vm.integer)}) vm.integer ∧ Nonempty (Algebra ℤ_[V.l] vm.integer) := by
  intro C _ V _ hc
  haveI := isAdicComplete V hc
  refine ⟨mulVal V, fun x hx => ?_, ?_, ?_, mulVal_le_one_iff V, mulVal_lt_one_iff V, this, ?_⟩
  · obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 ((AddValuation.ne_top_iff V.v).2 hx)
    refine ⟨t, ht.symm, ?_⟩
    rw [mulVal_l, mulVal_apply, ← ht, halfPow_coe, NNReal.coe_rpow]
  · rw [mulVal_l]; norm_num
  · rw [mulVal_l]; norm_num
  · obtain ⟨φ⟩ := nonempty_padicInt_ringHom_of_isAdicComplete
      (Ideal.span {((V.l : ℕ) : (mulVal V).integer)}) V.l (Ideal.mem_span_singleton_self _)
    exact ⟨φ.toAlgebra⟩

end GlobalTheory.ValExp
