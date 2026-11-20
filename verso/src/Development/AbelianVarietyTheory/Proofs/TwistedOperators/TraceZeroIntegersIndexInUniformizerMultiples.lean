import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceZeroIntegersModUniformizerCardOfCardSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardIntegersModUniformizerEqQSq

noncomputable section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

/- English proof (translation)
Introduce `L _ _ ϖ σ q f hU`. Establish `hq` using `traceZeroIndex_of_intIndex intIndex L ϖ σ q hU`. Take `⟨-, -, hϖ, h4, -, -, -⟩` from `hU`. Establish `h0 : ϖ ≠ 0`. Introduce `h0`.

Rewrite `h4` using `[h0, map_zero]`. Conclude with `WithZero.zero_ne_coe h4`. Establish `hϖO : ϖ ∈ intL L` using `by show Valued.v ϖ ≤ 1`. Rewrite using `[h4, ← WithZero.coe_one, WithZero.coe_le_coe]`. Use `show (-1 : ℤ) ≤ 0`.

Use linear arithmetic over natural numbers and integers. Use `set T := (intL L).toAddSubgroup ⊓ (σ.toAddMonoidHom + AddMonoidHom.id L).ker with hT`. Establish `memT : ∀ y, y ∈ T ↔ y ∈ intL L ∧ σ y + y = 0` using `fun y => Iff.rfl`. Establish `hinj : ∀ e : ℕ, Function.Injective (AddMonoidHom.mulLeft (ϖ ^ e))` using `fun e => mul_right_injective₀ (pow_ne_zero e h0)`. Establish `hmap : ∀ e : ℕ, (traceZero σ (ϖ ^ e)).map (AddMonoidHom.mulLeft (ϖ ^ e)) = T` using `fun e => by`.

Use extensionality with `x`. Rewrite using `[AddSubgroup.mem_map, memT]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Rewrite `hy` using `[mem_traceZero]`.

Use `⟨hy.1, ?_⟩` and prove the remaining obligations. Rewrite using `[AddMonoidHom.coe_mulLeft, map_mul, map_pow, hϖ]`. Take the linear combination `ϖ ^ e * hy.2`. Introduce and unpack `⟨hx, hx0⟩`. Use `⟨(ϖ ^ e)⁻¹ * x, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[mem_traceZero, mul_inv_cancel_left₀ (pow_ne_zero e h0)]`. Use `⟨hx, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_inv₀, map_pow, hϖ]`. Take the linear combination `(ϖ ^ e)⁻¹ * hx0`. Rewrite using `[AddMonoidHom.coe_mulLeft, mul_inv_cancel_left₀ (pow_ne_zero e h0)]`.

Establish `h1 : traceZero σ 1 = T`. Use extensionality with `x`. Rewrite using `[mem_traceZero, memT, one_mul]`. Establish `hmulle : ∀ e : ℕ, T.map (AddMonoidHom.mulLeft (ϖ ^ e)) ≤ T`. Introduce and unpack `e _ ⟨y, hy, rfl⟩`.

Establish `hy : y ∈ T` using `hy`. Rewrite `hy`, the goal using `[memT]`. Use `⟨(intL L).mul_mem (pow_mem hϖO e) hy.1, ?_⟩` and prove the remaining obligations. Rewrite using `[AddMonoidHom.coe_mulLeft, map_mul, map_pow, hϖ]`. Take the linear combination `ϖ ^ e * hy.2`.

Rewrite using `[← AddSubgroup.relIndex_map_map_of_injective (traceZero σ 1) (traceZero σ (ϖ ^ f)) (hinj f), hmap f, h1]`. Proceed by induction on `f with`. Consider the case `zero`. Establish `: T.map (AddMonoidHom.mulLeft (ϖ ^ 0)) = T`. Use extensionality with `x`.

Simplify using `[AddSubgroup.mem_map]`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Consider the case `succ e ih`. Establish `hcomp : T.map (AddMonoidHom.mulLeft (ϖ ^ (e + 1))) = (T.map (AddMonoidHom.mulLeft ϖ)).map (AddMonoidHom.mulLeft (ϖ ^ e))`.

Use extensionality with `x`. Simplify using `only [AddSubgroup.mem_map, AddMonoidHom.coe_mulLeft]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨o, ho, rfl⟩`. Conclude with `⟨ϖ * o, ⟨o, ho, rfl⟩, by rw [pow_succ, mul_assoc]⟩`.

Introduce and unpack `⟨_, ⟨o, ho, rfl⟩, rfl⟩`. Conclude with `⟨o, ho, by rw [pow_succ, mul_assoc]⟩`. Establish `hstep : (T.map (AddMonoidHom.mulLeft (ϖ ^ (e + 1)))).relIndex (T.map (AddMonoidHom.mulLeft (ϖ ^ e))) = q`. Rewrite using `[hcomp, AddSubgroup.relIndex_map_map_of_injective _ _ (hinj e)]`. Conclude with `hq`.

Establish `hle1 : T.map (AddMonoidHom.mulLeft (ϖ ^ (e + 1))) ≤ T.map (AddMonoidHom.mulLeft (ϖ ^ e))`. Rewrite using `[hcomp]`. Conclude with `AddSubgroup.map_mono (by simpa using hmulle 1)`. Rewrite using `[← AddSubgroup.relIndex_mul_relIndex _ _ _ hle1 (hmulle e), hstep, ih]`. Conclude with `(pow_succ' _ _).symm`.
-/
theorem traceIndex : TraceIndex := by
  intro L _ _ ϖ σ q f hU
  have hq := traceZeroIndex_of_intIndex intIndex L ϖ σ q hU
  obtain ⟨-, -, hϖ, h4, -, -, -⟩ := hU
  have h0 : ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h4
    exact WithZero.zero_ne_coe h4
  have hϖO : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [h4, ← WithZero.coe_one, WithZero.coe_le_coe]
    show (-1 : ℤ) ≤ 0
    omega
  set T := (intL L).toAddSubgroup ⊓ (σ.toAddMonoidHom + AddMonoidHom.id L).ker with hT
  have memT : ∀ y, y ∈ T ↔ y ∈ intL L ∧ σ y + y = 0 := fun y => Iff.rfl
  have hinj : ∀ e : ℕ, Function.Injective (AddMonoidHom.mulLeft (ϖ ^ e)) := fun e =>
    mul_right_injective₀ (pow_ne_zero e h0)
  have hmap : ∀ e : ℕ, (traceZero σ (ϖ ^ e)).map (AddMonoidHom.mulLeft (ϖ ^ e)) = T := fun e => by
    ext x
    rw [AddSubgroup.mem_map, memT]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [mem_traceZero] at hy
      refine ⟨hy.1, ?_⟩
      rw [AddMonoidHom.coe_mulLeft, map_mul, map_pow, hϖ]
      linear_combination ϖ ^ e * hy.2
    · rintro ⟨hx, hx0⟩
      refine ⟨(ϖ ^ e)⁻¹ * x, ?_, ?_⟩
      · rw [mem_traceZero, mul_inv_cancel_left₀ (pow_ne_zero e h0)]
        refine ⟨hx, ?_⟩
        rw [map_mul, map_inv₀, map_pow, hϖ]
        linear_combination (ϖ ^ e)⁻¹ * hx0
      · rw [AddMonoidHom.coe_mulLeft, mul_inv_cancel_left₀ (pow_ne_zero e h0)]
  have h1 : traceZero σ 1 = T := by
    ext x
    rw [mem_traceZero, memT, one_mul]
  have hmulle : ∀ e : ℕ, T.map (AddMonoidHom.mulLeft (ϖ ^ e)) ≤ T := by
    rintro e _ ⟨y, hy, rfl⟩
    have hy : y ∈ T := hy
    rw [memT] at hy ⊢
    refine ⟨(intL L).mul_mem (pow_mem hϖO e) hy.1, ?_⟩
    rw [AddMonoidHom.coe_mulLeft, map_mul, map_pow, hϖ]
    linear_combination ϖ ^ e * hy.2
  rw [← AddSubgroup.relIndex_map_map_of_injective (traceZero σ 1) (traceZero σ (ϖ ^ f)) (hinj f), hmap f, h1]
  induction f with
  | zero =>
    have : T.map (AddMonoidHom.mulLeft (ϖ ^ 0)) = T := by
      ext x
      simp [AddSubgroup.mem_map]
    rw [this]
    simp
  | succ e ih =>
    have hcomp : T.map (AddMonoidHom.mulLeft (ϖ ^ (e + 1))) =
        (T.map (AddMonoidHom.mulLeft ϖ)).map (AddMonoidHom.mulLeft (ϖ ^ e)) := by
      ext x
      simp only [AddSubgroup.mem_map, AddMonoidHom.coe_mulLeft]
      constructor
      · rintro ⟨o, ho, rfl⟩
        exact ⟨ϖ * o, ⟨o, ho, rfl⟩, by rw [pow_succ, mul_assoc]⟩
      · rintro ⟨_, ⟨o, ho, rfl⟩, rfl⟩
        exact ⟨o, ho, by rw [pow_succ, mul_assoc]⟩
    have hstep : (T.map (AddMonoidHom.mulLeft (ϖ ^ (e + 1)))).relIndex
        (T.map (AddMonoidHom.mulLeft (ϖ ^ e))) = q := by
      rw [hcomp, AddSubgroup.relIndex_map_map_of_injective _ _ (hinj e)]
      exact hq
    have hle1 : T.map (AddMonoidHom.mulLeft (ϖ ^ (e + 1))) ≤ T.map (AddMonoidHom.mulLeft (ϖ ^ e)) := by
      rw [hcomp]
      exact AddSubgroup.map_mono (by simpa using hmulle 1)
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ hle1 (hmulle e), hstep, ih]
    exact (pow_succ' _ _).symm

end GlobalTheory.InertZeta

end
