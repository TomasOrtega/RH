import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MinpolyIrreducibleNatDegreeOfRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory

/- English proof (translation)
Introduce `V E _ _ _ _ _ Φ hΦ S Y hY R hR`. Use `set M : Submodule ℤ V := Submodule.span ℤ (S : Set V) with hMdef`. Establish `hMY : Y ⊆ (M : Set V)`. Introduce `y hy`. Use `hY hy` as an intermediate fact.

Rewrite `this` using `[← Submodule.span_int_eq_addSubgroupClosure]`. Conclude with `this`. Use `haveI : Module.Finite ℤ M := Module.Finite.span_of_finite ℤ S.finite_toSet`. Use `haveI : Module.IsTorsionFree ℤ V := .trans_faithfulSMul ℤ ℚ V`. Use `haveI : Module.Free ℤ M := Module.free_of_finite_type_torsion_free'`.

Set `b` to `Module.finBasis ℤ M`. Use `set n := Module.finrank ℤ M`. Set `e : Fin n → V` to `fun j => (b j : V)`. Establish `heZ : LinearIndependent ℤ e` using `b.linearIndependent.map' M.subtype (Submodule.ker_subtype M)`. Establish `heQ : LinearIndependent ℚ e` using `(LinearIndependent.iff_fractionRing ℤ ℚ).1 heZ`.

Establish `heR` using `hΦ n e heQ`. Set `T : (Fin n → ℝ) →ₗ[ℝ] E` to `Fintype.linearCombination ℝ (fun j => Φ (e j))`. Establish `hT : LinearMap.ker T = ⊥` using `LinearMap.ker_eq_bot.2 (linearIndependent_iff_injective_fintypeLinearCombination.1 heR)`. Take `⟨K, -, hK⟩` from `T.exists_antilipschitzWith hT`. Set `f : V → (Fin n → ℤ)` to `fun y => if h : y ∈ M then fun j => b.repr ⟨y, h⟩ j else 0`.

Establish `hfy : ∀ y (h : y ∈ M), f y = fun j => b.repr ⟨y, h⟩ j` using `fun y h => by simp [f, h]`. Establish `hinj : Set.InjOn f Y`. Introduce `y hy z hz hyz`. Establish `h1` using `hMY hy`. Establish `h2` using `hMY hz`.

Rewrite `hyz` using `[hfy y h1, hfy z h2]`. Establish `: b.repr ⟨y, h1⟩ = b.repr ⟨z, h2⟩`. Use extensionality with `j`. Conclude with `congrFun hyz j`. Use `b.repr.injective this` as an intermediate fact.

Simplify using `using congrArg Subtype.val this`. Establish `hΦy : ∀ y (h : y ∈ M), Φ y = T (fun j => ((b.repr ⟨y, h⟩ j : ℤ) : ℝ))`. Introduce `y h`. Establish `hs' : y = ∑ j, b.repr ⟨y, h⟩ j • e j`. Use `congrArg (Subtype.val : M → V) (b.sum_repr ⟨y, h⟩)` as an intermediate fact.

Rewrite `this` using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul] at this`. Conclude with `this.symm`. Use `conv_lhs => rw [hs']`. Simplify using `[T, Fintype.linearCombination_apply, map_sum, map_zsmul, Int.cast_smul_eq_zsmul]`.

Use `set N : ℤ := ⌈(K : ℝ) * R⌉`. Establish `hsub : f '' Y ⊆ Set.Icc (fun _ => -N) (fun _ => N)`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Establish `h` using `hMY hy`. Rewrite using `[hfy y h]`.

Use `set c : Fin n → ℝ := fun j => ((b.repr ⟨y, h⟩ j : ℤ) : ℝ)`. Establish `hc : ‖c‖ ≤ (K : ℝ) * R`. Establish `h1` using `ZeroHomClass.bound_of_antilipschitz T hK c`. Rewrite `h1` using `[← hΦy y h]`. Conclude with `h1.trans (mul_le_mul_of_nonneg_left (hR y hy) K.2)`.

Establish `hcj : ∀ j, |c j| ≤ (K : ℝ) * R` using `fun j => by`. Establish `h0 : ‖c j‖ ≤ ‖c‖` using `norm_le_pi_norm c j`. Rewrite `h0` using `[Real.norm_eq_abs]`. Conclude with `h0.trans hc`. Apply the tactic sequence `constructor <;> intro j`.

Establish `h3 : -((K : ℝ) * R) ≤ c j` using `(abs_le.1 (hcj j)).1`. Establish `h4 : (-(N : ℝ)) ≤ c j` using `le_trans (neg_le_neg (Int.le_ceil _)) h3`. Establish `h5 : ((-N : ℤ) : ℝ) ≤ ((b.repr ⟨y, h⟩ j : ℤ) : ℝ)` using `by push_cast; exact h4`. Conclude with `Int.cast_le.1 h5`. Establish `h4 : c j ≤ (N : ℝ)` using `((abs_le.1 (hcj j)).2).trans (Int.le_ceil _)`.

Conclude with `Int.cast_le.1 h4`. Conclude with `Set.Finite.of_finite_image ((Set.finite_Icc _ _).subset hsub) hinj`.
-/
theorem finite_of_bounded_image_closure_finset :
    ∀ {V E : Type} [AddCommGroup V] [Module ℚ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] (Φ : V →+ E),
      (∀ (k : ℕ) (e : Fin k → V), LinearIndependent ℚ e → LinearIndependent ℝ (fun j => Φ (e j))) →
      ∀ (S : Finset V) (Y : Set V), Y ⊆ (AddSubgroup.closure (S : Set V) : Set V) →
        ∀ R : ℝ, (∀ y ∈ Y, ‖Φ y‖ ≤ R) → Y.Finite := by
  intro V E _ _ _ _ _ Φ hΦ S Y hY R hR
  set M : Submodule ℤ V := Submodule.span ℤ (S : Set V) with hMdef
  have hMY : Y ⊆ (M : Set V) := by
    intro y hy
    have := hY hy
    rw [← Submodule.span_int_eq_addSubgroupClosure] at this
    exact this
  haveI : Module.Finite ℤ M := Module.Finite.span_of_finite ℤ S.finite_toSet
  haveI : Module.IsTorsionFree ℤ V := .trans_faithfulSMul ℤ ℚ V
  haveI : Module.Free ℤ M := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ M
  set n := Module.finrank ℤ M
  let e : Fin n → V := fun j => (b j : V)
  have heZ : LinearIndependent ℤ e := b.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have heQ : LinearIndependent ℚ e := (LinearIndependent.iff_fractionRing ℤ ℚ).1 heZ
  have heR := hΦ n e heQ
  let T : (Fin n → ℝ) →ₗ[ℝ] E := Fintype.linearCombination ℝ (fun j => Φ (e j))
  have hT : LinearMap.ker T = ⊥ :=
    LinearMap.ker_eq_bot.2 (linearIndependent_iff_injective_fintypeLinearCombination.1 heR)
  obtain ⟨K, -, hK⟩ := T.exists_antilipschitzWith hT

  let f : V → (Fin n → ℤ) := fun y => if h : y ∈ M then fun j => b.repr ⟨y, h⟩ j else 0
  have hfy : ∀ y (h : y ∈ M), f y = fun j => b.repr ⟨y, h⟩ j := fun y h => by simp [f, h]
  have hinj : Set.InjOn f Y := by
    intro y hy z hz hyz
    have h1 := hMY hy
    have h2 := hMY hz
    rw [hfy y h1, hfy z h2] at hyz
    have : b.repr ⟨y, h1⟩ = b.repr ⟨z, h2⟩ := by
      ext j; exact congrFun hyz j
    have := b.repr.injective this
    simpa using congrArg Subtype.val this
  have hΦy : ∀ y (h : y ∈ M), Φ y = T (fun j => ((b.repr ⟨y, h⟩ j : ℤ) : ℝ)) := by
    intro y h
    have hs' : y = ∑ j, b.repr ⟨y, h⟩ j • e j := by
      have := congrArg (Subtype.val : M → V) (b.sum_repr ⟨y, h⟩)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    conv_lhs => rw [hs']
    simp [T, Fintype.linearCombination_apply, map_sum, map_zsmul, Int.cast_smul_eq_zsmul]
  set N : ℤ := ⌈(K : ℝ) * R⌉
  have hsub : f '' Y ⊆ Set.Icc (fun _ => -N) (fun _ => N) := by
    rintro _ ⟨y, hy, rfl⟩
    have h := hMY hy
    rw [hfy y h]
    set c : Fin n → ℝ := fun j => ((b.repr ⟨y, h⟩ j : ℤ) : ℝ)
    have hc : ‖c‖ ≤ (K : ℝ) * R := by
      have h1 := ZeroHomClass.bound_of_antilipschitz T hK c
      rw [← hΦy y h] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left (hR y hy) K.2)
    have hcj : ∀ j, |c j| ≤ (K : ℝ) * R := fun j => by
      have h0 : ‖c j‖ ≤ ‖c‖ := norm_le_pi_norm c j
      rw [Real.norm_eq_abs] at h0
      exact h0.trans hc
    constructor <;> intro j
    · have h3 : -((K : ℝ) * R) ≤ c j := (abs_le.1 (hcj j)).1
      have h4 : (-(N : ℝ)) ≤ c j := le_trans (neg_le_neg (Int.le_ceil _)) h3
      have h5 : ((-N : ℤ) : ℝ) ≤ ((b.repr ⟨y, h⟩ j : ℤ) : ℝ) := by push_cast; exact h4
      exact Int.cast_le.1 h5
    · have h4 : c j ≤ (N : ℝ) := ((abs_le.1 (hcj j)).2).trans (Int.le_ceil _)
      exact Int.cast_le.1 h4
  exact Set.Finite.of_finite_image ((Set.finite_Icc _ _).subset hsub) hinj

end GlobalTheory
