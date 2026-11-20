import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraRestrictionTwoBlockCuspidalEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassFunctionDegreeEqSumDerivativesStatement

noncomputable section

namespace GlobalTheory.GLq

open Polynomial Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

/- English proof (translation)
Take `⟨V, -, hV⟩` from `h`. Introduce `x y`. Rewrite using `[← hV, ← hV]`. Conclude with `FDRep.char_conj V x y`.
-/
theorem isClass_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsClass χ := by
  obtain ⟨V, -, hV⟩ := h
  intro x y
  rw [← hV, ← hV]
  exact FDRep.char_conj V x y

variable {g : ℕ} [Fact g.Prime]

/- English proof (translation)
Unfold `res`. Establish `key : ∀ x : Gn g d, (InPar 0 (x : Mt g d) ∧ tl 0 (x : Mt g d) = (h : Mt g 0) ∧ br 0 d (x : Mt g d) = (y : Mt g d)) ↔ x = y`. Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, -, hb⟩`.

Apply `Units.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `i j`. Use `congrFun (congrFun hb i) j` as an intermediate fact. Simplify `this` using `[br, entN, i.isLt, j.isLt]`. Introduce and unpack `rfl`.

Use `⟨fun i j hj _ => absurd hj (Nat.not_lt_zero _), Subsingleton.elim _ _, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i j`. Simplify using `[br, entN, i.isLt, j.isLt]`. Simplify using `only [key, Nat.zero_mul, pow_zero, inv_one, one_mul]`. Rewrite using `[Finset.sum_ite_eq' Finset.univ y]`.

Simplify using the standard rewrite rules.
-/
theorem res_zero_left {d : ℕ} (χ : Gn g d → ℂ) (h : Gn g 0) (y : Gn g d) :
    res 0 d χ h y = χ y := by
  unfold res
  have key : ∀ x : Gn g d, (InPar 0 (x : Mt g d) ∧ tl 0 (x : Mt g d) = (h : Mt g 0) ∧
      br 0 d (x : Mt g d) = (y : Mt g d)) ↔ x = y := by
    intro x
    constructor
    · rintro ⟨-, -, hb⟩
      apply Units.ext
      funext i j
      have := congrFun (congrFun hb i) j
      simpa [br, entN, i.isLt, j.isLt] using this
    · rintro rfl
      refine ⟨fun i j hj _ => absurd hj (Nat.not_lt_zero _), Subsingleton.elim _ _, ?_⟩
      funext i j
      simp [br, entN, i.isLt, j.isLt]
  simp only [key, Nat.zero_mul, pow_zero, inv_one, one_mul]
  rw [Finset.sum_ite_eq' Finset.univ y]
  simp

/- English proof (translation)
Unfold `der`. Establish `: res 0 (d - 0) χ 1 = χ` using `funext fun y => res_zero_left χ 1 y`. Rewrite using `[this]`.
-/
theorem der_zero_one (ψ : AddChar (ZMod g) ℂ) {d : ℕ} (χ : Gn g d → ℂ) :
    der ψ 0 χ 1 = wh ψ χ := by
  unfold der
  have : res 0 (d - 0) χ 1 = χ := funext fun y => res_zero_left χ 1 y
  rw [this]

/- English proof (translation)
Unfold `der wh tr`. Establish `: res m (d - m) χ h = fun _ => 0` using `funext fun y => res_cusp_eq_zero g d m χ hχ h0 hm h y`. Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem der_cusp_eq_zero (ψ : AddChar (ZMod g) ℂ) {d m : ℕ} {χ : Gn g d → ℂ} (hχ : IsCusp χ)
    (h0 : 0 < m) (hm : m < d) (h : Gn g m) : der ψ m χ h = 0 := by
  unfold der wh tr
  have : res m (d - m) χ h = fun _ => 0 := funext fun y => res_cusp_eq_zero g d m χ hχ h0 hm h y
  rw [this]
  simp

/- English proof (translation)
Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `i hi`. Establish `hi1 : i ≠ 0` using `by simp at hi; omega`. Establish `hg : 1 < g` using `(Fact.out : g.Prime).one_lt`. Establish `hlt : 1 < g ^ i` using `Nat.one_lt_pow hi1 hg`.

Introduce `h`. Establish `h' : ((g ^ i : ℕ) : ℂ) = ((1 : ℕ) : ℂ)` using `by push_cast; exact sub_eq_zero.mp h`. Use `Nat.cast_injective h'` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem green_deg_ne_zero (d : ℕ) : ∏ i ∈ Finset.Ico 1 d, ((g : ℂ) ^ i - 1) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  have hi1 : i ≠ 0 := by simp at hi; omega
  have hg : 1 < g := (Fact.out : g.Prime).one_lt
  have hlt : 1 < g ^ i := Nat.one_lt_pow hi1 hg
  intro h
  have h' : ((g ^ i : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by push_cast; exact sub_eq_zero.mp h
  have := Nat.cast_injective h'
  omega

/- English proof (translation)
Introduce `g _ ψ hψ d χ hχ hdeg`. Establish `hd : 0 < d` using `hχ.1`. Establish `hform` using `GlobalTheory.T.classFunction_degree_eq_sum_derivatives g ψ hψ d χ hd (isClass_of_isIrr hχ.2.1)`. Rewrite `hform` using `[Finset.sum_eq_single 0]`. Rewrite `hform` using `[der_zero_one, zero_add, hdeg]`.

Establish `hne` using `green_deg_ne_zero (g := g) d`. Establish `: (wh ψ χ - 1) * ∏ i ∈ Finset.Ico 1 d, ((g : ℂ) ^ i - 1) = 0`. Rewrite using `[sub_mul, ← hform]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hne)`.

Introduce `m hm hm0`. Rewrite using `[der_cusp_eq_zero ψ hχ (Nat.pos_of_ne_zero hm0) (Finset.mem_range.mp hm), zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_range.mpr hd) h`.
-/
theorem wh_cusp_eq_one : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (d : ℕ)
    (χ : Gn g d → ℂ), IsCusp χ → χ 1 = ∏ i ∈ Finset.Ico 1 d, ((g : ℂ) ^ i - 1) → wh ψ χ = 1 := by
  intro g _ ψ hψ d χ hχ hdeg
  have hd : 0 < d := hχ.1
  have hform := GlobalTheory.T.classFunction_degree_eq_sum_derivatives g ψ hψ d χ hd (isClass_of_isIrr hχ.2.1)
  rw [Finset.sum_eq_single 0] at hform
  · rw [der_zero_one, zero_add, hdeg] at hform
    have hne := green_deg_ne_zero (g := g) d
    have : (wh ψ χ - 1) * ∏ i ∈ Finset.Ico 1 d, ((g : ℂ) ^ i - 1) = 0 := by
      rw [sub_mul, ← hform]; ring
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hne)
  · intro m hm hm0
    rw [der_cusp_eq_zero ψ hχ (Nat.pos_of_ne_zero hm0) (Finset.mem_range.mp hm), zero_mul]
  · intro h; exact absurd (Finset.mem_range.mpr hd) h

end GlobalTheory.GLq
