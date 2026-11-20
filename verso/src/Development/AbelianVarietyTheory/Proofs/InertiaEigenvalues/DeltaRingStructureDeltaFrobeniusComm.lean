import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

/- English proof (translation)
Establish `h : ((a ^ l : ℤ) : ZMod l) = ((a : ℤ) : ZMod l)` using `by push_cast; exact ZMod.pow_card _`. Rewrite `h` using `[ZMod.intCast_eq_intCast_iff_dvd_sub]`. Take `⟨b, hb⟩` from `h`. Conclude with `⟨b, by simp only [RingHom.id_apply]; linear_combination hb⟩`.
-/
theorem int_frob_lift (l : ℕ) [hl : Fact l.Prime] (a : ℤ) :
    ∃ b : ℤ, (RingHom.id ℤ) a = a ^ l + (l : ℤ) * b := by
  have h : ((a ^ l : ℤ) : ZMod l) = ((a : ℤ) : ZMod l) := by
    push_cast; exact ZMod.pow_card _
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  obtain ⟨b, hb⟩ := h
  exact ⟨b, by simp only [RingHom.id_apply]; linear_combination hb⟩

def intDelta (l : ℕ) [hl : Fact l.Prime] : Delta l ℤ :=
  Delta.ofLift l (RingHom.id ℤ)
    (fun x hx => (mul_eq_zero.1 hx).resolve_left (by exact_mod_cast hl.out.ne_zero))
    (int_frob_lift l)

/- English proof (translation)
Use `set D := polyDelta (intDelta l)`. Establish `hl0 : (l : MvPolynomial ℕ ℤ) ≠ 0` using `Nat.cast_ne_zero.2 hl.out.ne_zero`. Use `mul_left_cancel₀ hl0 ?_` and prove the remaining obligations. Establish `h1` using `D.φ_eq (D.φ x)`. Establish `h2` using `D.φ_eq x`.

Establish `h3 : D.φ ((l : MvPolynomial ℕ ℤ) * D.δ x) = (l : MvPolynomial ℕ ℤ) * D.φ (D.δ x)`. Rewrite using `[map_mul, map_natCast]`. Establish `h4 : D.φ (D.φ x) = D.φ (x ^ l) + D.φ ((l : MvPolynomial ℕ ℤ) * D.δ x)`. Rewrite using `[← map_add, ← h2]`. Rewrite `h4` using `[map_pow]`.

Take the linear combination `-h1 + h4 + h3`.
-/
theorem poly_δ_φ (l : ℕ) [hl : Fact l.Prime] (x : MvPolynomial ℕ ℤ) :
    (polyDelta (intDelta l)).δ ((polyDelta (intDelta l)).φ x) =
      (polyDelta (intDelta l)).φ ((polyDelta (intDelta l)).δ x) := by
  set D := polyDelta (intDelta l)
  have hl0 : (l : MvPolynomial ℕ ℤ) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  refine mul_left_cancel₀ hl0 ?_
  have h1 := D.φ_eq (D.φ x)
  have h2 := D.φ_eq x
  have h3 : D.φ ((l : MvPolynomial ℕ ℤ) * D.δ x) = (l : MvPolynomial ℕ ℤ) * D.φ (D.δ x) := by
    rw [map_mul, map_natCast]
  have h4 : D.φ (D.φ x) = D.φ (x ^ l) + D.φ ((l : MvPolynomial ℕ ℤ) * D.δ x) := by
    rw [← map_add, ← h2]
  rw [map_pow] at h4
  linear_combination -h1 + h4 + h3

/- English proof (translation)
Introduce `l hl A _ D a`. Use `set D₀ := polyDelta (intDelta l)`. Set `g : MvPolynomial ℕ ℤ →+* A` to `MvPolynomial.eval₂Hom (Int.castRingHom A) (fun i => D.δ^[i] a)`. Establish `hg : ∀ p, p ∈ δLocus D₀ D g`. Introduce `p`.

Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C n`. Establish `: MvPolynomial.C n = ((n : ℤ) : MvPolynomial ℕ ℤ)` using `by simp`. Rewrite using `[this]`. Conclude with `intCast_mem _ n`.

Consider the case `add p q hp hq => exact add_mem hp hq`. Consider the case `mul_X p i hp`. Use `mul_mem hp (mem_δLocus.2 ?_)` and prove the remaining obligations. Rewrite using `[polyDelta_X]`. Simplify using `only [g, MvPolynomial.eval₂Hom_X']`.

Rewrite using `[Function.iterate_succ_apply']`. Establish `hgδ : ∀ p, g (D₀.δ p) = D.δ (g p)` using `fun p => mem_δLocus.1 (hg p)`. Establish `hgφ : ∀ p, g (D₀.φ p) = D.φ (g p)` using `Delta.map_φ_of_map_δ D₀ D g hgδ`. Establish `hX : g (MvPolynomial.X 0) = a` using `by simp [g]`. Use `congrArg g (poly_δ_φ l (MvPolynomial.X 0))` as an intermediate fact.

Rewrite `this` using `[hgδ, hgφ, hgφ, hgδ, hX]`. Conclude with `this`.
-/
theorem Delta.δ_φ_comm : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (a : A),
    D.δ (D.φ a) = D.φ (D.δ a) := by
  intro l hl A _ D a
  set D₀ := polyDelta (intDelta l)
  let g : MvPolynomial ℕ ℤ →+* A := MvPolynomial.eval₂Hom (Int.castRingHom A) (fun i => D.δ^[i] a)
  have hg : ∀ p, p ∈ δLocus D₀ D g := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C n =>
      have : MvPolynomial.C n = ((n : ℤ) : MvPolynomial ℕ ℤ) := by simp
      rw [this]; exact intCast_mem _ n
    | add p q hp hq => exact add_mem hp hq
    | mul_X p i hp =>
      refine mul_mem hp (mem_δLocus.2 ?_)
      rw [polyDelta_X]
      simp only [g, MvPolynomial.eval₂Hom_X']
      rw [Function.iterate_succ_apply']
  have hgδ : ∀ p, g (D₀.δ p) = D.δ (g p) := fun p => mem_δLocus.1 (hg p)
  have hgφ : ∀ p, g (D₀.φ p) = D.φ (g p) := Delta.map_φ_of_map_δ D₀ D g hgδ
  have hX : g (MvPolynomial.X 0) = a := by simp [g]
  have := congrArg g (poly_δ_φ l (MvPolynomial.X 0))
  rw [hgδ, hgφ, hgφ, hgδ, hX] at this
  exact this

end GlobalTheory.BSP
