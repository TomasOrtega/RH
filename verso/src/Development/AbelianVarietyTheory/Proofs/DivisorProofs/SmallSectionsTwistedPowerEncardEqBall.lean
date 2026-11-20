import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentedBundleSectionsRationalFunctionsDictStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundlePowStatement
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VolBr.SmallBall

/- English proof (translation)
Simplify using `only [Weight.nsq, HermLB.pow, HermLB.shift, Weight.pow]`. Use `erw [Weight.zpow_φ, Weight.zpow_φ]`. Rewrite using `[mul_assoc, ← Real.exp_add]`. Simplify using `only [Weight.addFn]`. Use `congr 2`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem nsq_shift_pow {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (L : HermLB p) (t : (k →+* ℂ) → ℝ)
    (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) (m : ℕ) (σ : k →+* ℂ) (f : (L.pow m).B.ι → CxPts p σ → ℂ)
    (y : CxPts p σ) :
    (((L.shift t ht).pow m).φ σ).nsq f y = ((L.pow m).φ σ).nsq f y * Real.exp (-(2 * m * t σ)) := by
  simp only [Weight.nsq, HermLB.pow, HermLB.shift, Weight.pow]
  erw [Weight.zpow_φ, Weight.zpow_φ]
  rw [mul_assoc, ← Real.exp_add]
  simp only [Weight.addFn]
  congr 2
  push_cast
  ring

/- English proof (translation)
Rewrite using `[sq, ← Real.exp_add, ← two_mul, ← h, Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos d)]`.
-/
theorem mul_exp_le_one_iff (x c d : ℝ) (h : d = 2 * c) : x * Real.exp (-d) ≤ 1 ↔ x ≤ Real.exp c ^ 2 := by
  rw [sq, ← Real.exp_add, ← two_mul, ← h, Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos d)]

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

/- English proof (translation)
Unfold `Pair.nu`. Check the signs of the components of the expression.
-/
theorem nu_nonneg (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    0 ≤ P.nu a b σ y f := by
  unfold Pair.nu; positivity

/- English proof (translation)
Take `⟨e, he, hr, hn, -⟩` from `GlobalTheory.T.representedBundle_sections_rationalFunctions_dict k X p P a b N h`. Establish `hi : e '' S = P.Bl a b R`. Use extensionality with `f`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, rfl⟩`.

Use `⟨?_, fun σ y => ?_⟩` and prove the remaining obligations. Establish `: e u ∈ Set.range e` using `⟨u, rfl⟩`. Rewrite `this` using `[hr]`. Conclude with `this`. Establish `h1` using `(hS u).1 hu σ y`.

Rewrite `h1` using `[← hn]`. Conclude with `(pow_le_pow_iff_left₀ (nu_nonneg P a b σ y _) hR two_ne_zero).1 h1`. Introduce and unpack `⟨hf, hb⟩`. Establish `: f ∈ Set.range e` using `by rw [hr]; exact hf`. Take `⟨u, rfl⟩` from `this`.

Use `⟨u, (hS u).2 fun σ y => ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[← hn]`. Conclude with `pow_le_pow_left₀ (nu_nonneg P a b σ y _) (hb σ y) 2`. Rewrite using `[← hi, he.encard_image]`.
-/
theorem encard_eq_Bl (P : Pair p) {a b : ℤ} {N : HermLB p} (h : P.Rep a b N) (S : Set N.B.Sec) (R : ℝ) (hR : 0 ≤ R)
    (hS : ∀ u, u ∈ S ↔ ∀ σ (y : CxPts p σ), (N.φ σ).nsq (secVal p σ u) y ≤ R ^ 2) :
    S.encard = (P.Bl a b R).encard := by
  obtain ⟨e, he, hr, hn, -⟩ := GlobalTheory.T.representedBundle_sections_rationalFunctions_dict k X p P a b N h
  have hi : e '' S = P.Bl a b R := by
    ext f
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨?_, fun σ y => ?_⟩
      · have : e u ∈ Set.range e := ⟨u, rfl⟩
        rw [hr] at this
        exact this
      · have h1 := (hS u).1 hu σ y
        rw [← hn] at h1
        exact (pow_le_pow_iff_left₀ (nu_nonneg P a b σ y _) hR two_ne_zero).1 h1
    · rintro ⟨hf, hb⟩
      have : f ∈ Set.range e := by rw [hr]; exact hf
      obtain ⟨u, rfl⟩ := this
      refine ⟨u, (hS u).2 fun σ y => ?_, rfl⟩
      rw [← hn]
      exact pow_le_pow_left₀ (nu_nonneg P a b σ y _) (hb σ y) 2
  rw [← hi, he.encard_image]

/- English proof (translation)
Introduce `k _ X _ p P a b M hM t m`. Establish `hm` using `GlobalTheory.T.represents_hermitianLineBundle_pow k X p P a b M m hM`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `encard_eq_Bl P hm _ _ (Real.exp_pos _).le fun u => ?_` and prove the remaining obligations. Simplify using `only [HermLB.smallSec, Set.mem_setOf_eq]`.

Use `forall_congr' fun σ => forall_congr' fun y => ?_` and prove the remaining obligations. Establish `e` using `nsq_shift_pow M (fun _ => t) (fun _ => rfl) m σ (secVal p σ u) y`. Conclude with `(iff_of_eq (congrArg (· ≤ (1 : ℝ)) e)).trans (mul_exp_le_one_iff _ _ _ (by ring))`. Use `encard_eq_Bl P hm _ _ zero_le_one fun u => ?_` and prove the remaining obligations. Simplify using `only [HermLB.smallSec, Set.mem_setOf_eq, one_pow]`.

Use `encard_eq_Bl P hM _ _ (Real.exp_pos _).le fun u => ?_` and prove the remaining obligations. Simplify using `only [HermLB.smallSec, Set.mem_setOf_eq]`. Use `forall_congr' fun σ => forall_congr' fun y => ?_` and prove the remaining obligations. Establish `e` using `HermLB.nsq_shift M (fun _ => t) (fun _ => rfl) (σ := σ) (secVal p σ u) y`. Conclude with `(iff_of_eq (congrArg (· ≤ (1 : ℝ)) e)).trans (mul_exp_le_one_iff _ _ _ (by ring))`.
-/
theorem main : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (M : HermLB p), P.Rep a b M → ∀ (t : ℝ) (m : ℕ), ((M.shift (fun _ => t) fun _ => rfl).pow m).smallSec.encard = (P.Bl (m * a) (m * b) (Real.exp (t * m))).encard ∧ (M.pow m).smallSec.encard = (P.Bl (m * a) (m * b) 1).encard ∧ (M.shift (fun _ => t) fun _ => rfl).smallSec.encard = (P.Bl a b (Real.exp t)).encard := by
  intro k _ X _ p P a b M hM t m
  have hm := GlobalTheory.T.represents_hermitianLineBundle_pow k X p P a b M m hM
  refine ⟨?_, ?_, ?_⟩
  · refine encard_eq_Bl P hm _ _ (Real.exp_pos _).le fun u => ?_
    simp only [HermLB.smallSec, Set.mem_setOf_eq]
    refine forall_congr' fun σ => forall_congr' fun y => ?_
    have e := nsq_shift_pow M (fun _ => t) (fun _ => rfl) m σ (secVal p σ u) y
    exact (iff_of_eq (congrArg (· ≤ (1 : ℝ)) e)).trans (mul_exp_le_one_iff _ _ _ (by ring))
  · refine encard_eq_Bl P hm _ _ zero_le_one fun u => ?_
    simp only [HermLB.smallSec, Set.mem_setOf_eq, one_pow]
  · refine encard_eq_Bl P hM _ _ (Real.exp_pos _).le fun u => ?_
    simp only [HermLB.smallSec, Set.mem_setOf_eq]
    refine forall_congr' fun σ => forall_congr' fun y => ?_
    have e := HermLB.nsq_shift M (fun _ => t) (fun _ => rfl) (σ := σ) (secVal p σ u) y
    exact (iff_of_eq (congrArg (· ≤ (1 : ℝ)) e)).trans (mul_exp_le_one_iff _ _ _ (by ring))

end GlobalTheory.VolBr.SmallBall
