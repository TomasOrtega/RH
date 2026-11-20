import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.BlockUni

/- English proof (translation)
Rewrite using `[Matrix.isUnit_iff_isUnit_det]`. Establish `hb : A.BlockTriangular id` using `fun i j h => h0 i j h`. Rewrite using `[Matrix.det_of_upperTriangular hb]`. Simplify using `[h1]`.
-/
theorem unitri_isUnit {R : Type} [CommRing R] {m : ℕ} (A : Matrix (Fin m) (Fin m) R)
    (h0 : ∀ i j, j < i → A i j = 0) (h1 : ∀ i, A i i = 1) : IsUnit A := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have hb : A.BlockTriangular id := fun i j h => h0 i j h
  rw [Matrix.det_of_upperTriangular hb]
  simp [h1]

/- English proof (translation)
Introduce `R _ n σ M w Y`. Use `set x : Matrix (Fin n) (Fin (σ+1)) R := Matrix.of (fun k => Fin.snoc (α := fun _ => R) (M k) (w k)) with hx`. Establish `hxc : ∀ k i, x k (Fin.castSucc i) = M k i` using `by intro k i; simp [hx]`. Establish `hxl : ∀ k, x k (Fin.last σ) = w k` using `by intro k; simp [hx]`. Establish `col : ∀ (U : Matrix (Fin (σ+1)) (Fin (σ+1)) R) k j, (x * U) k j = ∑ i, M k i * U (Fin.castSucc i) j + w k * U (Fin.last σ) j`.

Introduce `U k j`. Rewrite using `[Matrix.mul_apply, Fin.sum_univ_castSucc]`. Simplify using `only [hxc, hxl]`. Establish `Ycol : ∀ k j, (Y * x) k (Fin.castSucc j) = (Y * M) k j`. Introduce `k j`.

Simplify using `only [Matrix.mul_apply, hxc]`. Establish `Ylast : ∀ k, (Y * x) k (Fin.last σ) = (Y *ᵥ w) k`. Introduce `k`. Simplify using `only [Matrix.mul_apply, Matrix.mulVec, dotProduct, hxl]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨U, hU, hE⟩`. Establish `hU'` using `(GlobalTheory.UniIndexPrime.mem_uniSub U).1 hU`. Set `u : Matrix (Fin σ) (Fin σ) R` to `Matrix.of fun i j => (U : Matrix _ _ R) (Fin.castSucc i) (Fin.castSucc j)`. Establish `hu0 : ∀ i j, j < i → u i j = 0` using `fun i j h => hU'.1 (Fin.castSucc i) (Fin.castSucc j) (Fin.castSucc_lt_castSucc_iff.2 h)`. Establish `hu1 : ∀ i, u i i = 1` using `fun i => hU'.2 _`.

Use `⟨(unitri_isUnit u hu0 hu1).unit, (GlobalTheory.UniIndexPrime.mem_uniSub _).2 ⟨hu0, hu1⟩, fun i => (U : Matrix _ _ R) (Fin.castSucc i) (Fin.last σ), ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `k j`. Establish `h` using `congrFun (congrFun hE k) (Fin.castSucc j)`. Rewrite `h` using `[Ycol, col]`. Rewrite using `[h, IsUnit.unit_spec, Matrix.mul_apply]`.

Establish `h0 : (U : Matrix _ _ R) (Fin.last σ) (Fin.castSucc j) = 0` using `hU'.1 _ _ (Fin.castSucc_lt_last j)`. Simplify using `[h0, u]`. Use extensionality with `k`. Establish `h` using `congrFun (congrFun hE k) (Fin.last σ)`. Rewrite `h` using `[Ylast, col, hU'.2 (Fin.last σ)]`.

Rewrite using `[h]`. Simplify using `only [Pi.add_apply, Matrix.mulVec, dotProduct]`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `⟨u, hu, v, h1, h2⟩`. Establish `hu'` using `(GlobalTheory.UniIndexPrime.mem_uniSub u).1 hu`.

Set `U : Matrix (Fin (σ+1)) (Fin (σ+1)) R` to `Matrix.of fun a b => Fin.lastCases (Fin.lastCases (1 : R) (fun _ => 0) b) (fun i => Fin.lastCases (v i) (fun j => (u : Matrix _ _ R) i j) b) a`. Establish `Ucc : ∀ i j, U (Fin.castSucc i) (Fin.castSucc j) = (u : Matrix _ _ R) i j`. Introduce `i j`. Simplify using `[U]`. Establish `Ucl : ∀ i, U (Fin.castSucc i) (Fin.last σ) = v i` using `by intro i; simp [U]`.

Establish `Ulc : ∀ j, U (Fin.last σ) (Fin.castSucc j) = 0` using `by intro j; simp [U]`. Establish `Ull : U (Fin.last σ) (Fin.last σ) = 1` using `by simp [U]`. Establish `hU0 : ∀ a b, b < a → U a b = 0`. Introduce `a b hab`. Proceed by induction on `a using Fin.lastCases with`.

Consider the case `last`. Proceed by induction on `b using Fin.lastCases with`. Consider the case `last => exact absurd hab (lt_irrefl _)`. Consider the case `cast j => exact Ulc j`. Consider the case `cast i`.

Proceed by induction on `b using Fin.lastCases with`. Consider the case `last => exact absurd hab (not_lt.2 (Fin.castSucc_lt_last i).le)`. Consider the case `cast j => rw [Ucc]`. Conclude with `hu'.1 i j (Fin.castSucc_lt_castSucc_iff.1 hab)`. Establish `hU1 : ∀ a, U a a = 1`.

Introduce `a`. Proceed by induction on `a using Fin.lastCases with`. Consider the case `last => exact Ull`. Consider the case `cast i => rw [Ucc]`. Conclude with `hu'.2 i`.

Use `⟨(unitri_isUnit U hU0 hU1).unit, (GlobalTheory.UniIndexPrime.mem_uniSub _).2 ⟨hU0, hU1⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[IsUnit.unit_spec]`. Use extensionality with `k b`. Proceed by induction on `b using Fin.lastCases with`. Consider the case `last`.

Rewrite using `[Ylast, col, h2, Ull]`. Simplify using `only [Ucl, Pi.add_apply, Matrix.mulVec, dotProduct]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `cast j`. Rewrite using `[Ycol, col, h1, Matrix.mul_apply]`.

Simplify using `only [Ucc, Ulc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem snoc_uni_iff : ∀ (R : Type) [CommRing R] (n σ : ℕ) (M : Matrix (Fin n) (Fin σ) R) (w : Fin n → R) (Y : Matrix (Fin n) (Fin n) R), (∃ U ∈ GlobalTheory.UniIndexPrime.uniSub (σ + 1) R, Y * Matrix.of (fun k => Fin.snoc (α := fun _ => R) (M k) (w k)) = Matrix.of (fun k => Fin.snoc (α := fun _ => R) (M k) (w k)) * (U : Matrix (Fin (σ + 1)) (Fin (σ + 1)) R)) ↔ ∃ u ∈ GlobalTheory.UniIndexPrime.uniSub σ R, ∃ v : Fin σ → R, Y * M = M * (u : Matrix (Fin σ) (Fin σ) R) ∧ Y *ᵥ w = w + M *ᵥ v := by
  intro R _ n σ M w Y
  set x : Matrix (Fin n) (Fin (σ+1)) R := Matrix.of (fun k => Fin.snoc (α := fun _ => R) (M k) (w k)) with hx
  have hxc : ∀ k i, x k (Fin.castSucc i) = M k i := by intro k i; simp [hx]
  have hxl : ∀ k, x k (Fin.last σ) = w k := by intro k; simp [hx]
  have col : ∀ (U : Matrix (Fin (σ+1)) (Fin (σ+1)) R) k j,
      (x * U) k j = ∑ i, M k i * U (Fin.castSucc i) j + w k * U (Fin.last σ) j := by
    intro U k j; rw [Matrix.mul_apply, Fin.sum_univ_castSucc]; simp only [hxc, hxl]
  have Ycol : ∀ k j, (Y * x) k (Fin.castSucc j) = (Y * M) k j := by
    intro k j; simp only [Matrix.mul_apply, hxc]
  have Ylast : ∀ k, (Y * x) k (Fin.last σ) = (Y *ᵥ w) k := by
    intro k; simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, hxl]
  constructor
  · rintro ⟨U, hU, hE⟩
    have hU' := (GlobalTheory.UniIndexPrime.mem_uniSub U).1 hU
    let u : Matrix (Fin σ) (Fin σ) R := Matrix.of fun i j => (U : Matrix _ _ R) (Fin.castSucc i) (Fin.castSucc j)
    have hu0 : ∀ i j, j < i → u i j = 0 := fun i j h =>
      hU'.1 (Fin.castSucc i) (Fin.castSucc j) (Fin.castSucc_lt_castSucc_iff.2 h)
    have hu1 : ∀ i, u i i = 1 := fun i => hU'.2 _
    refine ⟨(unitri_isUnit u hu0 hu1).unit, (GlobalTheory.UniIndexPrime.mem_uniSub _).2 ⟨hu0, hu1⟩,
      fun i => (U : Matrix _ _ R) (Fin.castSucc i) (Fin.last σ), ?_, ?_⟩
    · ext k j
      have h := congrFun (congrFun hE k) (Fin.castSucc j)
      rw [Ycol, col] at h
      rw [h, IsUnit.unit_spec, Matrix.mul_apply]
      have h0 : (U : Matrix _ _ R) (Fin.last σ) (Fin.castSucc j) = 0 := hU'.1 _ _ (Fin.castSucc_lt_last j)
      simp [h0, u]
    · ext k
      have h := congrFun (congrFun hE k) (Fin.last σ)
      rw [Ylast, col, hU'.2 (Fin.last σ)] at h
      rw [h]; simp only [Pi.add_apply, Matrix.mulVec, dotProduct]; ring
  · rintro ⟨u, hu, v, h1, h2⟩
    have hu' := (GlobalTheory.UniIndexPrime.mem_uniSub u).1 hu
    let U : Matrix (Fin (σ+1)) (Fin (σ+1)) R := Matrix.of fun a b =>
      Fin.lastCases (Fin.lastCases (1 : R) (fun _ => 0) b)
        (fun i => Fin.lastCases (v i) (fun j => (u : Matrix _ _ R) i j) b) a
    have Ucc : ∀ i j, U (Fin.castSucc i) (Fin.castSucc j) = (u : Matrix _ _ R) i j := by
      intro i j; simp [U]
    have Ucl : ∀ i, U (Fin.castSucc i) (Fin.last σ) = v i := by intro i; simp [U]
    have Ulc : ∀ j, U (Fin.last σ) (Fin.castSucc j) = 0 := by intro j; simp [U]
    have Ull : U (Fin.last σ) (Fin.last σ) = 1 := by simp [U]
    have hU0 : ∀ a b, b < a → U a b = 0 := by
      intro a b hab
      induction a using Fin.lastCases with
      | last =>
        induction b using Fin.lastCases with
        | last => exact absurd hab (lt_irrefl _)
        | cast j => exact Ulc j
      | cast i =>
        induction b using Fin.lastCases with
        | last => exact absurd hab (not_lt.2 (Fin.castSucc_lt_last i).le)
        | cast j => rw [Ucc]; exact hu'.1 i j (Fin.castSucc_lt_castSucc_iff.1 hab)
    have hU1 : ∀ a, U a a = 1 := by
      intro a
      induction a using Fin.lastCases with
      | last => exact Ull
      | cast i => rw [Ucc]; exact hu'.2 i
    refine ⟨(unitri_isUnit U hU0 hU1).unit, (GlobalTheory.UniIndexPrime.mem_uniSub _).2 ⟨hU0, hU1⟩, ?_⟩
    rw [IsUnit.unit_spec]
    ext k b
    induction b using Fin.lastCases with
    | last =>
      rw [Ylast, col, h2, Ull]
      simp only [Ucl, Pi.add_apply, Matrix.mulVec, dotProduct]; ring
    | cast j =>
      rw [Ycol, col, h1, Matrix.mul_apply]
      simp only [Ucc, Ulc]; ring

end GlobalTheory.BlockUni
