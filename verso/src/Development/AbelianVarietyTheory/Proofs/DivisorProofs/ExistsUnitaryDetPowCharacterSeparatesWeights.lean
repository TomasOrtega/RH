import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplTupBijective
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

/- English proof (translation)
Introduce `ι _ a ha n n₀ hne`. Take `⟨τ₀, hτ⟩` from `Function.ne_iff.mp hne`. Establish `hN : n τ₀ + n₀ τ₀ + 1 ≠ 0` using `by omega`. Establish `hz : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / ((n τ₀ + n₀ τ₀ + 1 : ℕ) : ℂ))) (n τ₀ + n₀ τ₀ + 1)` using `Complex.isPrimitiveRoot_exp _ hN`. Use `set z : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((n τ₀ + n₀ τ₀ + 1 : ℕ) : ℂ)) with hzdef`.

Establish `hzn : ‖z‖ = 1` using `hz.norm'_eq_one hN`. Establish `hzz : z * star z = 1`. Rewrite using `[Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hzn]`. Simplify using the standard rewrite rules. Set `d : Fin a → ℂ` to `Function.update 1 ⟨0, ha⟩ z`.

Establish `hU : Matrix.diagonal d ∈ Matrix.unitaryGroup (Fin a) ℂ`. Rewrite using `[Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `only [d, Function.update_apply, Pi.star_apply]`.

Use `split_ifs`. Conclude with `hzz`. Simplify using the standard rewrite rules. Set `g : ι → Matrix.unitaryGroup (Fin a) ℂ` to `fun τ => if τ = τ₀ then ⟨_, hU⟩ else 1`. Use `⟨g, ?_⟩` and prove the remaining obligations.

Establish `key : ∀ m : ι → ℕ, GlobalTheory.MinorFrame.detChar m (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) = z ^ m τ₀`. Introduce `m`. Unfold `GlobalTheory.MinorFrame.detChar`. Rewrite using `[Finset.prod_eq_single τ₀]`. Simplify using `only [g, if_pos rfl, Matrix.det_diagonal, d]`.

Rewrite using `[Finset.prod_update_of_mem (Finset.mem_univ _)]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[g, hb]`. Simplify using the standard rewrite rules.

Rewrite using `[key, key]`. Introduce `h`. Conclude with `hτ (hz.pow_inj (by omega) (by omega) h)`.
-/
theorem GlobalTheory.MinorFrame.exists_unitary_detChar_ne : ∀ {ι : Type} [Fintype ι] (a : ℕ), 0 < a → ∀ n n₀ : ι → ℕ, n ≠ n₀ →
    ∃ g : ι → Matrix.unitaryGroup (Fin a) ℂ, GlobalTheory.MinorFrame.detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) ≠ GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) := by
  intro ι _ a ha n n₀ hne
  classical
  obtain ⟨τ₀, hτ⟩ := Function.ne_iff.mp hne
  have hN : n τ₀ + n₀ τ₀ + 1 ≠ 0 := by omega
  have hz : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / ((n τ₀ + n₀ τ₀ + 1 : ℕ) : ℂ))) (n τ₀ + n₀ τ₀ + 1) :=
    Complex.isPrimitiveRoot_exp _ hN
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((n τ₀ + n₀ τ₀ + 1 : ℕ) : ℂ)) with hzdef
  have hzn : ‖z‖ = 1 := hz.norm'_eq_one hN
  have hzz : z * star z = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hzn]; simp
  let d : Fin a → ℂ := Function.update 1 ⟨0, ha⟩ z
  have hU : Matrix.diagonal d ∈ Matrix.unitaryGroup (Fin a) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simp only [d, Function.update_apply, Pi.star_apply]
    split_ifs
    · exact hzz
    · simp
  let g : ι → Matrix.unitaryGroup (Fin a) ℂ := fun τ => if τ = τ₀ then ⟨_, hU⟩ else 1
  refine ⟨g, ?_⟩
  have key : ∀ m : ι → ℕ, GlobalTheory.MinorFrame.detChar m (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) = z ^ m τ₀ := by
    intro m
    unfold GlobalTheory.MinorFrame.detChar
    rw [Finset.prod_eq_single τ₀]
    · simp only [g, if_pos rfl, Matrix.det_diagonal, d]
      rw [Finset.prod_update_of_mem (Finset.mem_univ _)]
      simp
    · intro b _ hb
      simp [g, hb]
    · simp
  rw [key, key]
  intro h
  exact hτ (hz.pow_inj (by omega) (by omega) h)
