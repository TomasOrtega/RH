import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.KchainSt

noncomputable section

open Matrix Finset

namespace PositivityTheory.RgBcC.LfSt.Kchain.KcDual

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt PositivityTheory.RgBcC.LfSt.Kchain
open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

/- English proof (translation)
Take `⟨-, horth, -⟩` from `hH n`. Simplify using `only [hOf, Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul, horth, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_ite_eq']`. Simplify using `only [Finset.mem_univ, if_true]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem trace_hOf_mul (hH : HbFacts) (u u' : Fin n × Fin n → ℝ) :
    (hOf u * hOf u').trace = ∑ p, ((u p * u' p : ℝ) : ℂ) := by
  obtain ⟨-, horth, -⟩ := hH n
  simp only [hOf, Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sum,
    Matrix.trace_smul, horth, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  push_cast
  ring

/- English proof (translation)
Simplify using `only [hOf, map_sum]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Establish `e : ((u p : ℝ) : ℂ) • (hb p : Mat n) = (u p) • hb p`. Use extensionality with `a b`. Simplify using `[Complex.real_smul]`.

Rewrite using `[e, map_smul]`. Use extensionality with `v`. Simplify using `[Complex.coe_smul]`.
-/
theorem map_hOf {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (α : Mat n →ₗ[ℝ] (V →L[ℂ] V))
    (u : Fin n × Fin n → ℝ) : α (hOf u) = ∑ p, ((u p : ℝ) : ℂ) • α (hb p) := by
  simp only [hOf, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have e : ((u p : ℝ) : ℂ) • (hb p : Mat n) = (u p) • hb p := by
    ext a b
    simp [Complex.real_smul]
  rw [e, map_smul]
  ext v
  simp [Complex.coe_smul]

/- English proof (translation)
Introduce `n V _ _ α β A A' hA hA' htr`. Take `⟨-, -, hcoord, -, -, -, -, -⟩` from `hH n`. Use `set a : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ := fun i p => coords (A i) p with ha`. Use `set a' : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ := fun i p => coords (A' i) p with ha'`. Establish `eA : ∀ i, A i = hOf (a i)` using `fun i => (hcoord _ (hA i)).symm`.

Establish `eA' : ∀ i, A' i = hOf (a' i)` using `fun i => (hcoord _ (hA' i)).symm`. Establish `h1 : a * a'ᵀ = 1`. Use extensionality with `i j`. Use `htr i j` as an intermediate fact. Rewrite `this` using `[eA i, eA' j, trace_hOf_mul hH]`.

Establish `hre` using `congrArg Complex.re this`. Simplify using `only [Complex.re_sum, Complex.ofReal_re] at hre`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]`. Rewrite using `[hre]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `h2 : a'ᵀ * a = 1` using `mul_eq_one_comm.mp h1`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[eA i, eA' i, map_hOf α, map_hOf β, Finset.sum_mul_sum]`. Use `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_mul_smul_comm]`. Use `push_cast`. Both sides reduce to the same expression. Use `_ = ∑ p, ∑ q, ((a'ᵀ * a) q p : ℂ) • (α (hb p) * β (hb q)) := by`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_smul]`. Use `congr 1`.

Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply]`. Use `push_cast`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Use `_ = ∑ p, α (hb p) * β (hb p) := by`.

Rewrite using `[h2]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Simplify using `[Matrix.one_apply]`.
-/
theorem dualSum (hH : HbFacts) : DualSum := by
  intro n V _ _ α β A A' hA hA' htr
  obtain ⟨-, -, hcoord, -, -, -, -, -⟩ := hH n
  set a : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ := fun i p => coords (A i) p with ha
  set a' : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ := fun i p => coords (A' i) p with ha'
  have eA : ∀ i, A i = hOf (a i) := fun i => (hcoord _ (hA i)).symm
  have eA' : ∀ i, A' i = hOf (a' i) := fun i => (hcoord _ (hA' i)).symm
  have h1 : a * a'ᵀ = 1 := by
    ext i j
    have := htr i j
    rw [eA i, eA' j, trace_hOf_mul hH] at this
    have hre := congrArg Complex.re this
    simp only [Complex.re_sum, Complex.ofReal_re] at hre
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
    rw [hre]
    split_ifs <;> simp
  have h2 : a'ᵀ * a = 1 := mul_eq_one_comm.mp h1
  calc ∑ i, α (A i) * β (A' i)
      = ∑ i, ∑ p, ∑ q, ((a i p * a' i q : ℝ) : ℂ) • (α (hb p) * β (hb q)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [eA i, eA' i, map_hOf α, map_hOf β, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        rw [smul_mul_smul_comm]
        push_cast
        rfl
    _ = ∑ p, ∑ q, ((a'ᵀ * a) q p : ℂ) • (α (hb p) * β (hb q)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [← Finset.sum_smul]
        congr 1
        simp only [Matrix.mul_apply, Matrix.transpose_apply]
        push_cast
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = ∑ p, α (hb p) * β (hb p) := by
        rw [h2]
        refine Finset.sum_congr rfl fun p _ => ?_
        simp [Matrix.one_apply]

end PositivityTheory.RgBcC.LfSt.Kchain.KcDual
