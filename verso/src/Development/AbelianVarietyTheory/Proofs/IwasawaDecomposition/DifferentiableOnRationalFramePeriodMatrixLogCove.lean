import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExponentialOfSemiAbelianFibreLinearChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombMatAddMul

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PeriodFrame

/- English proof (translation)
Use `revert h`. Use `Finset.induction_on u ?_ ?_` and prove the remaining obligations. Introduce `_`. Simplify using `only [Finset.prod_empty]`. Conclude with `differentiableOn_const _`.

Introduce `a u ha ih h`. Simplify using `only [Finset.prod_insert ha]`. Conclude with `(h a (Finset.mem_insert_self a u)).fun_mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
private theorem differentiableOn_finsetProd' {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {Idx : Type}
    (u : Finset Idx) (f : Idx → E → ℂ) {S : Set E} (h : ∀ i ∈ u, DifferentiableOn ℂ (f i) S) :
    DifferentiableOn ℂ (fun s => ∏ i ∈ u, f i s) S := by
  classical
  revert h
  refine Finset.induction_on u ?_ ?_
  · intro _
    simp only [Finset.prod_empty]
    exact differentiableOn_const _
  · intro a u ha ih h
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a u)).fun_mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Establish `hdet : (fun s => (M s).det) = fun s => ∑ σ : Equiv.Perm (Fin g), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M s (σ i) i`. Use function extensionality and compare the values at `s`. Conclude with `Matrix.det_apply' (M s)`. Rewrite using `[hdet]`. Apply `DifferentiableOn.fun_sum` to reduce the goal to its premises.

Introduce `σ _`. Apply `DifferentiableOn.const_mul` to reduce the goal to its premises. Conclude with `differentiableOn_finsetProd' Finset.univ (fun i s => M s (σ i) i) (fun i _ => h (σ i) i)`.
-/
theorem differentiableOn_det_of_entries {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}
    {M : E → Matrix (Fin g) (Fin g) ℂ} {S : Set E} (h : ∀ i j, DifferentiableOn ℂ (fun s => M s i j) S) :
    DifferentiableOn ℂ (fun s => (M s).det) S := by
  have hdet : (fun s => (M s).det) = fun s => ∑ σ : Equiv.Perm (Fin g),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M s (σ i) i := by
    funext s
    exact Matrix.det_apply' (M s)
  rw [hdet]
  apply DifferentiableOn.fun_sum
  intro σ _
  apply DifferentiableOn.const_mul
  exact differentiableOn_finsetProd' Finset.univ (fun i s => M s (σ i) i) (fun i _ => h (σ i) i)

/- English proof (translation)
Establish `hdet : DifferentiableOn ℂ (fun s => (M s).det) S` using `differentiableOn_det_of_entries h`. Establish `hadj : DifferentiableOn ℂ (fun s => (M s).adjugate i j) S`. Establish `hupd : ∀ k l, DifferentiableOn ℂ (fun s => ((M s).updateRow j (Pi.single i 1)) k l) S`. Introduce `k l`. Distinguish the cases in `hk : k = j`.

Substitute `hk` using the available equality. Simplify using `only [Matrix.updateRow_self]`. Conclude with `differentiableOn_const _`. Simplify using `only [Matrix.updateRow_ne hk]`. Conclude with `h k l`.

Use `differentiableOn_det_of_entries hupd` as an intermediate fact. Simplify `this` using `only [Matrix.adjugate_apply]`. Establish `hinv : DifferentiableOn ℂ (fun s => ((M s).det)⁻¹) S` using `hdet.fun_inv fun s hs => (hu s hs).ne_zero`. Establish `heq : (fun s => (M s)⁻¹ i j) = fun s => ((M s).det)⁻¹ * (M s).adjugate i j`. Use function extensionality and compare the values at `s`.

Rewrite using `[Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]`. Rewrite using `[heq]`. Conclude with `hinv.fun_mul hadj`.
-/
theorem differentiableOn_inv_of_entries {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}
    {M : E → Matrix (Fin g) (Fin g) ℂ} {S : Set E} (h : ∀ i j, DifferentiableOn ℂ (fun s => M s i j) S)
    (hu : ∀ s ∈ S, IsUnit (M s).det) (i j : Fin g) :
    DifferentiableOn ℂ (fun s => (M s)⁻¹ i j) S := by
  have hdet : DifferentiableOn ℂ (fun s => (M s).det) S := differentiableOn_det_of_entries h
  have hadj : DifferentiableOn ℂ (fun s => (M s).adjugate i j) S := by
    have hupd : ∀ k l, DifferentiableOn ℂ (fun s => ((M s).updateRow j (Pi.single i 1)) k l) S := by
      intro k l
      by_cases hk : k = j
      · subst hk
        simp only [Matrix.updateRow_self]
        exact differentiableOn_const _
      · simp only [Matrix.updateRow_ne hk]
        exact h k l
    have := differentiableOn_det_of_entries hupd
    simpa only [Matrix.adjugate_apply] using this
  have hinv : DifferentiableOn ℂ (fun s => ((M s).det)⁻¹) S :=
    hdet.fun_inv fun s hs => (hu s hs).ne_zero
  have heq : (fun s => (M s)⁻¹ i j) = fun s => ((M s).det)⁻¹ * (M s).adjugate i j := by
    funext s
    rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  rw [heq]
  exact hinv.fun_mul hadj

/- English proof (translation)
Simplify using `only [combMat, Matrix.of_apply]`. Apply `DifferentiableOn.fun_sum` to reduce the goal to its premises. Introduce `m _`. Conclude with `(h m i).const_mul _`.
-/
theorem differentiableOn_combMat_of_entries {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g r : ℕ}
    {l : E → Fin r → Fin g → ℂ} {S : Set E} (ε : Matrix (Fin g) (Fin r) ℚ)
    (h : ∀ m k, DifferentiableOn ℂ (fun s => l s m k) S) (i j : Fin g) :
    DifferentiableOn ℂ (fun s => combMat (l s) ε i j) S := by
  simp only [combMat, Matrix.of_apply]
  apply DifferentiableOn.fun_sum
  intro m _
  exact (h m i).const_mul _

/- English proof (translation)
Introduce `n a g r₀ r ζ lam α φ D hζ hlam hunit`. Establish `hζd : DifferentiableOn ℂ ζ (Metric.ball 0 1)` using `hζ.differentiableOn`. Establish `hζe : ∀ m k, DifferentiableOn ℂ (fun z => ζ z m k) (Metric.ball 0 1)`. Introduce `m k`. Establish `h1` using `differentiableOn_pi.1 hζd m`.

Conclude with `differentiableOn_pi.1 h1 k`. Establish `hA : ∀ i j, DifferentiableOn ℂ (fun z => combMat (ζ z) α i j) (Metric.ball 0 1)` using `fun i j => differentiableOn_combMat_of_entries α hζe i j`. Use `⟨hA, ?_⟩` and prove the remaining obligations. Introduce `i j`. Use `set T : Set (Fin n → ℂ) := {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1} with hT`.

Establish `hexp : Differentiable ℂ (fun s : Fin n → ℂ => logExp a s)`. Use `differentiable_pi.2 fun k => ?_` and prove the remaining obligations. Simplify using `only [logExp]`. Use `split_ifs`. Conclude with `(differentiable_apply k).cexp`.

Conclude with `differentiable_apply k`. Establish `hAT : ∀ i j, DifferentiableOn ℂ (fun s => combMat (ζ (logExp a s)) α i j) T`. Introduce `i j`. Conclude with `(hA i j).comp hexp.differentiableOn (fun s hs => hs.2)`. Establish `hinvT : ∀ i j, DifferentiableOn ℂ (fun s => (combMat (ζ (logExp a s)) α)⁻¹ i j) T` using `differentiableOn_inv_of_entries hAT (fun s hs => hunit s hs.1)`.

Establish `hBT : ∀ i j, DifferentiableOn ℂ (fun s => combMat (lam s) φ i j) T`. Introduce `i j`. Conclude with `(differentiableOn_combMat_of_entries φ hlam i j).mono (fun s hs => hs.1)`. Simplify using `only [perTau, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]`. Apply `DifferentiableOn.const_mul` to reduce the goal to its premises.

Apply `DifferentiableOn.fun_sum` to reduce the goal to its premises. Introduce `k _`. Conclude with `(hinvT i k).fun_mul (hBT k j)`.
-/
theorem differentiableOn_combMat_perTau : ∀ (n a g r₀ r : ℕ) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (D : ℕ), AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ (j : Fin r) (k : Fin g), DifferentiableOn ℂ (fun s => lam s j k) (logDom n a)) → (∀ s ∈ logDom n a, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α).det) → (∀ i j, DifferentiableOn ℂ (fun z => GlobalTheory.PeriodFrame.combMat (ζ z) α i j) (Metric.ball 0 1)) ∧ ∀ i j, DifferentiableOn ℂ (fun s => GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1} := by
  intro n a g r₀ r ζ lam α φ D hζ hlam hunit
  have hζd : DifferentiableOn ℂ ζ (Metric.ball 0 1) := hζ.differentiableOn
  have hζe : ∀ m k, DifferentiableOn ℂ (fun z => ζ z m k) (Metric.ball 0 1) := by
    intro m k
    have h1 := differentiableOn_pi.1 hζd m
    exact differentiableOn_pi.1 h1 k
  have hA : ∀ i j, DifferentiableOn ℂ (fun z => combMat (ζ z) α i j) (Metric.ball 0 1) :=
    fun i j => differentiableOn_combMat_of_entries α hζe i j
  refine ⟨hA, ?_⟩
  intro i j
  set T : Set (Fin n → ℂ) := {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1} with hT
  have hexp : Differentiable ℂ (fun s : Fin n → ℂ => logExp a s) := by
    refine differentiable_pi.2 fun k => ?_
    simp only [logExp]
    split_ifs
    · exact (differentiable_apply k).cexp
    · exact differentiable_apply k
  have hAT : ∀ i j, DifferentiableOn ℂ (fun s => combMat (ζ (logExp a s)) α i j) T := by
    intro i j
    exact (hA i j).comp hexp.differentiableOn (fun s hs => hs.2)
  have hinvT : ∀ i j, DifferentiableOn ℂ (fun s => (combMat (ζ (logExp a s)) α)⁻¹ i j) T :=
    differentiableOn_inv_of_entries hAT (fun s hs => hunit s hs.1)
  have hBT : ∀ i j, DifferentiableOn ℂ (fun s => combMat (lam s) φ i j) T := by
    intro i j
    exact (differentiableOn_combMat_of_entries φ hlam i j).mono (fun s hs => hs.1)
  simp only [perTau, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
  apply DifferentiableOn.const_mul
  apply DifferentiableOn.fun_sum
  intro k _
  exact (hinvT i k).fun_mul (hBT k j)

end GlobalTheory.PeriodFrame
